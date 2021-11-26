CONSTRUCTOR = {
    '(_,_)' : ('+', ('+', '+')),
    '()' : ('+', ()),
    'int' : ('+', ()),  # Pattern matching don't deal with the actual stored integer
    'str' : ('+', ()),
    '(_)car' : ('~-', ('~-',)),
    '(_)cdr' : ('~-', ('~-',)),
    '(_->_)' : ('~-', ('+', '~-')),
    '(_)delay' : ('~-', ('~+',)),
    'wrap(_)' : ('+', ('-',)),
    'mu(_)' : ('+', ('~+',)),
    '(_)mu' : ('~-', ('-',)),
    '[]' : ('~-', ())
}
def format_constructor(name, args):
    return str(name).replace('_', '%s') % args

# A pattern is a tuple-tree like S-expressions.
def format_pattern(pattern):
    if isinstance(pattern, tuple):
        return format_constructor(pattern[0], tuple(format_pattern(x) for x in pattern[1:]))
    else:
        return str(pattern)

def var_pattern(pattern):
    """Finds the free variables in a pattern."""
    if isinstance(pattern, tuple):
        return set.union(*(var_pattern(x) for x in pattern[1:]))
    else:
        return {pattern}

def check_pattern(pattern):
    """Checks whether the polarity is well-formed, and checks for repeated variables.
    Returns the polarity and a set of free variables."""
    if isinstance(pattern, tuple):
        if pattern[0] in CONSTRUCTOR:
            fvar = set()
            for i, arg in enumerate(pattern[1:]):
                polarity, arg_fvar = check_pattern(arg)
                if polarity == "?" or polarity == CONSTRUCTOR[pattern[0]][i]:
                    if fvar.isdisjoint(var_pattern(arg)):
                        fvar.update(arg_fvar)
                    else:
                        raise Exception('Repeated variables in pattern: %s' % format_pattern(pattern))
                else:
                    raise Exception('Invalid polarity in pattern: %s' % format_pattern(pattern))
            return CONSTRUCTOR[pattern[0]][0], fvar
        else:
            raise ValueError('Unknown constructor: %s' % pattern[0])
    else:
        return "?", {pattern}

class SyntaxNode:
    """Represents a node in an abstract syntax tree.

    Each node has a `name` which is the name of its node type,
    and a `attr` dictionary recording various non-`SyntaxNode`
    attributes. The subtrees are recorded in the `child` dictionary.
    Each node also has a `bind` attribute which records the variables
    bound."""
    def __init__(self, name, attr=None, child=None, bind=None):
        self.name = name
        self.attr = attr or {}
        self.child = child or {}
        self.bind = bind or set()

    @staticmethod
    def var(name):
        """Creates a variable node."""
        return SyntaxNode('var', {'name': name})

    @staticmethod
    def cons(name, *args, **tag):
        """Creates a constructor node."""
        return SyntaxNode('cons', {'constructor': name, 'tag': tag}, {i: arg for i, arg in enumerate(args)})

    @staticmethod
    def command(lazy, eager):
        """Creates a command node."""
        return SyntaxNode('command', child={'lazy': lazy, 'eager': eager})

    @staticmethod
    def hole(var, body):
        """Creates a hole node."""
        return SyntaxNode('hole', attr={'bind':var}, child={'body': body}, bind={var})

    @staticmethod
    def case(term, cases:list):
        """Creates a case node."""
        return SyntaxNode('case', child={'term': term}.update({i: case for i, case in enumerate(cases)}))

    @staticmethod
    def clause(pattern, body):
        """Creates a pattern matching clause. This is used in the `cases` list."""
        return SyntaxNode('clause', attr={'pattern': pattern}, child={'body': body}, bind=var_pattern(pattern))

    @staticmethod
    def sub(name, **args):
        """Either calls a builtin or a predefined function."""
        return SyntaxNode('sub', {'name': name}, args)

HALT = SyntaxNode('halt')

def get_clauses(term):
    """Returns a list of clauses in a case node."""
    i = 0
    while i in term.child:
        yield term.child[i]
        i += 1

class PatternMatchException(Exception):
    """Raised when a pattern match fails."""
    pass

def match(pattern, term):
    """Matches a pattern against a term. Returns a dictionary of bindings."""
    if isinstance(pattern, tuple):
        if term.name == 'cons' and pattern[0] == term.attr['constructor']:
            if len(pattern) == 1:
                return {}
            else:
                bindings = {}
                for i, arg in enumerate(pattern[1:]):
                    bindings.update(match(arg, term.child[i]))
                return bindings
        else:
            raise PatternMatchException()
    else:
        return {pattern: term}

def casejump(clauses, term):
    for i, clause in enumerate(clauses):
        try:
            return i, match(clause.attr['pattern'], term)
        except PatternMatchException:
            pass
    raise PatternMatchException()

def check(constants, term, polarity=None):
    """Checks a term for polarity. polarity=`None` for inferring."""
    pass

def evaluate(constants, environment:dict, term):
    """Evaluates a (checked) term.
    Constants are dictionaries with value either:
    - ("native", polarity, list of argument polarities, function)
    - ("constant", polarity, dictionary of argument names -> polarities, term)"""
    if term.name == 'var':
        return environment[term.attr['name']]
    elif term.name == 'cons':
        return SyntaxNode.cons(term.attr['constructor'], *(evaluate(constants, environment, child) for child in term.child.values()), **term.attr['tag'])
    elif term.name == 'command':
        eager = evaluate(constants, environment, term.child['eager'])
        lazy = evaluate(constants, environment, term.child['lazy'])
        if lazy.name == 'hole':
            return evaluate(constants, {**environment, lazy.attr["bind"]:eager}, lazy.child['body'])
        else:
            raise Exception('Unexpected term: %s' % lazy)
    elif term.name == 'hole':
        return term
    elif term.name == 'case':
        i, bindings = casejump(get_clauses(term.child), evaluate(constants, environment, term.child['term']))
        return evaluate(constants, {**environment, **bindings}, term.child[i].child['body'])
    elif term.name == 'clause':
        raise RuntimeError('Unreachable!')
    elif term.name == 'sub':
        c = constants[term.attr['name']]
        if c[0] == 'native':
            return evaluate(constants, environment,
                c[3](**{name : evaluate(constants, environment, arg) for name, arg in term.child.items()}))
        elif c[0] == 'constant':
            arguments = {name: evaluate(constants, environment, arg) for name, arg in term.child.items()}
            return evaluate(constants, {**environment, **arguments}, c[2])
    elif term.name == 'halt':
        return term
    else:
        raise RuntimeError('Bad syntax tree.')

def _print(term, cont):
    print(term.attr["tag"]["value"])
    return SyntaxNode.command(cont, SyntaxNode.cons('[]'))

def _input(cont):
    i = int(input())
    return SyntaxNode.command(cont, SyntaxNode.cons('int', value = i))

# TODO better error prompts
CONSTANTS = {
    'add': ('native', '+', {'x':'+', 'y':'+'}, lambda x, y: SyntaxNode.cons("int", value = x.attr['tag']['value'] + y.attr['tag']['value'])),
    'print': ('native', '#', {'term':'+', 'cont':'-'}, _print),
    'input': ('native', '#', {'cont':'~+'}, _input),
}

if __name__ == '__main__':
    # Inputs an integer x, outputs x + 3.
    program = SyntaxNode.sub('input',
        cont = SyntaxNode.hole('x',
            SyntaxNode.sub('print',
                term = SyntaxNode.sub('add',
                    x = SyntaxNode.var('x'),
                    y = SyntaxNode.cons('int', value = 3)),
                cont = SyntaxNode.hole('_',
                    HALT))))
    evaluate(CONSTANTS, {}, program)
