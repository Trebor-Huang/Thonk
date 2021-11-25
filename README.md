# Thonk 🤔

An untyped programming language based on polarized type theory. The language is implemented and specified in Agda.

## Whassat? Was it typed or untyped?

A long-known motto in computer science is "Untyped is *uni*-typed." An untyped language is simply a typed language, but everything is of the same type, and the type-checker never complains. This allows us to cherrypick the features of a typed language without introducing a type system.

## But what's left when you remove the type system?

When you take "type system" away from "polarized type system", you get "polarized", of course! In Thonk, every expression is untyped (or, has the same type, if you prefer), but has a *polarity* of either "positive" or "negative". Simply put, positive means eager, and negative means lazy.

## Showcase: Fizzbuzz

```
-- Fizzbuzz
-- Prints numbers from 1 to 100, but only prints "Fizz" for multiples of 3, "Buzz" for multiples of 5, and "FizzBuzz" for multiples of both 3 and 5.

clause(+n) -> str
    \case (n % 3, n % 5) {
        (0, 0) => "FizzBuzz" ;
        (0, _) => "Fizz" ;
        (_, 0) => "Buzz" ;
        (_, _) => str(n) ;
    }

\{
    You can see that all the keywords
    begins with a backslash.

    This is a block comment.
}

fizzbuzz(+n) -> #
    \if (n == 0)
        exit()
    \else
        println(clause(n))>>  -- fishy syntax to be explained later
        fizzbuzz(n - 1)

main() -> #
    fizzbuzz(100)
```


