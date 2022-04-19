# XTT, probably

This is my attempt at implementing XTT, from the papers ["A cubical language for
Bishop sets"][xtt1] and ["Cubical syntax for reflection-free extensional
equality"][xtt2].

Check out some examples in [text.xtt](test.xtt), run them with
```
$ dune exec ./xtt.exe test.xtt
```
and run a (super minimal) REPL with
```
$ dune exec ./xtt.exe
> Π (A : Set) (x : A) → pathp i.A x x
<stdin> is well-typed!
it : Set
it = Π (A : Set) → Π (x : A) → pathp i.A x x
>
```

## Features

 - Pi types
 - Path types
 - `coe`, `com`
 - Yeah that's about it, sigmas and inductives (naturals, booleans) are still
   TO DO

[xtt1]: https://jozefg.github.io/papers/a-cubical-language-for-bishop-sets.pdf
[xtt2]: https://jozefg.github.io/papers/2019-xtt.pdf


