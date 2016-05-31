Linear Lambda Calculus using DbLib
====

This is a mechanical formalisation of a (Purely) Linear Lambda Calculus using the Coq theorem prover.

It makes use of François Pottier's [DbLib][dblib] for de Bruijn indices.

I completed this formalisation as part of my honours thesis in computer science at UNSW.

## Source Layout

+ DbLib - my fork of DbLib with a few minor changes (lowering added)
+ Linear - a collection of universal definitions about context splitting
+ Syntax.v - types, terms and substitution for PLLC
+ Typing.v - typing judgements for PLLC
+ SmallStepSemantics.v - small-step operational semantics for PLLC
+ Progress.v - proof of type soundness
+ Subst.v - proof of the substitution lemma for PLLC
+ Preservation.v - proof of type preservation, relying on the substitution lemma
+ Soundness.v - proof of soundness, relying on progress and preservation

## Dependencies

* [Coq v8.4][coq-84]. I've tested with 8.4pl5 specifically.

## Build Instructions

```
$ git clone --recursive https://github.com/michaelsproul/dblib-linear
$ make
```

The recursive Git clone just ensures that DbLib gets pulled in.

## Stepping Through Interactively

Once you've run `make` you should be able to step through any individual file using CoqIDE or
an editor of your choice. You just have to make sure to pass the `-R . LLC` option to the Coq
process at some point. For CoqIDE you can pass this flag via the command-line.

```
$ coqide -R . LLC .
```

[dblib]: https://github.com/fpottier/dblib
[coq-84]: https://coq.inria.fr/coq-84
