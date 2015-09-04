_formal-logic_
==============

Formalisation of some logical systems, in Agda, Haskell, and Idris.


### Propositional logic

#### Implicational Hilbert-style

* [ImpHm.agda](src/ImpHm.agda)
* [ImpHm.hs](src/ImpHm.hs)
* [ImpHm.idr](src/ImpHm.idr)


#### Implicational Gentzen-style

* [ImpNm.agda](src/ImpNm.agda)
* [ImpNm.hs](src/ImpNm.hs)
* [ImpNm.idr](src/ImpNm.idr)


### First-order predicate logic

#### Minimal

* [Nm.agda](src/Nm.agda)
* [Nm.idr](src/Nm.idr)


#### Classical

* [Nc.agda](src/Nc.agda)
* [Nc.idr](src/Nc.idr)


#### Intuitionistic

* [Ni.agda](src/Ni.agda)
* [Ni.idr](src/Ni.idr)


### Propositional modal logic

#### Implicational necessity Hilbert-style

* [ImpBoxHm.agda](src/ImpBoxHm.agda)
* [ImpBoxHm.hs](src/ImpBoxHm.hs)
* [ImpBoxHm.idr](src/ImpBoxHm.idr)


#### Implicational necessity Gentzen-style

* [ImpBoxNm.agda](src/ImpBoxNm.agda)
* [ImpBoxNm.hs](src/ImpBoxNm.hs)
* [ImpBoxNm.idr](src/ImpBoxNm.idr)


Usage
-----

To check all files automatically:

```
$ make
```

To load a particular file for interactive use:

```
$ agda -I --safe -i src src/FILE.agda
```

```
$ ghci src/FILE.hs
```

```
$ idris --noprelude --total src/FILE.idr
```


### Conventions

#### Connectives, quantifiers, and constants

| Symbol   | Name               | Introduction   | Elimination         |
| :------- | :----------------- | :------------- | :------------------ |
| —        | Hypothesis         | `var_`         | —                   |
| `>>`     | Implication (⊃)    | `lam_>>_`      | `_<<_`              |
| `/\`     | Conjunction (∧)    | `[_*_]`        | `fst_`, `snd_`      |
| `\/`     | Disjunction (∨)    | `one_`, `two_` | `case_of_>>_or_>>_` |
| `FORALL` | Universal (∀)      | `pi_!>>_`      | `_<<!_`             |
| `EXISTS` | Existential (∃)    | `[_!*_]`       | `take_as_>>_`       |
| `BOTTOM` | Falsehood (⊥)      | —              | `efq_>>_`; `efq_`   |
| `>><<`   | Biconditional (⊃⊂) | —              | —                   |
| `NOT`    | Negation (¬)       | —              | —                   |
| `TOP`    | Truth (⊤)          | —              | —                   |
| `BOX`    | Necessity (□)      | `box_`         | `unbox_as_>>_`      |
| `DIAMOND`| Possibility (◇)    | —              | —                   |


References
----------

* G. Boolos, [“The logic of provability”](http://www.cambridge.org/gb/academic/subjects/philosophy/logic/logic-provability), 1993
* A. Chlipala, [“Parametric higher-order abstract syntax for mechanized semantics”](http://adam.chlipala.net/papers/PhoasICFP08/PhoasICFP08.pdf), 2008
* F. Pfenning, R. Davies, [“A judgmental reconstruction of modal logic”](https://www.cs.cmu.edu/~fp/papers/mscs00.pdf), 2001
* A.S. Troelstra, H. Schwichtenberg, [“Basic proof theory”](http://www.cambridge.org/gb/academic/subjects/computer-science/programming-languages-and-applied-logic/basic-proof-theory-2nd-edition), 2000


About
-----

Made by [Miëtek Bak](https://mietek.io/).  Published under the [MIT X11 license](LICENSE.md).
