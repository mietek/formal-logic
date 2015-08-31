_formal-logic_
==============

Formalisation of some logical systems, in Agda and Idris.


### Logics

#### Natural deduction

##### ImpNm

Minimal implication logic  ([ImpNm.agda](src/ImpNm.agda), [ImpNm.idr](src/ImpNm.idr))


##### Nm

Minimal logic  ([Nm.agda](src/Nm.agda), [Nm.idr](src/Nm.idr))


##### Nc

Classical logic  ([Nc.agda](src/Nc.agda), [Nc.idr](src/Nc.idr))


##### Ni

Intuitionistic logic  ([Ni.agda](src/Ni.agda), [Ni.idr](src/Ni.idr))


#### Hilbert-style

##### ImpHm

Minimal implication logic  ([ImpHm.agda](src/ImpHm.agda), [ImpHm.idr](src/ImpHm.idr))


Usage
-----

##### Agda

```
$ agda -i src src/FILE.agda
```

##### Idris

```
$ idris --noprelude src/FILE.idr
```


### Conventions

#### Connectives, quantifiers, and constants

| Symbol   | Name               | Introduction   | Elimination         |
| :------- | :----------------- | :------------- | :------------------ |
| —        | Hypothesis         | `hyp_`         | —                   |
| `|>`     | Implication (⊃)    | `lam_>>_`      | `_<<_`              |
| `/\`     | Conjunction (∧)    | `[_*_]`        | `fst_`, `snd_`      |
| `\/`     | Disjunction (∨)    | `one_`, `two_` | `case_of_>>_or_>>_` |
| `FORALL` | Universal (∀)      | `pi_!>>_`      | `_<<!_`             |
| `EXISTS` | Existential (∃)    | `[_!*_]`       | `take_as_>>_`       |
| `BOTTOM` | Falsehood (⊥)      | —              | `efq_>>_`; `efq_`   |
| `|><|`   | Biconditional (⊃⊂) | —              | —                   |
| `NOT`    | Negation (¬)       | —              | —                   |
| `TOP`    | Truth (⊤)          | —              | —                   |


References
----------

* A.S. Troelstra, H. Schwichtenberg, [“Basic proof theory”](http://www.cambridge.org/gb/academic/subjects/computer-science/programming-languages-and-applied-logic/basic-proof-theory-2nd-edition), 2000


About
-----

Made by [Miëtek Bak](https://mietek.io/).  Published under the [MIT X11 license](LICENSE.md).
