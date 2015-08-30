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

| Symbol   | Name               | Intro rules  | Elim rules     |
| :------- | :----------------- | :----------- | :------------- |
| `>>`     | Implication (⊃)    | `Imp`        | `Emp`          |
| `&&`     | Conjunction (∧)    | `And`        | `Lend`, `Rend` |
| `||`     | Disjunction (∨)    | `Lor`, `Ror` | `Er`           |
| `>><<`   | Biconditional (⊃⊂) | —            | —              |
| `NOT`    | Negation (¬)       | —            | —              |
| `FORALL` | Universal (∀)      | `Forall`     | `Fae`          |
| `EXISTS` | Existential (∃)    | `Exists`     | `Ee`           |
| `FALSE`  | Falsehood (⊥)      | —            | `False`        |
| `TRUE`   | Truth (⊤)          | —            | —              |


References
----------

* A.S. Troelstra, H. Schwichtenberg, [“Basic proof theory”](http://www.cambridge.org/gb/academic/subjects/computer-science/programming-languages-and-applied-logic/basic-proof-theory-2nd-edition), 2000


About
-----

Made by [Miëtek Bak](https://mietek.io/).  Published under the [MIT X11 license](LICENSE.md).
