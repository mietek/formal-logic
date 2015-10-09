_formal-logic_
==============

Formalisation of some logical systems, in Agda, Idris, and Haskell.


### Notes

This work compares a number of techniques for formalising typed higher-order languages in a typed meta-language, with an eye towards the readability of programs written in the resulting object-language.

Following [Troelstra and Schwichtenberg](#references), we use **M**, **I**, and **C** for minimal, intuitionistic, and classical first-order predicate calculus, respectively; **Mp**, **Ip**, and **Cp** stand for the corresponding propositional systems.  For technical reasons, we refer to minimal implicational logic as **ArrMp**, and to minimal implicational modal logic as **BoxMp**.

We investigate the issue of binder representation by contrasting the use of _de Bruijn indices_ against _parametric higher-order abstract syntax_ (PHOAS), after [Chlipala](#references).  Each approach is presented in the widely-used _initial_ encoding, using a generalised algebraic data type, and the _final_ encoding of [Carette, Kiselyov, and Shan](#references), using a sequence of type classes.

We refer to the de Bruijn, vector-based de Bruijn, and PHOAS approach as **B**, **V**, and **P**, respectively; **i** and **f** correspond to the initial and final encoding.


### Implementations

|        | **Pi** | **Pf** | **Bi** | **Vi** | **Bf**
| :----- | :----- | :----- | :----- | :----- | :-----
| **ArrMp** | [`agda`](src/Pi/ArrMp.agda), [`idr`](src/Pi/ArrMp.idr), [`hs`](src/Pi/ArrMp.hs) | [`agda`](src/Pf/ArrMp.agda), [`idr`](src/Pf/ArrMp.idr), [`hs`](src/Pf/ArrMp.hs) | [`agda`](src/Bi/ArrMp.agda) | [`agda`](src/Vi/ArrMp.agda) | [`agda`](src/Bf/ArrMp.agda)
| **BoxMp** | [`agda`](src/Pi/BoxMp.agda), [`idr`](src/Pi/BoxMp.idr), [`hs`](src/Pi/BoxMp.hs) | [`agda`](src/Pf/BoxMp.agda), [`idr`](src/Pf/BoxMp.idr), [`hs`](src/Pf/BoxMp.hs) | [`agda`](src/Bi/BoxMp.agda) | [`agda`](src/Vi/BoxMp.agda) | [`agda`](src/Bf/BoxMp.agda)
| **Mp**    | [`agda`](src/Pi/Mp.agda), [`idr`](src/Pi/Mp.idr), [`hs`](src/Pi/Mp.hs) | [`agda`](src/Pf/Mp.agda), [`idr`](src/Pf/Mp.idr), [`hs`](src/Pf/Mp.hs) | [`agda`](src/Bi/Mp.agda) | [`agda`](src/Vi/Mp.agda)    | [`agda`](src/Bf/Mp.agda)
| **Ip**    | [`agda`](src/Pi/Ip.agda), [`idr`](src/Pi/Ip.idr), [`hs`](src/Pi/Ip.hs) | [`agda`](src/Pf/Ip.agda), [`idr`](src/Pf/Ip.idr), [`hs`](src/Pf/Ip.hs) | [`agda`](src/Bi/Ip.agda) | [`agda`](src/Vi/Ip.agda)    | [`agda`](src/Bf/Ip.agda)
| **Cp**    | [`agda`](src/Pi/Cp.agda), [`idr`](src/Pi/Cp.idr), [`hs`](src/Pi/Cp.hs) | [`agda`](src/Pf/Cp.agda), [`idr`](src/Pf/Cp.idr), [`hs`](src/Pf/Cp.hs) | [`agda`](src/Bi/Cp.agda) | [`agda`](src/Vi/Cp.agda)    | [`agda`](src/Bf/Cp.agda)
| **M**     | [`agda`](src/Pi/M.idr), [`idr`](src/Pi/M.idr) | | | | |
| **I**     | [`agda`](src/Pi/I.idr), [`idr`](src/Pi/I.idr) | | | | |
| **C**     | [`agda`](src/Pi/C.idr), [`idr`](src/Pi/C.idr) | | | | |


Usage
-----

To check all files automatically:

```
$ make
```

To load a particular file for interactive use:

```
$ agda --safe -I -i src src/FILE.agda
```

```
$ ghci -Wall -isrc src/FILE.hs
```

```
$ idris -i src src/FILE.idr
```

Tested with Agda 2.4.2.3, Idris 0.9.19, and GHC 7.8.4.


### Notation

This section describes the notation available in the PHOAS approach; in the de Bruijn approach, variable binding is not part of the constructors or eliminators.

#### Agda

| **Op** | **Type**  | **Constructors**             | **Eliminators**
| :----: | :-------- | :--------------------------- | :--------------------
| →      | `=>`      | `lam` *v* `=>` *e*           | *e₁* `$` *e₂*
| ∧      | `&&`      | `[` *e₁* `,` *e₂* `]`        | `fst` *e* ; `snd` *e*
| ∨      | `||`      | `left` *e* ; `right` *e*     | `case` *e₀* `of` *v₁* `=>` *e₁* `or` *v₂* `=>` *e₂*
| ⊥      | `FALSE`   | —                            | **I**: `abort` *e* ; **C**: `abort` *v* `=>` *e*
| ↔︎      | `<=>`     | —                            | —
| ¬      | `NOT`     | —                            | —
| ⊤      | `TRUE`    | —                            | —
| ∀      | `FORALL`  | `pi` *v* `=>` *e*            | *e₁* `$$` *e₂*
| ∃      | `EXISTS`  | `[` *e₁* `,,` *e₂* `]`       | `split` *e₀* `as` *v* `=>` *e*
| □      | `BOX`     | `box` *e*                    | `unbox` *e₀* `as` *v* `=>` *e*
| ◇      | `DIAMOND` | —                            | —


#### Idris

| **Op** | **Type**  | **Constructors**             | **Eliminators**
| :----: | :-------- | :--------------------------- | :--------------------
| →      | `:=>`     | `lam` *v* `:=>` *e*          | *e₁* `:$` *e₂*
| ∧      | `:&&`     | `[` *e₁* `,` *e₂* `]`        | `fst` *e* ; `snd` *e*
| ∨      | `:||`     | `left` *e* ; `right` *e*     | `case` *e₀* `of` *v₁* `:=>` *e₁* `or` *v₂* `:=>` *e₂*
| ⊥      | `FALSE`   | —                            | **I**: `abort` *e* ; **C**: `abort` *v* `:=>` *e*
| ↔︎      | `:<=>`    | —                            | —
| ¬      | `NOT`     | —                            | —
| ⊤      | `TRUE`    | —                            | —
| ∀      | `FORALL`  | `pi` *v* `:=>` *e*           | *e₁* `:$$` *e₂*
| ∃      | `EXISTS`  | `[` *e₁* `,,` *e₂* `]`       | `split` *e₀* `as` *v* `:=>` *e*
| □      | `BOX`     | `box` *e*                    | `unbox` *e₀* `as` *v* `:=>` *e*
| ◇      | `DIAMOND` | —                            | —


#### Haskell

| **Op** | **Type**  | **Constructors**             | **Eliminators**
| :----: | :-------- | :--------------------------- | :--------------------
| →      | `:=>`     | `lam` *λ*                    | **i**: *e₁* `:$` *e₂* ; **f**: *e₁* `.$` *e₂*
| ∧      | `:&&`     | `pair` `(` *e₁* `,` *e₂* `)` | `fst'` *e* ; `snd'`  *e*
| ∨      | `:||`     | `left` *e* ; `right` *e*     | `case'` *e₀* *λ₁* *λ₂*
| ⊥      | `FALSE`   | —                            | **I**: `abort` *e* ; **C**: `abort` *λ*
| ↔︎      | `:<=>`    | —                            | —
| ¬      | `NOT`     | —                            | —
| ⊤      | `TRUE`    | —                            | —
| ∀      | `FORALL`  | `pi` *λ*                     | **i**: *e₁* `:$$` *e₂* ; **f**: *e₁* `.$$` *e₂*
| ∃      | `EXISTS`  | `sig` `(` *e₁* `,` *e₂* `)`  | `split` *e₀* *λ*
| □      | `BOX`     | `box` *e*                    | `unbox` *e₀* *λ*
| ◇      | `DIAMOND` | —                            | —


About
-----

Made by [Miëtek Bak](https://mietek.io/).  Published under the [MIT X11 license](LICENSE.md).

Thanks to Dominique Devriese, Darryl McAdams, and Andrea Vezzosi for comments and discussion.


### References

* J.-P. Bernardy, [`PHOAS.hs`](https://github.com/jyp/topics/blob/master/PHOAS/PHOAS.hs), 2008
* G. Boolos, [“The logic of provability”](http://www.cambridge.org/gb/academic/subjects/philosophy/logic/logic-provability), 1993
* J. Carette, O. Kiselyov, C. Shan, [“Finally tagless, partially evaluated: Tagless staged interpreters for simpler typed languages”](http://okmij.org/ftp/tagless-final/JFP.pdf), 2009
* A. Chlipala, [“Parametric higher-order abstract syntax for mechanized semantics”](http://adam.chlipala.net/papers/PhoasICFP08/PhoasICFP08.pdf), 2008
* N.A. Danielsson, [`HOAS.SimplyTyped.agda`](http://www.cse.chalmers.se/~nad/listings/simply-typed/HOAS.SimplyTyped.html), 2008
* D. Devriese, F. Piessens, [“On the bright side of type classes: Instance arguments in Agda”](https://lirias.kuleuven.be/bitstream/123456789/304985/1/icfp001-Devriese.pdf), 2011
* F. Pfenning, R. Davies, [“A judgmental reconstruction of modal logic”](https://www.cs.cmu.edu/~fp/papers/mscs00.pdf), 2001
* A.S. Troelstra, H. Schwichtenberg, [“Basic proof theory”](http://www.cambridge.org/gb/academic/subjects/computer-science/programming-languages-and-applied-logic/basic-proof-theory-2nd-edition), 2000
