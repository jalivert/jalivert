#### 👔 Work
I am a programming languages and type theory researcher from Prague, currently working at Faculty of Mathematics and Physics at CUNI.

🧮 I am interested in systems for formal reasoning, programming languages and mathematical logic. I build small programming languages, theorem provers, and other systems related to PLT concepts.


#### :camera: 🎞️ 🏞️ Personal
Outside work, I like to take photos on film. I develop film and process the photos myself. I also design 3D printable devices that help me with that.

##### 🧵 [_spooler_ a film bulk loader](https://github.com/jalivert/spooler) 🎞️


📸 Also here's my current favorite image.

<div align="center">
  <img width="295.888888889" height="391.888888889" alt="a minimalist photo of a side of a concrete panel building, it's a black and white photo colorized to be black and orange instead" src="https://github.com/user-attachments/assets/9787e411-1fb0-47c2-a10d-ae944607566f" />
</div>


#### 🖋️ My Writings
I sometimes write about what I learned to my [notepad](https://github.com/jalivert/reading).


#### 💼 🗃️ My Projects
Here are some of my past projects.

##### Theorem Provers

###### [Detour](https://github.com/jalivert/detour) :pear: :tomato:

A toy proof-checker for first-order predicate logic natural deduction in Fitch-style notation.


###### [Resin](https://github.com/jalivert/resin) :hibiscus: :tulip:

A small automated theorem prover for _First Order Classical Logic_ built on *resolution*.

```
constants: zero .

aliases : 0 = zero
        , 1 = suc(0) .

axioms: ∀ n Plus(0, n, n)
      , ∀ n m r Plus(n, m, r) ==> Plus(suc(n), m, suc(r))

      , ∀ n Times(0, n, 0)
      , ∀ n m r a [Times(n, m, r) ∧ Plus(r, m, a) ==> Times(suc(n), m, a)]

      , Fact(0, 1)
      , ∀ n pr r [Fact(n, pr) ∧ Times(suc(n), pr, r) ==> Fact(suc(n), r)]
      .

theorem fact-0-is-1: Fact(0, 1) .

theorem fact-1-is-1 : Fact(1, 1) .

theorem exists-fact-for-1 : ∃ n Fact(n, 1) .
```

###### [Plover](https://github.com/jalivert/plover) :rose:

Plover is a small automated theorem prover based on a logic language like *Prolog*.
The main idea is to replace *Minilog's* depth-first search strategy with a complete one.

The main difference the complete search strategy makes is that the language can productively answer queries like `nat(A).` for a knowledge base like the following:

```prolog
nat(s(N)) :- nat(N).
nat(z).
```


##### Logic Languages

###### [Minilog](https://github.com/jalivert/minilog) :cherry_blossom:

Minilog is an implementation of a small logic programming language.
The primary purpose of it is to present a simple abstract machine that can be easily implemented in any language and can serve as an aid when making the intuition about how such a language works.

I have designed the abstract machine and written a [description](https://github.com/lambduli/minilog/blob/main/WRITEUP.md) of it for (not only) my students to learn about how such a language works.
It is meant to inspire and offer a starting point to them should they decide to implement a small subset of Prolog as their course project.

```prolog
plus(z, N, N).
plus(s(N), M, s(R)) :- plus(N, M, R).

times(z, _, z).
times(s(N), M, A) :- times(N, M, R), plus(R, M, A).

fact(z, s(z)).
fact(s(N), R) :- fact(N, PR), times(s(N), PR, R).
```


##### Functional Statically Typed Languages

###### [Frea](https://github.com/jalivert/frea) :chestnut:

Small programming language with HM type inference, higher-kinded types, and lazy evaluation.
Implemented as an AST interpreter in Haskell.

  
```haskell
module Main where

{ data Result a
    = None
    | Some a

; let
  { zero n = (n == 0)
  ; dec n = (n - 1)
  ; rec fact n =  if (zero n)
                  then 1
                  else (n * (fact (dec n)))
  } in (Some (fact 5))
}
```


