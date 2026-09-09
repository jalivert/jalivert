## 👔 Work
I am a programming languages and type theory researcher from Prague, currently working at the Faculty of Mathematics and Physics at Charles University (CUNI).

🧮 I am interested in systems for formal reasoning, programming languages and mathematical logic. I build small programming languages, theorem provers, and other systems related to PLT concepts.


## :camera: Personal 🎞️ 🏞️
Outside work, I like to take photos on film. I develop film and process the photos myself. I also design 3D printable devices that help me with that.


📸 Also here's my current favorite image.

<div align="center">
  <img width="296" height="392" alt="a minimalist photo of a side of a concrete panel building, it's a black and white photo colorized to be black and orange instead" src="https://github.com/user-attachments/assets/9787e411-1fb0-47c2-a10d-ae944607566f" />
</div>


## 🖋️ My Writings
I sometimes write about what I learned to my [digital notepad](https://github.com/jalivert/reading).


## 3D Product Design
I design free, open-source 3D printable alternatives to commercial devices for film photography.

### 🗜️ [gravity holder V1](https://github.com/jalivert/gravity-holder) 🎞️
a film holder for DSLR scanning

### 🧵 [spooler](https://github.com/jalivert/spooler) 🎞️
a film bulk loader

## 💼 My Research Projects 🗃️
Here are some of my past research projects. I mostly do PL, TT, logic, and formal reasoning related ones.

### [Detour](https://github.com/jalivert/detour) :pear: :tomato:

A research prototype behind our HATRA'24 (SPLASH) paper [`Don't Call Us, We'll Call You`](https://github.com/jalivert/detour/blob/main/hatra24.pdf).
Small Fitch-style FOL checker in Haskell, with automated proof search over user-declared syntax and induction.

<details>
<summary>Show example snippet</summary>

```
module demo

syntax N = Zero
         | Suc(N)

judgment sum = Sum(N, N, N)

rule schema sum-zero for all objects (n : N) :
|
|-------------------------------------- sum-zero
| Sum(Zero, n, n)

rule schema sum-suc for all objects (m : N), (n : N), (o : N) :
| Sum(m, n, o)
|-------------------------------------- sum-suc
| Sum(Suc(m), n, Suc(o))

theorem zero-plus-one : Sum(Suc(Zero), Zero, Suc(Zero))
prove Sum(Suc(Zero), Zero, Suc(Zero))
```
</details>

### [Resin](https://github.com/jalivert/resin) :hibiscus: :tulip:

A small automated theorem prover for _First Order Classical Logic_ built on *resolution*. The resolution machinery follows the [`Handbook of Practical Logic and Automated Reasoning`](https://www.cl.cam.ac.uk/~jrh13/atp/), supplemented by background from [`Artificial Intelligence: A Modern Approach`](https://aima.cs.berkeley.edu) (chapters 7–9); the structure of the implementation reflects those texts.

<details>
<summary>Show example snippet</summary>

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

theorem fact-0-is-1 : Fact(0, 1) .

theorem fact-1-is-1 : Fact(1, 1) .

theorem exists-fact-for-1 : ∃ n Fact(n, 1) .
```
</details>

### [Plover](https://github.com/jalivert/plover) :rose:

Plover is a small automated theorem prover based on a logic language like *Prolog*.
The main idea is to replace *Minilog's* depth-first search strategy with a complete one.

The main difference the complete search strategy makes is that the language can productively answer queries like `nat(A).` for a knowledge base like the following:

<details>
<summary>Show example snippet</summary>

```prolog
nat(s(N)) :- nat(N).
nat(z).
```
</details>


### [Minilog](https://github.com/jalivert/minilog) :cherry_blossom:

Minilog is an implementation of a small logic programming language.
The primary purpose of it is to present a simple abstract machine that can be easily implemented in any language and can serve as an aid when making the intuition about how such a language works.

I have designed the abstract machine and written a short description, [`Implementing Relational Language`](https://github.com/jalivert/minilog/blob/main/WRITEUP.md), of it for (not only) my students to learn about how such a language works.
It is meant to inspire and offer a starting point to them should they decide to implement a small subset of Prolog as their course project.

<details>
<summary>Show example snippet</summary>

```prolog
plus(z, N, N).
plus(s(N), M, s(R)) :- plus(N, M, R).

times(z, _, z).
times(s(N), M, A) :- times(N, M, R), plus(R, M, A).

fact(z, s(z)).
fact(s(N), R) :- fact(N, PR), times(s(N), PR, R).
```
</details>


### [Frea](https://github.com/jalivert/frea) :chestnut:

Small programming language with HM type inference, higher-kinded types, and lazy evaluation.
Implemented as an AST interpreter in Haskell.

<details>
<summary>Show example snippet</summary>

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
</details>


### [Lambdulus](https://github.com/lambdulus) 🌲

Lambdulus is an [interactive learning environment](https://lambdulus.github.io/) for the untyped lambda calculus. It began as my bachelor thesis [`Implementation of lambda expressions evaluator`](https://dspace.cvut.cz/server/api/core/bitstreams/7e28cbae-c8dc-49c1-9a94-472052deb057/content) and later became a paper I and my supervisor presented at SPLASH-E'19 [`Lambdulus: Teaching Lambda Calculus Practically`](https://dl.acm.org/doi/10.1145/3358711.3361629). Lambdulus has been used at FIT CTU since the autumn 2019 as a teaching aid for λ-calculus.
