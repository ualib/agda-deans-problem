---
layout: default
file: "src/DeansProblem/Examples/FreeseEquations.lagda.md"
title: "DeansProblem.Examples.FreeseEquations module"
date: "2026-10-13"
author: "the agda-lattices development team"
---

### Worked example: the equations for a self-similar Freese step

This is the [DeansProblem.Examples.FreeseEquations][] module of this repository.

Freese's step toward Dean's problem ([DeansProblem.Examples.FreeseStep][]) is a
proper containment `⟨a, b, c⟩ ⊊ ⟨a', b', c'⟩` of two copies of `FL(3)` in the
free lattice `FL(9)` on `a₁, a₂₁, a₂₂, b₁, b₂₁, b₂₂, c₁, c₂₁, c₂₂`.  It would
extend to an infinite strictly ascending chain, and so answer Dean's question
positively, if some injective endomorphism `Φ` of `FL(9)` sent the lower triple
to the upper one:

    Φ(a) = a',    Φ(b) = b',    Φ(c) = c'.

`Φ` is determined by the nine terms it assigns to the generators, so these are
three equations in nine unknown elements of `FL(9)`; the twelve relations that
define Freese's `ā`'s are not required of the unknowns.  Injectivity is
decidable for a candidate by Corollary 1.13.  The record
`FreeseΦ`{.AgdaRecord} states the equations together with injectivity, and a
solution would give a chain (`FreeseΦ→chain`{.AgdaFunction}, by
`selfSimilar→chain`{.AgdaFunction} of [DeansProblem.Chain][]).

There is no solution (`no-FreeseΦ`{.AgdaFunction}).  This is the theorem of
[DeansProblem.SelfSimilar][] for Freese's step, packaged as a
`Step`{.AgdaRecord} (`freese-step`{.AgdaFunction}): no step toward Dean's
problem is self-similar.  The search for `Φ` was planned as a sequence of hand
attempts and then a systematic search; the theorem settles every candidate at
once, and costs no decision on Freese's terms.  Three candidates are recorded
here anyway, because each fails for a reason worth seeing, and each verdict is
cheap.

+  **The cyclic permutation `π` and its square** (`π-fails`{.AgdaFunction},
   `π²-fails`{.AgdaFunction}).  `π` is an automorphism, so injective, and it
   sends `a` to `b`, which is not `a'`: `a'` lies below `a`, and `b` does not,
   since `{a, b, c}` freely generates.  Likewise `π²` sends `a` to `c`.
+  **The barred elements** (`bar`{.AgdaFunction}, `bar-not-free`{.AgdaFunction}).
   The natural guess sends each generator `g` to Freese's `ḡ`, so that
   `a₁ ↦ ā₁` and so on.  It is not injective: Freese's relation (1) is
   `c̄₁ ≤ ā₂₁`, while `c₁ ≰ a₂₁`.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module DeansProblem.Examples.FreeseEquations where

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty                             using ( ⊥ )
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Patterns                      using ( 0F ; 1F ; 2F ; 3F ; 4F ; 5F ; 6F
                                                         ; 7F ; 8F )
open import Data.Fin.Properties                    using ( _≟_ )
open import Data.List.Base                         using ( [] ; _∷_ )
open import Data.List.Membership.Propositional     using ( _∈_ )
open import Data.List.Relation.Unary.Any           using ( here ; there )
open import Data.Product                           using ( _,_ ; proj₁ )
open import Relation.Nullary                       using ( ¬_ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import DeansProblem.Examples.FreeseStep
  using  ( a ; b ; c ; a' ; b' ; c' ; π ; ā₁ ; ā₂₁ ; ā₂₂ ; b̄₁ ; b̄₂₁ ; b̄₂₂ ; c̄₁ ; c̄₂₁ ; c̄₂₂
         ; abc ; abc' ; abc-free ; abc'-free ; ρ ; abc≈ ; x∉ρ ; relation-1 )
open import DeansProblem.Chain                     using ( Step ; Chain ; selfSimilar→chain )
open import Lattices.Free.Generation               using ( FreelyGenerates )
open import DeansProblem.SelfSimilar               using ( no-self-similar-step )
open import Lattices.Free.Substitution             using ( Sub ; _[_] )
open import Lattices.Free.Whitman                  using ( _≤ʷ_ ; _≈ʷ_ ; ≤ʷ-trans ; ∧̇-lowerˡ )

open import Agda.Primitive  using () renaming ( Set to Type )
```
-->

#### Freese's step as a step

The lower triple is `abc`{.AgdaFunction}, the upper `abc'`{.AgdaFunction}, the
terms are `ρ`{.AgdaFunction} (`a = a' ∨ (b' ∧ c')` and symmetrically), and the
fresh generator is that of `a'`, which is none of the three terms: everything
was decided in [DeansProblem.Examples.FreeseStep][].

```agda
-- Freese's step ⟨a, b, c⟩ ⊊ ⟨a', b', c'⟩.
freese-step : Step (Fin 9)
freese-step = record
  { σ        = abc
  ; τ        = abc'
  ; σ-free   = abc-free
  ; τ-free   = abc'-free
  ; p        = ρ
  ; σ≈p[τ]   = abc≈
  ; fresh    = 0F
  ; fresh∉p  = x∉ρ
  }
```

#### The equations

```agda
-- An injective Φ sending Freese's lower triple to the upper one.
record FreeseΦ (Φ : Sub (Fin 9) (Fin 9)) : Type where
  field
    Φ-free  : FreelyGenerates Φ
    a↦a'    : a [ Φ ] ≈ʷ a'
    b↦b'    : b [ Φ ] ≈ʷ b'
    c↦c'    : c [ Φ ] ≈ʷ c'

  -- The three equations, indexed as the step's families are.
  Φσ≈τ : ∀ i → abc i [ Φ ] ≈ʷ abc' i
  Φσ≈τ 0F = a↦a'
  Φσ≈τ 1F = b↦b'
  Φσ≈τ 2F = c↦c'

  -- A solution would give an infinite strictly ascending chain.
  FreeseΦ→chain : Chain (Fin 9)
  FreeseΦ→chain = selfSimilar→chain freese-step Φ Φ-free Φσ≈τ
```

No `Φ` solves them (`no-FreeseΦ`{.AgdaFunction}).

```agda
-- The equations have no injective solution.
no-FreeseΦ : (Φ : Sub (Fin 9) (Fin 9)) → ¬ FreeseΦ Φ
no-FreeseΦ Φ sol = no-self-similar-step (_≟_ {9}) freese-step Φ Φ-free Φσ≈τ
  where open FreeseΦ sol
```

#### Three candidates

`a'` lies below `a` (`a'≤a`{.AgdaFunction}), since `a'` is `a ∧ b̄₂₁ ∧ c̄₂₂`.  If
`π` sent `a` to `a'`, then `b`, which is `a [ π ]`, would lie below `a`, and the
join condition of `{a, b, c}` would put the index of `b` in the list `[0F]` of
the index of `a` (`π-fails`{.AgdaFunction}); likewise for `π²`, with `c`
(`π²-fails`{.AgdaFunction}).

```agda
-- a' lies below a.
a'≤a : a' ≤ʷ a
a'≤a = ≤ʷ-trans ∧̇-lowerˡ ∧̇-lowerˡ

-- Two indices of FL(3) that differ.
1F∉[0F] : ¬ (_∈_ {A = Fin 3} 1F (0F ∷ []))
1F∉[0F] (here ())
1F∉[0F] (there ())

2F∉[0F] : ¬ (_∈_ {A = Fin 3} 2F (0F ∷ []))
2F∉[0F] (here ())
2F∉[0F] (there ())

-- The cyclic permutation does not send a to a'.
π-fails : ¬ (a [ π ] ≈ʷ a')
π-fails e = 1F∉[0F] (proj₁ abc-free {1F} {0F ∷ []} (≤ʷ-trans (proj₁ e) a'≤a))

-- Nor does its square.
π²-fails : ¬ (a [ π ] [ π ] ≈ʷ a')
π²-fails e = 2F∉[0F] (proj₁ abc-free {2F} {0F ∷ []} (≤ʷ-trans (proj₁ e) a'≤a))
```

The substitution `bar`{.AgdaFunction} sends each generator to its barred
element.  Its join condition fails at `c₁`: `bar` sends `c₁` to `c̄₁` and `a₂₁` to
`ā₂₁`, and `c̄₁ ≤ ā₂₁` is Freese's relation (1), decided as
`relation-1`{.AgdaFunction} in [DeansProblem.Examples.FreeseStep][]
(`bar-not-free`{.AgdaFunction}).  So `bar` is not injective, and whether it
solves the three equations is beside the point.

```agda
-- The natural guess: each generator to its barred element.
bar : Sub (Fin 9) (Fin 9)
bar 0F = ā₁
bar 1F = ā₂₁
bar 2F = ā₂₂
bar 3F = b̄₁
bar 4F = b̄₂₁
bar 5F = b̄₂₂
bar 6F = c̄₁
bar 7F = c̄₂₁
bar 8F = c̄₂₂

-- Two indices of FL(9) that differ.
6F∉[1F] : ¬ (_∈_ {A = Fin 9} 6F (1F ∷ []))
6F∉[1F] (here ())
6F∉[1F] (there ())

-- The natural guess is not injective.
bar-not-free : ¬ FreelyGenerates bar
bar-not-free (jc , _) = 6F∉[1F] (jc {6F} {1F ∷ []} relation-1)
```

**Corollary A2** of the paper, as one statement: the equations `Φ(a) = a'`,
`Φ(b) = b'`, `Φ(c) = c'` have no solution `Φ` among the injective
endomorphisms of `FL(9)`, the substitutions that freely generate.

```agda
-- Corollary A2: Freese's equations have no injective solution in the endomorphisms of FL(9).
Corollary-A2 : Type
Corollary-A2 =  (Φ : Sub (Fin 9) (Fin 9)) → FreelyGenerates Φ
                → a [ Φ ] ≈ʷ a' → b [ Φ ] ≈ʷ b' → c [ Φ ] ≈ʷ c' → ⊥

-- The proof of Corollary A2.
corollary-A2 : Corollary-A2
corollary-A2 Φ Φ-free ea eb ec =
  no-FreeseΦ Φ (record { Φ-free = Φ-free ; a↦a' = ea ; b↦b' = eb ; c↦c' = ec })
```

--------------------------------------

[DeansProblem.Examples.FreeseEquations]: DeansProblem.Examples.FreeseEquations.html
[DeansProblem.Chain]: DeansProblem.Chain.html
[DeansProblem.Examples.FreeseStep]: DeansProblem.Examples.FreeseStep.html
[DeansProblem.SelfSimilar]: DeansProblem.SelfSimilar.html
