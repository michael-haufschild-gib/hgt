import GaloisForLFunctions.HTGeometry.InvolutionTateDualLattice
import GaloisForLFunctions.HTGeometry.RealTorusComponentGroup

/-!
# Equality of the real-point component groups of a real torus and of its dual

Let `A = V / Λ` be a complex torus with a real structure `σ` (complex conjugation), so that `Λ` is a
finite free `ℤ`-module of rank `2g` with an involution `σ` whose `±1`-eigenlattices both have rank
`g`.  The dual complex torus `B` has period lattice `Λ^∨ = Hom_ℤ(Λ, ℤ)` with the involution
`-σ^∨`, and

```
#π₀(A(ℝ)) = #Ĥ¹(σ, Λ),      #π₀(B(ℝ)) = #Ĥ¹(-σ^∨, Λ^∨) .
```

This file proves that these two numbers agree
(`RealTorus.card_tateH1_eq_card_tateH1_neg_dual`), which is the final reduction in the proof of
Proposition 5.1 of Suzuki, *Duality invariance of Faltings heights, Hodge line bundles and global
periods* (arXiv:2504.04993) — the statement "we are reduced to showing that
`#π₀(A(ℝ)) = #π₀(B(ℝ))`".

The chain is:

* `#Ĥ¹(-σ^∨, Λ^∨) = #Ĥ⁰(σ^∨, Λ^∨)`  (replacing an involution by its negative swaps `Ĥ⁰` and `Ĥ¹`);
* `#Ĥ⁰(σ^∨, Λ^∨) = #Ĥ⁰(σ, Λ)`       (Tate duality for `ℤ/2`, `InvolutionTate.card_H0_dual`);
* `#Ĥ⁰(σ, Λ) = #Ĥ¹(σ, Λ)`           (the Herbrand quotient is `1` in the balanced case).

Combined with `RealTorus.card_quot_eq_card_tateH1` this computes the component group of `A(ℝ)`
itself.
-/

namespace GaloisForLFunctions.HTGeometry

open LinearMap Module Submodule InvolutionTate

namespace InvolutionTate

variable {Λ : Type*} [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ] {σ : Λ →ₗ[ℤ] Λ}

/-- `Ĥ¹` of the negated dual involution is `Ĥ⁰` of the dual involution. -/
theorem card_H1_neg_dual (τ : Module.Dual ℤ Λ →ₗ[ℤ] Module.Dual ℤ Λ) :
    Nat.card (H1 (-τ)) = Nat.card (H0 τ) :=
  card_subquot_congr (minusPart_neg τ) (range_dlt_neg τ)

/-- `#Ĥ¹(-σ^∨, Λ^∨) = #Ĥ⁰(σ, Λ)`. -/
theorem card_H1_neg_dualInvolution (hσ : ∀ x, σ (σ x) = x) :
    Nat.card (H1 (-(dualInvolution σ))) = Nat.card (H0 σ) :=
  (card_H1_neg_dual (dualInvolution σ)).trans (card_H0_dual hσ)

/-- **Suzuki, Proposition 5.1, final reduction.**  For a balanced involution of a finite free
`ℤ`-lattice, `Ĥ¹` of the lattice and `Ĥ¹` of the negated dual involution on the dual lattice have
the same cardinality: `#π₀(A(ℝ)) = #π₀(B(ℝ))`. -/
theorem card_H1_eq_card_H1_neg_dualInvolution (hσ : ∀ x, σ (σ x) = x)
    (hbal : finrank ℤ (plusPart σ) = finrank ℤ (minusPart σ)) :
    Nat.card (H1 σ) = Nat.card (H1 (-(dualInvolution σ))) := by
  rw [card_H1_neg_dualInvolution hσ, card_H0_eq_card_H1 hσ hbal]

/-- The same statement with the balance hypothesis expressed as "the fixed lattice has half the
total rank". -/
theorem card_H1_eq_card_H1_neg_dualInvolution_of_two_mul (hσ : ∀ x, σ (σ x) = x)
    (h : 2 * finrank ℤ (plusPart σ) = finrank ℤ Λ) :
    Nat.card (H1 σ) = Nat.card (H1 (-(dualInvolution σ))) := by
  refine card_H1_eq_card_H1_neg_dualInvolution hσ ?_
  have := finrank_plusPart_add_finrank_minusPart hσ
  omega

end InvolutionTate

namespace RealTorus

variable {R V : Type*} [CommRing R] [Invertible (2 : R)] [AddCommGroup V] [Module R V]
variable {σ : V →ₗ[R] V} {Λ : Submodule ℤ V}

/-- **The component group of `A(ℝ)` equals the one of `B(ℝ)`.**  For a real torus `V / Λ` with
`ℤ`-lattice `Λ` of balanced eigenranks, the component group of the `σ`-fixed points is finite of
cardinality `#Ĥ¹(-σ^∨, Λ^∨)`, the corresponding invariant of the dual torus. -/
theorem card_quot_eq_card_tateH1_neg_dual [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
    (hσ : ∀ x, σ (σ x) = x) (hΛ : ∀ x ∈ Λ, σ x ∈ Λ)
    (hbal : finrank ℤ (InvolutionTate.plusPart (sigmaLat σ Λ hΛ))
      = finrank ℤ (InvolutionTate.minusPart (sigmaLat σ Λ hΛ))) :
    Nat.card ((realLocus σ Λ) ⧸ comap (realLocus σ Λ).subtype (fixedPart σ ⊔ Λ))
      = Nat.card (InvolutionTate.H1 (-(InvolutionTate.dualInvolution (sigmaLat σ Λ hΛ)))) := by
  rw [card_quot_eq_card_tateH1 hσ hΛ]
  exact InvolutionTate.card_H1_eq_card_H1_neg_dualInvolution
    (sigmaLat_involutive hσ hΛ) hbal

end RealTorus

end GaloisForLFunctions.HTGeometry
