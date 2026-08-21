import GaloisForLFunctions.HTGeometry.DifferentialTangentLinearization
import GaloisForLFunctions.HTGeometry.JetHorizonAdditiveTorsorLaw

/-!
# The tangent space of a differential-algebraic set is a module over the constants

The linearisation of a differential polynomial at a point is `∑_v (∂_v F)(p) · δ^{v.2} X_{v.1}`,
which is additive in the perturbation `X` and commutes with multiplication by a *differential
constant*, because jets are additive and `δ(c·x) = c·δx` exactly when `δc = 0`.  So the tangent
directions at a point of the zero set of `F` form a submodule over the field of constants, in any
number of differential indeterminates.

That is the shape Cassidy's classification consumes: `cassidy_sl2` asks for a `C`-submodule of
`sl₂(U)`, and the Lie algebra of a differential algebraic group is exactly such a tangent space.

* `differentialJet_const_mul` — jets are linear over the constants;
* `linearisationForm`, `linearisationForm_add`, `linearisationForm_const_smul`;
* `tangentSpace`, `mem_tangentSpace_iff_snd_eq_zero`, `mem_tangentSpace_of_evalOver_dual`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential
open GaloisForLFunctions

variable {C : Type*} [CommRing C] [Differential C] {ι : Type*}

theorem differentialJet_eq_zero_zero (n : ℕ) : differentialJet n (0 : C) = 0 := by
  induction n with
  | zero => rw [differentialJet_zero]
  | succ n ih => rw [differentialJet_succ, ih, map_zero]

/-- **Jets are linear over the differential constants.** -/
theorem differentialJet_const_mul {c : C} (hc : c′ = 0) (x : C) :
    ∀ n : ℕ, differentialJet n (c * x) = c * differentialJet n x
  | 0 => by rw [differentialJet_zero, differentialJet_zero]
  | (n + 1) => by
      rw [differentialJet_succ, differentialJet_succ, differentialJet_const_mul hc x n,
        Derivation.leibniz, hc, smul_zero, add_zero, smul_eq_mul]

/-- The linearisation of `F` at `p`, as a form in the perturbation. -/
def linearisationForm (p : ι → C) (F : DifferentialPolynomial ι C) (s : Finset (ι × ℕ))
    (X : ι → C) : C :=
  ∑ v ∈ s, differentialPolynomialEvalOver (K := C) p (MvPolynomial.pderiv v F)
    * differentialJet v.2 (X v.1)

theorem linearisationForm_add (p : ι → C) (F : DifferentialPolynomial ι C) (s : Finset (ι × ℕ))
    (X Y : ι → C) :
    linearisationForm p F s (X + Y) = linearisationForm p F s X + linearisationForm p F s Y := by
  rw [linearisationForm, linearisationForm, linearisationForm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  show _ * differentialJet v.2 (X v.1 + Y v.1) = _
  rw [differentialJet_add_apply, mul_add]

theorem linearisationForm_zero (p : ι → C) (F : DifferentialPolynomial ι C)
    (s : Finset (ι × ℕ)) : linearisationForm p F s 0 = 0 := by
  rw [linearisationForm]
  refine Finset.sum_eq_zero fun v _ => ?_
  show _ * differentialJet v.2 (0 : C) = 0
  rw [differentialJet_eq_zero_zero, mul_zero]

theorem linearisationForm_const_smul (p : ι → C) (F : DifferentialPolynomial ι C)
    (s : Finset (ι × ℕ)) {c : C} (hc : c′ = 0) (X : ι → C) :
    linearisationForm p F s (fun i => c * X i) = c * linearisationForm p F s X := by
  rw [linearisationForm, linearisationForm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  show _ * differentialJet v.2 (c * X v.1) = _
  rw [differentialJet_const_mul hc]
  ring

section Field

variable {C : Type*} [Field C] [Differential C] {ι : Type*}

/-- **The tangent directions at a point of the zero set of `F`.** -/
def tangentSpace (p : ι → C) (F : DifferentialPolynomial ι C) (s : Finset (ι × ℕ)) :
    Submodule (differentialConstants C) (ι → C) where
  carrier := {X | linearisationForm p F s X = 0}
  zero_mem' := linearisationForm_zero p F s
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [linearisationForm_add, ha, hb, add_zero]
  smul_mem' := by
    intro c X hX
    simp only [Set.mem_setOf_eq] at hX ⊢
    have hc : (c : C)′ = 0 := c.2
    have hsm : (c • X : ι → C) = fun i => (c : C) * X i := rfl
    rw [hsm, linearisationForm_const_smul p F s hc, hX, mul_zero]

@[simp] theorem mem_tangentSpace_iff {p : ι → C} {F : DifferentialPolynomial ι C}
    {s : Finset (ι × ℕ)} {X : ι → C} :
    X ∈ tangentSpace p F s ↔ linearisationForm p F s X = 0 := Iff.rfl

/-- The tangent space is the vanishing locus of the `ε`-part at the dual point. -/
theorem mem_tangentSpace_iff_snd_eq_zero {p : ι → C} {F : DifferentialPolynomial ι C}
    {s : Finset (ι × ℕ)} (hs : F.vars ⊆ s) {X : ι → C} :
    X ∈ tangentSpace p F s
      ↔ (differentialPolynomialEvalOver (K := C) (dualPoint p X) F).snd = 0 := by
  rw [mem_tangentSpace_iff, snd_differentialPolynomialEvalOver_dual p X F s hs,
    linearisationForm]

/-- **A perturbation that keeps the value zero is a tangent direction.** -/
theorem mem_tangentSpace_of_evalOver_dual {p : ι → C} {F : DifferentialPolynomial ι C}
    {s : Finset (ι × ℕ)} (hs : F.vars ⊆ s) {X : ι → C}
    (h : differentialPolynomialEvalOver (K := C) (dualPoint p X) F = 0) :
    X ∈ tangentSpace p F s := by
  rw [mem_tangentSpace_iff_snd_eq_zero hs, h, TrivSqZeroExt.snd_zero]

end Field

end

end GaloisForLFunctions.HTGeometry
