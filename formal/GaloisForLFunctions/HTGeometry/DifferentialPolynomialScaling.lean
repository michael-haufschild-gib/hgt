import GaloisForLFunctions.HTGeometry.DifferentialPolynomialSubfieldDescent
import GaloisForLFunctions.HTGeometry.DifferentialSystemSolution

/-!
# Scaling the differential indeterminate

Substituting `y·u` for the indeterminate of a differential polynomial is an invertible operation
when `y ≠ 0`: the substitution by `y⁻¹·u` undoes it, because substitution is functorial and the
generic point is the identity.  Combined with the descent along a differentially closed subfield,
this says that a differential polynomial cannot vanish at every scaled point `y·c`, `c` in the
subfield, unless it is zero.

That is the form in which a *differentially algebraic* solution contradicts a full parameterized
Galois group: the group contains `diag(c, c⁻¹)` for every `c`, so the relation satisfied by the
solution is satisfied by every scalar multiple of it.

* `scaleSubst`, `evalOver_scaleSubst`, `scaleSubst_scaleSubst`;
* `eq_zero_of_evalOver_scaled_subfield_eq_zero` — **the contradiction.**
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential
open GaloisForLFunctions

attribute [local instance] differentialPolynomialOverDifferential

variable {C L : Type*} [Field C] [Field L] [Algebra C L] [Differential C] [Differential L]

/-- Differential polynomials over a differential base form a differential algebra over it. -/
local instance differentialPolynomialOverDifferentialAlgebra (ι : Type*) :
    DifferentialAlgebra L (DifferentialPolynomial ι L) where
  deriv_algebraMap a := by
    show differentialPolynomialOverDerivation ι L (MvPolynomial.C a) = MvPolynomial.C (a′)
    rw [differentialPolynomialOverDerivation_C]

/-- Substituting `y · u` for the differential indeterminate. -/
def scaleSubst (y : L) (F : DifferentialPolynomial Unit L) : DifferentialPolynomial Unit L :=
  differentialPolynomialEvalOver (K := L)
    (fun _ : Unit => MvPolynomial.C y * MvPolynomial.X (((), 0) : Unit × ℕ)) F

/-- Evaluation of a scaled polynomial is evaluation at the scaled point. -/
theorem evalOver_scaleSubst (y : L) (c : L) (F : DifferentialPolynomial Unit L) :
    differentialPolynomialEvalOver (K := L) (fun _ : Unit => c) (scaleSubst y F)
      = differentialPolynomialEvalOver (K := L) (fun _ : Unit => y * c) F := by
  set φ : DifferentialPolynomial Unit L →+* L :=
    (differentialPolynomialEvalOver (K := L) (fun _ : Unit => c)).toRingHom with hφ
  have hδ : ∀ P : DifferentialPolynomial Unit L, φ (P′) = (φ P)′ := fun P =>
    differentialPolynomialEvalOver_derivation (K := L) (fun _ : Unit => c) P
  have halg : ∀ a : L, φ (algebraMap L (DifferentialPolynomial Unit L) a) = algebraMap L L a := by
    intro a
    show differentialPolynomialEvalOver (K := L) (fun _ : Unit => c)
      (algebraMap L (DifferentialPolynomial Unit L) a) = algebraMap L L a
    rw [MvPolynomial.algebraMap_eq, differentialPolynomialEvalOver_C]
  have hmap := map_differentialPolynomialEvalOver φ hδ halg
    (fun _ : Unit => MvPolynomial.C y * MvPolynomial.X (((), 0) : Unit × ℕ)) F
  have hpt : (fun i : Unit => φ (MvPolynomial.C y * MvPolynomial.X (((), 0) : Unit × ℕ)))
      = fun _ : Unit => y * c := by
    funext i
    show differentialPolynomialEvalOver (K := L) (fun _ : Unit => c)
      (MvPolynomial.C y * MvPolynomial.X (((), 0) : Unit × ℕ)) = y * c
    rw [map_mul, differentialPolynomialEvalOver_C, differentialPolynomialEvalOver_X,
      differentialJet_zero, Algebra.algebraMap_self_apply]
  rw [hpt] at hmap
  exact hmap

theorem scaleSubst_scaleSubst {y : L} (hy : y ≠ 0) (F : DifferentialPolynomial Unit L) :
    scaleSubst y⁻¹ (scaleSubst y F) = F := by
  set q : Unit → DifferentialPolynomial Unit L :=
    fun _ : Unit => MvPolynomial.C y⁻¹ * MvPolynomial.X (((), 0) : Unit × ℕ) with hq
  set φ : DifferentialPolynomial Unit L →+* DifferentialPolynomial Unit L :=
    (differentialPolynomialEvalOver (K := L) q).toRingHom with hφ
  have hδ : ∀ P : DifferentialPolynomial Unit L, φ (P′) = (φ P)′ := fun P =>
    differentialPolynomialEvalOver_derivation (K := L) q P
  have halg : ∀ a : L, φ (algebraMap L (DifferentialPolynomial Unit L) a)
      = algebraMap L (DifferentialPolynomial Unit L) a := by
    intro a
    show differentialPolynomialEvalOver (K := L) q
      (algebraMap L (DifferentialPolynomial Unit L) a) = _
    rw [MvPolynomial.algebraMap_eq, differentialPolynomialEvalOver_C, MvPolynomial.algebraMap_eq]
  have hmap := map_differentialPolynomialEvalOver φ hδ halg
    (fun _ : Unit => MvPolynomial.C y * MvPolynomial.X (((), 0) : Unit × ℕ)) F
  have hpt : (fun i : Unit => φ (MvPolynomial.C y * MvPolynomial.X (((), 0) : Unit × ℕ)))
      = fun i : Unit => (MvPolynomial.X ((i, 0) : Unit × ℕ) : DifferentialPolynomial Unit L) := by
    funext i
    cases i
    show differentialPolynomialEvalOver (K := L) q
      (MvPolynomial.C y * MvPolynomial.X (((), 0) : Unit × ℕ)) = _
    rw [map_mul, differentialPolynomialEvalOver_C, differentialPolynomialEvalOver_X,
      differentialJet_zero, MvPolynomial.algebraMap_eq, hq]
    show MvPolynomial.C y * (MvPolynomial.C y⁻¹ * MvPolynomial.X (((), 0) : Unit × ℕ)) = _
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hy, map_one, one_mul]
  rw [hpt] at hmap
  rw [scaleSubst, scaleSubst]
  refine hmap.trans ?_
  exact differentialPolynomialEvalOver_generic
    (fun i n => by
      show differentialPolynomialOverDerivation Unit L (MvPolynomial.X (i, n)) = _
      rw [differentialPolynomialOverDerivation_X]) F

/-- **A differential polynomial vanishing at every nonzero scaled point of a differentially closed
subfield is zero.**  Multiplying by the indeterminate removes the excluded origin. -/
theorem eq_zero_of_evalOver_scaled_subfield_eq_zero [Algebra ℚ C] [IsDifferentiallyClosed C]
    (hcompat : ∀ a : C, (algebraMap C L a)′ = algebraMap C L (a′))
    {y : L} (hy : y ≠ 0) {F : DifferentialPolynomial Unit L}
    (hF : ∀ c : C, c ≠ 0 → differentialPolynomialEvalOver (K := L)
      (fun _ : Unit => y * algebraMap C L c) F = 0) :
    F = 0 := by
  have hzero : scaleSubst y F = 0 := by
    have hmul : scaleSubst y F * MvPolynomial.X (((), 0) : Unit × ℕ) = 0 := by
      refine eq_zero_of_evalOver_subfield_eq_zero (C := C) hcompat
        (fun G' hG' => exists_evalOver_ne_zero hG') ?_
      intro c
      rw [map_mul, differentialPolynomialEvalOver_X, differentialJet_zero]
      rcases eq_or_ne c 0 with rfl | hc
      · rw [map_zero, mul_zero]
      · rw [evalOver_scaleSubst, hF c hc, zero_mul]
    rcases mul_eq_zero.mp hmul with h | h
    · exact h
    · exact absurd h (MvPolynomial.X_ne_zero _)
  have hback := scaleSubst_scaleSubst hy F
  rw [hzero, scaleSubst, map_zero] at hback
  exact hback.symm

end

end GaloisForLFunctions.HTGeometry
