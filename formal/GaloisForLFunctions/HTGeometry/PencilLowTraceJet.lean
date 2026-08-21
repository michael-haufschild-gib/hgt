/-
# The low-trace jet of a finite-rank pencil, as a multivariable polynomial

The power traces of a finite-rank pencil expand over ordered words, so the jet of trace coordinates
below the regularization order is a multivariable polynomial in the pencil parameters, of total
degree below the order and with vanishing constant term.  Restricting it to a line through the
origin returns the one-variable low-trace polynomial of the pencil at that direction, which is the
bridge the several-variable completion law needs.

Main results:
* `pencilTraceMv`, `eval_pencilTraceMv`, `totalDegree_pencilTraceMv_le`.
* `lowTraceMv`, `totalDegree_lowTraceMv_le`, `eval_zero_lowTraceMv`.
* `lineRestrict_lowTraceMv` — **the line restriction is the one-variable low-trace polynomial**.
-/
import GaloisForLFunctions.HTGeometry.PencilTracePolynomial
import GaloisForLFunctions.HTGeometry.MultivariableDeterminantFibre
import GaloisForLFunctions.HTGeometry.PencilDeterminantSufficiency
import GaloisForLFunctions.HTGeometry.DeterminantGraphLocallyUniform

open Filter Topology ContinuousLinearMap

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open RHTower

set_option linter.unusedSectionVars false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The power trace of a finite-rank pencil, as a multivariable polynomial. -/
def pencilTraceMv {d : ℕ} (B : Fin d → (H →L[ℂ] H)) (k : ℕ) : MvPolynomial (Fin d) ℂ :=
  ∑ f : Fin (k + 1) → Fin d,
    MvPolynomial.C (opTrace (opWord B f)) * ∏ r, MvPolynomial.X (f r)

theorem eval_pencilTraceMv {d k N : ℕ} {B : Fin d → (H →L[ℂ] H)}
    (hB : ∀ j, HasRankLE (B j) N) (c : Fin d → ℂ) :
    MvPolynomial.eval c (pencilTraceMv B k) = opTrace ((pencilOperator B c) ^ (k + 1)) := by
  rw [opTrace_pow_pencilOperator hB, pencilTraceMv, map_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [map_mul, MvPolynomial.eval_C, map_prod]
  simp only [MvPolynomial.eval_X]
  ring

theorem totalDegree_pencilTraceMv_le {d : ℕ} (B : Fin d → (H →L[ℂ] H)) (k : ℕ) :
    (pencilTraceMv B k).totalDegree ≤ k + 1 := by
  refine le_trans (MvPolynomial.totalDegree_finsetSum _ _) ?_
  refine Finset.sup_le fun f _ => ?_
  refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  refine le_trans (MvPolynomial.totalDegree_finsetProd _ _) ?_
  calc (∑ r : Fin (k + 1), (MvPolynomial.X (f r) : MvPolynomial (Fin d) ℂ).totalDegree)
      ≤ ∑ _r : Fin (k + 1), 1 := by
        refine Finset.sum_le_sum fun r _ => ?_
        rw [MvPolynomial.totalDegree_X]
    _ = k + 1 := by simp

/-- The low-trace jet of a finite-rank pencil, as a multivariable polynomial. -/
def lowTraceMv (p : ℕ) {d : ℕ} (B : Fin d → (H →L[ℂ] H)) : MvPolynomial (Fin d) ℂ :=
  ∑ j ∈ Finset.range (p - 1),
    MvPolynomial.C (-(1 / ((j + 1 : ℕ) : ℂ))) * pencilTraceMv B j

theorem totalDegree_lowTraceMv_le (p : ℕ) {d : ℕ} (B : Fin d → (H →L[ℂ] H)) :
    (lowTraceMv p B).totalDegree ≤ p - 1 := by
  refine le_trans (MvPolynomial.totalDegree_finsetSum _ _) ?_
  refine Finset.sup_le fun j hj => ?_
  rw [Finset.mem_range] at hj
  refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  exact le_trans (totalDegree_pencilTraceMv_le B j) (by omega)

theorem eval_zero_lowTraceMv (p : ℕ) {d : ℕ} (B : Fin d → (H →L[ℂ] H)) :
    MvPolynomial.eval (0 : Fin d → ℂ) (lowTraceMv p B) = 0 := by
  rw [lowTraceMv, map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [map_mul, pencilTraceMv, map_sum]
  have hzero : ∀ f : Fin (j + 1) → Fin d,
      MvPolynomial.eval (0 : Fin d → ℂ)
        (MvPolynomial.C (opTrace (opWord B f)) * ∏ r, MvPolynomial.X (f r)) = 0 := by
    intro f
    rw [map_mul, map_prod]
    simp
  rw [Finset.sum_congr rfl (fun f _ => hzero f), Finset.sum_const_zero, mul_zero]


theorem lineRestrict_pencilTraceMv {d k N : ℕ} {B : Fin d → (H →L[ℂ] H)}
    (hB : ∀ j, HasRankLE (B j) N) (v : Fin d → ℂ) :
    polynomialLineRestrictionLineRestrict v (pencilTraceMv B k)
      = Polynomial.C (opTrace ((pencilOperator B v) ^ (k + 1))) * Polynomial.X ^ (k + 1) := by
  classical
  rw [pencilTraceMv, map_sum, opTrace_pow_pencilOperator hB]
  have hterm : ∀ f : Fin (k + 1) → Fin d,
      polynomialLineRestrictionLineRestrict v
          (MvPolynomial.C (opTrace (opWord B f)) * ∏ r, MvPolynomial.X (f r))
        = Polynomial.C ((∏ r, v (f r)) * opTrace (opWord B f)) * Polynomial.X ^ (k + 1) := by
    intro f
    rw [map_mul, map_prod]
    have hC : polynomialLineRestrictionLineRestrict v
        (MvPolynomial.C (opTrace (opWord B f))) = Polynomial.C (opTrace (opWord B f)) := by
      rw [polynomialLineRestrictionLineRestrict, MvPolynomial.eval₂Hom_C]
    have hX : ∀ r : Fin (k + 1), polynomialLineRestrictionLineRestrict v
        (MvPolynomial.X (f r)) = Polynomial.C (v (f r)) * Polynomial.X := by
      intro r
      rw [polynomialLineRestrictionLineRestrict, MvPolynomial.eval₂Hom_X']
    rw [hC, Finset.prod_congr rfl (fun r _ => hX r), Finset.prod_mul_distrib,
      Finset.prod_const, ← map_prod Polynomial.C, Finset.card_univ, Fintype.card_fin,
      Polynomial.C_mul]
    ring
  rw [Finset.sum_congr rfl (fun f _ => hterm f), ← Finset.sum_mul, ← map_sum Polynomial.C]

theorem lineRestrict_lowTraceMv {d N : ℕ} {B : Fin d → (H →L[ℂ] H)}
    (hB : ∀ j, HasRankLE (B j) N) (p : ℕ) (v : Fin d → ℂ) :
    polynomialLineRestrictionLineRestrict v (lowTraceMv p B)
      = lowTracePoly p (pencilOperator B v) := by
  classical
  rw [lowTraceMv, map_sum, lowTracePoly, Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr (by norm_num) fun j _ => ?_
  rw [map_mul, lineRestrict_pencilTraceMv hB]
  have hC : polynomialLineRestrictionLineRestrict v
      (MvPolynomial.C (-(1 / ((j + 1 : ℕ) : ℂ)))) = Polynomial.C (-(1 / ((j + 1 : ℕ) : ℂ))) := by
    rw [polynomialLineRestrictionLineRestrict, MvPolynomial.eval₂Hom_C]
  rw [hC, ← mul_assoc, ← Polynomial.C_mul]
  have hidx : 1 + j = j + 1 := by omega
  rw [hidx]
  congr 2
  rw [div_eq_mul_inv, one_mul]
  ring

end GaloisForLFunctions.HTGeometry

end
