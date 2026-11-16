import GaloisForLFunctions.HTGeometry.MatrixGeometry.PlanarRealStress
import Mathlib.Tactic.Module

/-!
# Target stress of an arbitrary family of planar trace-free Hessians

Stacking any finite family of real symmetric trace-free two-by-two matrices
produces two orthogonal columns of equal energy. The target stress therefore
has only the eigenvalues zero and half its trace, independently of target
dimension. This is the planar target-stress construction in Luchese's
regularity argument (https://arxiv.org/abs/2611.17317, proof of Theorem 3).
-/

open Matrix
open scoped BigOperators ComplexOrder

namespace HTGeometry.PlanarFamilyStress

variable {J : Type*} [Fintype J]

/-- Stack the real planar Hessians indexed by the target components. -/
def frame (a b : J → ℝ) : Matrix (J × Fin 2) (Fin 2) ℝ :=
  fun p k => if p.2 = 0 then (if k = 0 then a p.1 else b p.1)
    else (if k = 0 then b p.1 else -a p.1)

/-- Squared length of either derivative column. -/
def energy (a b : J → ℝ) : ℝ := ∑ j, ((a j)^2 + (b j)^2)

/-- Gram matrix in the target space of all Hessian components. -/
def stress (a b : J → ℝ) : Matrix (J × Fin 2) (J × Fin 2) ℝ :=
  frame a b * (frame a b)ᵀ

theorem energy_nonneg (a b : J → ℝ) : 0 ≤ energy a b :=
  Finset.sum_nonneg (fun _ _ => add_nonneg (sq_nonneg _) (sq_nonneg _))

/-- The scalar domain Gram identity persists for every target dimension. -/
theorem domain_gram (a b : J → ℝ) :
    (frame a b)ᵀ * frame a b = energy a b • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i k
  fin_cases i <;> fin_cases k
  all_goals simp [frame, energy, Matrix.mul_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two, pow_two, mul_comm, add_comm]

theorem stress_posSemidef (a b : J → ℝ) : (stress a b).PosSemidef := by
  simpa only [stress, Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_self_mul_conjTranspose (frame a b)

theorem stress_trace (a b : J → ℝ) : (stress a b).trace = 2 * energy a b := by
  rw [stress, Matrix.trace_mul_comm, domain_gram, Matrix.trace_smul, Matrix.trace_one]
  simp only [Fintype.card_fin, Nat.cast_ofNat, smul_eq_mul, mul_comm]

/-- The stress is a scalar multiple of an orthogonal projection. -/
theorem stress_sq (a b : J → ℝ) : stress a b * stress a b = energy a b • stress a b := by
  unfold stress
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (frame a b)ᵀ, domain_gram,
    Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul]

variable [DecidableEq J]

/-- Every target component pays the same sharp one-half aperture. -/
theorem stress_aperture_half (a b : J → ℝ) :
    (((stress a b).trace / 2) • (1 : Matrix (J × Fin 2) (J × Fin 2) ℝ) -
      stress a b).PosSemidef := by
  have htrace : (stress a b).trace / 2 = energy a b := by rw [stress_trace]; ring
  rw [htrace]
  let C := energy a b • (1 : Matrix (J × Fin 2) (J × Fin 2) ℝ) - stress a b
  have hC : Cᵀ = C := by
    simp only [C, stress, Matrix.transpose_sub, Matrix.transpose_smul,
      Matrix.transpose_one, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hCsq : C * C = energy a b • C := by
    dsimp only [C]
    simp only [sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, stress_sq]
    module
  by_cases he : energy a b = 0
  · have hF : frame a b = 0 := by
      have hj (j : J) : (a j)^2 + (b j)^2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun i _ => add_nonneg (sq_nonneg (a i)) (sq_nonneg (b i)))).mp he j
          (Finset.mem_univ j)
      ext p k
      have ha : a p.1 = 0 := by nlinarith only [hj p.1, sq_nonneg (b p.1)]
      have hb : b p.1 = 0 := by nlinarith only [hj p.1, sq_nonneg (a p.1)]
      simp only [frame, ha, hb, neg_zero, ite_self, Matrix.zero_apply]
    simp only [he, zero_smul, stress, hF, Matrix.zero_mul, sub_zero]
    exact Matrix.PosSemidef.zero
  · have hE : 0 < energy a b := lt_of_le_of_ne (energy_nonneg a b) (Ne.symm he)
    have hpos : (C * C).PosSemidef := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, hC] using
        Matrix.posSemidef_self_mul_conjTranspose C
    have hscale := hpos.smul (inv_nonneg.mpr hE.le)
    rw [hCsq, smul_smul, inv_mul_cancel₀ he, one_smul] at hscale
    exact hscale

/-- Summing the sheet stresses preserves the aperture, even when their ranges differ. -/
theorem sum_stress_aperture_half {I : Type*} (s : Finset I)
    (a b : I → J → ℝ) :
    (((∑ i ∈ s, stress (a i) (b i)).trace / 2) •
        (1 : Matrix (J × Fin 2) (J × Fin 2) ℝ) -
      ∑ i ∈ s, stress (a i) (b i)).PosSemidef := by
  classical
  have hsum : (∑ i ∈ s,
      (((stress (a i) (b i)).trace / 2) •
        (1 : Matrix (J × Fin 2) (J × Fin 2) ℝ) - stress (a i) (b i))).PosSemidef := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using
        (Matrix.PosSemidef.zero : (0 : Matrix (J × Fin 2) (J × Fin 2) ℝ).PosSemidef)
    | @insert i s hi ih =>
        rw [Finset.sum_insert hi]
        exact (stress_aperture_half (a i) (b i)).add ih
  simpa only [Matrix.trace_sum, Finset.sum_div, Finset.sum_smul,
    Finset.sum_sub_distrib] using hsum

#print axioms stress_sq
#print axioms stress_aperture_half
#print axioms sum_stress_aperture_half

end HTGeometry.PlanarFamilyStress
