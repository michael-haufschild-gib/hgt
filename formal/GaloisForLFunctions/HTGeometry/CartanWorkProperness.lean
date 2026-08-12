import Mathlib
import GaloisForLFunctions.HTGeometry.HermitianInertia

/-!
# The Cartan work of an invertible operator

The Cartan work of an invertible `S` is the total Hilbert–Schmidt energy of `S` and of `S⁻¹`,
normalized by the rank:

`W(S) = tr(SᴴS) + tr((SᴴS)⁻¹) − 2r`.

Writing `A = SᴴS` and letting `μ` be its (positive) eigenvalues, `W(S) = ∑ⱼ (μⱼ − 1)²/μⱼ`.  Every
summand is nonnegative and vanishes exactly at `μⱼ = 1`, so the work is nonnegative and vanishes
exactly when `A = 1`, that is when `S` is unitary.  Bounding the work bounds both Hilbert–Schmidt
energies, which is the sublevel bound behind properness.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix
open scoped ComplexOrder

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem posDef_conjTranspose_mul_self {S : Matrix n n ℂ} (hS : IsUnit S) : (Sᴴ * S).PosDef := by
  have h1 : (1 : Matrix n n ℂ).PosDef := Matrix.PosDef.one
  have h := h1.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hS)
  simpa using h

/-- The trace of the inverse of a positive definite matrix is the sum of the inverse
eigenvalues. -/
theorem trace_inv_eq_sum_inv_eigenvalues {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (hne : ∀ i, hA.eigenvalues i ≠ 0) :
    (A⁻¹).trace = ∑ i, (((hA.eigenvalues i : ℝ) : ℂ))⁻¹ := by
  obtain ⟨D, hD⟩ : ∃ D : Matrix n n ℂ,
      D = diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) := ⟨_, rfl⟩
  set U : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ) with hUdef
  have hUU : Uᴴ * U = 1 := by
    rw [hUdef, ← Matrix.star_eq_conjTranspose]
    exact Unitary.coe_star_mul_self _
  have hUU' : U * Uᴴ = 1 := by
    rw [hUdef, ← Matrix.star_eq_conjTranspose]
    exact Unitary.coe_mul_star_self _
  have hd : Uᴴ * A * U = D := by
    rw [hD]
    exact conjTranspose_mul_mul_eigenvectorUnitary hA
  have hA' : A = U * D * Uᴴ := by
    calc A = U * Uᴴ * A * (U * Uᴴ) := by rw [hUU', Matrix.one_mul, Matrix.mul_one]
      _ = U * (Uᴴ * A * U) * Uᴴ := by simp [Matrix.mul_assoc]
      _ = U * D * Uᴴ := by rw [hd]
  have hUinv : U⁻¹ = Uᴴ := Matrix.inv_eq_right_inv hUU'
  have hUHinv : (Uᴴ)⁻¹ = U := Matrix.inv_eq_right_inv hUU
  have hinv : A⁻¹ = U * D⁻¹ * Uᴴ := by
    have hcong := congrArg (fun M : Matrix n n ℂ => M⁻¹) hA'
    rw [hcong, Matrix.mul_inv_rev, Matrix.mul_inv_rev, hUinv, hUHinv, Matrix.mul_assoc]
  have hDinv : D⁻¹ = diagonal (fun i => (((hA.eigenvalues i : ℝ) : ℂ))⁻¹) := by
    refine Matrix.inv_eq_right_inv ?_
    rw [hD, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    refine congrArg _ (funext fun i => ?_)
    have hi : ((hA.eigenvalues i : ℝ) : ℂ) ≠ 0 := by
      simpa using hne i
    field_simp
  rw [hinv, Matrix.trace_mul_cycle, hUU, Matrix.one_mul, hDinv, Matrix.trace_diagonal]

/-- The Cartan work of an invertible operator. -/
def cartanWork (S : Matrix n n ℂ) : ℝ :=
  (Sᴴ * S).trace.re + ((Sᴴ * S)⁻¹).trace.re - 2 * Fintype.card n

/-- **The exact Cartan work formula.**  The work is the eigenvalue sum `∑ (μ − 1)²/μ` of the
positive definite form `SᴴS`. -/
theorem cartanWork_eq_sum {S : Matrix n n ℂ} (hS : IsUnit S) :
    cartanWork S
      = ∑ i, ((posDef_conjTranspose_mul_self hS).1.eigenvalues i - 1) ^ 2 /
          (posDef_conjTranspose_mul_self hS).1.eigenvalues i := by
  have hpd := posDef_conjTranspose_mul_self hS
  have hH := hpd.1
  have hunit : IsUnit (Sᴴ * S) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul, Matrix.det_conjTranspose]
    exact ((Matrix.isUnit_iff_isUnit_det S).mp hS).map (starRingEnd ℂ) |>.mul
      ((Matrix.isUnit_iff_isUnit_det S).mp hS)
  have htr : (Sᴴ * S).trace = ∑ i, ((hH.eigenvalues i : ℝ) : ℂ) := hH.trace_eq_sum_eigenvalues
  have htrinv : ((Sᴴ * S)⁻¹).trace = ∑ i, (((hH.eigenvalues i : ℝ) : ℂ))⁻¹ :=
    trace_inv_eq_sum_inv_eigenvalues hH (fun i => (hpd.eigenvalues_pos i).ne')
  rw [cartanWork, htr, htrinv]
  have hre1 : (∑ i, ((hH.eigenvalues i : ℝ) : ℂ)).re = ∑ i, hH.eigenvalues i := by
    rw [Complex.re_sum]
    simp
  have hre2 : (∑ i, (((hH.eigenvalues i : ℝ) : ℂ))⁻¹).re = ∑ i, (hH.eigenvalues i)⁻¹ := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Complex.ofReal_inv, Complex.ofReal_re]
  rw [hre1, hre2, show (2 : ℝ) * Fintype.card n = ∑ _i : n, (2 : ℝ) by
    rw [Finset.sum_const, Finset.card_univ]; ring]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hpos : 0 < hH.eigenvalues i := hpd.eigenvalues_pos i
  field_simp
  ring

/-- **The Cartan work is nonnegative.** -/
theorem cartanWork_nonneg {S : Matrix n n ℂ} (hS : IsUnit S) : 0 ≤ cartanWork S := by
  rw [cartanWork_eq_sum hS]
  refine Finset.sum_nonneg (fun i _ => ?_)
  have hpos : 0 < (posDef_conjTranspose_mul_self hS).1.eigenvalues i :=
    (posDef_conjTranspose_mul_self hS).eigenvalues_pos i
  positivity

/-- **The zero locus of the Cartan work.**  The work vanishes exactly when every eigenvalue of
`SᴴS` is one. -/
theorem cartanWork_eq_zero_iff {S : Matrix n n ℂ} (hS : IsUnit S) :
    cartanWork S = 0 ↔ ∀ i, (posDef_conjTranspose_mul_self hS).1.eigenvalues i = 1 := by
  rw [cartanWork_eq_sum hS]
  have hterm : ∀ i : n, (0 : ℝ) ≤ ((posDef_conjTranspose_mul_self hS).1.eigenvalues i - 1) ^ 2 /
      (posDef_conjTranspose_mul_self hS).1.eigenvalues i := by
    intro i
    have hpos : 0 < (posDef_conjTranspose_mul_self hS).1.eigenvalues i :=
      (posDef_conjTranspose_mul_self hS).eigenvalues_pos i
    positivity
  constructor
  · intro hzero i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hterm j)).mp hzero i (Finset.mem_univ i)
    have hpos : 0 < (posDef_conjTranspose_mul_self hS).1.eigenvalues i :=
      (posDef_conjTranspose_mul_self hS).eigenvalues_pos i
    have hnum : ((posDef_conjTranspose_mul_self hS).1.eigenvalues i - 1) ^ 2 = 0 := by
      field_simp at hi
      simpa using hi
    have := pow_eq_zero_iff (n := 2) (by omega) |>.mp hnum
    linarith [sub_eq_zero.mp this]
  · intro hall
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [hall i]
    norm_num

/-- **The sublevel bound.**  A bound on the Cartan work bounds both Hilbert–Schmidt energies,
which is the boundedness half of properness. -/
theorem trace_le_of_cartanWork_le {S : Matrix n n ℂ} (hS : IsUnit S) {C : ℝ}
    (hC : cartanWork S ≤ C) :
    (Sᴴ * S).trace.re ≤ C + 2 * Fintype.card n ∧
      ((Sᴴ * S)⁻¹).trace.re ≤ C + 2 * Fintype.card n := by
  have hpd := posDef_conjTranspose_mul_self hS
  have hH := hpd.1
  have hunit : IsUnit (Sᴴ * S) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul, Matrix.det_conjTranspose]
    exact ((Matrix.isUnit_iff_isUnit_det S).mp hS).map (starRingEnd ℂ) |>.mul
      ((Matrix.isUnit_iff_isUnit_det S).mp hS)
  have htr : (Sᴴ * S).trace.re = ∑ i, hH.eigenvalues i := by
    rw [hH.trace_eq_sum_eigenvalues, Complex.re_sum]
    simp
  have htrinv : ((Sᴴ * S)⁻¹).trace.re = ∑ i, (hH.eigenvalues i)⁻¹ := by
    rw [trace_inv_eq_sum_inv_eigenvalues hH (fun i => (hpd.eigenvalues_pos i).ne'), Complex.re_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Complex.ofReal_inv, Complex.ofReal_re]
  have hnn1 : 0 ≤ ∑ i, hH.eigenvalues i :=
    Finset.sum_nonneg (fun i _ => (hpd.eigenvalues_pos i).le)
  have hnn2 : 0 ≤ ∑ i, (hH.eigenvalues i)⁻¹ :=
    Finset.sum_nonneg (fun i _ => (inv_pos.mpr (hpd.eigenvalues_pos i)).le)
  rw [cartanWork, htr, htrinv] at hC
  constructor
  · rw [htr]
    linarith
  · rw [htrinv]
    linarith

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open Matrix
open scoped ComplexOrder

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## The sublevel is bounded and stays away from the kernel -/

omit [DecidableEq n] in
/-- The trace of `SᴴS` is the Hilbert–Schmidt energy of `S`. -/
theorem trace_conjTranspose_mul_self_re (S : Matrix n n ℂ) :
    (Sᴴ * S).trace.re = ∑ i, ∑ j, ‖S j i‖ ^ 2 := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hterm : star (S j i) * S j i = ((‖S j i‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
  rw [hterm, Complex.ofReal_re]

/-- **Hilbert–Schmidt bound on a work sublevel.**  Bounding the Cartan work bounds every entry
energy of `S`. -/
theorem sum_norm_sq_le_of_cartanWork_le {S : Matrix n n ℂ} (hS : IsUnit S) {C : ℝ}
    (hC : cartanWork S ≤ C) :
    ∑ i, ∑ j, ‖S j i‖ ^ 2 ≤ C + 2 * Fintype.card n := by
  rw [← trace_conjTranspose_mul_self_re]
  exact (trace_le_of_cartanWork_le hS hC).1

/-- **The spectrum on a work sublevel is trapped in a compact interval away from zero.** -/
theorem eigenvalue_bounds_of_cartanWork_le {S : Matrix n n ℂ} (hS : IsUnit S) {C : ℝ}
    (hC : cartanWork S ≤ C) (i : n) :
    (C + 2 * Fintype.card n)⁻¹ ≤ (posDef_conjTranspose_mul_self hS).1.eigenvalues i ∧
      (posDef_conjTranspose_mul_self hS).1.eigenvalues i ≤ C + 2 * Fintype.card n := by
  have hpd := posDef_conjTranspose_mul_self hS
  have hH := hpd.1
  have hpos : ∀ j, 0 < hH.eigenvalues j := fun j => hpd.eigenvalues_pos j
  have htr : (Sᴴ * S).trace.re = ∑ j, hH.eigenvalues j := by
    rw [hH.trace_eq_sum_eigenvalues, Complex.re_sum]
    simp
  have htrinv : ((Sᴴ * S)⁻¹).trace.re = ∑ j, (hH.eigenvalues j)⁻¹ := by
    rw [trace_inv_eq_sum_inv_eigenvalues hH (fun j => (hpos j).ne'), Complex.re_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Complex.ofReal_inv, Complex.ofReal_re]
  obtain ⟨hb1, hb2⟩ := trace_le_of_cartanWork_le hS hC
  rw [htr] at hb1
  rw [htrinv] at hb2
  have hupper : hH.eigenvalues i ≤ C + 2 * Fintype.card n :=
    le_trans (Finset.single_le_sum (fun j _ => (hpos j).le) (Finset.mem_univ i)) hb1
  have hinvle : (hH.eigenvalues i)⁻¹ ≤ C + 2 * Fintype.card n :=
    le_trans (Finset.single_le_sum (fun j _ => (inv_pos.mpr (hpos j)).le) (Finset.mem_univ i)) hb2
  refine ⟨?_, hupper⟩
  have hCpos : 0 < C + 2 * Fintype.card n :=
    lt_of_lt_of_le (inv_pos.mpr (hpos i)) hinvle
  rw [inv_le_comm₀ hCpos (hpos i)]
  exact hinvle

/-- **No kernel in the limit.**  On a work sublevel the positive form `SᴴS` has determinant bounded
below by a constant depending only on the level and the rank, so the sublevel closure cannot meet
the singular locus. -/
theorem det_ge_of_cartanWork_le [Nonempty n] {S : Matrix n n ℂ} (hS : IsUnit S) {C : ℝ}
    (hC : cartanWork S ≤ C) :
    ((C + 2 * Fintype.card n)⁻¹) ^ Fintype.card n
      ≤ ∏ i, (posDef_conjTranspose_mul_self hS).1.eigenvalues i := by
  have hpd := posDef_conjTranspose_mul_self hS
  have hCpos : 0 < C + 2 * Fintype.card n := by
    have h := (eigenvalue_bounds_of_cartanWork_le hS hC (Classical.arbitrary n)).2
    exact lt_of_lt_of_le (hpd.eigenvalues_pos _) h
  calc ((C + 2 * Fintype.card n)⁻¹) ^ Fintype.card n
      = ∏ _i : n, (C + 2 * Fintype.card n)⁻¹ := by
        rw [Finset.prod_const, Finset.card_univ]
    _ ≤ ∏ i, hpd.1.eigenvalues i :=
        Finset.prod_le_prod (fun i _ => (inv_pos.mpr hCpos).le)
          (fun i _ => (eigenvalue_bounds_of_cartanWork_le hS hC i).1)

end

end GaloisForLFunctions.HTGeometry
