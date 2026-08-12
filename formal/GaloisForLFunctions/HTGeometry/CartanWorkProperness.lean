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

namespace GaloisForLFunctions.HTGeometry

open Matrix
open scoped ComplexOrder

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## A polynomial description of the work sublevel -/

/-- The trace of the inverse is a rational function of the entries: the adjugate trace over the
determinant.  This is what turns the work sublevel into a locus cut out by polynomials. -/
theorem trace_inv_eq_det_inv_mul_trace_adjugate (A : Matrix n n ℂ) :
    (A⁻¹).trace = (A.det)⁻¹ * (A.adjugate).trace := by
  rw [Matrix.inv_def, Matrix.trace_smul, Ring.inverse_eq_inv, smul_eq_mul]

/-- The polynomial that cuts out the work sublevel: for invertible `S` the inequality
`cartanWorkNumerator S C ≤ 0` is exactly `cartanWork S ≤ C`. -/
def cartanWorkNumerator (S : Matrix n n ℂ) (C : ℝ) : ℝ :=
  ((Sᴴ * S).det.re) * ((Sᴴ * S).trace.re - 2 * Fintype.card n - C)
    + ((Sᴴ * S).adjugate.trace.re)

theorem sublevel_algebra {t a d C r : ℝ} (hd : 0 < d) :
    (t + d⁻¹ * a - 2 * r ≤ C ↔ d * (t - 2 * r - C) + a ≤ 0) := by
  constructor
  · intro h
    have hmul := mul_le_mul_of_nonneg_left h hd.le
    have hda : d * (d⁻¹ * a) = a := by field_simp
    nlinarith [hmul, hda]
  · intro h
    have hd' : 0 < d⁻¹ := inv_pos.mpr hd
    have hmul := mul_le_mul_of_nonneg_left h hd'.le
    have hda : d⁻¹ * (d * (t - 2 * r - C)) = t - 2 * r - C := by field_simp
    nlinarith [hmul, hda]

/-- **The sublevel is a polynomial locus.**  On the invertible matrices the Cartan work sublevel
is cut out by one polynomial inequality in the entries, because the determinant of `SᴴS` is a
positive real there. -/
theorem cartanWork_le_iff_numerator {S : Matrix n n ℂ} (hS : IsUnit S) (C : ℝ) :
    cartanWork S ≤ C ↔ cartanWorkNumerator S C ≤ 0 := by
  have hpd := posDef_conjTranspose_mul_self hS
  have hH := hpd.1
  have hdetpos : 0 < (Sᴴ * S).det.re := by
    have hdet : (Sᴴ * S).det = ∏ i, ((hH.eigenvalues i : ℝ) : ℂ) := hH.det_eq_prod_eigenvalues
    have hre : (Sᴴ * S).det.re = ∏ i, hH.eigenvalues i := by
      rw [hdet, ← Complex.ofReal_prod, Complex.ofReal_re]
    rw [hre]
    exact Finset.prod_pos (fun i _ => hpd.eigenvalues_pos i)
  have htrinv : ((Sᴴ * S)⁻¹).trace.re
      = ((Sᴴ * S).det.re)⁻¹ * ((Sᴴ * S).adjugate.trace.re) := by
    rw [trace_inv_eq_det_inv_mul_trace_adjugate]
    have hdetreal : ((Sᴴ * S).det) = (((Sᴴ * S).det.re : ℝ) : ℂ) := by
      have hstar : star ((Sᴴ * S).det) = (Sᴴ * S).det := by
        rw [← Matrix.det_conjTranspose, hH.eq]
      exact (Complex.conj_eq_iff_re.mp hstar).symm
    rw [hdetreal, ← Complex.ofReal_inv, Complex.re_ofReal_mul]
    simp
  rw [cartanWork, htrinv, cartanWorkNumerator]
  exact sublevel_algebra hdetpos

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open Matrix
open scoped ComplexOrder

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Compactness of the work sublevel -/

/-- The work sublevel, as a subset of all matrices. -/
def cartanWorkSublevel (C : ℝ) : Set (Matrix n n ℂ) :=
  {S | IsUnit S ∧ cartanWork S ≤ C}

theorem isUnit_of_det_conjTranspose_mul_self_ne_zero {S : Matrix n n ℂ}
    (h : (Sᴴ * S).det ≠ 0) : IsUnit S := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro hdet
  apply h
  rw [Matrix.det_mul, hdet, mul_zero]

/-- **The sublevel is a polynomial locus, globally.**  With `K` the uniform determinant floor the
sublevel is exactly the intersection of two loci cut out by continuous functions of the entries. -/
theorem cartanWorkSublevel_eq [Nonempty n] {C : ℝ} (hCpos : 0 < C + 2 * Fintype.card n) :
    cartanWorkSublevel C
      = {S : Matrix n n ℂ | ((C + 2 * Fintype.card n)⁻¹) ^ Fintype.card n ≤ (Sᴴ * S).det.re}
        ∩ {S : Matrix n n ℂ | cartanWorkNumerator S C ≤ 0} := by
  have hKpos : (0 : ℝ) < ((C + 2 * Fintype.card n)⁻¹) ^ Fintype.card n :=
    pow_pos (inv_pos.mpr hCpos) _
  ext S
  constructor
  · rintro ⟨hS, hC⟩
    have hre : (Sᴴ * S).det.re = ∏ i, (posDef_conjTranspose_mul_self hS).1.eigenvalues i := by
      rw [(posDef_conjTranspose_mul_self hS).1.det_eq_prod_eigenvalues]
      norm_cast
    refine ⟨?_, (cartanWork_le_iff_numerator hS C).mp hC⟩
    show ((C + 2 * Fintype.card n)⁻¹) ^ Fintype.card n ≤ (Sᴴ * S).det.re
    rw [hre]
    exact det_ge_of_cartanWork_le hS hC
  · rintro ⟨hdet, hnum⟩
    have hdet' : ((C + 2 * Fintype.card n)⁻¹) ^ Fintype.card n ≤ (Sᴴ * S).det.re := hdet
    have hne : (Sᴴ * S).det ≠ 0 := by
      intro h0
      rw [h0] at hdet'
      simp only [Complex.zero_re] at hdet'
      linarith
    have hS : IsUnit S := isUnit_of_det_conjTranspose_mul_self_ne_zero hne
    exact ⟨hS, (cartanWork_le_iff_numerator hS C).mpr hnum⟩

/-- **The work sublevel is closed.** -/
theorem isClosed_cartanWorkSublevel [Nonempty n] {C : ℝ}
    (hCpos : 0 < C + 2 * Fintype.card n) :
    IsClosed (cartanWorkSublevel (n := n) C) := by
  have hgram : Continuous fun S : Matrix n n ℂ => Sᴴ * S :=
    (continuous_id.matrix_conjTranspose).mul continuous_id
  have hdet : Continuous fun S : Matrix n n ℂ => (Sᴴ * S).det.re :=
    Complex.continuous_re.comp hgram.matrix_det
  have hnum : Continuous fun S : Matrix n n ℂ => cartanWorkNumerator S C := by
    have htr : Continuous fun S : Matrix n n ℂ => (Sᴴ * S).trace.re :=
      Complex.continuous_re.comp hgram.matrix_trace
    have hadj : Continuous fun S : Matrix n n ℂ => (Sᴴ * S).adjugate.trace.re :=
      Complex.continuous_re.comp (hgram.matrix_adjugate.matrix_trace)
    have h := (hdet.mul (htr.sub (continuous_const (y := 2 * (Fintype.card n : ℝ) + C)))).add hadj
    refine h.congr (fun S => ?_)
    simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply, cartanWorkNumerator]
    ring
  rw [cartanWorkSublevel_eq hCpos]
  exact (isClosed_le continuous_const hdet).inter (isClosed_le hnum continuous_const)

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open Matrix
open scoped ComplexOrder

attribute [local instance] Matrix.seminormedAddCommGroup Matrix.normedAddCommGroup
  Matrix.normedSpace

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The work sublevel is bounded** in the entrywise sup norm, by the square root of the level. -/
theorem isBounded_cartanWorkSublevel (C : ℝ) :
    Bornology.IsBounded (cartanWorkSublevel (n := n) C) := by
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨Real.sqrt (C + 2 * Fintype.card n), fun S hS => ?_⟩
  obtain ⟨hunit, hle⟩ := hS
  have hsum := sum_norm_sq_le_of_cartanWork_le hunit hle
  rw [Metric.mem_closedBall, dist_zero_right]
  refine (Matrix.norm_le_iff (Real.sqrt_nonneg _)).mpr (fun j i => ?_)
  have hinner : ‖S j i‖ ^ 2 ≤ ∑ k, ‖S k i‖ ^ 2 :=
    Finset.single_le_sum (f := fun k => ‖S k i‖ ^ 2) (fun k _ => sq_nonneg _) (Finset.mem_univ j)
  have houter : (∑ k, ‖S k i‖ ^ 2) ≤ ∑ l, ∑ k, ‖S k l‖ ^ 2 :=
    Finset.single_le_sum (f := fun l => ∑ k, ‖S k l‖ ^ 2)
      (fun l _ => Finset.sum_nonneg (fun k _ => sq_nonneg _)) (Finset.mem_univ i)
  have hb : ‖S j i‖ ^ 2 ≤ C + 2 * Fintype.card n := by linarith
  have hnn : (0 : ℝ) ≤ C + 2 * Fintype.card n := le_trans (sq_nonneg _) hb
  calc ‖S j i‖ = Real.sqrt (‖S j i‖ ^ 2) := by
        rw [Real.sqrt_sq (norm_nonneg _)]
    _ ≤ Real.sqrt (C + 2 * Fintype.card n) := Real.sqrt_le_sqrt hb

/-- **Theorem 6.1, properness.**  Every Cartan work sublevel is compact. -/
theorem isCompact_cartanWorkSublevel [Nonempty n] {C : ℝ}
    (hCpos : 0 < C + 2 * Fintype.card n) :
    IsCompact (cartanWorkSublevel (n := n) C) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_cartanWorkSublevel hCpos)
    (isBounded_cartanWorkSublevel C)

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Proper radial selection -/

/-- **Theorem 7.1, the selection core.**  A Cartan ray has bounded work exactly when its radial
generator is neutral: the hyperbolic profile `4 ∑ sinh²(t λⱼ)` is bounded in `t` if and only if
every `λⱼ` vanishes.  A recurrent unitary phase therefore cannot keep the factorization history
closed unless the radial generator is zero. -/
theorem bounded_sinh_sq_sum_iff {ι : Type*} [Fintype ι] (lam : ι → ℝ) :
    (∃ C : ℝ, ∀ t : ℝ, 4 * ∑ j, Real.sinh (t * lam j) ^ 2 ≤ C) ↔ ∀ j, lam j = 0 := by
  constructor
  · rintro ⟨C, hC⟩ j
    by_contra hne
    obtain ⟨M, hM0, hMC⟩ : ∃ M : ℝ, 0 ≤ M ∧ C < M ^ 2 := by
      refine ⟨max C 0 + 1, by positivity, ?_⟩
      have h0 : (0 : ℝ) ≤ max C 0 := le_max_right _ _
      have h1 : C ≤ max C 0 := le_max_left _ _
      nlinarith
    have ht := hC (M / lam j)
    have harg : (M / lam j) * lam j = M := by field_simp
    have hge : M / 2 ≤ Real.sinh M := by
      rw [Real.sinh_eq]
      have h1 : M + 1 ≤ Real.exp M := Real.add_one_le_exp M
      have h2 : Real.exp (-M) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      linarith
    have hsq : M ^ 2 / 4 ≤ Real.sinh ((M / lam j) * lam j) ^ 2 := by
      rw [harg]
      nlinarith [hge, hM0]
    have hsingle : Real.sinh ((M / lam j) * lam j) ^ 2
        ≤ ∑ k, Real.sinh ((M / lam j) * lam k) ^ 2 :=
      Finset.single_le_sum (f := fun k => Real.sinh ((M / lam j) * lam k) ^ 2)
        (fun k _ => sq_nonneg _) (Finset.mem_univ j)
    nlinarith
  · intro hall
    refine ⟨0, fun t => ?_⟩
    have hz : ∀ j, Real.sinh (t * lam j) ^ 2 = 0 := by
      intro j
      rw [hall j, mul_zero, Real.sinh_zero]
      ring
    rw [Finset.sum_congr rfl (fun j _ => hz j)]
    simp

end

end GaloisForLFunctions.HTGeometry
