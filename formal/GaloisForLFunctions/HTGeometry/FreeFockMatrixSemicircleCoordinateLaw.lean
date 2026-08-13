import GaloisForLFunctions.HTGeometry.MatrixSemicircleAnalyticLaw
import GaloisForLFunctions.HTGeometry.StieltjesAtomMassBoundary

/-!
# Coordinate spectral laws for finite matrix semicircles

The normalized trace law forgets the diagonal matrix-valued Cauchy transform needed by the
atom audit.  This file constructs, from the same exact Fock moments, the compact probability law
seen by each internal basis vector.  No operator-algebraic spectral theorem is assumed: Hamburger
existence, the explicit Fock positivity identity, and the established compact moment bound suffice.
-/

open scoped BigOperators Matrix ENNReal
open Matrix MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]

/-- Vacuum moment seen from one internal matrix coordinate. -/
def freeFockCoordinateMoment (A : K → Matrix I I ℂ) (i : I) (n : ℕ) : ℝ :=
  (freeFockPower A i n (i, [])).re

omit [DecidableEq I] [DecidableEq K] in
@[simp]
theorem freeFockCoordinateMoment_zero (A : K → Matrix I I ℂ) (i : I) :
    freeFockCoordinateMoment A i 0 = 1 := by
  simp [freeFockCoordinateMoment, freeFockPower, freeFockVacuum]

theorem momentInner_freeFockCoordinateMoment_eq
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (i : I) (p : Polynomial ℝ) :
    HTGeometry.momentInner (freeFockCoordinateMoment A i) p p =
      (freeFockInner (freeFockPolynomialVector A p i)
        (freeFockPolynomialVector A p i)).re := by
  rw [momentInner_eq_double_support_sum,
    freeFockInner_polynomialVector_self A hA]
  simp only [freeFockCoordinateMoment]
  have hre (s : Finset ℕ) (f : ℕ → ℂ) :
      (∑ n ∈ s, f n).re = ∑ n ∈ s, (f n).re := by
    exact map_sum Complex.reCLM f s
  simp_rw [hre]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]

theorem freeFockCoordinateMoment_positiveMomentForm
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (i : I) :
    HTGeometry.PositiveMomentForm (freeFockCoordinateMoment A i) := by
  letI : Nonempty I := ⟨i⟩
  constructor
  intro p hp
  rw [momentInner_freeFockCoordinateMoment_eq A hA]
  exact re_freeFockInner_self_pos _
    (freeFockPolynomialVector_ne_zero A hA hker p hp i)

theorem re_freeFockInner_self_le_finsuppL1_sq
    {I K : Type*} (x : FreeFockVector I K) :
    (freeFockInner x x).re ≤ finsuppL1 x ^ 2 := by
  rw [re_freeFockInner_self_eq_sum_normSq, finsuppL1, Finsupp.sum]
  simp_rw [← Complex.sq_norm]
  exact Finset.sum_sq_le_sq_sum_of_nonneg (R := ℝ) fun _ _ ↦ norm_nonneg _

theorem freeFockCoordinateMoment_even_le_radius
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (i : I) (n : ℕ) :
    freeFockCoordinateMoment A i (2 * n) ≤ freeFockSpectralRadius A ^ (2 * n) := by
  have hm : freeFockCoordinateMoment A i (2 * n) =
      (freeFockInner (freeFockPower A i n) (freeFockPower A i n)).re := by
    rw [freeFockCoordinateMoment, show 2 * n = n + n by omega,
      ← freeFockInner_power_power A hA n n i i]
  rw [hm]
  calc
    (freeFockInner (freeFockPower A i n) (freeFockPower A i n)).re ≤
        finsuppL1 (freeFockPower A i n) ^ 2 :=
      re_freeFockInner_self_le_finsuppL1_sq _
    _ ≤ (2 * matrixFamilyEntryL1 A) ^ (2 * n) := by
      have hpow := pow_le_pow_left₀ (finsuppL1_nonneg (freeFockPower A i n))
        (finsuppL1_freeFockPower_le A i n) 2
      simpa [pow_mul, mul_comm] using hpow
    _ ≤ freeFockSpectralRadius A ^ (2 * n) := by
      exact pow_le_pow_left₀
        (mul_nonneg (by positivity) (matrixFamilyEntryL1_nonneg A))
        (by simp [freeFockSpectralRadius]) _

/-- Compact coordinate law selected from its exact Fock moment sequence. -/
noncomputable def freeFockCoordinateSpectralLaw
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (i : I) : ProbabilityMeasure ℝ :=
  Classical.choose (HTGeometry.exists_hasHamburgerMoments_of_moment_zero_eq_one
    (freeFockCoordinateMoment_positiveMomentForm A hA hker i)
    (freeFockCoordinateMoment_zero A i))

theorem freeFockCoordinateSpectralLaw_hasMoments
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (i : I) :
    HasHamburgerMoments (freeFockCoordinateMoment A i)
      (freeFockCoordinateSpectralLaw A hA hker i : Measure ℝ) :=
  Classical.choose_spec (HTGeometry.exists_hasHamburgerMoments_of_moment_zero_eq_one
    (freeFockCoordinateMoment_positiveMomentForm A hA hker i)
    (freeFockCoordinateMoment_zero A i))

theorem freeFockCoordinateSpectralLaw_carried
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (i : I) :
    (freeFockCoordinateSpectralLaw A hA hker i : Measure ℝ)
      (Set.Icc (-freeFockSpectralRadius A) (freeFockSpectralRadius A))ᶜ = 0 := by
  let mu : Measure ℝ := freeFockCoordinateSpectralLaw A hA hker i
  let R := freeFockSpectralRadius A
  have hR : 0 < R := freeFockSpectralRadius_pos A
  let f : ℝ → ℝ := fun x ↦ (x / R) ^ 2
  have hfmeas : Measurable f := by fun_prop
  have hfnn : ∀ x, 0 ≤ f x := fun x ↦ sq_nonneg _
  have hfeq (x : ℝ) (n : ℕ) : f x ^ n = R⁻¹ ^ (2 * n) * x ^ (2 * n) := by
    dsimp only [f]
    rw [pow_mul, div_pow, inv_pow]
    ring
  have hmu := freeFockCoordinateSpectralLaw_hasMoments A hA hker i
  have hint : ∀ n : ℕ, Integrable (fun x ↦ f x ^ n) mu := by
    intro n
    refine ((hmu (2 * n)).1.const_mul (R⁻¹ ^ (2 * n))).congr
      (Filter.Eventually.of_forall fun x ↦ (hfeq x n).symm)
  have hbound : ∀ n : ℕ, ∫ x, f x ^ n ∂mu ≤ 1 := by
    intro n
    rw [integral_congr_ae (Filter.Eventually.of_forall fun x ↦ hfeq x n),
      integral_const_mul, (hmu (2 * n)).2]
    have hm := freeFockCoordinateMoment_even_le_radius A hA i n
    change R⁻¹ ^ (2 * n) * freeFockCoordinateMoment A i (2 * n) ≤ 1
    calc
      R⁻¹ ^ (2 * n) * freeFockCoordinateMoment A i (2 * n) ≤
          R⁻¹ ^ (2 * n) * R ^ (2 * n) :=
        mul_le_mul_of_nonneg_left hm (pow_nonneg (inv_nonneg.mpr hR.le) _)
      _ = 1 := by rw [← mul_pow, inv_mul_cancel₀ hR.ne', one_pow]
  have hnull : ∀ k : ℕ, mu {x | 1 + 1 / (k + 1 : ℝ) ≤ f x} = 0 := by
    intro k
    apply HTGeometry.measure_ge_eq_zero_of_pow_integral_le hfmeas hfnn hint hbound
    have : (0 : ℝ) < 1 / (k + 1 : ℝ) := by positivity
    linarith
  have hcover : (Set.Icc (-R) R)ᶜ ⊆
      ⋃ k : ℕ, {x | 1 + 1 / (k + 1 : ℝ) ≤ f x} := by
    intro x hx
    have hgt : 1 < f x := by
      simpa [f] using
        (HTGeometry.sq_gt_one_iff_notMem_Icc (c := 0) hR).mpr (by simpa using hx)
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (by linarith : (0 : ℝ) < f x - 1)
    exact Set.mem_iUnion.mpr ⟨k, by simp only [Set.mem_setOf_eq]; linarith⟩
  exact measure_mono_null hcover (measure_iUnion_null hnull)

/-! ## Monomial coefficient families -/

/-- Every column of every coefficient matrix has at most one nonzero entry. -/
def MatrixFamilyHasSubsingletonColumns (A : K → Matrix I I ℂ) : Prop :=
  ∀ k j i l, A k i j ≠ 0 → A k l j ≠ 0 → i = l

omit [DecidableEq K] in
theorem matrixSemicircleCovariance_diagonal_of_subsingletonColumns
    (A : K → Matrix I I ℂ) (hmono : MatrixFamilyHasSubsingletonColumns A)
    (d : I → ℂ) :
    matrixSemicircleCovariance A (Matrix.diagonal d) =
      Matrix.diagonal (fun i ↦ ∑ k : K, ∑ j : I,
        A k i j * d j * star (A k i j)) := by
  ext i l
  simp only [matrixSemicircleCovariance, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.diagonal_apply, Matrix.conjTranspose_apply]
  by_cases hil : i = l
  · subst l
    simp
  · rw [if_neg hil]
    apply Finset.sum_eq_zero
    intro k hk
    apply Finset.sum_eq_zero
    intro j hj
    simp only [mul_ite, mul_zero]
    by_cases hij : A k i j = 0
    · simp [hij]
    · have hlj : A k l j = 0 := by
        by_contra hne
        exact hil (hmono k j i l hij hne)
      simp [hlj]

omit [DecidableEq K] in
theorem matrixDysonFormalCoeff_diagonal_of_subsingletonColumns
    (A : K → Matrix I I ℂ) (hmono : MatrixFamilyHasSubsingletonColumns A) :
    ∀ n : ℕ, matrixDysonFormalCoeff A n =
      Matrix.diagonal (fun i ↦ matrixDysonFormalCoeff A n i i) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          ext i j
          simp [matrixDysonFormalCoeff, Matrix.one_apply]
      | succ n =>
          rw [matrixDysonFormalCoeff]
          have hterm : ∀ p : Fin (n + 1),
              matrixSemicircleCovariance A (matrixDysonFormalCoeff A p) *
                  matrixDysonFormalCoeff A (n - p) =
                Matrix.diagonal (fun i ↦
                  (matrixSemicircleCovariance A (matrixDysonFormalCoeff A p) *
                    matrixDysonFormalCoeff A (n - p)) i i) := by
            intro p
            have hp : (p : ℕ) < n + 1 := p.isLt
            have hnp : n - (p : ℕ) < n + 1 := by omega
            rw [ih p hp, ih (n - p) hnp,
              matrixSemicircleCovariance_diagonal_of_subsingletonColumns A hmono]
            rw [Matrix.diagonal_mul_diagonal]
            congr 1
            funext i
            rw [Matrix.diagonal_apply, if_pos rfl]
          calc
            (∑ p : Fin (n + 1),
                matrixSemicircleCovariance A (matrixDysonFormalCoeff A p) *
                  matrixDysonFormalCoeff A (n - p)) =
                ∑ p : Fin (n + 1), Matrix.diagonal (fun i ↦
                  (matrixSemicircleCovariance A (matrixDysonFormalCoeff A p) *
                    matrixDysonFormalCoeff A (n - p)) i i) := by
              exact Finset.sum_congr rfl fun p _ ↦ hterm p
            _ = Matrix.diagonal (fun i ↦ ∑ p : Fin (n + 1),
                  (matrixSemicircleCovariance A (matrixDysonFormalCoeff A p) *
                    matrixDysonFormalCoeff A (n - p)) i i) := by
              ext i j
              by_cases hij : i = j
              · subst j
                simp only [Matrix.sum_apply, Matrix.diagonal_apply, if_true]
              · simp only [Matrix.sum_apply, Matrix.diagonal_apply, if_neg hij,
                  Finset.sum_const_zero]
            _ = Matrix.diagonal (fun i ↦
                (∑ p : Fin (n + 1),
                  matrixSemicircleCovariance A (matrixDysonFormalCoeff A p) *
                    matrixDysonFormalCoeff A (n - p)) i i) := by
              congr 1
              funext i
              rw [Matrix.sum_apply]

omit [DecidableEq K] in
theorem matrixDysonResolventSeries_offdiag_of_subsingletonColumns
    (A : K → Matrix I I ℂ) (hmono : MatrixFamilyHasSubsingletonColumns A)
    {i j : I} (hij : i ≠ j) :
    matrixDysonResolventSeries A i j = 0 := by
  ext n
  rw [matrixDysonResolventSeries_coeff]
  split
  · rw [matrixDysonFormalCoeff_diagonal_of_subsingletonColumns A hmono]
    simp [hij]
  · simp

omit [DecidableEq K] in
theorem matrixDysonResolventSeries_diagonal_of_subsingletonColumns
    (A : K → Matrix I I ℂ) (hmono : MatrixFamilyHasSubsingletonColumns A) :
    matrixDysonResolventSeries A =
      Matrix.diagonal (fun i ↦ matrixDysonResolventSeries A i i) := by
  ext i j
  by_cases hij : i = j
  · subst j
    rw [Matrix.diagonal_apply, if_pos rfl]
  · rw [matrixDysonResolventSeries_offdiag_of_subsingletonColumns A hmono hij,
      Matrix.diagonal_apply, if_neg hij]

/-- Squared-entry variance profile of a Hermitian monomial coefficient family. -/
def matrixFamilySquaredEntryWeight (A : K → Matrix I I ℂ) (i j : I) : ℝ :=
  ∑ k : K, Complex.normSq (A k i j)

omit [Fintype I] [DecidableEq I] [DecidableEq K] in
theorem matrixFamilySquaredEntryWeight_nonneg
    (A : K → Matrix I I ℂ) (i j : I) :
    0 ≤ matrixFamilySquaredEntryWeight A i j :=
  Finset.sum_nonneg fun _ _ ↦ Complex.normSq_nonneg _

omit [Fintype I] [DecidableEq I] [DecidableEq K] in
theorem matrixFamilySquaredEntryWeight_symm
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k) (i j : I) :
    matrixFamilySquaredEntryWeight A i j = matrixFamilySquaredEntryWeight A j i := by
  apply Finset.sum_congr rfl
  intro k hk
  have hentry := congr_fun (congr_fun (hA k) j) i
  rw [Matrix.conjTranspose_apply] at hentry
  calc
    Complex.normSq (A k i j) = Complex.normSq (star (A k i j)) :=
      (Complex.normSq_conj _).symm
    _ = Complex.normSq (A k j i) := by rw [hentry]

omit [DecidableEq I] [DecidableEq K] in
theorem matrixSemicircleCovariancePowerSeries_diagonal_entry
    (A : K → Matrix I I ℂ) (H : Matrix I I (PowerSeries ℂ))
    (hH : ∀ p q, p ≠ q → H p q = 0) (i : I) :
    matrixSemicircleCovariancePowerSeries A H i i =
      ∑ j : I, PowerSeries.C ((matrixFamilySquaredEntryWeight A i j : ℝ) : ℂ) *
        H j j := by
  simp only [matrixSemicircleCovariancePowerSeries, Matrix.sum_apply,
    Matrix.mul_apply, constantPowerSeriesMatrix, Matrix.conjTranspose_apply]
  calc
    (∑ k : K, ∑ q : I, (∑ p : I,
        PowerSeries.C (A k i p) * H p q) * PowerSeries.C (star (A k i q))) =
        ∑ k : K, ∑ q : I,
          (PowerSeries.C (A k i q) * H q q) *
            PowerSeries.C (star (A k i q)) := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro q hq
      congr 1
      rw [Finset.sum_eq_single q]
      · intro p hp hpq
        rw [hH p q hpq]
        simp
      · intro hqnot
        exact (hqnot (Finset.mem_univ q)).elim
    _ = ∑ q : I, ∑ k : K,
          PowerSeries.C (((Complex.normSq (A k i q) : ℝ) : ℂ)) * H q q := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro k hk
      rw [Complex.normSq_eq_conj_mul_self]
      simp only [map_mul]
      simp only [starRingEnd_apply]
      ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [← Finset.sum_mul]
      congr 1
      simp [matrixFamilySquaredEntryWeight]

omit [DecidableEq K] in
theorem matrixSemicircleCovariancePowerSeries_diagonal_of_subsingletonColumns
    (A : K → Matrix I I ℂ) (hmono : MatrixFamilyHasSubsingletonColumns A)
    (H : Matrix I I (PowerSeries ℂ)) (hH : ∀ p q, p ≠ q → H p q = 0) :
    matrixSemicircleCovariancePowerSeries A H =
      Matrix.diagonal (fun i ↦
        ∑ j : I, PowerSeries.C ((matrixFamilySquaredEntryWeight A i j : ℝ) : ℂ) *
          H j j) := by
  apply Matrix.ext
  intro i l
  by_cases hil : i = l
  · subst l
    rw [matrixSemicircleCovariancePowerSeries_diagonal_entry A H hH,
      Matrix.diagonal_apply, if_pos rfl]
  · apply PowerSeries.ext
    intro n
    have hcoeff : matrixPowerSeriesCoeff H n =
        Matrix.diagonal (fun p ↦ PowerSeries.coeff n (H p p)) := by
      ext p q
      simp only [matrixPowerSeriesCoeff]
      by_cases hpq : p = q
      · subst q
        rw [Matrix.diagonal_apply, if_pos rfl]
      · rw [hH p q hpq, map_zero, Matrix.diagonal_apply, if_neg hpq]
    have hcov := matrixPowerSeriesCoeff_covariance A H n
    have hentry := congr_fun (congr_fun hcov i) l
    rw [hcoeff,
      matrixSemicircleCovariance_diagonal_of_subsingletonColumns A hmono,
      Matrix.diagonal_apply, if_neg hil] at hentry
    rw [Matrix.diagonal_apply, if_neg hil, map_zero]
    change PowerSeries.coeff n
      (matrixSemicircleCovariancePowerSeries A H i l) = 0
    change PowerSeries.coeff n
      (matrixSemicircleCovariancePowerSeries A H i l) = 0 at hentry
    exact hentry

omit [DecidableEq K] in
theorem matrixDysonResolventSeries_coordinate_eq
    (A : K → Matrix I I ℂ)
    (hmono : MatrixFamilyHasSubsingletonColumns A) (i : I) :
    matrixDysonResolventSeries A i i = 1 + PowerSeries.X ^ 2 *
      (∑ j : I, PowerSeries.C ((matrixFamilySquaredEntryWeight A i j : ℝ) : ℂ) *
        matrixDysonResolventSeries A j j) * matrixDysonResolventSeries A i i := by
  let R := matrixDysonResolventSeries A
  have hCov : matrixSemicircleCovariancePowerSeries A R =
      Matrix.diagonal (fun l ↦
        ∑ j : I, PowerSeries.C ((matrixFamilySquaredEntryWeight A l j : ℝ) : ℂ) *
          R j j) :=
    matrixSemicircleCovariancePowerSeries_diagonal_of_subsingletonColumns A hmono R
      (fun p q hpq ↦ matrixDysonResolventSeries_offdiag_of_subsingletonColumns
        A hmono hpq)
  have h := congr_fun (congr_fun (matrixDysonResolventSeries_eq A) i) i
  change R i i =
    ((1 : Matrix I I (PowerSeries ℂ)) + PowerSeries.X ^ 2 •
      (matrixSemicircleCovariancePowerSeries A R * R)) i i at h
  change R i i = _
  rw [h, hCov]
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_apply, Matrix.diagonal_apply, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

/-! ## Coordinate Stieltjes transforms and the scalar Dyson system -/

theorem freeFockPower_diag_eq_ofReal_re
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (i : I) (n : ℕ) :
    freeFockPower A i n (i, []) =
      ((freeFockPower A i n (i, [])).re : ℂ) := by
  obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' n
  · subst n
    rw [show 2 * m = m + m by omega,
      ← freeFockInner_power_power A hA m m i i]
    exact freeFockInner_self_eq_ofReal_re _
  · subst n
    rw [freeFockPower_vacuumCoefficient_odd A hA]
    simp

theorem coeff_matrixDysonResolventSeries_eq_freeFockPower
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (i : I) (n : ℕ) :
    PowerSeries.coeff n (matrixDysonResolventSeries A i i) =
      freeFockPower A i n (i, []) := by
  rw [matrixDysonResolventSeries_coeff,
    freeFockPower_vacuumCoefficient A hA]

theorem coeff_matrixDysonResolventSeries_eq_coordinateMoment
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (i : I) (n : ℕ) :
    PowerSeries.coeff n (matrixDysonResolventSeries A i i) =
      (freeFockCoordinateMoment A i n : ℂ) := by
  rw [coeff_matrixDysonResolventSeries_eq_freeFockPower A hA]
  exact freeFockPower_diag_eq_ofReal_re A hA i n

theorem matrixDysonResolventSeries_coordinate_absoluteSummableAt
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (i : I) (u : ℂ) (hu : freeFockSpectralRadius A * ‖u‖ < 1) :
    (matrixDysonResolventSeries A i i).AbsoluteSummableAt u := by
  let q : ℝ := freeFockSpectralRadius A * ‖u‖
  have hq0 : 0 ≤ q := mul_nonneg (freeFockSpectralRadius_pos A).le (norm_nonneg _)
  have hqnorm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    exact hu
  rw [PowerSeries.AbsoluteSummableAt]
  apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ ?_)
    (summable_geometric_of_norm_lt_one hqnorm)
  rw [norm_mul, coeff_matrixDysonResolventSeries_eq_freeFockPower A hA,
    norm_pow]
  calc
    ‖freeFockPower A i n (i, [])‖ * ‖u‖ ^ n ≤
        (2 * matrixFamilyEntryL1 A) ^ n * ‖u‖ ^ n := by
      gcongr
      exact norm_freeFockPower_apply_le A i i [] n
    _ ≤ freeFockSpectralRadius A ^ n * ‖u‖ ^ n := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (norm_nonneg _) _)
      apply pow_le_pow_left₀
        (mul_nonneg (by positivity) (matrixFamilyEntryL1_nonneg A))
      rw [freeFockSpectralRadius]
      linarith
    _ = q ^ n := by rw [← mul_pow]

theorem compactMomentGeneratingFunction_freeFockCoordinate_eq_absoluteEval
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (i : I) (u : ℂ)
    (hu : ‖u‖ * freeFockSpectralRadius A < 1) :
    compactMomentGeneratingFunction
        (freeFockCoordinateSpectralLaw A hA hker i : Measure ℝ) u =
      (matrixDysonResolventSeries A i i).absoluteEval u := by
  let mu : Measure ℝ := freeFockCoordinateSpectralLaw A hA hker i
  have hseries := matrixDysonResolventSeries_coordinate_absoluteSummableAt
    A hA i u (by simpa [mul_comm] using hu)
  rw [compactMomentGeneratingFunction_eq_tsum mu _
    (freeFockCoordinateSpectralLaw_hasMoments A hA hker i)
    (freeFockSpectralRadius A) (freeFockSpectralRadius_pos A)
    (freeFockCoordinateSpectralLaw_carried A hA hker i) u hu,
    PowerSeries.absoluteEval]
  apply tsum_congr
  intro n
  rw [coeff_matrixDysonResolventSeries_eq_coordinateMoment A hA]

def freeFockCoordinateStieltjes
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (i : I) (z : ℂ) : ℂ :=
  ∫ x : ℝ, ((x : ℂ) - z)⁻¹
    ∂(freeFockCoordinateSpectralLaw A hA hker i : Measure ℝ)

theorem freeFockCoordinateStieltjes_eq_neg_mul_mgf
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (i : I) (u : ℂ) (hu : u ≠ 0) :
    freeFockCoordinateStieltjes A hA hker i u⁻¹ =
      -u * compactMomentGeneratingFunction
        (freeFockCoordinateSpectralLaw A hA hker i : Measure ℝ) u := by
  exact stieltjesTransform_inv_eq_neg_mul_compactMomentGeneratingFunction _ u hu

theorem freeFockCoordinateMGF_dyson
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A)
    (hmono : MatrixFamilyHasSubsingletonColumns A)
    (u : ℂ) (hu : ‖u‖ * freeFockSpectralRadius A < 1) (i : I) :
    let M := fun j ↦ compactMomentGeneratingFunction
      (freeFockCoordinateSpectralLaw A hA hker j : Measure ℝ) u
    M i = 1 + u ^ 2 *
      (∑ j : I, (matrixFamilySquaredEntryWeight A i j : ℝ) * M j) * M i := by
  dsimp only
  have hR : ∀ j : I,
      (matrixDysonResolventSeries A j j).AbsoluteSummableAt u := fun j ↦
    matrixDysonResolventSeries_coordinate_absoluteSummableAt A hA j u
      (by simpa [mul_comm] using hu)
  let F : I → PowerSeries ℂ := fun j ↦
    PowerSeries.C ((matrixFamilySquaredEntryWeight A i j : ℝ) : ℂ) *
      matrixDysonResolventSeries A j j
  have hF : ∀ j : I, (F j).AbsoluteSummableAt u := fun j ↦
    (PowerSeries.absoluteSummableAt_C _ _).mul (hR j)
  have hsum : (∑ j : I, F j).AbsoluteSummableAt u :=
    PowerSeries.AbsoluteSummableAt.sum Finset.univ F (fun j _ ↦ hF j)
  dsimp only [F] at hF hsum
  have hOne : (1 : PowerSeries ℂ).AbsoluteSummableAt u := by
    rw [PowerSeries.AbsoluteSummableAt]
    apply (hasSum_single 0 (fun n hn => ?_)).summable
    simp [PowerSeries.coeff_one, hn]
  have hEq := congrArg (fun f : PowerSeries ℂ ↦ f.absoluteEval u)
    (matrixDysonResolventSeries_coordinate_eq A hmono i)
  rw [PowerSeries.absoluteEval_add hOne
      (((PowerSeries.X_absoluteSummableAt u).pow 2).mul hsum |>.mul (hR i)),
    show (1 : PowerSeries ℂ).absoluteEval u = 1 by
      rw [PowerSeries.absoluteEval, tsum_eq_single 0]
      · simp
      · intro n hn
        simp [PowerSeries.coeff_one, hn],
    PowerSeries.absoluteEval_mul
      (((PowerSeries.X_absoluteSummableAt u).pow 2).mul hsum) (hR i),
    PowerSeries.absoluteEval_mul ((PowerSeries.X_absoluteSummableAt u).pow 2) hsum,
    PowerSeries.absoluteEval_pow (PowerSeries.X_absoluteSummableAt u),
    PowerSeries.absoluteEval_X,
    PowerSeries.absoluteEval_sum Finset.univ
      (fun j ↦ PowerSeries.C ((matrixFamilySquaredEntryWeight A i j : ℝ) : ℂ) *
        matrixDysonResolventSeries A j j) (fun j _ ↦ hF j)] at hEq
  simp only [PowerSeries.absoluteEval_mul
    (PowerSeries.absoluteSummableAt_C _ _) (hR _), PowerSeries.absoluteEval_C] at hEq
  simp_rw [← compactMomentGeneratingFunction_freeFockCoordinate_eq_absoluteEval
    A hA hker _ u hu] at hEq
  simpa using hEq

def freeFockCoordinateDysonResidual
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (i : I) (z : ℂ) : ℂ :=
  1 + freeFockCoordinateStieltjes A hA hker i z *
    (z + ∑ j : I, (matrixFamilySquaredEntryWeight A i j : ℝ) *
      freeFockCoordinateStieltjes A hA hker j z)

theorem freeFockCoordinateDysonResidual_exterior
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A)
    (hmono : MatrixFamilyHasSubsingletonColumns A)
    (z : ℂ) (hz : freeFockSpectralRadius A < ‖z‖) (i : I) :
    freeFockCoordinateDysonResidual A hA hker i z = 0 := by
  have hz0 : z ≠ 0 := fun hzero ↦ by
    rw [hzero, norm_zero] at hz
    linarith [freeFockSpectralRadius_pos A]
  let u : ℂ := z⁻¹
  have hu0 : u ≠ 0 := inv_ne_zero hz0
  have hu : ‖u‖ * freeFockSpectralRadius A < 1 := by
    rw [show u = z⁻¹ by rfl, norm_inv]
    simpa [div_eq_mul_inv, mul_comm] using
      (div_lt_one (norm_pos_iff.mpr hz0)).mpr hz
  have hM := freeFockCoordinateMGF_dyson A hA hker hmono u hu i
  let M : I → ℂ := fun j ↦ compactMomentGeneratingFunction
    (freeFockCoordinateSpectralLaw A hA hker j : Measure ℝ) u
  have hg : ∀ j : I,
      freeFockCoordinateStieltjes A hA hker j z = -u * M j := by
    intro j
    have h := freeFockCoordinateStieltjes_eq_neg_mul_mgf A hA hker j u hu0
    have huinv : u⁻¹ = z := by simp [u]
    simpa [M, huinv] using h
  change M i = 1 + u ^ 2 *
    (∑ x : I, (matrixFamilySquaredEntryWeight A i x : ℝ) * M x) * M i at hM
  simp only [freeFockCoordinateDysonResidual]
  simp_rw [hg]
  have huz : u * z = 1 := by simp [u, hz0]
  have hsumW :
      (∑ x : I, (matrixFamilySquaredEntryWeight A i x : ℝ) * (-u * M x)) =
        -u * ∑ x : I, (matrixFamilySquaredEntryWeight A i x : ℝ) * M x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hsumW]
  linear_combination -hM - (M i) * huz

theorem freeFockCoordinateDysonResidual_differentiableOn
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (i : I) :
    DifferentiableOn ℂ (freeFockCoordinateDysonResidual A hA hker i)
      {z : ℂ | 0 < z.im} := by
  intro z hz
  have hg : ∀ j : I, DifferentiableAt ℂ
      (freeFockCoordinateStieltjes A hA hker j) z := fun j ↦
    (HTGeometry.stieltjes_hasDerivAt z hz).differentiableAt
  have hsum : DifferentiableAt ℂ
      (fun w ↦ ∑ j : I, (matrixFamilySquaredEntryWeight A i j : ℝ) *
        freeFockCoordinateStieltjes A hA hker j w) z := by
    fun_prop
  exact ((hg i).mul (differentiableAt_id.add hsum)).const_add 1 |>.differentiableWithinAt

theorem freeFockCoordinateDysonResidual_upperHalfPlane
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A)
    (hmono : MatrixFamilyHasSubsingletonColumns A)
    (i : I) (z : ℂ) (hz : 0 < z.im) :
    freeFockCoordinateDysonResidual A hA hker i z = 0 := by
  let U : Set ℂ := {w | 0 < w.im}
  let z₀ : ℂ := (freeFockSpectralRadius A + 1) * Complex.I
  have hz₀U : z₀ ∈ U := by
    change 0 < z₀.im
    simp [z₀]
    linarith [freeFockSpectralRadius_pos A]
  have hz₀ext : freeFockSpectralRadius A < ‖z₀‖ := by
    dsimp [z₀]
    rw [norm_mul, show ((freeFockSpectralRadius A : ℂ) + 1) =
      ((freeFockSpectralRadius A + 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one,
      abs_of_pos (by linarith [freeFockSpectralRadius_pos A])]
    linarith
  have hseed : Filter.Eventually
      (fun w ↦ freeFockCoordinateDysonResidual A hA hker i w = 0) (nhds z₀) := by
    have hopen : IsOpen {w : ℂ | freeFockSpectralRadius A < ‖w‖} :=
      isOpen_lt continuous_const continuous_norm
    filter_upwards [hopen.mem_nhds hz₀ext] with w hw
    exact freeFockCoordinateDysonResidual_exterior A hA hker hmono w hw i
  have hanalytic : AnalyticOnNhd ℂ
      (freeFockCoordinateDysonResidual A hA hker i) U :=
    (freeFockCoordinateDysonResidual_differentiableOn A hA hker i).analyticOnNhd
      (isOpen_lt continuous_const Complex.continuous_im)
  have hzero : AnalyticOnNhd ℂ (fun _w : ℂ ↦ (0 : ℂ)) U := analyticOnNhd_const
  have hEq := hanalytic.eqOn_of_preconnected_of_eventuallyEq hzero
    (convex_halfSpace_im_gt 0).isPreconnected hz₀U hseed
  exact hEq hz

/-! ## Coordinate algebraicity and absolute continuity -/

theorem coeff_matrixDysonFormalSeries_eq_coordinateMoment_even
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (i : I) (n : ℕ) :
    PowerSeries.coeff n (matrixDysonFormalSeries A i i) =
      (freeFockCoordinateMoment A i (2 * n) : ℂ) := by
  rw [coeff_matrixDysonFormalSeries,
    ← freeFockPower_vacuumCoefficient_even A hA n i i]
  exact freeFockPower_diag_eq_ofReal_re A hA i (2 * n)

theorem matrixDysonFormalSeries_coordinate_coeff_bound
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (i : I) (n : ℕ) :
    ‖PowerSeries.coeff n (matrixDysonFormalSeries A i i)‖ ≤
      (freeFockSpectralRadius A ^ 2) ^ n := by
  rw [coeff_matrixDysonFormalSeries_eq_coordinateMoment_even A hA]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  have hnonneg : 0 ≤ freeFockCoordinateMoment A i (2 * n) := by
    rw [freeFockCoordinateMoment, show 2 * n = n + n by omega,
      ← freeFockInner_power_power A hA n n i i]
    exact re_freeFockInner_self_nonneg _
  rw [abs_of_nonneg hnonneg]
  simpa [pow_mul] using freeFockCoordinateMoment_even_le_radius A hA i n

theorem matrixDysonFormalSeries_coordinate_absoluteSummableAt
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (i : I) (u : ℂ) (hu : freeFockSpectralRadius A ^ 2 * ‖u‖ < 1) :
    (matrixDysonFormalSeries A i i).AbsoluteSummableAt u := by
  let q : ℝ := freeFockSpectralRadius A ^ 2 * ‖u‖
  have hq0 : 0 ≤ q := by positivity
  have hqnorm : ‖q‖ < 1 := by
    simpa [q, Real.norm_eq_abs, abs_of_nonneg hq0] using hu
  apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ ?_)
    (summable_geometric_of_norm_lt_one hqnorm)
  calc
    ‖PowerSeries.coeff n (matrixDysonFormalSeries A i i) * u ^ n‖ ≤
        (freeFockSpectralRadius A ^ 2) ^ n * ‖u ^ n‖ := by
      rw [norm_mul]
      gcongr
      exact matrixDysonFormalSeries_coordinate_coeff_bound A hA i n
    _ = q ^ n := by simp [q, norm_pow, mul_pow]

theorem freeFockCoordinateMoment_odd
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (i : I) (n : ℕ) :
    freeFockCoordinateMoment A i (2 * n + 1) = 0 := by
  rw [freeFockCoordinateMoment,
    freeFockPower_vacuumCoefficient_odd A hA n i i]
  simp

set_option maxHeartbeats 3000000 in
theorem compactMomentGeneratingFunction_freeFockCoordinate_eq_formalAbsoluteEval
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (i : I) (u : ℂ)
    (hu : ‖u‖ * freeFockSpectralRadius A < 1) :
    compactMomentGeneratingFunction
        (freeFockCoordinateSpectralLaw A hA hker i : Measure ℝ) u =
      (matrixDysonFormalSeries A i i).absoluteEval (u ^ 2) := by
  let R := freeFockSpectralRadius A
  have hR : 0 < R := freeFockSpectralRadius_pos A
  have hq0 : 0 ≤ ‖u‖ * R := mul_nonneg (norm_nonneg _) hR.le
  have hsq : R ^ 2 * ‖u ^ 2‖ < 1 := by
    rw [norm_pow]
    calc
      R ^ 2 * ‖u‖ ^ 2 = (‖u‖ * R) ^ 2 := by ring
      _ < 1 ^ 2 := (sq_lt_sq₀ hq0 zero_le_one).mpr hu
      _ = 1 := one_pow 2
  have habs := matrixDysonFormalSeries_coordinate_absoluteSummableAt
    A hA i (u ^ 2) hsq
  have heven : Summable (fun n : ℕ ↦
      (freeFockCoordinateMoment A i (2 * n) : ℂ) * u ^ (2 * n)) := by
    convert habs.summable using 1
    funext n
    rw [coeff_matrixDysonFormalSeries_eq_coordinateMoment_even A hA, pow_mul]
  have hodd : Summable (fun n : ℕ ↦
      (freeFockCoordinateMoment A i (2 * n + 1) : ℂ) * u ^ (2 * n + 1)) := by
    simp [freeFockCoordinateMoment_odd A hA]
  rw [compactMomentGeneratingFunction_eq_tsum _ _
    (freeFockCoordinateSpectralLaw_hasMoments A hA hker i)
    R hR (freeFockCoordinateSpectralLaw_carried A hA hker i) u hu]
  rw [← tsum_even_add_odd heven hodd]
  simp [freeFockCoordinateMoment_odd A hA]
  rw [PowerSeries.absoluteEval]
  apply tsum_congr
  intro n
  rw [coeff_matrixDysonFormalSeries_eq_coordinateMoment_even A hA, pow_mul]

theorem freeFockCoordinate_exterior_stieltjes_relation
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (i : I) :
    ∃ P : Polynomial (Polynomial ℂ), P.leadingCoeff ≠ 0 ∧
      ∀ z : ℂ, freeFockSpectralRadius A < ‖z‖ →
        reciprocalStieltjesRelation P
          (freeFockCoordinateSpectralLaw A hA hker i : Measure ℝ) z = 0 := by
  obtain ⟨P, hPlead, hPformal⟩ :=
    matrixDysonFormalSeries_exists_bivariateRelation A i i
  refine ⟨P, hPlead, fun z hz ↦ ?_⟩
  have hz0 : z ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hz
    linarith [freeFockSpectralRadius_pos A]
  let u : ℂ := z⁻¹
  have hu0 : u ≠ 0 := inv_ne_zero hz0
  have hu : ‖u‖ * freeFockSpectralRadius A < 1 := by
    change ‖z⁻¹‖ * freeFockSpectralRadius A < 1
    rw [norm_inv]
    simpa [div_eq_mul_inv, mul_comm] using
      (div_lt_one (norm_pos_iff.mpr hz0)).mpr hz
  have hM := compactMomentGeneratingFunction_freeFockCoordinate_eq_formalAbsoluteEval
    A hA hker i u hu
  have hrel := PowerSeries.polynomial_relation_absoluteEval P
    (matrixDysonFormalSeries A i i) (u ^ 2)
    (matrixDysonFormalSeries_coordinate_absoluteSummableAt A hA i (u ^ 2) (by
      have hR := freeFockSpectralRadius_pos A
      have hq0 : 0 ≤ ‖u‖ * freeFockSpectralRadius A :=
        mul_nonneg (norm_nonneg _) hR.le
      rw [norm_pow]
      calc
        freeFockSpectralRadius A ^ 2 * ‖u‖ ^ 2 =
            (‖u‖ * freeFockSpectralRadius A) ^ 2 := by ring
        _ < 1 ^ 2 := (sq_lt_sq₀ hq0 zero_le_one).mpr hu
        _ = 1 := one_pow 2)) hPformal
  have hS := freeFockCoordinateStieltjes_eq_neg_mul_mgf A hA hker i u hu0
  have hzinv : u⁻¹ = z := by simp [u]
  rw [hzinv] at hS
  have hMstieltjes :
      compactMomentGeneratingFunction
          (freeFockCoordinateSpectralLaw A hA hker i : Measure ℝ) u =
        -z * freeFockCoordinateStieltjes A hA hker i z := by
    have hzu : z * u = 1 := by simp [u, hz0]
    calc
      compactMomentGeneratingFunction
          (freeFockCoordinateSpectralLaw A hA hker i : Measure ℝ) u =
          (z * u) * compactMomentGeneratingFunction
            (freeFockCoordinateSpectralLaw A hA hker i : Measure ℝ) u := by
              rw [hzu, one_mul]
      _ = -z * (-u * compactMomentGeneratingFunction
            (freeFockCoordinateSpectralLaw A hA hker i : Measure ℝ) u) := by ring
      _ = -z * freeFockCoordinateStieltjes A hA hker i z := by rw [← hS]
  change P.eval₂ (Polynomial.evalRingHom (z⁻¹ ^ 2))
      (-z * freeFockCoordinateStieltjes A hA hker i z) = 0
  have hu2 : u ^ 2 = z⁻¹ ^ 2 := by simp [u]
  rw [← hu2, ← hMstieltjes, hM]
  exact hrel

theorem freeFockCoordinate_upperHalfPlane_stieltjes_relation
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (i : I) :
    ∃ P : Polynomial (Polynomial ℂ), P.leadingCoeff ≠ 0 ∧
      ∀ z : ℂ, 0 < z.im →
        reciprocalStieltjesRelation P
          (freeFockCoordinateSpectralLaw A hA hker i : Measure ℝ) z = 0 := by
  obtain ⟨P, hPlead, hPext⟩ :=
    freeFockCoordinate_exterior_stieltjes_relation A hA hker i
  refine ⟨P, hPlead, ?_⟩
  let U : Set ℂ := {z | 0 < z.im}
  let z₀ : ℂ := (freeFockSpectralRadius A + 1) * Complex.I
  have hz₀U : z₀ ∈ U := by
    change 0 < z₀.im
    simp [z₀]
    linarith [freeFockSpectralRadius_pos A]
  have hz₀ext : freeFockSpectralRadius A < ‖z₀‖ := by
    dsimp [z₀]
    rw [norm_mul, show ((freeFockSpectralRadius A : ℂ) + 1) =
      ((freeFockSpectralRadius A + 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one,
      abs_of_pos (by linarith [freeFockSpectralRadius_pos A])]
    linarith
  have hseed : Filter.Eventually
      (fun z ↦ reciprocalStieltjesRelation P
        (freeFockCoordinateSpectralLaw A hA hker i : Measure ℝ) z = 0)
      (nhds z₀) := by
    have hopen : IsOpen {z : ℂ | freeFockSpectralRadius A < ‖z‖} :=
      isOpen_lt continuous_const continuous_norm
    filter_upwards [hopen.mem_nhds hz₀ext] with z hz
    exact hPext z hz
  have hrelAnalytic : AnalyticOnNhd ℂ
      (reciprocalStieltjesRelation P
        (freeFockCoordinateSpectralLaw A hA hker i : Measure ℝ)) U :=
    (reciprocalStieltjesRelation_differentiableOn P
      (freeFockCoordinateSpectralLaw A hA hker i : Measure ℝ)).analyticOnNhd
      (isOpen_lt continuous_const Complex.continuous_im)
  have hzeroAnalytic : AnalyticOnNhd ℂ (fun _z : ℂ ↦ (0 : ℂ)) U :=
    analyticOnNhd_const
  have hEq := hrelAnalytic.eqOn_of_preconnected_of_eventuallyEq hzeroAnalytic
    (convex_halfSpace_im_gt 0).isPreconnected hz₀U hseed
  intro z hz
  exact hEq hz

theorem freeFockCoordinateSpectralLaw_absolutelyContinuous
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (i : I)
    (hatom : ∀ a : ℝ,
      (freeFockCoordinateSpectralLaw A hA hker i : Measure ℝ) {a} = 0) :
    (freeFockCoordinateSpectralLaw A hA hker i : Measure ℝ) ≪ volume := by
  letI : NullSingletonClass
      (freeFockCoordinateSpectralLaw A hA hker i : Measure ℝ) := ⟨hatom⟩
  obtain ⟨P, hPlead, hP⟩ :=
    freeFockCoordinate_upperHalfPlane_stieltjes_relation A hA hker i
  exact atomless_reciprocal_algebraic_stieltjes_absolutelyContinuous
    (freeFockCoordinateSpectralLaw A hA hker i : Measure ℝ) P hPlead hP

/-! ## Exact normalized scalar law as the coordinate average -/

/-- Uniform average of the exact coordinate spectral laws. -/
noncomputable def freeFockCoordinateAverageMeasure [Nonempty I]
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) : Measure ℝ :=
  ((Fintype.card I : ℝ≥0∞)⁻¹) •
    ∑ i : I, (freeFockCoordinateSpectralLaw A hA hker i : Measure ℝ)

theorem freeFockCoordinateAverageMeasure_isProbabilityMeasure [Nonempty I]
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) :
    IsProbabilityMeasure (freeFockCoordinateAverageMeasure A hA hker) := by
  constructor
  rw [freeFockCoordinateAverageMeasure, Measure.smul_apply,
    Measure.coe_finsetSum, Finset.sum_apply]
  simp only [measure_univ, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one]
  exact ENNReal.inv_mul_cancel
    (by exact_mod_cast Fintype.card_ne_zero)
    (by finiteness)

/-- Probability-valued scalar law whose moments are the normalized Fock trace moments. -/
noncomputable def freeFockCoordinateAverageSpectralLaw [Nonempty I]
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) : ProbabilityMeasure ℝ :=
  ⟨freeFockCoordinateAverageMeasure A hA hker,
    freeFockCoordinateAverageMeasure_isProbabilityMeasure A hA hker⟩

theorem freeFockCoordinateAverageSpectralLaw_hasMoments [Nonempty I]
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) :
    HasHamburgerMoments (freeFockTraceMoment A)
      (freeFockCoordinateAverageSpectralLaw A hA hker : Measure ℝ) := by
  intro k
  let f : ℝ → ℝ := fun x ↦ x ^ k
  have hi : ∀ i : I, Integrable f
      (freeFockCoordinateSpectralLaw A hA hker i : Measure ℝ) := fun i ↦
    (freeFockCoordinateSpectralLaw_hasMoments A hA hker i k).1
  have hm : ∀ i : I,
      (∫ x, f x ∂(freeFockCoordinateSpectralLaw A hA hker i : Measure ℝ)) =
        freeFockCoordinateMoment A i k := fun i ↦ by
    simpa [f] using (freeFockCoordinateSpectralLaw_hasMoments A hA hker i k).2
  have hsum : Integrable f
      (∑ i : I, (freeFockCoordinateSpectralLaw A hA hker i : Measure ℝ)) := by
    exact integrable_finsetSum_measure.mpr fun i _ ↦ hi i
  have hcoeffTop : (Fintype.card I : ℝ≥0∞)⁻¹ ≠ ∞ := by finiteness
  constructor
  · exact hsum.smul_measure hcoeffTop
  · change (∫ x, f x ∂freeFockCoordinateAverageMeasure A hA hker) =
      freeFockTraceMoment A k
    rw [freeFockCoordinateAverageMeasure, integral_smul_measure,
      integral_finsetSum_measure (s := Finset.univ) (fun i _ ↦ hi i)]
    simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]
    simp_rw [hm]
    rfl

theorem freeFockCoordinateAverageSpectralLaw_carried [Nonempty I]
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) :
    (freeFockCoordinateAverageSpectralLaw A hA hker : Measure ℝ)
      (Set.Icc (-freeFockSpectralRadius A) (freeFockSpectralRadius A))ᶜ = 0 := by
  rw [show (freeFockCoordinateAverageSpectralLaw A hA hker : Measure ℝ) =
      freeFockCoordinateAverageMeasure A hA hker by rfl,
    freeFockCoordinateAverageMeasure, Measure.smul_apply,
    Measure.coe_finsetSum, Finset.sum_apply]
  simp only [freeFockCoordinateSpectralLaw_carried, Finset.sum_const_zero,
    smul_eq_mul, mul_zero]

theorem freeFockCoordinateAverageSpectralLaw_singleton_zero [Nonempty I]
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A)
    (hatom : ∀ i a,
      (freeFockCoordinateSpectralLaw A hA hker i : Measure ℝ) {a} = 0)
    (a : ℝ) :
    (freeFockCoordinateAverageSpectralLaw A hA hker : Measure ℝ) {a} = 0 := by
  rw [show (freeFockCoordinateAverageSpectralLaw A hA hker : Measure ℝ) =
      freeFockCoordinateAverageMeasure A hA hker by rfl,
    freeFockCoordinateAverageMeasure, Measure.smul_apply,
    Measure.coe_finsetSum, Finset.sum_apply]
  simp only [hatom, Finset.sum_const_zero, smul_eq_mul, mul_zero]

theorem freeFockCoordinateAverageSpectralLaw_absolutelyContinuous [Nonempty I]
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A)
    (hac : ∀ i,
      (freeFockCoordinateSpectralLaw A hA hker i : Measure ℝ) ≪ volume) :
    (freeFockCoordinateAverageSpectralLaw A hA hker : Measure ℝ) ≪ volume := by
  intro s hs
  have hzero : ∀ i,
      (freeFockCoordinateSpectralLaw A hA hker i : Measure ℝ) s = 0 :=
    fun i ↦ hac i hs
  rw [show (freeFockCoordinateAverageSpectralLaw A hA hker : Measure ℝ) =
      freeFockCoordinateAverageMeasure A hA hker by rfl,
    freeFockCoordinateAverageMeasure, Measure.smul_apply,
    Measure.coe_finsetSum, Finset.sum_apply]
  simp only [hzero, Finset.sum_const_zero, smul_eq_mul, mul_zero]

end

end GaloisForLFunctions.HTGeometry
