import GaloisForLFunctions.HTGeometry.FreeFockMatrixSemicircleCoordinateLaw
import GaloisForLFunctions.HTGeometry.CompactDeterminacy
import GaloisForLFunctions.HTGeometry.ComplexQuadraticPolarization
import GaloisForLFunctions.HTGeometry.PositiveConeDeterminantMonotone
import GaloisForLFunctions.HTGeometry.StieltjesAtomMassBoundary

/-!
# Matrix-valued spectral law of a finite matrix semicircle

The coordinate laws alone do not retain the off-diagonal Cauchy transform.  This file constructs
the compact spectral measure of every internal vacuum vector directly from the algebraic free-Fock
moments.  Compact determinacy makes those independently constructed measures a coherent quadratic
family; polarization can therefore recover the full matrix-valued law without assuming an
operator-algebraic spectral theorem.
-/

open scoped BigOperators Matrix ENNReal ComplexOrder
open Filter Topology Matrix MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]

/-- Internal vacuum with coefficient vector `x`. -/
def freeFockVacuumSuperposition (x : I → ℂ) : FreeFockVector I K :=
  ∑ i : I, x i • freeFockVacuum i

/-- `n`th free-Fock power applied to an arbitrary internal vacuum vector. -/
def freeFockPowerSuperposition (A : K → Matrix I I ℂ) (x : I → ℂ) (n : ℕ) :
    FreeFockVector I K :=
  ∑ i : I, x i • freeFockPower A i n

/-- Polynomial in the free-Fock action applied to an arbitrary internal vacuum vector. -/
def freeFockPolynomialSuperposition
    (A : K → Matrix I I ℂ) (p : Polynomial ℝ) (x : I → ℂ) : FreeFockVector I K :=
  ∑ i : I, x i • freeFockPolynomialVector A p i

/-- Vacuum moment of the matrix semicircle in an arbitrary internal vector state. -/
def freeFockVectorMoment (A : K → Matrix I I ℂ) (x : I → ℂ) (n : ℕ) : ℝ :=
  (freeFockInner (freeFockVacuumSuperposition x)
    (freeFockPowerSuperposition A x n)).re

omit [DecidableEq K] in
theorem freeFockPowerSuperposition_zero (A : K → Matrix I I ℂ) (x : I → ℂ) :
    freeFockPowerSuperposition A x 0 = freeFockVacuumSuperposition x := by
  simp [freeFockPowerSuperposition, freeFockVacuumSuperposition]

omit [DecidableEq K] in
theorem freeFockPowerSuperposition_succ
    (A : K → Matrix I I ℂ) (x : I → ℂ) (n : ℕ) :
    freeFockPowerSuperposition A x (n + 1) =
      freeFockAction A (freeFockPowerSuperposition A x n) := by
  simp [freeFockPowerSuperposition, map_sum]

theorem freeFockInner_powerSuperposition
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (x : I → ℂ) (m n : ℕ) :
    freeFockInner (freeFockPowerSuperposition A x m)
        (freeFockPowerSuperposition A x n) =
      freeFockInner (freeFockVacuumSuperposition x)
        (freeFockPowerSuperposition A x (m + n)) := by
  simp only [freeFockPowerSuperposition, freeFockVacuumSuperposition,
    freeFockInner_finset_sum_left, freeFockInner_finset_sum_right,
    freeFockInner_smul_left, freeFockInner_smul_right]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [freeFockInner_power_power A hA,
    show freeFockVacuum j = freeFockPower A j 0 by rfl,
    freeFockInner_power_power A hA]
  simp

theorem freeFockInner_conj_symm
    (x y : FreeFockVector I K) :
    freeFockInner x y = star (freeFockInner y x) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x z hx hz =>
      rw [freeFockInner_add_left, freeFockInner_add_right]
      calc
        freeFockInner x y + freeFockInner z y =
            star (freeFockInner y x) + star (freeFockInner y z) := by rw [hx, hz]
        _ = star (freeFockInner y x + freeFockInner y z) := by rw [star_add]
  | single a c =>
      rw [freeFockInner_single_left, freeFockInner_single_right]
      rw [star_mul, star_star]

@[simp]
theorem freeFockInner_neg_left
    (x y : FreeFockVector I K) : freeFockInner (-x) y = -freeFockInner x y := by
  simpa only [neg_smul, one_smul, neg_one_mul, star_neg, star_one] using
    freeFockInner_smul_left (-1 : ℂ) x y

@[simp]
theorem freeFockInner_neg_right
    (x y : FreeFockVector I K) : freeFockInner x (-y) = -freeFockInner x y := by
  simpa only [neg_smul, one_smul, neg_one_mul] using
    freeFockInner_smul_right (-1 : ℂ) x y

theorem freeFockInner_vacuum_left
    (i : I) (y : FreeFockVector I K) :
    freeFockInner (freeFockVacuum i) y = y (i, []) := by
  simp [freeFockVacuum]

theorem freeFockInner_vacuum_power_conj
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (i j : I) (n : ℕ) :
    freeFockInner (freeFockVacuum j) (freeFockPower A i n) =
      star (freeFockInner (freeFockVacuum i) (freeFockPower A j n)) := by
  calc
    freeFockInner (freeFockVacuum j) (freeFockPower A i n) =
        star (freeFockInner (freeFockPower A i n) (freeFockVacuum j)) :=
      freeFockInner_conj_symm _ _
    _ = star (freeFockInner (freeFockVacuum i) (freeFockPower A j n)) := by
      congr 1
      rw [show freeFockVacuum j = freeFockPower A j 0 by rfl,
        show freeFockVacuum i = freeFockPower A i 0 by rfl,
        freeFockInner_power_power A hA,
        freeFockInner_power_power A hA]
      simp

theorem freeFockPolynomialSuperposition_eq_sum_power
    (A : K → Matrix I I ℂ) (p : Polynomial ℝ) (x : I → ℂ) :
    freeFockPolynomialSuperposition A p x =
      ∑ n ∈ p.support, (p.coeff n : ℂ) • freeFockPowerSuperposition A x n := by
  ext iw
  simp only [freeFockPolynomialSuperposition, freeFockPolynomialVector,
    freeFockPowerSuperposition, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem momentInner_freeFockVectorMoment_eq
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (x : I → ℂ) (p : Polynomial ℝ) :
    HTGeometry.momentInner (freeFockVectorMoment A x) p p =
      (freeFockInner (freeFockPolynomialSuperposition A p x)
        (freeFockPolynomialSuperposition A p x)).re := by
  rw [momentInner_eq_double_support_sum]
  rw [freeFockPolynomialSuperposition_eq_sum_power]
  simp only [
    freeFockInner_finset_sum_left, freeFockInner_finset_sum_right,
    freeFockInner_smul_left, freeFockInner_smul_right]
  simp_rw [freeFockInner_powerSuperposition A hA]
  simp only [freeFockVectorMoment]
  have hre (s : Finset ℕ) (f : ℕ → ℂ) :
      (∑ n ∈ s, f n).re = ∑ n ∈ s, (f n).re := by
    exact map_sum Complex.reCLM f s
  simp_rw [hre]
  simp only [Complex.star_def, Complex.conj_ofReal, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  simp_rw [hre]
  simp only [Complex.star_def, Complex.conj_ofReal, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [add_comm n m]
  ring

/-- Iterated common-kernel injectivity for an arbitrary starting vector. -/
theorem exists_freeFockCreationProduct_vector_entry_ne_zero
    (A : K → Matrix I I ℂ) (hker : HasTrivialCommonKernel A)
    (x : I → ℂ) (hx : x ≠ 0) (n : ℕ) :
    ∃ w : List K, w.length = n ∧
      ∃ i : I, ∑ j : I, freeFockCreationProduct A w i j * x j ≠ 0 := by
  induction n with
  | zero =>
      obtain ⟨i, hi⟩ : ∃ i : I, x i ≠ 0 := by
        by_contra h
        push Not at h
        exact hx (funext h)
      refine ⟨[], rfl, i, ?_⟩
      simpa [freeFockCreationProduct, Matrix.one_apply] using hi
  | succ n ih =>
      obtain ⟨w, hw, i, hi⟩ := ih
      let y : I → ℂ := fun p ↦ ∑ j : I, freeFockCreationProduct A w p j * x j
      have hy : y ≠ 0 := by
        intro hy
        exact hi (congr_fun hy i)
      have hnot : ¬ ∀ k i, ∑ p : I, A k i p * y p = 0 := by
        intro hall
        exact hy (hker y hall)
      push Not at hnot
      obtain ⟨k, i', hki⟩ := hnot
      refine ⟨k :: w, by simp [hw], i', ?_⟩
      simp only [freeFockCreationProduct, Matrix.mul_apply]
      rw [show (∑ j : I, (∑ p : I, A k i' p * freeFockCreationProduct A w p j) * x j) =
          ∑ p : I, A k i' p * y p by
        simp only [y, Finset.mul_sum, Finset.sum_mul, mul_assoc]
        rw [Finset.sum_comm]]
      exact hki

theorem freeFockPolynomialSuperposition_apply_top
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (p : Polynomial ℝ) (hp : p ≠ 0) (x : I → ℂ) (i : I) (w : List K)
    (hw : w.length = p.natDegree) :
    freeFockPolynomialSuperposition A p x (i, w) =
      (p.leadingCoeff : ℂ) *
        ∑ j : I, freeFockCreationProduct A w i j * x j := by
  simp only [freeFockPolynomialSuperposition, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, smul_eq_mul]
  simp_rw [freeFockPolynomialVector_apply_top A hA p hp _ i w hw]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem freeFockPolynomialSuperposition_ne_zero
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (p : Polynomial ℝ) (hp : p ≠ 0)
    (x : I → ℂ) (hx : x ≠ 0) :
    freeFockPolynomialSuperposition A p x ≠ 0 := by
  obtain ⟨w, hw, i, hi⟩ :=
    exists_freeFockCreationProduct_vector_entry_ne_zero A hker x hx p.natDegree
  apply Finsupp.ne_iff.mpr
  refine ⟨(i, w), ?_⟩
  rw [freeFockPolynomialSuperposition_apply_top A hA p hp x i w hw]
  exact mul_ne_zero (by exact_mod_cast Polynomial.leadingCoeff_ne_zero.mpr hp) hi

theorem freeFockVectorMoment_positiveMomentForm
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (x : I → ℂ) (hx : x ≠ 0) :
    HTGeometry.PositiveMomentForm (freeFockVectorMoment A x) := by
  constructor
  intro p hp
  rw [momentInner_freeFockVectorMoment_eq A hA]
  exact re_freeFockInner_self_pos _
    (freeFockPolynomialSuperposition_ne_zero A hA hker p hp x hx)

theorem freeFockVectorMoment_zero
    (A : K → Matrix I I ℂ) (x : I → ℂ) :
    freeFockVectorMoment A x 0 = ∑ i : I, Complex.normSq (x i) := by
  rw [freeFockVectorMoment, freeFockPowerSuperposition_zero]
  simp only [freeFockVacuumSuperposition, freeFockInner_finset_sum_left,
    freeFockInner_finset_sum_right, freeFockInner_smul_left,
    freeFockInner_smul_right, freeFockInner_single_left, freeFockVacuum,
    Finsupp.single_apply]
  simp [Complex.normSq_apply]

theorem freeFockVectorMoment_even_eq_inner
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (x : I → ℂ) (n : ℕ) :
    freeFockVectorMoment A x (2 * n) =
      (freeFockInner (freeFockPowerSuperposition A x n)
        (freeFockPowerSuperposition A x n)).re := by
  rw [freeFockVectorMoment, show 2 * n = n + n by omega]
  exact congrArg Complex.re (freeFockInner_powerSuperposition A hA x n n).symm

theorem finsuppL1_freeFockPowerSuperposition_le
    (A : K → Matrix I I ℂ) (x : I → ℂ) (n : ℕ) :
    finsuppL1 (freeFockPowerSuperposition A x n) ≤
      (∑ i : I, ‖x i‖) * freeFockSpectralRadius A ^ n := by
  rw [freeFockPowerSuperposition]
  calc
    finsuppL1 (∑ i : I, x i • freeFockPower A i n) ≤
        ∑ i : I, finsuppL1 (x i • freeFockPower A i n) :=
      finsuppL1_finsetSum_le Finset.univ _
    _ = ∑ i : I, ‖x i‖ * finsuppL1 (freeFockPower A i n) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [finsuppL1_smul]
    _ ≤ ∑ i : I, ‖x i‖ * freeFockSpectralRadius A ^ n := by
      apply Finset.sum_le_sum
      intro i hi
      gcongr
      calc
        finsuppL1 (freeFockPower A i n) ≤ (2 * matrixFamilyEntryL1 A) ^ n :=
          finsuppL1_freeFockPower_le A i n
        _ ≤ freeFockSpectralRadius A ^ n := by
          apply pow_le_pow_left₀
            (mul_nonneg (by positivity) (matrixFamilyEntryL1_nonneg A))
          simp [freeFockSpectralRadius]
    _ = (∑ i : I, ‖x i‖) * freeFockSpectralRadius A ^ n := by
      rw [Finset.sum_mul]

theorem freeFockVectorMoment_even_le_l1
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (x : I → ℂ) (n : ℕ) :
    freeFockVectorMoment A x (2 * n) ≤
      (∑ i : I, ‖x i‖) ^ 2 * freeFockSpectralRadius A ^ (2 * n) := by
  rw [freeFockVectorMoment_even_eq_inner A hA]
  calc
    (freeFockInner (freeFockPowerSuperposition A x n)
      (freeFockPowerSuperposition A x n)).re ≤
        finsuppL1 (freeFockPowerSuperposition A x n) ^ 2 :=
      re_freeFockInner_self_le_finsuppL1_sq _
    _ ≤ ((∑ i : I, ‖x i‖) * freeFockSpectralRadius A ^ n) ^ 2 :=
      pow_le_pow_left₀ (finsuppL1_nonneg _) (finsuppL1_freeFockPowerSuperposition_le A x n) 2
    _ = (∑ i : I, ‖x i‖) ^ 2 * freeFockSpectralRadius A ^ (2 * n) := by
      rw [mul_pow]
      congr 1
      rw [← pow_mul]
      congr 1
      omega

theorem sq_sum_norm_le_card_mul_sum_normSq (x : I → ℂ) :
    (∑ i : I, ‖x i‖) ^ 2 ≤
      (Fintype.card I : ℝ) * ∑ i : I, Complex.normSq (x i) := by
  simpa [Complex.sq_norm] using
    (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : I ↦ ‖x i‖))

/-- One common compact carrier for all internal vacuum-vector spectral measures. -/
def freeFockMatrixSpectralRadius (A : K → Matrix I I ℂ) : ℝ :=
  ((Fintype.card I : ℝ) + 1) * freeFockSpectralRadius A

theorem freeFockMatrixSpectralRadius_pos (A : K → Matrix I I ℂ) :
    0 < freeFockMatrixSpectralRadius A := by
  exact mul_pos (by positivity) (freeFockSpectralRadius_pos A)

theorem freeFockVectorMoment_even_le_matrixRadius
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (x : I → ℂ) (n : ℕ) :
    freeFockVectorMoment A x (2 * n) ≤
      (∑ i : I, Complex.normSq (x i)) * freeFockMatrixSpectralRadius A ^ (2 * n) := by
  cases n with
  | zero =>
      simp [freeFockVectorMoment_zero]
  | succ n =>
      let c : ℝ := Fintype.card I
      let R : ℝ := freeFockSpectralRadius A
      let q : ℝ := ∑ i : I, Complex.normSq (x i)
      have hc0 : 0 ≤ c := by positivity
      have hq0 : 0 ≤ q := Finset.sum_nonneg fun i _ ↦ Complex.normSq_nonneg _
      have hR0 : 0 ≤ R := (freeFockSpectralRadius_pos A).le
      have hbase : 1 ≤ c + 1 := by linarith
      have hcpow : c ≤ (c + 1) ^ (2 * (n + 1)) := by
        calc
          c ≤ c + 1 := by linarith
          _ = (c + 1) ^ 1 := by ring
          _ ≤ (c + 1) ^ (2 * (n + 1)) :=
            pow_le_pow_right₀ hbase (by omega)
      calc
        freeFockVectorMoment A x (2 * (n + 1)) ≤
            (∑ i : I, ‖x i‖) ^ 2 * R ^ (2 * (n + 1)) :=
          freeFockVectorMoment_even_le_l1 A hA x (n + 1)
        _ ≤ (c * q) * R ^ (2 * (n + 1)) := by
          gcongr
          exact sq_sum_norm_le_card_mul_sum_normSq x
        _ ≤ ((c + 1) ^ (2 * (n + 1)) * q) * R ^ (2 * (n + 1)) := by
          gcongr
        _ = q * freeFockMatrixSpectralRadius A ^ (2 * (n + 1)) := by
          simp only [freeFockMatrixSpectralRadius, c, R, q, mul_pow]
          ring

/-- A finite positive spectral measure for every internal vacuum vector. -/
noncomputable def freeFockVectorSpectralMeasureData
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (x : I → ℂ) :
    { μ : Measure ℝ // IsFiniteMeasure μ ∧
      HasHamburgerMoments (freeFockVectorMoment A x) μ } := by
  by_cases hx : x = 0
  · subst x
    refine ⟨0, inferInstance, fun n ↦ ⟨by simp, ?_⟩⟩
    simp [freeFockVectorMoment, freeFockVacuumSuperposition,
      freeFockPowerSuperposition]
  · let hex := HTGeometry.exists_finiteMeasure_hasHamburgerMoments
      (freeFockVectorMoment_positiveMomentForm A hA hker x hx)
    exact ⟨Classical.choose hex, (Classical.choose_spec hex).1,
      (Classical.choose_spec hex).2⟩

/-- Coherent vector spectral measure; coherence is proved below from compact determinacy. -/
noncomputable def freeFockVectorSpectralMeasure
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (x : I → ℂ) : Measure ℝ :=
  (freeFockVectorSpectralMeasureData A hA hker x).1

noncomputable instance freeFockVectorSpectralMeasure_isFinite
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (x : I → ℂ) :
    IsFiniteMeasure (freeFockVectorSpectralMeasure A hA hker x) :=
  (freeFockVectorSpectralMeasureData A hA hker x).2.1

theorem freeFockVectorSpectralMeasure_hasMoments
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (x : I → ℂ) :
    HasHamburgerMoments (freeFockVectorMoment A x)
      (freeFockVectorSpectralMeasure A hA hker x) :=
  (freeFockVectorSpectralMeasureData A hA hker x).2.2

theorem freeFockVectorSpectralMeasure_carried
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (x : I → ℂ) :
    freeFockVectorSpectralMeasure A hA hker x
      (Set.Icc (-freeFockMatrixSpectralRadius A) (freeFockMatrixSpectralRadius A))ᶜ = 0 := by
  let μ := freeFockVectorSpectralMeasure A hA hker x
  let R := freeFockMatrixSpectralRadius A
  have hR : 0 < R := freeFockMatrixSpectralRadius_pos A
  let f : ℝ → ℝ := fun y ↦ (y / R) ^ 2
  have hfmeas : Measurable f := by fun_prop
  have hfnn : ∀ y, 0 ≤ f y := fun y ↦ sq_nonneg _
  have hfeq (y : ℝ) (n : ℕ) : f y ^ n = R⁻¹ ^ (2 * n) * y ^ (2 * n) := by
    dsimp only [f]
    rw [pow_mul, div_pow, inv_pow]
    ring
  have hμ := freeFockVectorSpectralMeasure_hasMoments A hA hker x
  have hint : ∀ n : ℕ, Integrable (fun y ↦ f y ^ n) μ := by
    intro n
    refine ((hμ (2 * n)).1.const_mul (R⁻¹ ^ (2 * n))).congr
      (Filter.Eventually.of_forall fun y ↦ (hfeq y n).symm)
  have hbound : ∀ n : ℕ, ∫ y, f y ^ n ∂μ ≤ ∑ i : I, Complex.normSq (x i) := by
    intro n
    rw [integral_congr_ae (Filter.Eventually.of_forall fun y ↦ hfeq y n),
      integral_const_mul, (hμ (2 * n)).2]
    have hm := freeFockVectorMoment_even_le_matrixRadius A hA x n
    change R⁻¹ ^ (2 * n) * freeFockVectorMoment A x (2 * n) ≤ _
    calc
      R⁻¹ ^ (2 * n) * freeFockVectorMoment A x (2 * n) ≤
          R⁻¹ ^ (2 * n) *
            ((∑ i : I, Complex.normSq (x i)) * R ^ (2 * n)) :=
        mul_le_mul_of_nonneg_left hm (pow_nonneg (inv_nonneg.mpr hR.le) _)
      _ = ∑ i : I, Complex.normSq (x i) := by
        calc
          R⁻¹ ^ (2 * n) *
              ((∑ i : I, Complex.normSq (x i)) * R ^ (2 * n)) =
              (R⁻¹ ^ (2 * n) * R ^ (2 * n)) *
                ∑ i : I, Complex.normSq (x i) := by ring
          _ = ∑ i : I, Complex.normSq (x i) := by
            rw [← mul_pow, inv_mul_cancel₀ hR.ne', one_pow, one_mul]
  have hnull : ∀ k : ℕ, μ {y | 1 + 1 / (k + 1 : ℝ) ≤ f y} = 0 := by
    intro k
    apply HTGeometry.measure_ge_eq_zero_of_pow_integral_le hfmeas hfnn hint hbound
    have : (0 : ℝ) < 1 / (k + 1 : ℝ) := by positivity
    linarith
  have hcover : (Set.Icc (-R) R)ᶜ ⊆
      ⋃ k : ℕ, {y | 1 + 1 / (k + 1 : ℝ) ≤ f y} := by
    intro y hy
    have hgt : 1 < f y := by
      simpa [f] using
        (HTGeometry.sq_gt_one_iff_notMem_Icc (c := 0) hR).mpr (by simpa using hy)
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (by linarith : (0 : ℝ) < f y - 1)
    exact Set.mem_iUnion.mpr ⟨k, by simp only [Set.mem_setOf_eq]; linarith⟩
  exact measure_mono_null hcover (measure_iUnion_null hnull)

omit [DecidableEq K] in
theorem freeFockVacuumSuperposition_add (x y : I → ℂ) :
    freeFockVacuumSuperposition (x + y) =
      freeFockVacuumSuperposition (K := K) x + freeFockVacuumSuperposition y := by
  simp [freeFockVacuumSuperposition, add_smul, Finset.sum_add_distrib]

omit [DecidableEq K] in
theorem freeFockVacuumSuperposition_smul (c : ℂ) (x : I → ℂ) :
    freeFockVacuumSuperposition (c • x) =
      c • freeFockVacuumSuperposition (K := K) x := by
  simp [freeFockVacuumSuperposition, Finset.smul_sum, smul_smul]

omit [DecidableEq K] in
theorem freeFockPowerSuperposition_add
    (A : K → Matrix I I ℂ) (x y : I → ℂ) (n : ℕ) :
    freeFockPowerSuperposition A (x + y) n =
      freeFockPowerSuperposition A x n + freeFockPowerSuperposition A y n := by
  simp [freeFockPowerSuperposition, add_smul, Finset.sum_add_distrib]

omit [DecidableEq K] in
theorem freeFockPowerSuperposition_smul
    (A : K → Matrix I I ℂ) (c : ℂ) (x : I → ℂ) (n : ℕ) :
    freeFockPowerSuperposition A (c • x) n = c • freeFockPowerSuperposition A x n := by
  simp [freeFockPowerSuperposition, Finset.smul_sum, smul_smul]

omit [DecidableEq K] in
theorem freeFockVacuumSuperposition_neg (x : I → ℂ) :
    freeFockVacuumSuperposition (-x) =
      -freeFockVacuumSuperposition (K := K) x := by
  rw [show -x = (-1 : ℂ) • x by ext; simp,
    freeFockVacuumSuperposition_smul]
  simp

omit [DecidableEq K] in
theorem freeFockPowerSuperposition_neg
    (A : K → Matrix I I ℂ) (x : I → ℂ) (n : ℕ) :
    freeFockPowerSuperposition A (-x) n =
      -freeFockPowerSuperposition A x n := by
  rw [show -x = (-1 : ℂ) • x by ext; simp,
    freeFockPowerSuperposition_smul]
  simp

theorem freeFockVectorMoment_smul
    (A : K → Matrix I I ℂ) (c : ℂ) (x : I → ℂ) (n : ℕ) :
    freeFockVectorMoment A (c • x) n =
      Complex.normSq c * freeFockVectorMoment A x n := by
  rw [freeFockVectorMoment, freeFockVacuumSuperposition_smul,
    freeFockPowerSuperposition_smul, freeFockInner_smul_left,
    freeFockInner_smul_right]
  simp only [freeFockVectorMoment, Complex.star_def, Complex.conj_re,
    Complex.conj_im, Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  ring

theorem freeFockVectorMoment_parallelogram
    (A : K → Matrix I I ℂ) (x y : I → ℂ) (n : ℕ) :
    freeFockVectorMoment A (x + y) n + freeFockVectorMoment A (x - y) n =
      2 * freeFockVectorMoment A x n + 2 * freeFockVectorMoment A y n := by
  simp only [sub_eq_add_neg, freeFockVectorMoment,
    freeFockVacuumSuperposition_add, freeFockPowerSuperposition_add,
    show freeFockVacuumSuperposition (-y) =
        (-1 : ℂ) • freeFockVacuumSuperposition (K := K) y by
      rw [show -y = (-1 : ℂ) • y by ext; simp,
        freeFockVacuumSuperposition_smul],
    show freeFockPowerSuperposition A (-y) n =
        (-1 : ℂ) • freeFockPowerSuperposition A y n by
      rw [show -y = (-1 : ℂ) • y by ext; simp,
        freeFockPowerSuperposition_smul],
    freeFockInner_add_left, freeFockInner_add_right,
    freeFockInner_smul_left, freeFockInner_smul_right]
  simp only [freeFockVectorMoment, Complex.star_def, map_neg, map_one,
    one_mul, neg_mul, mul_neg, neg_neg, Complex.add_re, Complex.neg_re]
  ring

theorem freeFockVectorSpectralMeasure_smul
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (c : ℂ) (x : I → ℂ) :
    freeFockVectorSpectralMeasure A hA hker (c • x) =
      ENNReal.ofReal (Complex.normSq c) • freeFockVectorSpectralMeasure A hA hker x := by
  let μ := freeFockVectorSpectralMeasure A hA hker (c • x)
  let ν := ENNReal.ofReal (Complex.normSq c) •
    freeFockVectorSpectralMeasure A hA hker x
  let R := freeFockMatrixSpectralRadius A
  let s := freeFockVectorMoment A (c • x)
  have hμ := freeFockVectorSpectralMeasure_hasMoments A hA hker (c • x)
  have hx := freeFockVectorSpectralMeasure_hasMoments A hA hker x
  letI : IsFiniteMeasure ν := by
    constructor
    change ENNReal.ofReal (Complex.normSq c) *
      (freeFockVectorSpectralMeasure A hA hker x) Set.univ < ⊤
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  apply HTGeometry.measure_eq_of_moments_eq_of_carried (s := s) (m := -R) (M := R)
  · exact freeFockVectorSpectralMeasure_carried A hA hker (c • x)
  · change ν (Set.Icc (-R) R)ᶜ = 0
    change ENNReal.ofReal (Complex.normSq c) *
      (freeFockVectorSpectralMeasure A hA hker x) (Set.Icc (-R) R)ᶜ = 0
    rw [freeFockVectorSpectralMeasure_carried A hA hker x, mul_zero]
  · intro n
    exact (hμ n).2.symm
  · intro n
    exact (hμ n).1
  · intro n
    change s n = ∫ y, y ^ n ∂ν
    rw [integral_smul_measure, ENNReal.toReal_ofReal (Complex.normSq_nonneg c),
      smul_eq_mul, (hx n).2]
    exact freeFockVectorMoment_smul A c x n
  · intro n
    exact (hx n).1.smul_measure ENNReal.ofReal_ne_top

theorem freeFockVectorSpectralMeasure_parallelogram
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (x y : I → ℂ) :
    freeFockVectorSpectralMeasure A hA hker (x + y) +
        freeFockVectorSpectralMeasure A hA hker (x - y) =
      ENNReal.ofReal 2 • freeFockVectorSpectralMeasure A hA hker x +
        ENNReal.ofReal 2 • freeFockVectorSpectralMeasure A hA hker y := by
  let μ := freeFockVectorSpectralMeasure A hA hker (x + y) +
    freeFockVectorSpectralMeasure A hA hker (x - y)
  let ν := ENNReal.ofReal 2 • freeFockVectorSpectralMeasure A hA hker x +
    ENNReal.ofReal 2 • freeFockVectorSpectralMeasure A hA hker y
  let R := freeFockMatrixSpectralRadius A
  let s := fun n ↦ freeFockVectorMoment A (x + y) n +
    freeFockVectorMoment A (x - y) n
  have hxy := freeFockVectorSpectralMeasure_hasMoments A hA hker (x + y)
  have hxm := freeFockVectorSpectralMeasure_hasMoments A hA hker (x - y)
  have hx := freeFockVectorSpectralMeasure_hasMoments A hA hker x
  have hy := freeFockVectorSpectralMeasure_hasMoments A hA hker y
  letI : IsFiniteMeasure ν := by
    constructor
    change ENNReal.ofReal 2 * (freeFockVectorSpectralMeasure A hA hker x) Set.univ +
      ENNReal.ofReal 2 * (freeFockVectorSpectralMeasure A hA hker y) Set.univ < ⊤
    exact ENNReal.add_lt_top.2 ⟨
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _),
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩
  apply HTGeometry.measure_eq_of_moments_eq_of_carried (s := s) (m := -R) (M := R)
  · change μ (Set.Icc (-R) R)ᶜ = 0
    change (freeFockVectorSpectralMeasure A hA hker (x + y)) (Set.Icc (-R) R)ᶜ +
      (freeFockVectorSpectralMeasure A hA hker (x - y)) (Set.Icc (-R) R)ᶜ = 0
    rw [freeFockVectorSpectralMeasure_carried A hA hker,
      freeFockVectorSpectralMeasure_carried A hA hker, zero_add]
  · change ν (Set.Icc (-R) R)ᶜ = 0
    change ENNReal.ofReal 2 *
          (freeFockVectorSpectralMeasure A hA hker x) (Set.Icc (-R) R)ᶜ +
        ENNReal.ofReal 2 *
          (freeFockVectorSpectralMeasure A hA hker y) (Set.Icc (-R) R)ᶜ = 0
    rw [freeFockVectorSpectralMeasure_carried A hA hker,
      freeFockVectorSpectralMeasure_carried A hA hker]
    simp
  · intro n
    change s n = ∫ z, z ^ n ∂μ
    rw [integral_add_measure (hxy n).1 (hxm n).1, (hxy n).2, (hxm n).2]
  · intro n
    exact (hxy n).1.add_measure (hxm n).1
  · intro n
    change s n = ∫ z, z ^ n ∂ν
    rw [integral_add_measure ((hx n).1.smul_measure ENNReal.ofReal_ne_top)
        ((hy n).1.smul_measure ENNReal.ofReal_ne_top),
      integral_smul_measure, integral_smul_measure,
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2),
      smul_eq_mul, (hx n).2, (hy n).2]
    exact freeFockVectorMoment_parallelogram A x y n
  · intro n
    exact ((hx n).1.smul_measure ENNReal.ofReal_ne_top).add_measure
      ((hy n).1.smul_measure ENNReal.ofReal_ne_top)

/-- Mass of the atom at `a` in the spectral measure generated by internal vector `x`. -/
def freeFockVectorAtomMass
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (a : ℝ) (x : I → ℂ) : ℝ :=
  (freeFockVectorSpectralMeasure A hA hker x {a}).toReal

theorem freeFockVectorAtomMass_nonneg
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (a : ℝ) (x : I → ℂ) :
    0 ≤ freeFockVectorAtomMass A hA hker a x :=
  ENNReal.toReal_nonneg

theorem freeFockVectorAtomMass_smul
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (a : ℝ) (c : ℂ) (x : I → ℂ) :
    freeFockVectorAtomMass A hA hker a (c • x) =
      Complex.normSq c * freeFockVectorAtomMass A hA hker a x := by
  unfold freeFockVectorAtomMass
  rw [freeFockVectorSpectralMeasure_smul A hA hker c x]
  change (ENNReal.ofReal (Complex.normSq c) *
      (freeFockVectorSpectralMeasure A hA hker x) {a}).toReal = _
  rw [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Complex.normSq_nonneg c)]

theorem freeFockVectorAtomMass_parallelogram
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (a : ℝ) (x y : I → ℂ) :
    freeFockVectorAtomMass A hA hker a (x + y) +
        freeFockVectorAtomMass A hA hker a (x - y) =
      2 * freeFockVectorAtomMass A hA hker a x +
        2 * freeFockVectorAtomMass A hA hker a y := by
  have h := congrArg (fun μ : Measure ℝ ↦ (μ {a}).toReal)
    (freeFockVectorSpectralMeasure_parallelogram A hA hker x y)
  unfold freeFockVectorAtomMass
  change
    (((freeFockVectorSpectralMeasure A hA hker (x + y)) {a} +
      (freeFockVectorSpectralMeasure A hA hker (x - y)) {a}).toReal) =
    ((ENNReal.ofReal 2 * (freeFockVectorSpectralMeasure A hA hker x) {a} +
      ENNReal.ofReal 2 * (freeFockVectorSpectralMeasure A hA hker y) {a}).toReal) at h
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
    ENNReal.toReal_add
      (ne_of_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)))
      (ne_of_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _))),
    ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2)] at h
  exact h

theorem freeFockVectorSpectralMeasure_totalMass
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (x : I → ℂ) :
    (freeFockVectorSpectralMeasure A hA hker x Set.univ).toReal =
      ∑ i : I, Complex.normSq (x i) := by
  have h := (freeFockVectorSpectralMeasure_hasMoments A hA hker x 0).2
  rw [freeFockVectorMoment_zero] at h
  simpa only [pow_zero, integral_const, MeasureTheory.measureReal_def,
    smul_eq_mul, mul_one] using h

theorem sum_normSq_le_card_mul_norm_sq (x : I → ℂ) :
    (∑ i : I, Complex.normSq (x i)) ≤
      (Fintype.card I : ℝ) * ‖x‖ ^ 2 := by
  calc
    (∑ i : I, Complex.normSq (x i)) = ∑ i : I, ‖x i‖ ^ 2 := by
      simp only [Complex.sq_norm]
    _ ≤ ∑ _i : I, ‖x‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      apply pow_le_pow_left₀ (norm_nonneg _) _ 2
      rw [Pi.norm_def]
      exact_mod_cast Finset.le_sup (f := fun j : I ↦ ‖x j‖₊) (Finset.mem_univ i)
    _ = (Fintype.card I : ℝ) * ‖x‖ ^ 2 := by
      simp [mul_comm]

theorem freeFockVectorAtomMass_le
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (a : ℝ) (x : I → ℂ) :
    freeFockVectorAtomMass A hA hker a x ≤
      (Fintype.card I : ℝ) * ‖x‖ ^ 2 := by
  calc
    freeFockVectorAtomMass A hA hker a x ≤
        (freeFockVectorSpectralMeasure A hA hker x Set.univ).toReal := by
      apply ENNReal.toReal_mono (measure_ne_top _ _)
      exact measure_mono (Set.subset_univ {a})
    _ = ∑ i : I, Complex.normSq (x i) :=
      freeFockVectorSpectralMeasure_totalMass A hA hker x
    _ ≤ (Fintype.card I : ℝ) * ‖x‖ ^ 2 :=
      sum_normSq_le_card_mul_norm_sq x

/-- Standard internal coordinate vector. -/
def freeFockInternalBasis (i : I) : I → ℂ := Pi.single i 1

theorem freeFockVacuumSuperposition_internalBasis (i : I) :
    freeFockVacuumSuperposition (K := K) (freeFockInternalBasis i) =
      freeFockVacuum i := by
  classical
  rw [freeFockVacuumSuperposition]
  apply Finsupp.ext
  intro jw
  simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul,
    freeFockInternalBasis]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    rw [Pi.single_eq_of_ne hji]
    simp
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem freeFockPowerSuperposition_internalBasis
    (A : K → Matrix I I ℂ) (i : I) (n : ℕ) :
    freeFockPowerSuperposition A (freeFockInternalBasis i) n =
      freeFockPower A i n := by
  classical
  rw [freeFockPowerSuperposition]
  apply Finsupp.ext
  intro jw
  simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul,
    freeFockInternalBasis]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    rw [Pi.single_eq_of_ne hji]
    simp
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem complexQuadraticPolarization_freeFockVectorMoment_internalBasis
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (i j : I) (n : ℕ) :
    complexQuadraticPolarization (fun x ↦ freeFockVectorMoment A x n)
        (freeFockInternalBasis i) (freeFockInternalBasis j) =
      freeFockPower A j n (i, []) := by
  let vi : FreeFockVector I K := freeFockVacuum i
  let vj : FreeFockVector I K := freeFockVacuum j
  let pi : FreeFockVector I K := freeFockPower A i n
  let pj : FreeFockVector I K := freeFockPower A j n
  have hji : freeFockInner vj pi = star (freeFockInner vi pj) := by
    exact freeFockInner_vacuum_power_conj A hA i j n
  rw [← freeFockInner_vacuum_left (K := K) i (freeFockPower A j n)]
  unfold complexQuadraticPolarization realQuadraticPolarization
  simp only [freeFockVectorMoment, sub_eq_add_neg,
    freeFockVacuumSuperposition_add, freeFockPowerSuperposition_add,
    freeFockVacuumSuperposition_neg, freeFockPowerSuperposition_neg,
    freeFockVacuumSuperposition_smul, freeFockPowerSuperposition_smul,
    freeFockVacuumSuperposition_internalBasis,
    freeFockPowerSuperposition_internalBasis,
    freeFockInner_add_left, freeFockInner_add_right,
    freeFockInner_smul_left, freeFockInner_smul_right,
    freeFockInner_neg_left, freeFockInner_neg_right]
  change _ = freeFockInner vi pj
  rw [hji]
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im, Complex.normSq_apply] <;> ring

/-- Matrix of singleton masses, reconstructed by complex polarization. -/
def freeFockMatrixAtomMass
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (a : ℝ) : Matrix I I ℂ :=
  fun i j ↦ complexQuadraticPolarization
    (freeFockVectorAtomMass A hA hker a)
    (freeFockInternalBasis i) (freeFockInternalBasis j)

theorem freeFockMatrixAtomMass_conjTranspose
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (a : ℝ) :
    (freeFockMatrixAtomMass A hA hker a)ᴴ =
      freeFockMatrixAtomMass A hA hker a := by
  ext i j
  change star (complexQuadraticPolarization
      (freeFockVectorAtomMass A hA hker a)
      (freeFockInternalBasis j) (freeFockInternalBasis i)) =
    complexQuadraticPolarization
      (freeFockVectorAtomMass A hA hker a)
      (freeFockInternalBasis i) (freeFockInternalBasis j)
  exact (complexQuadraticPolarization_conj_symm
    (freeFockVectorAtomMass A hA hker a)
    (freeFockVectorAtomMass_smul A hA hker a)
    (freeFockVectorAtomMass_parallelogram A hA hker a)
    (freeFockInternalBasis j) (freeFockInternalBasis i)).symm

theorem sum_smul_freeFockInternalBasis (x : I → ℂ) :
    (∑ i : I, x i • freeFockInternalBasis i) = x := by
  classical
  funext j
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single j (fun i _ hi ↦ by
      show x i • (Pi.single i 1 : I → ℂ) j = 0
      rw [Pi.single_eq_of_ne (Ne.symm hi), smul_zero])
    (fun hj ↦ absurd (Finset.mem_univ j) hj)]
  show x j • (Pi.single j 1 : I → ℂ) j = x j
  rw [Pi.single_eq_same, smul_eq_mul, mul_one]

/-- Singleton mass is exactly the quadratic form of the polarized atom matrix. -/
theorem star_dotProduct_freeFockMatrixAtomMass_mulVec
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (a : ℝ) (x : I → ℂ) :
    star x ⬝ᵥ (freeFockMatrixAtomMass A hA hker a).mulVec x =
      freeFockVectorAtomMass A hA hker a x := by
  let q : (I → ℂ) → ℝ := freeFockVectorAtomMass A hA hker a
  have hsmul : ∀ (c : ℂ) x, q (c • x) = Complex.normSq c * q x :=
    freeFockVectorAtomMass_smul A hA hker a
  have hpar : ∀ x y, q (x + y) + q (x - y) = 2 * q x + 2 * q y :=
    freeFockVectorAtomMass_parallelogram A hA hker a
  have hnonneg : ∀ x, 0 ≤ q x := freeFockVectorAtomMass_nonneg A hA hker a
  have hC : 0 ≤ (Fintype.card I : ℝ) := by positivity
  have hbound : ∀ x, q x ≤ (Fintype.card I : ℝ) * ‖x‖ ^ 2 :=
    freeFockVectorAtomMass_le A hA hker a
  change (∑ i : I, star (x i) * ∑ j : I,
      complexQuadraticPolarization q (freeFockInternalBasis i)
        (freeFockInternalBasis j) * x j) = q x
  calc
    (∑ i : I, star (x i) * ∑ j : I,
        complexQuadraticPolarization q (freeFockInternalBasis i)
          (freeFockInternalBasis j) * x j) =
        ∑ i : I, ∑ j : I, star (x i) * x j *
          complexQuadraticPolarization q (freeFockInternalBasis i)
            (freeFockInternalBasis j) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = ∑ i : I, ∑ j : I,
        complexQuadraticPolarization q (x i • freeFockInternalBasis i)
          (x j • freeFockInternalBasis j) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [complexQuadraticPolarization_smul_left q hsmul hpar hnonneg _ hC hbound,
        complexQuadraticPolarization_smul_right q hsmul hpar hnonneg _ hC hbound]
      ring
    _ = ∑ i : I, complexQuadraticPolarization q
        (x i • freeFockInternalBasis i)
        (∑ j : I, x j • freeFockInternalBasis j) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [complexQuadraticPolarization_sum_right q hsmul hpar hnonneg _ hC hbound]
    _ = complexQuadraticPolarization q
        (∑ i : I, x i • freeFockInternalBasis i)
        (∑ j : I, x j • freeFockInternalBasis j) := by
      rw [complexQuadraticPolarization_sum_left q hsmul hpar hnonneg _ hC hbound]
    _ = complexQuadraticPolarization q x x := by
      rw [sum_smul_freeFockInternalBasis]
    _ = q x := complexQuadraticPolarization_self q hsmul hpar x

theorem freeFockMatrixAtomMass_posSemidef
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (a : ℝ) :
    (freeFockMatrixAtomMass A hA hker a).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact freeFockMatrixAtomMass_conjTranspose A hA hker a
  · intro x
    rw [star_dotProduct_freeFockMatrixAtomMass_mulVec A hA hker a x]
    exact Complex.zero_le_real.mpr
      (freeFockVectorAtomMass_nonneg A hA hker a x)

/-- Compactly supported finite measures have their moment-generating function given by the
absolutely convergent moment series.  Unlike the probability-measure version, this also covers the
zero and non-normalized vector states needed by matrix polarization. -/
theorem compactMomentSeries_summable_of_finite
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (s : ℕ → ℝ) (hμ : HasHamburgerMoments s μ)
    (R : ℝ) (hR : 0 < R)
    (hcarry : μ (Set.Icc (-R) R)ᶜ = 0)
    (u : ℂ) (hu : ‖u‖ * R < 1) :
    Summable (fun n : ℕ ↦ (s n : ℂ) * u ^ n) := by
  let q : ℝ := ‖u‖ * R
  let C : ℝ := μ.real Set.univ
  have hq0 : 0 ≤ q := mul_nonneg (norm_nonneg _) hR.le
  have hqnorm : ‖q‖ < 1 := by
    change |q| < 1
    rw [abs_of_nonneg hq0]
    exact hu
  have hmem : ∀ᵐ x ∂μ, x ∈ Set.Icc (-R) R := by
    change Set.Icc (-R) R ∈ ae μ
    simpa only [compl_compl] using MeasureTheory.compl_mem_ae_iff.mpr hcarry
  let F : ℕ → ℝ → ℂ := fun n x ↦ (u * (x : ℂ)) ^ n
  have hFint : ∀ n, Integrable (F n) μ := by
    intro n
    refine ((hμ n).1.ofReal.const_mul (u ^ n)).congr
      (Filter.Eventually.of_forall fun x ↦ ?_)
    simp [F, mul_pow]
  have hFnorm : ∀ᵐ x ∂μ, ∀ n, ‖F n x‖ ≤ q ^ n := by
    filter_upwards [hmem] with x hx
    intro n
    have hxabs : |x| ≤ R := abs_le.mpr hx
    simp only [F, norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (abs_nonneg _))
      (mul_le_mul_of_nonneg_left hxabs (norm_nonneg _)) n
  have hIntNorm : ∀ n, ∫ x, ‖F n x‖ ∂μ ≤ C * q ^ n := by
    intro n
    calc
      ∫ x, ‖F n x‖ ∂μ ≤ ∫ _x, q ^ n ∂μ := by
        exact integral_mono_ae (hFint n).norm
          (integrable_const (μ := μ) (q ^ n)) (hFnorm.mono fun x hx ↦ hx n)
      _ = C * q ^ n := by simp [C, smul_eq_mul]
  have hsumNorm : Summable (fun n ↦ ∫ x, ‖F n x‖ ∂μ) :=
    Summable.of_nonneg_of_le
      (fun _ ↦ integral_nonneg fun _ ↦ norm_nonneg _)
      hIntNorm (Summable.mul_left C (summable_geometric_of_norm_lt_one hqnorm))
  have hsumIntegralNorm : Summable (fun n ↦ ‖∫ x, F n x ∂μ‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
      (fun n ↦ MeasureTheory.norm_integral_le_integral_norm (F n)) hsumNorm
  have hFintValue : ∀ n, (∫ x, F n x ∂μ) = (s n : ℂ) * u ^ n := by
    intro n
    calc
      (∫ x, F n x ∂μ) = ∫ x, u ^ n * ((x ^ n : ℝ) : ℂ) ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        simp only [F, mul_pow]
        push_cast
        ring
      _ = u ^ n * ∫ x, ((x ^ n : ℝ) : ℂ) ∂μ := by
        rw [MeasureTheory.integral_const_mul]
      _ = u ^ n * ((∫ x, x ^ n ∂μ : ℝ) : ℂ) := by
        congr 1
        exact _root_.integral_ofReal
      _ = (s n : ℂ) * u ^ n := by rw [(hμ n).2]; ring
  exact (Summable.of_norm hsumIntegralNorm).congr hFintValue

theorem compactMomentGeneratingFunction_eq_tsum_of_finite
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (s : ℕ → ℝ) (hμ : HasHamburgerMoments s μ)
    (R : ℝ) (hR : 0 < R)
    (hcarry : μ (Set.Icc (-R) R)ᶜ = 0)
    (u : ℂ) (hu : ‖u‖ * R < 1) :
    compactMomentGeneratingFunction μ u = ∑' n : ℕ, (s n : ℂ) * u ^ n := by
  let q : ℝ := ‖u‖ * R
  let C : ℝ := μ.real Set.univ
  have hq0 : 0 ≤ q := mul_nonneg (norm_nonneg _) hR.le
  have hqnorm : ‖q‖ < 1 := by
    change |q| < 1
    rw [abs_of_nonneg hq0]
    exact hu
  have hmem : ∀ᵐ x ∂μ, x ∈ Set.Icc (-R) R := by
    change Set.Icc (-R) R ∈ ae μ
    simpa only [compl_compl] using MeasureTheory.compl_mem_ae_iff.mpr hcarry
  let F : ℕ → ℝ → ℂ := fun n x ↦ (u * (x : ℂ)) ^ n
  have hFint : ∀ n, Integrable (F n) μ := by
    intro n
    refine ((hμ n).1.ofReal.const_mul (u ^ n)).congr
      (Filter.Eventually.of_forall fun x ↦ ?_)
    simp [F, mul_pow]
  have hFnorm : ∀ᵐ x ∂μ, ∀ n, ‖F n x‖ ≤ q ^ n := by
    filter_upwards [hmem] with x hx
    intro n
    have hxabs : |x| ≤ R := abs_le.mpr hx
    simp only [F, norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (abs_nonneg _))
      (mul_le_mul_of_nonneg_left hxabs (norm_nonneg _)) n
  have hIntNorm : ∀ n, ∫ x, ‖F n x‖ ∂μ ≤ C * q ^ n := by
    intro n
    calc
      ∫ x, ‖F n x‖ ∂μ ≤ ∫ _x, q ^ n ∂μ := by
        exact integral_mono_ae (hFint n).norm
          (integrable_const (μ := μ) (q ^ n)) (hFnorm.mono fun x hx ↦ hx n)
      _ = C * q ^ n := by simp [C, smul_eq_mul]
  have hsumNorm : Summable (fun n ↦ ∫ x, ‖F n x‖ ∂μ) :=
    Summable.of_nonneg_of_le
      (fun _ ↦ integral_nonneg fun _ ↦ norm_nonneg _)
      hIntNorm (Summable.mul_left C (summable_geometric_of_norm_lt_one hqnorm))
  have hFsum : ∀ᵐ x ∂μ, (∑' n, F n x) = (1 - u * (x : ℂ))⁻¹ := by
    filter_upwards [hmem] with x hx
    have hxabs : |x| ≤ R := abs_le.mpr hx
    have hux : ‖u * (x : ℂ)‖ < 1 := by
      calc
        ‖u * (x : ℂ)‖ = ‖u‖ * |x| := by simp [Real.norm_eq_abs]
        _ ≤ ‖u‖ * R := mul_le_mul_of_nonneg_left hxabs (norm_nonneg _)
        _ < 1 := hu
    exact tsum_geometric_of_norm_lt_one hux
  have hFintValue : ∀ n, (∫ x, F n x ∂μ) = (s n : ℂ) * u ^ n := by
    intro n
    calc
      (∫ x, F n x ∂μ) = ∫ x, u ^ n * ((x ^ n : ℝ) : ℂ) ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        simp only [F, mul_pow]
        push_cast
        ring
      _ = u ^ n * ∫ x, ((x ^ n : ℝ) : ℂ) ∂μ := by
        rw [MeasureTheory.integral_const_mul]
      _ = u ^ n * ((∫ x, x ^ n ∂μ : ℝ) : ℂ) := by
        congr 1
        exact _root_.integral_ofReal
      _ = (s n : ℂ) * u ^ n := by rw [(hμ n).2]; ring
  rw [compactMomentGeneratingFunction]
  calc
    (∫ x, (1 - u * (x : ℂ))⁻¹ ∂μ) = ∫ x, ∑' n, F n x ∂μ :=
      integral_congr_ae (Filter.EventuallyEq.symm hFsum)
    _ = ∑' n, ∫ x, F n x ∂μ :=
      (MeasureTheory.integral_tsum_of_summable_integral_norm hFint hsumNorm).symm
    _ = ∑' n, (s n : ℂ) * u ^ n := tsum_congr hFintValue

theorem freeFockVectorMomentSeries_summable
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (x : I → ℂ) (u : ℂ)
    (hu : ‖u‖ * freeFockMatrixSpectralRadius A < 1) :
    Summable (fun n : ℕ ↦ (freeFockVectorMoment A x n : ℂ) * u ^ n) :=
  compactMomentSeries_summable_of_finite
    (freeFockVectorSpectralMeasure A hA hker x)
    (freeFockVectorMoment A x)
    (freeFockVectorSpectralMeasure_hasMoments A hA hker x)
    (freeFockMatrixSpectralRadius A) (freeFockMatrixSpectralRadius_pos A)
    (freeFockVectorSpectralMeasure_carried A hA hker x) u hu

theorem compactMomentGeneratingFunction_freeFockVector_eq_tsum
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (x : I → ℂ) (u : ℂ)
    (hu : ‖u‖ * freeFockMatrixSpectralRadius A < 1) :
    compactMomentGeneratingFunction
        (freeFockVectorSpectralMeasure A hA hker x) u =
      ∑' n : ℕ, (freeFockVectorMoment A x n : ℂ) * u ^ n :=
  compactMomentGeneratingFunction_eq_tsum_of_finite
    (freeFockVectorSpectralMeasure A hA hker x)
    (freeFockVectorMoment A x)
    (freeFockVectorSpectralMeasure_hasMoments A hA hker x)
    (freeFockMatrixSpectralRadius A) (freeFockMatrixSpectralRadius_pos A)
    (freeFockVectorSpectralMeasure_carried A hA hker x) u hu

/-- Full matrix moment-generating function reconstructed from four positive vector states. -/
def freeFockMatrixMomentGeneratingFunction
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (u : ℂ) : Matrix I I ℂ :=
  fun i j ↦
    (4 : ℂ)⁻¹ *
        (compactMomentGeneratingFunction
            (freeFockVectorSpectralMeasure A hA hker
              (freeFockInternalBasis i + freeFockInternalBasis j)) u -
          compactMomentGeneratingFunction
            (freeFockVectorSpectralMeasure A hA hker
              (freeFockInternalBasis i - freeFockInternalBasis j)) u) -
      Complex.I * (4 : ℂ)⁻¹ *
        (compactMomentGeneratingFunction
            (freeFockVectorSpectralMeasure A hA hker
              (freeFockInternalBasis i + Complex.I • freeFockInternalBasis j)) u -
          compactMomentGeneratingFunction
            (freeFockVectorSpectralMeasure A hA hker
              (freeFockInternalBasis i - Complex.I • freeFockInternalBasis j)) u)

theorem coeff_matrixDysonResolventSeries_eq_freeFockPower_entry
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (i j : I) (n : ℕ) :
    PowerSeries.coeff n (matrixDysonResolventSeries A i j) =
      freeFockPower A j n (i, []) := by
  rw [matrixDysonResolventSeries_coeff,
    freeFockPower_vacuumCoefficient A hA]

theorem matrixDysonResolventSeries_entry_absoluteSummableAt
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (i j : I) (u : ℂ) (hu : freeFockSpectralRadius A * ‖u‖ < 1) :
    (matrixDysonResolventSeries A i j).AbsoluteSummableAt u := by
  let q : ℝ := freeFockSpectralRadius A * ‖u‖
  have hq0 : 0 ≤ q := mul_nonneg (freeFockSpectralRadius_pos A).le (norm_nonneg _)
  have hqnorm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    exact hu
  rw [PowerSeries.AbsoluteSummableAt]
  apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ ?_)
    (summable_geometric_of_norm_lt_one hqnorm)
  rw [norm_mul, coeff_matrixDysonResolventSeries_eq_freeFockPower_entry A hA,
    norm_pow]
  calc
    ‖freeFockPower A j n (i, [])‖ * ‖u‖ ^ n ≤
        (2 * matrixFamilyEntryL1 A) ^ n * ‖u‖ ^ n := by
      gcongr
      exact norm_freeFockPower_apply_le A j i [] n
    _ ≤ freeFockSpectralRadius A ^ n * ‖u‖ ^ n := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (norm_nonneg _) _)
      apply pow_le_pow_left₀
        (mul_nonneg (by positivity) (matrixFamilyEntryL1_nonneg A))
      rw [freeFockSpectralRadius]
      linarith
    _ = q ^ n := by rw [← mul_pow]

theorem freeFockSpectralRadius_le_matrixSpectralRadius
    (A : K → Matrix I I ℂ) :
    freeFockSpectralRadius A ≤ freeFockMatrixSpectralRadius A := by
  unfold freeFockMatrixSpectralRadius
  have hR := (freeFockSpectralRadius_pos A).le
  have hc0 : (0 : ℝ) ≤ (Fintype.card I : ℝ) := by positivity
  have hc : (1 : ℝ) ≤ (Fintype.card I : ℝ) + 1 := by linarith
  nlinarith

/-- Entrywise absolute evaluation of a matrix of power series. -/
def matrixPowerSeriesAbsoluteEval
    (H : Matrix I I (PowerSeries ℂ)) (u : ℂ) : Matrix I I ℂ :=
  fun i j ↦ (H i j).absoluteEval u

theorem matrixPowerSeries_mul_absoluteSummableAt
    (H Q : Matrix I I (PowerSeries ℂ)) (u : ℂ)
    (hH : ∀ i j, (H i j).AbsoluteSummableAt u)
    (hQ : ∀ i j, (Q i j).AbsoluteSummableAt u)
    (i j : I) :
    ((H * Q) i j).AbsoluteSummableAt u := by
  rw [Matrix.mul_apply]
  exact PowerSeries.AbsoluteSummableAt.sum Finset.univ _
    (fun l _ ↦ (hH i l).mul (hQ l j))

theorem matrixPowerSeriesAbsoluteEval_mul
    (H Q : Matrix I I (PowerSeries ℂ)) (u : ℂ)
    (hH : ∀ i j, (H i j).AbsoluteSummableAt u)
    (hQ : ∀ i j, (Q i j).AbsoluteSummableAt u) :
    matrixPowerSeriesAbsoluteEval (H * Q) u =
      matrixPowerSeriesAbsoluteEval H u * matrixPowerSeriesAbsoluteEval Q u := by
  ext i j
  rw [matrixPowerSeriesAbsoluteEval, Matrix.mul_apply, Matrix.mul_apply,
    PowerSeries.absoluteEval_sum Finset.univ _
      (fun l _ ↦ (hH i l).mul (hQ l j))]
  apply Finset.sum_congr rfl
  intro l hl
  exact PowerSeries.absoluteEval_mul (hH i l) (hQ l j)

theorem constantPowerSeriesMatrix_absoluteSummableAt
    (M : Matrix I I ℂ) (u : ℂ) (i j : I) :
    (constantPowerSeriesMatrix M i j).AbsoluteSummableAt u :=
  PowerSeries.absoluteSummableAt_C _ _

@[simp]
theorem matrixPowerSeriesAbsoluteEval_constant
    (M : Matrix I I ℂ) (u : ℂ) :
    matrixPowerSeriesAbsoluteEval (constantPowerSeriesMatrix M) u = M := by
  ext i j
  simp [matrixPowerSeriesAbsoluteEval, constantPowerSeriesMatrix]

theorem matrixSemicircleCovariancePowerSeries_absoluteSummableAt
    (A : K → Matrix I I ℂ) (H : Matrix I I (PowerSeries ℂ)) (u : ℂ)
    (hH : ∀ i j, (H i j).AbsoluteSummableAt u) (i j : I) :
    (matrixSemicircleCovariancePowerSeries A H i j).AbsoluteSummableAt u := by
  rw [matrixSemicircleCovariancePowerSeries, Matrix.sum_apply]
  apply PowerSeries.AbsoluteSummableAt.sum Finset.univ
  intro k hk
  exact matrixPowerSeries_mul_absoluteSummableAt
    (constantPowerSeriesMatrix (A k) * H)
    (constantPowerSeriesMatrix (A k)ᴴ) u
    (fun p q ↦ matrixPowerSeries_mul_absoluteSummableAt
      (constantPowerSeriesMatrix (A k)) H u
      (constantPowerSeriesMatrix_absoluteSummableAt (A k) u) hH p q)
    (constantPowerSeriesMatrix_absoluteSummableAt (A k)ᴴ u) i j

theorem matrixPowerSeriesAbsoluteEval_covariance
    (A : K → Matrix I I ℂ) (H : Matrix I I (PowerSeries ℂ)) (u : ℂ)
    (hH : ∀ i j, (H i j).AbsoluteSummableAt u) :
    matrixPowerSeriesAbsoluteEval (matrixSemicircleCovariancePowerSeries A H) u =
      matrixSemicircleCovariance A (matrixPowerSeriesAbsoluteEval H u) := by
  ext i j
  rw [matrixSemicircleCovariancePowerSeries, matrixSemicircleCovariance,
    matrixPowerSeriesAbsoluteEval, Matrix.sum_apply, Matrix.sum_apply,
    PowerSeries.absoluteEval_sum Finset.univ _ (fun k _ ↦
      matrixPowerSeries_mul_absoluteSummableAt
        (constantPowerSeriesMatrix (A k) * H)
        (constantPowerSeriesMatrix (A k)ᴴ) u
        (fun p q ↦ matrixPowerSeries_mul_absoluteSummableAt
          (constantPowerSeriesMatrix (A k)) H u
          (constantPowerSeriesMatrix_absoluteSummableAt (A k) u) hH p q)
        (constantPowerSeriesMatrix_absoluteSummableAt (A k)ᴴ u) i j)]
  apply Finset.sum_congr rfl
  intro k hk
  change matrixPowerSeriesAbsoluteEval
      ((constantPowerSeriesMatrix (A k) * H) *
        constantPowerSeriesMatrix (A k)ᴴ) u i j = _
  rw [matrixPowerSeriesAbsoluteEval_mul
      (constantPowerSeriesMatrix (A k) * H)
      (constantPowerSeriesMatrix (A k)ᴴ) u
      (fun p q ↦ matrixPowerSeries_mul_absoluteSummableAt
        (constantPowerSeriesMatrix (A k)) H u
        (constantPowerSeriesMatrix_absoluteSummableAt (A k) u) hH p q)
      (constantPowerSeriesMatrix_absoluteSummableAt (A k)ᴴ u),
    matrixPowerSeriesAbsoluteEval_mul
      (constantPowerSeriesMatrix (A k)) H u
      (constantPowerSeriesMatrix_absoluteSummableAt (A k) u) hH,
    matrixPowerSeriesAbsoluteEval_constant,
    matrixPowerSeriesAbsoluteEval_constant]

/-- Polarized vector moment series is exactly the full formal matrix Dyson resolvent. -/
theorem freeFockMatrixMomentGeneratingFunction_eq_absoluteEval
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (u : ℂ)
    (hu : ‖u‖ * freeFockMatrixSpectralRadius A < 1) (i j : I) :
    freeFockMatrixMomentGeneratingFunction A hA hker u i j =
      (matrixDysonResolventSeries A i j).absoluteEval u := by
  let e : I → I → ℂ := freeFockInternalBasis
  let fpp : ℕ → ℂ := fun n ↦
    (freeFockVectorMoment A (e i + e j) n : ℂ) * u ^ n
  let fmp : ℕ → ℂ := fun n ↦
    (freeFockVectorMoment A (e i - e j) n : ℂ) * u ^ n
  let fpi : ℕ → ℂ := fun n ↦
    (freeFockVectorMoment A (e i + Complex.I • e j) n : ℂ) * u ^ n
  let fmi : ℕ → ℂ := fun n ↦
    (freeFockVectorMoment A (e i - Complex.I • e j) n : ℂ) * u ^ n
  have hpp : Summable fpp := freeFockVectorMomentSeries_summable A hA hker _ u hu
  have hmp : Summable fmp := freeFockVectorMomentSeries_summable A hA hker _ u hu
  have hpi : Summable fpi := freeFockVectorMomentSeries_summable A hA hker _ u hu
  have hmi : Summable fmi := freeFockVectorMomentSeries_summable A hA hker _ u hu
  have hs1 : Summable (fun n ↦ (4 : ℂ)⁻¹ * (fpp n - fmp n)) :=
    Summable.mul_left (4 : ℂ)⁻¹ (hpp.sub hmp)
  have hs2 : Summable (fun n ↦ Complex.I * (4 : ℂ)⁻¹ * (fpi n - fmi n)) :=
    Summable.mul_left (Complex.I * (4 : ℂ)⁻¹) (hpi.sub hmi)
  rw [freeFockMatrixMomentGeneratingFunction,
    compactMomentGeneratingFunction_freeFockVector_eq_tsum A hA hker _ u hu,
    compactMomentGeneratingFunction_freeFockVector_eq_tsum A hA hker _ u hu,
    compactMomentGeneratingFunction_freeFockVector_eq_tsum A hA hker _ u hu,
    compactMomentGeneratingFunction_freeFockVector_eq_tsum A hA hker _ u hu]
  change (4 : ℂ)⁻¹ * ((∑' n, fpp n) - ∑' n, fmp n) -
      Complex.I * (4 : ℂ)⁻¹ * ((∑' n, fpi n) - ∑' n, fmi n) = _
  rw [← (hpp.hasSum.sub hmp.hasSum).tsum_eq,
    ← (hpi.hasSum.sub hmi.hasSum).tsum_eq,
    ← tsum_mul_left, ← tsum_mul_left,
    ← (hs1.hasSum.sub hs2.hasSum).tsum_eq,
    PowerSeries.absoluteEval]
  apply tsum_congr
  intro n
  rw [coeff_matrixDysonResolventSeries_eq_freeFockPower_entry A hA]
  rw [← complexQuadraticPolarization_freeFockVectorMoment_internalBasis A hA i j n]
  unfold complexQuadraticPolarization realQuadraticPolarization
  simp only [fpp, fmp, fpi, fmi, e]
  push_cast
  ring

/-- The full polarized moment-generating matrix satisfies the matrix Dyson equation near zero. -/
theorem freeFockMatrixMomentGeneratingFunction_dyson
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (u : ℂ)
    (hu : ‖u‖ * freeFockMatrixSpectralRadius A < 1) :
    let M := freeFockMatrixMomentGeneratingFunction A hA hker u
    M = 1 + u ^ 2 • (matrixSemicircleCovariance A M * M) := by
  dsimp only
  let R := matrixDysonResolventSeries A
  let M := freeFockMatrixMomentGeneratingFunction A hA hker u
  have huR : freeFockSpectralRadius A * ‖u‖ < 1 := by
    calc
      freeFockSpectralRadius A * ‖u‖ ≤
          freeFockMatrixSpectralRadius A * ‖u‖ := by
        gcongr
        exact freeFockSpectralRadius_le_matrixSpectralRadius A
      _ = ‖u‖ * freeFockMatrixSpectralRadius A := by ring
      _ < 1 := hu
  have hR : ∀ i j, (R i j).AbsoluteSummableAt u := fun i j ↦
    matrixDysonResolventSeries_entry_absoluteSummableAt A hA i j u huR
  have hCov : ∀ i j,
      (matrixSemicircleCovariancePowerSeries A R i j).AbsoluteSummableAt u :=
    fun i j ↦ matrixSemicircleCovariancePowerSeries_absoluteSummableAt A R u hR i j
  have hProd : ∀ i j,
      ((matrixSemicircleCovariancePowerSeries A R * R) i j).AbsoluteSummableAt u :=
    fun i j ↦ matrixPowerSeries_mul_absoluteSummableAt
      (matrixSemicircleCovariancePowerSeries A R) R u hCov hR i j
  have hEval : matrixPowerSeriesAbsoluteEval R u = M := by
    ext i j
    exact (freeFockMatrixMomentGeneratingFunction_eq_absoluteEval
      A hA hker u hu i j).symm
  have hCovEval : matrixPowerSeriesAbsoluteEval
      (matrixSemicircleCovariancePowerSeries A R) u =
      matrixSemicircleCovariance A M := by
    rw [matrixPowerSeriesAbsoluteEval_covariance A R u hR, hEval]
  ext i j
  have hentry : R i j = (if i = j then 1 else 0) +
      PowerSeries.X ^ 2 *
        (matrixSemicircleCovariancePowerSeries A R * R) i j := by
    have h := congr_fun (congr_fun (matrixDysonResolventSeries_eq A) i) j
    simpa only [Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul,
      one_mul] using h
  have hOne : (1 : PowerSeries ℂ).AbsoluteSummableAt u := by
    rw [PowerSeries.AbsoluteSummableAt]
    apply (hasSum_single 0 (fun n hn ↦ ?_)).summable
    simp [PowerSeries.coeff_one, hn]
  have hConst : ((if i = j then 1 else 0) : PowerSeries ℂ).AbsoluteSummableAt u := by
    by_cases hij : i = j
    · simpa [hij] using hOne
    · simpa [hij] using PowerSeries.absoluteSummableAt_zero u
  have heval := congrArg (fun f : PowerSeries ℂ ↦ f.absoluteEval u) hentry
  rw [PowerSeries.absoluteEval_add
      hConst
      (((PowerSeries.X_absoluteSummableAt u).pow 2).mul (hProd i j)),
    PowerSeries.absoluteEval_mul ((PowerSeries.X_absoluteSummableAt u).pow 2)
      (hProd i j),
    PowerSeries.absoluteEval_pow (PowerSeries.X_absoluteSummableAt u),
    PowerSeries.absoluteEval_X] at heval
  have hConstEval :
      ((if i = j then 1 else 0) : PowerSeries ℂ).absoluteEval u =
        (if i = j then 1 else 0 : ℂ) := by
    by_cases hij : i = j
    · simp only [hij, if_true]
      rw [PowerSeries.absoluteEval]
      rw [tsum_eq_single 0]
      · simp
      · intro n hn
        simp [PowerSeries.coeff_one, hn]
    · simp [hij, PowerSeries.absoluteEval_zero]
  rw [hConstEval] at heval
  have hProdEval : matrixPowerSeriesAbsoluteEval
      (matrixSemicircleCovariancePowerSeries A R * R) u =
      matrixSemicircleCovariance A M * M := by
    rw [matrixPowerSeriesAbsoluteEval_mul
      (matrixSemicircleCovariancePowerSeries A R) R u hCov hR,
      hCovEval, hEval]
  change M i j =
    ((1 : Matrix I I ℂ) + u ^ 2 •
      (matrixSemicircleCovariance A M * M)) i j
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul]
  calc
    M i j = matrixPowerSeriesAbsoluteEval R u i j := by rw [hEval]
    _ = (if i = j then 1 else 0) + u ^ 2 *
        matrixPowerSeriesAbsoluteEval
          (matrixSemicircleCovariancePowerSeries A R * R) u i j := heval
    _ = (if i = j then 1 else 0) + u ^ 2 *
        (matrixSemicircleCovariance A M * M) i j := by rw [hProdEval]

/-- Matrix coefficient of the `n`th free-Fock vacuum moment. -/
def freeFockMatrixMomentCoefficient
    (A : K → Matrix I I ℂ) (n : ℕ) : Matrix I I ℂ :=
  fun i j ↦ freeFockPower A j n (i, [])

theorem freeFockInner_vacuumSuperposition_powerSuperposition
    (A : K → Matrix I I ℂ) (x : I → ℂ) (n : ℕ) :
    freeFockInner (freeFockVacuumSuperposition x)
        (freeFockPowerSuperposition A x n) =
      star x ⬝ᵥ (freeFockMatrixMomentCoefficient A n).mulVec x := by
  simp only [freeFockVacuumSuperposition, freeFockPowerSuperposition,
    freeFockInner_finset_sum_left, freeFockInner_finset_sum_right,
    freeFockInner_smul_left, freeFockInner_smul_right,
    freeFockInner_vacuum_left, dotProduct, Matrix.mulVec,
    freeFockMatrixMomentCoefficient, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [Pi.star_apply]
  ring

theorem freeFockInner_vacuumSuperposition_powerSuperposition_im
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (x : I → ℂ) (n : ℕ) :
    (freeFockInner (freeFockVacuumSuperposition x)
      (freeFockPowerSuperposition A x n)).im = 0 := by
  let z := freeFockInner (freeFockVacuumSuperposition x)
    (freeFockPowerSuperposition A x n)
  have hright := freeFockInner_powerSuperposition A hA x n 0
  have hright' : freeFockInner (freeFockPowerSuperposition A x n)
      (freeFockVacuumSuperposition x) = z := by
    simpa [z, freeFockPowerSuperposition_zero] using hright
  have hconj := freeFockInner_conj_symm
    (freeFockVacuumSuperposition x) (freeFockPowerSuperposition A x n)
  have hz : z = star z := by
    calc
      z = star (freeFockInner (freeFockPowerSuperposition A x n)
          (freeFockVacuumSuperposition x)) := hconj
      _ = star z := by rw [hright']
  have him := congrArg Complex.im hz
  change z.im = 0
  have him' : z.im = -z.im := by simpa using him
  linarith

/-- Every matrix moment coefficient has the intended arbitrary-vector vacuum quadratic form. -/
theorem star_dotProduct_freeFockMatrixMomentCoefficient_mulVec
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (x : I → ℂ) (n : ℕ) :
    star x ⬝ᵥ (freeFockMatrixMomentCoefficient A n).mulVec x =
      (freeFockVectorMoment A x n : ℂ) := by
  rw [← freeFockInner_vacuumSuperposition_powerSuperposition]
  unfold freeFockVectorMoment
  apply Complex.ext
  · simp
  · simp [freeFockInner_vacuumSuperposition_powerSuperposition_im A hA x n]

theorem tsum_finset_comm_of_summable
    {J : Type*} (s : Finset J) (f : J → ℕ → ℂ)
    (hf : ∀ j ∈ s, Summable (f j)) :
    (∑ j ∈ s, ∑' n, f j n) = ∑' n, ∑ j ∈ s, f j n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hjs ih =>
      rw [Finset.sum_insert hjs,
        ih (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))]
      simp only [Finset.sum_insert hjs]
      exact ((hf j (Finset.mem_insert_self j s)).tsum_add
        (summable_sum (s := s)
          (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)))).symm

/-- The full moment-generating matrix has every vector spectral MGF as its quadratic form. -/
theorem star_dotProduct_freeFockMatrixMomentGeneratingFunction_mulVec
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (x : I → ℂ) (u : ℂ)
    (hu : ‖u‖ * freeFockMatrixSpectralRadius A < 1) :
    star x ⬝ᵥ (freeFockMatrixMomentGeneratingFunction A hA hker u).mulVec x =
      compactMomentGeneratingFunction
        (freeFockVectorSpectralMeasure A hA hker x) u := by
  let f : I → I → ℕ → ℂ := fun i j n ↦
    star (x i) *
      (PowerSeries.coeff n (matrixDysonResolventSeries A i j) * u ^ n) * x j
  have huR : freeFockSpectralRadius A * ‖u‖ < 1 := by
    calc
      freeFockSpectralRadius A * ‖u‖ ≤
          freeFockMatrixSpectralRadius A * ‖u‖ := by
        gcongr
        exact freeFockSpectralRadius_le_matrixSpectralRadius A
      _ = ‖u‖ * freeFockMatrixSpectralRadius A := by ring
      _ < 1 := hu
  have hcoeff : ∀ i j, Summable (fun n : ℕ ↦
      PowerSeries.coeff n (matrixDysonResolventSeries A i j) * u ^ n) := by
    intro i j
    exact (matrixDysonResolventSeries_entry_absoluteSummableAt
      A hA i j u huR).summable
  have hf : ∀ i j, Summable (f i j) := by
    intro i j
    exact ((hcoeff i j).mul_left (star (x i))).mul_right (x j)
  rw [compactMomentGeneratingFunction_freeFockVector_eq_tsum A hA hker x u hu]
  calc
    star x ⬝ᵥ (freeFockMatrixMomentGeneratingFunction A hA hker u).mulVec x =
        ∑ i : I, ∑ j : I, star (x i) *
          freeFockMatrixMomentGeneratingFunction A hA hker u i j * x j := by
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = ∑ i : I, ∑ j : I, ∑' n, f i j n := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [freeFockMatrixMomentGeneratingFunction_eq_absoluteEval A hA hker u hu i j,
        PowerSeries.absoluteEval]
      rw [← tsum_mul_left, ← tsum_mul_right]
    _ = ∑ i : I, ∑' n, ∑ j : I, f i j n := by
      apply Finset.sum_congr rfl
      intro i hi
      exact tsum_finset_comm_of_summable Finset.univ (f i)
        (fun j hj ↦ hf i j)
    _ = ∑' n, ∑ i : I, ∑ j : I, f i j n := by
      exact tsum_finset_comm_of_summable Finset.univ
        (fun i n ↦ ∑ j : I, f i j n)
        (fun i hi ↦ summable_sum (fun j hj ↦ hf i j))
    _ = ∑' n, (freeFockVectorMoment A x n : ℂ) * u ^ n := by
      apply tsum_congr
      intro n
      rw [← star_dotProduct_freeFockMatrixMomentCoefficient_mulVec A hA x n]
      simp only [f, dotProduct, Matrix.mulVec, freeFockMatrixMomentCoefficient,
        Finset.mul_sum, Pi.star_apply]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      rw [coeff_matrixDysonResolventSeries_eq_freeFockPower_entry A hA]
      ring

/-- Stieltjes transform of the spectral measure generated by an arbitrary internal vector. -/
def freeFockVectorStieltjes
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (x : I → ℂ) (z : ℂ) : ℂ :=
  ∫ t : ℝ, ((t : ℂ) - z)⁻¹ ∂(freeFockVectorSpectralMeasure A hA hker x)

theorem freeFockVectorStieltjes_eq_neg_mul_mgf
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (x : I → ℂ) (u : ℂ) (hu : u ≠ 0) :
    freeFockVectorStieltjes A hA hker x u⁻¹ =
      -u * compactMomentGeneratingFunction
        (freeFockVectorSpectralMeasure A hA hker x) u := by
  exact stieltjesTransform_inv_eq_neg_mul_compactMomentGeneratingFunction _ u hu

/-- Full matrix Stieltjes transform reconstructed from four positive vector states. -/
def freeFockMatrixStieltjes
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (z : ℂ) : Matrix I I ℂ :=
  fun i j ↦
    (4 : ℂ)⁻¹ *
        (freeFockVectorStieltjes A hA hker
            (freeFockInternalBasis i + freeFockInternalBasis j) z -
          freeFockVectorStieltjes A hA hker
            (freeFockInternalBasis i - freeFockInternalBasis j) z) -
      Complex.I * (4 : ℂ)⁻¹ *
        (freeFockVectorStieltjes A hA hker
            (freeFockInternalBasis i + Complex.I • freeFockInternalBasis j) z -
          freeFockVectorStieltjes A hA hker
            (freeFockInternalBasis i - Complex.I • freeFockInternalBasis j) z)

theorem freeFockMatrixStieltjes_inv_eq_neg_mul_mgf
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (u : ℂ) (hu : u ≠ 0) (i j : I) :
    freeFockMatrixStieltjes A hA hker u⁻¹ i j =
      -u * freeFockMatrixMomentGeneratingFunction A hA hker u i j := by
  rw [freeFockMatrixStieltjes, freeFockMatrixMomentGeneratingFunction,
    freeFockVectorStieltjes_eq_neg_mul_mgf A hA hker _ u hu,
    freeFockVectorStieltjes_eq_neg_mul_mgf A hA hker _ u hu,
    freeFockVectorStieltjes_eq_neg_mul_mgf A hA hker _ u hu,
    freeFockVectorStieltjes_eq_neg_mul_mgf A hA hker _ u hu]
  ring

theorem freeFockMatrixStieltjes_inv_eq_neg_mul_absoluteEval
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (u : ℂ) (hu0 : u ≠ 0)
    (hu : ‖u‖ * freeFockMatrixSpectralRadius A < 1) (i j : I) :
    freeFockMatrixStieltjes A hA hker u⁻¹ i j =
      -u * (matrixDysonResolventSeries A i j).absoluteEval u := by
  rw [freeFockMatrixStieltjes_inv_eq_neg_mul_mgf A hA hker u hu0 i j,
    freeFockMatrixMomentGeneratingFunction_eq_absoluteEval A hA hker u hu i j]

/-- On the exterior convergence region, the full matrix Stieltjes transform has every vector
Stieltjes transform as its quadratic form. -/
theorem star_dotProduct_freeFockMatrixStieltjes_mulVec_exterior
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (x : I → ℂ) (z : ℂ)
    (hz : freeFockMatrixSpectralRadius A < ‖z‖) :
    star x ⬝ᵥ (freeFockMatrixStieltjes A hA hker z).mulVec x =
      freeFockVectorStieltjes A hA hker x z := by
  have hz0 : z ≠ 0 := fun hzero ↦ by
    rw [hzero, norm_zero] at hz
    linarith [freeFockMatrixSpectralRadius_pos A]
  let u : ℂ := z⁻¹
  have hu0 : u ≠ 0 := inv_ne_zero hz0
  have hu : ‖u‖ * freeFockMatrixSpectralRadius A < 1 := by
    rw [show u = z⁻¹ by rfl, norm_inv]
    simpa [div_eq_mul_inv, mul_comm] using
      (div_lt_one (norm_pos_iff.mpr hz0)).mpr hz
  have huinv : u⁻¹ = z := by simp [u]
  have hG : freeFockMatrixStieltjes A hA hker z =
      (-u) • freeFockMatrixMomentGeneratingFunction A hA hker u := by
    ext i j
    have hij := freeFockMatrixStieltjes_inv_eq_neg_mul_mgf
      A hA hker u hu0 i j
    simpa only [huinv, Matrix.smul_apply, smul_eq_mul] using hij
  rw [hG, Matrix.smul_mulVec, dotProduct_smul,
    star_dotProduct_freeFockMatrixMomentGeneratingFunction_mulVec A hA hker x u hu]
  simpa only [huinv, smul_eq_mul] using
    (freeFockVectorStieltjes_eq_neg_mul_mgf A hA hker x u hu0).symm

/-- Cleared matrix Dyson residual for the sign convention `∫ (t-z)⁻¹ dμ(t)`. -/
def freeFockMatrixDysonResidual
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (z : ℂ) : Matrix I I ℂ :=
  let G := freeFockMatrixStieltjes A hA hker z
  1 + (z • (1 : Matrix I I ℂ) + matrixSemicircleCovariance A G) * G

/-- Matrix Dyson equation on the exterior region where the moment series converges. -/
theorem freeFockMatrixDysonResidual_exterior
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (z : ℂ)
    (hz : freeFockMatrixSpectralRadius A < ‖z‖) :
    freeFockMatrixDysonResidual A hA hker z = 0 := by
  have hz0 : z ≠ 0 := fun hzero ↦ by
    rw [hzero, norm_zero] at hz
    linarith [freeFockMatrixSpectralRadius_pos A]
  let u : ℂ := z⁻¹
  let M := freeFockMatrixMomentGeneratingFunction A hA hker u
  let G := freeFockMatrixStieltjes A hA hker z
  have hu0 : u ≠ 0 := inv_ne_zero hz0
  have hu : ‖u‖ * freeFockMatrixSpectralRadius A < 1 := by
    rw [show u = z⁻¹ by rfl, norm_inv]
    simpa [div_eq_mul_inv, mul_comm] using
      (div_lt_one (norm_pos_iff.mpr hz0)).mpr hz
  have hM : M = 1 + u ^ 2 • (matrixSemicircleCovariance A M * M) :=
    freeFockMatrixMomentGeneratingFunction_dyson A hA hker u hu
  have hG : G = (-u) • M := by
    ext i j
    have h := freeFockMatrixStieltjes_inv_eq_neg_mul_mgf A hA hker u hu0 i j
    have huinv : u⁻¹ = z := by simp [u]
    simpa [G, M, huinv, Matrix.smul_apply, smul_eq_mul] using h
  have hCovG : matrixSemicircleCovariance A G =
      (-u) • matrixSemicircleCovariance A M := by
    rw [hG, matrixSemicircleCovariance_smul]
  have hzu : z * u = 1 := by simp [u, hz0]
  have hnzu : -z * u = -1 := by rw [neg_mul, hzu]
  unfold freeFockMatrixDysonResidual
  dsimp only
  change 1 + (z • (1 : Matrix I I ℂ) + matrixSemicircleCovariance A G) * G = 0
  rw [hCovG, hG]
  ext i j
  have hMij := congr_fun (congr_fun hM i) j
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_apply] at hMij ⊢
  simp only [Matrix.zero_apply, add_mul, Finset.sum_add_distrib]
  have hdelta :
      (∑ x : I, (z * if i = x then 1 else 0) * (-u * M x j)) =
        -z * u * M i j := by
    rw [Finset.sum_eq_single i]
    · simp
      ring
    · intro x hx hxi
      rw [if_neg (Ne.symm hxi)]
      simp
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hcovsum :
      (∑ x : I, (-u * matrixSemicircleCovariance A M i x) * (-u * M x j)) =
        u ^ 2 * ∑ x : I, matrixSemicircleCovariance A M i x * M x j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  rw [hdelta, hcovsum, hnzu]
  linear_combination -hMij

theorem freeFockMatrixStieltjes_differentiableOn
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (i j : I) :
    DifferentiableOn ℂ (fun z ↦ freeFockMatrixStieltjes A hA hker z i j)
      {z : ℂ | 0 < z.im} := by
  intro z hz
  have hv : ∀ x : I → ℂ,
      DifferentiableAt ℂ (freeFockVectorStieltjes A hA hker x) z := fun x ↦
    (HTGeometry.stieltjes_hasDerivAt z hz).differentiableAt
  have hpp := hv (freeFockInternalBasis i + freeFockInternalBasis j)
  have hmp := hv (freeFockInternalBasis i - freeFockInternalBasis j)
  have hpi := hv (freeFockInternalBasis i + Complex.I • freeFockInternalBasis j)
  have hmi := hv (freeFockInternalBasis i - Complex.I • freeFockInternalBasis j)
  have hc : DifferentiableAt ℂ (fun _w : ℂ ↦ (4 : ℂ)⁻¹) z := differentiableAt_const _
  have hcI : DifferentiableAt ℂ
      (fun _w : ℂ ↦ Complex.I * (4 : ℂ)⁻¹) z := differentiableAt_const _
  exact ((hc.mul (hpp.sub hmp)).sub (hcI.mul (hpi.sub hmi))).differentiableWithinAt

set_option maxHeartbeats 1000000 in
/-- Throughout the upper half-plane, the full matrix Stieltjes transform has every vector
Stieltjes transform as its quadratic form. -/
theorem star_dotProduct_freeFockMatrixStieltjes_mulVec
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (x : I → ℂ) (z : ℂ) (hz : 0 < z.im) :
    star x ⬝ᵥ (freeFockMatrixStieltjes A hA hker z).mulVec x =
      freeFockVectorStieltjes A hA hker x z := by
  let U : Set ℂ := {w | 0 < w.im}
  let F : ℂ → ℂ := fun w ↦
    star x ⬝ᵥ (freeFockMatrixStieltjes A hA hker w).mulVec x
  let S : ℂ → ℂ := freeFockVectorStieltjes A hA hker x
  let z₀ : ℂ := (freeFockMatrixSpectralRadius A + 1) * Complex.I
  have hz₀U : z₀ ∈ U := by
    change 0 < z₀.im
    simp [z₀]
    linarith [freeFockMatrixSpectralRadius_pos A]
  have hz₀ext : freeFockMatrixSpectralRadius A < ‖z₀‖ := by
    dsimp [z₀]
    rw [norm_mul, show ((freeFockMatrixSpectralRadius A : ℂ) + 1) =
      ((freeFockMatrixSpectralRadius A + 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one,
      abs_of_pos (by linarith [freeFockMatrixSpectralRadius_pos A])]
    linarith
  have hseed : Filter.Eventually (fun w ↦ F w = S w) (nhds z₀) := by
    have hopen : IsOpen {w : ℂ | freeFockMatrixSpectralRadius A < ‖w‖} :=
      isOpen_lt continuous_const continuous_norm
    filter_upwards [hopen.mem_nhds hz₀ext] with w hw
    exact star_dotProduct_freeFockMatrixStieltjes_mulVec_exterior
      A hA hker x w hw
  have hFdiff : DifferentiableOn ℂ F U := by
    intro w hw
    have hentry : ∀ i j, DifferentiableAt ℂ
        (fun q ↦ freeFockMatrixStieltjes A hA hker q i j) w := fun i j ↦
      (freeFockMatrixStieltjes_differentiableOn A hA hker i j w hw).differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hw)
    dsimp only [F]
    simp only [dotProduct, Matrix.mulVec]
    have hinner : ∀ i, DifferentiableAt ℂ
        (fun q ↦ ∑ j : I,
          freeFockMatrixStieltjes A hA hker q i j * x j) w := by
      intro i
      have hs := DifferentiableAt.sum (𝕜 := ℂ) (x := w)
        (A := fun j q ↦ freeFockMatrixStieltjes A hA hker q i j * x j)
        (u := (Finset.univ : Finset I)) (fun j hj ↦
          (hentry i j).mul (differentiableAt_const _))
      exact hs.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun q ↦ by simp)
    have houter := DifferentiableAt.sum (𝕜 := ℂ) (x := w)
      (A := fun i q ↦ star (x i) *
        ∑ j : I, freeFockMatrixStieltjes A hA hker q i j * x j)
      (u := (Finset.univ : Finset I)) (fun i hi ↦
        (differentiableAt_const _).mul (hinner i))
    exact houter.differentiableWithinAt.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun q ↦ by simp) (by simp)
  have hSdiff : DifferentiableOn ℂ S U := by
    intro w hw
    exact (HTGeometry.stieltjes_hasDerivAt w hw).differentiableAt.differentiableWithinAt
  have hEq := hFdiff.analyticOnNhd
      (isOpen_lt continuous_const Complex.continuous_im) |>.eqOn_of_preconnected_of_eventuallyEq
        (hSdiff.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_im))
        (convex_halfSpace_im_gt 0).isPreconnected hz₀U hseed
  exact hEq hz

omit [DecidableEq K] in
theorem star_dotProduct_conjTranspose_mulVec_eq_star
    (M : Matrix I I ℂ) (x : I → ℂ) :
    star x ⬝ᵥ Mᴴ.mulVec x = star (star x ⬝ᵥ M.mulVec x) := by
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, RCLike.star_def, map_sum, map_mul,
    Matrix.conjTranspose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp
  ring

/-- Hermitian imaginary part `(M - Mᴴ)/(2i)`. -/
def matrixHermitianImaginaryPart (M : Matrix I I ℂ) : Matrix I I ℂ :=
  (-Complex.I / 2) • (M - Mᴴ)

omit [DecidableEq K] in
theorem matrixHermitianImaginaryPart_conjTranspose (M : Matrix I I ℂ) :
    (matrixHermitianImaginaryPart M)ᴴ = matrixHermitianImaginaryPart M := by
  ext i j
  simp [matrixHermitianImaginaryPart, Matrix.conjTranspose_apply, Complex.star_def]
  ring

omit [DecidableEq K] in
theorem star_dotProduct_matrixHermitianImaginaryPart_mulVec
    (M : Matrix I I ℂ) (x : I → ℂ) :
    star x ⬝ᵥ (matrixHermitianImaginaryPart M).mulVec x =
      ((star x ⬝ᵥ M.mulVec x).im : ℂ) := by
  rw [matrixHermitianImaginaryPart, Matrix.smul_mulVec, dotProduct_smul,
    Matrix.sub_mulVec, dotProduct_sub,
    star_dotProduct_conjTranspose_mulVec_eq_star]
  rw [smul_eq_mul]
  apply Complex.ext <;> simp [Complex.star_def] <;> ring

/-- The imaginary part of the matrix Stieltjes transform is strictly positive definite in the
upper half-plane. -/
theorem freeFockMatrixStieltjes_hermitianImaginaryPart_posDef
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (z : ℂ) (hz : 0 < z.im) :
    (matrixHermitianImaginaryPart
      (freeFockMatrixStieltjes A hA hker z)).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · exact matrixHermitianImaginaryPart_conjTranspose _
  · intro x hx
    rw [star_dotProduct_matrixHermitianImaginaryPart_mulVec,
      star_dotProduct_freeFockMatrixStieltjes_mulVec A hA hker x z hz]
    apply Complex.zero_lt_real.mpr
    have hmassReal : 0 <
        ((freeFockVectorSpectralMeasure A hA hker x) Set.univ).toReal := by
      rw [freeFockVectorSpectralMeasure_totalMass]
      simpa only [Complex.sq_norm] using dotProduct_star_self_pos hx
    have hmass : 0 < (freeFockVectorSpectralMeasure A hA hker x) Set.univ :=
      (ENNReal.toReal_pos_iff.mp hmassReal).1
    exact HTGeometry.stieltjesTransform_im_pos z hz hmass
      (HTGeometry.integrable_cauchy_kernel
        (freeFockVectorSpectralMeasure A hA hker x) (ne_of_gt hz))

set_option maxHeartbeats 1000000 in
theorem freeFockMatrixDysonResidual_entry_differentiableOn
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (i j : I) :
    DifferentiableOn ℂ (fun z ↦ freeFockMatrixDysonResidual A hA hker z i j)
      {z : ℂ | 0 < z.im} := by
  intro z hz
  have hG : ∀ p q, DifferentiableAt ℂ
      (fun w ↦ freeFockMatrixStieltjes A hA hker w p q) z := fun p q ↦
    (freeFockMatrixStieltjes_differentiableOn A hA hker p q z hz).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz)
  have hCov : ∀ p q, DifferentiableAt ℂ
      (fun w ↦ matrixSemicircleCovariance A
        (freeFockMatrixStieltjes A hA hker w) p q) z := by
    intro p q
    unfold matrixSemicircleCovariance
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
    fun_prop
  have hterm : ∀ l : I, DifferentiableAt ℂ (fun w ↦
      (w * (if i = l then 1 else 0) +
        matrixSemicircleCovariance A
          (freeFockMatrixStieltjes A hA hker w) i l) *
        freeFockMatrixStieltjes A hA hker w l j) z := by
    intro l
    exact ((differentiableAt_id.mul (differentiableAt_const _)).add (hCov i l)).mul
      (hG l j)
  have hsum : DifferentiableAt ℂ (fun w ↦
      ∑ l : I, (w * (if i = l then 1 else 0) +
        matrixSemicircleCovariance A
          (freeFockMatrixStieltjes A hA hker w) i l) *
        freeFockMatrixStieltjes A hA hker w l j) z := by
    fun_prop
  change DifferentiableWithinAt ℂ (fun w ↦
      (if i = j then 1 else 0) +
        ∑ l : I, (w * (if i = l then 1 else 0) +
          matrixSemicircleCovariance A
            (freeFockMatrixStieltjes A hA hker w) i l) *
          freeFockMatrixStieltjes A hA hker w l j)
      {z : ℂ | 0 < z.im} z
  exact (hsum.const_add _).differentiableWithinAt

theorem freeFockMatrixDysonResidual_upperHalfPlane_entry
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (i j : I) (z : ℂ) (hz : 0 < z.im) :
    freeFockMatrixDysonResidual A hA hker z i j = 0 := by
  let U : Set ℂ := {w | 0 < w.im}
  let z₀ : ℂ := (freeFockMatrixSpectralRadius A + 1) * Complex.I
  have hz₀U : z₀ ∈ U := by
    change 0 < z₀.im
    simp [z₀]
    linarith [freeFockMatrixSpectralRadius_pos A]
  have hz₀ext : freeFockMatrixSpectralRadius A < ‖z₀‖ := by
    dsimp [z₀]
    rw [norm_mul, show ((freeFockMatrixSpectralRadius A : ℂ) + 1) =
      ((freeFockMatrixSpectralRadius A + 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one,
      abs_of_pos (by linarith [freeFockMatrixSpectralRadius_pos A])]
    linarith
  have hseed : Filter.Eventually
      (fun w ↦ freeFockMatrixDysonResidual A hA hker w i j = 0) (nhds z₀) := by
    have hopen : IsOpen {w : ℂ | freeFockMatrixSpectralRadius A < ‖w‖} :=
      isOpen_lt continuous_const continuous_norm
    filter_upwards [hopen.mem_nhds hz₀ext] with w hw
    have h := freeFockMatrixDysonResidual_exterior A hA hker w hw
    exact congr_fun (congr_fun h i) j
  have hanalytic : AnalyticOnNhd ℂ
      (fun w ↦ freeFockMatrixDysonResidual A hA hker w i j) U :=
    (freeFockMatrixDysonResidual_entry_differentiableOn A hA hker i j).analyticOnNhd
      (isOpen_lt continuous_const Complex.continuous_im)
  have hzero : AnalyticOnNhd ℂ (fun _w : ℂ ↦ (0 : ℂ)) U := analyticOnNhd_const
  have hEq := hanalytic.eqOn_of_preconnected_of_eventuallyEq hzero
    (convex_halfSpace_im_gt 0).isPreconnected hz₀U hseed
  exact hEq hz

/-- Full matrix Dyson equation throughout the upper half-plane. -/
theorem freeFockMatrixDysonResidual_upperHalfPlane
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (z : ℂ) (hz : 0 < z.im) :
    freeFockMatrixDysonResidual A hA hker z = 0 := by
  ext i j
  exact freeFockMatrixDysonResidual_upperHalfPlane_entry A hA hker i j z hz

/-- Height-scaled matrix Stieltjes boundary equals `i` times the PSD atom matrix. -/
theorem freeFockMatrixStieltjes_atom_boundary
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (a : ℝ) (i j : I) :
    Tendsto (fun y : ℝ ↦ (y : ℂ) *
      freeFockMatrixStieltjes A hA hker
        ((a : ℂ) + (y : ℂ) * Complex.I) i j)
      (nhdsWithin 0 {0}ᶜ)
      (nhds (Complex.I * freeFockMatrixAtomMass A hA hker a i j)) := by
  let e : I → I → ℂ := freeFockInternalBasis
  let μpp := freeFockVectorSpectralMeasure A hA hker (e i + e j)
  let μmp := freeFockVectorSpectralMeasure A hA hker (e i - e j)
  let μpi := freeFockVectorSpectralMeasure A hA hker (e i + Complex.I • e j)
  let μmi := freeFockVectorSpectralMeasure A hA hker (e i - Complex.I • e j)
  have hpp := tendsto_mul_stieltjes_atomMass μpp a
  have hmp := tendsto_mul_stieltjes_atomMass μmp a
  have hpi := tendsto_mul_stieltjes_atomMass μpi a
  have hmi := tendsto_mul_stieltjes_atomMass μmi a
  have hc4 : Tendsto (fun _y : ℝ ↦ (4 : ℂ)⁻¹)
      (nhdsWithin 0 {0}ᶜ) (nhds (4 : ℂ)⁻¹) := tendsto_const_nhds
  have hcI4 : Tendsto (fun _y : ℝ ↦ Complex.I * (4 : ℂ)⁻¹)
      (nhdsWithin 0 {0}ᶜ) (nhds (Complex.I * (4 : ℂ)⁻¹)) := tendsto_const_nhds
  have h := (hc4.mul (hpp.sub hmp)).sub (hcI4.mul (hpi.sub hmi))
  convert h using 1
  · funext y
    simp only [freeFockMatrixStieltjes, freeFockVectorStieltjes, e, μpp, μmp, μpi, μmi]
    ring
  · unfold freeFockMatrixAtomMass complexQuadraticPolarization
    unfold realQuadraticPolarization freeFockVectorAtomMass
    simp only [e, μpp, μmp, μpi, μmi]
    push_cast
    ring

/-- The covariance image of an atom annihilates the atom matrix.  This is the leading boundary
coefficient of the full matrix Dyson equation and is the matrix analogue of the fact that every
positive-weight neighbour of a scalar atom lies outside its atom support. -/
theorem matrixSemicircleCovariance_freeFockMatrixAtomMass_mul_eq_zero
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (a : ℝ) :
    matrixSemicircleCovariance A (freeFockMatrixAtomMass A hA hker a) *
        freeFockMatrixAtomMass A hA hker a = 0 := by
  let z : ℝ → ℂ := fun y ↦ (a : ℂ) + (y : ℂ) * Complex.I
  let G : ℝ → Matrix I I ℂ := fun y ↦ freeFockMatrixStieltjes A hA hker (z y)
  let H : ℝ → Matrix I I ℂ := fun y ↦ (y : ℂ) • G y
  let M : Matrix I I ℂ := freeFockMatrixAtomMass A hA hker a
  have hright_le : 𝓝[>] (0 : ℝ) ≤ nhdsWithin 0 {0}ᶜ := by
    apply nhdsWithin_mono
    intro y hy
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using (ne_of_gt hy)
  have hH (i j : I) : Tendsto (fun y ↦ H y i j) (𝓝[>] (0 : ℝ))
      (𝓝 ((Complex.I • M) i j)) := by
    have hij := (freeFockMatrixStieltjes_atom_boundary A hA hker a i j).mono_left
      hright_le
    simpa only [H, G, z, Matrix.smul_apply, smul_eq_mul] using hij
  have hCov (i j : I) : Tendsto
      (fun y ↦ matrixSemicircleCovariance A (H y) i j)
      (𝓝[>] (0 : ℝ)) (𝓝 (matrixSemicircleCovariance A (Complex.I • M) i j)) := by
    have hsum : Tendsto
        (fun y ↦ ∑ k : K, ∑ q : I,
          (∑ p : I, A k i p * H y p q) * star (A k j q))
        (𝓝[>] (0 : ℝ))
        (𝓝 (∑ k : K, ∑ q : I,
          (∑ p : I, A k i p * (Complex.I • M) p q) * star (A k j q))) := by
      apply tendsto_finsetSum
      intro k hk
      apply tendsto_finsetSum
      intro q hq
      apply Tendsto.mul
      · apply tendsto_finsetSum
        intro p hp
        exact tendsto_const_nhds.mul (hH p q)
      · exact tendsto_const_nhds
    simpa only [matrixSemicircleCovariance, Matrix.sum_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply] using hsum
  have hleft (i j : I) : Tendsto
      (fun y ↦ (matrixSemicircleCovariance A (H y) * H y) i j)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((matrixSemicircleCovariance A (Complex.I • M) * (Complex.I • M)) i j)) := by
    simp only [Matrix.mul_apply]
    apply tendsto_finsetSum
    intro p hp
    exact (hCov i p).mul (hH p j)
  have hscaled : ∀ᶠ y : ℝ in 𝓝[>] 0,
      matrixSemicircleCovariance A (H y) * H y =
        -(((y : ℂ) ^ 2) • (1 : Matrix I I ℂ) +
          ((y : ℂ) * z y) • H y) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hres := freeFockMatrixDysonResidual_upperHalfPlane A hA hker (z y) (by
      simpa [z, Complex.mul_im] using hy)
    have hcore : matrixSemicircleCovariance A (G y) * G y =
        -(1 + (z y) • G y) := by
      ext i j
      have hresij := congr_fun (congr_fun hres i) j
      simp only [freeFockMatrixDysonResidual, G, Matrix.add_apply,
        Matrix.one_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
        Matrix.neg_apply, Matrix.zero_apply, add_mul, Finset.sum_add_distrib] at hresij ⊢
      have hdiag :
          (∑ x : I, (z y * if i = x then 1 else 0) * G y x j) = z y * G y i j := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro x hx hxi
          rw [if_neg (Ne.symm hxi)]
          simp
        · intro hi
          exact absurd (Finset.mem_univ i) hi
      rw [hdiag] at hresij
      linear_combination hresij
    rw [matrixSemicircleCovariance_smul]
    simp only [H, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [hcore]
    ext i j
    simp only [Matrix.smul_apply, Matrix.neg_apply, Matrix.add_apply,
      Matrix.one_apply, smul_eq_mul]
    ring
  have hy0 : Tendsto (fun y : ℝ ↦ (y : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have h : ContinuousAt (fun y : ℝ ↦ (y : ℂ)) 0 := by fun_prop
    change Tendsto _ (𝓝 0 ⊓ 𝓟 (Set.Ioi 0)) (𝓝 0)
    exact h.tendsto.mono_left inf_le_left
  have hz : Tendsto z (𝓝[>] 0) (𝓝 (a : ℂ)) := by
    have h : ContinuousAt z 0 := by
      dsimp only [z]
      fun_prop
    change Tendsto _ (𝓝 0 ⊓ 𝓟 (Set.Ioi 0)) (𝓝 (a : ℂ))
    simpa only [z, Complex.ofReal_zero, zero_mul, add_zero] using
      h.tendsto.mono_left inf_le_left
  have hlimit : matrixSemicircleCovariance A (Complex.I • M) * (Complex.I • M) = 0 := by
    ext i j
    have hright : Tendsto
        (fun y : ℝ ↦ (-(((y : ℂ) ^ 2) • (1 : Matrix I I ℂ) +
          ((y : ℂ) * z y) • H y)) i j)
        (𝓝[>] 0) (𝓝 0) := by
      have hδ : Tendsto
          (fun _y : ℝ ↦ (if i = j then 1 else 0 : ℂ))
          (𝓝[>] 0) (𝓝 (if i = j then 1 else 0 : ℂ)) := tendsto_const_nhds
      simpa only [Matrix.neg_apply, Matrix.add_apply, Matrix.smul_apply,
        Matrix.one_apply, smul_eq_mul, Matrix.zero_apply, pow_two, zero_mul,
        add_zero, neg_zero] using
        (((hy0.pow 2).mul hδ).add
          ((hy0.mul hz).mul (hH i j))).neg
    have hzero : Tendsto
        (fun y ↦ (matrixSemicircleCovariance A (H y) * H y) i j)
        (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      hright.congr' (hscaled.mono fun y h ↦ congr_fun (congr_fun h i) j |>.symm)
    exact tendsto_nhds_unique (hleft i j) hzero
  rw [matrixSemicircleCovariance_smul] at hlimit
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.I_mul_I,
    neg_one_smul] at hlimit
  exact neg_eq_zero.mp hlimit

end

end GaloisForLFunctions.HTGeometry
