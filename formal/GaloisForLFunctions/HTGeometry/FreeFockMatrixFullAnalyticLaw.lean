import GaloisForLFunctions.HTGeometry.FreeFockMatrixValuedSpectralLaw
import GaloisForLFunctions.HTGeometry.MatrixSemicircleAnalyticLaw
import GaloisForLFunctions.HTGeometry.CompactMomentReflectionSymmetry
import GaloisForLFunctions.HTGeometry.MatrixQuadraticFormDetermination

/-!
# Full vector analytic law of a finite matrix semicircle

Every internal-vector moment series is a finite quadratic combination of the algebraic matrix
Dyson branch.  Consequently every vector spectral measure has an algebraic Stieltjes transform.
If the matrix atom mass vanishes, all vector measures are atomless and hence absolutely continuous.
-/

open scoped BigOperators Matrix LaurentSeries RatFunc ComplexOrder
open Filter Topology Matrix MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]

/-- Quadratic evaluation of the formal matrix Dyson branch in an arbitrary internal vector. -/
def matrixDysonFormalVectorSeries
    (A : K → Matrix I I ℂ) (x : I → ℂ) : PowerSeries ℂ :=
  ∑ i : I, ∑ j : I,
    PowerSeries.C (star (x i) * x j) * matrixDysonFormalSeries A i j

omit [DecidableEq K] in
theorem matrixDysonFormalVectorSeriesLaurent_isIntegral_ratFunc
    (A : K → Matrix I I ℂ) (x : I → ℂ) :
    IsIntegral (RatFunc ℂ)
      ((matrixDysonFormalVectorSeries A x : PowerSeries ℂ) : LaurentSeries ℂ) := by
  rw [matrixDysonFormalVectorSeries, map_sum]
  apply IsIntegral.sum
  intro i _hi
  rw [map_sum]
  apply IsIntegral.sum
  intro j _hj
  rw [map_mul]
  let c : ℂ := star (x i) * x j
  change IsIntegral (RatFunc ℂ)
    (((PowerSeries.C c : PowerSeries ℂ) : LaurentSeries ℂ) *
      ((matrixDysonFormalSeries A i j : PowerSeries ℂ) : LaurentSeries ℂ))
  have hc : IsIntegral (RatFunc ℂ)
      (algebraMap (RatFunc ℂ) (LaurentSeries ℂ)
        (algebraMap ℂ (RatFunc ℂ) c)) := isIntegral_algebraMap
  have hC : algebraMap (RatFunc ℂ) (LaurentSeries ℂ)
        (algebraMap ℂ (RatFunc ℂ) c) =
      ((PowerSeries.C c : PowerSeries ℂ) : LaurentSeries ℂ) := by
    simpa using (RatFunc.coe_coe (Polynomial.C c)).symm
  have hc' : IsIntegral (RatFunc ℂ)
      (((PowerSeries.C c : PowerSeries ℂ) : LaurentSeries ℂ)) := by
    rw [← hC]
    exact hc
  exact hc'.mul
    (matrixDysonFormalSeriesLaurent_isIntegral_ratFunc A i j)

omit [DecidableEq K] in
theorem matrixDysonFormalVectorSeries_exists_bivariateRelation
    (A : K → Matrix I I ℂ) (x : I → ℂ) :
    ∃ P : Polynomial (Polynomial ℂ), P.leadingCoeff ≠ 0 ∧
      P.eval₂ Polynomial.coeToPowerSeries.ringHom
        (matrixDysonFormalVectorSeries A x) = 0 :=
  powerSeries_bivariateRelation_of_ratFuncIntegral _
    (matrixDysonFormalVectorSeriesLaurent_isIntegral_ratFunc A x)

theorem freeFockVectorMoment_odd
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (x : I → ℂ) (n : ℕ) :
    freeFockVectorMoment A x (2 * n + 1) = 0 := by
  rw [freeFockVectorMoment]
  simp only [freeFockVacuumSuperposition, freeFockPowerSuperposition,
    freeFockInner_finset_sum_left, freeFockInner_finset_sum_right,
    freeFockInner_smul_left, freeFockInner_smul_right,
    freeFockInner_vacuum_left]
  simp_rw [freeFockPower_vacuumCoefficient_odd A hA]
  simp

/-- Every vector spectral law of a centered matrix semicircle is invariant under reflection. -/
theorem freeFockVectorSpectralMeasure_map_neg
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (x : I → ℂ) :
    Measure.map (fun t : ℝ => -t)
        (freeFockVectorSpectralMeasure A hA hker x) =
      freeFockVectorSpectralMeasure A hA hker x := by
  apply HTGeometry.map_neg_eq_self_of_compact_moments
    (freeFockMatrixSpectralRadius_pos A)
    (freeFockVectorSpectralMeasure_carried A hA hker x)
    (fun k => (freeFockVectorSpectralMeasure_hasMoments A hA hker x k).1)
  intro k
  have hneg : (fun t : ℝ => (-t) ^ k) =
      fun t : ℝ => (-1 : ℝ) ^ k * t ^ k := by
    funext t
    rw [show -t = (-1 : ℝ) * t by ring, mul_pow]
  rw [hneg, integral_const_mul,
    (freeFockVectorSpectralMeasure_hasMoments A hA hker x k).2]
  obtain ⟨n, hn | hn⟩ := Nat.even_or_odd' k
  · subst k
    simp [pow_mul]
  · subst k
    rw [freeFockVectorMoment_odd A hA x n]
    simp

/-- The Stieltjes transform of every vector law is purely imaginary on the punctured imaginary
axis. -/
theorem freeFockVectorStieltjes_re_imaginaryAxis_eq_zero
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (x : I → ℂ) (y : ℝ) (hy : y ≠ 0) :
    (freeFockVectorStieltjes A hA hker x ((y : ℂ) * Complex.I)).re = 0 := by
  rw [freeFockVectorStieltjes]
  rw [HTGeometry.stieltjesTransform_re_eq_conjPoisson]
  · have hden : ∀ t : ℝ, t ^ 2 + y ^ 2 ≠ 0 := by
      intro t ht
      have hy2 : 0 < y ^ 2 := sq_pos_of_ne_zero hy
      nlinarith [sq_nonneg t]
    have hmeas : AEStronglyMeasurable (fun t : ℝ => t / (t ^ 2 + y ^ 2))
        (freeFockVectorSpectralMeasure A hA hker x) :=
      (continuous_id.div ((continuous_id.pow 2).add (continuous_const.pow 2)) hden)
        |>.aestronglyMeasurable
    simpa using HTGeometry.integral_eq_zero_of_map_neg_eq_self
      (freeFockVectorSpectralMeasure_map_neg A hA hker x)
      (f := fun t : ℝ => t / (t ^ 2 + y ^ 2)) hmeas (fun t => by ring)
  · apply HTGeometry.integrable_cauchy_kernel
    simpa using hy

/-- The matrix Stieltjes transform is skew-Hermitian on the positive imaginary axis. -/
theorem freeFockMatrixStieltjes_conjTranspose_imaginaryAxis
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (y : ℝ) (hy : 0 < y) :
    (freeFockMatrixStieltjes A hA hker ((y : ℂ) * Complex.I))ᴴ =
      -freeFockMatrixStieltjes A hA hker ((y : ℂ) * Complex.I) := by
  apply conjTranspose_eq_neg_of_quadraticForm_re_eq_zero
  intro x
  rw [star_dotProduct_freeFockMatrixStieltjes_mulVec A hA hker]
  · exact freeFockVectorStieltjes_re_imaginaryAxis_eq_zero A hA hker x y hy.ne'
  · simpa using hy

/-- Positive imaginary-axis Dyson profile `X_y = -iy G(iy)`. -/
def freeFockMatrixImaginaryAxisProfile
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (y : ℝ) : Matrix I I ℂ :=
  (-Complex.I * (y : ℂ)) •
    freeFockMatrixStieltjes A hA hker ((y : ℂ) * Complex.I)

/-- The imaginary-axis profile is the positive scalar multiple of the Herglotz imaginary part. -/
theorem freeFockMatrixImaginaryAxisProfile_eq_smul_hermitianImaginaryPart
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (y : ℝ) (hy : 0 < y) :
    freeFockMatrixImaginaryAxisProfile A hA hker y =
      y • matrixHermitianImaginaryPart
        (freeFockMatrixStieltjes A hA hker ((y : ℂ) * Complex.I)) := by
  rw [freeFockMatrixImaginaryAxisProfile, matrixHermitianImaginaryPart,
    freeFockMatrixStieltjes_conjTranspose_imaginaryAxis A hA hker y hy]
  ext i j
  apply Complex.ext <;>
    simp [Matrix.smul_apply, Matrix.sub_apply, Matrix.neg_apply,
      Complex.mul_re, Complex.mul_im] <;> ring

/-- Every positive-height imaginary-axis profile is positive definite. -/
theorem freeFockMatrixImaginaryAxisProfile_posDef
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (y : ℝ) (hy : 0 < y) :
    (freeFockMatrixImaginaryAxisProfile A hA hker y).PosDef := by
  rw [freeFockMatrixImaginaryAxisProfile_eq_smul_hermitianImaginaryPart
    A hA hker y hy]
  exact Matrix.PosDef.smul (α := ℝ)
    (freeFockMatrixStieltjes_hermitianImaginaryPart_posDef A hA hker
      ((y : ℂ) * Complex.I) (by simpa using hy)) hy

/-- Positive imaginary-axis Dyson equation in the nonsingular form
`(η(X_y) + y²I)X_y = y²I`. -/
theorem freeFockMatrixImaginaryAxisProfile_dyson
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (y : ℝ) (hy : 0 < y) :
    (matrixSemicircleCovariance A
        (freeFockMatrixImaginaryAxisProfile A hA hker y) +
      (y ^ 2 : ℂ) • (1 : Matrix I I ℂ)) *
        freeFockMatrixImaginaryAxisProfile A hA hker y =
      (y ^ 2 : ℂ) • (1 : Matrix I I ℂ) := by
  let z : ℂ := (y : ℂ) * Complex.I
  let G : Matrix I I ℂ := freeFockMatrixStieltjes A hA hker z
  let c : ℂ := -Complex.I * (y : ℂ)
  have hres := freeFockMatrixDysonResidual_upperHalfPlane A hA hker z (by
    simpa [z] using hy)
  have hDG : (z • (1 : Matrix I I ℂ) + matrixSemicircleCovariance A G) * G = -1 := by
    rw [freeFockMatrixDysonResidual] at hres
    change 1 + (z • (1 : Matrix I I ℂ) + matrixSemicircleCovariance A G) * G = 0 at hres
    exact eq_neg_of_add_eq_zero_right hres
  have hX : freeFockMatrixImaginaryAxisProfile A hA hker y = c • G := by
    rfl
  have hfactor :
      matrixSemicircleCovariance A
          (freeFockMatrixImaginaryAxisProfile A hA hker y) +
        (y ^ 2 : ℂ) • (1 : Matrix I I ℂ) =
      c • (z • (1 : Matrix I I ℂ) + matrixSemicircleCovariance A G) := by
    rw [hX, matrixSemicircleCovariance_smul]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    dsimp only [c, z]
    have hI : Complex.I ^ 2 = (-1 : ℂ) := by norm_num
    ring_nf
    rw [hI]
    ring
  rw [hfactor, hX]
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hDG]
  ext i j
  simp only [Matrix.smul_apply, Matrix.neg_apply, Matrix.one_apply, smul_eq_mul]
  dsimp only [c]
  have hI : Complex.I ^ 2 = (-1 : ℂ) := by norm_num
  split_ifs
  · ring_nf
    rw [hI]
    ring
  · ring

theorem coeff_matrixDysonFormalVectorSeries
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (x : I → ℂ) (n : ℕ) :
    PowerSeries.coeff n (matrixDysonFormalVectorSeries A x) =
      (freeFockVectorMoment A x (2 * n) : ℂ) := by
  have hinner :
      freeFockInner (freeFockVacuumSuperposition x)
          (freeFockPowerSuperposition A x (2 * n)) =
        (freeFockVectorMoment A x (2 * n) : ℂ) := by
    have hp := freeFockInner_powerSuperposition A hA x n n
    rw [show n + n = 2 * n by omega] at hp
    calc
      freeFockInner (freeFockVacuumSuperposition x)
          (freeFockPowerSuperposition A x (2 * n)) =
          freeFockInner (freeFockPowerSuperposition A x n)
            (freeFockPowerSuperposition A x n) := hp.symm
      _ = ((freeFockInner (freeFockPowerSuperposition A x n)
            (freeFockPowerSuperposition A x n)).re : ℂ) := by
        simpa only [freeFockInner] using
          freeFockInner_self_eq_ofReal_re (freeFockPowerSuperposition A x n)
      _ = (freeFockVectorMoment A x (2 * n) : ℂ) := by
        rw [freeFockVectorMoment, hp]
  rw [matrixDysonFormalVectorSeries, map_sum]
  simp only [map_sum, PowerSeries.coeff_C_mul, coeff_matrixDysonFormalSeries]
  rw [← hinner]
  simp only [freeFockVacuumSuperposition, freeFockPowerSuperposition,
    freeFockInner_finset_sum_left, freeFockInner_finset_sum_right,
    freeFockInner_smul_left, freeFockInner_smul_right,
    freeFockInner_vacuum_left]
  simp_rw [Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  rw [← freeFockPower_vacuumCoefficient_even A hA n i j]
  ring

theorem matrixDysonFormalVectorSeries_coeff_bound
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (x : I → ℂ) (n : ℕ) :
    ‖PowerSeries.coeff n (matrixDysonFormalVectorSeries A x)‖ ≤
      (∑ i : I, Complex.normSq (x i)) *
        (freeFockMatrixSpectralRadius A ^ 2) ^ n := by
  rw [coeff_matrixDysonFormalVectorSeries A hA]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  have hnonneg : 0 ≤ freeFockVectorMoment A x (2 * n) := by
    rw [freeFockVectorMoment_even_eq_inner A hA]
    exact re_freeFockInner_self_nonneg _
  rw [abs_of_nonneg hnonneg]
  simpa [pow_mul] using freeFockVectorMoment_even_le_matrixRadius A hA x n

theorem matrixDysonFormalVectorSeries_absoluteSummableAt
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (x : I → ℂ) (u : ℂ)
    (hu : freeFockMatrixSpectralRadius A ^ 2 * ‖u‖ < 1) :
    (matrixDysonFormalVectorSeries A x).AbsoluteSummableAt u := by
  let q : ℝ := freeFockMatrixSpectralRadius A ^ 2 * ‖u‖
  let c : ℝ := ∑ i : I, Complex.normSq (x i)
  have hq0 : 0 ≤ q := by positivity
  have hc0 : 0 ≤ c := Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have hqnorm : ‖q‖ < 1 := by
    simpa [q, Real.norm_eq_abs, abs_of_nonneg hq0] using hu
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    ((summable_geometric_of_norm_lt_one hqnorm).mul_left c)
  calc
    ‖PowerSeries.coeff n (matrixDysonFormalVectorSeries A x) * u ^ n‖ ≤
        (c * (freeFockMatrixSpectralRadius A ^ 2) ^ n) * ‖u ^ n‖ := by
      rw [norm_mul]
      gcongr
      exact matrixDysonFormalVectorSeries_coeff_bound A hA x n
    _ = c * q ^ n := by simp [q, norm_pow, mul_pow]; ring

set_option maxHeartbeats 3000000 in
theorem compactMomentGeneratingFunction_freeFockVector_eq_formalAbsoluteEval
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (x : I → ℂ) (u : ℂ)
    (hu : ‖u‖ * freeFockMatrixSpectralRadius A < 1) :
    compactMomentGeneratingFunction
        (freeFockVectorSpectralMeasure A hA hker x) u =
      (matrixDysonFormalVectorSeries A x).absoluteEval (u ^ 2) := by
  let R := freeFockMatrixSpectralRadius A
  have hR : 0 < R := freeFockMatrixSpectralRadius_pos A
  have hq0 : 0 ≤ ‖u‖ * R := mul_nonneg (norm_nonneg _) hR.le
  have hsq : R ^ 2 * ‖u ^ 2‖ < 1 := by
    rw [norm_pow]
    calc
      R ^ 2 * ‖u‖ ^ 2 = (‖u‖ * R) ^ 2 := by ring
      _ < 1 ^ 2 := (sq_lt_sq₀ hq0 zero_le_one).mpr hu
      _ = 1 := one_pow 2
  have habs := matrixDysonFormalVectorSeries_absoluteSummableAt
    A hA x (u ^ 2) hsq
  have heven : Summable (fun n : ℕ =>
      (freeFockVectorMoment A x (2 * n) : ℂ) * u ^ (2 * n)) := by
    convert habs.summable using 1
    funext n
    rw [coeff_matrixDysonFormalVectorSeries A hA, pow_mul]
  have hodd : Summable (fun n : ℕ =>
      (freeFockVectorMoment A x (2 * n + 1) : ℂ) * u ^ (2 * n + 1)) := by
    simp [freeFockVectorMoment_odd A hA]
  rw [compactMomentGeneratingFunction_freeFockVector_eq_tsum A hA hker x u hu]
  rw [← tsum_even_add_odd heven hodd]
  simp [freeFockVectorMoment_odd A hA]
  rw [PowerSeries.absoluteEval]
  apply tsum_congr
  intro n
  rw [coeff_matrixDysonFormalVectorSeries A hA, pow_mul]

theorem freeFockVector_exterior_stieltjes_relation
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (x : I → ℂ) :
    ∃ P : Polynomial (Polynomial ℂ), P.leadingCoeff ≠ 0 ∧
      ∀ z : ℂ, freeFockMatrixSpectralRadius A < ‖z‖ →
        reciprocalStieltjesRelation P
          (freeFockVectorSpectralMeasure A hA hker x) z = 0 := by
  obtain ⟨P, hPlead, hPformal⟩ :=
    matrixDysonFormalVectorSeries_exists_bivariateRelation A x
  refine ⟨P, hPlead, fun z hz => ?_⟩
  have hz0 : z ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hz
    linarith [freeFockMatrixSpectralRadius_pos A]
  let u : ℂ := z⁻¹
  have hu0 : u ≠ 0 := inv_ne_zero hz0
  have hu : ‖u‖ * freeFockMatrixSpectralRadius A < 1 := by
    change ‖z⁻¹‖ * freeFockMatrixSpectralRadius A < 1
    rw [norm_inv]
    simpa [div_eq_mul_inv, mul_comm] using
      (div_lt_one (norm_pos_iff.mpr hz0)).mpr hz
  have hM := compactMomentGeneratingFunction_freeFockVector_eq_formalAbsoluteEval
    A hA hker x u hu
  have hrel := PowerSeries.polynomial_relation_absoluteEval P
    (matrixDysonFormalVectorSeries A x) (u ^ 2)
    (matrixDysonFormalVectorSeries_absoluteSummableAt A hA x (u ^ 2) (by
      have hR := freeFockMatrixSpectralRadius_pos A
      have hq0 : 0 ≤ ‖u‖ * freeFockMatrixSpectralRadius A :=
        mul_nonneg (norm_nonneg _) hR.le
      rw [norm_pow]
      calc
        freeFockMatrixSpectralRadius A ^ 2 * ‖u‖ ^ 2 =
            (‖u‖ * freeFockMatrixSpectralRadius A) ^ 2 := by ring
        _ < 1 ^ 2 := (sq_lt_sq₀ hq0 zero_le_one).mpr hu
        _ = 1 := one_pow 2)) hPformal
  have hS := freeFockVectorStieltjes_eq_neg_mul_mgf A hA hker x u hu0
  have hzinv : u⁻¹ = z := by simp [u]
  rw [hzinv] at hS
  have hMstieltjes :
      compactMomentGeneratingFunction
          (freeFockVectorSpectralMeasure A hA hker x) u =
        -z * freeFockVectorStieltjes A hA hker x z := by
    have hzu : z * u = 1 := by simp [u, hz0]
    calc
      compactMomentGeneratingFunction
          (freeFockVectorSpectralMeasure A hA hker x) u =
          (z * u) * compactMomentGeneratingFunction
            (freeFockVectorSpectralMeasure A hA hker x) u := by rw [hzu, one_mul]
      _ = -z * (-u * compactMomentGeneratingFunction
            (freeFockVectorSpectralMeasure A hA hker x) u) := by ring
      _ = -z * freeFockVectorStieltjes A hA hker x z := by rw [← hS]
  change P.eval₂ (Polynomial.evalRingHom (z⁻¹ ^ 2))
      (-z * freeFockVectorStieltjes A hA hker x z) = 0
  have hu2 : u ^ 2 = z⁻¹ ^ 2 := by simp [u]
  rw [← hu2, ← hMstieltjes, hM]
  exact hrel

theorem freeFockVector_upperHalfPlane_stieltjes_relation
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (x : I → ℂ) :
    ∃ P : Polynomial (Polynomial ℂ), P.leadingCoeff ≠ 0 ∧
      ∀ z : ℂ, 0 < z.im →
        reciprocalStieltjesRelation P
          (freeFockVectorSpectralMeasure A hA hker x) z = 0 := by
  obtain ⟨P, hPlead, hPext⟩ :=
    freeFockVector_exterior_stieltjes_relation A hA hker x
  refine ⟨P, hPlead, ?_⟩
  let U : Set ℂ := {z | 0 < z.im}
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
      (fun z => reciprocalStieltjesRelation P
        (freeFockVectorSpectralMeasure A hA hker x) z = 0) (nhds z₀) := by
    have hopen : IsOpen {z : ℂ | freeFockMatrixSpectralRadius A < ‖z‖} :=
      isOpen_lt continuous_const continuous_norm
    filter_upwards [hopen.mem_nhds hz₀ext] with z hz
    exact hPext z hz
  have hrelAnalytic : AnalyticOnNhd ℂ
      (reciprocalStieltjesRelation P
        (freeFockVectorSpectralMeasure A hA hker x)) U :=
    (reciprocalStieltjesRelation_differentiableOn P
      (freeFockVectorSpectralMeasure A hA hker x)).analyticOnNhd
      (isOpen_lt continuous_const Complex.continuous_im)
  have hzeroAnalytic : AnalyticOnNhd ℂ (fun _z : ℂ => (0 : ℂ)) U :=
    analyticOnNhd_const
  have hEq := hrelAnalytic.eqOn_of_preconnected_of_eventuallyEq hzeroAnalytic
    (convex_halfSpace_im_gt 0).isPreconnected hz₀U hseed
  intro z hz
  exact hEq hz

/-- An atomless arbitrary-vector free-Fock spectral law is purely absolutely continuous. -/
theorem freeFockVectorSpectralMeasure_absolutelyContinuous
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (x : I → ℂ)
    (hatom : ∀ a : ℝ,
      freeFockVectorSpectralMeasure A hA hker x {a} = 0) :
    freeFockVectorSpectralMeasure A hA hker x ≪ volume := by
  letI : NullSingletonClass (freeFockVectorSpectralMeasure A hA hker x) := ⟨hatom⟩
  obtain ⟨P, hPlead, hP⟩ :=
    freeFockVector_upperHalfPlane_stieltjes_relation A hA hker x
  exact atomless_reciprocal_algebraic_stieltjes_absolutelyContinuous
    (freeFockVectorSpectralMeasure A hA hker x) P hPlead hP

/-- Vanishing of the polarized atom matrix annihilates every vector-state atom. -/
theorem freeFockVectorSpectralMeasure_singleton_eq_zero_of_matrixAtomMass_eq_zero
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) (a : ℝ)
    (hzero : freeFockMatrixAtomMass A hA hker a = 0) (x : I → ℂ) :
    freeFockVectorSpectralMeasure A hA hker x {a} = 0 := by
  have hq := star_dotProduct_freeFockMatrixAtomMass_mulVec A hA hker a x
  rw [hzero, Matrix.zero_mulVec, dotProduct_zero] at hq
  have hr : (freeFockVectorSpectralMeasure A hA hker x {a}).toReal = 0 := by
    simpa [freeFockVectorAtomMass] using hq.symm
  exact (ENNReal.toReal_eq_zero_iff _).mp hr |>.resolve_right
    (measure_ne_top (freeFockVectorSpectralMeasure A hA hker x) {a})

/-- Zero matrix atom mass at every energy gives absolute continuity in every vector state. -/
theorem freeFockVectorSpectralMeasure_absolutelyContinuous_of_matrixAtomMass_eq_zero
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A)
    (hatom : ∀ a : ℝ, freeFockMatrixAtomMass A hA hker a = 0)
    (x : I → ℂ) :
    freeFockVectorSpectralMeasure A hA hker x ≪ volume :=
  freeFockVectorSpectralMeasure_absolutelyContinuous A hA hker x fun a =>
    freeFockVectorSpectralMeasure_singleton_eq_zero_of_matrixAtomMass_eq_zero
      A hA hker a (hatom a) x

end

end GaloisForLFunctions.HTGeometry
