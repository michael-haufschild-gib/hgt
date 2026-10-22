import GaloisForLFunctions.HTGeometry.PowerSeriesAbsoluteEvaluation
import GaloisForLFunctions.HTGeometry.AlgebraicStieltjesAbsoluteContinuity

/-!
# Analytic law of the matrix semicircle trace: algebraic Stieltjes transform

For a finite family of complex matrices `A k` (indices `I × I`), the formal branch `H(u)` of the
rescaled matrix Dyson equation `H = 1 + u · η(H) H`, `η(X) = Σ_k A k X (A k)ᴴ`, has normalized trace
series `m(u) = |I|⁻¹ Σ_i H_ii(u)`. This series is integral over `ℂ(X)`, so `P(u, m(u)) = 0` for a
bivariate polynomial `P` with nonzero leading coefficient. For Hermitian `A k` the coefficients of
`m` are the even free-Fock trace moments (the normalized trace of vacuum moments of the free Fock
operator built from the `A k`), the odd moments vanish, and the `n`-th coefficient is bounded by
`R^{2n}` with `R = freeFockSpectralRadius A`. Hence, for a probability measure `μ` on `[-R, R]`
with these moments, the Stieltjes transform `S(z) = ∫ (x - z)⁻¹ dμ` satisfies
`P(z⁻², -z S(z)) = 0` for `|z| > R` and, by analytic continuation, on the whole upper half-plane.
Separately, a finite measure whose Stieltjes transform satisfies such a relation on the upper
half-plane is absolutely continuous on the nonexceptional set where `x ≠ 0` and the leading
coefficient of `P` does not vanish at `x⁻²`; if `μ` has no atoms, `μ` is absolutely continuous.

## Main results

- `matrixDysonFormalTraceSeries_exists_bivariateRelation`: a nonzero-leading-coefficient bivariate
  polynomial relation for the trace series.
- `coeff_matrixDysonFormalTraceSeries`: for Hermitian `A k`, the `n`-th coefficient is the
  free-Fock trace moment of order `2n`.
- `compactMomentGeneratingFunction_freeFockTrace_eq_absoluteEval`: `∫ (1 - u x)⁻¹ dμ = m(u²)` for
  `|u| R < 1`.
- `matrixDysonFormalTraceSeries_upperHalfPlane_stieltjes_relation`: `P(z⁻², -z S(z)) = 0` for all
  `z` with `Im z > 0`.
- `reciprocal_algebraic_stieltjes_restrict_absolutelyContinuous`: `μ` restricted to the
  nonexceptional set is absolutely continuous with respect to Lebesgue measure.
- `atomless_reciprocal_algebraic_stieltjes_absolutelyContinuous`: an atomless finite measure with an
  algebraic reciprocal Stieltjes relation is absolutely continuous.

## Hypotheses

The bivariate relation for the formal series is unconditional. Coefficient and moment statements
assume `A k` Hermitian. The Stieltjes relations are conditional on a probability measure `μ` whose
Hamburger moments are the free-Fock trace moments (`HasHamburgerMoments`) and which is carried by
`[-R, R]`; existence of such a `μ` is not proved here. The absolute-continuity theorems take the
upper-half-plane relation `∀ z, 0 < Im z → reciprocalStieltjesRelation P μ z = 0` as a hypothesis,
and the atomless version also assumes `μ` has no atoms and `P` has nonzero leading coefficient.
-/

open scoped BigOperators Matrix LaurentSeries RatFunc
open Matrix MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]

/-- Normalized trace `|I|⁻¹ Σ_i H_ii(u)` of the formal matrix Dyson branch. -/
def matrixDysonFormalTraceSeries [Nonempty I]
    (A : K → Matrix I I ℂ) : PowerSeries ℂ :=
  PowerSeries.C ((Fintype.card I : ℂ)⁻¹) *
    ∑ i : I, matrixDysonFormalSeries A i i

omit [DecidableEq K] in
/-- The trace series, viewed as a Laurent series, is integral over `ℂ(X)`. -/
theorem matrixDysonFormalTraceSeriesLaurent_isIntegral_ratFunc [Nonempty I]
    (A : K → Matrix I I ℂ) :
    IsIntegral (RatFunc ℂ)
      ((matrixDysonFormalTraceSeries A : PowerSeries ℂ) : LaurentSeries ℂ) := by
  rw [matrixDysonFormalTraceSeries, map_mul, map_sum]
  apply IsIntegral.mul
  · have h : IsIntegral (RatFunc ℂ)
        (algebraMap (RatFunc ℂ) (LaurentSeries ℂ)
          (algebraMap ℂ (RatFunc ℂ) ((Fintype.card I : ℂ)⁻¹))) := isIntegral_algebraMap
    simpa using h
  · induction (Finset.univ : Finset I) using Finset.induction_on with
    | empty => exact isIntegral_zero
    | @insert i s hi ih =>
        rw [Finset.sum_insert hi]
        exact (matrixDysonFormalSeriesLaurent_isIntegral_ratFunc A i i).add ih

omit [DecidableEq K] in
/-- There is `P ∈ ℂ[X][Y]` with nonzero leading coefficient such that `P(u, m(u)) = 0` as formal
power series. -/
theorem matrixDysonFormalTraceSeries_exists_bivariateRelation [Nonempty I]
    (A : K → Matrix I I ℂ) :
    ∃ P : Polynomial (Polynomial ℂ), P.leadingCoeff ≠ 0 ∧
      P.eval₂ Polynomial.coeToPowerSeries.ringHom (matrixDysonFormalTraceSeries A) = 0 :=
  powerSeries_bivariateRelation_of_ratFuncIntegral _
    (matrixDysonFormalTraceSeriesLaurent_isIntegral_ratFunc A)

theorem freeFockInner_self_eq_ofReal_re
    {L : Type*} (x : L →₀ ℂ) :
    x.sum (fun a c => star c * x a) = ((x.sum fun a c => star c * x a).re : ℂ) := by
  rw [Finsupp.sum]
  simp only [Complex.star_def]
  simp_rw [← Complex.normSq_eq_conj_mul_self]
  simp

/-- For Hermitian `A k`, the `n`-th coefficient of the trace series is the free-Fock trace moment of
order `2n`. -/
theorem coeff_matrixDysonFormalTraceSeries [Nonempty I]
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k) (n : ℕ) :
    PowerSeries.coeff n (matrixDysonFormalTraceSeries A) =
      (freeFockTraceMoment A (2 * n) : ℂ) := by
  rw [matrixDysonFormalTraceSeries, PowerSeries.coeff_C_mul, map_sum,
    freeFockTraceMoment]
  simp only [coeff_matrixDysonFormalSeries]
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [← freeFockPower_vacuumCoefficient_even A hA n i i]
  rw [show 2 * n = n + n by omega,
    ← freeFockInner_power_power A hA n n i i]
  rw [freeFockInner]
  exact freeFockInner_self_eq_ofReal_re (freeFockPower A i n)

/-- For Hermitian `A k`, even free-Fock trace moments are nonnegative. -/
theorem freeFockTraceMoment_even_nonneg [Nonempty I]
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k) (n : ℕ) :
    0 ≤ freeFockTraceMoment A (2 * n) := by
  rw [freeFockTraceMoment]
  apply mul_nonneg
  · exact inv_nonneg.mpr (Nat.cast_nonneg _)
  · apply Finset.sum_nonneg
    intro i hi
    rw [show 2 * n = n + n by omega,
      ← freeFockInner_power_power A hA n n i i]
    exact re_freeFockInner_self_nonneg _

/-- For Hermitian `A k`, the `n`-th coefficient of the trace series has modulus at most `(R²)^n`,
`R = freeFockSpectralRadius A`. -/
theorem matrixDysonFormalTraceSeries_coeff_bound [Nonempty I]
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k) (n : ℕ) :
    ‖PowerSeries.coeff n (matrixDysonFormalTraceSeries A)‖ ≤
      (freeFockSpectralRadius A ^ (2 : ℕ)) ^ n := by
  rw [coeff_matrixDysonFormalTraceSeries A hA]
  simp only [Complex.norm_real]
  rw [Real.norm_eq_abs]
  rw [abs_of_nonneg (freeFockTraceMoment_even_nonneg A hA n)]
  simpa [freeFockSpectralRadius, pow_mul] using
    freeFockTraceMoment_even_le_radius A n

/-- For Hermitian `A k`, the trace series converges absolutely at every `v` with `R² |v| < 1`. -/
theorem matrixDysonFormalTraceSeries_absoluteSummableAt [Nonempty I]
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k) (v : ℂ)
    (hv : freeFockSpectralRadius A ^ (2 : ℕ) * ‖v‖ < 1) :
    (matrixDysonFormalTraceSeries A).AbsoluteSummableAt v := by
  let q : ℝ := freeFockSpectralRadius A ^ (2 : ℕ) * ‖v‖
  have hq0 : 0 ≤ q := by positivity
  have hqnorm : ‖q‖ < 1 := by simpa [q, Real.norm_eq_abs, abs_of_nonneg hq0] using hv
  have hgeom : Summable (fun n : ℕ ↦ q ^ n) := summable_geometric_of_norm_lt_one hqnorm
  apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (fun n ↦ ?_) hgeom
  calc
    ‖PowerSeries.coeff n (matrixDysonFormalTraceSeries A) * v ^ n‖ ≤
        (freeFockSpectralRadius A ^ (2 : ℕ)) ^ n * ‖v ^ n‖ := by
          rw [norm_mul]
          gcongr
          exact matrixDysonFormalTraceSeries_coeff_bound A hA n
    _ = q ^ n := by simp [q, norm_pow, mul_pow]

/-- For Hermitian `A k`, odd free-Fock trace moments vanish. -/
theorem freeFockTraceMoment_odd [Nonempty I]
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k) (n : ℕ) :
    freeFockTraceMoment A (2 * n + 1) = 0 := by
  rw [freeFockTraceMoment]
  simp_rw [freeFockPower_vacuumCoefficient_odd A hA n]
  simp

/-- The moment generating function `u ↦ ∫ (1 - u x)⁻¹ dμ(x)`. -/
def compactMomentGeneratingFunction (mu : Measure ℝ) (u : ℂ) : ℂ :=
  ∫ x : ℝ, (1 - u * (x : ℂ))⁻¹ ∂mu

/-- For a probability measure carried by `[-R, R]` with Hamburger moments `s`, and `|u| R < 1`,
`∫ (1 - u x)⁻¹ dμ = Σ_n s_n u^n`. -/
theorem compactMomentGeneratingFunction_eq_tsum
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (s : ℕ → ℝ) (hmu : HasHamburgerMoments s mu)
    (R : ℝ) (hR : 0 < R)
    (hcarry : mu (Set.Icc (-R) R)ᶜ = 0)
    (u : ℂ) (hu : ‖u‖ * R < 1) :
    compactMomentGeneratingFunction mu u = ∑' n : ℕ, (s n : ℂ) * u ^ n := by
  let q : ℝ := ‖u‖ * R
  have hq0 : 0 ≤ q := mul_nonneg (norm_nonneg _) hR.le
  have hqnorm : ‖q‖ < 1 := by
    change |q| < 1
    rw [abs_of_nonneg hq0]
    exact hu
  have hmem : ∀ᵐ x ∂mu, x ∈ Set.Icc (-R) R := by
    change Set.Icc (-R) R ∈ ae mu
    simpa only [compl_compl] using MeasureTheory.compl_mem_ae_iff.mpr hcarry
  let F : ℕ → ℝ → ℂ := fun n x ↦ (u * (x : ℂ)) ^ n
  have hFint : ∀ n, Integrable (F n) mu := by
    intro n
    refine ((hmu n).1.ofReal.const_mul (u ^ n)).congr
      (Filter.Eventually.of_forall fun x ↦ ?_)
    simp [F, mul_pow]
  have hFnorm : ∀ᵐ x ∂mu, ∀ n, ‖F n x‖ ≤ q ^ n := by
    filter_upwards [hmem] with x hx
    intro n
    have hxabs : |x| ≤ R := abs_le.mpr hx
    simp only [F, norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (abs_nonneg _))
      (mul_le_mul_of_nonneg_left hxabs (norm_nonneg _)) n
  have hIntNorm : ∀ n, ∫ x, ‖F n x‖ ∂mu ≤ q ^ n := by
    intro n
    calc
      ∫ x, ‖F n x‖ ∂mu ≤ ∫ _x, q ^ n ∂mu := by
        exact integral_mono_ae (hFint n).norm
          (integrable_const (μ := mu) (q ^ n)) (hFnorm.mono fun x hx ↦ hx n)
      _ = q ^ n := by simp
  have hsumNorm : Summable (fun n ↦ ∫ x, ‖F n x‖ ∂mu) :=
    Summable.of_nonneg_of_le
      (fun _ ↦ integral_nonneg fun _ ↦ norm_nonneg _)
      hIntNorm (summable_geometric_of_norm_lt_one hqnorm)
  have hFsum : ∀ᵐ x ∂mu, (∑' n, F n x) = (1 - u * (x : ℂ))⁻¹ := by
    filter_upwards [hmem] with x hx
    have hxabs : |x| ≤ R := abs_le.mpr hx
    have hux : ‖u * (x : ℂ)‖ < 1 := by
      calc
        ‖u * (x : ℂ)‖ = ‖u‖ * |x| := by simp [Real.norm_eq_abs]
        _ ≤ ‖u‖ * R := mul_le_mul_of_nonneg_left hxabs (norm_nonneg _)
        _ < 1 := hu
    exact tsum_geometric_of_norm_lt_one hux
  have hFintValue : ∀ n, (∫ x, F n x ∂mu) = (s n : ℂ) * u ^ n := by
    intro n
    calc
      (∫ x, F n x ∂mu) = ∫ x, u ^ n * ((x ^ n : ℝ) : ℂ) ∂mu := by
        apply integral_congr_ae
        filter_upwards with x
        simp only [F, mul_pow]
        push_cast
        ring
      _ = u ^ n * ∫ x, ((x ^ n : ℝ) : ℂ) ∂mu := by
        rw [MeasureTheory.integral_const_mul]
      _ = u ^ n * ((∫ x, x ^ n ∂mu : ℝ) : ℂ) := by
        congr 1
        exact _root_.integral_ofReal
      _ = (s n : ℂ) * u ^ n := by rw [(hmu n).2]; ring
  rw [compactMomentGeneratingFunction]
  calc
    (∫ x, (1 - u * (x : ℂ))⁻¹ ∂mu) = ∫ x, ∑' n, F n x ∂mu :=
      integral_congr_ae (Filter.EventuallyEq.symm hFsum)
    _ = ∑' n, ∫ x, F n x ∂mu :=
      (MeasureTheory.integral_tsum_of_summable_integral_norm hFint hsumNorm).symm
    _ = ∑' n, (s n : ℂ) * u ^ n := tsum_congr hFintValue

set_option maxHeartbeats 3000000 in
/-- For Hermitian `A k` and a probability measure on `[-R, R]` whose moments are the free-Fock trace
moments, `∫ (1 - u x)⁻¹ dμ = m(u²)` whenever `|u| R < 1`. -/
theorem compactMomentGeneratingFunction_freeFockTrace_eq_absoluteEval
    [Nonempty I] (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hmu : HasHamburgerMoments (freeFockTraceMoment A) mu)
    (hcarry : mu
      (Set.Icc (-freeFockSpectralRadius A) (freeFockSpectralRadius A))ᶜ = 0)
    (u : ℂ) (hu : ‖u‖ * freeFockSpectralRadius A < 1) :
    compactMomentGeneratingFunction mu u =
      (matrixDysonFormalTraceSeries A).absoluteEval (u ^ (2 : ℕ)) := by
  let R := freeFockSpectralRadius A
  have hR : 0 < R := freeFockSpectralRadius_pos A
  have hq0 : 0 ≤ ‖u‖ * R := mul_nonneg (norm_nonneg _) hR.le
  have hsq : R ^ (2 : ℕ) * ‖u ^ (2 : ℕ)‖ < 1 := by
    rw [norm_pow]
    calc
      R ^ (2 : ℕ) * ‖u‖ ^ (2 : ℕ) = (‖u‖ * R) ^ (2 : ℕ) := by ring
      _ < 1 ^ (2 : ℕ) := (sq_lt_sq₀ hq0 zero_le_one).mpr hu
      _ = 1 := one_pow 2
  have habs := matrixDysonFormalTraceSeries_absoluteSummableAt A hA (u ^ (2 : ℕ)) hsq
  have heven : Summable (fun n : ℕ ↦
      (freeFockTraceMoment A (2 * n) : ℂ) * u ^ (2 * n)) := by
    convert habs.summable using 1
    funext n
    rw [coeff_matrixDysonFormalTraceSeries A hA, pow_mul]
  have hodd : Summable (fun n : ℕ ↦
      (freeFockTraceMoment A (2 * n + 1) : ℂ) * u ^ (2 * n + 1)) := by
    simp [freeFockTraceMoment_odd A hA]
  rw [compactMomentGeneratingFunction_eq_tsum mu _ hmu R hR hcarry u hu]
  rw [← tsum_even_add_odd heven hodd]
  simp [freeFockTraceMoment_odd A hA]
  rw [PowerSeries.absoluteEval]
  apply tsum_congr
  intro n
  rw [coeff_matrixDysonFormalTraceSeries A hA, pow_mul]

/-- For `u ≠ 0`, `∫ (x - u⁻¹)⁻¹ dμ = -u ∫ (1 - u x)⁻¹ dμ`. -/
theorem stieltjesTransform_inv_eq_neg_mul_compactMomentGeneratingFunction
    (mu : Measure ℝ) (u : ℂ) (hu : u ≠ 0) :
    (∫ x : ℝ, ((x : ℂ) - u⁻¹)⁻¹ ∂mu) =
      -u * compactMomentGeneratingFunction mu u := by
  rw [compactMomentGeneratingFunction, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  rw [show (x : ℂ) - u⁻¹ = -u⁻¹ * (1 - u * (x : ℂ)) by
    field_simp
    ring]
  rw [_root_.mul_inv_rev, inv_neg, inv_inv]
  ring

/-- Under the Hermitian, moment and support hypotheses, there is `P` with nonzero leading
coefficient such that `P(z⁻², -z S(z)) = 0` for all `|z| > R`, where `S` is the Stieltjes
transform of `μ`. -/
theorem matrixDysonFormalTraceSeries_exterior_stieltjes_relation
    [Nonempty I] (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hmu : HasHamburgerMoments (freeFockTraceMoment A) mu)
    (hcarry : mu
      (Set.Icc (-freeFockSpectralRadius A) (freeFockSpectralRadius A))ᶜ = 0) :
    ∃ P : Polynomial (Polynomial ℂ), P.leadingCoeff ≠ 0 ∧
      ∀ z : ℂ, freeFockSpectralRadius A < ‖z‖ →
        P.eval₂ (Polynomial.evalRingHom (z⁻¹ ^ (2 : ℕ)))
          (-z * (∫ x : ℝ, ((x : ℂ) - z)⁻¹ ∂mu)) = 0 := by
  obtain ⟨P, hPlead, hPformal⟩ :=
    matrixDysonFormalTraceSeries_exists_bivariateRelation A
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
  have hM := compactMomentGeneratingFunction_freeFockTrace_eq_absoluteEval
    A hA mu hmu hcarry u hu
  have hrel := PowerSeries.polynomial_relation_absoluteEval P
    (matrixDysonFormalTraceSeries A) (u ^ (2 : ℕ))
    (matrixDysonFormalTraceSeries_absoluteSummableAt A hA (u ^ (2 : ℕ)) (by
      have hR := freeFockSpectralRadius_pos A
      have hq0 : 0 ≤ ‖u‖ * freeFockSpectralRadius A :=
        mul_nonneg (norm_nonneg _) hR.le
      rw [norm_pow]
      calc
        freeFockSpectralRadius A ^ (2 : ℕ) * ‖u‖ ^ (2 : ℕ) =
            (‖u‖ * freeFockSpectralRadius A) ^ (2 : ℕ) := by ring
        _ < 1 ^ (2 : ℕ) := (sq_lt_sq₀ hq0 zero_le_one).mpr hu
        _ = 1 := one_pow 2)) hPformal
  have hS := stieltjesTransform_inv_eq_neg_mul_compactMomentGeneratingFunction
    mu u hu0
  have hzinv : u⁻¹ = z := by simp [u]
  rw [hzinv] at hS
  have hMstieltjes : compactMomentGeneratingFunction mu u =
      -z * (∫ x : ℝ, ((x : ℂ) - z)⁻¹ ∂mu) := by
    have hzu : z * u = 1 := by simp [u, hz0]
    calc
      compactMomentGeneratingFunction mu u =
          (z * u) * compactMomentGeneratingFunction mu u := by rw [hzu, one_mul]
      _ = -z * (-u * compactMomentGeneratingFunction mu u) := by ring
      _ = -z * (∫ x : ℝ, ((x : ℂ) - z)⁻¹ ∂mu) := by rw [← hS]
  have hu2 : u ^ (2 : ℕ) = z⁻¹ ^ (2 : ℕ) := by simp [u]
  rw [← hu2, ← hMstieltjes, hM]
  exact hrel

/-- The value `P(z⁻², -z S(z))` of a bivariate polynomial on the reciprocal Stieltjes pair of `μ`,
with `S(z) = ∫ (x - z)⁻¹ dμ`. -/
def reciprocalStieltjesRelation
    (P : Polynomial (Polynomial ℂ)) (mu : Measure ℝ) (z : ℂ) : ℂ :=
  P.eval₂ (Polynomial.evalRingHom (z⁻¹ ^ (2 : ℕ)))
    (-z * (∫ x : ℝ, ((x : ℂ) - z)⁻¹ ∂mu))

/-- For a finite measure, `z ↦ P(z⁻², -z S(z))` is holomorphic on the upper half-plane. -/
theorem reciprocalStieltjesRelation_differentiableOn
    (P : Polynomial (Polynomial ℂ)) (mu : Measure ℝ) [IsFiniteMeasure mu] :
    DifferentiableOn ℂ (reciprocalStieltjesRelation P mu) {z : ℂ | 0 < z.im} := by
  intro z hz
  have hz0 : z ≠ 0 := by
    intro hzero
    simp [hzero] at hz
  have hInv : DifferentiableAt ℂ (fun w : ℂ ↦ w⁻¹ ^ (2 : ℕ)) z :=
    ((differentiableAt_id.inv hz0).pow 2)
  have hS : DifferentiableAt ℂ
      (fun w : ℂ ↦ ∫ x : ℝ, ((x : ℂ) - w)⁻¹ ∂mu) z :=
    (HTGeometry.stieltjes_hasDerivAt z hz).differentiableAt
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      rw [show reciprocalStieltjesRelation (P + Q) mu =
          reciprocalStieltjesRelation P mu + reciprocalStieltjesRelation Q mu by
        funext w
        simp only [reciprocalStieltjesRelation, Polynomial.eval₂_add,
          Pi.add_apply]]
      exact hP.add hQ
  | monomial n p =>
      have hterm : DifferentiableWithinAt ℂ
          (fun w : ℂ ↦ p.eval (w⁻¹ ^ (2 : ℕ)) *
            (-w * (∫ x : ℝ, ((x : ℂ) - w)⁻¹ ∂mu)) ^ n)
          {w : ℂ | 0 < w.im} z :=
        ((p.differentiableAt.comp z hInv).mul
          (((differentiableAt_id.neg).mul hS).pow n)).differentiableWithinAt
      rw [show reciprocalStieltjesRelation (Polynomial.monomial n p) mu =
          fun w : ℂ ↦ p.eval (w⁻¹ ^ (2 : ℕ)) *
            (-w * (∫ x : ℝ, ((x : ℂ) - w)⁻¹ ∂mu)) ^ n by
        funext w
        simp [reciprocalStieltjesRelation]]
      exact hterm

/-- Under the Hermitian, moment and support hypotheses, there is `P` with nonzero leading
coefficient such that `P(z⁻², -z S(z)) = 0` on the whole upper half-plane (identity theorem from
the exterior region `|z| > R`). -/
theorem matrixDysonFormalTraceSeries_upperHalfPlane_stieltjes_relation
    [Nonempty I] (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hmu : HasHamburgerMoments (freeFockTraceMoment A) mu)
    (hcarry : mu
      (Set.Icc (-freeFockSpectralRadius A) (freeFockSpectralRadius A))ᶜ = 0) :
    ∃ P : Polynomial (Polynomial ℂ), P.leadingCoeff ≠ 0 ∧
      ∀ z : ℂ, 0 < z.im → reciprocalStieltjesRelation P mu z = 0 := by
  obtain ⟨P, hPlead, hPext⟩ :=
    matrixDysonFormalTraceSeries_exterior_stieltjes_relation A hA mu hmu hcarry
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
      Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
      mul_one, abs_of_pos (add_pos_of_pos_of_nonneg (freeFockSpectralRadius_pos A) zero_le_one)]
    linarith
  have hseed : Filter.Eventually
      (fun z ↦ reciprocalStieltjesRelation P mu z = 0) (nhds z₀) := by
    have hopen : IsOpen {z : ℂ | freeFockSpectralRadius A < ‖z‖} :=
      isOpen_lt continuous_const continuous_norm
    filter_upwards [hopen.mem_nhds hz₀ext] with z hz
    exact hPext z hz
  have hrelAnalytic : AnalyticOnNhd ℂ (reciprocalStieltjesRelation P mu) U :=
    (reciprocalStieltjesRelation_differentiableOn P mu).analyticOnNhd
      (isOpen_lt continuous_const Complex.continuous_im)
  have hzeroAnalytic : AnalyticOnNhd ℂ (fun _z : ℂ ↦ (0 : ℂ)) U := analyticOnNhd_const
  have hEq := hrelAnalytic.eqOn_of_preconnected_of_eventuallyEq hzeroAnalytic
    (convex_halfSpace_im_gt 0).isPreconnected hz₀U hseed
  intro z hz
  exact hEq hz

/-- Real points `x ≠ 0` at which the leading coefficient of `P` does not vanish at `x⁻²`. -/
def reciprocalStieltjesNonexceptionalSet
    (P : Polynomial (Polynomial ℂ)) : Set ℝ :=
  {x | x ≠ 0 ∧ P.leadingCoeff.eval (((x : ℂ)⁻¹) ^ (2 : ℕ)) ≠ 0}

/-- Complex points `z ≠ 0` at which the leading coefficient of `P` does not vanish at `z⁻²`. -/
def reciprocalStieltjesComplexNonexceptionalSet
    (P : Polynomial (Polynomial ℂ)) : Set ℂ :=
  {z | z ≠ 0 ∧ P.leadingCoeff.eval (z⁻¹ ^ (2 : ℕ)) ≠ 0}

theorem isOpen_reciprocalStieltjesComplexNonexceptionalSet
    (P : Polynomial (Polynomial ℂ)) :
    IsOpen (reciprocalStieltjesComplexNonexceptionalSet P) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  have hz0 : z ≠ 0 := hz.1
  have hInv : ContinuousAt (fun w : ℂ ↦ w⁻¹ ^ (2 : ℕ)) z :=
    (continuousAt_id.inv₀ hz0).pow 2
  have hPoly : ContinuousAt
      (fun w : ℂ ↦ P.leadingCoeff.eval (w⁻¹ ^ (2 : ℕ))) z :=
    P.leadingCoeff.continuous.continuousAt.comp hInv
  exact Filter.inter_mem (isOpen_ne.mem_nhds hz0)
    (hPoly (isOpen_ne.mem_nhds hz.2))

theorem isOpen_reciprocalStieltjesNonexceptionalSet
    (P : Polynomial (Polynomial ℂ)) :
    IsOpen (reciprocalStieltjesNonexceptionalSet P) := by
  have heq : reciprocalStieltjesNonexceptionalSet P =
      Complex.ofReal ⁻¹'
        reciprocalStieltjesComplexNonexceptionalSet P := by
    ext x
    simp [reciprocalStieltjesNonexceptionalSet,
      reciprocalStieltjesComplexNonexceptionalSet]
  rw [heq]
  exact (isOpen_reciprocalStieltjesComplexNonexceptionalSet P).preimage
    Complex.continuous_ofReal

set_option maxHeartbeats 3000000 in
/-- If a finite measure satisfies `P(z⁻², -z S(z)) = 0` for all `Im z > 0`, then its restriction to
the nonexceptional set is absolutely continuous; the root bound for `P` keeps `S` locally bounded
near nonexceptional real points. -/
theorem reciprocal_algebraic_stieltjes_restrict_absolutelyContinuous
    (mu : Measure ℝ) [IsFiniteMeasure mu] (P : Polynomial (Polynomial ℂ))
    (hAlg : ∀ z : ℂ, 0 < z.im → reciprocalStieltjesRelation P mu z = 0) :
    mu.restrict (reciprocalStieltjesNonexceptionalSet P) ≪ volume := by
  apply absolutelyContinuous_restrict_of_locally_bounded_stieltjes mu
    (isOpen_reciprocalStieltjesNonexceptionalSet P)
  intro K hK hKU
  let KC : Set ℂ := Complex.ofReal '' K
  have hKC : IsCompact KC := hK.image Complex.continuous_ofReal
  let N : Set ℂ := reciprocalStieltjesComplexNonexceptionalSet P
  have hNopen : IsOpen N := isOpen_reciprocalStieltjesComplexNonexceptionalSet P
  have hKCN : KC ⊆ N := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hz
    simpa [N, reciprocalStieltjesComplexNonexceptionalSet,
      reciprocalStieltjesNonexceptionalSet] using hKU hx
  obtain ⟨delta, hdelta, hdeltasub⟩ := hKC.exists_cthickening_subset_open hNopen hKCN
  let L : Set ℂ := Metric.cthickening (delta / 2) KC
  have hLcompact : IsCompact L := hKC.cthickening
  have hLN : L ⊆ N :=
    (Metric.cthickening_mono (by linarith : delta / 2 ≤ delta) KC).trans hdeltasub
  have hInvSqCont : ContinuousOn (fun z : ℂ ↦ z⁻¹ ^ (2 : ℕ)) L := by
    intro z hz
    exact ((continuousAt_id.inv₀ (hLN hz).1).pow 2).continuousWithinAt
  let T : Set ℂ := (fun z : ℂ ↦ z⁻¹ ^ (2 : ℕ)) '' L
  have hTcompact : IsCompact T := hLcompact.image_of_continuousOn hInvSqCont
  have hTlead : ∀ xi ∈ T, P.leadingCoeff.eval xi ≠ 0 := by
    intro xi hxi
    obtain ⟨z, hz, rfl⟩ := hxi
    exact (hLN hz).2
  obtain ⟨C, hCpos, hC⟩ :=
    cauchyBound_bivariatePolynomialSpecialize_bounded_on_compact P hTcompact hTlead
  have hInvCont : ContinuousOn (fun z : ℂ ↦ z⁻¹) L := by
    intro z hz
    exact (continuousAt_id.inv₀ (hLN hz).1).continuousWithinAt
  obtain ⟨D₀, hD₀⟩ := hLcompact.exists_bound_of_continuousOn hInvCont
  let D : ℝ := max D₀ 0
  have hDnonneg : 0 ≤ D := le_max_right _ _
  have hD : ∀ z ∈ L, ‖z⁻¹‖ ≤ D := fun z hz ↦
    (hD₀ z hz).trans (le_max_left _ _)
  let W : Set ℝ := Metric.thickening (delta / 4) K
  have hWopen : IsOpen W := Metric.isOpen_thickening
  have hKW : K ⊆ W := Metric.self_subset_thickening (by positivity) K
  have hgeom : ∀ x ∈ W, ∀ y : ℝ, 0 ≤ y → y < delta / 4 →
      ((x : ℂ) + (y : ℂ) * Complex.I) ∈ L := by
    intro x hx y hy hydelta
    change x ∈ Metric.thickening (delta / 4) K at hx
    rw [Metric.mem_thickening_iff] at hx
    obtain ⟨a, ha, hxa⟩ := hx
    apply Metric.closedBall_subset_cthickening
      (show (a : ℂ) ∈ KC from ⟨a, ha, rfl⟩) (delta / 2)
    rw [Metric.mem_closedBall, Complex.dist_eq]
    apply le_of_lt
    calc
      ‖(x : ℂ) + (y : ℂ) * Complex.I - (a : ℂ)‖ =
          ‖((x - a : ℝ) : ℂ) + (y : ℂ) * Complex.I‖ := by
            congr 1
            all_goals
              push_cast
              ring
      _ ≤ ‖((x - a : ℝ) : ℂ)‖ + ‖(y : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = |x - a| + |y| := by
        simp only [Complex.norm_real, Complex.norm_mul, Complex.norm_I, mul_one,
          Real.norm_eq_abs]
      _ < delta / 4 + delta / 4 := by
        gcongr
        · simpa [Real.dist_eq] using hxa
        · simpa [abs_of_nonneg hy] using hydelta
      _ = delta / 2 := by ring
  have hWU : W ⊆ reciprocalStieltjesNonexceptionalSet P := by
    intro x hx
    have hxL : (x : ℂ) ∈ L := by
      simpa using hgeom x hx 0 le_rfl (by positivity)
    simpa [N, reciprocalStieltjesComplexNonexceptionalSet,
      reciprocalStieltjesNonexceptionalSet] using hLN hxL
  refine ⟨W, hWopen, hKW, hWU, D * C, delta / 4, by positivity,
    fun x hx y hy hydelta ↦ ?_⟩
  let z : ℂ := (x : ℂ) + (y : ℂ) * Complex.I
  have hzL : z ∈ L := hgeom x hx y hy.le hydelta
  have hzN := hLN hzL
  have hxiT : z⁻¹ ^ (2 : ℕ) ∈ T := ⟨z, hzL, rfl⟩
  have hlead : P.leadingCoeff.eval (z⁻¹ ^ (2 : ℕ)) ≠ 0 := hTlead _ hxiT
  have hQne : bivariatePolynomialSpecialize P (z⁻¹ ^ (2 : ℕ)) ≠ 0 := by
    intro hzero
    have h := congrArg (fun q : Polynomial ℂ ↦ q.leadingCoeff) hzero
    rw [bivariatePolynomialSpecialize_leadingCoeff P _ hlead,
      Polynomial.leadingCoeff_zero] at h
    exact hlead h
  let S : ℂ := ∫ t : ℝ, ((t : ℂ) - z)⁻¹ ∂mu
  have hzIm : z.im = y := by simp [z]
  have hroot : (bivariatePolynomialSpecialize P (z⁻¹ ^ (2 : ℕ))).IsRoot (-z * S) := by
    rw [Polynomial.IsRoot, bivariatePolynomialSpecialize, Polynomial.eval_map]
    exact hAlg z (by rw [hzIm]; exact hy)
  have hrootBoundNN := hroot.norm_lt_cauchyBound hQne
  have hrootBound : ‖-z * S‖ <
      (Polynomial.cauchyBound (bivariatePolynomialSpecialize P (z⁻¹ ^ (2 : ℕ))) : ℝ) := by
    exact_mod_cast hrootBoundNN
  have hrootC : ‖-z * S‖ ≤ C := hrootBound.le.trans (hC _ hxiT)
  have hSbound : ‖S‖ ≤ D * C := by
    calc
      ‖S‖ = ‖z⁻¹ * (z * S)‖ := by
        congr 1
        field_simp [hzN.1]
      _ ≤ ‖z⁻¹‖ * ‖z * S‖ := norm_mul_le _ _
      _ = ‖z⁻¹‖ * ‖-z * S‖ := by simp only [neg_mul, norm_neg]
      _ ≤ D * C := mul_le_mul (hD z hzL) hrootC (norm_nonneg _) hDnonneg
  exact (Complex.im_le_norm S).trans hSbound

/-- Real `x ≠ 0` with `x⁻² = r`. -/
def reciprocalRootFiber (r : ℂ) : Set ℝ :=
  {x | x ≠ 0 ∧ ((x : ℂ)⁻¹) ^ (2 : ℕ) = r}

/-- Each fiber `{x ≠ 0 | x⁻² = r}` is finite. -/
theorem reciprocalRootFiber_finite (r : ℂ) :
    (reciprocalRootFiber r).Finite := by
  let q : Polynomial ℂ := Polynomial.C r * Polynomial.X ^ (2 : ℕ) - 1
  have hqne : q ≠ 0 := by
    intro hzero
    have h := congrArg (fun p : Polynomial ℂ ↦ p.eval 0) hzero
    simp [q] at h
  have hroots : {z : ℂ | q.IsRoot z}.Finite :=
    Polynomial.finite_setOf_isRoot hqne
  have hpre : {x : ℝ | q.IsRoot (x : ℂ)}.Finite := by
    have := hroots.preimage Complex.ofReal_injective.injOn
    simpa only [Set.preimage_setOf_eq] using this
  apply hpre.subset
  intro x hx
  rw [Set.mem_setOf_eq, Polynomial.IsRoot]
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.1
  simp only [q, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
  calc
    r * (x : ℂ) ^ (2 : ℕ) - 1 = ((x : ℂ)⁻¹) ^ (2 : ℕ) * (x : ℂ) ^ (2 : ℕ) - 1 := by
      rw [hx.2]
    _ = 0 := by field_simp; ring

/-- If `P` has nonzero leading coefficient, the exceptional real set is finite. -/
theorem reciprocalStieltjesNonexceptionalSet_compl_finite
    (P : Polynomial (Polynomial ℂ)) (hlead : P.leadingCoeff ≠ 0) :
    (reciprocalStieltjesNonexceptionalSet P)ᶜ.Finite := by
  let roots : Set ℂ := {r | P.leadingCoeff.IsRoot r}
  have hroots : roots.Finite := Polynomial.finite_setOf_isRoot hlead
  have hunion : (⋃ r ∈ roots, reciprocalRootFiber r).Finite :=
    hroots.biUnion fun r _ ↦ reciprocalRootFiber_finite r
  have hfinite : ({0} ∪ ⋃ r ∈ roots, reciprocalRootFiber r : Set ℝ).Finite :=
    Set.finite_singleton 0 |>.union hunion
  apply hfinite.subset
  intro x hx
  by_cases hx0 : x = 0
  · exact Set.mem_union_left _ (by simp [hx0])
  · have hroot : P.leadingCoeff.IsRoot (((x : ℂ)⁻¹) ^ (2 : ℕ)) := by
      rw [Polynomial.IsRoot]
      simpa [reciprocalStieltjesNonexceptionalSet, hx0] using hx
    apply Set.mem_union_right
    exact Set.mem_iUnion₂.mpr
      ⟨((x : ℂ)⁻¹) ^ (2 : ℕ), hroot, ⟨hx0, rfl⟩⟩

/-- An atomless finite measure whose Stieltjes transform satisfies `P(z⁻², -z S(z)) = 0` on the
upper half-plane, with `P` of nonzero leading coefficient, is absolutely continuous with respect to
Lebesgue measure. -/
theorem atomless_reciprocal_algebraic_stieltjes_absolutelyContinuous
    (mu : Measure ℝ) [IsFiniteMeasure mu] [NullSingletonClass mu]
    (P : Polynomial (Polynomial ℂ)) (hlead : P.leadingCoeff ≠ 0)
    (hAlg : ∀ z : ℂ, 0 < z.im → reciprocalStieltjesRelation P mu z = 0) :
    mu ≪ volume := by
  have hac := reciprocal_algebraic_stieltjes_restrict_absolutelyContinuous mu P hAlg
  let U := reciprocalStieltjesNonexceptionalSet P
  have hUopen : IsOpen U := isOpen_reciprocalStieltjesNonexceptionalSet P
  have hbadFinite : Uᶜ.Finite :=
    reciprocalStieltjesNonexceptionalSet_compl_finite P hlead
  have hbadZero : mu Uᶜ = 0 := hbadFinite.measure_zero mu
  have hrestrictBad : mu.restrict Uᶜ = 0 := Measure.restrict_eq_zero.mpr hbadZero
  have hmueq : mu.restrict U = mu := by
    calc
      mu.restrict U = mu.restrict U + mu.restrict Uᶜ := by rw [hrestrictBad, add_zero]
      _ = mu := Measure.restrict_add_restrict_compl hUopen.measurableSet
  simpa [U, hmueq] using hac

end
end GaloisForLFunctions.HTGeometry
