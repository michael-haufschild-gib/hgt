import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.AlmostEveryZeroOrdinateIsNearlyWeilPositive

/-!
# Weil positivity at almost every zero ordinate

At a zero ordinate `γ = Im ρ₀` the zero `ρ₀` itself enters the Weil form `Q_γ(F₀) =
Q(F₀ cos γ·) + Q(F₀ sin γ·)` with weight `m_{ρ₀} (∫ F₀(u) cosh((Re ρ₀ - 1/2) u) du)²`, because the
modulation `e^{iγu}` cancels the phase of `ρ₀`. For a nonnegative test this is at least `(∫ F₀)²`,
and the negative part is at most `4 (A + 1)² e^A N(F₀)² Φ(γ)` with the off-line field `Φ`.

**Pointwise law** (`sq_integral_sub_offLineField_le_fullZeroForm`). For every copy `q`, aperture
`A ≥ 0` and nonnegative `F₀ ∈ C²_c([-A, A])`, at `γ = Im q`:
`Q_γ(F₀) ≥ (∫ F₀)² - 4 (A + 1)² e^A N(F₀)² Φ(γ)`.

**Selection** (`exists_shortWindow_almostEvery_zeroOrdinate_positive`). On every window
`[Γ, Γ + H]`, `Γ^{99/100} ≤ H ≤ Γ/8`, all but `C H / η` of the `≥ H log Γ / (16π)` zero copies have
`Q_{Im q}(F₀) ≥ (∫ F₀)² - 4η (A + 1)² e^A N(F₀)²` for every aperture and every nonnegative test.
So `Q_{Im q}(F₀) > 0` at those ordinates for every nonnegative test with
`4η (A + 1)² e^A N(F₀)² < (∫ F₀)²`: positivity at almost every zero ordinate, uniformly over each
class of nonnegative tests of bounded shape.
-/

open Complex MeasureTheory Real Set Filter Topology Finset
open scoped BigOperators Real ComplexConjugate
open Zeta23 RHTower GaloisForLFunctions.ArithmeticCriticalityTheory
  GaloisForLFunctions.ArithmeticPositivityTheory
  GaloisForLFunctions.BiScaleUncertainty
  GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- At its own ordinate a zero is seen without phase:
`F̂(depthSum_ρ)(-Im ρ) = ∫ F₀(u) cosh((Re ρ - 1/2) u) du`, which is `≥ ∫ F₀` for `F₀ ≥ 0`. -/
theorem integral_le_norm_paperFT_depthSumProfile_self {F₀ : ℝ → ℝ} (hF₀ : Continuous F₀)
    (hF₀c : HasCompactSupport F₀) (hnn : ∀ u, 0 ≤ F₀ u) (ρ : ℂ) :
    (∫ u, F₀ u) ≤ ‖paperFT (depthSumProfile F₀ ρ) (-((ρ.im : ℝ) : ℂ))‖ := by
  set c : ℝ → ℝ := fun u => (Real.exp ((ρ.re - 1 / 2) * u) + Real.exp (-((ρ.re - 1 / 2) * u))) / 2
    with hc
  have hc1 : ∀ u, 1 ≤ c u := fun u => by
    rw [hc]
    have h := Real.one_le_cosh ((ρ.re - 1 / 2) * u)
    rwa [Real.cosh_eq] at h
  have hpt : ∀ u : ℝ, depthSumProfile F₀ ρ u * Complex.exp (Complex.I * (-((ρ.im : ℝ) : ℂ)) * u) =
      ((F₀ u * c u : ℝ) : ℂ) := fun u => by
    unfold depthSumProfile
    rw [mul_assoc, ← Complex.exp_add,
      show Complex.I * (ρ.im : ℂ) * (u : ℂ) + Complex.I * (-((ρ.im : ℝ) : ℂ)) * (u : ℂ) = 0 by
        ring,
      Complex.exp_zero, mul_one]
  have hval : paperFT (depthSumProfile F₀ ρ) (-((ρ.im : ℝ) : ℂ)) = ((∫ u, F₀ u * c u : ℝ) : ℂ) := by
    unfold paperFT
    simp_rw [hpt]
    exact integral_complex_ofReal
  have hcc : Continuous c := by rw [hc]; fun_prop
  have hint1 : Integrable F₀ := hF₀.integrable_of_hasCompactSupport hF₀c
  have hint2 : Integrable fun u => F₀ u * c u :=
    (hF₀.mul hcc).integrable_of_hasCompactSupport hF₀c.mul_right
  have hmono : (∫ u, F₀ u) ≤ ∫ u, F₀ u * c u :=
    integral_mono hint1 hint2 fun u => le_mul_of_one_le_right (hnn u) (hc1 u)
  rw [hval, Complex.norm_real, Real.norm_eq_abs]
  exact hmono.trans (le_abs_self _)

/-- The off-line depth differences of all zeros sum to at most `4 (A + 1)² e^A N² Φ(γ)`. -/
theorem tsum_depthDiff_le_offLineField {F₀ : ℝ → ℝ} (hF₀ : ContDiff ℝ 2 F₀)
    (hF₀c : HasCompactSupport F₀) {A : ℝ} (hA : 0 ≤ A) (hsupp : ∀ u : ℝ, A < |u| → F₀ u = 0)
    (γ : ℝ) :
    (∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℝ) *
        ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) - (γ : ℂ)) -
          paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) - (γ : ℂ))‖ ^ 2 / 4) ≤
      4 * (A + 1) ^ 2 * Real.exp A * envelopeWindowNorm F₀ ^ 2 * offLineField γ := by
  set K : ℝ := 4 * (A + 1) ^ 2 * Real.exp A * envelopeWindowNorm F₀ ^ 2 with hK
  set d : ℂ → ℝ := fun z =>
    ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf z - (γ : ℂ)) -
      paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf z) - (γ : ℂ))‖ ^ 2 / 4 with hd_def
  have hdom : ∀ q : XiZeroCopy, d (q.1 : ℂ) ≤
      K * (((q.1 : ℂ).re - 1 / 2) ^ 2 / (1 + ((q.1 : ℂ).im - γ) ^ 2) ^ 2) := fun q => by
    have hstrip := xi_divisor_support_re_mem_open_unit q.1
    exact depthDiff_sq_div_four_le_depth hF₀ hF₀c hA hsupp hstrip.1 hstrip.2 γ
  have hsum_q : Summable fun q : XiZeroCopy => d (q.1 : ℂ) :=
    ((summable_offLineField γ).mul_left K).of_nonneg_of_le
      (fun q => by simp only [hd_def]; positivity) hdom
  have hbridge := tsum_xiZeroCopy_eq_zetaCarrier (g := d) hsum_q
  have hle : (∑' q : XiZeroCopy, d (q.1 : ℂ)) ≤ K * offLineField γ := by
    rw [offLineField, ← tsum_mul_left]
    exact Summable.tsum_le_tsum hdom hsum_q ((summable_offLineField γ).mul_left K)
  have hform : (∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℝ) *
        ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) - (γ : ℂ)) -
          paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) - (γ : ℂ))‖ ^ 2 / 4) =
      ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℝ) * d (ρ : ℂ) :=
    tsum_congr fun ρ => by simp only [hd_def]; ring
  rw [hform, ← hbridge]
  exact hle

/-- **Pointwise law at a zero ordinate.** For a zero copy `q`, an aperture `A ≥ 0` and a
nonnegative `F₀ ∈ C²_c([-A, A])`, at `γ = Im q`:
`Q(F₀ cos γ·) + Q(F₀ sin γ·) ≥ (∫ F₀)² - 4 (A + 1)² e^A N(F₀)² Φ(γ)`. -/
theorem sq_integral_sub_offLineField_le_fullZeroForm {F₀ : ℝ → ℝ} (hF₀ : ContDiff ℝ 2 F₀)
    (hF₀c : HasCompactSupport F₀) {A : ℝ} (hA : 0 ≤ A) (hsupp : ∀ u : ℝ, A < |u| → F₀ u = 0)
    (hnn : ∀ u, 0 ≤ F₀ u) (q : XiZeroCopy) :
    (∫ u, F₀ u) ^ 2 - 4 * (A + 1) ^ 2 * Real.exp A * envelopeWindowNorm F₀ ^ 2 *
        offLineField (q.1 : ℂ).im ≤
      fullZeroForm (cosineSource F₀ (q.1 : ℂ).im) + fullZeroForm (sineSource F₀ (q.1 : ℂ).im) := by
  classical
  set γ : ℝ := (q.1 : ℂ).im with hγ
  rw [fullZeroForm_cosine_add_sine_eq_zeta_W_re hF₀ hF₀c γ]
  obtain ⟨hsum, -⟩ := integral_Icc_tsum_depthDiff_div_four_le hF₀ hF₀c (Γ := 1) le_rfl hA hsupp
  set ρ₀ : zetaZeroConfig.carrier := xiDivisorZetaCarrierEquiv q.1 with hρ₀
  have h := re_zeta_W_complexModulatedSource_ge_finset hF₀ hF₀c γ {ρ₀} (hsum γ)
  rw [Finset.sum_singleton] at h
  have hcoe : ((ρ₀ : ℂ)) = (q.1 : ℂ) := rfl
  have hm : (1 : ℝ) ≤ (zetaZeroConfig.mult ρ₀ : ℝ) := by
    have h1 := xiDivisorZetaCarrierEquiv_multiplicity q.1
    have h2 := xiSupportMultiplicity_pos q.1
    have h3 : (1 : ℕ) ≤ zetaZeroConfig.mult ρ₀ := by
      rw [hρ₀, ← h1]
      exact h2
    exact_mod_cast h3
  have hmain : (∫ u, F₀ u) ^ 2 ≤ ‖paperFT (depthSumProfile F₀ (ρ₀ : ℂ)) (-(γ : ℂ))‖ ^ 2 := by
    have hI : 0 ≤ ∫ u, F₀ u := integral_nonneg hnn
    have h1 := integral_le_norm_paperFT_depthSumProfile_self hF₀.continuous hF₀c hnn (q.1 : ℂ)
    rw [hcoe]
    exact pow_le_pow_left₀ hI h1 2
  have hmain' : (∫ u, F₀ u) ^ 2 ≤ (zetaZeroConfig.mult ρ₀ : ℝ) *
      ‖paperFT (depthSumProfile F₀ (ρ₀ : ℂ)) (-(γ : ℂ))‖ ^ 2 :=
    hmain.trans (le_mul_of_one_le_left (sq_nonneg _) hm)
  have htail := tsum_depthDiff_le_offLineField hF₀ hF₀c hA hsupp γ
  linarith

/-- **Weil positivity at almost every zero ordinate of a short window.** There are `C` and `Γ₀` such
that for `Γ ≥ Γ₀`, `Γ^{99/100} ≤ H ≤ Γ/8` and `η > 0`, the set `Z` of zero copies with ordinate in
`[Γ, Γ + H]` has at least `H log Γ / (16π)` elements, at most `C H / η` of them have `Φ(Im q) > η`,
and at every other one, for every aperture `A ≥ 0` and every nonnegative `F₀ ∈ C²_c([-A, A])`,
`Q(F₀ cos γ·) + Q(F₀ sin γ·) ≥ (∫ F₀)² - 4η (A + 1)² e^A N(F₀)²` at `γ = Im q`. -/
theorem exists_shortWindow_almostEvery_zeroOrdinate_positive :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ Γ₀ : ℝ, 64 ≤ Γ₀ ∧
      ∀ Γ : ℝ, Γ₀ ≤ Γ → ∀ H : ℝ, Γ ^ (99 / 100 : ℝ) ≤ H → H ≤ Γ / 8 → ∀ η : ℝ, 0 < η →
        ∃ Z : Finset XiZeroCopy,
          (∀ q : XiZeroCopy, q ∈ Z ↔ Γ ≤ (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ Γ + H) ∧
          H * Real.log Γ / (16 * Real.pi) ≤ (Z.card : ℝ) ∧
          ((Z.filter fun q => η < offLineField (q.1 : ℂ).im).card : ℝ) ≤ C * H / η ∧
          ∀ q ∈ Z, offLineField (q.1 : ℂ).im ≤ η →
            ∀ A : ℝ, 0 ≤ A → ∀ F₀ : ℝ → ℝ, ContDiff ℝ 2 F₀ → HasCompactSupport F₀ →
              (∀ u : ℝ, A < |u| → F₀ u = 0) → (∀ u, 0 ≤ F₀ u) →
              (∫ u, F₀ u) ^ 2 - 4 * η * (A + 1) ^ 2 * Real.exp A * envelopeWindowNorm F₀ ^ 2 ≤
                fullZeroForm (cosineSource F₀ (q.1 : ℂ).im) +
                  fullZeroForm (sineSource F₀ (q.1 : ℂ).im) := by
  obtain ⟨C, hC, Γ₀, hΓ₀, hsel⟩ := exists_shortWindow_almostEvery_zeroOrdinate_nearly_positive
  refine ⟨C, hC, Γ₀, hΓ₀, fun Γ hΓ H hH1 hH2 η hη => ?_⟩
  obtain ⟨Z, hZ, hcard, hbad, -⟩ := hsel Γ hΓ H hH1 hH2 η hη
  refine ⟨Z, hZ, hcard, hbad, fun q _ hq A hA F₀ hF₀ hF₀c hsupp hnn => ?_⟩
  have h := sq_integral_sub_offLineField_le_fullZeroForm hF₀ hF₀c hA hsupp hnn q
  have hK : 0 ≤ 4 * (A + 1) ^ 2 * Real.exp A * envelopeWindowNorm F₀ ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left hq hK
  linarith

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
