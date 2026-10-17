import GaloisForLFunctions.BiScaleUncertainty.SignedGramCapacity

/-!
# Supporting prices for the full measured translation Gram matrix

Packet correlations give signed slopes in [-1,1]. Their affine rescaling gives
bounded prices, and the norm support inequality gives an exact nonnegative
comparison remainder. Total division selects the zero subgradient at a zero
packet; no positivity or invertibility condition is imposed on the Gram matrix.
-/

set_option autoImplicit false
open MeasureTheory
open scoped BigOperators CompactlySupported
open RHTower.ArchimedeanAnomaly
namespace GaloisForLFunctions.BiScaleUncertainty.AnchoredGram
noncomputable section
variable {ι : Type*}

def packetScale (f : C_c(ℝ, ℝ)) (M : Finset ι) (a t : ι → ℝ) (W : ℝ) : ℝ :=
  Real.sqrt (autocorr f 0 * gram f M a t W)

def covariance (f : C_c(ℝ, ℝ)) (M : Finset ι) (a t : ι → ℝ) (W x : ℝ) : ℝ :=
  W * autocorr f x + ∑ j ∈ M, a j * autocorr f (x - t j)

def signedSlope (f : C_c(ℝ, ℝ)) (M : Finset ι) (a t : ι → ℝ) (W x : ℝ) : ℝ :=
  covariance f M a t W x / packetScale f M a t W

def price (f : C_c(ℝ, ℝ)) (M : Finset ι) (a t : ι → ℝ) (W x : ℝ) : ℝ :=
  (1 + signedSlope f M a t W x) / 2

theorem packetScale_eq_norm (f : C_c(ℝ, ℝ)) (M : Finset ι) (a t : ι → ℝ) (W : ℝ) :
    packetScale f M a t W = Real.sqrt (autocorr f 0) * ‖packet f M a t W‖ := by
  rw [packetScale, Real.sqrt_mul (autocorr_zero_nonneg f), ← packet_norm_sq,
    Real.sqrt_sq (norm_nonneg _)]

theorem covariance_eq_inner (f : C_c(ℝ, ℝ)) (M : Finset ι) (a t : ι → ℝ) (W x : ℝ) :
    covariance f M a t W x = RCLike.re (inner ℂ (packet f M a t W) (translationFeature f x)) := by
  simp only [packet, inner_add_left, sum_inner]
  simp_rw [inner_smul_left, translationFeature_inner]
  simp [covariance]

theorem covariance_abs_le (f : C_c(ℝ, ℝ)) (M : Finset ι) (a t : ι → ℝ) (W x : ℝ) :
    |covariance f M a t W x| ≤ packetScale f M a t W := by
  rw [covariance_eq_inner, packetScale_eq_norm]
  have hn : ‖translationFeature f x‖ = Real.sqrt (autocorr f 0) := by
    rw [← translationFeature_norm_sq f x, Real.sqrt_sq (norm_nonneg _)]
  calc
    _ ≤ ‖inner ℂ (packet f M a t W) (translationFeature f x)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖packet f M a t W‖ * ‖translationFeature f x‖ := norm_inner_le_norm _ _
    _ = _ := by rw [hn]; ring

/-- Signed correlations remain signed; only the normalized slope is bounded. -/
theorem signedSlope_bounds (f : C_c(ℝ, ℝ)) (M : Finset ι) (a t : ι → ℝ) (W x : ℝ) :
    -1 ≤ signedSlope f M a t W x ∧ signedSlope f M a t W x ≤ 1 := by
  apply abs_le.mp
  have hs : 0 ≤ packetScale f M a t W := Real.sqrt_nonneg _
  rw [signedSlope, abs_div, abs_of_nonneg hs]
  exact div_le_one_of_le₀ (covariance_abs_le f M a t W x) (Real.sqrt_nonneg _)

theorem price_bounds (f : C_c(ℝ, ℝ)) (M : Finset ι) (a t : ι → ℝ) (W x : ℝ) :
    0 ≤ price f M a t W x ∧ price f M a t W x ≤ 1 := by
  have h := signedSlope_bounds f M a t W x
  unfold price
  constructor <;> linarith only [h.1, h.2]

theorem packet_inner_eq (f : C_c(ℝ, ℝ)) (M : Finset ι) (a b t : ι → ℝ) (W : ℝ) :
    RCLike.re (inner ℂ (packet f M a t W) (packet f M b t W)) =
      W * covariance f M a t W 0 + ∑ i ∈ M, b i * covariance f M a t W (t i) := by
  simp only [covariance_eq_inner]
  change RCLike.re (inner ℂ (packet f M a t W)
    ((W : ℂ) • translationFeature f 0 + ∑ i ∈ M, (b i : ℂ) • translationFeature f (t i))) = _
  rw [inner_add_right, inner_sum]
  simp_rw [inner_smul_right]
  simp

theorem covariance_difference (f : C_c(ℝ, ℝ)) (M : Finset ι) (a b t : ι → ℝ) (W : ℝ) :
    (∑ i ∈ M, (b i - a i) * covariance f M a t W (t i)) =
      RCLike.re (inner ℂ (packet f M a t W) (packet f M b t W)) - ‖packet f M a t W‖ ^ 2 := by
  have ha := packet_inner_eq f M a a t W
  rw [inner_self_eq_norm_sq] at ha
  rw [packet_inner_eq]
  simp only [sub_mul, Finset.sum_sub_distrib]
  linarith only [ha]

/-- The norm's supporting hyperplane remains valid at zero through total division. -/
theorem signedSlope_support (f : C_c(ℝ, ℝ)) (M : Finset ι) (a b t : ι → ℝ) (W : ℝ) :
    autocorr f 0 * (∑ i ∈ M, (b i - a i) * signedSlope f M a t W (t i)) ≤
      packetScale f M b t W - packetScale f M a t W := by
  by_cases hz : packetScale f M a t W = 0
  · simp only [signedSlope, hz, div_zero, mul_zero, Finset.sum_const_zero, sub_zero]
    exact Real.sqrt_nonneg _
  · have hp : 0 < packetScale f M a t W := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hz)
    simp only [signedSlope, ← mul_div_assoc, ← Finset.sum_div]
    apply (div_le_iff₀ hp).2
    rw [covariance_difference]
    have h := mul_le_mul_of_nonneg_left
      (re_inner_le_norm (𝕜 := ℂ) (packet f M a t W) (packet f M b t W)) (autocorr_zero_nonneg f)
    have hprod : packetScale f M a t W * packetScale f M b t W =
        autocorr f 0 * (‖packet f M a t W‖ * ‖packet f M b t W‖) := by
      simp only [packetScale_eq_norm]
      nlinarith only [congrArg (fun z => z * (‖packet f M a t W‖ * ‖packet f M b t W‖))
        (Real.sq_sqrt (autocorr_zero_nonneg f))]
    have hsq : packetScale f M a t W ^ 2 = autocorr f 0 * ‖packet f M a t W‖ ^ 2 := by
      rw [packetScale_eq_norm, mul_pow, Real.sq_sqrt (autocorr_zero_nonneg f)]
    nlinarith only [h, hprod, hsq]

def dualRemainder (f : C_c(ℝ, ℝ)) (M : Finset ι) (a b t : ι → ℝ) (W : ℝ) : ℝ :=
  packetScale f M b t W - packetScale f M a t W -
    autocorr f 0 * ∑ i ∈ M, (b i - a i) * signedSlope f M a t W (t i)

theorem dualRemainder_nonneg (f : C_c(ℝ, ℝ)) (M : Finset ι) (a b t : ι → ℝ) (W : ℝ) :
    0 ≤ dualRemainder f M a b t W := sub_nonneg.mpr (signedSlope_support f M a b t W)

/-- Combined quantities cancel the singular anchor before integration. -/
theorem dualRemainder_eq_combined (f : C_c(ℝ, ℝ)) (M : Finset ι) (a b t : ι → ℝ) (W : ℝ) :
    dualRemainder f M a b t W = kernel f M a t W - kernel f M b t W +
      2 * autocorr f 0 * ((∑ i ∈ M, b i) - ∑ i ∈ M, a i) -
      2 * autocorr f 0 * ((∑ i ∈ M, b i * price f M a t W (t i)) -
        ∑ i ∈ M, a i * price f M a t W (t i)) := by
  unfold dualRemainder kernel packetScale price
  simp only [← mul_div_assoc, ← Finset.sum_div, mul_add, mul_one, Finset.sum_add_distrib,
    sub_mul, Finset.sum_sub_distrib]
  ring

/-- Prices are measurable finite expressions in the actual source Gram entries. -/
theorem measurable_price (f : C_c(ℝ, ℝ)) (M : Finset ι) (a : ℝ → ι → ℝ)
    (t : ι → ℝ) (W : ℝ → ℝ) (ha : ∀ i, Measurable (fun y => a y i)) (hW : Measurable W) (x : ℝ) :
    Measurable (fun y => price f M (a y) t (W y) x) := by
  have hw (i : Unit ⊕ ι) : Measurable (fun y => weights (W y) (a y) i) := by
    cases i with
    | inl u => exact hW
    | inr i => exact ha i
  have hg : Measurable (fun y => gram f M (a y) t (W y)) := by
    unfold gram translationGramEnergy
    exact (nodes M).measurable_sum fun i _ => (nodes M).measurable_sum fun j _ =>
      ((hw i).mul (hw j)).mul_const _
  have hc : Measurable (fun y => covariance f M (a y) t (W y) x) :=
    (hW.mul_const _).add (M.measurable_sum fun i _ => (ha i).mul_const _)
  exact (measurable_const.add (hc.div (Real.continuous_sqrt.measurable.comp (hg.const_mul _)))).div_const 2

end
end GaloisForLFunctions.BiScaleUncertainty.AnchoredGram
