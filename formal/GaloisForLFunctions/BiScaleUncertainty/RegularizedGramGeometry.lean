import GaloisForLFunctions.BiScaleUncertainty.SignedGramDualSupport

/-!
# Regularized full-Gram packet geometry

Adding a fixed orthogonal coordinate to the packet norm preserves every measured
Gram entry. The resulting kernel differs from the original by at most `ε R`.
Its exact remainder identity gives a quadratic bound even when the original
packet vanishes. No spectral lower bound is assumed.
-/

set_option autoImplicit false
open MeasureTheory
open scoped BigOperators CompactlySupported
open RHTower.ArchimedeanAnomaly
namespace GaloisForLFunctions.BiScaleUncertainty.AnchoredGram
noncomputable section
variable {ι : Type*}

def regularizedScale (f : C_c(ℝ, ℝ)) (M : Finset ι) (a t : ι → ℝ) (W ε : ℝ) : ℝ :=
  Real.sqrt (packetScale f M a t W ^ 2 + (ε * autocorr f 0) ^ 2)

def regularizedSlope (f : C_c(ℝ, ℝ)) (M : Finset ι) (a t : ι → ℝ) (W ε x : ℝ) : ℝ :=
  covariance f M a t W x / regularizedScale f M a t W ε

def regularizedPrice (f : C_c(ℝ, ℝ)) (M : Finset ι) (a t : ι → ℝ) (W ε x : ℝ) : ℝ :=
  (1 + regularizedSlope f M a t W ε x) / 2

def regularizedKernel (f : C_c(ℝ, ℝ)) (M : Finset ι) (a t : ι → ℝ) (W ε : ℝ) : ℝ :=
  autocorr f 0 * (W + ∑ i ∈ M, a i) - regularizedScale f M a t W ε

def regularizedRemainder (f : C_c(ℝ, ℝ)) (M : Finset ι)
    (a b t : ι → ℝ) (W ε : ℝ) : ℝ :=
  regularizedScale f M b t W ε - regularizedScale f M a t W ε -
    autocorr f 0 * (∑ i ∈ M, (b i - a i) * covariance f M a t W (t i)) /
      regularizedScale f M a t W ε

theorem regularizedScale_sq (f : C_c(ℝ, ℝ)) (M : Finset ι) (a t : ι → ℝ) (W ε : ℝ) :
    regularizedScale f M a t W ε ^ 2 =
      autocorr f 0 * ‖packet f M a t W‖ ^ 2 + (ε * autocorr f 0) ^ 2 := by
  rw [regularizedScale, Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _)),
    packetScale_eq_norm, mul_pow, Real.sq_sqrt (autocorr_zero_nonneg f)]

theorem regularizedScale_nonneg (f : C_c(ℝ, ℝ)) (M : Finset ι) (a t : ι → ℝ) (W ε : ℝ) :
    0 ≤ regularizedScale f M a t W ε := Real.sqrt_nonneg _

theorem packetScale_le_regularizedScale (f : C_c(ℝ, ℝ)) (M : Finset ι)
    (a t : ι → ℝ) (W ε : ℝ) :
    packetScale f M a t W ≤ regularizedScale f M a t W ε :=
  Real.le_sqrt_of_sq_le (le_add_of_nonneg_right (sq_nonneg _))

theorem regularizedScale_lower (f : C_c(ℝ, ℝ)) (M : Finset ι)
    (a t : ι → ℝ) (W ε : ℝ) : ε * autocorr f 0 ≤ regularizedScale f M a t W ε :=
  Real.le_sqrt_of_sq_le (le_add_of_nonneg_left (sq_nonneg _))

theorem regularizedScale_error (f : C_c(ℝ, ℝ)) (M : Finset ι)
    (a t : ι → ℝ) (W : ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    0 ≤ regularizedScale f M a t W ε - packetScale f M a t W ∧
    regularizedScale f M a t W ε - packetScale f M a t W ≤ ε * autocorr f 0 := by
  refine ⟨sub_nonneg.mpr (packetScale_le_regularizedScale f M a t W ε), ?_⟩
  have hp : 0 ≤ packetScale f M a t W := Real.sqrt_nonneg _
  have hc := mul_nonneg hε (autocorr_zero_nonneg f)
  have h : regularizedScale f M a t W ε ≤ packetScale f M a t W + ε * autocorr f 0 := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨add_nonneg hp hc, by nlinarith only [mul_nonneg hp hc]⟩
  linarith only [h]

theorem regularizedKernel_error (f : C_c(ℝ, ℝ)) (M : Finset ι)
    (a t : ι → ℝ) (W : ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    0 ≤ kernel f M a t W - regularizedKernel f M a t W ε ∧
    kernel f M a t W - regularizedKernel f M a t W ε ≤ ε * autocorr f 0 := by
  have h := regularizedScale_error f M a t W hε
  unfold kernel regularizedKernel packetScale at *
  constructor <;> linarith only [h.1, h.2]

theorem regularizedPrice_bounds (f : C_c(ℝ, ℝ)) (M : Finset ι)
    (a t : ι → ℝ) (W ε x : ℝ) :
    0 ≤ regularizedPrice f M a t W ε x ∧ regularizedPrice f M a t W ε x ≤ 1 := by
  have hs := regularizedScale_nonneg f M a t W ε
  have hb : |regularizedSlope f M a t W ε x| ≤ 1 := by
    rw [regularizedSlope, abs_div, abs_of_nonneg hs]
    exact div_le_one_of_le₀ ((covariance_abs_le f M a t W x).trans
      (packetScale_le_regularizedScale f M a t W ε)) hs
  have h := abs_le.mp hb
  unfold regularizedPrice
  constructor <;> linarith only [h.1, h.2]

private theorem augmented_cauchy (x y c : ℝ) :
    x * y + c ^ 2 ≤ Real.sqrt (x ^ 2 + c ^ 2) * Real.sqrt (y ^ 2 + c ^ 2) := by
  have ha := Real.sqrt_nonneg (x ^ 2 + c ^ 2)
  have hb := Real.sqrt_nonneg (y ^ 2 + c ^ 2)
  have hsq : (Real.sqrt (x ^ 2 + c ^ 2) * Real.sqrt (y ^ 2 + c ^ 2)) ^ 2 =
      (x * y + c ^ 2) ^ 2 + (c * (x - y)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _)),
      Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))]
    ring
  nlinarith only [hsq, sq_nonneg (c * (x - y)), mul_nonneg ha hb]

theorem regularizedRemainder_nonneg (f : C_c(ℝ, ℝ)) (M : Finset ι)
    (a b t : ι → ℝ) (W ε : ℝ) : 0 ≤ regularizedRemainder f M a b t W ε := by
  by_cases hz : regularizedScale f M a t W ε = 0
  · simpa [regularizedRemainder, hz] using regularizedScale_nonneg f M b t W ε
  have hp := lt_of_le_of_ne (regularizedScale_nonneg f M a t W ε) (Ne.symm hz)
  have hc := augmented_cauchy (packetScale f M a t W) (packetScale f M b t W)
    (ε * autocorr f 0)
  change packetScale f M a t W * packetScale f M b t W + (ε * autocorr f 0) ^ 2 ≤
    regularizedScale f M a t W ε * regularizedScale f M b t W ε at hc
  have hprod : packetScale f M a t W * packetScale f M b t W =
      autocorr f 0 * (‖packet f M a t W‖ * ‖packet f M b t W‖) := by
    rw [packetScale_eq_norm, packetScale_eq_norm]
    nlinarith only [congrArg (fun z => z * (‖packet f M a t W‖ * ‖packet f M b t W‖))
      (Real.sq_sqrt (autocorr_zero_nonneg f))]
  rw [hprod] at hc
  have hi := mul_le_mul_of_nonneg_left
    (re_inner_le_norm (𝕜 := ℂ) (packet f M a t W) (packet f M b t W))
    (autocorr_zero_nonneg f)
  have hs := regularizedScale_sq f M a t W ε
  unfold regularizedRemainder
  apply sub_nonneg.mpr
  apply (div_le_iff₀ hp).2
  rw [covariance_difference]
  nlinarith only [hc, hi, hs]

/-- Exact curvature defect, including the zero-energy source. -/
theorem regularizedRemainder_identity (f : C_c(ℝ, ℝ)) (M : Finset ι)
    (a b t : ι → ℝ) (W : ℝ) {ε : ℝ} (hε : 0 < ε) :
    2 * regularizedScale f M a t W ε * regularizedRemainder f M a b t W ε =
      autocorr f 0 * ‖packet f M a t W - packet f M b t W‖ ^ 2 -
        (regularizedScale f M b t W ε - regularizedScale f M a t W ε) ^ 2 := by
  by_cases hR : autocorr f 0 = 0
  · simp [regularizedRemainder, regularizedScale, packetScale_eq_norm, hR]
  have hRp := lt_of_le_of_ne (autocorr_zero_nonneg f) (Ne.symm hR)
  have hp := (mul_pos hε hRp).trans_le (regularizedScale_lower f M a t W ε)
  have ha := regularizedScale_sq f M a t W ε
  have hb := regularizedScale_sq f M b t W ε
  have hd := norm_sub_sq (𝕜 := ℂ) (packet f M a t W) (packet f M b t W)
  have hc : (2 * regularizedScale f M a t W ε) *
      (autocorr f 0 * (∑ i ∈ M, (b i - a i) * covariance f M a t W (t i)) /
        regularizedScale f M a t W ε) =
      2 * autocorr f 0 * (∑ i ∈ M, (b i - a i) * covariance f M a t W (t i)) := by
    field_simp [hp.ne']
  unfold regularizedRemainder
  rw [mul_sub, hc]
  rw [covariance_difference]
  nlinarith only [ha, hb, congrArg (fun z => autocorr f 0 * z) hd]

/-- Uniform quadratic curvature requires no positivity of the original packet. -/
theorem regularizedRemainder_le (f : C_c(ℝ, ℝ)) (M : Finset ι)
    (a b t : ι → ℝ) (W : ℝ) {ε : ℝ} (hε : 0 < ε) :
    regularizedRemainder f M a b t W ε ≤
      ‖packet f M a t W - packet f M b t W‖ ^ 2 / (2 * ε) := by
  by_cases hR : autocorr f 0 = 0
  · simp only [regularizedRemainder, regularizedScale, packetScale_eq_norm, hR,
      Real.sqrt_zero, zero_mul, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      add_zero, sub_zero, div_zero]
    positivity
  have hRp := lt_of_le_of_ne (autocorr_zero_nonneg f) (Ne.symm hR)
  have hi := regularizedRemainder_identity f M a b t W hε
  have hl := mul_le_mul_of_nonneg_right (regularizedScale_lower f M a t W ε)
    (regularizedRemainder_nonneg f M a b t W ε)
  apply (le_div_iff₀ (by positivity : 0 < 2 * ε)).2
  apply le_of_mul_le_mul_left (a := autocorr f 0) (a0 := hRp)
  nlinarith only [hi, hl,
    sq_nonneg (regularizedScale f M b t W ε - regularizedScale f M a t W ε)]

theorem regularizedRemainder_eq_combined (f : C_c(ℝ, ℝ)) (M : Finset ι)
    (a b t : ι → ℝ) (W ε : ℝ) :
    regularizedRemainder f M a b t W ε =
      regularizedKernel f M a t W ε - regularizedKernel f M b t W ε +
      2 * autocorr f 0 * ((∑ i ∈ M, b i) - ∑ i ∈ M, a i) -
      2 * autocorr f 0 * ((∑ i ∈ M, b i * regularizedPrice f M a t W ε (t i)) -
        ∑ i ∈ M, a i * regularizedPrice f M a t W ε (t i)) := by
  unfold regularizedRemainder regularizedKernel regularizedPrice regularizedSlope
  simp only [← mul_div_assoc, ← Finset.sum_div, mul_add, mul_one, Finset.sum_add_distrib,
    sub_mul, Finset.sum_sub_distrib]
  ring

theorem measurable_regularizedScale (f : C_c(ℝ, ℝ)) (M : Finset ι)
    (a : ℝ → ι → ℝ) (t : ι → ℝ) (W : ℝ → ℝ) (ε : ℝ)
    (ha : ∀ i, Measurable (fun y => a y i)) (hW : Measurable W) :
    Measurable (fun y => regularizedScale f M (a y) t (W y) ε) := by
  have hw (i : Unit ⊕ ι) : Measurable (fun y => weights (W y) (a y) i) := by
    cases i with
    | inl u => exact hW
    | inr i => exact ha i
  have hg : Measurable (fun y => gram f M (a y) t (W y)) := by
    unfold gram translationGramEnergy
    exact (nodes M).measurable_sum fun i _ => (nodes M).measurable_sum fun j _ =>
      ((hw i).mul (hw j)).mul_const _
  exact Real.continuous_sqrt.measurable.comp
    (((Real.continuous_sqrt.measurable.comp (hg.const_mul _)).pow_const 2).add_const _)

theorem measurable_regularizedPrice (f : C_c(ℝ, ℝ)) (M : Finset ι)
    (a : ℝ → ι → ℝ) (t : ι → ℝ) (W : ℝ → ℝ) (ε x : ℝ)
    (ha : ∀ i, Measurable (fun y => a y i)) (hW : Measurable W) :
    Measurable (fun y => regularizedPrice f M (a y) t (W y) ε x) := by
  have hc : Measurable (fun y => covariance f M (a y) t (W y) x) :=
    (hW.mul_const _).add (M.measurable_sum fun i _ => (ha i).mul_const _)
  exact (measurable_const.add (hc.div
    (measurable_regularizedScale f M a t W ε ha hW))).div_const 2

end
end GaloisForLFunctions.BiScaleUncertainty.AnchoredGram
