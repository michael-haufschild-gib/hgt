import GaloisForLFunctions.BiScaleUncertainty.ExponentialDecayCompactConvolution
import GaloisForLFunctions.BiScaleUncertainty.FactorialMuntzUniformTail
import GaloisForLFunctions.RHTower.CHMDGraphMollification
import GaloisForLFunctions.RHTower.WeilPrimeBlindZeroSideIdentity

/-! Actual normalized smooth Müntz sources in the decay-class Weil domain.
Both polar branches and the Abel prime pairing are retained. No continuity of
the unsmoothed Weil form, positivity, or RH is inferred. -/

open MeasureTheory Set Filter
open scoped Topology Convolution
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open _root_.RHTower _root_.RHTower.WeilSpectral _root_.RHTower.CHMDDoobGraph
open _root_.Zeta23
noncomputable section
set_option autoImplicit false

theorem factorialMuntzBoundaryCorrected_integrable (n : ℕ) :
    Integrable (factorialMuntzBoundaryCorrected n (factorialMuntzBoundaryCoefficient n)) := by
  have h := (factorialMuntzBoundaryCorrected_readout_integrable_extended n
    (1/2 : ℂ) (by norm_num)).re
  change Integrable (fun x : ℝ =>
    (Complex.exp (((1/2 : ℂ)-1/2)*(x : ℂ))*
      (factorialMuntzBoundaryCorrected n (factorialMuntzBoundaryCoefficient n) x : ℂ)).re) at h
  simpa only [sub_self, zero_mul, Complex.exp_zero, one_mul, Complex.ofReal_re] using h

/-- The actual corrected source has a global fixed-rate envelope; its compact
positive half does not require an unproved regularity hypothesis. -/
theorem factorialMuntzBoundaryCorrected_exp_bound (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ,
      |factorialMuntzBoundaryCorrected n (factorialMuntzBoundaryCoefficient n) x| ≤
        C*Real.exp (-|x|) := by
  have hc : Continuous (fun x : ℝ => sourceFactorialRamp (n+1) x*Real.exp |x|) :=
    (continuous_sourceFactorialRamp (n+1)).mul (Real.continuous_exp.comp continuous_abs)
  have hcs : HasCompactSupport (fun x : ℝ => sourceFactorialRamp (n+1) x*Real.exp |x|) :=
    (hasCompactSupport_sourceFactorialRamp (N := n+1) (by omega)).mul_right
  obtain ⟨B, hB⟩ := hc.bounded_above_of_compact_support hcs
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hr (x : ℝ) : |sourceFactorialRamp (n+1) x| ≤ B*Real.exp (-|x|) := by
    have hb : |sourceFactorialRamp (n+1) x| * Real.exp |x| ≤ B := by
      simpa only [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hB x
    have he : Real.exp |x| * Real.exp (-|x|) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    calc
      _ = (|sourceFactorialRamp (n+1) x| * Real.exp |x|)*Real.exp (-|x|) := by
        rw [mul_assoc, he, mul_one]
      _ ≤ _ := mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
  have ht (x : ℝ) : |factorialMuntzCorrectedTail n x| ≤
      (12/Real.sqrt ((n+1 : ℕ) : ℝ))*Real.exp (-|x|) := by
    have hb := factorialMuntzCorrectedTail_abs_le n x
    by_cases hx : x ≤ 0
    · rw [indicator_of_mem (show x ∈ Iic (0 : ℝ) from hx)] at hb
      calc
        _ ≤ 12*Real.exp (3*x/2)/Real.sqrt ((n+1 : ℕ) : ℝ) := hb
        _ ≤ 12*Real.exp x/Real.sqrt ((n+1 : ℕ) : ℝ) := by
          gcongr
          linarith
        _ = _ := by rw [abs_of_nonpos hx]; ring
    · rw [indicator_of_notMem (show x ∉ Iic (0 : ℝ) from hx)] at hb
      exact hb.trans (by positivity)
  refine ⟨B+12/Real.sqrt ((n+1 : ℕ) : ℝ), by positivity, fun x => ?_⟩
  have he : factorialMuntzBoundaryCorrected n (factorialMuntzBoundaryCoefficient n) x =
      sourceFactorialRamp (n+1) x+factorialMuntzCorrectedTail n x := by
    linarith only [factorialMuntzBoundaryCorrected_sub_ramp n x]
  rw [he]
  calc
    _ ≤ |sourceFactorialRamp (n+1) x|+|factorialMuntzCorrectedTail n x| := _root_.abs_add_le _ _
    _ ≤ B*Real.exp (-|x|)+(12/Real.sqrt ((n+1 : ℕ) : ℝ))*Real.exp (-|x|) := by
      linarith only [hr x, ht x]
    _ = _ := by ring

def factorialMuntzSmoothed (n k : ℕ) : ℝ → ℝ :=
  CHMDDoobGraph.mollifier k ⋆[ContinuousLinearMap.mul ℝ ℝ]
    factorialMuntzBoundaryCorrected n (factorialMuntzBoundaryCoefficient n)

/-- Every decay-class premise is discharged for this literal normalized
convolution of the canonical corrected source. -/
theorem factorialMuntzSmoothed_expDecayTest (n k : ℕ) :
    ExpDecayTest (factorialMuntzSmoothed n k) := by
  obtain ⟨C, hC, hf⟩ := factorialMuntzBoundaryCorrected_exp_bound n
  obtain ⟨hc, D, hD, hd⟩ := compactConvolution_contDiff_exp_bounds
    (factorialMuntzBoundaryCorrected_integrable n) hC hf (mollifier_contDiff k) (mollifier_compact k)
  refine ⟨hc, 1/2, D, by norm_num, hD, fun x => ?_⟩
  simpa only [factorialMuntzSmoothed, show (1/2 : ℝ)+1/2 = 1 by norm_num, one_mul] using hd x

/-- The normalization is exactly unit mass, without an omitted scale factor. -/
theorem factorialMuntzSmoothed_integral (n k : ℕ) :
    (∫ x : ℝ, factorialMuntzSmoothed n k x) =
      ∫ x : ℝ, factorialMuntzBoundaryCorrected n (factorialMuntzBoundaryCoefficient n) x := by
  simpa only [factorialMuntzSmoothed, ContinuousLinearMap.mul_apply', mollifier_integral, one_mul] using
    integral_convolution (ContinuousLinearMap.mul ℝ ℝ) (mollifier_integrable k)
      (factorialMuntzBoundaryCorrected_integrable n)

/-- The normalized family returns to the actual corrected source almost
everywhere in Lebesgue measure. No Weil-form limit is asserted. -/
theorem factorialMuntzSmoothed_tendsto_ae (n : ℕ) :
    ∀ᵐ x : ℝ, Tendsto (fun k : ℕ => factorialMuntzSmoothed n k x) atTop
      (𝓝 (factorialMuntzBoundaryCorrected n (factorialMuntzBoundaryCoefficient n) x)) := by
  have hr : ∀ᶠ k : ℕ in atTop,
      (WeilOneSided.narrowBump k).rOut ≤ 2*(WeilOneSided.narrowBump k).rIn :=
    Eventually.of_forall fun k => by
      apply le_of_eq
      dsimp [WeilOneSided.narrowBump]
      field_simp
      ring
  have ht := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (μ := (volume : Measure ℝ)) narrowBump_rOut_tendsto hr
      (factorialMuntzBoundaryCorrected_integrable n).locallyIntegrable
  simpa only [factorialMuntzSmoothed, CHMDDoobGraph.mollifier, convolution_def,
    ContinuousLinearMap.mul_apply', ContinuousLinearMap.lsmul_apply, smul_eq_mul] using ht

private theorem mollifier_readout_integrable (k : ℕ) (s : ℂ) :
    Integrable (fun x : ℝ => Complex.exp ((s-1/2)*(x : ℂ))*(CHMDDoobGraph.mollifier k x : ℂ)) := by
  have hk : Continuous (fun x : ℝ => Complex.exp ((s-1/2)*(x : ℂ))) := by fun_prop
  exact (hk.mul (Complex.continuous_ofReal.comp (mollifier_contDiff k).continuous)).integrable_of_hasCompactSupport
    ((mollifier_compact k).comp_left Complex.ofReal_zero).mul_left

/-- Every fixed exponential moment of the normalized kernel tends to one. -/
theorem mollifier_readout_tendsto (s : ℂ) :
    Tendsto (fun k : ℕ => ∫ x : ℝ,
      Complex.exp ((s-1/2)*(x : ℂ))*(CHMDDoobGraph.mollifier k x : ℂ)) atTop (𝓝 1) := by
  have hc : Continuous (fun x : ℝ => Complex.exp (-((s-1/2)*(x : ℂ)))) := by fun_prop
  have h := ContDiffBump.convolution_tendsto_right_of_continuous
    (μ := (volume : Measure ℝ)) narrowBump_rOut_tendsto hc (0 : ℝ)
  simpa only [CHMDDoobGraph.mollifier, convolution_def, ContinuousLinearMap.lsmul_apply,
    Complex.real_smul, zero_sub, Complex.ofReal_neg, mul_neg, neg_mul, neg_neg,
    Complex.ofReal_zero, mul_zero, zero_mul, neg_zero, Complex.exp_zero, mul_comm] using h

/-- Exact Fubini factorization for the actual smoothed source throughout the
extended half-plane, including both polar parameters. -/
theorem factorialMuntzSmoothed_readout (n k : ℕ) (s : ℂ) (hs : -1 < s.re) :
    Integrable (fun x : ℝ => Complex.exp ((s-1/2)*(x : ℂ))*(factorialMuntzSmoothed n k x : ℂ)) ∧
    (∫ x : ℝ, Complex.exp ((s-1/2)*(x : ℂ))*(factorialMuntzSmoothed n k x : ℂ)) =
      (∫ x : ℝ, Complex.exp ((s-1/2)*(x : ℂ))*(CHMDDoobGraph.mollifier k x : ℂ))*
        (∫ x : ℝ, Complex.exp ((s-1/2)*(x : ℂ))*
          (factorialMuntzBoundaryCorrected n (factorialMuntzBoundaryCoefficient n) x : ℂ)) :=
  integral_exponential_tilt_convolution (s-1/2) (mollifier_readout_integrable k s)
    (factorialMuntzBoundaryCorrected_readout_integrable_extended n s hs)

/-- Smoothing preserves the limiting readout throughout the extended
half-plane, in particular at both polar parameters. -/
theorem factorialMuntzSmoothed_readout_tendsto (n : ℕ) (s : ℂ) (hs : -1 < s.re) :
    Tendsto (fun k : ℕ => ∫ x : ℝ,
      Complex.exp ((s-1/2)*(x : ℂ))*(factorialMuntzSmoothed n k x : ℂ)) atTop
      (𝓝 (∫ x : ℝ, Complex.exp ((s-1/2)*(x : ℂ))*
        (factorialMuntzBoundaryCorrected n (factorialMuntzBoundaryCoefficient n) x : ℂ))) := by
  have h := (mollifier_readout_tendsto s).mul_const
    (∫ x : ℝ, Complex.exp ((s-1/2)*(x : ℂ))*
      (factorialMuntzBoundaryCorrected n (factorialMuntzBoundaryCoefficient n) x : ℂ))
  simpa only [one_mul, ← (factorialMuntzSmoothed_readout n _ s hs).2] using h

theorem factorialMuntzSmoothed_zeta_readout (n k : ℕ) {ρ : ℂ}
    (hρ : 0 < ρ.re) (hz : riemannZeta ρ = 0) :
    (∫ x : ℝ, Complex.exp ((ρ-1/2)*(x : ℂ))*(factorialMuntzSmoothed n k x : ℂ)) =
      (∫ x : ℝ, Complex.exp ((ρ-1/2)*(x : ℂ))*(CHMDDoobGraph.mollifier k x : ℂ))*
        ((factorialMuntzBoundaryCoefficient n : ℂ)/ρ) := by
  rw [(factorialMuntzSmoothed_readout n k ρ (by linarith)).2,
    factorialMuntzBoundaryCorrected_zeta_readout n _ hρ hz]

/-- At every fixed right-half-plane zero, sufficiently narrow smoothings
retain the canonical correction's nonzero readout. -/
theorem factorialMuntzSmoothed_zeta_readout_eventually_ne_zero (n : ℕ) {ρ : ℂ}
    (hρ : 0 < ρ.re) (hz : riemannZeta ρ = 0) :
    ∀ᶠ k : ℕ in atTop, (∫ x : ℝ,
      Complex.exp ((ρ-1/2)*(x : ℂ))*(factorialMuntzSmoothed n k x : ℂ)) ≠ 0 :=
  (factorialMuntzSmoothed_readout_tendsto n ρ (by linarith)).eventually_ne
    (factorialMuntzBoundaryCorrected_canonical_zeta_readout_ne_zero n hρ hz)

/-- The complete decay-class Weil identity for the actual source. Domain
regularity, derivative decay, and polar admissibility are produced above. -/
theorem factorialMuntzSmoothed_weil_identity (n k : ℕ) :
    archPoleEnergy (factorialMuntzSmoothed n k) =
      (zetaZeroConfig.W (fun x => (factorialMuntzSmoothed n k x : ℂ))
        (fun x => (factorialMuntzSmoothed n k x : ℂ))).re+
      abelPrimePairing (fun j => (ArithmeticFunction.vonMangoldt j : ℝ))
        (factorialMuntzSmoothed n k) :=
  archPoleEnergy_eq_re_W_add_abelPrimePairing (factorialMuntzSmoothed_expDecayTest n k)

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
