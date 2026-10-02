import GaloisForLFunctions.RHTower.MobiusDivisorCriticalSourceSimpleJet
import GaloisForLFunctions.RHTower.MobiusDivisorCriticalRetainedPrimeMellin
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Centered logarithmic Mellin jet of the complete moving prime head

The old-prime term is retained with its actual nonzero boundary value. Its
finite right slope and the Abel source's simple jet cannot cancel the full
prime head's positive logarithmic jet.
-/

noncomputable section
open Filter Topology MeasureTheory Set
namespace RHTower

/-- The actual head after retaining the complete old-prime subtraction. -/
def criticalMovingPrimeHead (x : ℝ) : ℝ :=
  criticalContinuousAbel x + (criticalPrimeAbelHead x).re - criticalRetainedPrimeHead x

/-- Real Mellin receiver at the critical boundary, with the full source ray. -/
def criticalSourceRealMellin (f : ℝ → ℝ) (δ : ℝ) : ℝ :=
  ∫ x in Ioi (1 : ℝ), x ^ (-(5 / 2 : ℝ) - δ) * f x

private theorem source_mellin_ofReal (f : ℝ → ℝ)
    (hf : ∀ x, x ≤ 1 → f x = 0) (δ : ℝ) :
    mellin (fun x : ℝ => (f x : ℂ)) (-((1 : ℂ) + (δ : ℂ) + 1 / 2)) =
      (criticalSourceRealMellin f δ : ℂ) := by
  unfold mellin criticalSourceRealMellin
  rw [← integral_complex_ofReal, ← integral_indicator measurableSet_Ioi,
    ← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : 1 < x
  · have hx0 : 0 < x := lt_trans zero_lt_one hx
    simp only [Set.indicator_apply, Set.mem_Ioi, hx, hx0, ite_true, smul_eq_mul]
    have hp : (x : ℂ) ^ (-((1 : ℂ) + (δ : ℂ) + 1 / 2) - 1) =
        ((x ^ (-(5 / 2 : ℝ) - δ) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow hx0.le]
      congr 1
      push_cast
      ring
    rw [hp, ← Complex.ofReal_mul]
  · have hz := hf x (le_of_not_gt hx)
    by_cases hx0 : 0 < x <;> simp [hx, hx0, hz]

private theorem primeHead_real (x : ℝ) :
    criticalPrimeAbelHead x = ((criticalPrimeAbelHead x).re : ℂ) := by
  obtain ⟨N, hN⟩ := exists_nat_ge x
  apply Complex.ext
  · simp
  · rw [criticalPrimeAbelHead_eq_finite x N hN]
    simp

private theorem primeHead_zero {x : ℝ} (hx : x ≤ 1) : criticalPrimeAbelHead x = 0 := by
  rw [criticalPrimeAbelHead_eq_finite x 1 (by simpa using hx)]
  apply Finset.sum_eq_zero
  intro p hp
  have hp1 : (p : ℕ) < 1 := by simpa using hp
  have hp2 := p.2.two_le
  omega

private theorem primeHead_mellin_real (δ : ℝ) :
    mellin criticalPrimeAbelHead (-((1 : ℂ) + (δ : ℂ) + 1 / 2)) =
      (criticalSourceRealMellin (fun x => (criticalPrimeAbelHead x).re) δ : ℂ) := by
  have hf : criticalPrimeAbelHead = fun x => ((criticalPrimeAbelHead x).re : ℂ) :=
    funext primeHead_real
  rw [hf]
  exact source_mellin_ofReal _ (fun x hx => by rw [primeHead_zero hx]; simp) δ

/-- The actual Abel source's first Mellin jet in the real source receiver. -/
theorem criticalAbelRealMellin_simpleJet :
    Tendsto (fun δ : ℝ => criticalSourceRealMellin criticalContinuousAbel δ / δ)
      (𝓝[>] (0 : ℝ)) (𝓝 (divisorHarmonicBoundary / 3)) := by
  have h := (Complex.continuous_re.tendsto ((divisorHarmonicBoundary : ℂ) / 3)).comp
    criticalAbelMellin_simpleJet
  simp only [Function.comp_def, source_mellin_ofReal criticalContinuousAbel
    (fun _ hx => criticalContinuousAbel_eq_zero_le_one hx),
    Complex.div_ofReal_re, Complex.ofReal_re] at h
  simpa using h

/-- The literal all-prime logarithmic jet in the real source receiver. -/
theorem criticalPrimeRealMellin_logJet :
    Tendsto (fun δ : ℝ =>
      criticalSourceRealMellin (fun x => (criticalPrimeAbelHead x).re) δ / δ / (-Real.log δ))
      (𝓝[>] (0 : ℝ)) (𝓝 (divisorHarmonicBoundary / 3)) := by
  have h := (Complex.continuous_re.tendsto ((divisorHarmonicBoundary : ℂ) / 3)).comp
    criticalPrimeAbelHead_simpleLogJet
  simp only [Function.comp_def, primeHead_mellin_real,
    Complex.div_ofReal_re, Complex.ofReal_re] at h
  simpa [abscissaLog] using h

private theorem jet_coefficient_pos : 0 < divisorHarmonicBoundary / 3 :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 90)
    criticalPrimeAbelHead_simpleLogJet_coefficient_lower

private theorem source_integrability_eventually :
    ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      IntegrableOn (fun x : ℝ => x ^ (-(5 / 2 : ℝ) - δ) * criticalContinuousAbel x)
        (Ioi (1 : ℝ)) ∧
      IntegrableOn (fun x : ℝ => x ^ (-(5 / 2 : ℝ) - δ) * (criticalPrimeAbelHead x).re)
        (Ioi (1 : ℝ)) := by
  filter_upwards [criticalAbelRealMellin_simpleJet.eventually (lt_mem_nhds jet_coefficient_pos),
    criticalPrimeRealMellin_logJet.eventually (lt_mem_nhds jet_coefficient_pos)] with δ hA hF
  constructor
  · apply Integrable.of_integral_ne_zero
    change criticalSourceRealMellin criticalContinuousAbel δ ≠ 0
    intro hz
    simp [hz] at hA
  · apply Integrable.of_integral_ne_zero
    change criticalSourceRealMellin (fun x => (criticalPrimeAbelHead x).re) δ ≠ 0
    intro hz
    simp [hz] at hF

/-- Eventual admission and the exact complete moving-head decomposition,
with the old-prime boundary transform present. -/
theorem criticalMovingPrimeHead_mellin_admission :
    ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      IntegrableOn (fun x : ℝ => x ^ (-(5 / 2 : ℝ) - δ) * criticalMovingPrimeHead x)
        (Ioi (1 : ℝ)) ∧
      criticalSourceRealMellin criticalMovingPrimeHead δ =
        criticalSourceRealMellin criticalContinuousAbel δ +
          criticalSourceRealMellin (fun x => (criticalPrimeAbelHead x).re) δ -
            criticalRetainedPrimeBoundaryTransform δ := by
  filter_upwards [source_integrability_eventually, self_mem_nhdsWithin] with δ hi hδ
  change 0 < δ at hδ
  have hiG := integrableOn_criticalRetainedPrimeHead hδ.le
  have hiAF : IntegrableOn (fun x : ℝ =>
      x ^ (-(5 / 2 : ℝ) - δ) * criticalContinuousAbel x +
        x ^ (-(5 / 2 : ℝ) - δ) * (criticalPrimeAbelHead x).re) (Ioi (1 : ℝ)) := hi.1.add hi.2
  have he (x : ℝ) : x ^ (-(5 / 2 : ℝ) - δ) * criticalMovingPrimeHead x =
      x ^ (-(5 / 2 : ℝ) - δ) * criticalContinuousAbel x +
        x ^ (-(5 / 2 : ℝ) - δ) * (criticalPrimeAbelHead x).re -
          x ^ (-(5 / 2 : ℝ) - δ) * criticalRetainedPrimeHead x := by
    dsimp [criticalMovingPrimeHead]
    ring
  constructor
  · exact ((hi.1.add hi.2).sub hiG).congr_fun (fun x _ => (he x).symm) measurableSet_Ioi
  · unfold criticalSourceRealMellin
    rw [setIntegral_congr_fun measurableSet_Ioi (fun x _ => he x),
      integral_sub hiAF hiG, integral_add hi.1 hi.2,
      criticalRetainedPrimeHead_transform_eq hδ.le]

/-- The complete moving head retains the positive logarithmic jet after
centering at its actual boundary value. -/
theorem criticalMovingPrimeHead_centered_logJet :
    Tendsto (fun δ : ℝ =>
      (criticalSourceRealMellin criticalMovingPrimeHead δ +
        criticalRetainedPrimeBoundaryTransform 0) / δ / (-Real.log δ))
      (𝓝[>] (0 : ℝ)) (𝓝 (divisorHarmonicBoundary / 3)) := by
  have hl : Tendsto (fun δ : ℝ => -Real.log δ) (𝓝[>] (0 : ℝ)) atTop :=
    tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have hA := criticalAbelRealMellin_simpleJet.div_atTop hl
  have hG := criticalRetainedPrimeBoundaryTransform_right_slope.div_atTop hl
  have h := (hA.add criticalPrimeRealMellin_logJet).sub hG
  simp only [zero_add, sub_zero] at h
  apply h.congr'
  filter_upwards [criticalMovingPrimeHead_mellin_admission] with δ hδ
  rw [hδ.2]
  ring

/-- The moving-head Mellin limit includes the full retained boundary mass. -/
theorem criticalMovingPrimeHead_mellin_boundary :
    Tendsto (criticalSourceRealMellin criticalMovingPrimeHead)
      (𝓝[>] (0 : ℝ)) (𝓝 (-criticalRetainedPrimeBoundaryTransform 0)) := by
  have hscale : Tendsto (fun δ : ℝ => δ * (-Real.log δ))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [Real.rpow_one, neg_mul, mul_neg, mul_comm, neg_zero] using
      (tendsto_log_mul_rpow_nhdsGT_zero (r := 1) zero_lt_one).neg
  have h := criticalMovingPrimeHead_centered_logJet.mul hscale
  simp only [mul_zero] at h
  have hc : Tendsto (fun δ : ℝ => criticalSourceRealMellin criticalMovingPrimeHead δ +
      criticalRetainedPrimeBoundaryTransform 0) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))] with δ hδ hδ1
    change 0 < δ at hδ
    have hl : -Real.log δ ≠ 0 := neg_ne_zero.mpr (ne_of_lt (Real.log_neg hδ hδ1))
    field_simp [ne_of_gt hδ, hl, ne_of_lt (Real.log_neg hδ hδ1)]
  simpa only [add_sub_cancel_right, zero_sub] using
    hc.sub (tendsto_const_nhds (x := criticalRetainedPrimeBoundaryTransform 0))

/-- The actual centered moving-head transform has an infinite positive
right boundary slope. -/
theorem criticalMovingPrimeHead_centered_slope_atTop :
    Tendsto (fun δ : ℝ =>
      (criticalSourceRealMellin criticalMovingPrimeHead δ +
        criticalRetainedPrimeBoundaryTransform 0) / δ)
      (𝓝[>] (0 : ℝ)) atTop := by
  have hl : Tendsto (fun δ : ℝ => -Real.log δ) (𝓝[>] (0 : ℝ)) atTop :=
    tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have h := criticalMovingPrimeHead_centered_logJet.pos_mul_atTop jet_coefficient_pos hl
  apply h.congr'
  filter_upwards [hl.eventually (eventually_gt_atTop (0 : ℝ))] with δ hδ
  exact div_mul_cancel₀ _ (ne_of_gt hδ)

end RHTower
