import GaloisForLFunctions.RHTower.Sieve.ZetaLogDerivLineBound

/-!
# The logarithmic weight integrated along a vertical line

The weight `(1 + log(2+|t|))/|σ + it|` integrates to `O(log²T)` over `[−T, T]`: on the unit block the
denominator is bounded below by `σ`, and outside it the integrand is at most `(1+log(2+T))/|t|`,
whose integral is the harmonic logarithm.
-/

namespace RHTower.Sieve

open Complex MeasureTheory

noncomputable section

theorem norm_sigma_add_mul_I_ge (σ t : ℝ) :
    σ ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ := by
  have h := Complex.abs_re_le_norm ((σ : ℂ) + (t : ℂ) * Complex.I)
  have hre : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
  rw [hre] at h
  exact le_trans (le_abs_self σ) h

theorem abs_le_norm_sigma_add_mul_I {σ t : ℝ} :
    |t| ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ := by
  have h := Complex.abs_im_le_norm ((σ : ℂ) + (t : ℂ) * Complex.I)
  have him : ((σ : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
  rw [him] at h
  exact h

/-- The logarithmic weight is continuous. -/
theorem continuous_logWeight {σ : ℝ} (hσ : 0 < σ) :
    Continuous fun t : ℝ =>
      (1 + Real.log (2 + |t|)) / ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ := by
  have hnum : Continuous fun t : ℝ => 1 + Real.log (2 + |t|) :=
    continuous_const.add ((continuous_const.add continuous_abs).log fun t =>
      ne_of_gt (by positivity : (0 : ℝ) < 2 + |t|))
  have hden : Continuous fun t : ℝ => ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ := by
    refine Continuous.norm ?_
    exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  refine hnum.div hden fun t => ?_
  have h := norm_sigma_add_mul_I_ge σ t
  intro hz
  rw [hz] at h
  linarith

/-- **The logarithmic weight on a vertical segment.** -/
theorem integral_log_weight_le {σ T : ℝ} (hσ : 0 < σ) (hT : 1 ≤ T) :
    (∫ t in (-T)..T, (1 + Real.log (2 + |t|)) / ‖(σ : ℂ) + (t : ℂ) * Complex.I‖)
      ≤ 2 * (1 + Real.log 3) / σ + 2 * (1 + Real.log (2 + T)) * Real.log T := by
  have hT0 : (0 : ℝ) < T := by linarith
  set g : ℝ → ℝ := fun t => (1 + Real.log (2 + |t|)) / ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ with hg
  have hgc : Continuous g := continuous_logWeight hσ
  have hint : ∀ a b : ℝ, IntervalIntegrable g volume a b := fun a b =>
    hgc.intervalIntegrable a b
  have hsplit : (∫ t in (-T)..T, g t)
      = (∫ t in (-T)..(-1), g t) + (∫ t in (-1)..1, g t) + (∫ t in (1:ℝ)..T, g t) := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _),
      intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)]
  rw [hsplit]
  have hlogT : (0 : ℝ) ≤ Real.log T := Real.log_nonneg hT
  have hM : (0 : ℝ) ≤ 1 + Real.log (2 + T) := by
    have : (0 : ℝ) ≤ Real.log (2 + T) := Real.log_nonneg (by linarith)
    linarith
  -- the unit block
  have hmid : (∫ t in (-1)..1, g t) ≤ 2 * (1 + Real.log 3) / σ := by
    have hpt : ∀ t ∈ Set.Icc (-1 : ℝ) 1, g t ≤ (1 + Real.log 3) / σ := by
      intro t ht
      rw [Set.mem_Icc] at ht
      have habs : |t| ≤ 1 := abs_le.2 ⟨ht.1, ht.2⟩
      have hlog : Real.log (2 + |t|) ≤ Real.log 3 :=
        Real.log_le_log (by positivity) (by linarith)
      have hden := norm_sigma_add_mul_I_ge σ t
      have hden0 : (0 : ℝ) < ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ := by linarith
      have hnum : (0 : ℝ) ≤ 1 + Real.log (2 + |t|) := by
        have : (0 : ℝ) ≤ Real.log (2 + |t|) :=
          Real.log_nonneg (by have := abs_nonneg t; linarith)
        linarith
      rw [hg, div_le_div_iff₀ hden0 hσ]
      nlinarith [hlog, hden, hnum, hσ]
    have hmono := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (-1:ℝ) ≤ 1)
      (hint _ _) (intervalIntegrable_const) hpt
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
    refine hmono.trans (le_of_eq ?_)
    ring
  -- the right tail
  have hright : (∫ t in (1:ℝ)..T, g t) ≤ (1 + Real.log (2 + T)) * Real.log T := by
    have hpt : ∀ t ∈ Set.Icc (1 : ℝ) T, g t ≤ (1 + Real.log (2 + T)) * (1 / t) := by
      intro t ht
      rw [Set.mem_Icc] at ht
      have ht0 : (0 : ℝ) < t := by linarith [ht.1]
      have habs : |t| = t := abs_of_pos ht0
      have hlog : Real.log (2 + |t|) ≤ Real.log (2 + T) := by
        rw [habs]
        exact Real.log_le_log (by linarith) (by linarith [ht.2])
      have hden : t ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ := by
        have := abs_le_norm_sigma_add_mul_I (σ := σ) (t := t)
        rwa [habs] at this
      have hden0 : (0 : ℝ) < ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ := by linarith
      have hnum : (0 : ℝ) ≤ 1 + Real.log (2 + |t|) := by
        have : (0 : ℝ) ≤ Real.log (2 + |t|) :=
          Real.log_nonneg (by have := abs_nonneg t; linarith)
        linarith
      rw [hg, mul_one_div, div_le_div_iff₀ hden0 ht0]
      nlinarith [hlog, hden, hnum]
    have hbase : IntervalIntegrable (fun t : ℝ => 1 / t) volume 1 T := by
      refine intervalIntegral.intervalIntegrable_one_div ?_ continuousOn_id
      intro y hy
      rw [Set.uIcc_of_le hT] at hy
      exact ne_of_gt (by simpa using (by linarith [hy.1] : (0:ℝ) < y))
    have hii : IntervalIntegrable (fun t : ℝ => (1 + Real.log (2 + T)) * (1 / t)) volume 1 T :=
      hbase.const_mul _
    have hmono := intervalIntegral.integral_mono_on (μ := volume) hT (hint _ _) hii hpt
    rw [intervalIntegral.integral_const_mul,
      integral_one_div (by rw [Set.uIcc_of_le hT]; intro hc; linarith [hc.1])] at hmono
    refine hmono.trans (le_of_eq ?_)
    rw [div_one]
  -- the left tail
  have hleft : (∫ t in (-T)..(-1), g t) ≤ (1 + Real.log (2 + T)) * Real.log T := by
    have hTle : (-T : ℝ) ≤ -1 := by linarith
    have hpt : ∀ t ∈ Set.Icc (-T) (-1 : ℝ), g t ≤ (1 + Real.log (2 + T)) * (-(1 / t)) := by
      intro t ht
      rw [Set.mem_Icc] at ht
      have ht0 : t < 0 := by linarith [ht.2]
      have habs : |t| = -t := abs_of_neg ht0
      have hlog : Real.log (2 + |t|) ≤ Real.log (2 + T) := by
        rw [habs]
        exact Real.log_le_log (by linarith) (by linarith [ht.1])
      have hden : -t ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ := by
        have := abs_le_norm_sigma_add_mul_I (σ := σ) (t := t)
        rwa [habs] at this
      have hden0 : (0 : ℝ) < ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ := by linarith
      have hnum : (0 : ℝ) ≤ 1 + Real.log (2 + |t|) := by
        have : (0 : ℝ) ≤ Real.log (2 + |t|) :=
          Real.log_nonneg (by have := abs_nonneg t; linarith)
        linarith
      have hrw : (1 + Real.log (2 + T)) * (-(1 / t)) = (1 + Real.log (2 + T)) / (-t) := by
        field_simp
      rw [hg, hrw, div_le_div_iff₀ hden0 (by linarith)]
      nlinarith [hlog, hden, hnum]
    have hbase : IntervalIntegrable (fun t : ℝ => 1 / t) volume (-T) (-1) := by
      refine intervalIntegral.intervalIntegrable_one_div ?_ continuousOn_id
      intro y hy
      rw [Set.uIcc_of_le hTle] at hy
      exact ne_of_lt (by simpa using (by linarith [hy.2] : y < (0:ℝ)))
    have hii : IntervalIntegrable (fun t : ℝ => (1 + Real.log (2 + T)) * (-(1 / t)))
        volume (-T) (-1) := hbase.neg.const_mul _
    have hmono := intervalIntegral.integral_mono_on (μ := volume) hTle (hint _ _) hii hpt
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_neg,
      integral_one_div (by rw [Set.uIcc_of_le hTle]; intro hc; linarith [hc.2])] at hmono
    refine hmono.trans (le_of_eq ?_)
    have hid : (-1 : ℝ) / (-T) = 1 / T := by
      field_simp
    rw [hid, one_div, Real.log_inv]
    ring
  linarith [hmid, hright, hleft]

end

end RHTower.Sieve
