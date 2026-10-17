import GaloisForLFunctions.BiScaleUncertainty.DistantCopyCorrelationTopology
import GaloisForLFunctions.BiScaleUncertainty.UnitEnergySmallSources

/-!
# Exact polar-moment scale of a separated copy

The normalized polar moment changes by the mixing coefficient multiplied by
`cosh (T / 2)`. A concrete nonnegative smooth bump has strictly positive moment.
-/

open MeasureTheory Set Filter Topology
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

def normalizedPolarMoment (f : ℝ → ℝ) : ℝ :=
  (∫ x in Ioi 0, autocorr f x * Real.cosh (x / 2)) / autocorr f 0

theorem integrable_normalizedPolarIntegrand {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    Integrable (fun x => normalizedSourceCorrelation f x * Real.cosh (x / 2)) := by
  have hi : Integrable (fun x => autocorr f x * Real.cosh (x / 2)) :=
    ((continuous_autocorr hf hfc).mul (by fun_prop)).integrable_of_hasCompactSupport
      (hasCompactSupport_autocorr hfc).mul_right
  convert hi.div_const (autocorr f 0) using 1
  funext x
  dsimp [normalizedSourceCorrelation]
  ring

theorem normalizedPolarMoment_eq_integral (f : ℝ → ℝ) :
    normalizedPolarMoment f = ∫ x in Ioi 0,
      normalizedSourceCorrelation f x * Real.cosh (x / 2) := by
  unfold normalizedPolarMoment normalizedSourceCorrelation
  rw [← integral_div]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

/-- The actual half-line polar moment is half the product of the two source moments. -/
theorem two_mul_integral_autocorr_cosh {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    2 * (∫ x in Ioi 0, autocorr f x * Real.cosh (x / 2)) =
      (∫ u, f u * Real.exp (u / 2)) * ∫ u, f u * Real.exp (-u / 2) := by
  have he := integral_comp_abs (f := fun x => autocorr f x * Real.cosh (x / 2))
  have hid : (fun x : ℝ => autocorr f |x| * Real.cosh (|x| / 2)) =
      fun x => autocorr f x * Real.cosh (x / 2) := by
    funext x
    rcases abs_choice x with hx | hx
    · rw [hx]
    · rw [hx, autocorr_neg, show -x / 2 = -(x / 2) by ring, Real.cosh_neg]
  rw [hid, integral_autocorr_mul_cosh hf hfc] at he
  exact he.symm

/-- Every real amplitude has an exact polar multiplier before normalization. -/
theorem integral_subtractCopy_autocorr_cosh {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (a T : ℝ) :
    (∫ x in Ioi 0, autocorr (subtractCopy f a T) x * Real.cosh (x / 2)) =
      (1 + a ^ 2 - 2 * a * Real.cosh (T / 2)) *
        ∫ x in Ioi 0, autocorr f x * Real.cosh (x / 2) := by
  have hp := integral_subtractCopy_mul_exp hf.continuous hfc a T (1 / 2)
  have hm := integral_subtractCopy_mul_exp hf.continuous hfc a T (-(1 / 2))
  have hp' : (∫ u, subtractCopy f a T u * Real.exp (u / 2)) =
      (1 - a * Real.exp (T / 2)) * ∫ u, f u * Real.exp (u / 2) := by
    simpa only [show ∀ u : ℝ, (1 / 2 : ℝ) * u = u / 2 by intro u; ring] using hp
  have hm' : (∫ u, subtractCopy f a T u * Real.exp (-u / 2)) =
      (1 - a * Real.exp (-T / 2)) * ∫ u, f u * Real.exp (-u / 2) := by
    simpa only [show ∀ u : ℝ, (-(1 / 2) : ℝ) * u = -u / 2 by intro u; ring] using hm
  have he : Real.exp (T / 2) * Real.exp (-T / 2) = 1 := by
    rw [← Real.exp_add, show T / 2 + -T / 2 = 0 by ring, Real.exp_zero]
  have hc : (1 - a * Real.exp (T / 2)) * (1 - a * Real.exp (-T / 2)) =
      1 + a ^ 2 - 2 * a * Real.cosh (T / 2) := by
    calc
      _ = 1 - a * (Real.exp (T / 2) + Real.exp (-T / 2)) +
          a ^ 2 * (Real.exp (T / 2) * Real.exp (-T / 2)) := by ring
      _ = _ := by rw [he, Real.cosh_eq, show -(T / 2) = -T / 2 by ring]; ring
  have hg := two_mul_integral_autocorr_cosh (contDiff_subtractCopy hf a T)
    (hasCompactSupport_subtractCopy hfc a T)
  rw [hp', hm'] at hg
  have hb := two_mul_integral_autocorr_cosh hf hfc
  calc
    _ = ((1 - a * Real.exp (T / 2)) * (1 - a * Real.exp (-T / 2))) *
        ((∫ u, f u * Real.exp (u / 2)) * ∫ u, f u * Real.exp (-u / 2)) / 2 := by
      nlinarith only [hg]
    _ = _ := by rw [hc, ← hb]; ring

/-- The polar weight magnifies the correlation mixing coefficient by `cosh (T / 2)`. -/
theorem normalizedPolarMoment_subtractCopy {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hR : 0 < autocorr f 0)
    {D T : ℝ} (hs : ∀ x, D < |x| → autocorr f x = 0) (hT : D < T) (a : ℝ) :
    normalizedPolarMoment (subtractCopy f a T) =
      (1 - 2 * copyMixingCoefficient a * Real.cosh (T / 2)) * normalizedPolarMoment f := by
  unfold normalizedPolarMoment
  rw [integral_subtractCopy_autocorr_cosh hf hfc,
    autocorr_subtractCopy_zero hf.continuous hfc hs hT]
  unfold copyMixingCoefficient
  have hd : (1 + a ^ 2 : ℝ) ≠ 0 := by positivity
  field_simp [hR.ne', hd]

/-- For a nonzero seed moment, polar continuity is exactly weighted mixing decay. -/
theorem tendsto_normalizedPolarMoment_subtractCopy_iff {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hR : 0 < autocorr f 0)
    (hP : normalizedPolarMoment f ≠ 0) {D : ℝ}
    (hs : ∀ x, D < |x| → autocorr f x = 0)
    (a T : ℕ → ℝ) (hT : ∀ n, D < T n) :
    Tendsto (fun n => normalizedPolarMoment (subtractCopy f (a n) (T n))) atTop
      (𝓝 (normalizedPolarMoment f)) ↔
    Tendsto (fun n => copyMixingCoefficient (a n) * Real.cosh (T n / 2)) atTop (𝓝 0) := by
  constructor
  · intro h
    have hc := (h.const_sub (normalizedPolarMoment f)).div_const (2 * normalizedPolarMoment f)
    have heq (n : ℕ) : (normalizedPolarMoment f -
        normalizedPolarMoment (subtractCopy f (a n) (T n))) / (2 * normalizedPolarMoment f) =
        copyMixingCoefficient (a n) * Real.cosh (T n / 2) := by
      rw [normalizedPolarMoment_subtractCopy hf hfc hR hs (hT n)]
      field_simp [hP]
      ring
    simpa only [heq, sub_self, zero_div] using hc
  · intro h
    have hc := ((h.const_mul 2).const_sub 1).mul_const (normalizedPolarMoment f)
    simpa only [normalizedPolarMoment_subtractCopy hf hfc hR hs (hT _),
      mul_assoc, mul_zero, sub_zero, one_mul] using hc

theorem normalizedPolarMoment_polarCopy {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (T : ℝ) :
    normalizedPolarMoment (polarCopy f T) = 0 := by
  rw [normalizedPolarMoment, integral_polarCopy_autocorr_cosh hf hfc, zero_div]

/-- A concrete smooth compact source has positive mass and positive polar moment in any radius. -/
theorem exists_smooth_source_positive_polar_moment {r : ℝ} (hr : 0 < r) :
    ∃ f : ℝ → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) f ∧ HasCompactSupport f ∧
      0 < autocorr f 0 ∧ 0 < normalizedPolarMoment f ∧
      ∀ u, r < |u| → f u = 0 := by
  let p : ContDiffBump (0 : ℝ) := ⟨r / 2, r, by positivity, by linarith⟩
  have hp0 : p 0 = 1 := p.one_of_mem_closedBall (by
    simpa only [Metric.mem_closedBall, dist_self] using p.rIn_pos.le)
  have hR : 0 < autocorr (p : ℝ → ℝ) 0 := by
    unfold autocorr
    simp only [add_zero]
    exact (p.continuous.mul p.continuous).integral_pos_of_hasCompactSupport_nonneg_nonzero
      p.hasCompactSupport.mul_right (fun x => mul_self_nonneg (p x)) (x := 0)
      (by rw [hp0]; norm_num)
  have hm (s : ℝ) : 0 < ∫ u, p u * Real.exp (s * u) := by
    apply (p.continuous.mul (by fun_prop)).integral_pos_of_hasCompactSupport_nonneg_nonzero
      p.hasCompactSupport.mul_right (fun u => mul_nonneg p.nonneg (Real.exp_pos _).le) (x := 0)
    change p 0 * Real.exp (s * 0) ≠ 0
    rw [hp0]
    norm_num
  have hp := hm (1 / 2)
  have hn := hm (-(1 / 2))
  simp only [show ∀ u : ℝ, (1 / 2 : ℝ) * u = u / 2 by intro u; ring] at hp
  simp only [show ∀ u : ℝ, (-(1 / 2) : ℝ) * u = -u / 2 by intro u; ring] at hn
  have hwhole := two_mul_integral_autocorr_cosh (f := (p : ℝ → ℝ)) p.contDiff p.hasCompactSupport
  have hhalf : 0 < ∫ x in Ioi 0, autocorr (p : ℝ → ℝ) x * Real.cosh (x / 2) := by
    have hh := mul_pos hp hn
    linarith only [hwhole, hh]
  refine ⟨p, p.contDiff, p.hasCompactSupport, hR, div_pos hhalf hR, ?_⟩
  intro u hu
  apply p.zero_of_le_dist
  simpa only [Real.dist_eq, sub_zero, p] using hu.le

end

end GaloisForLFunctions.BiScaleUncertainty
