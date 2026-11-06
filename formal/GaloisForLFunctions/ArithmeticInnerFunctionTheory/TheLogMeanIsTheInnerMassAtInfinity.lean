import GaloisForLFunctions.ArithmeticInnerFunctionTheory.TheArithmeticCarlesonMeasure
import GaloisForLFunctions.RHTower.CompletePositiveKolchinFreeRiemannResolution

/-!
# The log-mean of `ζ` is the inner mass at infinity

At width `x` the Poisson kernel is an average over heights at scale `x`. So the Poisson mean of `log |ζ|` on the line is an Abel log-mean, and it differs from the inner field by a term tending to `0` (`tendsto_log_correction`).

**Theorem** (`tendsto_poisson_log_iff`, `tendsto_poisson_log_iff_depthDensity`). As `x → ∞`,

`∫ log |ζ(½ + iτ)| P_{½+x+it}(τ) dτ → 0  ⇔  I(½ + x + it) → 0  ⇔  Σ_{|γ−t|≤T} m_ρ b_ρ = o(T)`.

So the Abel log-mean of `ζ` on the line tends to `0` iff the zeros have depth density zero. This is one statement on three sides: analysis on the line, potential theory on the half-plane, and a count of zeros. It holds under RH, and for an Euler column it fails with the value `log(|c|/√p)`.
-/

open Complex Filter Topology MeasureTheory

namespace GaloisForLFunctions.ArithmeticInnerFunctionTheory

open _root_.RHTower

noncomputable section

/-- The correction between the inner field and the Poisson log-mean tends to `0`. -/
theorem tendsto_log_correction (t : ℝ) :
    Tendsto (fun x : ℝ => Real.log ‖centre x t‖ - Real.log ‖zetaEntire (centre x t)‖) atTop (𝓝 0) := by
  have hre : Tendsto (fun x : ℝ => (centre x t).re - 1) atTop atTop := by
    simp only [centre_re]
    refine tendsto_atTop_add_const_right _ (-1 + 1 / 2) tendsto_id |>.congr fun x => ?_
    simp only [id]
    ring
  -- `ζ → 1`
  have hz : Tendsto (fun x : ℝ => riemannZeta (centre x t)) atTop (𝓝 1) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h1 : Tendsto (fun x : ℝ => 1 / ((centre x t).re - 1)) atTop (𝓝 0) := hre.const_div_atTop 1
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h1
    filter_upwards [hre.eventually_gt_atTop 0] with x hx
    exact norm_riemannZeta_sub_one_le (by linarith)
  have hzlog : Tendsto (fun x : ℝ => Real.log ‖riemannZeta (centre x t)‖) atTop (𝓝 0) := by
    have := (hz.norm).log (by simp)
    simpa using this
  -- `|w|/|w − 1| → 1`
  have hn : Tendsto (fun x : ℝ => ‖centre x t - 1‖) atTop atTop :=
    tendsto_atTop_mono (fun x => by
      have h := Complex.abs_re_le_norm (centre x t - 1)
      have e : (centre x t - 1).re = (centre x t).re - 1 := by simp
      rw [e] at h
      exact (le_abs_self _).trans h) hre
  have hratio : Tendsto (fun x : ℝ => ‖centre x t‖ / ‖centre x t - 1‖) atTop (𝓝 1) := by
    have hinv : Tendsto (fun x : ℝ => 1 / ‖centre x t - 1‖) atTop (𝓝 0) := hn.const_div_atTop 1
    have hlo : Tendsto (fun x : ℝ => 1 - 1 / ‖centre x t - 1‖) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub hinv
    have hhi : Tendsto (fun x : ℝ => 1 + 1 / ‖centre x t - 1‖) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add hinv
    rw [sub_zero] at hlo
    rw [add_zero] at hhi
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
    · filter_upwards [hn.eventually_gt_atTop 0] with x hx
      rw [le_div_iff₀ hx]
      have h := norm_sub_norm_le (centre x t - 1) (-1)
      simp only [sub_neg_eq_add, sub_add_cancel, norm_neg, norm_one] at h
      have e : (1 - 1 / ‖centre x t - 1‖) * ‖centre x t - 1‖ = ‖centre x t - 1‖ - 1 := by
        field_simp
      linarith
    · filter_upwards [hn.eventually_gt_atTop 0] with x hx
      rw [div_le_iff₀ hx]
      have h : ‖centre x t‖ ≤ ‖centre x t - 1‖ + 1 := by
        have := norm_add_le (centre x t - 1) 1
        simpa using this
      have e : (1 + 1 / ‖centre x t - 1‖) * ‖centre x t - 1‖ = ‖centre x t - 1‖ + 1 := by
        field_simp
      linarith
  have hrlog : Tendsto (fun x : ℝ => Real.log (‖centre x t‖ / ‖centre x t - 1‖)) atTop (𝓝 0) := by
    have := hratio.log (by norm_num)
    simpa using this
  have hcomb := hrlog.sub hzlog
  rw [sub_zero] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [hre.eventually_gt_atTop 0] with x hx
  have hne1 : centre x t ≠ 1 := fun h => by
    rw [h] at hx
    simp at hx
  have hz0 : riemannZeta (centre x t) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by linarith)
  have hw0 : centre x t ≠ 0 := fun h => by
    rw [h] at hx
    simp at hx
    linarith
  have hsub : centre x t - 1 ≠ 0 := sub_ne_zero.mpr hne1
  rw [zetaEntire_eq hne1, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hsub) (norm_ne_zero_iff.mpr hz0),
    Real.log_div (norm_ne_zero_iff.mpr hw0) (norm_ne_zero_iff.mpr hsub)]
  ring

/-- **The Abel log-mean of `ζ` on the line is the inner mass at infinity.** -/
theorem tendsto_poisson_log_iff (t : ℝ) :
    Tendsto (fun x : ℝ => ∫ τ : ℝ, Real.log ‖riemannZeta (1 / 2 + τ * I)‖ *
      halfPlanePoissonKernel (centre x t) τ) atTop (𝓝 0) ↔
      Tendsto (fun x : ℝ => innerField (centre x t)) atTop (𝓝 0) := by
  have hc := tendsto_log_correction t
  constructor
  · intro h
    have := h.add hc
    rw [add_zero] at this
    refine this.congr fun x => ?_
    rw [innerField]
    ring
  · intro h
    have := h.sub hc
    rw [sub_zero] at this
    refine this.congr fun x => ?_
    rw [innerField]
    ring

/-- **Three readings of one statement.** The Abel log-mean of `ζ` tends to `0` iff the zeros have depth density zero. -/
theorem tendsto_poisson_log_iff_depthDensity (t : ℝ) :
    Tendsto (fun x : ℝ => ∫ τ : ℝ, Real.log ‖riemannZeta (1 / 2 + τ * I)‖ *
      halfPlanePoissonKernel (centre x t) τ) atTop (𝓝 0) ↔
      ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ Z : Finset ZetaRightZero,
        (∀ ρ ∈ Z, |(ρ : ℂ).im - t| ≤ T) → ∑ ρ ∈ Z, zeroMult ρ * depth ρ ≤ ε * T :=
  (tendsto_poisson_log_iff t).trans (tendsto_innerField_iff_depthDensity t)

end

end GaloisForLFunctions.ArithmeticInnerFunctionTheory
