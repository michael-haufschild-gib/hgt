import GaloisForLFunctions.HTGeometry.KleinGordonFloquetSpectrum
import Mathlib.Analysis.Normed.Algebra.GelfandFormula

/-!
# Decay from the spectral radius

Statement 315 damps the clock out when the monodromy is a contraction, `‖M‖ < 1`. That is not the
sharp condition: a clock can have `‖M‖ > 1` and still decay, because the norm sees one period while
the fate of the clock is decided by many.

The sharp condition is on the spectral radius, and it is reached through Gelfand's formula:
`‖Mⁿ‖^{1/n} → spectralRadius M`, so a spectral radius below one forces `‖Mⁿ‖ ≤ qⁿ` eventually for
some `q < 1`, hence `‖Mⁿ‖ → 0`. mathlib has Gelfand's formula but not this consequence, so it is
proved here for an arbitrary complex Banach algebra and then applied.

The result is the sharp Floquet decay criterion: **every Floquet multiplier inside the open unit disc
means the clock is damped out**, at every time and not only along the periods.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology ENNReal

/-! ## Powers of an element of small spectral radius -/

section BanachAlgebra

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- **The powers of an element of spectral radius less than one vanish in norm.** Gelfand's formula
gives `‖aⁿ‖^{1/n} → spectralRadius a`, so the powers are eventually dominated by a geometric
sequence. -/
theorem tendsto_norm_pow_zero_of_spectralRadius_lt_one {a : A}
    (ha : spectralRadius ℂ a < 1) : Tendsto (fun n : ℕ => ‖a ^ n‖) atTop (𝓝 0) := by
  set r : ℝ≥0∞ := spectralRadius ℂ a with hrdef
  have hrtop : r ≠ ⊤ := ne_top_of_lt ha
  have hr0 : (0 : ℝ) ≤ r.toReal := ENNReal.toReal_nonneg
  have hrt : r.toReal < 1 := by
    have h1 : r < ENNReal.ofReal 1 := by simpa using ha
    exact (ENNReal.lt_ofReal_iff_toReal_lt hrtop).mp h1
  set q : ℝ := (r.toReal + 1) / 2 with hqdef
  have hq0 : 0 < q := by rw [hqdef]; linarith
  have hq1 : q < 1 := by rw [hqdef]; linarith
  have hrq : r < ENNReal.ofReal q := by
    rw [ENNReal.lt_ofReal_iff_toReal_lt hrtop, hqdef]
    linarith
  have hgel := spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius (A := A) a
  have hev : ∀ᶠ n : ℕ in atTop, ENNReal.ofReal (‖a ^ n‖ ^ (1 / n : ℝ)) < ENNReal.ofReal q :=
    hgel.eventually_lt_const hrq
  have hev2 : ∀ᶠ n : ℕ in atTop, ‖a ^ n‖ ≤ q ^ n := by
    filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
    have hlt : ‖a ^ n‖ ^ (1 / n : ℝ) < q := (ENNReal.ofReal_lt_ofReal_iff hq0).mp hn
    rw [one_div] at hlt
    have hn0 : n ≠ 0 := by omega
    have hbase : (0 : ℝ) ≤ ‖a ^ n‖ ^ ((n : ℝ))⁻¹ := Real.rpow_nonneg (norm_nonneg _) _
    have hkey : ‖a ^ n‖ = (‖a ^ n‖ ^ ((n : ℝ))⁻¹) ^ n :=
      (Real.rpow_inv_natCast_pow (norm_nonneg _) hn0).symm
    rw [hkey]
    gcongr
  have hqlim : Tendsto (fun n : ℕ => q ^ n) atTop (𝓝 0) :=
    _root_.tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hev2 hqlim

end BanachAlgebra

/-! ## The sharp decay criterion -/

section Decay

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

variable {W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b T : ℝ}

/-- **Every multiplier inside the open unit disc damps the clock along the periods.** -/
theorem tendsto_kgFieldStateT_period_zero_of_spectralRadius (hb0 : 0 ≤ b)
    (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hper : ∀ r : ℝ, W (r + T) = W r)
    (hspec : spectralRadius ℂ (kgMonodromy W b hb0 hWb hWs T) < 1)
    (g h : Lp ℂ 2 (volume : Measure E)) :
    Tendsto (fun n : ℕ => kgFieldStateT W g h (n * T)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hpow := tendsto_norm_pow_zero_of_spectralRadius_lt_one hspec
  have hle : ∀ n : ℕ, ‖kgFieldStateT W g h (n * T)‖
      ≤ ‖kgMonodromy W b hb0 hWb hWs T ^ n‖ * ‖kgPair E (g, h)‖ := by
    intro n
    rw [kgFieldStateT_monodromy_pow hb0 hWb hWs hper g h n]
    exact (kgMonodromy W b hb0 hWb hWs T ^ n).le_opNorm _
  have hbound : Tendsto (fun n : ℕ => ‖kgMonodromy W b hb0 hWb hWs T ^ n‖
      * ‖kgPair E (g, h)‖) atTop (𝓝 0) := by
    simpa using hpow.mul_const (‖kgPair E (g, h)‖)
  exact squeeze_zero (fun _ => norm_nonneg _) hle hbound

set_option maxHeartbeats 1000000 in
/-- **The sharp Floquet decay criterion.** A spectral radius below one damps the clock out at every
time, not only along the periods. -/
theorem tendsto_kgFieldStateT_zero_of_spectralRadius (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hper : ∀ r : ℝ, W (r + T) = W r) (hT : 0 < T)
    (hspec : spectralRadius ℂ (kgMonodromy W b hb0 hWb hWs T) < 1)
    (g h : Lp ℂ 2 (volume : Measure E)) :
    Tendsto (fun t : ℝ => kgFieldStateT W g h t) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hpow := tendsto_norm_pow_zero_of_spectralRadius_lt_one hspec
  have hle : ∀ᶠ t : ℝ in atTop, ‖kgFieldStateT W g h t‖
      ≤ ‖kgMonodromy W b hb0 hWb hWs T ^ (⌊t / T⌋₊)‖ * ‖kgPair E (g, h)‖
        * Real.exp (b * T) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    refine (norm_kgFieldStateT_le_floor hb0 hWb hWs hper hT g h ht).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    rw [kgFieldStateT_monodromy_pow hb0 hWb hWs hper g h ⌊t / T⌋₊]
    exact (kgMonodromy W b hb0 hWb hWs T ^ ⌊t / T⌋₊).le_opNorm _
  have hfloor : Tendsto (fun t : ℝ => ⌊t / T⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (Filter.Tendsto.atTop_div_const hT tendsto_id)
  have hcomp : Tendsto (fun t : ℝ => ‖kgMonodromy W b hb0 hWb hWs T ^ (⌊t / T⌋₊)‖)
      atTop (𝓝 0) := hpow.comp hfloor
  have hbound : Tendsto (fun t : ℝ => ‖kgMonodromy W b hb0 hWb hWs T ^ (⌊t / T⌋₊)‖
      * ‖kgPair E (g, h)‖ * Real.exp (b * T)) atTop (𝓝 0) := by
    simpa using (hcomp.mul_const (‖kgPair E (g, h)‖)).mul_const (Real.exp (b * T))
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hle hbound

end Decay

end GaloisForLFunctions.HTGeometry
