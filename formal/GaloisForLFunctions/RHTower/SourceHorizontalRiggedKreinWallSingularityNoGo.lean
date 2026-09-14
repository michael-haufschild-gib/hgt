import GaloisForLFunctions.RHTower.SourceHorizontalRiggedKreinFundamentalSymmetry

/-!
# Critical-wall singularity of the source-selected Krein polarization

The canonical source-selected fundamental symmetry acts by opposite signs on the two open
half-strips.  Its action on the two-prime time axis is exactly `-1` on the left and `+1` on the
right, while its canonical critical-wall value is zero.  Consequently even the weakest regular
completion that retains this one vector cannot join the two chambers continuously.

This is stronger than failure of the canonical wall value: no alternative value on the wall can
repair continuity while preserving both chamber actions.  A completion retaining the canonical
source polarization must therefore be genuinely wall-singular or sheet-changing.
-/

open Complex Real Set Filter Topology

namespace RHTower

noncomputable section

open PreDivisorReflectionDefectStabilization

private theorem timeAxis_ne_zero : preDivisorRiggedPrimeTimeAxis ≠ 0 := by
  intro hzero
  have hpq : nthPrimePoint 0 ≠ nthPrimePoint 1 :=
    preDivisorRiggedNthPrimePoint_injective.ne (by omega)
  have hcoord := congrArg
    (fun a : DeningerHeightKothe =>
      ((a : DeningerPrimeLattice → ℂ)
        (preDivisorRiggedPrimeAxis (nthPrimePoint 0)))) hzero
  simp [preDivisorRiggedPrimeTimeAxis, hpq] at hcoord

private theorem timeReflection_timeAxis_of_pairing_ne
    (s : ℂ)
    (haxis : preDivisorRiggedPrimeWittPairing s preDivisorRiggedPrimeTimeAxis
      preDivisorRiggedPrimeTimeAxis ≠ 0) :
    preDivisorRiggedPrimeTimeReflection s preDivisorRiggedPrimeTimeAxis =
      -preDivisorRiggedPrimeTimeAxis := by
  rw [preDivisorRiggedPrimeTimeReflection, div_self haxis]
  module

private theorem fundamentalSymmetry_timeAxis_left
    (s : ℂ) (hs0 : 0 < s.re) (hleft : s.re < 1 / 2) :
    preDivisorRiggedPrimeFundamentalSymmetry s preDivisorRiggedPrimeTimeAxis =
      -preDivisorRiggedPrimeTimeAxis := by
  rw [preDivisorRiggedPrimeFundamentalSymmetry_eq_timeReflection_left s hleft,
    timeReflection_timeAxis_of_pairing_ne s
      (preDivisorRiggedPrimeTimeAxis_negative_left s hs0 hleft).ne]

private theorem fundamentalSymmetry_timeAxis_right
    (s : ℂ) (hright : 1 / 2 < s.re) (hs1 : s.re < 1) :
    preDivisorRiggedPrimeFundamentalSymmetry s preDivisorRiggedPrimeTimeAxis =
      preDivisorRiggedPrimeTimeAxis := by
  rw [preDivisorRiggedPrimeFundamentalSymmetry_eq_neg_timeReflection_right s hright,
    timeReflection_timeAxis_of_pairing_ne s
      (preDivisorRiggedPrimeTimeAxis_positive_right s hright hs1).ne']
  module

private theorem fundamentalSymmetry_wall
    (s : ℂ) (hs : s.re = 1 / 2) (a : DeningerHeightKothe) :
    preDivisorRiggedPrimeFundamentalSymmetry s a = 0 := by
  have ho : preDivisorOrientation s = 0 := by
    rw [preDivisorOrientation, preDivisorTailLog, hs]
    norm_num
  rw [preDivisorRiggedPrimeFundamentalSymmetry, ho, zero_smul]

/-- Exact three-chamber action on the canonical two-prime time axis. -/
theorem preDivisorRiggedPrimeFundamentalSymmetry_timeAxis_chambers
    (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    preDivisorRiggedPrimeFundamentalSymmetry s preDivisorRiggedPrimeTimeAxis =
      if s.re < 1 / 2 then -preDivisorRiggedPrimeTimeAxis
      else if 1 / 2 < s.re then preDivisorRiggedPrimeTimeAxis else 0 := by
  by_cases hleft : s.re < 1 / 2
  · rw [if_pos hleft]
    exact fundamentalSymmetry_timeAxis_left s hs0 hleft
  rw [if_neg hleft]
  by_cases hright : 1 / 2 < s.re
  · rw [if_pos hright]
    exact fundamentalSymmetry_timeAxis_right s hright hs1
  rw [if_neg hright]
  exact fundamentalSymmetry_wall s (le_antisymm (not_lt.mp hright) (not_lt.mp hleft))
    preDivisorRiggedPrimeTimeAxis

private def wallStep (n : ℕ) : ℂ := ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)

private theorem wallStep_tendsto : Tendsto wallStep atTop (𝓝 0) := by
  have h := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  change Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ))
    atTop (𝓝 (0 : ℂ)) at h
  exact h

private theorem wallStep_re_pos (n : ℕ) : 0 < (wallStep n).re := by
  simp only [wallStep, Complex.ofReal_re]
  exact one_div_pos.mpr (by positivity)

private theorem wallStep_re_le_quarter {n : ℕ} (hn : 3 ≤ n) :
    (wallStep n).re ≤ 1 / 4 := by
  simp only [wallStep, Complex.ofReal_re]
  apply one_div_le_one_div_of_le (by norm_num)
  exact_mod_cast Nat.add_le_add_right hn 1

/--
A path agreeing with both canonical open-strip chambers cannot be continuous at a critical-wall
point.  The obstruction is already visible on one fixed nonzero vector.
-/
theorem no_continuousAt_fundamentalSymmetry_timeAxis_extension
    (s : ℂ) (hs : s.re = 1 / 2) (F : ℂ → DeningerHeightKothe)
    (hleft : ∀ z : ℂ, 0 < z.re → z.re < 1 / 2 →
      F z = preDivisorRiggedPrimeFundamentalSymmetry z preDivisorRiggedPrimeTimeAxis)
    (hright : ∀ z : ℂ, 1 / 2 < z.re → z.re < 1 →
      F z = preDivisorRiggedPrimeFundamentalSymmetry z preDivisorRiggedPrimeTimeAxis) :
    ¬ ContinuousAt F s := by
  intro hcont
  let xl : ℕ → ℂ := fun n => s - wallStep n
  let xr : ℕ → ℂ := fun n => s + wallStep n
  have hxl : Tendsto xl atTop (𝓝 s) := by
    simpa [xl] using wallStep_tendsto.const_sub s
  have hxr : Tendsto xr atTop (𝓝 s) := by
    simpa [xr] using (tendsto_const_nhds.add wallStep_tendsto :
      Tendsto (fun n : ℕ => s + wallStep n) atTop (𝓝 (s + 0)))
  have hleftEventually :
      (fun n : ℕ => F (xl n)) =ᶠ[atTop]
        (fun _ : ℕ => -preDivisorRiggedPrimeTimeAxis) := by
    filter_upwards [eventually_ge_atTop (3 : ℕ)] with n hn
    have hxl0 : 0 < (xl n).re := by
      simp only [xl, Complex.sub_re, hs]
      have hbound := wallStep_re_le_quarter hn
      norm_num at hbound ⊢
      linarith
    have hxll : (xl n).re < 1 / 2 := by
      simp only [xl, Complex.sub_re, hs]
      linarith [wallStep_re_pos n]
    rw [hleft (xl n) hxl0 hxll]
    exact fundamentalSymmetry_timeAxis_left (xl n) hxl0 hxll
  have hrightEventually :
      (fun n : ℕ => F (xr n)) =ᶠ[atTop]
        (fun _ : ℕ => preDivisorRiggedPrimeTimeAxis) := by
    filter_upwards [eventually_ge_atTop (3 : ℕ)] with n hn
    have hxrr : 1 / 2 < (xr n).re := by
      simp only [xr, Complex.add_re, hs]
      linarith [wallStep_re_pos n]
    have hxr1 : (xr n).re < 1 := by
      simp only [xr, Complex.add_re, hs]
      have hbound := wallStep_re_le_quarter hn
      norm_num at hbound ⊢
      linarith
    rw [hright (xr n) hxrr hxr1]
    exact fundamentalSymmetry_timeAxis_right (xr n) hxrr hxr1
  have hminus : -preDivisorRiggedPrimeTimeAxis = F s :=
    tendsto_nhds_unique (tendsto_const_nhds.congr' hleftEventually.symm)
      (hcont.tendsto.comp hxl)
  have hplus : preDivisorRiggedPrimeTimeAxis = F s :=
    tendsto_nhds_unique (tendsto_const_nhds.congr' hrightEventually.symm)
      (hcont.tendsto.comp hxr)
  have hneg : -preDivisorRiggedPrimeTimeAxis = preDivisorRiggedPrimeTimeAxis :=
    hminus.trans hplus.symm
  have hdouble : preDivisorRiggedPrimeTimeAxis + preDivisorRiggedPrimeTimeAxis = 0 :=
    (congrArg (fun a => a + preDivisorRiggedPrimeTimeAxis) hneg).symm.trans
      (neg_add_cancel preDivisorRiggedPrimeTimeAxis)
  apply timeAxis_ne_zero
  calc
    preDivisorRiggedPrimeTimeAxis =
        (1 / 2 : ℂ) •
          (preDivisorRiggedPrimeTimeAxis + preDivisorRiggedPrimeTimeAxis) := by module
    _ = 0 := by rw [hdouble]; simp

/-- Wall-regular global continuation of the chamberwise source-selected polarization. -/
def SourceHorizontalWallRegularRiggedKreinCompletion : Prop :=
  ∃ F : ℂ → DeningerHeightKothe,
    (∀ s : ℂ, s.re = 1 / 2 → ContinuousAt F s) ∧
    (∀ s : ℂ, 0 < s.re → s.re < 1 / 2 →
      F s = preDivisorRiggedPrimeFundamentalSymmetry s preDivisorRiggedPrimeTimeAxis) ∧
    (∀ s : ℂ, 1 / 2 < s.re → s.re < 1 →
      F s = preDivisorRiggedPrimeFundamentalSymmetry s preDivisorRiggedPrimeTimeAxis)

/-- No regular global completion can join the two canonical Krein chambers. -/
theorem sourceHorizontalWallRegularRiggedKreinCompletionRouteKilled :
    ¬ SourceHorizontalWallRegularRiggedKreinCompletion := by
  rintro ⟨F, hwall, hleft, hright⟩
  exact no_continuousAt_fundamentalSymmetry_timeAxis_extension
    ((1 / 2 : ℝ) : ℂ) (by norm_num) F hleft hright
      (hwall ((1 / 2 : ℝ) : ℂ) (by norm_num))

end

end RHTower
