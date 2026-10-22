import GaloisForLFunctions.RHTower.CCM.CCMGuinandWeilActualExponentialAbelShift
import GaloisForLFunctions.RHTower.CCM.CCMHardyCriticalMellinNonextension
import GaloisForLFunctions.RHTower.CCM.CCMFUSuzukiSignedWindowMixture

open Complex Filter Set MeasureTheory Topology
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

def ccmThirdGradeExponentialClockWeightClamped (b a h : ℝ) : ℝ :=
  Real.exp (a * max b h) * (32 / (max b h) ^ (3 : ℕ))

def ccmThirdGradeExponentialClockCumulativeClamped (b a H : ℝ) : ℝ :=
  ccmGuinandWeilPrimePolarWeightedWindow b H
    (ccmThirdGradeExponentialClockWeightClamped b a)

theorem measurable_ccmThirdGradeExponentialClockCumulativeClamped
    {b a : ℝ} (hb : 0 < b) :
    Measurable (ccmThirdGradeExponentialClockCumulativeClamped b a) := by
  let F := ccmThirdGradeExponentialClockWeightClamped b a
  let B : ℕ → ℝ := fun m =>
    ∑ k ∈ Finset.Icc 2 m,
      if b < Real.log k then criticalMellinAtomWeight k * F (Real.log k) else 0
  have hB : Measurable B := measurable_of_countable B
  have hfloor : Measurable (fun H : ℝ => ⌊Real.exp H⌋₊) :=
    Real.measurable_exp.nat_floor
  have hprime : Measurable (fun H : ℝ => B ⌊Real.exp H⌋₊) :=
    hB.comp hfloor
  have hm : Continuous (fun h : ℝ => max b h) :=
    continuous_const.max continuous_id
  have hmne (h : ℝ) : max b h ^ (3 : ℕ) ≠ 0 :=
    pow_ne_zero 3 (ne_of_gt (hb.trans_le (le_max_left b h)))
  have hF : Continuous F := by
    dsimp only [F, ccmThirdGradeExponentialClockWeightClamped]
    exact (Real.continuous_exp.comp (continuous_const.mul hm)).mul
      (continuous_const.div (hm.pow 3) hmne)
  have hpolar : Continuous (fun h : ℝ => F h * (2 * Real.cosh (h / 2))) := by
    exact hF.mul (continuous_const.mul
      (Real.continuous_cosh.comp (continuous_id.div_const 2)))
  have hprim : Continuous (fun H : ℝ =>
      ∫ h in b..H, F h * (2 * Real.cosh (h / 2))) :=
    intervalIntegral.continuous_primitive
      (fun x y => hpolar.intervalIntegrable x y) b
  change Measurable (fun H : ℝ => B ⌊Real.exp H⌋₊ -
    ∫ h in b..H, F h * (2 * Real.cosh (h / 2)))
  exact hprime.sub hprim.measurable

theorem ccmThirdGradeExponentialClockCumulativeClamped_eq_literal
    {b H : ℝ} (hbH : b ≤ H) (a : ℝ) :
    ccmThirdGradeExponentialClockCumulativeClamped b a H =
      ccmThirdGradeExponentialClockCumulative b a H := by
  apply ccmGuinandWeilPrimePolarWeightedWindow_congr_on hbH
  · intro k hk hbk
    simp only [ccmThirdGradeExponentialClockWeightClamped,
      max_eq_right hbk.le, ccmGuinandWeilThirdGradeWeight]
  · intro h hh
    simp only [ccmThirdGradeExponentialClockWeightClamped,
      max_eq_right hh.1, ccmGuinandWeilThirdGradeWeight]

/-- Any positive fixed exponential clock makes the actual completed third-grade
prime-minus-polar cumulative source unbounded. -/
theorem not_bounded_ccmThirdGradeExponentialClockCumulative
    {b a : ℝ} (hb : 0 < b) (ha : 0 < a) :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ H : ℝ, b < H →
      |ccmThirdGradeExponentialClockCumulative b a H| ≤ C := by
  rintro ⟨C, hC, hbound⟩
  let q := ccmThirdGradeExponentialClockCumulativeClamped b a
  let G : ℂ → ℂ := ccmAbelCumulativeSourceContinuation q b
  let G₀ : ℂ → ℂ := ccmAbelCumulativeSourceContinuation
    (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b
  let F : ℂ → ℂ := fun z => G (z + (a : ℂ))
  let A : ℂ → ℂ := fun s =>
    (1 / 32 : ℂ) * iteratedDeriv 3 F (s + 1 / 2) +
      ccmGuinandWeilThirdGradeWallHead b s
  have hqmeas : Measurable q :=
    measurable_ccmThirdGradeExponentialClockCumulativeClamped hb
  have hqbound : ∀ H : ℝ, b < H → |q H| ≤ C := by
    intro H hH
    dsimp only [q]
    rw [ccmThirdGradeExponentialClockCumulativeClamped_eq_literal hH.le a]
    exact hbound H hH
  have hG : AnalyticOnNhd ℂ G {u : ℂ | 0 < u.re} :=
    analyticOnNhd_ccmAbelCumulativeSourceContinuation_of_bounded
      hqmeas hb hC hqbound
  have hF : AnalyticOnNhd ℂ F {z : ℂ | -a < z.re} := by
    intro z hz
    have hza : 0 < (z + (a : ℂ)).re := by
      change -a < z.re at hz
      norm_num [Complex.add_re]
      linarith
    have hshift : AnalyticAt ℂ (fun z : ℂ => z + (a : ℂ)) z := by
      fun_prop
    exact AnalyticAt.comp (f := fun w : ℂ => w + (a : ℂ))
      (hG (z + (a : ℂ)) hza) hshift
  have hF3 : AnalyticOnNhd ℂ (iteratedDeriv 3 F) {z : ℂ | -a < z.re} := by
    simpa only [iteratedDeriv_eq_iterate] using hF.iterated_deriv 3
  have hA : AnalyticOnNhd ℂ A {s : ℂ | -1 / 2 - a < s.re} := by
    intro s hs
    have hshift : AnalyticAt ℂ (fun z : ℂ => z + 1 / 2) s := by fun_prop
    have hza : -a < (s + 1 / 2).re := by
      change -1 / 2 - a < s.re at hs
      norm_num [Complex.add_re]
      linarith
    have hcomp := AnalyticAt.comp (f := fun z : ℂ => z + 1 / 2)
      (hF3 (s + 1 / 2) hza) hshift
    have hwall := analyticOnNhd_ccmGuinandWeilThirdGradeWallHead hb
      s (Set.mem_univ _)
    change AnalyticAt ℂ
      (fun z => (1 / 32 : ℂ) * iteratedDeriv 3 F (z + 1 / 2) +
        ccmGuinandWeilThirdGradeWallHead b z) s
    exact (analyticAt_const.mul hcomp).add hwall
  have hclock (z : ℂ) (hz : 1 < z.re) : F z = G₀ z := by
    have hu : 1 + a < (z + (a : ℂ)).re := by
      norm_num [Complex.add_re]
      linarith
    have hraw := ccmThirdGradeExponentialClock_abel_shift hb ha.le hu
    have hclamp : G (z + (a : ℂ)) =
        ccmAbelCumulativeSourceContinuation
          (ccmThirdGradeExponentialClockCumulative b a) b (z + (a : ℂ)) := by
      dsimp only [G, ccmAbelCumulativeSourceContinuation, ccmAbelLaplaceTail]
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioi
      intro H hH
      simp only [q, ccmThirdGradeExponentialClockCumulativeClamped_eq_literal hH.le a]
    dsimp only [F, G₀]
    rw [hclamp, hraw]
    congr 1
    ring
  have hAsafe (s : ℂ) (hs : 3 / 2 < s.re) :
      A s = regularizedCriticalMellinDefect s := by
    have hu : 1 < (s + 1 / 2).re := by
      norm_num [Complex.add_re]
      linarith
    have hevent : F =ᶠ[𝓝 (s + 1 / 2)] G₀ := by
      have hopen : IsOpen {z : ℂ | 1 < z.re} :=
        isOpen_lt continuous_const Complex.continuous_re
      filter_upwards [hopen.mem_nhds hu] with z hz
      exact hclock z hz
    have hder : iteratedDeriv 3 F (s + 1 / 2) =
        iteratedDeriv 3 G₀ (s + 1 / 2) := by
      exact hevent.iteratedDeriv_eq 3
    dsimp only [A]
    rw [hder]
    exact ccmGuinandWeilThirdGradeAbelCriticalMellinExtension_eq_regularized_safe hb hs
  have hagree : ∀ s : ℂ, 0 < s.re →
      A s = regularizedCriticalMellinDefect s := by
    let U : Set ℂ := {s : ℂ | 0 < s.re}
    have hUpre : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
    have hAU : AnalyticOnNhd ℂ A U := by
      intro s hs
      apply hA
      change -1 / 2 - a < s.re
      change 0 < s.re at hs
      linarith
    have hDU : AnalyticOnNhd ℂ regularizedCriticalMellinDefect U :=
      analyticOnNhd_regularizedCriticalMellinDefect_rightHalfPlane
    have htwo : (2 : ℂ) ∈ U := by norm_num [U]
    have hevent : A =ᶠ[𝓝 (2 : ℂ)] regularizedCriticalMellinDefect := by
      have hopen : IsOpen {s : ℂ | 3 / 2 < s.re} :=
        isOpen_lt continuous_const Complex.continuous_re
      have htwoSafe : (2 : ℂ) ∈ {s : ℂ | 3 / 2 < s.re} := by norm_num
      filter_upwards [hopen.mem_nhds htwoSafe] with s hs
      exact hAsafe s hs
    have heq := hAU.eqOn_of_preconnected_of_eventuallyEq hDU hUpre htwo hevent
    intro s hs
    exact heq hs
  let eps : ℝ := min a (1 / 4)
  have hepspos : 0 < eps := lt_min ha (by norm_num)
  have hepsa : eps ≤ a := min_le_left a (1 / 4)
  have hepssmall : eps ≤ 1 / 4 := min_le_right a (1 / 4)
  let c : ℝ := -1 / 2 - eps
  have hcLow : -1 < c := by dsimp [c]; linarith
  have hcHigh : c < -1 / 2 := by dsimp [c]; linarith
  have hAc : AnalyticOnNhd ℂ A {s : ℂ | c < s.re} := by
    intro s hs
    apply hA
    change -1 / 2 - a < s.re
    change c < s.re at hs
    dsimp [c] at hs
    linarith
  exact no_analytic_extension_regularizedCriticalMellinDefect_pastHardy
    hcLow hcHigh A hAc hagree

end

end RHTower
