import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.VectorMeasure.SetIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Tilted weights concentrate at the top of their support

Let `g ≥ 0` be integrable on `[−1, 1]` with `1` in its support, in the sense that every window
`[1 − ε, 1]` carries positive mass.  Tilting by `e^{αc}` and testing against `cos(πα)`, which is
negative on `(1/2, 1]`, gives an eventually negative integral:

`∫_{−1}^{1} g(α) e^{αc} cos(πα) dα < 0`  for all large `c`.

The mechanism: the mass on `[7/8, 1]` grows like `e^{7c/8}` while everything on `[−1, 3/4]` is at most
`e^{3c/4} ∫ g`.  This is the obstruction to reading zero multiplicities from a bandwidth-one pair
statistic: any kernel `r ≥ 0` with `supp r̂ ⊆ [−1, 1]` has `Re r(π − ic) < 0` for large `c`, so
off-line pairs at one mean spacing and fixed positive displacement enter the pair form negatively.
-/

open MeasureTheory Set Filter

namespace GaloisForLFunctions.HTGeometry

/-- `cos(πα) ≤ −1/2` for `α ∈ [3/4, 1]`. -/
theorem cos_pi_mul_le_neg_half {α : ℝ} (hα : 3 / 4 ≤ α) (hα1 : α ≤ 1) :
    Real.cos (Real.pi * α) ≤ -(1 / 2) := by
  have hpi := Real.pi_pos
  have h1 : Real.cos (Real.pi * α) ≤ Real.cos (Real.pi * (3 / 4)) := by
    apply Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by nlinarith) (by nlinarith)
  have h2 : Real.cos (Real.pi * (3 / 4)) = -(Real.sqrt 2 / 2) := by
    rw [show Real.pi * (3 / 4) = Real.pi - Real.pi / 4 by ring, Real.cos_pi_sub, Real.cos_pi_div_four]
  have h3 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  linarith

/-- **Top concentration of tilted weights.**  For `g ≥ 0` integrable on `[−1,1]` whose every top
window `[1−ε, 1]` has positive mass, `∫_{−1}^{1} g(α) e^{αc} cos(πα) dα < 0` for all large `c`. -/
theorem eventually_integral_tilt_cos_neg {g : ℝ → ℝ} (hg : IntegrableOn g (Icc (-1 : ℝ) 1))
    (hg0 : ∀ α ∈ Icc (-1 : ℝ) 1, 0 ≤ g α)
    (htop : ∀ ε : ℝ, 0 < ε → 0 < ∫ α in Icc (1 - ε) 1, g α) :
    ∀ᶠ c : ℝ in atTop,
      ∫ α in Icc (-1 : ℝ) 1, g α * Real.exp (α * c) * Real.cos (Real.pi * α) < 0 := by
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = ∫ α in Icc (-1 : ℝ) 1, g α := ⟨_, rfl⟩
  obtain ⟨m, hmdef⟩ : ∃ m : ℝ, m = ∫ α in Icc (7 / 8 : ℝ) 1, g α := ⟨_, rfl⟩
  have hm : 0 < m := by
    have := htop (1 / 8) (by norm_num)
    rw [show (1 : ℝ) - 1 / 8 = 7 / 8 by norm_num] at this
    rw [hmdef]; exact this
  have hM0 : 0 ≤ M := by rw [hMdef]; exact setIntegral_nonneg measurableSet_Icc hg0
  have hlim : Tendsto (fun c : ℝ => Real.exp (c / 8)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.atTop_div_const (by norm_num))
  filter_upwards [hlim.eventually_gt_atTop (2 * M / m), eventually_ge_atTop (0 : ℝ)] with c hc hc0
  -- integrability
  have hexpc : ContinuousOn (fun α : ℝ => Real.exp (α * c)) (Icc (-1 : ℝ) 1) :=
    (Real.continuous_exp.comp (continuous_id.mul continuous_const)).continuousOn
  have hge : IntegrableOn (fun α : ℝ => g α * Real.exp (α * c)) (Icc (-1 : ℝ) 1) :=
    hg.mul_continuousOn hexpc isCompact_Icc
  have hint : IntegrableOn (fun α : ℝ => g α * Real.exp (α * c) * Real.cos (Real.pi * α))
      (Icc (-1 : ℝ) 1) :=
    hge.mul_continuousOn (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn
      isCompact_Icc
  have hsub1 : Icc (-1 : ℝ) (3 / 4) ⊆ Icc (-1 : ℝ) 1 := Icc_subset_Icc le_rfl (by norm_num)
  have hsub2 : Ioc (3 / 4 : ℝ) 1 ⊆ Icc (-1 : ℝ) 1 :=
    Ioc_subset_Icc_self.trans (Icc_subset_Icc (by norm_num) le_rfl)
  have hsub3 : Icc (7 / 8 : ℝ) 1 ⊆ Ioc (3 / 4 : ℝ) 1 := fun α hα => ⟨by linarith [hα.1], hα.2⟩
  -- split the integral at `3/4`
  have hsplit : ∫ α in Icc (-1 : ℝ) 1, g α * Real.exp (α * c) * Real.cos (Real.pi * α)
      = (∫ α in Icc (-1 : ℝ) (3 / 4), g α * Real.exp (α * c) * Real.cos (Real.pi * α))
        + ∫ α in Ioc (3 / 4 : ℝ) 1, g α * Real.exp (α * c) * Real.cos (Real.pi * α) := by
    rw [← Icc_union_Ioc_eq_Icc (by norm_num : (-1 : ℝ) ≤ 3 / 4) (by norm_num : (3 / 4 : ℝ) ≤ 1)]
    refine setIntegral_union ?_ measurableSet_Ioc (hint.mono_set hsub1) (hint.mono_set hsub2)
    rw [Set.disjoint_left]
    intro x hx hx'
    exact absurd hx'.1 (not_lt.mpr hx.2)
  -- the lower piece is at most `e^{3c/4} M`
  have hI1 : (∫ α in Icc (-1 : ℝ) (3 / 4), g α * Real.exp (α * c) * Real.cos (Real.pi * α))
      ≤ Real.exp (3 / 4 * c) * M := by
    have hle : (∫ α in Icc (-1 : ℝ) (3 / 4), g α * Real.exp (α * c) * Real.cos (Real.pi * α))
        ≤ ∫ α in Icc (-1 : ℝ) (3 / 4), Real.exp (3 / 4 * c) * g α := by
      refine setIntegral_mono_on (hint.mono_set hsub1) ((hg.mono_set hsub1).const_mul _)
        measurableSet_Icc ?_
      intro α hα
      have h0 := hg0 α (hsub1 hα)
      have hexp : Real.exp (α * c) ≤ Real.exp (3 / 4 * c) :=
        Real.exp_le_exp.mpr (by nlinarith [hα.2])
      have hcos : Real.cos (Real.pi * α) ≤ 1 := Real.cos_le_one _
      have hge0 : 0 ≤ g α * Real.exp (α * c) := mul_nonneg h0 (Real.exp_pos _).le
      calc g α * Real.exp (α * c) * Real.cos (Real.pi * α)
          ≤ g α * Real.exp (α * c) * 1 := mul_le_mul_of_nonneg_left hcos hge0
        _ = g α * Real.exp (α * c) := by ring
        _ ≤ g α * Real.exp (3 / 4 * c) := mul_le_mul_of_nonneg_left hexp h0
        _ = Real.exp (3 / 4 * c) * g α := by ring
    rw [integral_const_mul] at hle
    have hmass : ∫ α in Icc (-1 : ℝ) (3 / 4), g α ≤ M := by
      rw [hMdef]
      exact setIntegral_mono_set hg (ae_restrict_of_forall_mem measurableSet_Icc hg0)
        hsub1.eventuallyLE
    calc _ ≤ Real.exp (3 / 4 * c) * ∫ α in Icc (-1 : ℝ) (3 / 4), g α := hle
      _ ≤ Real.exp (3 / 4 * c) * M := by gcongr
  -- the top piece is at most `−(1/2) e^{7c/8} m`
  have hI2 : (∫ α in Ioc (3 / 4 : ℝ) 1, g α * Real.exp (α * c) * Real.cos (Real.pi * α))
      ≤ -(1 / 2) * (Real.exp (7 / 8 * c) * m) := by
    have hle : (∫ α in Ioc (3 / 4 : ℝ) 1, g α * Real.exp (α * c) * Real.cos (Real.pi * α))
        ≤ ∫ α in Ioc (3 / 4 : ℝ) 1, (-(1 / 2)) * (g α * Real.exp (α * c)) := by
      refine setIntegral_mono_on (hint.mono_set hsub2) ((hge.mono_set hsub2).const_mul _)
        measurableSet_Ioc ?_
      intro α hα
      have h0 := hg0 α (hsub2 hα)
      have hcos := cos_pi_mul_le_neg_half hα.1.le hα.2
      have hge0 : 0 ≤ g α * Real.exp (α * c) := mul_nonneg h0 (Real.exp_pos _).le
      calc g α * Real.exp (α * c) * Real.cos (Real.pi * α)
          ≤ g α * Real.exp (α * c) * (-(1 / 2)) := mul_le_mul_of_nonneg_left hcos hge0
        _ = (-(1 / 2)) * (g α * Real.exp (α * c)) := by ring
    rw [integral_const_mul] at hle
    have h78 : (∫ α in Icc (7 / 8 : ℝ) 1, g α * Real.exp (α * c))
        ≤ ∫ α in Ioc (3 / 4 : ℝ) 1, g α * Real.exp (α * c) := by
      refine setIntegral_mono_set (hge.mono_set hsub2) ?_ hsub3.eventuallyLE
      exact ae_restrict_of_forall_mem measurableSet_Ioc
        fun α hα => mul_nonneg (hg0 α (hsub2 hα)) (Real.exp_pos _).le
    have hlow : Real.exp (7 / 8 * c) * m ≤ ∫ α in Icc (7 / 8 : ℝ) 1, g α * Real.exp (α * c) := by
      rw [hmdef, ← integral_const_mul]
      refine setIntegral_mono_on ((hg.mono_set (hsub3.trans hsub2)).const_mul _)
        (hge.mono_set (hsub3.trans hsub2)) measurableSet_Icc ?_
      intro α hα
      have h0 := hg0 α (hsub2 (hsub3 hα))
      have hexp : Real.exp (7 / 8 * c) ≤ Real.exp (α * c) :=
        Real.exp_le_exp.mpr (by nlinarith [hα.1])
      calc Real.exp (7 / 8 * c) * g α = g α * Real.exp (7 / 8 * c) := by ring
        _ ≤ g α * Real.exp (α * c) := mul_le_mul_of_nonneg_left hexp h0
    calc _ ≤ -(1 / 2) * ∫ α in Ioc (3 / 4 : ℝ) 1, g α * Real.exp (α * c) := hle
      _ ≤ -(1 / 2) * (Real.exp (7 / 8 * c) * m) := by linarith [h78, hlow]
  -- conclude
  rw [hsplit]
  have hsplitexp : Real.exp (7 / 8 * c) = Real.exp (3 / 4 * c) * Real.exp (c / 8) := by
    rw [← Real.exp_add]; congr 1; ring
  have hc' : 2 * M < Real.exp (c / 8) * m := by
    rwa [div_lt_iff₀ hm] at hc
  have hp : 0 < Real.exp (3 / 4 * c) := Real.exp_pos _
  have hfin : Real.exp (3 / 4 * c) * M + (-(1 / 2)) * (Real.exp (7 / 8 * c) * m) < 0 := by
    rw [hsplitexp]
    nlinarith [mul_lt_mul_of_pos_left hc' hp]
  linarith [hI1, hI2, hfin]

end GaloisForLFunctions.HTGeometry
