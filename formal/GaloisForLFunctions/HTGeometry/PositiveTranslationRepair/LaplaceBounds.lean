import GaloisForLFunctions.HTGeometry.UniformGridStep
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! Positive outer bands control large real Laplace parameters. On bounded parameter
intervals, a compact approximation error and one stronger exponential moment
control the transform uniformly. -/

open MeasureTheory Set Filter Topology

noncomputable section
namespace GaloisForLFunctions.HTGeometry.PositiveTranslationRepair

theorem abs_mul_exp_le {s S : ℝ} (hs : |s| ≤ S) (f : ℝ → ℝ) (x : ℝ) :
    |f x * Real.exp (s * x)| ≤ Real.exp (S * |x|) * |f x| := by
  rw [abs_mul, abs_of_pos (Real.exp_pos _), mul_comm]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  apply Real.exp_le_exp.mpr
  calc
    s * x ≤ |s * x| := le_abs_self _
    _ = |s| * |x| := abs_mul _ _
    _ ≤ S * |x| := mul_le_mul_of_nonneg_right hs (abs_nonneg _)

theorem integrable_mul_exp_of_abs_moment {f : ℝ → ℝ} (hf : Measurable f)
    {s S : ℝ} (hs : |s| ≤ S)
    (hm : Integrable fun x => Real.exp (S * |x|) * |f x|) :
    Integrable fun x => f x * Real.exp (s * x) := by
  apply hm.mono' (hf.mul (by fun_prop)).aestronglyMeasurable
  filter_upwards [] with x
  simpa only [Real.norm_eq_abs, Pi.mul_apply] using abs_mul_exp_le hs f x

theorem continuousOn_laplace_of_abs_moment {f : ℝ → ℝ} (hf : Measurable f) (S : ℝ)
    (hm : Integrable fun x => Real.exp (S * |x|) * |f x|) :
    ContinuousOn (fun s : ℝ => ∫ x, f x * Real.exp (s * x)) (Icc (-S) S) := by
  apply continuousOn_of_dominated
    (bound := fun x => Real.exp (S * |x|) * |f x|)
  · intro s hs
    exact (hf.mul (by fun_prop)).aestronglyMeasurable
  · intro s hs
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs] using abs_mul_exp_le (abs_le.mpr hs) f x
  · exact hm
  · filter_upwards [] with x
    exact (show Continuous (fun s : ℝ => f x * Real.exp (s * x)) by fun_prop).continuousOn

theorem exists_laplace_margin {f : ℝ → ℝ} (hf : Measurable f) {S : ℝ} (hS : 0 ≤ S)
    (hm : Integrable fun x => Real.exp (S * |x|) * |f x|)
    (hp : ∀ s : ℝ, 0 < ∫ x, f x * Real.exp (s * x)) :
    ∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, |s| ≤ S → η ≤ ∫ x, f x * Real.exp (s * x) := by
  obtain ⟨s₀, hs₀, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr (by linarith : -S ≤ S)) (continuousOn_laplace_of_abs_moment hf S hm)
  exact ⟨_, hp s₀, fun s hs => hmin (abs_le.mp hs)⟩

theorem abs_mul_exp_le_tail_weight {s S R x : ℝ} (hs : |s| ≤ S) (hx : R ≤ |x|)
    (f : ℝ → ℝ) :
    |f x * Real.exp (s * x)| ≤
      Real.exp (-R) * (Real.exp ((S + 1) * |x|) * |f x|) := by
  apply (abs_mul_exp_le hs f x).trans
  rw [← mul_assoc, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  apply Real.exp_le_exp.mpr
  linarith only [hx]


/-- Compact uniform error and one stronger exponential moment control all bounded tilts. -/
theorem laplace_sub_le_of_compact_error {f g : ℝ → ℝ} (hf : Measurable f)
    {S s R ε : ℝ} (hS : 0 ≤ S) (hs : |s| ≤ S) (hR : 0 ≤ R) (hε : 0 ≤ ε)
    (hm : Integrable fun x => Real.exp ((S + 1) * |x|) * |f x|)
    (hg : Integrable fun x => g x * Real.exp (s * x))
    (herr : ∀ x ∈ Ioc (-R) R, f x - g x ≤ ε)
    (hout : ∀ x, x ∉ Ioc (-R) R → g x = 0) :
    (∫ x, f x * Real.exp (s * x)) - (∫ x, g x * Real.exp (s * x)) ≤
      2 * R * ε * Real.exp (S * R) +
        Real.exp (-R) * ∫ x, Real.exp ((S + 1) * |x|) * |f x| := by
  let b : ℝ → ℝ := (Ioc (-R) R).indicator (fun _ => ε * Real.exp (S * R))
  have hb : Integrable b := by
    apply IntegrableOn.integrable_indicator _ measurableSet_Ioc
    exact (continuous_const : Continuous (fun _ : ℝ => ε * Real.exp (S * R))).continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hfi := integrable_mul_exp_of_abs_moment hf (hs.trans (by linarith)) hm
  have hbound : ∀ x, (f x - g x) * Real.exp (s * x) ≤
      b x + Real.exp (-R) * (Real.exp ((S + 1) * |x|) * |f x|) := by
    intro x
    by_cases hx : x ∈ Ioc (-R) R
    · have hax : |x| ≤ R := abs_le.mpr ⟨hx.1.le, hx.2⟩
      have he : Real.exp (s * x) ≤ Real.exp (S * R) := by
        apply Real.exp_le_exp.mpr
        calc
          s * x ≤ |s * x| := le_abs_self _
          _ = |s| * |x| := abs_mul _ _
          _ ≤ S * R := mul_le_mul hs hax (abs_nonneg _) hS
      have he' := mul_le_mul_of_nonneg_left he hε
      have hc := mul_le_mul_of_nonneg_right (herr x hx) (Real.exp_pos (s * x)).le
      simp only [b, Set.indicator_of_mem hx]
      exact hc.trans (he'.trans (le_add_of_nonneg_right (by positivity)))
    · have hax : R ≤ |x| := by
        by_contra hn
        have hx' := abs_lt.mp (lt_of_not_ge hn)
        exact hx ⟨hx'.1, hx'.2.le⟩
      rw [hout x hx, sub_zero]
      have hb0 : b x = 0 := Set.indicator_of_notMem hx _
      rw [hb0, zero_add]
      exact (le_abs_self _).trans (abs_mul_exp_le_tail_weight hs hax f)
  have hi : Integrable (fun x => (f x - g x) * Real.exp (s * x)) := by
    apply (hfi.sub hg).congr
    filter_upwards [] with x
    exact (sub_mul (f x) (g x) (Real.exp (s * x))).symm
  have hle := integral_mono hi (hb.add (hm.const_mul (Real.exp (-R)))) hbound
  simp only [Pi.add_apply, sub_mul, integral_sub hfi hg, integral_add hb (hm.const_mul _),
    integral_const_mul] at hle
  have hib : ∫ x, b x = 2 * R * ε * Real.exp (S * R) := by
    rw [show b = (Ioc (-R) R).indicator (fun _ => ε * Real.exp (S * R)) from rfl,
      integral_indicator measurableSet_Ioc]
    simp only [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Ioc]
    rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ R - -R)]
    ring
  simpa only [hib] using hle


/-- A positive unit band beyond the negative core controls every sufficiently large tilt. -/
theorem laplace_pos_of_right_band {g : ℝ → ℝ} {a m B s : ℝ}
    (ha : 0 ≤ a) (hm : 0 < m) (hB : 0 ≤ B) (hs : 0 ≤ s)
    (hg : Integrable fun x => g x * Real.exp (s * x))
    (hlower : ∀ x, m * (Ioc (a + 1) (a + 2)).indicator (1 : ℝ → ℝ) x -
      B * (Ioc (-a) a).indicator (1 : ℝ → ℝ) x ≤ g x)
    (hgap : 2 * a * B < m * Real.exp s) :
    0 < ∫ x, g x * Real.exp (s * x) := by
  let p : ℝ → ℝ := (Ioc (a + 1) (a + 2)).indicator (fun _ => m * Real.exp (s * (a + 1)))
  let n : ℝ → ℝ := (Ioc (-a) a).indicator (fun _ => B * Real.exp (s * a))
  have hp : Integrable p := by
    apply IntegrableOn.integrable_indicator _ measurableSet_Ioc
    exact (continuous_const : Continuous (fun _ : ℝ => m * Real.exp (s * (a + 1)))).continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hn : Integrable n := by
    apply IntegrableOn.integrable_indicator _ measurableSet_Ioc
    exact (continuous_const : Continuous (fun _ : ℝ => B * Real.exp (s * a))).continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hpoint : ∀ x, p x - n x ≤ g x * Real.exp (s * x) := by
    intro x
    have hl := mul_le_mul_of_nonneg_right (hlower x) (Real.exp_pos (s * x)).le
    have hp' : p x ≤ m * (Ioc (a + 1) (a + 2)).indicator (1 : ℝ → ℝ) x * Real.exp (s * x) := by
      by_cases hx : x ∈ Ioc (a + 1) (a + 2)
      · simp only [p, Set.indicator_of_mem hx, Pi.one_apply, mul_one]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx.1.le hs)) hm.le
      · simp only [p, Set.indicator_of_notMem hx, mul_zero, zero_mul, le_refl]
    have hn' : B * (Ioc (-a) a).indicator (1 : ℝ → ℝ) x * Real.exp (s * x) ≤ n x := by
      by_cases hx : x ∈ Ioc (-a) a
      · simp only [n, Set.indicator_of_mem hx, Pi.one_apply, mul_one]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx.2 hs)) hB
      · simp only [n, Set.indicator_of_notMem hx, mul_zero, zero_mul, le_refl]
    rw [sub_mul] at hl
    linarith only [hp', hn', hl]
  have hle := integral_mono (hp.sub hn) hg hpoint
  simp only [Pi.sub_apply, integral_sub hp hn] at hle
  have hip : ∫ x, p x = m * Real.exp (s * (a + 1)) := by
    rw [show p = (Ioc (a + 1) (a + 2)).indicator (fun _ => m * Real.exp (s * (a + 1))) from rfl,
      integral_indicator measurableSet_Ioc]
    simp only [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Ioc]
    rw [show a + 2 - (a + 1) = 1 by ring]
    simp
  have hin : ∫ x, n x = 2 * a * B * Real.exp (s * a) := by
    rw [show n = (Ioc (-a) a).indicator (fun _ => B * Real.exp (s * a)) from rfl,
      integral_indicator measurableSet_Ioc]
    simp only [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Ioc]
    rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ a - -a)]
    ring
  rw [hip, hin] at hle
  have hpos := mul_lt_mul_of_pos_right hgap (Real.exp_pos (s * a))
  rw [show s * (a + 1) = s + s * a by ring, Real.exp_add] at hle
  nlinarith only [hle, hpos]


/-- A bounded negative core and positive bands on both sides control both real tails. -/
theorem laplace_pos_of_outer_bands {g : ℝ → ℝ} {a m B S : ℝ}
    (ha : 0 ≤ a) (hm : 0 < m) (hB : 0 ≤ B)
    (hg : ∀ s : ℝ, Integrable fun x => g x * Real.exp (s * x))
    (hcore : ∀ x, -B ≤ g x) (hout : ∀ x, a ≤ |x| → 0 ≤ g x)
    (hband : ∀ x, a + 1 ≤ |x| → |x| ≤ a + 2 → m ≤ g x)
    (hgap : 2 * a * B < m * Real.exp S) (s : ℝ) (hs : S ≤ |s|) :
    0 < ∫ x, g x * Real.exp (s * x) := by
  have hright : ∀ k : ℝ → ℝ, (∀ x, -B ≤ k x) →
      (∀ x, a ≤ |x| → 0 ≤ k x) →
      (∀ x, a + 1 ≤ |x| → |x| ≤ a + 2 → m ≤ k x) →
      ∀ x, m * (Ioc (a + 1) (a + 2)).indicator (1 : ℝ → ℝ) x -
        B * (Ioc (-a) a).indicator (1 : ℝ → ℝ) x ≤ k x := by
    intro k hc ho hb x
    by_cases hx : x ∈ Ioc (a + 1) (a + 2)
    · have hxc : x ∉ Ioc (-a) a := fun h => by linarith only [hx.1, h.2]
      simp only [Set.indicator_of_mem hx, Set.indicator_of_notMem hxc,
        Pi.one_apply, mul_one, mul_zero, sub_zero]
      have hx0 : 0 ≤ x := by linarith only [ha, hx.1]
      apply hb x <;> rw [abs_of_nonneg hx0]
      · exact hx.1.le
      · exact hx.2
    · simp only [Set.indicator_of_notMem hx, mul_zero, zero_sub]
      by_cases hc' : x ∈ Ioc (-a) a
      · simpa only [Set.indicator_of_mem hc', Pi.one_apply, mul_one] using hc x
      · simp only [Set.indicator_of_notMem hc', mul_zero, neg_zero]
        apply ho x
        by_contra h
        have h' := abs_lt.mp (lt_of_not_ge h)
        exact hc' ⟨h'.1, h'.2.le⟩
  have hgap' : 2 * a * B < m * Real.exp |s| :=
    hgap.trans_le (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hs) hm.le)
  by_cases hs0 : 0 ≤ s
  · rw [abs_of_nonneg hs0] at hgap'
    exact laplace_pos_of_right_band ha hm hB hs0 (hg s) (hright g hcore hout hband) hgap'
  · have hs0' : s ≤ 0 := (lt_of_not_ge hs0).le
    rw [abs_of_nonpos hs0'] at hgap'
    have hint : Integrable (fun x => g (-x) * Real.exp (-s * x)) := by
      simpa only [Function.comp_def, neg_mul, mul_neg] using (hg s).comp_neg
    have h := laplace_pos_of_right_band ha hm hB (neg_nonneg.mpr hs0') hint
      (hright (fun x => g (-x)) (fun x => hcore (-x))
        (fun x hx => hout (-x) (by simpa only [abs_neg] using hx))
        (fun x hl hu => hband (-x) (by simpa only [abs_neg] using hl)
          (by simpa only [abs_neg] using hu))) hgap'
    rw [← integral_neg_eq_self (fun x => g (-x) * Real.exp (-s * x))] at h
    simpa only [neg_neg, neg_mul_neg] using h

/-- Strict positivity on a compact annulus has a uniform positive margin. -/
theorem exists_pos_annulus_margin {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hp : ∀ x, a ≤ |x| → |x| ≤ b → 0 < f x) :
    ∃ m : ℝ, 0 < m ∧ ∀ x, a ≤ |x| → |x| ≤ b → m ≤ f x := by
  let K : Set ℝ := Icc (-b) b ∩ {x | a ≤ |x|}
  have hc : IsCompact K := isCompact_Icc.inter_right (isClosed_le continuous_const continuous_abs)
  have hn : K.Nonempty := ⟨b, ⟨⟨by linarith, le_rfl⟩,
    by simpa only [mem_setOf_eq, abs_of_nonneg (ha.trans hab)] using hab⟩⟩
  obtain ⟨x, hx, hmin⟩ := hc.exists_isMinOn hn hf.continuousOn
  refine ⟨f x, hp x hx.2 (abs_le.mpr hx.1), fun y hyl hyu => ?_⟩
  exact hmin ⟨abs_le.mp hyu, hyl⟩

#print axioms exists_laplace_margin
#print axioms laplace_sub_le_of_compact_error
#print axioms laplace_pos_of_outer_bands
end GaloisForLFunctions.HTGeometry.PositiveTranslationRepair
