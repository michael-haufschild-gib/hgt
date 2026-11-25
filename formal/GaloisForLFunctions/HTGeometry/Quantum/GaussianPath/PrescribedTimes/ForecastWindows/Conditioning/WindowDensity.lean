import Mathlib.Analysis.Calculus.Monotone
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Local window bounds for a conditional date distribution -/

open Set Filter MeasureTheory Topology
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ForecastWindows.Conditioning
noncomputable section

/-- At almost every target time a probability measure assigns at most a
constant times the radius to every centered window. The constant is local
to the target and the distribution may have atoms elsewhere. -/
theorem ae_window_bound (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ∀ᵐ t : ℝ, ∃ C ≥ (0:ℝ), ∀ h> (0:ℝ), μ.real {u | |u-t|<h} ≤ C*h := by
  let G (u : ℝ) := μ.real (Iic u)
  have hG : Monotone G := fun _ _ h => measureReal_mono (μ:=μ) (Iic_subset_Iic.mpr h) (measure_ne_top _ _)
  filter_upwards [hG.ae_differentiableAt] with t ht
  obtain ⟨c,hc,hlocal⟩ := ht.hasFDerivAt.isBigO_sub.exists_pos
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hlocal.bound
  let C := max (2*c) δ⁻¹
  have hC : 0≤C := (mul_nonneg (by norm_num) hc.le).trans (le_max_left ..)
  refine ⟨C,hC,fun h hh => ?_⟩
  by_cases hd : h<δ
  · have hl : t-h∈Metric.ball t δ := by
      rwa [Metric.mem_ball, Real.dist_eq, sub_sub_cancel_left, abs_neg, abs_of_pos hh]
    have hu : t+h∈Metric.ball t δ := by
      rwa [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos hh]
    have hlo := hball hl
    have hhi := hball hu
    simp only [mem_setOf_eq,Real.norm_eq_abs,sub_sub_cancel_left,abs_neg,abs_of_pos hh] at hlo
    simp only [mem_setOf_eq,Real.norm_eq_abs,add_sub_cancel_left,abs_of_pos hh] at hhi
    have hs : {u : ℝ | |u-t|<h}⊆ Iic (t+h) \ Iic (t-h) := by
      intro u hv
      change |u-t| < h at hv
      obtain ⟨h₁,h₂⟩ := abs_lt.mp hv
      exact ⟨by change u≤t+h; linarith only [h₂],by change ¬u≤t-h; linarith only [h₁]⟩
    apply (measureReal_mono (μ:=μ) hs (measure_ne_top _ _)).trans
    rw [measureReal_sdiff (Iic_subset_Iic.mpr (by linarith only [hh])) measurableSet_Iic]
    change G (t+h)-G (t-h)≤C*h
    exact (show G (t+h)-G (t-h)≤(2*c)*h by
      linarith only [(abs_le.mp hlo).1,(abs_le.mp hhi).2]).trans
      (mul_le_mul_of_nonneg_right (le_max_left ..) hh.le)
  · apply measureReal_le_one.trans
    calc
      (1:ℝ) = δ⁻¹*δ := (inv_mul_cancel₀ hδ.ne').symm
      _ ≤ δ⁻¹*h := mul_le_mul_of_nonneg_left (le_of_not_gt hd) (inv_nonneg.mpr hδ.le)
      _ ≤ C*h := mul_le_mul_of_nonneg_right (le_max_right ..) hh.le

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Conditional window mass is measurable jointly in the background and center. -/
theorem measurable_window_mass (ν : Measure Y) [IsProbabilityMeasure ν] {F : X×Y→ℝ}
    (hF : Measurable F) (r : ℝ) :
    Measurable (fun p : X×ℝ => ν.real {y | |F (p.1,y)-p.2|<r}) := by
  let A := {z : (X×ℝ)×Y | |F (z.1.1,z.2)-z.1.2|<r}
  have hA : MeasurableSet A := measurableSet_lt
    (continuous_abs.measurable.comp ((hF.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).sub
      (measurable_snd.comp measurable_fst))) measurable_const
  exact ENNReal.measurable_toReal.comp (measurable_measure_prodMk_left (ν:=ν) hA)

/-- Rational radii give a countable measurable test for local linear growth. -/
def Regular (ν : Measure Y) (F : X×Y→ℝ) (x : X) (t : ℝ) : Prop :=
  ∃ m : ℕ, ∀ q : ℚ, 0<q → ν.real {y | |F (x,y)-t|<(q:ℝ)}≤(m:ℝ)*q

theorem measurableSet_regular (ν : Measure Y) [IsProbabilityMeasure ν] {F : X×Y→ℝ}
    (hF : Measurable F) : MeasurableSet {p : X×ℝ | Regular ν F p.1 p.2} := by
  unfold Regular
  rw [setOf_exists]
  apply MeasurableSet.iUnion
  intro m
  rw [setOf_forall]
  apply MeasurableSet.iInter
  intro q
  by_cases hq : 0<q
  · simp only [hq,true_implies]
    exact measurableSet_le (measurable_window_mass ν hF q) measurable_const
  · simp [hq]

omit [MeasurableSpace X] in
theorem regular_of_bound (ν : Measure Y) (F : X×Y→ℝ) (x : X) (t C : ℝ)
    (h : ∀ r> (0:ℝ), ν.real {y | |F (x,y)-t|<r}≤C*r) : Regular ν F x t := by
  refine ⟨⌈C⌉₊,fun q hq => (h _ (by exact_mod_cast hq)).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (Nat.le_ceil C) (by exact_mod_cast hq.le)

omit [MeasurableSpace X] in
theorem bound_of_regular (ν : Measure Y) [IsProbabilityMeasure ν] (F : X×Y→ℝ)
    {x : X} {t : ℝ} (h : Regular ν F x t) :
    ∃ C ≥ (0:ℝ), ∀ r> (0:ℝ), ν.real {y | |F (x,y)-t|<r}≤C*r := by
  obtain ⟨m,hm⟩ := h
  refine ⟨2*m,by positivity,fun r hr => ?_⟩
  obtain ⟨q,hrq,hqr⟩ := exists_rat_btwn (show r<2*r by linarith only [hr])
  have hq : (0:ℚ)<q := by exact_mod_cast hr.trans hrq
  apply (measureReal_mono (μ:=ν) (s₂:={y | |F (x,y)-t|<(q:ℝ)}) (fun _ hy => hy.trans hrq)).trans
  exact (hm q hq).trans ((mul_le_mul_of_nonneg_left hqr.le (Nat.cast_nonneg m)).trans_eq (by ring))

#print axioms ae_window_bound
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ForecastWindows.Conditioning
