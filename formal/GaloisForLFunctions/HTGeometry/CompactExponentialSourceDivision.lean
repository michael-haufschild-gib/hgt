import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Algebra.Indicator
import Mathlib.Topology.Algebra.Support

/-!
# Compact division for exponential source equations

The equation `H' - z H = q` on a finite interval has a solution with both endpoint
values zero exactly when the weighted source moment vanishes. The integrating
factor gives both the exact endpoint balance and an explicit solution, whose
zero extension is continuous and compactly supported.

Subtracting a multiple of `exp(z t)` removes the obstruction. The coefficient
is uniquely determined by the source moment and interval length. For constant
window forcing the obstruction vanishes exactly at the nonzero exponential
resonances; in particular, it never vanishes when `z.re` is nonzero.
-/

open Complex Set MeasureTheory
open scoped Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Exponential integrating factor for a constant complex source parameter. -/
def sourceDivisionPhase (z : ℂ) (t : ℝ) : ℂ := Complex.exp (z * (t : ℂ))

theorem sourceDivisionPhase_hasDerivAt (z : ℂ) (t : ℝ) :
    HasDerivAt (sourceDivisionPhase z) (sourceDivisionPhase z t * z) t := by
  have hlin : HasDerivAt (fun s : ℝ => z * (s : ℂ)) z t := by
    simpa using (hasDerivAt_id t).ofReal_comp.const_mul z
  exact hlin.cexp

theorem sourceDivisionPhase_continuous (z : ℂ) : Continuous (sourceDivisionPhase z) :=
  continuous_iff_continuousAt.mpr fun t => (sourceDivisionPhase_hasDerivAt z t).continuousAt

theorem sourceDivisionPhase_mul_neg (z : ℂ) (t : ℝ) :
    sourceDivisionPhase z t * sourceDivisionPhase (-z) t = 1 := by
  rw [sourceDivisionPhase, sourceDivisionPhase, ← Complex.exp_add]
  simp

/-- The weighted source moment determining the endpoint mismatch. -/
def sourceDivisionMoment (z : ℂ) (a b : ℝ) (q : ℝ → ℂ) : ℂ :=
  ∫ t in a..b, sourceDivisionPhase (-z) t * q t

/-- The solution with zero value at the left endpoint. -/
def sourceDivisionPrimitive (z : ℂ) (a : ℝ) (q : ℝ → ℂ) (t : ℝ) : ℂ :=
  sourceDivisionPhase z t * sourceDivisionMoment z a t q

/-- Exact boundary balance for the original inhomogeneous equation. -/
theorem sourceDivision_boundary_balance {a b : ℝ} (hab : a ≤ b)
    (z : ℂ) {q H : ℝ → ℂ} (hH : ContinuousOn H (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt H (z * H t + q t) t)
    (hiq : IntervalIntegrable (fun t => sourceDivisionPhase (-z) t * q t) volume a b) :
    sourceDivisionMoment z a b q =
      sourceDivisionPhase (-z) b * H b - sourceDivisionPhase (-z) a * H a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    ((sourceDivisionPhase_continuous (-z)).continuousOn.mul hH) _ hiq
  intro t ht
  apply ((sourceDivisionPhase_hasDerivAt (-z) t).mul (hd t ht)).congr_deriv
  ring

theorem sourceDivisionPrimitive_hasDerivAt (z : ℂ) (a : ℝ)
    {q : ℝ → ℂ} (hq : Continuous q) (t : ℝ) :
    HasDerivAt (sourceDivisionPrimitive z a q)
      (z * sourceDivisionPrimitive z a q t + q t) t := by
  have hc : Continuous (fun t => sourceDivisionPhase (-z) t * q t) :=
    (sourceDivisionPhase_continuous (-z)).mul hq
  have hi := intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable a t) hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have hd := (sourceDivisionPhase_hasDerivAt z t).mul hi
  apply hd.congr_deriv
  change sourceDivisionPhase z t * z * sourceDivisionMoment z a t q +
      sourceDivisionPhase z t * (sourceDivisionPhase (-z) t * q t) = _
  rw [← mul_assoc (sourceDivisionPhase z t), sourceDivisionPhase_mul_neg, one_mul]
  dsimp [sourceDivisionPrimitive]
  ring

theorem sourceDivisionPrimitive_continuous (z : ℂ) (a : ℝ)
    {q : ℝ → ℂ} (hq : Continuous q) : Continuous (sourceDivisionPrimitive z a q) :=
  continuous_iff_continuousAt.mpr fun t =>
    (sourceDivisionPrimitive_hasDerivAt z a hq t).continuousAt

@[simp] theorem sourceDivisionPrimitive_left (z : ℂ) (a : ℝ) (q : ℝ → ℂ) :
    sourceDivisionPrimitive z a q a = 0 := by
  simp [sourceDivisionPrimitive, sourceDivisionMoment]

theorem sourceDivisionPrimitive_right_eq_zero_iff (z : ℂ) (a b : ℝ) (q : ℝ → ℂ) :
    sourceDivisionPrimitive z a q b = 0 ↔ sourceDivisionMoment z a b q = 0 := by
  simp [sourceDivisionPrimitive, sourceDivisionPhase, Complex.exp_ne_zero]

/-- The weighted moment is the complete obstruction to two zero endpoint values. -/
theorem sourceDivision_exists_zero_boundary_iff {a b : ℝ} (hab : a ≤ b)
    (z : ℂ) {q : ℝ → ℂ} (hq : Continuous q) :
    (∃ H : ℝ → ℂ, ContinuousOn H (Icc a b) ∧ H a = 0 ∧ H b = 0 ∧
      ∀ t ∈ Ioo a b, HasDerivAt H (z * H t + q t) t) ↔
        sourceDivisionMoment z a b q = 0 := by
  constructor
  · rintro ⟨H, hH, ha, hb, hd⟩
    have hi := ((sourceDivisionPhase_continuous (-z)).mul hq).intervalIntegrable (μ := volume) a b
    simpa [ha, hb] using sourceDivision_boundary_balance hab z hH hd hi
  · intro hm
    refine ⟨sourceDivisionPrimitive z a q,
      (sourceDivisionPrimitive_continuous z a hq).continuousOn,
      sourceDivisionPrimitive_left z a q,
      (sourceDivisionPrimitive_right_eq_zero_iff z a b q).2 hm, ?_⟩
    exact fun t _ => sourceDivisionPrimitive_hasDerivAt z a hq t

/-- Zero extension of the left-normalized solution. -/
def sourceDivisionCompactPrimitive (z : ℂ) (a b : ℝ) (q : ℝ → ℂ) : ℝ → ℂ :=
  (Icc a b).indicator (sourceDivisionPrimitive z a q)

theorem sourceDivisionCompactPrimitive_hasCompactSupport (z : ℂ) (a b : ℝ) (q : ℝ → ℂ) :
    HasCompactSupport (sourceDivisionCompactPrimitive z a b q) := by
  apply HasCompactSupport.intro isCompact_Icc
  intro t ht
  exact Set.indicator_of_notMem ht _

theorem sourceDivisionCompactPrimitive_continuous {a b : ℝ} (hab : a ≤ b)
    (z : ℂ) {q : ℝ → ℂ} (hq : Continuous q) (hm : sourceDivisionMoment z a b q = 0) :
    Continuous (sourceDivisionCompactPrimitive z a b q) := by
  apply (sourceDivisionPrimitive_continuous z a hq).indicator
  intro t ht
  rw [frontier_Icc hab, mem_insert_iff, mem_singleton_iff] at ht
  rcases ht with ha | hb
  · rw [ha]
    exact sourceDivisionPrimitive_left z a q
  · rw [hb]
    exact (sourceDivisionPrimitive_right_eq_zero_iff z a b q).2 hm

theorem sourceDivisionCompactPrimitive_hasDerivAt (z : ℂ) (a b : ℝ)
    {q : ℝ → ℂ} (hq : Continuous q) {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (sourceDivisionCompactPrimitive z a b q)
      (z * sourceDivisionCompactPrimitive z a b q t + q t) t := by
  have heq : sourceDivisionCompactPrimitive z a b q =ᶠ[𝓝 t]
      sourceDivisionPrimitive z a q := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
    exact Set.indicator_of_mem (show u ∈ Icc a b from ⟨hu.1.le, hu.2.le⟩) _
  rw [heq.eq_of_nhds]
  exact (sourceDivisionPrimitive_hasDerivAt z a hq t).congr_of_eventuallyEq heq

/-- Constructive compact-source division alternative, retaining both endpoints. -/
theorem sourceDivision_exists_compact_iff {a b : ℝ} (hab : a ≤ b)
    (z : ℂ) {q : ℝ → ℂ} (hq : Continuous q) :
    (∃ H : ℝ → ℂ, Continuous H ∧ HasCompactSupport H ∧
      (∀ t ∉ Icc a b, H t = 0) ∧ H a = 0 ∧ H b = 0 ∧
      ∀ t ∈ Ioo a b, HasDerivAt H (z * H t + q t) t) ↔
        sourceDivisionMoment z a b q = 0 := by
  constructor
  · rintro ⟨H, hc, _, _, ha, hb, hd⟩
    exact (sourceDivision_exists_zero_boundary_iff hab z hq).1
      ⟨H, hc.continuousOn, ha, hb, hd⟩
  · intro hm
    refine ⟨sourceDivisionCompactPrimitive z a b q,
      sourceDivisionCompactPrimitive_continuous hab z hq hm,
      sourceDivisionCompactPrimitive_hasCompactSupport z a b q,
      fun t ht => Set.indicator_of_notMem ht _, ?_, ?_, ?_⟩
    · rw [sourceDivisionCompactPrimitive,
        Set.indicator_of_mem (show a ∈ Icc a b from ⟨le_rfl, hab⟩)]
      exact sourceDivisionPrimitive_left z a q
    · rw [sourceDivisionCompactPrimitive,
        Set.indicator_of_mem (show b ∈ Icc a b from ⟨hab, le_rfl⟩)]
      exact (sourceDivisionPrimitive_right_eq_zero_iff z a b q).2 hm
    · exact fun t ht => sourceDivisionCompactPrimitive_hasDerivAt z a b hq ht

/-- The uniquely normalized exponential correction to the original forcing. -/
def sourceDivisionCorrection (z : ℂ) (a b : ℝ) (q : ℝ → ℂ) (t : ℝ) : ℂ :=
  sourceDivisionPhase z t * (sourceDivisionMoment z a b q / ((b - a : ℝ) : ℂ))

theorem sourceDivisionMoment_sub_phase (z : ℂ) (a b : ℝ)
    {q : ℝ → ℂ} (hq : Continuous q) (c : ℂ) :
    sourceDivisionMoment z a b (fun t => q t - sourceDivisionPhase z t * c) =
      sourceDivisionMoment z a b q - ((b - a : ℝ) : ℂ) * c := by
  have hc : Continuous (fun t => sourceDivisionPhase (-z) t * q t) :=
    (sourceDivisionPhase_continuous (-z)).mul hq
  have hi : (fun t => sourceDivisionPhase (-z) t *
      (q t - sourceDivisionPhase z t * c)) =
      fun t => sourceDivisionPhase (-z) t * q t - c := by
    funext t
    rw [mul_sub, ← mul_assoc]
    have he : sourceDivisionPhase (-z) t * sourceDivisionPhase z t = 1 := by
      rw [mul_comm]
      exact sourceDivisionPhase_mul_neg z t
    rw [he, one_mul]
  change (∫ t in a..b, sourceDivisionPhase (-z) t *
    (q t - sourceDivisionPhase z t * c)) = _
  rw [hi, intervalIntegral.integral_sub (hc.intervalIntegrable a b) intervalIntegrable_const]
  rw [intervalIntegral.integral_const]
  rfl

/-- Exactly one exponential correction annihilates the weighted source moment. -/
theorem sourceDivision_compensation_unique {a b : ℝ} (hab : a < b)
    (z : ℂ) {q : ℝ → ℂ} (hq : Continuous q) (c : ℂ) :
    sourceDivisionMoment z a b (fun t => q t - sourceDivisionPhase z t * c) = 0 ↔
      c = sourceDivisionMoment z a b q / ((b - a : ℝ) : ℂ) := by
  have hba : ((b - a : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (sub_pos.mpr hab).ne'
  rw [sourceDivisionMoment_sub_phase z a b hq c, sub_eq_zero, eq_div_iff hba]
  exact ⟨fun h => by rw [mul_comm]; exact h.symm,
    fun h => by rw [mul_comm]; exact h.symm⟩

theorem sourceDivisionMoment_sub_correction {a b : ℝ} (hab : a < b)
    (z : ℂ) {q : ℝ → ℂ} (hq : Continuous q) :
    sourceDivisionMoment z a b (fun t => q t - sourceDivisionCorrection z a b q t) = 0 :=
  (sourceDivision_compensation_unique hab z hq _).2 rfl

/-- Every continuous forcing admits compact division after its explicit correction. -/
theorem sourceDivision_corrected_source_has_compact_solution {a b : ℝ} (hab : a < b)
    (z : ℂ) {q : ℝ → ℂ} (hq : Continuous q) :
    ∃ H : ℝ → ℂ, Continuous H ∧ HasCompactSupport H ∧
      (∀ t ∉ Icc a b, H t = 0) ∧ H a = 0 ∧ H b = 0 ∧
      ∀ t ∈ Ioo a b,
        HasDerivAt H (z * H t + q t - sourceDivisionCorrection z a b q t) t := by
  have hc : Continuous (fun t => q t - sourceDivisionCorrection z a b q t) :=
    hq.sub ((sourceDivisionPhase_continuous z).mul continuous_const)
  obtain ⟨H, hH, hK, hs, ha, hb, hd⟩ :=
    (sourceDivision_exists_compact_iff hab.le z hc).2
      (sourceDivisionMoment_sub_correction hab z hq)
  refine ⟨H, hH, hK, hs, ha, hb, fun t ht => ?_⟩
  convert hd t ht using 1
  ring

theorem sourceDivisionMoment_one_mul {a b : ℝ} (hab : a ≤ b) (z : ℂ) :
    sourceDivisionMoment z a b (fun _ => 1) * (-z) =
      sourceDivisionPhase (-z) b - sourceDivisionPhase (-z) a := by
  have hd := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    (sourceDivisionPhase_continuous (-z)).continuousOn
    (fun t _ => sourceDivisionPhase_hasDerivAt (-z) t)
    (((sourceDivisionPhase_continuous (-z)).mul continuous_const).intervalIntegrable
      (μ := volume) a b)
  simpa [sourceDivisionMoment, intervalIntegral.integral_mul_const] using hd

/-- A window source has nonzero obstruction away from the imaginary parameter axis. -/
theorem sourceDivisionMoment_one_ne_zero {a b : ℝ} (hab : a < b)
    {z : ℂ} (hz : z.re ≠ 0) : sourceDivisionMoment z a b (fun _ => 1) ≠ 0 := by
  intro hzero
  have h := sourceDivisionMoment_one_mul hab.le z
  rw [hzero, zero_mul] at h
  have he := congrArg norm (sub_eq_zero.mp h.symm)
  simp only [sourceDivisionPhase, Complex.norm_exp, Complex.mul_re,
    Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero] at he
  have he' := Real.exp_injective he
  have hzba : z.re * (b - a) = 0 := by nlinarith [he']
  exact (mul_ne_zero hz (sub_pos.mpr hab).ne') hzba

/-- The uncorrected window has no solution with two zero endpoint values off the imaginary axis. -/
theorem sourceDivision_no_zero_boundary_window {a b : ℝ} (hab : a < b)
    {z : ℂ} (hz : z.re ≠ 0) :
    ¬ ∃ H : ℝ → ℂ, ContinuousOn H (Icc a b) ∧ H a = 0 ∧ H b = 0 ∧
      ∀ t ∈ Ioo a b, HasDerivAt H (z * H t + 1) t := by
  exact fun h => sourceDivisionMoment_one_ne_zero hab hz
    ((sourceDivision_exists_zero_boundary_iff hab.le z continuous_const).1 h)

/-- Sharp classification of the window obstruction by nonzero exponential resonance. -/
theorem sourceDivisionMoment_one_eq_zero_iff {a b : ℝ} (hab : a < b) (z : ℂ) :
    sourceDivisionMoment z a b (fun _ => 1) = 0 ↔
      z ≠ 0 ∧ sourceDivisionPhase (-z) b = sourceDivisionPhase (-z) a := by
  constructor
  · intro hm
    refine ⟨?_, ?_⟩
    · intro hz
      subst z
      have hba : ((b - a : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (sub_pos.mpr hab).ne'
      apply hba
      simpa [sourceDivisionMoment, sourceDivisionPhase] using hm
    · have h := sourceDivisionMoment_one_mul hab.le z
      rw [hm, zero_mul] at h
      exact sub_eq_zero.mp h.symm
  · rintro ⟨hz, he⟩
    have h := sourceDivisionMoment_one_mul hab.le z
    rw [he, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_right (neg_ne_zero.mpr hz)

end
end GaloisForLFunctions.HTGeometry
