import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Continuous functions are determined by their pairings with test weights

If a continuous function on the line integrates to zero against every continuous compactly
supported weight, it vanishes.  Pairing the function against a triangular bump times its own
conjugate produces the integral of a nonnegative continuous function that is strictly positive
near any point where the function does not vanish.

This is the fundamental lemma of the calculus of variations, in the form needed to pass from
pairings with test weights to pointwise identities.  mathlib does not have it.

* `triangleBump` : the elementary nonnegative compactly supported weight, with
  `integral_triangleBump_pos`.
* `eq_zero_of_forall_integral_mul_eq_zero` : the real statement.
* `eq_of_forall_integral_mul_eq` : the complex statement, for two continuous functions.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

section TriangleBump

/-- The triangular bump of height `δ` centred at `c`. -/
noncomputable def triangleBump (c delta : ℝ) : ℝ → ℝ := fun t => max 0 (delta - |t - c|)

theorem continuous_triangleBump (c delta : ℝ) : Continuous (triangleBump c delta) :=
  continuous_const.max (continuous_const.sub ((continuous_id.sub continuous_const).abs))

theorem triangleBump_nonneg (c delta : ℝ) (t : ℝ) : 0 ≤ triangleBump c delta t :=
  le_max_left _ _

theorem triangleBump_eq_zero_of_notMem (c delta : ℝ) {t : ℝ}
    (ht : t ∉ Set.Icc (c - delta) (c + delta)) : triangleBump c delta t = 0 := by
  rw [triangleBump, max_eq_left]
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
  rcases ht with h | h
  · have habs : delta < |t - c| := by
      have h1 : delta < c - t := by linarith
      refine lt_of_lt_of_le h1 ?_
      rw [abs_sub_comm]
      exact le_abs_self (c - t)
    linarith
  · have habs : delta < |t - c| := by
      have h1 : delta < t - c := by linarith
      exact lt_of_lt_of_le h1 (le_abs_self (t - c))
    linarith

theorem hasCompactSupport_triangleBump (c delta : ℝ) :
    HasCompactSupport (triangleBump c delta) :=
  HasCompactSupport.intro (isCompact_Icc (a := c - delta) (b := c + delta))
    fun _ ht => triangleBump_eq_zero_of_notMem c delta ht

theorem triangleBump_pos_of_mem {c delta t : ℝ} (h : |t - c| < delta) :
    0 < triangleBump c delta t := by
  rw [triangleBump, lt_max_iff]
  exact Or.inr (by linarith)

theorem integrable_triangleBump (c delta : ℝ) : Integrable (triangleBump c delta) :=
  (continuous_triangleBump c delta).integrable_of_hasCompactSupport
    (hasCompactSupport_triangleBump c delta)

/-- A nonnegative continuous function that is strictly positive on the bump's interior has
strictly positive integral. -/
theorem integral_pos_of_pos_on_ball {g : ℝ → ℝ} (hnonneg : ∀ s, 0 ≤ g s)
    (hint : Integrable g) {c delta : ℝ} (hdelta : 0 < delta)
    (hpos : ∀ s, |s - c| < delta → 0 < g s) :
    0 < ∫ s, g s := by
  rw [integral_pos_iff_support_of_nonneg hnonneg hint]
  have hsub : Set.Ioo (c - delta) (c + delta) ⊆ Function.support g := by
    intro s hs
    have habs : |s - c| < delta := by
      rw [abs_lt]
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    exact ne_of_gt (hpos s habs)
  have hvol : 0 < MeasureTheory.volume (Set.Ioo (c - delta) (c + delta)) := by
    rw [Real.volume_Ioo, ENNReal.ofReal_pos]
    linarith
  exact lt_of_lt_of_le hvol (measure_mono hsub)

/-- The triangular bump has strictly positive integral. -/
theorem integral_triangleBump_pos (c : ℝ) {delta : ℝ} (hdelta : 0 < delta) :
    0 < ∫ t, triangleBump c delta t :=
  integral_pos_of_pos_on_ball (triangleBump_nonneg c delta)
    (integrable_triangleBump c delta) hdelta fun _ hs => triangleBump_pos_of_mem hs

end TriangleBump

section TestPairing

/-- A radius on which a continuous function stays away from zero near a point where it does not
vanish. -/
theorem exists_ball_norm_pos {F : Type*} [NormedAddCommGroup F] {f : ℝ → F} (hf : Continuous f)
    {t : ℝ} (hne : f t ≠ 0) :
    ∃ delta > 0, ∀ s, |s - t| < delta → f s ≠ 0 := by
  have hpos : 0 < ‖f t‖ / 2 := by
    have := norm_pos_iff.mpr hne
    linarith
  obtain ⟨delta, hdelta, hball⟩ :=
    Metric.continuousAt_iff.mp (hf.norm).continuousAt (‖f t‖ / 2) hpos
  refine ⟨delta, hdelta, fun s hs => ?_⟩
  have hds : dist s t < delta := by
    rw [Real.dist_eq]
    exact hs
  have hb := hball hds
  rw [Real.dist_eq, abs_lt] at hb
  have hlow : ‖f t‖ / 2 < ‖f s‖ := by linarith [hb.1]
  exact norm_pos_iff.mp (lt_trans hpos hlow)

/-- **The fundamental lemma of the calculus of variations, complex form.**  A continuous function
that integrates to zero against every continuous compactly supported weight is zero. -/
theorem eq_zero_of_forall_integral_mul_eq_zero_complex {f : ℝ → ℂ} (hf : Continuous f)
    (h : ∀ phi : ℝ → ℂ, Continuous phi → HasCompactSupport phi → ∫ t, phi t * f t = 0) (t : ℝ) :
    f t = 0 := by
  by_contra hne
  obtain ⟨delta, hdelta, hball⟩ := exists_ball_norm_pos hf hne
  set phi : ℝ → ℂ := fun s => ((triangleBump t delta s : ℝ) : ℂ) * (starRingEnd ℂ) (f s) with hphi
  have hcontphi : Continuous phi := by
    rw [hphi]
    exact (Complex.continuous_ofReal.comp (continuous_triangleBump t delta)).mul
      (Complex.continuous_conj.comp hf)
  have hsuppphi : HasCompactSupport phi := by
    refine HasCompactSupport.intro (isCompact_Icc (a := t - delta) (b := t + delta)) ?_
    intro s hs
    rw [hphi]
    simp only
    rw [triangleBump_eq_zero_of_notMem t delta hs]
    simp
  have hzero := h phi hcontphi hsuppphi
  set g : ℝ → ℝ := fun s => triangleBump t delta s * Complex.normSq (f s) with hg
  have hgcont : Continuous g := by
    rw [hg]
    exact (continuous_triangleBump t delta).mul (Complex.continuous_normSq.comp hf)
  have hgnonneg : ∀ s, 0 ≤ g s := fun s =>
    mul_nonneg (triangleBump_nonneg t delta s) (Complex.normSq_nonneg _)
  have hgsupp : HasCompactSupport g := by
    refine HasCompactSupport.intro (isCompact_Icc (a := t - delta) (b := t + delta)) ?_
    intro s hs
    rw [hg]
    simp only
    rw [triangleBump_eq_zero_of_notMem t delta hs, zero_mul]
  have hgint : Integrable g := hgcont.integrable_of_hasCompactSupport hgsupp
  have hpoint : ∀ s, phi s * f s = ((g s : ℝ) : ℂ) := by
    intro s
    rw [hphi, hg]
    simp only
    rw [mul_assoc, mul_comm ((starRingEnd ℂ) (f s)) (f s), Complex.mul_conj]
    push_cast
    ring
  have hgzero : ∫ s, g s = 0 := by
    have h1 : ∫ s, Complex.ofRealCLM (g s) = 0 := by
      rw [← hzero]
      exact integral_congr_ae (Filter.Eventually.of_forall fun s => (hpoint s).symm)
    rw [Complex.ofRealCLM.integral_comp_comm hgint] at h1
    exact Complex.ofReal_eq_zero.mp h1
  have hgpos : 0 < ∫ s, g s := by
    refine integral_pos_of_pos_on_ball (c := t) hgnonneg hgint hdelta ?_
    intro s hs
    refine mul_pos (triangleBump_pos_of_mem hs) ?_
    rw [Complex.normSq_pos]
    exact hball s hs
  linarith

/-- **Two continuous functions with the same test pairings agree.** -/
theorem eq_of_forall_integral_mul_eq {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ phi : ℝ → ℂ, Continuous phi → HasCompactSupport phi →
      ∫ t, phi t * f t = ∫ t, phi t * g t) (t : ℝ) : f t = g t := by
  have hsub : ∀ phi : ℝ → ℂ, Continuous phi → HasCompactSupport phi →
      ∫ s, phi s * (f s - g s) = 0 := by
    intro phi hphi hsupp
    have hf1 : Integrable (fun s => phi s * f s) :=
      (hphi.mul hf).integrable_of_hasCompactSupport hsupp.mul_right
    have hg1 : Integrable (fun s => phi s * g s) :=
      (hphi.mul hg).integrable_of_hasCompactSupport hsupp.mul_right
    have hsplit : ∀ s, phi s * (f s - g s) = phi s * f s - phi s * g s := fun s => by ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hsplit),
      integral_sub hf1 hg1, h phi hphi hsupp, sub_self]
  have hzz := eq_zero_of_forall_integral_mul_eq_zero_complex (hf.sub hg) hsub t
  rw [Pi.sub_apply, sub_eq_zero] at hzz
  exact hzz

/-- **The fundamental lemma of the calculus of variations, real form.** -/
theorem eq_zero_of_forall_integral_mul_eq_zero {f : ℝ → ℝ} (hf : Continuous f)
    (h : ∀ phi : ℝ → ℝ, Continuous phi → HasCompactSupport phi → ∫ t, phi t * f t = 0) (t : ℝ) :
    f t = 0 := by
  by_contra hne
  obtain ⟨delta, hdelta, hball⟩ := exists_ball_norm_pos hf hne
  set g : ℝ → ℝ := fun s => triangleBump t delta s * (f s * f s) with hg
  have hgcont : Continuous g := (continuous_triangleBump t delta).mul (hf.mul hf)
  have hgsupp : HasCompactSupport g := by
    refine HasCompactSupport.intro (isCompact_Icc (a := t - delta) (b := t + delta)) ?_
    intro s hs
    show triangleBump t delta s * (f s * f s) = 0
    rw [triangleBump_eq_zero_of_notMem t delta hs, zero_mul]
  have hphisupp : HasCompactSupport (fun s => triangleBump t delta s * f s) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := t - delta) (b := t + delta)) ?_
    intro s hs
    show triangleBump t delta s * f s = 0
    rw [triangleBump_eq_zero_of_notMem t delta hs, zero_mul]
  have hzero := h (fun s => triangleBump t delta s * f s)
    ((continuous_triangleBump t delta).mul hf) hphisupp
  have hgeq : ∀ s, triangleBump t delta s * f s * f s = g s := fun s => by rw [hg]; ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hgeq)] at hzero
  have hgpos : 0 < ∫ s, g s := by
    refine integral_pos_of_pos_on_ball (c := t)
      (fun s => mul_nonneg (triangleBump_nonneg t delta s) (mul_self_nonneg _))
      (hgcont.integrable_of_hasCompactSupport hgsupp) hdelta ?_
    intro s hs
    refine mul_pos (triangleBump_pos_of_mem hs) ?_
    have := hball s hs
    exact mul_self_pos.mpr this
  linarith

end TestPairing

end GaloisForLFunctions.HTGeometry
