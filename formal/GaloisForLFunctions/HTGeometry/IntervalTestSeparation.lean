import GaloisForLFunctions.HTGeometry.SchwartzCompactSupport
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Test functions separate continuous functions on an interval

A function continuous on a compact interval whose integral against every Schwartz test function
supported in the open interval vanishes is identically zero there.  This is the fundamental lemma of
the calculus of variations in the form needed to pin down the vector in a distributional
representation.
-/

open Set MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- **Test functions separate continuous functions on an interval.** -/
theorem eq_zero_of_forall_test_integral_zero {G : ℝ → X} {a b : ℝ} (hab : a < b)
    (hG : ContinuousOn G (Icc a b))
    (h : ∀ φ : SchwartzMap ℝ ℂ, (∀ x, x ∉ Ioo a b → (φ : ℝ → ℂ) x = 0) →
      (∫ t in a..b, ((φ : ℝ → ℂ) t) • G t) = 0) :
    ∀ t ∈ Ioo a b, G t = 0 := by
  have hloc : LocallyIntegrableOn G (Ioo a b) volume :=
    (hG.mono Ioo_subset_Icc_self).locallyIntegrableOn measurableSet_Ioo
  have hae : ∀ᵐ x : ℝ, x ∈ Ioo a b → G x = 0 := by
    refine isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc ?_
    intro g hgd hgcs hgsupp
    have hgzero : ∀ x, x ∉ Ioo a b → g x = 0 := fun x hx =>
      image_eq_zero_of_notMem_tsupport fun hc => hx (hgsupp hc)
    have hcdC : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => ((g x : ℂ))) :=
      Complex.ofRealCLM.contDiff.comp hgd
    have hcsC : HasCompactSupport (fun x : ℝ => ((g x : ℂ))) :=
      hgcs.comp_left (g := fun z : ℝ => ((z : ℂ))) Complex.ofReal_zero
    set φ : SchwartzMap ℝ ℂ := schwartzOfCompactSupport hcdC hcsC with hφ
    have hφsupp : ∀ x, x ∉ Ioo a b → (φ : ℝ → ℂ) x = 0 := by
      intro x hx
      show ((g x : ℂ)) = 0
      rw [hgzero x hx, Complex.ofReal_zero]
    have hzero : ∀ x ∉ Ioc a b, g x • G x = 0 := by
      intro x hx
      rw [hgzero x fun hc => hx (Ioo_subset_Ioc_self hc), zero_smul]
    have hpt : ∀ x : ℝ, ((φ : ℝ → ℂ) x) • G x = g x • G x := by
      intro x
      show ((g x : ℂ)) • G x = g x • G x
      rw [← Complex.coe_algebraMap, algebraMap_smul]
    have hcongr : (∫ t in a..b, ((φ : ℝ → ℂ) t) • G t) = ∫ x : ℝ, g x • G x := by
      rw [intervalIntegral.integral_of_le hab.le]
      simp only [hpt]
      exact MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero
    rw [← hcongr]
    exact h φ hφsupp
  intro t ht
  by_contra hne
  have hIccmem : Icc a b ∈ nhds t := by
    refine Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht) Ioo_subset_Icc_self
  have hcont : ContinuousAt G t := hG.continuousAt hIccmem
  have hnhds : ∀ᶠ x in nhds t, x ∈ Ioo a b ∧ G x ≠ 0 := by
    have h1 : ∀ᶠ x in nhds t, G x ≠ 0 := hcont (isOpen_ne.mem_nhds hne)
    have h2 : ∀ᶠ x in nhds t, x ∈ Ioo a b := isOpen_Ioo.mem_nhds ht
    exact h2.and h1
  obtain ⟨ε, hεpos, hball⟩ := Metric.eventually_nhds_iff.mp hnhds
  have hsubset : Metric.ball t ε ⊆ {x : ℝ | ¬(x ∈ Ioo a b → G x = 0)} := by
    intro x hx
    have := hball (Metric.mem_ball.mp hx)
    intro hcon
    exact this.2 (hcon this.1)
  have hmeas : volume {x : ℝ | ¬(x ∈ Ioo a b → G x = 0)} = 0 := MeasureTheory.ae_iff.mp hae
  have hpos : 0 < volume (Metric.ball t ε) := Metric.measure_ball_pos volume t hεpos
  have hle := measure_mono (μ := volume) hsubset
  rw [hmeas] at hle
  have hzeroball : volume (Metric.ball t ε) = 0 := le_antisymm hle (by simp)
  exact absurd hzeroball (ne_of_gt hpos)

end

end GaloisForLFunctions.HTGeometry
