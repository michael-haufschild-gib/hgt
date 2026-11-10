import GaloisForLFunctions.RHTower.LandauRelativeRigidity
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Analytic.Uniqueness

/-! A positive Dirichlet series cannot have a convergence boundary where
an analytic cleared denominator stays nonzero on the real axis. -/

open Complex Filter Topology Set Metric
open GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations

/-- A cleared analytic identity and real nonvanishing of its denominator
force convergence throughout the corresponding half-plane. Complex zeros
of the denominator do not obstruct this conclusion. -/
theorem summable_of_cleared_identity {ι : Type*} {a lam : ι → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hlam : ∀ j, 0 ≤ lam j)
    {σ₁ c : ℝ} (hsum : Summable (gdTwistTerm a lam σ₁ 0))
    {P N : ℂ → ℂ}
    (hP : AnalyticOnNhd ℂ P {s : ℂ | c < s.re})
    (hN : AnalyticOnNhd ℂ N {s : ℂ | c < s.re})
    (hPne : ∀ t : ℝ, c < t → P (t : ℂ) ≠ 0)
    (hagree : ∀ s : ℂ, σ₁ < s.re → P s * gdSeries a lam s = N s)
    {σ : ℝ} (hσ : c < σ) : Summable (gdTwistTerm a lam σ 0) := by
  classical
  by_contra hnot
  let S : Set ℝ := {t | Summable (gdTwistTerm a lam t 0)}
  have hSne : S.Nonempty := ⟨σ₁, hsum⟩
  have hbelow : ∀ t ∈ S, σ ≤ t := by
    intro t ht
    by_contra h
    exact hnot (summable_gdTwistTerm_of_le ha hlam ht (le_of_not_ge h))
  have hSbdd : BddBelow S := ⟨σ, hbelow⟩
  let σc : ℝ := sInf S
  have hσc : σ ≤ σc := le_csInf hSne hbelow
  have hcσc : c < σc := hσ.trans_le hσc
  have hσc₁ : σc ≤ σ₁ := csInf_le hSbdd hsum
  have hright : ∀ t : ℝ, σc < t → Summable (gdTwistTerm a lam t 0) := by
    intro t ht
    have hex : ∃ r ∈ S, r < t := by
      by_contra h
      push Not at h
      have hh : t ≤ σc := le_csInf hSne h
      exact (not_le_of_gt ht) hh
    obtain ⟨r, hr, hrt⟩ := hex
    exact summable_gdTwistTerm_of_le ha hlam hr hrt.le
  have hleft : ∀ t : ℝ, t < σc → ¬ Summable (gdTwistTerm a lam t 0) := by
    intro t ht hts
    exact (not_le_of_gt ht) (csInf_le hSbdd hts)
  have hDdiff : DifferentiableOn ℂ (gdSeries a lam) {s : ℂ | σc < s.re} := by
    intro s hs
    change σc < s.re at hs
    have hmid : σc < (σc + s.re) / 2 := by linarith only [hs]
    exact (_root_.RHTower.differentiableAt_gdSeries ha hlam
      (hright _ hmid) (by linarith only [hs])).differentiableWithinAt
  have hD := hDdiff.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)
  have hsub : {s : ℂ | σc < s.re} ⊆ {s : ℂ | c < s.re} :=
    fun s hs => hcσc.trans hs
  have hid : EqOn (fun s => P s * gdSeries a lam s) N {s : ℂ | σc < s.re} := by
    apply ((hP.mono hsub).mul hD).eqOn_of_preconnected_of_eventuallyEq (hN.mono hsub)
      (convex_halfSpace_re_gt σc).isPreconnected (z₀ := ((σ₁ + 1 : ℝ) : ℂ))
    · simp only [mem_setOf_eq, Complex.ofReal_re]
      linarith only [hσc₁]
    · filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show σ₁ < (((σ₁ + 1 : ℝ) : ℂ)).re by simp)] with s hs
      exact hagree s hs
  have hPc : AnalyticAt ℂ P (σc : ℂ) := hP _ hcσc
  have hNc : AnalyticAt ℂ N (σc : ℂ) := hN _ hcσc
  have hfrac : AnalyticAt ℂ (fun s => N s / P s) (σc : ℂ) :=
    hNc.div hPc (hPne σc hcσc)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (hfrac.eventually_analyticAt.and (hPc.continuousAt.eventually_ne (hPne σc hcσc)))
  apply _root_.RHTower.gdSeries_no_continuation_at_abscissa ha hlam hright hleft hr
    (G := fun s => N s / P s)
  · intro s hs
    exact (hball hs).1.differentiableAt.differentiableWithinAt
  · intro s hs hsr
    apply (div_eq_iff (hball hs).2).mpr
    simpa only [mul_comm] using (hid hsr).symm

#print axioms summable_of_cleared_identity
end GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations
