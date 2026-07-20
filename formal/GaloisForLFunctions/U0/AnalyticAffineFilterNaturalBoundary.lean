import GaloisForLFunctions.U0.U0NaturalBoundary

/-!
# Analytic affine filters preserve a genuine natural boundary

An affine signal filter `f ↦ a * f + b` with analytic feedthrough `b` and analytic nonzero gain
`a` cannot remove a local analytic-continuation obstruction.  Indeed, a continuation of the filtered
signal would recover a continuation of `f` by the analytic inverse filter `(g - b) / a`.

Applied to the dyadic Mahler source `u₀`, any analytic affine filter whose gain is nonzero on the
unit circle preserves the full natural boundary.  Finite rational transfer functions regular and
nonzero on the circle are a special case.  This is a source-extraction law, not a claim that a
filter constructs hypertranscendence.
-/

open Filter Topology
open U0NaturalBoundary

namespace U0

/-- A continuation of an analytically affine-filtered signal, with nonzero local gain, recovers a
continuation of the original signal. -/
theorem continuesAcross_of_continuesAcross_analyticAffine
    {f a b : ℂ → ℂ} {D : Set ℂ} {z₀ : ℂ}
    (ha : AnalyticAt ℂ a z₀) (hb : AnalyticAt ℂ b z₀) (ha0 : a z₀ ≠ 0)
    (hfilter : ContinuesAcross (fun z => a z * f z + b z) D z₀) :
    ContinuesAcross f D z₀ := by
  obtain ⟨g, hg, hgeq⟩ := hfilter
  refine ⟨fun z => (g z - b z) / a z, (hg.sub hb).div ha ha0, ?_⟩
  have hane : ∀ᶠ z in 𝓝 z₀, a z ≠ 0 :=
    ha.continuousAt.eventually_ne ha0
  filter_upwards [hgeq, hane.filter_mono nhdsWithin_le_nhds] with z hgz haz
  rw [hgz]
  field_simp
  ring

/-- Contrapositive source-extraction form: a locally invertible analytic affine filter preserves a
failure of analytic continuation. -/
theorem not_continuesAcross_analyticAffine_of_not_continuesAcross
    {f a b : ℂ → ℂ} {D : Set ℂ} {z₀ : ℂ}
    (ha : AnalyticAt ℂ a z₀) (hb : AnalyticAt ℂ b z₀) (ha0 : a z₀ ≠ 0)
    (hf : ¬ ContinuesAcross f D z₀) :
    ¬ ContinuesAcross (fun z => a z * f z + b z) D z₀ := by
  intro hfilter
  exact hf (continuesAcross_of_continuesAcross_analyticAffine ha hb ha0 hfilter)

/-- Every analytic affine filter with gain nonzero on the unit circle preserves the complete
natural boundary of the dyadic Mahler source `u₀`. -/
theorem u0_analyticAffineFilter_naturalBoundary
    {a b : ℂ → ℂ}
    (ha : ∀ z : ℂ, ‖z‖ = 1 → AnalyticAt ℂ a z)
    (hb : ∀ z : ℂ, ‖z‖ = 1 → AnalyticAt ℂ b z)
    (ha0 : ∀ z : ℂ, ‖z‖ = 1 → a z ≠ 0) :
    ∀ z₀ : ℂ, ‖z₀‖ = 1 →
      ¬ ContinuesAcross (fun z => a z * u0 z + b z) Ext z₀ := by
  intro z₀ hz₀
  exact not_continuesAcross_analyticAffine_of_not_continuesAcross
    (ha z₀ hz₀) (hb z₀ hz₀) (ha0 z₀ hz₀) (u0_natural_boundary z₀ hz₀)

end U0
