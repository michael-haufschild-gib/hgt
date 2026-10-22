import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingPreDivisorOpticalCancellationMeromorphicRemovability

/-!
# Optical cancellation on the meromorphic regular locus

HC75 excludes an everywhere-equal meromorphic scalar cancellation profile. Here pole values are
left completely unconstrained: equality is required only where the response is analytic.

For a meromorphic `f` and continuous profile `p`, retain `f` on its analytic locus and insert `p`
elsewhere. Meromorphic germs are analytic on a punctured neighbourhood, so this regularization has
the same punctured germ as `f`. It is also locally equal to `p`, hence continuous. Every singularity
is therefore removable. Applied to HC74's nonholomorphic optical profile, this excludes genuine
isolated Green/QNM poles as a scalar escape.
-/

open Complex Set Filter Topology

namespace RHTower

noncomputable section

/-- Canonical regularization of a meromorphic response against a prescribed profile: retain the
response precisely on its analytic locus and insert the profile at all other points. -/
def meromorphicAnalyticLocusRegularization (f p : ℂ → ℂ) (z : ℂ) : ℂ :=
  by
    classical
    exact if AnalyticAt ℂ f z then f z else p z

/-- If a response agrees with a profile at every analytic point in `U`, its analytic-locus
regularization agrees with the profile everywhere in `U`, including at arbitrary pole values. -/
theorem meromorphicAnalyticLocusRegularization_eq_profile
    (U : Set ℂ) (f p : ℂ → ℂ)
    (hregular : ∀ z ∈ U, AnalyticAt ℂ f z → f z = p z) :
    Set.EqOn (meromorphicAnalyticLocusRegularization f p) p U := by
  intro z hz
  by_cases han : AnalyticAt ℂ f z
  · simp [meromorphicAnalyticLocusRegularization, han, hregular z hz han]
  · simp [meromorphicAnalyticLocusRegularization, han]

/-- General simultaneous-removability law. On an open set, a meromorphic response agreeing with a
continuous profile throughout its analytic locus has a canonical regularization analytic at every
point. No finiteness or enumeration of the pole set is needed. -/
theorem analyticOnNhd_meromorphicAnalyticLocusRegularization
    (U : Set ℂ) (hU : IsOpen U) (f p : ℂ → ℂ)
    (hf : MeromorphicOn f U)
    (hp : ContinuousOn p U)
    (hregular : ∀ z ∈ U, AnalyticAt ℂ f z → f z = p z) :
    AnalyticOnNhd ℂ (meromorphicAnalyticLocusRegularization f p) U := by
  have heqOn : Set.EqOn (meromorphicAnalyticLocusRegularization f p) p U :=
    meromorphicAnalyticLocusRegularization_eq_profile U f p hregular
  intro z hz
  have hfg : f =ᶠ[𝓝[≠] z] meromorphicAnalyticLocusRegularization f p := by
    filter_upwards [(hf z hz).eventually_analyticAt] with w hw
    simp [meromorphicAnalyticLocusRegularization, hw]
  have hmeromorphic : MeromorphicAt (meromorphicAnalyticLocusRegularization f p) z :=
    (hf z hz).congr hfg
  apply hmeromorphic.analyticAt
  have heq : meromorphicAnalyticLocusRegularization f p =ᶠ[𝓝 z] p := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact heqOn hw
  rw [continuousAt_congr heq]
  exact (hp z hz).continuousAt (hU.mem_nhds hz)

/-- No meromorphic scalar response on the open critical strip can track the exact pre-divisor
optical-cancellation susceptibility merely on its analytic locus. Values at genuine poles are
unconstrained: canonical regularization removes them and contradicts HC74. -/
theorem not_exists_meromorphic_regularLocus_preDivisorOpticalCancellationSusceptibility :
    ¬ ∃ f : ℂ → ℂ,
      MeromorphicOn f {z : ℂ | 0 < z.re ∧ z.re < 1} ∧
        ∀ z : ℂ, z ∈ {z : ℂ | 0 < z.re ∧ z.re < 1} →
          AnalyticAt ℂ f z →
            f z = (d4PreDivisorOpticalCancellationSusceptibility z.re : ℂ) := by
  rintro ⟨f, hmeromorphic, hregular⟩
  let p : ℂ → ℂ := fun z =>
    (d4PreDivisorOpticalCancellationSusceptibility z.re : ℂ)
  let g : ℂ → ℂ := meromorphicAnalyticLocusRegularization f p
  apply not_exists_holomorphic_preDivisorOpticalCancellationSusceptibility
  refine ⟨g, ?_, ?_⟩
  · exact analyticOnNhd_meromorphicAnalyticLocusRegularization
      {z : ℂ | 0 < z.re ∧ z.re < 1} isOpen_criticalOpenStrip f p
      hmeromorphic
      (by
        intro z hz
        exact
          (continuousAt_d4PreDivisorOpticalCancellationSusceptibility_re z hz).continuousWithinAt)
      (by
        intro z hz han
        exact hregular z hz han)
  · intro z hz
    change meromorphicAnalyticLocusRegularization f p z = p z
    exact meromorphicAnalyticLocusRegularization_eq_profile
      {z : ℂ | 0 < z.re ∧ z.re < 1} f p hregular hz

end

end RHTower
