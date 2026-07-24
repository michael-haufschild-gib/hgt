/-
The compact Thorin exponent and compact Markov germ interfaces carry identical information.

Differentiating a Thorin exponent gives its Markov transform.  Conversely, local equality of the
completed source moment germ with a compact Markov transform identifies the derivatives of the
normalized source logarithm and the corresponding Thorin exponent.  Both primitives vanish at
the origin, so derivative uniqueness on a small complex ball recovers the exponent identity.
-/
import GaloisForLFunctions.RHTower.CompletedSeamCompactThorinExponentCapstone

open Complex Filter MeasureTheory Metric Set Topology

namespace RHTower

noncomputable section

/-- A compact Markov germ integrates to the normalized completed-source Thorin exponent. -/
theorem primeArchCompactThorinExponentRepresentation_of_compactMarkovGerm
    (hrep : PrimeArchCompactMarkovGermRepresentation) :
    PrimeArchCompactThorinExponentRepresentation := by
  obtain ⟨μ, B, hfinite, hB, hsupport, hgerm⟩ := hrep
  letI : IsFiniteMeasure μ := hfinite
  have hbound : ∀ᵐ x : ℝ ∂μ, |x| ≤ B := hsupport.mono fun _ hx => hx.2
  have hratioCont : ContinuousAt (fun z : ℂ =>
      xiSquaredSeamCassiniSource (1 + z) /
        xiSquaredSeamCassiniSource 1) 0 := by
    have hshift : ContinuousAt (fun z : ℂ =>
        xiSquaredSeamCassiniSource (1 + z)) 0 :=
      differentiable_xiSquaredSeamCassiniSource.continuous.continuousAt.comp
        (continuousAt_const.add continuousAt_id)
    exact hshift.div_const _
  have hslit : ∀ᶠ z : ℂ in 𝓝 0,
      xiSquaredSeamCassiniSource (1 + z) /
        xiSquaredSeamCassiniSource 1 ∈ Complex.slitPlane := by
    have hratio0 : xiSquaredSeamCassiniSource (1 + (0 : ℂ)) /
        xiSquaredSeamCassiniSource 1 = 1 := by
      simp [xiSquaredSeamCassiniSource_one_ne]
    have hmem : xiSquaredSeamCassiniSource (1 + (0 : ℂ)) /
        xiSquaredSeamCassiniSource 1 ∈ Complex.slitPlane := by
      rw [hratio0]
      exact Complex.one_mem_slitPlane
    exact hratioCont.eventually (Complex.isOpen_slitPlane.mem_nhds hmem)
  have hdisk : ∀ᶠ z : ℂ in 𝓝 0, ‖z‖ < 1 / (2 * B) :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds
      (by simpa using (show (0 : ℝ) < 1 / (2 * B) by positivity))
  have hthorin : deriv (compactThorinExponent μ) =ᶠ[𝓝 0]
      compactMarkovTransform μ := by
    filter_upwards [hdisk] with z hz
    exact (hasDerivAt_compactThorinExponent μ hB hbound hz).deriv
  have hderiv : deriv completedSeamSourceLogExponent =ᶠ[𝓝 0]
      deriv (compactThorinExponent μ) :=
    deriv_completedSeamSourceLogExponent_eventuallyEq_momentGerm.trans
      (hgerm.trans hthorin.symm)
  have hlocal : ∀ᶠ z : ℂ in 𝓝 0,
      (xiSquaredSeamCassiniSource (1 + z) /
          xiSquaredSeamCassiniSource 1 ∈ Complex.slitPlane) ∧
        ‖z‖ < 1 / (2 * B) ∧
        deriv completedSeamSourceLogExponent z =
          deriv (compactThorinExponent μ) z := by
    filter_upwards [hslit, hdisk, hderiv] with z hzslit hz hdz
    exact ⟨hzslit, hz, hdz⟩
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hlocal
  have hsourceDiff :
      DifferentiableOn ℂ completedSeamSourceLogExponent (Metric.ball 0 r) := by
    intro z hz
    have hzlocal := hball (Metric.mem_ball.mp hz)
    exact (hasDerivAt_completedSeamSourceLogExponent hzlocal.1).differentiableAt
      |>.differentiableWithinAt
  have hthorinDiff :
      DifferentiableOn ℂ (compactThorinExponent μ) (Metric.ball 0 r) := by
    intro z hz
    have hzlocal := hball (Metric.mem_ball.mp hz)
    exact (hasDerivAt_compactThorinExponent μ hB hbound hzlocal.2.1).differentiableAt
      |>.differentiableWithinAt
  have hderivOn : Set.EqOn (deriv completedSeamSourceLogExponent)
      (deriv (compactThorinExponent μ)) (Metric.ball 0 r) := by
    intro z hz
    exact (hball (Metric.mem_ball.mp hz)).2.2
  have hsourceZero : completedSeamSourceLogExponent 0 = 0 := by
    simp [completedSeamSourceLogExponent, xiSquaredSeamCassiniSource_one_ne]
  have hthorinZero : compactThorinExponent μ 0 = 0 := by
    simp [compactThorinExponent, compactThorinLogKernel]
  have heqOn : Set.EqOn completedSeamSourceLogExponent
      (compactThorinExponent μ) (Metric.ball 0 r) :=
    Metric.isOpen_ball.eqOn_of_deriv_eq (convex_ball 0 r).isPreconnected
      hsourceDiff hthorinDiff hderivOn
      (Metric.mem_ball_self hr) (hsourceZero.trans hthorinZero.symm)
  refine ⟨μ, B, hfinite, hB, hsupport, ?_⟩
  filter_upwards [Metric.ball_mem_nhds 0 hr] with z hz
  exact heqOn hz

/-- Compact Thorin exponent representation is exactly compact Markov germ representation. -/
theorem primeArchCompactThorinExponentRepresentation_iff_compactMarkovGerm :
    PrimeArchCompactThorinExponentRepresentation ↔
      PrimeArchCompactMarkovGermRepresentation :=
  ⟨primeArchCompactMarkovGermRepresentation_of_compactThorinExponent,
    primeArchCompactThorinExponentRepresentation_of_compactMarkovGerm⟩

end

end RHTower
