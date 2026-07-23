import GaloisForLFunctions.RHTower.PrimeBarycentricProjectiveEscape
import GaloisForLFunctions.RHTower.PrimeLogSamplingWeightObstruction

/-!
# Prime barycentric-sampling joint escape universality

The reciprocal-log-square prime tail drives two different observables: projective escape between
canonical prime barycentric coefficients and divergence of the critical shifted-sinc sampling
profile.  Their pointwise minimum still diverges, so neither channel can remain bounded along a
common cofinal scale.
-/

namespace RHTower

open Filter Topology

noncomputable section

/-- Common-scale lower envelope of projective barycentric escape and critical sampling mass. -/
def primeBarycentricSamplingJointEscape (p q : ℕ) (x : ℝ) : ℝ :=
  min (primeBarycentricProjectiveRatio p q x) (primeShiftedSincProfileSum x)

/-- **Joint prime-tail escape law.**  For every pair of distinct ordered prime labels, the lower
envelope of the projective coefficient ratio and shifted-sinc sampling profile tends to infinity. -/
theorem tendsto_primeBarycentricSamplingJointEscape_atTop
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    Tendsto (primeBarycentricSamplingJointEscape p q) atTop atTop := by
  have hprojective :=
    tendsto_primeBarycentricProjectiveRatio_atTop p q hp hq hpq
  have hsampling := tendsto_primeShiftedSincProfileSum_atTop
  rw [tendsto_atTop]
  intro B
  filter_upwards
    [hprojective.eventually (eventually_ge_atTop B),
      hsampling.eventually (eventually_ge_atTop B)] with x hxProjective hxSampling
  exact le_min hxProjective hxSampling

end

end RHTower
