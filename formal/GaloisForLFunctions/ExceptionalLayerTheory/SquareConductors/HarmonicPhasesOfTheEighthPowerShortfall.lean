import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheGcdDeficitAtTheEighthPowerEndpoints
import GaloisForLFunctions.RHTower.GaussComponentPhaseResidue

/-!
# Harmonic phases of paired eighth-power shortfalls

The cumulative readings at n and n^q have one common logarithmic
frequency. Every nonresonant linear combination is Haar distributed on
the circle under harmonic sampling. Every resonant combination instead
converges to a single phase fixed by the arithmetic finite part.
-/

noncomputable section
open Filter Finset MeasureTheory
open scoped Topology
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private abbrev D := powerGridGcdDeficit 8
private abbrev Circle := AddCircle (1:ℝ)

/-- Linear combination of two cumulative readings at linked endpoints. -/
def pairedEighthPhase (q : ℕ) (u v : ℝ) (m : ℕ) := u*D m + v*D (m^q)

private theorem uniform_test_error {x y : ℕ → ℝ}
    (h : Tendsto (fun n => x n-y n) atTop (𝓝 0)) (f : C(Circle,ℂ)) :
    Tendsto (fun n => f (x n : Circle)-f (y n : Circle)) atTop (𝓝 0) := by
  have hcircle : Tendsto (fun n => (x n : Circle)-(y n : Circle)) atTop (𝓝 0) := by
    simpa only [AddCircle.coe_sub,AddCircle.coe_zero] using
      (AddCircle.continuous_mk' (1:ℝ)).continuousAt.tendsto.comp h
  apply Metric.tendsto_nhds.mpr
  intro ε ep
  obtain ⟨δ,dp,test⟩ := Metric.uniformContinuous_iff.mp f.continuous.uniformContinuous ε ep
  filter_upwards [Metric.tendsto_nhds.mp hcircle δ dp] with n hn
  rw [dist_zero_right,←dist_eq_norm] at hn ⊢
  exact test hn

/-- A vanishing real phase error preserves all harmonically sampled
continuous circle tests of a logarithmic rotation. -/
theorem perturbed_logarithmic_circle_sampling {x : ℕ → ℝ} {β θ : ℝ}
    (h : Tendsto (fun n : ℕ => x n-(β*Real.log ((n:ℝ)+1)+θ)) atTop (𝓝 0))
    (f : C(Circle,ℂ)) :
    Tendsto (fun N : ℕ => (Real.log N)⁻¹ •
        (∑ n ∈ range N, ((n:ℝ)+1)⁻¹ • f (x n : Circle)) -
      harmonicLogCircleAverage β θ f N) atTop (𝓝 0) := by
  have err := tendsto_complexHarmonicWeighted_error_zero (uniform_test_error h f)
  apply err.congr
  intro N
  rw [_root_.RHTower.harmonicLogCircleAverage_eq_smul,←smul_sub,←sum_sub_distrib]
  exact congrArg _ (sum_congr rfl (fun n _ => smul_sub ..))

private theorem paired_finite_part {c : ℝ}
    (hc : Tendsto (fun n : ℕ => D n-(1/2)*Real.log n) atTop (𝓝 c))
    {q : ℕ} (hq : 0 < q) (u v : ℝ) :
    Tendsto (fun n : ℕ => pairedEighthPhase q u v n - ((u+v*q)/2)*Real.log n)
      atTop (𝓝 ((u+v)*c)) := by
  have ht : Tendsto (fun n : ℕ => n^q) atTop atTop := tendsto_pow_atTop hq.ne'
  have h := (hc.const_mul u).add ((hc.comp ht).const_mul v)
  rw [←add_mul] at h
  exact h.congr fun n => by
    change u*(D n-1/2*Real.log n)+v*(D (n^q)-1/2*Real.log (n^q:ℕ))=_
    rw [Nat.cast_pow,Real.log_pow]
    dsimp only [pairedEighthPhase]
    ring

/-- A common finite part controls every pair of power dilations. On
resonance the unwrapped real phase itself converges. Off resonance its
harmonic empirical measure tends to Haar for every continuous test. -/
theorem paired_eighth_phase_resonance :
    ∃ c : ℝ, ∀ q : ℕ, 0 < q → ∀ u v : ℝ,
      (u+v*q=0 → Tendsto (pairedEighthPhase q u v) atTop (𝓝 ((u+v)*c))) ∧
      (u+v*q≠0 → ∀ f : C(Circle,ℂ), Tendsto (fun N : ℕ =>
        (Real.log N)⁻¹ • ∑ n ∈ range N, ((n:ℝ)+1)⁻¹ •
          f ((pairedEighthPhase q u v (n+1):ℝ) : Circle))
        atTop (𝓝 (∫ t, f t ∂unitCircleHaar))) := by
  obtain ⟨c,hc⟩ := eighth_gcd_deficit_centered_converges
  refine ⟨c,fun q qp u v => ?_⟩
  have h := paired_finite_part hc qp u v
  constructor
  · intro hz
    simpa only [hz,zero_div,zero_mul,sub_zero] using h
  · intro hz f
    let β := (u+v*q)/2
    let θ := (u+v)*c
    have e := ((h.comp (tendsto_add_atTop_nat 1)).sub_const θ)
    rw [show (u+v)*c-θ=0 by exact sub_self _] at e
    have he : Tendsto (fun n : ℕ => pairedEighthPhase q u v (n+1)-
        (β*Real.log ((n:ℝ)+1)+θ)) atTop (𝓝 0) := by
      apply e.congr
      intro n
      change (pairedEighthPhase q u v (n+1)-β*Real.log ((n+1:ℕ):ℝ))-θ=_
      rw [Nat.cast_succ]; ring
    have avg := harmonicLogCircleAverage_tendsto_haar β θ (div_ne_zero hz (by norm_num)) f
    have tot := (perturbed_logarithmic_circle_sampling he f).add avg
    simpa only [sub_add_cancel,zero_add] using tot

#print axioms perturbed_logarithmic_circle_sampling
#print axioms paired_eighth_phase_resonance

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
