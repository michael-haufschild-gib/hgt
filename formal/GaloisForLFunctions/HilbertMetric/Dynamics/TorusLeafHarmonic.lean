import GaloisForLFunctions.HilbertMetric.Dynamics.TorusFourierHarmonic
import GaloisForLFunctions.RHTower.Deninger.DeningerParametricTorus

/-!
# Full leafwise harmonic equation for linear torus flows

Continuous test functions with two jointly continuous leaf derivatives
give the usual weak leafwise Laplacian equation. Differentiation under
the integral shows that flow-invariant laws satisfy every such test.
Conversely, characters already determine the entire probability law.
Thus the Fourier classification extends to the full leafwise C² test
space, rather than assuming a density theorem for second derivatives.
-/

open MeasureTheory Filter Topology UnitAddTorus
namespace GaloisForLFunctions.HilbertMetric.Dynamics.TorusHarmonic
open HTGeometry _root_.RHTower
noncomputable section
variable {d : Type*} [Fintype d]

def leafPath (lam : d → ℝ) (f : C(UnitAddTorus d, ℂ)) (x : UnitAddTorus d) (t : ℝ) : ℂ :=
  f (x + deningerTorusFlow lam t)

/-- Actual twice differentiable leaf restrictions, with joint continuity of both derivatives. -/
def LeafC2 (lam : d → ℝ) (f : C(UnitAddTorus d, ℂ)) : Prop :=
  (∀ x, Differentiable ℝ (leafPath lam f x)) ∧
  (∀ x, Differentiable ℝ (deriv (leafPath lam f x))) ∧
  Continuous (fun p : ℝ × UnitAddTorus d => deriv (leafPath lam f p.2) p.1) ∧
  Continuous (fun p : ℝ × UnitAddTorus d => deriv (deriv (leafPath lam f p.2)) p.1)

def leafLaplacian (lam : d → ℝ) (f : C(UnitAddTorus d, ℂ)) (x : UnitAddTorus d) : ℂ :=
  deriv (deriv (leafPath lam f x)) 0

/-- Harmonicity against the full continuous leafwise C² test space. -/
def LeafHarmonic (lam : d → ℝ) (μ : ProbabilityMeasure (UnitAddTorus d)) : Prop :=
  ∀ f : C(UnitAddTorus d, ℂ), LeafC2 lam f →
    (∫ x, leafLaplacian lam f x ∂(μ : Measure (UnitAddTorus d))) = 0

private theorem leafPath_joint_continuous (lam : d → ℝ) (f : C(UnitAddTorus d, ℂ)) :
    Continuous (fun p : ℝ × UnitAddTorus d => leafPath lam f p.2 p.1) :=
  f.continuous.comp (continuous_snd.add ((deningerTorusFlow_continuous lam).comp continuous_fst))

/-- Fourier characters belong to the literal leafwise C² test space. -/
theorem leafC2_mFourier (lam : d → ℝ) (n : d → ℤ) : LeafC2 lam (mFourier n) := by
  let A : ℂ := ((2 * Real.pi * deningerFrequency n lam : ℝ) : ℂ) * Complex.I
  have hd (x : UnitAddTorus d) (t : ℝ) :
      HasDerivAt (leafPath lam (mFourier n) x) (A * leafPath lam (mFourier n) x t) t :=
    characterPath_hasDerivAt lam n x t
  have hfirst (x : UnitAddTorus d) : deriv (leafPath lam (mFourier n) x) =
      fun t => A * leafPath lam (mFourier n) x t := funext fun t => (hd x t).deriv
  have hsecond (x : UnitAddTorus d) : deriv (deriv (leafPath lam (mFourier n) x)) =
      fun t => A * (A * leafPath lam (mFourier n) x t) := by
    funext t
    rw [hfirst, ((hd x t).const_mul A).deriv]
  refine ⟨fun x t => (hd x t).differentiableAt, ?_, ?_, ?_⟩
  · intro x
    rw [hfirst]
    exact fun t => ((hd x t).const_mul A).differentiableAt
  · simp only [hfirst]
    exact continuous_const.mul (leafPath_joint_continuous lam (mFourier n))
  · simp only [hsecond]
    exact continuous_const.mul (continuous_const.mul (leafPath_joint_continuous lam (mFourier n)))

/-- Flow invariance implies the actual Laplacian equation for all leafwise C² tests. -/
theorem leafHarmonic_of_flow_invariant (lam : d → ℝ)
    (μ : ProbabilityMeasure (UnitAddTorus d))
    (hμ : ∀ t : ℝ, flowTranslate lam μ t = μ) : LeafHarmonic lam μ := by
  intro f hf
  have hconstant : (fun t : ℝ => ∫ x, leafPath lam f x t ∂(μ : Measure (UnitAddTorus d))) =
      fun _ => ∫ x, f x ∂(μ : Measure (UnitAddTorus d)) := by
    funext t
    have he := congrArg (fun ν : ProbabilityMeasure (UnitAddTorus d) =>
      ∫ x, f x ∂(ν : Measure (UnitAddTorus d))) (hμ t)
    rw [flowTranslate, ProbabilityMeasure.toMeasure_map,
      integral_map (continuous_id.add continuous_const).aemeasurable
        f.continuous.aestronglyMeasurable] at he
    exact he
  have hfirst (t : ℝ) :
      (∫ x, deriv (leafPath lam f x) t ∂(μ : Measure (UnitAddTorus d))) = 0 := by
    have hd := deningerHasDerivAt_integral (μ := (μ : Measure (UnitAddTorus d)))
      (leafPath_joint_continuous lam f) hf.2.2.1
      (fun s x => (hf.1 x s).hasDerivAt) t
    rw [hconstant] at hd
    exact hd.unique (hasDerivAt_const t _)
  have hzero : (fun t : ℝ => ∫ x, deriv (leafPath lam f x) t
      ∂(μ : Measure (UnitAddTorus d))) = fun _ => (0 : ℂ) := funext hfirst
  have hd := deningerHasDerivAt_integral (μ := (μ : Measure (UnitAddTorus d)))
    hf.2.2.1 hf.2.2.2 (fun t x => (hf.2.1 x t).hasDerivAt) 0
  rw [hzero] at hd
  exact hd.unique (hasDerivAt_const 0 (0 : ℂ))

/-- Testing every leafwise C² function is equivalent to testing only the Fourier characters. -/
theorem leafHarmonic_iff_fourierHarmonic (lam : d → ℝ)
    (μ : ProbabilityMeasure (UnitAddTorus d)) : LeafHarmonic lam μ ↔ FourierHarmonic lam μ := by
  constructor
  · intro h n
    exact h (mFourier n) (leafC2_mFourier lam n)
  · intro h
    exact leafHarmonic_of_flow_invariant lam μ ((fourierHarmonic_iff_flow_invariant lam μ).mp h)

/-- The full weak leaf Laplacian equation is exactly stationarity of the probability law. -/
theorem leafHarmonic_iff_flow_invariant (lam : d → ℝ)
    (μ : ProbabilityMeasure (UnitAddTorus d)) :
    LeafHarmonic lam μ ↔ ∀ t : ℝ, flowTranslate lam μ t = μ := by
  rw [leafHarmonic_iff_fourierHarmonic, fourierHarmonic_iff_flow_invariant]

/-- Prime irrational slope has exactly Haar probability as its full leafwise harmonic measure. -/
theorem prime_leafHarmonic_iff_haar (p : Nat.Primes)
    (μ : ProbabilityMeasure (UnitAddTorus (Fin 2))) :
    LeafHarmonic (primeVelocity p) μ ↔ μ = finiteTorusHaarProbabilityMeasure (Fin 2) := by
  rw [leafHarmonic_iff_fourierHarmonic, prime_fourierHarmonic_iff_haar]

#print axioms leafC2_mFourier
#print axioms leafHarmonic_of_flow_invariant
#print axioms leafHarmonic_iff_fourierHarmonic
#print axioms leafHarmonic_iff_flow_invariant
#print axioms prime_leafHarmonic_iff_haar
end
end GaloisForLFunctions.HilbertMetric.Dynamics.TorusHarmonic
