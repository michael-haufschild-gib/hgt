import GaloisForLFunctions.HTGeometry.PerturbedOuterOrbitBoundary
import GaloisForLFunctions.HTGeometry.StieltjesTranslationCollapse
import GaloisForLFunctions.HTGeometry.ParabolicOrbitCircleClosure

/-!
# The outer background of a finite Stieltjes mass

The Cayley exponential of the Cauchy transform of a finite positive measure is a bounded outer
background on the upper half plane.  Its horizontal translates collapse to the single value
`exp (-1)` uniformly on compact subsets: the Cauchy transform itself collapses to zero, and the
Cayley exponential is continuous there.

Perturbing this background by a fixed multiple of an exponential carrier therefore produces an orbit
whose closure is the orbit together with the whole phase boundary, and whose limiting time
distribution is Haar measure on that boundary.
-/

open Filter MeasureTheory Set Topology

namespace GaloisForLFunctions

open GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*}

/-- The Cayley exponential: the outer multiplier which sends the upper half plane into the annulus
`exp (-1) < |w| < exp 1`. -/
def cayleyOuter (w : ℂ) : ℂ := Complex.exp ((w - Complex.I) / (w + Complex.I))

@[simp]
theorem cayleyOuter_zero : cayleyOuter 0 = Complex.exp (-1) := by
  rw [cayleyOuter]
  norm_num

theorem add_I_ne_zero_of_im_nonneg {w : ℂ} (hw : 0 ≤ w.im) : w + Complex.I ≠ 0 := by
  intro hzero
  have hw' : w = -Complex.I := by linear_combination hzero
  rw [hw'] at hw
  simp at hw
  linarith

theorem continuousAt_cayleyOuter {w : ℂ} (hw : w + Complex.I ≠ 0) : ContinuousAt cayleyOuter w := by
  refine Complex.continuous_exp.continuousAt.comp ?_
  exact ContinuousAt.div (continuousAt_id.sub continuousAt_const)
    (continuousAt_id.add continuousAt_const) hw

/-- **Uniform convergence composes with a continuous outer function.** -/
theorem tendstoUniformlyOn_comp_continuousAt {α : Type*} {γ : Type*} {l : Filter γ}
    {F : γ → α → ℂ} {c₀ : ℂ} {K : Set α} (hF : TendstoUniformlyOn F (fun _ => c₀) l K)
    {g : ℂ → ℂ} (hg : ContinuousAt g c₀) :
    TendstoUniformlyOn (fun t x => g (F t x)) (fun _ => g c₀) l K := by
  rw [Metric.tendstoUniformlyOn_iff] at hF ⊢
  intro ε hε
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.mp hg ε hε
  filter_upwards [hF δ hδ] with t ht x hx
  have hd : dist (F t x) c₀ < δ := by
    rw [dist_comm]
    exact ht x hx
  rw [dist_comm]
  exact hball hd

/-- The outer background attached to a finite Stieltjes mass. -/
def outerBackground (ν : Measure ℝ) (z : ℂ) : ℂ := cayleyOuter (cauchyTransform ν z)

theorem continuousOn_outerBackground (ν : Measure ℝ) [IsFiniteMeasure ν] :
    ContinuousOn (outerBackground ν) {z : ℂ | 0 < z.im} := by
  refine ContinuousOn.comp (t := {w : ℂ | w + Complex.I ≠ 0}) ?_
    (continuousOn_cauchyTransform_upper ν) ?_
  · intro w hw
    exact (continuousAt_cayleyOuter hw).continuousWithinAt
  · intro z hz
    exact add_I_ne_zero_of_im_nonneg (im_cauchyTransform_nonneg ν hz)

/-- **The outer background collapses to a constant.**  Its horizontal translates converge to
`exp (-1)` uniformly on every compact subset of the upper half plane. -/
theorem tendstoUniformlyOn_outerBackground_translate (ν : Measure ℝ) [IsFiniteMeasure ν]
    {K : Set ℂ} (hK : IsCompact K) (hKH : ∀ z ∈ K, 0 < z.im) :
    TendstoUniformlyOn (fun (t : ℝ) (z : ℂ) => outerBackground ν (z + (t : ℂ)))
      (fun _ => Complex.exp (-1)) (cocompact ℝ) K := by
  have hbase := tendstoUniformlyOn_cauchyTransform_translate_isCompact ν hK hKH
  have hcomp := tendstoUniformlyOn_comp_continuousAt hbase (g := cayleyOuter)
    (continuousAt_cayleyOuter (by simp))
  simpa [outerBackground] using hcomp

/-! ## The perturbed outer orbit -/

/-- **The closure of the perturbed outer orbit.**  Equation (12) for the Cayley exponential of a
finite Stieltjes mass perturbed by a rationally independent exponential carrier. -/
theorem closure_range_outerCauchyOrbit [Countable ι] [DecidableEq ι] (ν : Measure ℝ)
    [IsFiniteMeasure ν] {a : ι → ℂ} {omega : ι → ℝ} (h : ExpSeriesNormallySummable a omega)
    (hindep : RationallyIndependentSequence omega) (eps : ℂ) :
    closure (Set.range (perturbedOrbit h (outerBackground ν)
        (continuousOn_outerBackground ν) eps))
      = Set.range (perturbedOrbit h (outerBackground ν) (continuousOn_outerBackground ν) eps)
        ∪ Set.range (perturbedBoundary h (Complex.exp (-1)) eps) :=
  closure_range_perturbedOrbit h hindep (continuousOn_outerBackground ν)
    fun _ hK hKH => tendstoUniformlyOn_outerBackground_translate ν hK hKH

/-- **The Haar limiting law of the perturbed outer orbit.**  Equation (16) for the same data. -/
theorem tendsto_windowAverage_outerCauchyOrbit [Countable ι] [DecidableEq ι] (ν : Measure ℝ)
    [IsFiniteMeasure ν] {a : ι → ℂ} {omega : ι → ℝ} (h : ExpSeriesNormallySummable a omega)
    (hindep : RationallyIndependentSequence omega) (eps : ℂ)
    {test : C(UpperPlane, ℂ) → ℂ} (htest : UniformContinuous test) :
    Tendsto (windowAverage fun t => test (perturbedOrbit h (outerBackground ν)
        (continuousOn_outerBackground ν) eps t)) atTop
      (nhds (∫ x, test (perturbedBoundary h (Complex.exp (-1)) eps
        (unitTorusHomeomorphCircles ι x)) ∂(torusHaar ι))) :=
  tendsto_windowAverage_perturbedOrbit h hindep (continuousOn_outerBackground ν)
    (fun _ hK hKH => tendstoUniformlyOn_outerBackground_translate ν hK hKH) htest

end

end GaloisForLFunctions
