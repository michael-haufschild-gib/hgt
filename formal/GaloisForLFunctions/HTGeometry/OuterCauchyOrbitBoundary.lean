import GaloisForLFunctions.HTGeometry.PerturbedBoundaryRigidity
import GaloisForLFunctions.HTGeometry.StieltjesTranslationCollapse
import GaloisForLFunctions.HTGeometry.ParabolicOrbitCircleClosure
import GaloisForLFunctions.HTGeometry.CayleyOuterFamilyGauge

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

/-! ## The outer background is not constant -/

theorem norm_sub_I_lt_norm_add_I {w : ℂ} (hw : 0 < w.im) : ‖w - Complex.I‖ < ‖w + Complex.I‖ := by
  refine lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) ?_
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply]
  nlinarith

/-- **The Cayley exponential leaves the inner circle.**  On the upper half plane the outer
multiplier has modulus strictly above `exp (-1)`. -/
theorem norm_cayleyOuter_gt {w : ℂ} (hw : 0 < w.im) : Real.exp (-1) < ‖cayleyOuter w‖ := by
  have hne : w + Complex.I ≠ 0 := add_I_ne_zero_of_im_nonneg hw.le
  set zeta : ℂ := (w - Complex.I) / (w + Complex.I) with hzeta
  have hlt : ‖zeta‖ < 1 := by
    rw [hzeta, norm_div, div_lt_one (by positivity)]
    exact norm_sub_I_lt_norm_add_I hw
  have hre : -1 < zeta.re := by
    have hbound := Complex.abs_re_le_norm zeta
    have hneg := neg_abs_le zeta.re
    linarith
  rw [cayleyOuter, Complex.norm_exp, ← hzeta]
  exact Real.exp_lt_exp.mpr hre

theorem outerBackground_ne_const (ν : Measure ℝ) [IsFiniteMeasure ν] (hν : ν ≠ 0) :
    ¬ ∀ z : ℂ, 0 < z.im → outerBackground ν z = Complex.exp (-1) := by
  intro hall
  have hz : (0 : ℝ) < (Complex.I).im := by simp
  have hm := im_cauchyTransform_pos_of_ne_zero ν hν hz
  have hgt : Real.exp (-1) < ‖outerBackground ν Complex.I‖ := norm_cayleyOuter_gt hm
  rw [hall Complex.I hz, Complex.norm_exp] at hgt
  simp at hgt

/-- **The perturbed outer orbit misses its boundary.**  Together with the closure decomposition this
is the disjoint union of equation (12). -/
theorem outerCauchyOrbit_ne_perturbedBoundary [Countable ι] [DecidableEq ι] (ν : Measure ℝ)
    [IsFiniteMeasure ν] (hν : ν ≠ 0) {a : ι → ℂ} {omega : ι → ℝ}
    (h : ExpSeriesNormallySummable a omega) {eps : ℂ} (heps : eps ≠ 0)
    (hane : ∀ i, a i ≠ 0) (hinj : Function.Injective omega) (t : ℝ) (lam : ι → Circle) :
    perturbedOrbit h (outerBackground ν) (continuousOn_outerBackground ν) eps t
      ≠ perturbedBoundary h (Complex.exp (-1)) eps lam :=
  perturbedOrbit_ne_perturbedBoundary h (continuousOn_outerBackground ν) heps hane hinj
    (fun _ hK hKH => tendstoUniformlyOn_outerBackground_translate ν hK hKH)
    (outerBackground_ne_const ν hν) t lam

/-- **The closure of the perturbed outer orbit is a disjoint union.**  This is equation (12). -/
theorem disjoint_range_outerCauchyOrbit [Countable ι] [DecidableEq ι] (ν : Measure ℝ)
    [IsFiniteMeasure ν] (hν : ν ≠ 0) {a : ι → ℂ} {omega : ι → ℝ}
    (h : ExpSeriesNormallySummable a omega) {eps : ℂ} (heps : eps ≠ 0)
    (hane : ∀ i, a i ≠ 0) (hinj : Function.Injective omega) :
    Disjoint (Set.range (perturbedOrbit h (outerBackground ν)
        (continuousOn_outerBackground ν) eps))
      (Set.range (perturbedBoundary h (Complex.exp (-1)) eps)) := by
  rw [Set.disjoint_left]
  rintro g ⟨t, rfl⟩ ⟨lam, hlam⟩
  exact outerCauchyOrbit_ne_perturbedBoundary ν hν h heps hane hinj t lam hlam.symm

end

end GaloisForLFunctions
