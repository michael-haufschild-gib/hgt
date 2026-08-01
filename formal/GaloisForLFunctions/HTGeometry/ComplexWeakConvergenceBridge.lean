import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.RCLike.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Testing weak convergence against a complex integrand

Weak convergence of probability measures is stated in mathlib against bounded continuous
*real-valued* test functions.  Herglotz transforms are tested against complex kernels, so the two
have to be bridged.

The bridge is elementary and needs nothing from the measures: a complex limit is determined by the
limits of its real and imaginary parts, and the Bochner integral commutes with taking real and
imaginary parts of an integrable complex integrand.  Feeding the real theorem into these two facts
turns real weak convergence into convergence of the complex transform.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

/-- **A complex limit is determined by its real and imaginary parts.** -/
theorem tendsto_complex_of_re_im {ι : Type*} {l : Filter ι} {f : ι → ℂ} {z : ℂ}
    (hre : Tendsto (fun i => (f i).re) l (𝓝 z.re))
    (him : Tendsto (fun i => (f i).im) l (𝓝 z.im)) :
    Tendsto f l (𝓝 z) := by
  have hcastre : Tendsto (fun i => (((f i).re : ℝ) : ℂ)) l (𝓝 ((z.re : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp hre
  have hcastim : Tendsto (fun i => (((f i).im : ℝ) : ℂ)) l (𝓝 ((z.im : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp him
  have hsum := hcastre.add (hcastim.mul (tendsto_const_nhds (x := Complex.I)))
  rw [Complex.re_add_im] at hsum
  exact hsum.congr fun i => Complex.re_add_im (f i)

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Weak convergence tested against a complex integrand.**  If the real and imaginary parts of a
complex integrand have convergent integrals, so does the integrand. -/
theorem tendsto_integral_complex_of_re_im {ι : Type*} {l : Filter ι}
    {mu : ι → Measure Ω} {mu0 : Measure Ω} {F : Ω → ℂ}
    (hint : ∀ i, Integrable F (mu i)) (hint0 : Integrable F mu0)
    (hre : Tendsto (fun i => ∫ x, (F x).re ∂(mu i)) l (𝓝 (∫ x, (F x).re ∂mu0)))
    (him : Tendsto (fun i => ∫ x, (F x).im ∂(mu i)) l (𝓝 (∫ x, (F x).im ∂mu0))) :
    Tendsto (fun i => ∫ x, F x ∂(mu i)) l (𝓝 (∫ x, F x ∂mu0)) := by
  refine tendsto_complex_of_re_im ?_ ?_
  · have hrw : ∀ i, (∫ x, F x ∂(mu i)).re = ∫ x, (F x).re ∂(mu i) := by
      intro i
      simpa using (integral_re (hint i)).symm
    have hrw0 : (∫ x, F x ∂mu0).re = ∫ x, (F x).re ∂mu0 := by
      simpa using (integral_re hint0).symm
    rw [hrw0]
    exact hre.congr fun i => (hrw i).symm
  · have hrw : ∀ i, (∫ x, F x ∂(mu i)).im = ∫ x, (F x).im ∂(mu i) := by
      intro i
      simpa using (integral_im (hint i)).symm
    have hrw0 : (∫ x, F x ∂mu0).im = ∫ x, (F x).im ∂mu0 := by
      simpa using (integral_im hint0).symm
    rw [hrw0]
    exact him.congr fun i => (hrw i).symm

/-! ## Weak convergence on a compact space -/

section Compact

variable {Ω : Type*} [TopologicalSpace Ω] [CompactSpace Ω] [MeasurableSpace Ω]
  [OpensMeasurableSpace Ω]

/-- **On a compact space weak convergence tests every continuous real function.**  Compactness
turns a continuous function into a bounded continuous one, which is what mathlib's weak-convergence
theorem consumes. -/
theorem tendsto_integral_real_of_compact {ι : Type*} {l : Filter ι}
    {nu : ι → ProbabilityMeasure Ω} {nu0 : ProbabilityMeasure Ω}
    (h : Tendsto nu l (𝓝 nu0)) (f : C(Ω, ℝ)) :
    Tendsto (fun i => ∫ x, f x ∂(nu i : Measure Ω)) l
      (𝓝 (∫ x, f x ∂(nu0 : Measure Ω))) := by
  have hbc := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp h)
    (BoundedContinuousFunction.mkOfCompact f)
  simpa using hbc

/-- **Weak convergence on a compact space tests every continuous complex function.**  This is the
form in which a Herglotz transform is tested against its kernel. -/
theorem tendsto_integral_complex_of_compact {ι : Type*} {l : Filter ι}
    {nu : ι → ProbabilityMeasure Ω} {nu0 : ProbabilityMeasure Ω}
    (h : Tendsto nu l (𝓝 nu0)) (F : C(Ω, ℂ)) :
    Tendsto (fun i => ∫ x, F x ∂(nu i : Measure Ω)) l
      (𝓝 (∫ x, F x ∂(nu0 : Measure Ω))) := by
  have hint : ∀ mu : Measure Ω, IsFiniteMeasure mu → Integrable (fun x => F x) mu := by
    intro mu hmu
    exact (BoundedContinuousFunction.mkOfCompact F).integrable mu
  refine tendsto_integral_complex_of_re_im (fun i => hint _ inferInstance)
    (hint _ inferInstance) ?_ ?_
  · exact tendsto_integral_real_of_compact h
      ⟨fun x => (F x).re, Complex.continuous_re.comp F.continuous⟩
  · exact tendsto_integral_real_of_compact h
      ⟨fun x => (F x).im, Complex.continuous_im.comp F.continuous⟩

end Compact

end GaloisForLFunctions.HTGeometry
