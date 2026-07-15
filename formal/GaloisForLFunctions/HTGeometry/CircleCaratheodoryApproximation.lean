import GaloisForLFunctions.HTGeometry.BernsteinSzegoProbabilityApproximation
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Circle Carathéodory transforms of the canonical approximations

Weak convergence of the Bernstein--Szegő probability measures is upgraded here to convergence of
their genuine Herglotz--Carathéodory transforms at every disk point.  The transform is defined by
the literal integral kernel, rather than by a formal Taylor series.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology Set
open scoped Topology

noncomputable section

/-- The normalized circle Herglotz--Carathéodory kernel. -/
def circleCaratheodoryKernel (w : ℂ) (z : Circle) : ℂ :=
  ((z : ℂ) + w) / ((z : ℂ) - w)

/-- The kernel is continuous on the circle for every point of the open disk. -/
theorem continuous_circleCaratheodoryKernel {w : ℂ} (hw : ‖w‖ < 1) :
    Continuous (circleCaratheodoryKernel w) := by
  apply Continuous.div
  · exact continuous_subtype_val.add continuous_const
  · exact continuous_subtype_val.sub continuous_const
  · intro z hzero
    have hzw : (z : ℂ) = w := sub_eq_zero.mp hzero
    have : ‖w‖ = 1 := by rw [← hzw, Circle.norm_coe]
    linarith

/-- The disk kernel is integrable against every circle probability law. -/
theorem circleCaratheodoryKernel_integrable_probability
    (mu : ProbabilityMeasure Circle) {w : ℂ} (hw : ‖w‖ < 1) :
    Integrable (circleCaratheodoryKernel w) (mu : Measure Circle) :=
  (BoundedContinuousFunction.mkOfCompact
    (⟨circleCaratheodoryKernel w,
      continuous_circleCaratheodoryKernel hw⟩ : C(Circle, ℂ))).integrable _

/-- The genuine Carathéodory transform of a finite circle measure. -/
def circleCaratheodoryTransform (mu : Measure Circle) (w : ℂ) : ℂ :=
  ∫ z : Circle, circleCaratheodoryKernel w z ∂mu

/-- At each disk point, the Carathéodory transform varies continuously with a probability law in
the weak topology. -/
theorem continuous_circleCaratheodoryTransform_probability {w : ℂ} (hw : ‖w‖ < 1) :
    Continuous (fun mu : ProbabilityMeasure Circle =>
      circleCaratheodoryTransform (mu : Measure Circle) w) := by
  have hkernel := continuous_circleCaratheodoryKernel hw
  let fre : C(Circle, ℝ) :=
    ⟨fun z => (circleCaratheodoryKernel w z).re, by
      simpa only [Function.comp_apply] using Complex.continuous_re.comp hkernel⟩
  let fim : C(Circle, ℝ) :=
    ⟨fun z => (circleCaratheodoryKernel w z).im, by
      simpa only [Function.comp_apply] using Complex.continuous_im.comp hkernel⟩
  have hre := ProbabilityMeasure.continuous_integral_boundedContinuousFunction
    (BoundedContinuousFunction.mkOfCompact fre)
  have him := ProbabilityMeasure.continuous_integral_boundedContinuousFunction
    (BoundedContinuousFunction.mkOfCompact fim)
  have hcomplex : Continuous (fun mu : ProbabilityMeasure Circle =>
      (((∫ z, fre z ∂(mu : Measure Circle)) : ℝ) : ℂ) +
        ((∫ z, fim z ∂(mu : Measure Circle)) : ℝ) * Complex.I) :=
    (Complex.continuous_ofReal.comp hre).add
      ((Complex.continuous_ofReal.comp him).mul continuous_const)
  convert hcomplex using 1
  funext mu
  have hint : Integrable (circleCaratheodoryKernel w) (mu : Measure Circle) :=
    (BoundedContinuousFunction.mkOfCompact
      (⟨circleCaratheodoryKernel w, hkernel⟩ : C(Circle, ℂ))).integrable
        (mu : Measure Circle)
  apply Complex.ext
  · simpa [circleCaratheodoryTransform, fre] using (integral_re hint).symm
  · simpa [circleCaratheodoryTransform, fim] using (integral_im hint).symm

/-- The genuine transforms of the canonical Bernstein--Szegő laws converge at every point of the
open unit disk. -/
theorem bernsteinSzegoProbabilityApproximation_caratheodory_tendsto
    (mu : ProbabilityMeasure Circle) (hmu : (mu : Measure Circle).support.Infinite)
    {w : ℂ} (hw : ‖w‖ < 1) :
    Tendsto (fun N => circleCaratheodoryTransform
      (bernsteinSzegoProbabilityApproximation mu hmu N : Measure Circle) w)
      atTop (𝓝 (circleCaratheodoryTransform (mu : Measure Circle) w)) := by
  exact ((continuous_circleCaratheodoryTransform_probability hw).tendsto mu).comp
    (bernsteinSzegoProbabilityApproximation_tendsto mu hmu)

/-- On every closed disk of radius strictly below one, the canonical transforms converge
uniformly.  This is the literal locally-uniform convergence asserted by the card. -/
theorem bernsteinSzegoProbabilityApproximation_caratheodory_tendstoUniformly_closedBall
    (mu : ProbabilityMeasure Circle) (hmu : (mu : Measure Circle).support.Infinite)
    {r : ℝ} (_hr0 : 0 ≤ r) (hr1 : r < 1) :
    let K := (Metric.closedBall (0 : ℂ) r : Set ℂ)
    Tendsto
      (fun N => UniformFun.ofFun (fun w : K =>
        circleCaratheodoryTransform
          (bernsteinSzegoProbabilityApproximation mu hmu N : Measure Circle) w.1))
      atTop
      (𝓝 (UniformFun.ofFun (fun w : K =>
        circleCaratheodoryTransform (mu : Measure Circle) w.1))) := by
  let K := (Metric.closedBall (0 : ℂ) r : Set ℂ)
  letI : CompactSpace K :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : ℂ) r)
  let H : Circle × K → ℂ := fun zw => circleCaratheodoryKernel zw.2.1 zw.1
  have hH : Continuous H := by
    apply Continuous.div
    · exact (continuous_subtype_val.comp continuous_fst).add
        (continuous_subtype_val.comp continuous_snd)
    · exact (continuous_subtype_val.comp continuous_fst).sub
        (continuous_subtype_val.comp continuous_snd)
    · intro zw hzero
      have hEq : (zw.1 : ℂ) = (zw.2.1 : ℂ) := sub_eq_zero.mp hzero
      have hwle : ‖(zw.2.1 : ℂ)‖ ≤ r := by
        simpa only [K, Metric.mem_closedBall, dist_zero_right] using zw.2.2
      have hz : ‖(zw.1 : ℂ)‖ = 1 := Circle.norm_coe zw.1
      rw [← hEq, hz] at hwle
      linarith
  let F : ℕ → K → ℂ := fun N w => circleCaratheodoryTransform
    (bernsteinSzegoProbabilityApproximation mu hmu N : Measure Circle) w.1
  let f : K → ℂ := fun w => circleCaratheodoryTransform (mu : Measure Circle) w.1
  have hFEquicont : Equicontinuous F := by
    apply UniformEquicontinuous.equicontinuous
    rw [Metric.uniformEquicontinuous_iff]
    intro ε hε
    obtain ⟨δ, hδ, hHδ⟩ := (Metric.uniformContinuous_iff.mp
      (CompactSpace.uniformContinuous_of_continuous hH))
      (ε / 2) (by linarith)
    refine ⟨δ, hδ, ?_⟩
    intro w v hwv N
    have hwDisk : ‖(w.1 : ℂ)‖ < 1 := by
      have hwle : ‖(w.1 : ℂ)‖ ≤ r := by
        simpa only [K, Metric.mem_closedBall, dist_zero_right] using w.2
      linarith
    have hvDisk : ‖(v.1 : ℂ)‖ < 1 := by
      have hvle : ‖(v.1 : ℂ)‖ ≤ r := by
        simpa only [K, Metric.mem_closedBall, dist_zero_right] using v.2
      linarith
    have hpoint : ∀ z : Circle,
        dist (circleCaratheodoryKernel w.1 z)
          (circleCaratheodoryKernel v.1 z) < ε / 2 := by
      intro z
      have hp : dist ((z, w) : Circle × K) (z, v) < δ := by
        simpa only [Prod.dist_eq, dist_self, max_eq_right dist_nonneg] using hwv
      have hout := hHδ hp
      change dist (circleCaratheodoryKernel w.1 z)
        (circleCaratheodoryKernel v.1 z) < ε / 2 at hout
      exact hout
    have hintw : Integrable (circleCaratheodoryKernel w.1)
        (bernsteinSzegoProbabilityApproximation mu hmu N : Measure Circle) :=
      circleCaratheodoryKernel_integrable_probability
        (bernsteinSzegoProbabilityApproximation mu hmu N) hwDisk
    have hintv : Integrable (circleCaratheodoryKernel v.1)
        (bernsteinSzegoProbabilityApproximation mu hmu N : Measure Circle) :=
      circleCaratheodoryKernel_integrable_probability
        (bernsteinSzegoProbabilityApproximation mu hmu N) hvDisk
    have hbound : dist (F N w) (F N v) ≤ ε / 2 := by
      rw [dist_eq_norm]
      change ‖(∫ z, circleCaratheodoryKernel w.1 z
          ∂(bernsteinSzegoProbabilityApproximation mu hmu N : Measure Circle)) -
        ∫ z, circleCaratheodoryKernel v.1 z
          ∂(bernsteinSzegoProbabilityApproximation mu hmu N : Measure Circle)‖ ≤ _
      rw [← integral_sub hintw hintv]
      calc
        ‖∫ z, circleCaratheodoryKernel w.1 z - circleCaratheodoryKernel v.1 z
            ∂(bernsteinSzegoProbabilityApproximation mu hmu N : Measure Circle)‖
            ≤ (ε / 2) *
              (bernsteinSzegoProbabilityApproximation mu hmu N : Measure Circle).real Set.univ :=
          norm_integral_le_of_norm_le_const
            (Filter.Eventually.of_forall fun z => by
              simpa only [dist_eq_norm] using (hpoint z).le)
        _ = ε / 2 := by simp
    exact hbound.trans_lt (by linarith)
  have hpointwise : Tendsto F atTop (𝓝 f) := by
    rw [tendsto_pi_nhds]
    intro w
    have hwDisk : ‖(w.1 : ℂ)‖ < 1 := by
      have hwle : ‖(w.1 : ℂ)‖ ≤ r := by
        simpa only [K, Metric.mem_closedBall, dist_zero_right] using w.2
      linarith
    exact bernsteinSzegoProbabilityApproximation_caratheodory_tendsto mu hmu hwDisk
  exact (hFEquicont.tendsto_uniformFun_iff_pi atTop f).2 hpointwise

end

end GaloisForLFunctions.HTGeometry
