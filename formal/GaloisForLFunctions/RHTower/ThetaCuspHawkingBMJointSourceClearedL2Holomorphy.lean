import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceClearedRadialAdmission
import GaloisForLFunctions.HTGeometry.L2RestrictedHolomorphy

/-! Genuine L²-valued holomorphy of the original denominator-cleared cutoff numerator. -/
namespace RHTower.D4BMJointSource
open Complex Set Filter Topology Metric MeasureTheory D4BMLaplaceRadial D4BMModularCore D4BMJointWave GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- The actual undivided cutoff family is complex differentiable in the full radial L² norm. -/
theorem clearedCutoffRadialCoefficient_l2_differentiableAt (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : w.im ≠ 0) (hwre : -2 < w.re) (hwr : |w.re| < 2) (i : Fin 3) :
    DifferentiableAt ℂ (l2Family radialMeasure (fun u => clearedCutoffRadialCoefficient q branch u a i)) w := by
  obtain ⟨R,b,C,hR,hb,hC,hM,hbound⟩ := clearedCutoffRadialCoefficient_local_bound q branch w a hw hwre hwr i
  have hN : ∀ᶠ u in 𝓝 w, u ∈ ball w R ∧ u.im ≠ 0 ∧ -2 < u.re ∧ |u.re| < 2 :=
    (show ∀ᶠ u in 𝓝 w, u ∈ ball w R from ball_mem_nhds w hR).and
      ((Complex.continuous_im.continuousAt.eventually_ne hw).and
        ((Complex.continuous_re.continuousAt.eventually_const_lt hwre).and
          (Complex.continuous_re.continuousAt.abs.eventually_lt_const hwr)))
  obtain ⟨r,hr,hrs⟩ := Metric.mem_nhds_iff.mp hN
  apply differentiableAt_l2Family_restrict_of_cauchy_dominated volume (Iio 0) measurableSet_Iio
    (fun u => clearedCutoffRadialCoefficient q branch u a i) w r hr (fun t => C*Real.exp (b*t)) hM
  · intro u hu
    have h := hrs hu
    exact (clearedCutoffRadialCoefficient_memLp q branch u a h.2.1 h.2.2.1 h.2.2.2 i).aestronglyMeasurable
  · intro t ht u hu
    have h := hrs hu
    have ha : AnalyticAt ℂ (fun v => clearedCutoffRadialCoefficient q branch v a i t) u :=
      analyticAt_const.mul (clearedPrincipalDifference_analyticAt q branch u a h.2.1 h.2.2.1 i t ht).1
    exact ha.differentiableAt.differentiableWithinAt
  · intro t ht u hu
    exact hbound u (hrs hu).1 t ht

/-- Holomorphy is established in the actual L² space, including the analytic numerator at original poles. -/
theorem clearedCutoffRadialCoefficient_l2_analyticAt (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : w.im ≠ 0) (hwre : -2 < w.re) (hwr : |w.re| < 2) (i : Fin 3) :
    AnalyticAt ℂ (l2Family radialMeasure (fun u => clearedCutoffRadialCoefficient q branch u a i)) w := by
  have hd : DifferentiableOn ℂ
      (l2Family radialMeasure (fun u => clearedCutoffRadialCoefficient q branch u a i))
      {u : ℂ | u.im ≠ 0 ∧ -2 < u.re ∧ |u.re| < 2} := fun u hu =>
    (clearedCutoffRadialCoefficient_l2_differentiableAt q branch u a hu.1 hu.2.1 hu.2.2 i).differentiableWithinAt
  exact hd.analyticAt ((Complex.continuous_im.continuousAt.eventually_ne hw).and
    ((Complex.continuous_re.continuousAt.eventually_const_lt hwre).and
      (Complex.continuous_re.continuousAt.abs.eventually_lt_const hwr)))

end
end RHTower.D4BMJointSource
