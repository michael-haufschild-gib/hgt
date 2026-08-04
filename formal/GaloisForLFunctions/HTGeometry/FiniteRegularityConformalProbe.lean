import GaloisForLFunctions.HTGeometry.FiniteRegularitySpacetimeProbe
import GaloisForLFunctions.HTGeometry.KleinGordonConformallyFlat

/-!
# Finite regularity on a conformally rescaled chart

The finite-order probe theorem is stated for a potential read in the time-space splitting; composing
with the linear identification of an event with its coordinates gives it for a potential of the
chart variable, and the conformal pullback of such a potential by a smooth conformal factor has the
same finite regularity, because the factor contributes only smooth terms.

So every conformal rescaling of the flat chart carries clock probes for a potential of class
`C^{2d+5}`, with no smoothness hypothesis on the potential itself.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped ContDiff

section Chart

variable {d N j m : ℕ}

/-- **Clock probes for a potential of finite regularity, read in the chart variable.** -/
theorem regularOpenProbes_of_contDiff_chart
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N)
    (hdim : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < m) (hj : N + m ≤ 2 * j)
    {V : (Fin (d + 1) → ℝ) → ℝ} (hV : ContDiff ℝ ((2 * j + 1 : ℕ) : WithTop ℕ∞) V) :
    RegularOpenProbes (kgWaveOp d) V := by
  have hsplit : V = fun y : Fin (d + 1) → ℝ =>
      (fun p : ℝ × EuclideanSpace ℝ (Fin d) => V (kgEventInvCLM d p)) (y 0, kgSpatial d y) := by
    funext y
    show V y = V (kgEventInvCLM d (y 0, kgSpatial d y))
    rw [kgEventInvCLM_split y]
  have hcomp : ContDiff ℝ ((2 * j + 1 : ℕ) : WithTop ℕ∞)
      fun p : ℝ × EuclideanSpace ℝ (Fin d) => V (kgEventInvCLM d p) :=
    hV.comp ((kgEventInvCLM d).contDiff.of_le (by exact_mod_cast le_top))
  rw [hsplit]
  exact regularOpenProbes_of_contDiff_spacetime (N := N) (m := m) (j := j) hN hdim hj hcomp

/-- The explicit finite order, in the chart variable. -/
theorem regularOpenProbes_of_contDiff_chart_explicit
    {V : (Fin (d + 1) → ℝ) → ℝ} (hV : ContDiff ℝ ((2 * d + 5 : ℕ) : WithTop ℕ∞) V) :
    RegularOpenProbes (kgWaveOp d) V := by
  have hrank : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := finrank_euclideanSpace_fin
  have hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < (d + 3 : ℕ) := by
    rw [hrank]; push_cast; linarith
  have hdim : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < (d + 1 : ℕ) := by
    rw [hrank]; push_cast; linarith
  have hj : (d + 3) + (d + 1) ≤ 2 * (d + 2) := by omega
  have hord : 2 * (d + 2) + 1 = 2 * d + 5 := by omega
  refine regularOpenProbes_of_contDiff_chart (N := d + 3) (m := d + 1) (j := d + 2) hN hdim hj ?_
  rw [hord]
  exact hV

end Chart

/-! ## The conformal pullback keeps the regularity -/

namespace SmoothMetricChart

variable {d : ℕ} (M : SmoothMetricChart d)

theorem contDiff_conformalPullbackPotential_finite {k : ℕ} {sigma P : (Fin d → ℝ) → ℝ}
    (hsigma : ContDiff ℝ ∞ sigma) (hP : ContDiff ℝ ((k : ℕ) : WithTop ℕ∞) P) :
    ContDiff ℝ ((k : ℕ) : WithTop ℕ∞) (M.conformalPullbackPotential sigma P) := by
  have hk : ((k : ℕ) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  refine ContDiff.sub ?_ ?_
  · exact ((Real.contDiff_exp.comp (contDiff_const.mul hsigma)).of_le hk).mul hP
  · exact ((contDiff_const.mul (M.contDiff_dalembert hsigma)).add
      (contDiff_const.mul (M.contDiff_gradPair hsigma hsigma))).of_le hk

end SmoothMetricChart

/-! ## Probes on a conformally rescaled flat chart -/

section ConformallyFlat

variable {d N j m : ℕ}

/-- **Clock probes for a potential of finite regularity on every conformal rescaling of the flat
chart.** The conformal factor is an arbitrary smooth function; the potential is only `C^{2j+1}`. -/
theorem regularOpenProbes_conformalRescale_kgChart_contDiff
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N)
    (hdim : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < m) (hj : N + m ≤ 2 * j)
    {sigma : (Fin (d + 1) → ℝ) → ℝ} (hsigma : ContDiff ℝ ∞ sigma)
    {P : (Fin (d + 1) → ℝ) → ℝ} (hP : ContDiff ℝ ((2 * j + 1 : ℕ) : WithTop ℕ∞) P) :
    RegularOpenProbes ((kgChart d).conformalRescale sigma hsigma).dalembert P := by
  have hbase : RegularOpenProbes (kgChart d).dalembert
      ((kgChart d).conformalPullbackPotential sigma P) := by
    rw [← kgWaveOp_eq_dalembert]
    exact regularOpenProbes_of_contDiff_chart (N := N) (m := m) (j := j) hN hdim hj
      ((kgChart d).contDiff_conformalPullbackPotential_finite hsigma hP)
  have htransfer := regularOpenProbes_conformalRescale (kgChart d) hsigma hbase
  rwa [(kgChart d).conformalTransferPotential_pullback sigma P] at htransfer

/-- The explicit finite order on a conformally rescaled chart. -/
theorem regularOpenProbes_conformalRescale_kgChart_contDiff_explicit
    {sigma : (Fin (d + 1) → ℝ) → ℝ} (hsigma : ContDiff ℝ ∞ sigma)
    {P : (Fin (d + 1) → ℝ) → ℝ} (hP : ContDiff ℝ ((2 * d + 5 : ℕ) : WithTop ℕ∞) P) :
    RegularOpenProbes ((kgChart d).conformalRescale sigma hsigma).dalembert P := by
  have hrank : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := finrank_euclideanSpace_fin
  have hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < (d + 3 : ℕ) := by
    rw [hrank]; push_cast; linarith
  have hdim : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < (d + 1 : ℕ) := by
    rw [hrank]; push_cast; linarith
  have hj : (d + 3) + (d + 1) ≤ 2 * (d + 2) := by omega
  have hord : 2 * (d + 2) + 1 = 2 * d + 5 := by omega
  refine regularOpenProbes_conformalRescale_kgChart_contDiff (N := d + 3) (m := d + 1) (j := d + 2)
    hN hdim hj hsigma ?_
  rw [hord]
  exact hP

end ConformallyFlat

end GaloisForLFunctions.HTGeometry
