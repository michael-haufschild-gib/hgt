import GaloisForLFunctions.HTGeometry.ClockFoliationRegularProbes

/-!
# The flat chart is foliated by its time coordinate

The foliation hypotheses — a smooth level function whose carré du champ and d'Alembertian are
functions of its own value, the first nowhere zero — are inhabited by the simplest possible datum:
the time coordinate of the flat chart, with `Γ(t,t) = -1` and `□t = 0`.

This makes the foliation theorems non-vacuous and supplies a second, ordinary-differential
construction of clock probes on the flat chart for potentials depending only on time, independent of
the hyperbolic one.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped ContDiff

section TimeFoliation

variable {d : ℕ}

/-- The time coordinate of the chart. -/
def timeCoord (d : ℕ) : (Fin (d + 1) → ℝ) → ℝ := fun y => y 0

theorem contDiff_timeCoord : ContDiff ℝ ∞ (timeCoord d) :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (d + 1) => ℝ) 0).contDiff

theorem coordPartial_timeCoord (i : Fin (d + 1)) (x : Fin (d + 1) → ℝ) :
    coordPartial i (timeCoord d) x = if i = 0 then 1 else 0 := by
  have hderiv : HasFDerivAt (timeCoord d)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (d + 1) => ℝ) 0) x :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (d + 1) => ℝ) 0).hasFDerivAt
  rw [coordPartial, hderiv.fderiv]
  show (Pi.single i (1 : ℝ) : Fin (d + 1) → ℝ) 0 = if i = 0 then 1 else 0
  by_cases hi : i = 0
  · subst hi
    simp
  · rw [if_neg hi, Pi.single_apply, if_neg (fun h => hi h.symm)]

theorem coordPartial_coordPartial_timeCoord (i j : Fin (d + 1)) (x : Fin (d + 1) → ℝ) :
    coordPartial j (coordPartial i (timeCoord d)) x = 0 := by
  have hconst : coordPartial i (timeCoord d) = fun _ : Fin (d + 1) → ℝ =>
      (if i = 0 then (1 : ℝ) else 0) := by
    funext y
    exact coordPartial_timeCoord i y
  rw [hconst, coordPartial_const]

/-! ## The invariants of the time foliation -/

theorem gradPair_kgChart_timeCoord (x : Fin (d + 1) → ℝ) :
    (kgChart d).gradPair (timeCoord d) (timeCoord d) x = -1 := by
  classical
  simp only [SmoothMetricChart.gradPair, kgChart,
    SmoothPseudoMetric.ofSignature_inverseMetric, Matrix.diagonal_apply,
    coordPartial_timeCoord]
  rw [Finset.sum_eq_single (0 : Fin (d + 1))]
  · rw [Finset.sum_eq_single (0 : Fin (d + 1))]
    · simp [kgEps]
    · intro j _ hj
      simp [hj, Ne.symm hj]
    · intro h
      exact absurd (Finset.mem_univ (0 : Fin (d + 1))) h
  · intro i _ hi
    refine Finset.sum_eq_zero fun j _ => ?_
    simp [hi]
  · intro h
    exact absurd (Finset.mem_univ (0 : Fin (d + 1))) h

theorem dalembert_kgChart_timeCoord (x : Fin (d + 1) → ℝ) :
    (kgChart d).dalembert (timeCoord d) x = 0 := by
  rw [kgChart, SmoothPseudoMetric.ofSignature_dalembert (kgEps d) (kgEps_ne_zero d)
    contDiff_timeCoord x]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [coordPartial_coordPartial_timeCoord i i x, mul_zero]

/-! ## Probes from the time foliation -/

/-- **Clock probes on the flat chart for a potential depending only on time**, constructed by
solving an ordinary differential equation along the time axis. -/
theorem regularOpenProbes_kgChart_timeFoliation {V : ℝ → ℝ} (hV : ContDiff ℝ 1 V) :
    RegularOpenProbes (kgChart d).dalembert (fun y => V (timeCoord d y)) :=
  regularOpenProbes_foliation (kgChart d) contDiff_timeCoord
    (P := fun _ => -1) (R := fun _ => 0)
    (fun x => gradPair_kgChart_timeCoord x) (fun x => dalembert_kgChart_timeCoord x)
    contDiff_const contDiff_const (fun _ => by norm_num) hV

/-- **The foliation transfer is non-vacuous**: an arbitrary conformal rescaling of the flat chart
carries the probes of its time foliation. -/
theorem regularOpenProbes_conformalRescale_kgChart_timeFoliation {V : ℝ → ℝ}
    (hV : ContDiff ℝ 1 V) {sigma : (Fin (d + 1) → ℝ) → ℝ} (hsigma : ContDiff ℝ ∞ sigma) :
    RegularOpenProbes ((kgChart d).conformalRescale sigma hsigma).dalembert
      ((kgChart d).conformalTransferPotential sigma fun y => V (timeCoord d y)) :=
  regularOpenProbes_conformalRescale_foliation (kgChart d) contDiff_timeCoord
    (P := fun _ => -1) (R := fun _ => 0)
    (fun x => gradPair_kgChart_timeCoord x) (fun x => dalembert_kgChart_timeCoord x)
    contDiff_const contDiff_const (fun _ => by norm_num) hV hsigma

end TimeFoliation

end GaloisForLFunctions.HTGeometry
