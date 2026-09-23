import GaloisForLFunctions.HTGeometry.HillProbeAnywhere

/-!
# The chart of a variable propagation speed

The wave operator of a speed is the divergence-form operator of an explicit smooth chart: the
inverse metric is diagonal, `-1` in time and `c(t)²` in each spatial direction, and the volume
density is constant. Since the speed depends on the time coordinate only, the spatial fluxes
differentiate the field alone, and the operator is the literal alternating sum of pure second
derivatives, the spatial ones weighted by `c(t)²`.

That identification puts the evolution's probes inside the corpus's chart calculus, where the
conformal transfer and the two-species scale law live.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

open scoped ContDiff

section SpeedChart

variable {d : ℕ} {c : ℝ → ℝ}

/-- A function of the time coordinate has no spatial partials. -/
theorem coordPartial_time_only {g : ℝ → ℝ} (hg : Differentiable ℝ g) (i : Fin d)
    (y : Fin (d + 1) → ℝ) :
    coordPartial i.succ (fun z : Fin (d + 1) → ℝ => g (z 0)) y = 0 := by
  have hproj : HasFDerivAt (fun z : Fin (d + 1) → ℝ => z 0)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (d + 1) => ℝ) 0) y :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (d + 1) => ℝ) 0).hasFDerivAt
  have hcomp : HasFDerivAt (fun z : Fin (d + 1) → ℝ => g (z 0))
      ((fderiv ℝ g (y 0)).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (d + 1) => ℝ) 0)) y :=
    ((hg (y 0)).hasFDerivAt).comp y hproj
  rw [coordPartial, hcomp.fderiv]
  show (fderiv ℝ g (y 0)) ((Pi.single i.succ (1 : ℝ) : Fin (d + 1) → ℝ) 0) = 0
  rw [Pi.single_eq_of_ne (Ne.symm (Fin.succ_ne_zero i)), map_zero]

theorem differentiable_speedSq (hs : ContDiff ℝ ∞ c) :
    Differentiable ℝ fun z : Fin (d + 1) → ℝ => c (z 0) ^ (2 : ℕ) := by
  have hproj : ContDiff ℝ ∞ fun z : Fin (d + 1) → ℝ => z 0 :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (d + 1) => ℝ) 0).contDiff
  exact ((hs.comp hproj).pow 2).differentiable (by simp)

/-- The chart of a variable propagation speed: diagonal inverse metric, constant density. -/
noncomputable def hillSpeedChart (d : ℕ) (c : ℝ → ℝ) (hs : ContDiff ℝ ∞ c) :
    SmoothMetricChart (d + 1) where
  inverseMetric := fun y =>
    Matrix.diagonal fun j : Fin (d + 1) => if j = 0 then -1 else c (y 0) ^ (2 : ℕ)
  density := fun _ => 1
  contDiff_inverseMetric := by
    intro i j
    by_cases hij : i = j
    · subst hij
      by_cases hi : i = 0
      · subst hi
        have hfun : (fun y : Fin (d + 1) → ℝ =>
            (Matrix.diagonal fun j : Fin (d + 1) => if j = 0 then -1 else c (y 0) ^ (2 : ℕ))
              (0 : Fin (d + 1)) (0 : Fin (d + 1))) = fun _ => (-1 : ℝ) := by
          funext y
          rw [Matrix.diagonal_apply_eq, if_pos rfl]
        rw [hfun]
        exact contDiff_const
      · have hfun : (fun y : Fin (d + 1) → ℝ =>
            (Matrix.diagonal fun j : Fin (d + 1) => if j = 0 then -1 else c (y 0) ^ (2 : ℕ)) i i)
              = fun y => c (y 0) ^ (2 : ℕ) := by
          funext y
          rw [Matrix.diagonal_apply_eq, if_neg hi]
        rw [hfun]
        have hproj : ContDiff ℝ ∞ fun z : Fin (d + 1) → ℝ => z 0 :=
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (d + 1) => ℝ) 0).contDiff
        exact (hs.comp hproj).pow 2
    · have hfun : (fun y : Fin (d + 1) → ℝ =>
          (Matrix.diagonal fun j : Fin (d + 1) => if j = 0 then -1 else c (y 0) ^ (2 : ℕ)) i j)
            = fun _ => (0 : ℝ) := by
        funext y
        rw [Matrix.diagonal_apply_ne _ hij]
      rw [hfun]
      exact contDiff_const
  contDiff_density := contDiff_const
  density_pos := fun _ => one_pos
  inverseMetric_symm := by
    intro y i j
    by_cases hij : i = j
    · rw [hij]
    · rw [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ (Ne.symm hij)]

theorem hillSpeedChart_density (hs : ContDiff ℝ ∞ c) (y : Fin (d + 1) → ℝ) :
    (hillSpeedChart d c hs).density y = 1 := rfl

theorem hillSpeedChart_inverseMetric (hs : ContDiff ℝ ∞ c) (y : Fin (d + 1) → ℝ)
    (i j : Fin (d + 1)) :
    (hillSpeedChart d c hs).inverseMetric y i j =
      Matrix.diagonal (fun k : Fin (d + 1) => if k = 0 then -1 else c (y 0) ^ (2 : ℕ)) i j := rfl

/-! ## The fluxes -/

theorem hillSpeedChart_flux_zero (hs : ContDiff ℝ ∞ c) (u : (Fin (d + 1) → ℝ) → ℝ) :
    (hillSpeedChart d c hs).flux u 0 = fun y => -(coordPartial 0 u y) := by
  funext y
  rw [SmoothMetricChart.flux, hillSpeedChart_density, one_mul,
    Finset.sum_eq_single (0 : Fin (d + 1))]
  · rw [hillSpeedChart_inverseMetric, Matrix.diagonal_apply_eq, if_pos rfl]
    ring
  · intro j _ hj
    rw [hillSpeedChart_inverseMetric, Matrix.diagonal_apply_ne _ (Ne.symm hj), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem hillSpeedChart_flux_succ (hs : ContDiff ℝ ∞ c) (u : (Fin (d + 1) → ℝ) → ℝ) (i : Fin d) :
    (hillSpeedChart d c hs).flux u i.succ
      = fun y => c (y 0) ^ (2 : ℕ) * coordPartial i.succ u y := by
  funext y
  rw [SmoothMetricChart.flux, hillSpeedChart_density, one_mul,
    Finset.sum_eq_single i.succ]
  · rw [hillSpeedChart_inverseMetric, Matrix.diagonal_apply_eq, if_neg (Fin.succ_ne_zero i)]
  · intro j _ hj
    rw [hillSpeedChart_inverseMetric, Matrix.diagonal_apply_ne _ (Ne.symm hj), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-! ## The operator -/

/-- **The divergence-form operator of the speed chart is the wave operator of the speed.** -/
theorem hillSpeedChart_dalembert (hs : ContDiff ℝ ∞ c) {u : (Fin (d + 1) → ℝ) → ℝ}
    {y : Fin (d + 1) → ℝ} (hdiff : ∀ j : Fin (d + 1), DifferentiableAt ℝ (coordPartial j u) y) :
    (hillSpeedChart d c hs).dalembert u y = hillWaveOp d c u y := by
  have hspeed : DifferentiableAt ℝ (fun z : Fin (d + 1) → ℝ => c (z 0) ^ (2 : ℕ)) y :=
    (differentiable_speedSq hs) y
  have h0 : coordPartial 0 ((hillSpeedChart d c hs).flux u 0) y
      = -(coordPartial 0 (coordPartial 0 u) y) := by
    rw [hillSpeedChart_flux_zero]
    have hfun : (fun z : Fin (d + 1) → ℝ => -(coordPartial 0 u z))
        = fun z => (-1 : ℝ) * coordPartial 0 u z := by
      funext z
      ring
    rw [hfun, coordPartial_const_mul (hdiff 0) (-1) 0]
    ring
  have hsucc : ∀ i : Fin d, coordPartial i.succ ((hillSpeedChart d c hs).flux u i.succ) y
      = c (y 0) ^ (2 : ℕ) * coordPartial i.succ (coordPartial i.succ u) y := by
    intro i
    rw [hillSpeedChart_flux_succ, coordPartial_mul hspeed (hdiff i.succ) i.succ,
      coordPartial_time_only (g := fun t : ℝ => c t ^ (2 : ℕ)) ((hs.pow 2).differentiable (by simp)) i y,
      mul_zero, add_zero]
  rw [SmoothMetricChart.dalembert, hillSpeedChart_density, inv_one, one_mul, Fin.sum_univ_succ,
    h0, Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hsucc i, ← Finset.mul_sum, hillWaveOp]

end SpeedChart

end GaloisForLFunctions.HTGeometry
