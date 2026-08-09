import GaloisForLFunctions.HTGeometry.InterfinityGeometry.ParametricSmoothness

/-!
# Hadamard's lemma in one coordinate of several

A smooth function of several variables splits, in every single coordinate, as its restriction to the
corresponding face plus that coordinate times a smooth function:

`h x = h (x with x_j = 0) + x_j · r_j(x)`,  `r_j(x) = ∫₀¹ (∂_j h)(x with x_j = t x_j) dt`.

Smoothness of the remainder is the parametric-average theorem; the identity itself is the
fundamental theorem of calculus along the `j`-th coordinate segment.
-/

namespace GaloisForLFunctions.HTGeometry.Interfinity

open MeasureTheory Set Filter Topology

noncomputable section

variable {d : ℕ}

/-- Smoothness of every finite order on the multi-time chart space. -/
def IsSmoothMulti (h : (Fin d → ℝ) → ℝ) : Prop := ∀ n : ℕ, ContDiff ℝ n h

namespace IsSmoothMulti

theorem continuous {h : (Fin d → ℝ) → ℝ} (hh : IsSmoothMulti h) : Continuous h := (hh 0).continuous

theorem differentiable {h : (Fin d → ℝ) → ℝ} (hh : IsSmoothMulti h) : Differentiable ℝ h :=
  (hh 1).differentiable (by norm_num)

theorem fderivSmooth {h : (Fin d → ℝ) → ℝ} (hh : IsSmoothMulti h) (n : ℕ) :
    ContDiff ℝ n (fderiv ℝ h) := by
  have hn : ContDiff ℝ ((n : WithTop ℕ∞) + 1) h := by exact_mod_cast hh (n + 1)
  exact hn.fderiv_right le_rfl

end IsSmoothMulti

/-- Rescaling the `j`-th coordinate. -/
def scaleCoord (j : Fin d) (p : (Fin d → ℝ) × ℝ) : Fin d → ℝ :=
  Function.update p.1 j (p.2 * p.1 j)

@[simp] theorem scaleCoord_apply_self (j : Fin d) (p : (Fin d → ℝ) × ℝ) :
    scaleCoord j p j = p.2 * p.1 j := by
  simp [scaleCoord]

theorem scaleCoord_apply_ne (j : Fin d) (p : (Fin d → ℝ) × ℝ) {i : Fin d} (hij : i ≠ j) :
    scaleCoord j p i = p.1 i := by
  simp [scaleCoord, Function.update_of_ne hij]

theorem contDiff_scaleCoord (j : Fin d) (n : ℕ) : ContDiff ℝ n (scaleCoord (d := d) j) := by
  refine contDiff_pi.2 fun i => ?_
  by_cases hij : i = j
  · subst hij
    have hEq : (fun p : (Fin d → ℝ) × ℝ => scaleCoord i p i) = fun p => p.2 * p.1 i := by
      funext p
      exact scaleCoord_apply_self i p
    rw [hEq]
    exact contDiff_snd.mul ((contDiff_pi.1 (contDiff_id : ContDiff ℝ n _) i).comp contDiff_fst)
  · have hEq : (fun p : (Fin d → ℝ) × ℝ => scaleCoord j p i) = fun p => p.1 i := by
      funext p
      exact scaleCoord_apply_ne j p hij
    rw [hEq]
    exact (contDiff_pi.1 (contDiff_id : ContDiff ℝ n _) i).comp contDiff_fst

/-- The integrand of the coordinate Hadamard remainder. -/
def coordIntegrand (j : Fin d) (h : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) (t : ℝ) : ℝ :=
  fderiv ℝ h (scaleCoord j (x, t)) (Pi.single j 1)

theorem contDiff_uncurry_coordIntegrand (j : Fin d) {h : (Fin d → ℝ) → ℝ} (hh : IsSmoothMulti h)
    (n : ℕ) : ContDiff ℝ n (Function.uncurry (coordIntegrand j h)) := by
  have hEq : Function.uncurry (coordIntegrand j h) =
      fun p : (Fin d → ℝ) × ℝ =>
        (ContinuousLinearMap.apply ℝ ℝ (Pi.single j (1 : ℝ))) (fderiv ℝ h (scaleCoord j p)) := rfl
  rw [hEq]
  exact (ContinuousLinearMap.apply ℝ ℝ (Pi.single j (1 : ℝ))).contDiff.comp
    ((hh.fderivSmooth n).comp (contDiff_scaleCoord j n))

/-- The Hadamard remainder in the `j`-th coordinate. -/
def coordRemainder (j : Fin d) (h : (Fin d → ℝ) → ℝ) : (Fin d → ℝ) → ℝ :=
  paramAvg (coordIntegrand j h)

theorem isSmoothMulti_coordRemainder (j : Fin d) {h : (Fin d → ℝ) → ℝ} (hh : IsSmoothMulti h) :
    IsSmoothMulti (coordRemainder j h) := fun n =>
  contDiff_paramAvg n (contDiff_uncurry_coordIntegrand j hh n)

/-- **Hadamard's lemma in one coordinate.** -/
theorem coord_hadamard (j : Fin d) {h : (Fin d → ℝ) → ℝ} (hh : IsSmoothMulti h)
    (x : Fin d → ℝ) :
    h x = h (Function.update x j 0) + x j * coordRemainder j h x := by
  have hseg : ∀ t : ℝ, HasDerivAt (fun u : ℝ => h (Function.update x j (u * x j)))
      (x j * coordIntegrand j h x t) t := by
    intro t
    have hinner : HasDerivAt (fun u : ℝ => Function.update x j (u * x j))
        (Pi.single j (x j)) t := by
      refine hasDerivAt_pi.2 fun i => ?_
      by_cases hij : i = j
      · subst hij
        have hEq : (fun u : ℝ => Function.update x i (u * x i) i) = fun u : ℝ => u * x i := by
          funext u
          simp
        rw [hEq]
        simpa [Pi.single_eq_same] using (hasDerivAt_id t).mul_const (x i)
      · have hEq : (fun u : ℝ => Function.update x j (u * x j) i) = fun _ : ℝ => x i := by
          funext u
          simp [Function.update_of_ne hij]
        rw [hEq]
        simpa [Pi.single_eq_of_ne hij] using hasDerivAt_const t (x i)
    have hcomp := (hh.differentiable (Function.update x j (t * x j))).hasFDerivAt.comp_hasDerivAt t
      hinner
    have hlin : fderiv ℝ h (Function.update x j (t * x j)) (Pi.single j (x j)) =
        x j * coordIntegrand j h x t := by
      rw [coordIntegrand]
      have hsingle : (Pi.single j (x j) : Fin d → ℝ) = x j • Pi.single j (1 : ℝ) := by
        funext i
        by_cases hij : i = j <;> simp [hij]
      rw [hsingle, map_smul]
      simp [scaleCoord, smul_eq_mul]
    rw [hlin] at hcomp
    exact hcomp
  have hcont : Continuous fun t : ℝ => x j * coordIntegrand j h x t := by
    have := (contDiff_uncurry_coordIntegrand j hh 0).continuous
    exact continuous_const.mul (this.comp (Continuous.prodMk_right x))
  have hFTC : (∫ t in (0 : ℝ)..1, x j * coordIntegrand j h x t) =
      h (Function.update x j (1 * x j)) - h (Function.update x j (0 * x j)) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hseg t) ?_
    exact hcont.intervalIntegrable _ _
  rw [intervalIntegral.integral_const_mul] at hFTC
  have hx1 : Function.update x j (1 * x j) = x := by
    rw [one_mul, Function.update_eq_self]
  have hx0 : Function.update x j (0 * x j) = Function.update x j 0 := by
    rw [zero_mul]
  rw [hx1, hx0] at hFTC
  rw [coordRemainder, paramAvg]
  linarith

end

end GaloisForLFunctions.HTGeometry.Interfinity
