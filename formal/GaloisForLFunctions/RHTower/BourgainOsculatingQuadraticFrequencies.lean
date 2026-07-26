/-
# Quadratic frequencies in scaled osculating coordinates

After the phase-coordinate map at two separated bases and the physical
parabola dilation `H/D`, the two quadratic osculating increments become the
independent sampled parabolas `(n/H,n²/H²,0,0)` and
`(0,0,n/H,n²/H²)` exactly.
-/
import GaloisForLFunctions.RHTower.BourgainDualFrequencyCoordinates

namespace RHTower

noncomputable section

/-- Phase increment of the vector-valued quadratic model. -/
theorem bourgainDot_quadraticCurveModel_sub_base
    (a s : ℝ) (x : BourgainPhaseSpace) :
    bourgainDot x
        (bourgainSquareRootQuadraticCurveModel a s -
          bourgainSquareRootCurve (a ^ (2 : ℕ))) =
      bourgainSquareRootLinearPhaseCoordinate a x * s +
        bourgainSquareRootQuadraticPhaseCoordinate a x *
          s ^ (2 : ℕ) := by
  rw [show
      bourgainDot x
          (bourgainSquareRootQuadraticCurveModel a s -
            bourgainSquareRootCurve (a ^ (2 : ℕ))) =
        bourgainDot x (bourgainSquareRootQuadraticCurveModel a s) -
          bourgainDot x
            (bourgainSquareRootCurve (a ^ (2 : ℕ))) by
    unfold bourgainDot
    simp_rw [Pi.sub_apply, mul_sub]
    rw [Finset.sum_sub_distrib]]
  rw [bourgainDot_quadraticCurveModel]
  unfold bourgainSquareRootQuadraticLocalPhase
    bourgainSquareRootCurvePhase
  ring

/-- The left quadratic osculating increment becomes the left independent
parabola sample under the dual scaled phase map. -/
theorem bourgainDualPullback_quadraticLeft_eq
    {H : ℕ} (hH : 0 < H) {D a b : ℝ}
    (hD : 0 < D) (ha : 0 < a) (hab : a < b)
    (n : Fin H) :
    bourgainDualPullbackFrequency
        (bourgainScaledOsculatingPhaseContinuousLinearEquiv
          (div_ne_zero (Nat.cast_ne_zero.mpr hH.ne') hD.ne')
          ha hab).toLinearEquiv
        (bourgainSquareRootQuadraticCurveModel a
            ((bourgainIndex n : ℝ) / D) -
          bourgainSquareRootCurve (a ^ (2 : ℕ))) =
      bourgainLeftParabolaSample (H : ℝ) n := by
  let scale : ℝ := (H : ℝ) / D
  have hscale : scale ≠ 0 :=
    div_ne_zero (Nat.cast_ne_zero.mpr hH.ne') hD.ne'
  let E :=
    bourgainScaledOsculatingPhaseContinuousLinearEquiv
      hscale ha hab
  funext j
  let x : BourgainPhaseSpace := E.symm (bourgainPhaseBasis j)
  have hmap :
      bourgainScaledOsculatingPhaseCoordinates scale a b x =
        bourgainPhaseBasis j := by
    calc
      bourgainScaledOsculatingPhaseCoordinates scale a b x = E x := by
        symm
        exact
          bourgainScaledOsculatingPhaseContinuousLinearEquiv_apply
            hscale ha hab x
      _ = bourgainPhaseBasis j := E.apply_symm_apply _
  have hlin := congrFun hmap (0 : Fin 4)
  have hquad := congrFun hmap (1 : Fin 4)
  change scale *
      bourgainSquareRootPhaseCoordinates a b x 0 =
        bourgainPhaseBasis j 0 at hlin
  change scale ^ (2 : ℕ) *
      bourgainSquareRootPhaseCoordinates a b x 1 =
        bourgainPhaseBasis j 1 at hquad
  rw [← bourgainSquareRootLinearPhaseCoordinate_eq (a := a) (b := b)]
    at hlin
  rw [← bourgainSquareRootQuadraticPhaseCoordinate_eq (a := a) (b := b)]
    at hquad
  change bourgainDot x
      (bourgainSquareRootQuadraticCurveModel a
          ((bourgainIndex n : ℝ) / D) -
        bourgainSquareRootCurve (a ^ (2 : ℕ))) =
    bourgainLeftParabolaSample (H : ℝ) n j
  rw [bourgainDot_quadraticCurveModel_sub_base]
  fin_cases j
  · simp [bourgainLeftParabolaSample, bourgainPhaseBasis,
      scale] at hlin hquad ⊢
    field_simp [hD.ne', Nat.cast_ne_zero.mpr hH.ne']
      at hlin hquad ⊢
    simp [hH.ne', hD.ne'] at hquad
    rw [hquad]
    ring_nf
    linear_combination
      ((D : ℝ) * (bourgainIndex n : ℝ)) * hlin
  · simp [bourgainLeftParabolaSample, bourgainPhaseBasis,
      scale] at hlin hquad ⊢
    field_simp [hD.ne', Nat.cast_ne_zero.mpr hH.ne']
      at hlin hquad ⊢
    simp [hH.ne', hD.ne'] at hlin
    rw [hlin]
    ring_nf
    linear_combination
      ((bourgainIndex n : ℝ) ^ (2 : ℕ)) * hquad
  · simp [bourgainLeftParabolaSample, bourgainPhaseBasis,
      scale] at hlin hquad ⊢
    field_simp [hD.ne', Nat.cast_ne_zero.mpr hH.ne']
      at hlin hquad ⊢
    simp [hH.ne', hD.ne'] at hlin hquad
    rw [hlin, hquad]
    ring
  · simp [bourgainLeftParabolaSample, bourgainPhaseBasis,
      scale] at hlin hquad ⊢
    field_simp [hD.ne', Nat.cast_ne_zero.mpr hH.ne']
      at hlin hquad ⊢
    simp [hH.ne', hD.ne'] at hlin hquad
    rw [hlin, hquad]
    ring

/-- The right quadratic increment becomes the right independent parabola. -/
theorem bourgainDualPullback_quadraticRight_eq
    {H : ℕ} (hH : 0 < H) {D a b : ℝ}
    (hD : 0 < D) (ha : 0 < a) (hab : a < b)
    (n : Fin H) :
    bourgainDualPullbackFrequency
        (bourgainScaledOsculatingPhaseContinuousLinearEquiv
          (div_ne_zero (Nat.cast_ne_zero.mpr hH.ne') hD.ne')
          ha hab).toLinearEquiv
        (bourgainSquareRootQuadraticCurveModel b
            ((bourgainIndex n : ℝ) / D) -
          bourgainSquareRootCurve (b ^ (2 : ℕ))) =
      bourgainRightParabolaSample (H : ℝ) n := by
  let scale : ℝ := (H : ℝ) / D
  have hscale : scale ≠ 0 :=
    div_ne_zero (Nat.cast_ne_zero.mpr hH.ne') hD.ne'
  let E :=
    bourgainScaledOsculatingPhaseContinuousLinearEquiv
      hscale ha hab
  funext j
  let x : BourgainPhaseSpace := E.symm (bourgainPhaseBasis j)
  have hmap :
      bourgainScaledOsculatingPhaseCoordinates scale a b x =
        bourgainPhaseBasis j := by
    calc
      bourgainScaledOsculatingPhaseCoordinates scale a b x = E x := by
        symm
        exact
          bourgainScaledOsculatingPhaseContinuousLinearEquiv_apply
            hscale ha hab x
      _ = bourgainPhaseBasis j := E.apply_symm_apply _
  have hlin := congrFun hmap (2 : Fin 4)
  have hquad := congrFun hmap (3 : Fin 4)
  change scale *
      bourgainSquareRootPhaseCoordinates a b x 2 =
        bourgainPhaseBasis j 2 at hlin
  change scale ^ (2 : ℕ) *
      bourgainSquareRootPhaseCoordinates a b x 3 =
        bourgainPhaseBasis j 3 at hquad
  rw [← bourgainSquareRootLinearPhaseCoordinate_eq_right
    (a := a) (b := b)] at hlin
  rw [← bourgainSquareRootQuadraticPhaseCoordinate_eq_right
    (a := a) (b := b)] at hquad
  change bourgainDot x
      (bourgainSquareRootQuadraticCurveModel b
          ((bourgainIndex n : ℝ) / D) -
        bourgainSquareRootCurve (b ^ (2 : ℕ))) =
    bourgainRightParabolaSample (H : ℝ) n j
  rw [bourgainDot_quadraticCurveModel_sub_base]
  fin_cases j
  · simp [bourgainRightParabolaSample, bourgainPhaseBasis,
      scale] at hlin hquad ⊢
    field_simp [hD.ne', Nat.cast_ne_zero.mpr hH.ne']
      at hlin hquad ⊢
    simp [hH.ne', hD.ne'] at hlin hquad
    rw [hlin, hquad]
    ring
  · simp [bourgainRightParabolaSample, bourgainPhaseBasis,
      scale] at hlin hquad ⊢
    field_simp [hD.ne', Nat.cast_ne_zero.mpr hH.ne']
      at hlin hquad ⊢
    simp [hH.ne', hD.ne'] at hlin hquad
    rw [hlin, hquad]
    ring
  · simp [bourgainRightParabolaSample, bourgainPhaseBasis,
      scale] at hlin hquad ⊢
    field_simp [hD.ne', Nat.cast_ne_zero.mpr hH.ne']
      at hlin hquad ⊢
    simp [hH.ne', hD.ne'] at hquad
    rw [hquad]
    ring_nf
    linear_combination
      ((D : ℝ) * (bourgainIndex n : ℝ)) * hlin
  · simp [bourgainRightParabolaSample, bourgainPhaseBasis,
      scale] at hlin hquad ⊢
    field_simp [hD.ne', Nat.cast_ne_zero.mpr hH.ne']
      at hlin hquad ⊢
    simp [hH.ne', hD.ne'] at hlin
    rw [hlin]
    ring_nf
    linear_combination
      ((bourgainIndex n : ℝ) ^ (2 : ℕ)) * hquad

end

end RHTower
