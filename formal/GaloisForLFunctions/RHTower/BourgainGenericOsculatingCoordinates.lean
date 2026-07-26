/-
# Generic osculating coordinates for Bourgain four-curves

For a curve `(t,t²,φ₃(t),φ₄(t))`, this module constructs the literal
first/half-second-jet coordinate map at two base points.  Whenever its matrix
is invertible, the scaled dual map sends both quadratic osculating models
exactly to two independent sampled parabolas.  No regularity or approximation
hypothesis is used in these algebraic statements.
-/
import GaloisForLFunctions.RHTower.BourgainDualFrequencyCoordinates
import GaloisForLFunctions.RHTower.BourgainTaylorWronskian

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Four-curve used in Bourgain's normalized mean-value reduction. -/
def bourgainGenericFourCurve
    (φ₃ φ₄ : ℝ → ℝ) (t : ℝ) : BourgainPhaseSpace :=
  ![t, t ^ (2 : ℕ), φ₃ t, φ₄ t]

/-- Phase of the generic four-curve. -/
def bourgainGenericFourCurvePhase
    (φ₃ φ₄ : ℝ → ℝ) (x : BourgainPhaseSpace) (t : ℝ) : ℝ :=
  bourgainDot x (bourgainGenericFourCurve φ₃ φ₄ t)

/-- Literal quadratic osculating model at `a`. -/
def bourgainGenericFourCurveQuadraticModel
    (φ₃ φ₄ : ℝ → ℝ) (a s : ℝ) : BourgainPhaseSpace :=
  ![a + s,
    a ^ (2 : ℕ) + 2 * a * s + s ^ (2 : ℕ),
    φ₃ a + iteratedDeriv 1 φ₃ a * s +
      iteratedDeriv 2 φ₃ a * s ^ (2 : ℕ) / 2,
    φ₄ a + iteratedDeriv 1 φ₄ a * s +
      iteratedDeriv 2 φ₄ a * s ^ (2 : ℕ) / 2]

/-- Linear phase coordinate at one base point. -/
def bourgainGenericLinearPhaseCoordinate
    (φ₃ φ₄ : ℝ → ℝ) (a : ℝ) (x : BourgainPhaseSpace) : ℝ :=
  x 0 + 2 * a * x 1 +
    iteratedDeriv 1 φ₃ a * x 2 +
    iteratedDeriv 1 φ₄ a * x 3

/-- Half-second-derivative phase coordinate at one base point. -/
def bourgainGenericQuadraticPhaseCoordinate
    (φ₃ φ₄ : ℝ → ℝ) (a : ℝ) (x : BourgainPhaseSpace) : ℝ :=
  x 1 +
    (iteratedDeriv 2 φ₃ a / 2) * x 2 +
    (iteratedDeriv 2 φ₄ a / 2) * x 3

/-- The quadratic model increment has the expected two phase coordinates. -/
theorem bourgainDot_genericQuadraticModel_sub_base
    (φ₃ φ₄ : ℝ → ℝ) (a s : ℝ) (x : BourgainPhaseSpace) :
    bourgainDot x
        (bourgainGenericFourCurveQuadraticModel φ₃ φ₄ a s -
          bourgainGenericFourCurve φ₃ φ₄ a) =
      bourgainGenericLinearPhaseCoordinate φ₃ φ₄ a x * s +
        bourgainGenericQuadraticPhaseCoordinate φ₃ φ₄ a x *
          s ^ (2 : ℕ) := by
  simp [bourgainDot, bourgainGenericFourCurveQuadraticModel,
    bourgainGenericFourCurve, bourgainGenericLinearPhaseCoordinate,
    bourgainGenericQuadraticPhaseCoordinate, Fin.sum_univ_four]
  ring

/-- Matrix of the two first/half-second jet pairs. -/
def bourgainGenericPhaseCoordinateMatrix
    (φ₃ φ₄ : ℝ → ℝ) (a b : ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 2 * a, iteratedDeriv 1 φ₃ a, iteratedDeriv 1 φ₄ a;
     0, 1, iteratedDeriv 2 φ₃ a / 2, iteratedDeriv 2 φ₄ a / 2;
     1, 2 * b, iteratedDeriv 1 φ₃ b, iteratedDeriv 1 φ₄ b;
     0, 1, iteratedDeriv 2 φ₃ b / 2, iteratedDeriv 2 φ₄ b / 2]

/-- Function represented by the generic jet matrix. -/
def bourgainGenericPhaseCoordinates
    (φ₃ φ₄ : ℝ → ℝ) (a b : ℝ)
    (x : BourgainPhaseSpace) : BourgainPhaseSpace :=
  (bourgainGenericPhaseCoordinateMatrix φ₃ φ₄ a b).mulVec x

@[simp] theorem bourgainGenericPhaseCoordinates_zero
    (φ₃ φ₄ : ℝ → ℝ) (a b : ℝ) (x : BourgainPhaseSpace) :
    bourgainGenericPhaseCoordinates φ₃ φ₄ a b x 0 =
      bourgainGenericLinearPhaseCoordinate φ₃ φ₄ a x := by
  simp [bourgainGenericPhaseCoordinates,
    bourgainGenericPhaseCoordinateMatrix,
    bourgainGenericLinearPhaseCoordinate, Matrix.mulVec,
    dotProduct, Fin.sum_univ_four]

@[simp] theorem bourgainGenericPhaseCoordinates_one
    (φ₃ φ₄ : ℝ → ℝ) (a b : ℝ) (x : BourgainPhaseSpace) :
    bourgainGenericPhaseCoordinates φ₃ φ₄ a b x 1 =
      bourgainGenericQuadraticPhaseCoordinate φ₃ φ₄ a x := by
  simp [bourgainGenericPhaseCoordinates,
    bourgainGenericPhaseCoordinateMatrix,
    bourgainGenericQuadraticPhaseCoordinate, Matrix.mulVec,
    dotProduct, Fin.sum_univ_four]

@[simp] theorem bourgainGenericPhaseCoordinates_two
    (φ₃ φ₄ : ℝ → ℝ) (a b : ℝ) (x : BourgainPhaseSpace) :
    bourgainGenericPhaseCoordinates φ₃ φ₄ a b x 2 =
      bourgainGenericLinearPhaseCoordinate φ₃ φ₄ b x := by
  simp [bourgainGenericPhaseCoordinates,
    bourgainGenericPhaseCoordinateMatrix,
    bourgainGenericLinearPhaseCoordinate, Matrix.mulVec,
    dotProduct, Fin.sum_univ_four]

@[simp] theorem bourgainGenericPhaseCoordinates_three
    (φ₃ φ₄ : ℝ → ℝ) (a b : ℝ) (x : BourgainPhaseSpace) :
    bourgainGenericPhaseCoordinates φ₃ φ₄ a b x 3 =
      bourgainGenericQuadraticPhaseCoordinate φ₃ φ₄ b x := by
  simp [bourgainGenericPhaseCoordinates,
    bourgainGenericPhaseCoordinateMatrix,
    bourgainGenericQuadraticPhaseCoordinate, Matrix.mulVec,
    dotProduct, Fin.sum_univ_four]

/-- Linear equivalence supplied by an invertible generic jet matrix. -/
noncomputable def bourgainGenericPhaseCoordinateLinearEquiv
    (φ₃ φ₄ : ℝ → ℝ) (a b : ℝ)
    (hunit : IsUnit (bourgainGenericPhaseCoordinateMatrix φ₃ φ₄ a b)) :
    BourgainPhaseSpace ≃ₗ[ℝ] BourgainPhaseSpace :=
  LinearEquiv.ofBijective
    (bourgainGenericPhaseCoordinateMatrix φ₃ φ₄ a b).mulVecLin
    ⟨Matrix.mulVec_injective_iff_isUnit.mpr hunit,
      Matrix.mulVec_surjective_iff_isUnit.mpr hunit⟩

/-- Continuous form of the generic jet-coordinate equivalence. -/
noncomputable def bourgainGenericPhaseCoordinateContinuousLinearEquiv
    (φ₃ φ₄ : ℝ → ℝ) (a b : ℝ)
    (hunit : IsUnit (bourgainGenericPhaseCoordinateMatrix φ₃ φ₄ a b)) :
    BourgainPhaseSpace ≃L[ℝ] BourgainPhaseSpace :=
  (bourgainGenericPhaseCoordinateLinearEquiv
    φ₃ φ₄ a b hunit).toContinuousLinearEquiv

@[simp] theorem bourgainGenericPhaseCoordinateContinuousLinearEquiv_apply
    (φ₃ φ₄ : ℝ → ℝ) (a b : ℝ)
    (hunit : IsUnit (bourgainGenericPhaseCoordinateMatrix φ₃ φ₄ a b))
    (x : BourgainPhaseSpace) :
    bourgainGenericPhaseCoordinateContinuousLinearEquiv
        φ₃ φ₄ a b hunit x =
      bourgainGenericPhaseCoordinates φ₃ φ₄ a b x := by
  rfl

/-- Generic jet coordinates followed by parabola scaling. -/
def bourgainGenericScaledPhaseCoordinates
    (φ₃ φ₄ : ℝ → ℝ) (scale a b : ℝ)
    (x : BourgainPhaseSpace) : BourgainPhaseSpace :=
  bourgainParabolaPhaseScale scale
    (bourgainGenericPhaseCoordinates φ₃ φ₄ a b x)

/-- Scaled generic coordinate map as a continuous linear equivalence. -/
noncomputable def bourgainGenericScaledPhaseContinuousLinearEquiv
    (φ₃ φ₄ : ℝ → ℝ) {scale a b : ℝ}
    (hscale : scale ≠ 0)
    (hunit : IsUnit (bourgainGenericPhaseCoordinateMatrix φ₃ φ₄ a b)) :
    BourgainPhaseSpace ≃L[ℝ] BourgainPhaseSpace :=
  (bourgainGenericPhaseCoordinateContinuousLinearEquiv
    φ₃ φ₄ a b hunit).trans
      (bourgainParabolaPhaseScaleContinuousLinearEquiv hscale)

@[simp] theorem bourgainGenericScaledPhaseContinuousLinearEquiv_apply
    (φ₃ φ₄ : ℝ → ℝ) {scale a b : ℝ}
    (hscale : scale ≠ 0)
    (hunit : IsUnit (bourgainGenericPhaseCoordinateMatrix φ₃ φ₄ a b))
    (x : BourgainPhaseSpace) :
    bourgainGenericScaledPhaseContinuousLinearEquiv
        φ₃ φ₄ hscale hunit x =
      bourgainGenericScaledPhaseCoordinates φ₃ φ₄ scale a b x := by
  simp [bourgainGenericScaledPhaseContinuousLinearEquiv,
    bourgainGenericScaledPhaseCoordinates,
    bourgainGenericPhaseCoordinateContinuousLinearEquiv_apply,
    bourgainParabolaPhaseScaleContinuousLinearEquiv_apply]

/-- Exact left curve increment in generic scaled osculating coordinates. -/
def bourgainGenericExactLeftFrequency
    {H : ℕ} (φ₃ φ₄ : ℝ → ℝ) {scale a b : ℝ}
    (hscale : scale ≠ 0)
    (hunit : IsUnit (bourgainGenericPhaseCoordinateMatrix φ₃ φ₄ a b))
    (D : ℝ) (n : Fin H) : BourgainPhaseSpace :=
  bourgainDualPullbackFrequency
    (bourgainGenericScaledPhaseContinuousLinearEquiv
      φ₃ φ₄ hscale hunit).toLinearEquiv
    (bourgainGenericFourCurve φ₃ φ₄
        (a + (bourgainIndex n : ℝ) / D) -
      bourgainGenericFourCurve φ₃ φ₄ a)

/-- Exact right curve increment in generic scaled osculating coordinates. -/
def bourgainGenericExactRightFrequency
    {H : ℕ} (φ₃ φ₄ : ℝ → ℝ) {scale a b : ℝ}
    (hscale : scale ≠ 0)
    (hunit : IsUnit (bourgainGenericPhaseCoordinateMatrix φ₃ φ₄ a b))
    (D : ℝ) (n : Fin H) : BourgainPhaseSpace :=
  bourgainDualPullbackFrequency
    (bourgainGenericScaledPhaseContinuousLinearEquiv
      φ₃ φ₄ hscale hunit).toLinearEquiv
    (bourgainGenericFourCurve φ₃ φ₄
        (b + (bourgainIndex n : ℝ) / D) -
      bourgainGenericFourCurve φ₃ φ₄ b)

/-- The left quadratic osculating increment becomes the left independent
sampled parabola. -/
theorem bourgainGenericDualPullback_quadraticLeft_eq
    {H : ℕ} (hH : 0 < H) (φ₃ φ₄ : ℝ → ℝ)
    {D scale a b : ℝ} (hD : 0 < D)
    (hscale : scale = (H : ℝ) / D)
    (hscale0 : scale ≠ 0)
    (hunit : IsUnit (bourgainGenericPhaseCoordinateMatrix φ₃ φ₄ a b))
    (n : Fin H) :
    bourgainDualPullbackFrequency
        (bourgainGenericScaledPhaseContinuousLinearEquiv
          φ₃ φ₄ hscale0 hunit).toLinearEquiv
        (bourgainGenericFourCurveQuadraticModel φ₃ φ₄ a
            ((bourgainIndex n : ℝ) / D) -
          bourgainGenericFourCurve φ₃ φ₄ a) =
      bourgainLeftParabolaSample (H : ℝ) n := by
  let E :=
    bourgainGenericScaledPhaseContinuousLinearEquiv
      φ₃ φ₄ hscale0 hunit
  funext j
  let x : BourgainPhaseSpace := E.symm (bourgainPhaseBasis j)
  have hmap :
      bourgainGenericScaledPhaseCoordinates φ₃ φ₄ scale a b x =
        bourgainPhaseBasis j := by
    calc
      bourgainGenericScaledPhaseCoordinates φ₃ φ₄ scale a b x = E x := by
        symm
        exact bourgainGenericScaledPhaseContinuousLinearEquiv_apply
          φ₃ φ₄ hscale0 hunit x
      _ = bourgainPhaseBasis j := E.apply_symm_apply _
  have hlin := congrFun hmap (0 : Fin 4)
  have hquad := congrFun hmap (1 : Fin 4)
  simp only [bourgainGenericScaledPhaseCoordinates,
    bourgainParabolaPhaseScale, Matrix.cons_val,
    bourgainGenericPhaseCoordinates_zero] at hlin
  simp only [bourgainGenericScaledPhaseCoordinates,
    bourgainParabolaPhaseScale, Matrix.cons_val,
    bourgainGenericPhaseCoordinates_one] at hquad
  change bourgainDot x
      (bourgainGenericFourCurveQuadraticModel φ₃ φ₄ a
          ((bourgainIndex n : ℝ) / D) -
        bourgainGenericFourCurve φ₃ φ₄ a) =
    bourgainLeftParabolaSample (H : ℝ) n j
  rw [bourgainDot_genericQuadraticModel_sub_base]
  subst scale
  fin_cases j
  · simp [bourgainLeftParabolaSample, bourgainPhaseBasis] at hlin hquad ⊢
    field_simp [hD.ne', Nat.cast_ne_zero.mpr hH.ne'] at hlin hquad ⊢
    simp [hH.ne', hD.ne'] at hquad
    rw [hquad]
    ring_nf
    linear_combination
      ((D : ℝ) * (bourgainIndex n : ℝ)) * hlin
  · simp [bourgainLeftParabolaSample, bourgainPhaseBasis] at hlin hquad ⊢
    field_simp [hD.ne', Nat.cast_ne_zero.mpr hH.ne'] at hlin hquad ⊢
    simp [hH.ne', hD.ne'] at hlin
    rw [hlin]
    ring_nf
    linear_combination
      ((bourgainIndex n : ℝ) ^ (2 : ℕ)) * hquad
  · simp [bourgainLeftParabolaSample, bourgainPhaseBasis] at hlin hquad ⊢
    field_simp [hD.ne', Nat.cast_ne_zero.mpr hH.ne'] at hlin hquad ⊢
    simp [hH.ne', hD.ne'] at hlin hquad
    rw [hlin, hquad]
    ring
  · simp [bourgainLeftParabolaSample, bourgainPhaseBasis] at hlin hquad ⊢
    field_simp [hD.ne', Nat.cast_ne_zero.mpr hH.ne'] at hlin hquad ⊢
    simp [hH.ne', hD.ne'] at hlin hquad
    rw [hlin, hquad]
    ring

/-- Right-hand analogue of the generic quadratic pullback identity. -/
theorem bourgainGenericDualPullback_quadraticRight_eq
    {H : ℕ} (hH : 0 < H) (φ₃ φ₄ : ℝ → ℝ)
    {D scale a b : ℝ} (hD : 0 < D)
    (hscale : scale = (H : ℝ) / D)
    (hscale0 : scale ≠ 0)
    (hunit : IsUnit (bourgainGenericPhaseCoordinateMatrix φ₃ φ₄ a b))
    (n : Fin H) :
    bourgainDualPullbackFrequency
        (bourgainGenericScaledPhaseContinuousLinearEquiv
          φ₃ φ₄ hscale0 hunit).toLinearEquiv
        (bourgainGenericFourCurveQuadraticModel φ₃ φ₄ b
            ((bourgainIndex n : ℝ) / D) -
          bourgainGenericFourCurve φ₃ φ₄ b) =
      bourgainRightParabolaSample (H : ℝ) n := by
  let E :=
    bourgainGenericScaledPhaseContinuousLinearEquiv
      φ₃ φ₄ hscale0 hunit
  funext j
  let x : BourgainPhaseSpace := E.symm (bourgainPhaseBasis j)
  have hmap :
      bourgainGenericScaledPhaseCoordinates φ₃ φ₄ scale a b x =
        bourgainPhaseBasis j := by
    calc
      bourgainGenericScaledPhaseCoordinates φ₃ φ₄ scale a b x = E x := by
        symm
        exact bourgainGenericScaledPhaseContinuousLinearEquiv_apply
          φ₃ φ₄ hscale0 hunit x
      _ = bourgainPhaseBasis j := E.apply_symm_apply _
  have hlin := congrFun hmap (2 : Fin 4)
  have hquad := congrFun hmap (3 : Fin 4)
  simp only [bourgainGenericScaledPhaseCoordinates,
    bourgainParabolaPhaseScale, Matrix.cons_val,
    bourgainGenericPhaseCoordinates_two] at hlin
  simp only [bourgainGenericScaledPhaseCoordinates,
    bourgainParabolaPhaseScale, Matrix.cons_val,
    bourgainGenericPhaseCoordinates_three] at hquad
  change bourgainDot x
      (bourgainGenericFourCurveQuadraticModel φ₃ φ₄ b
          ((bourgainIndex n : ℝ) / D) -
        bourgainGenericFourCurve φ₃ φ₄ b) =
    bourgainRightParabolaSample (H : ℝ) n j
  rw [bourgainDot_genericQuadraticModel_sub_base]
  subst scale
  fin_cases j
  · simp [bourgainRightParabolaSample, bourgainPhaseBasis] at hlin hquad ⊢
    field_simp [hD.ne', Nat.cast_ne_zero.mpr hH.ne'] at hlin hquad ⊢
    simp [hH.ne', hD.ne'] at hlin hquad
    rw [hlin, hquad]
    ring
  · simp [bourgainRightParabolaSample, bourgainPhaseBasis] at hlin hquad ⊢
    field_simp [hD.ne', Nat.cast_ne_zero.mpr hH.ne'] at hlin hquad ⊢
    simp [hH.ne', hD.ne'] at hlin hquad
    rw [hlin, hquad]
    ring
  · simp [bourgainRightParabolaSample, bourgainPhaseBasis] at hlin hquad ⊢
    field_simp [hD.ne', Nat.cast_ne_zero.mpr hH.ne'] at hlin hquad ⊢
    simp [hH.ne', hD.ne'] at hquad
    rw [hquad]
    ring_nf
    linear_combination
      ((D : ℝ) * (bourgainIndex n : ℝ)) * hlin
  · simp [bourgainRightParabolaSample, bourgainPhaseBasis] at hlin hquad ⊢
    field_simp [hD.ne', Nat.cast_ne_zero.mpr hH.ne'] at hlin hquad ⊢
    simp [hH.ne', hD.ne'] at hlin
    rw [hlin]
    ring_nf
    linear_combination
      ((bourgainIndex n : ℝ) ^ (2 : ℕ)) * hquad

end

end RHTower
