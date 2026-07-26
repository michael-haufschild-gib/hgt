/-
# Anisotropic planar transfer for Bourgain's square-root curve

This module makes the phase dilation from a local quadratic square-root
model to the physical planar decoupling box exact.  The diagonal phase map
has determinant `scale⁶`; composing it with the osculating-coordinate map
therefore records both Jacobians explicitly.
-/
import GaloisForLFunctions.RHTower.BourgainSquareRootQuadraticModel

open MeasureTheory

namespace RHTower

noncomputable section

def bourgainParabolaPhaseScaleMatrix
    (scale : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![scale, 0, 0, 0;
     0, scale ^ (2 : ℕ), 0, 0;
     0, 0, scale, 0;
     0, 0, 0, scale ^ (2 : ℕ)]

theorem bourgainParabolaPhaseScaleMatrix_mulVec
    (scale : ℝ) (y : Fin 4 → ℝ) :
    (bourgainParabolaPhaseScaleMatrix scale).mulVec y =
      bourgainParabolaPhaseScale scale y := by
  ext i
  fin_cases i <;>
    simp [bourgainParabolaPhaseScaleMatrix,
      bourgainParabolaPhaseScale, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four]

theorem det_bourgainParabolaPhaseScaleMatrix
    (scale : ℝ) :
    (bourgainParabolaPhaseScaleMatrix scale).det =
      scale ^ (6 : ℕ) := by
  have hdiag :
      bourgainParabolaPhaseScaleMatrix scale =
        Matrix.diagonal ![scale, scale ^ (2 : ℕ), scale, scale ^ (2 : ℕ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [bourgainParabolaPhaseScaleMatrix]
  rw [hdiag, Matrix.det_diagonal, Fin.prod_univ_four]
  simp only [Matrix.cons_val]
  ring

theorem isUnit_bourgainParabolaPhaseScaleMatrix
    {scale : ℝ} (hscale : scale ≠ 0) :
    IsUnit (bourgainParabolaPhaseScaleMatrix scale) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero,
    det_bourgainParabolaPhaseScaleMatrix]
  exact pow_ne_zero 6 hscale

noncomputable def bourgainParabolaPhaseScaleLinearEquiv
    {scale : ℝ} (hscale : scale ≠ 0) :
    (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ) :=
  LinearEquiv.ofBijective
    (bourgainParabolaPhaseScaleMatrix scale).mulVecLin
    ⟨Matrix.mulVec_injective_iff_isUnit.mpr
        (isUnit_bourgainParabolaPhaseScaleMatrix hscale),
      Matrix.mulVec_surjective_iff_isUnit.mpr
        (isUnit_bourgainParabolaPhaseScaleMatrix hscale)⟩

noncomputable def bourgainParabolaPhaseScaleContinuousLinearEquiv
    {scale : ℝ} (hscale : scale ≠ 0) :
    (Fin 4 → ℝ) ≃L[ℝ] (Fin 4 → ℝ) :=
  (bourgainParabolaPhaseScaleLinearEquiv hscale).toContinuousLinearEquiv

@[simp] theorem bourgainParabolaPhaseScaleContinuousLinearEquiv_apply
    {scale : ℝ} (hscale : scale ≠ 0) (y : Fin 4 → ℝ) :
    bourgainParabolaPhaseScaleContinuousLinearEquiv hscale y =
      bourgainParabolaPhaseScale scale y := by
  rw [← bourgainParabolaPhaseScaleMatrix_mulVec]
  rfl

theorem norm_bourgainParabolaPhaseScale_le
    {scale : ℝ} (hscale : scale ≠ 0) (y : Fin 4 → ℝ) :
    ‖bourgainParabolaPhaseScale scale y‖ ≤
      ‖(bourgainParabolaPhaseScaleContinuousLinearEquiv hscale :
          (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ))‖ * ‖y‖ := by
  simpa using
    (bourgainParabolaPhaseScaleContinuousLinearEquiv hscale :
      (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ)).le_opNorm y

theorem map_bourgainParabolaPhaseScaleMatrix_volume
    {scale : ℝ} (hscale : scale ≠ 0) :
    Measure.map
        (Matrix.toLin' (bourgainParabolaPhaseScaleMatrix scale))
        volume =
      ENNReal.ofReal |(scale ^ (6 : ℕ))⁻¹| • volume := by
  rw [Real.map_matrix_volume_pi_eq_smul_volume_pi
    (by rw [det_bourgainParabolaPhaseScaleMatrix]; exact pow_ne_zero 6 hscale)]
  rw [det_bourgainParabolaPhaseScaleMatrix]

theorem setLIntegral_comp_bourgainParabolaPhaseScale_le
    {scale R : ℝ} (hscale : scale ≠ 0)
    (g : (Fin 4 → ℝ) → ENNReal) (hg : Measurable g) :
    (∫⁻ y in {y : Fin 4 → ℝ | ‖y‖ ≤ R},
        g (bourgainParabolaPhaseScale scale y)) ≤
      ENNReal.ofReal |(scale ^ (6 : ℕ))⁻¹| *
        ∫⁻ z in
          {z : Fin 4 → ℝ |
            ‖z‖ ≤
              ‖(bourgainParabolaPhaseScaleContinuousLinearEquiv hscale :
                (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ))‖ * R},
          g z := by
  let M := bourgainParabolaPhaseScaleMatrix scale
  let C : ℝ :=
    ‖(bourgainParabolaPhaseScaleContinuousLinearEquiv hscale :
      (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ))‖
  let A : Set (Fin 4 → ℝ) := {y | ‖y‖ ≤ R}
  let B : Set (Fin 4 → ℝ) := {z | ‖z‖ ≤ C * R}
  have hA : MeasurableSet A := by
    exact measurableSet_Iic.preimage
      ((continuous_norm.comp continuous_id).measurable)
  have hB : MeasurableSet B := by
    exact measurableSet_Iic.preimage
      ((continuous_norm.comp continuous_id).measurable)
  have hM : Measurable (Matrix.toLin' M) :=
    (Matrix.toLin' M).continuous_of_finiteDimensional.measurable
  have hcoord (y : Fin 4 → ℝ) :
      Matrix.toLin' M y = bourgainParabolaPhaseScale scale y := by
    rw [Matrix.toLin'_apply]
    exact bourgainParabolaPhaseScaleMatrix_mulVec scale y
  have hsubset : A ⊆ (Matrix.toLin' M) ⁻¹' B := by
    intro y hy
    change ‖Matrix.toLin' M y‖ ≤ C * R
    rw [hcoord]
    exact (norm_bourgainParabolaPhaseScale_le hscale y).trans
      (mul_le_mul_of_nonneg_left hy (norm_nonneg _))
  change
    (∫⁻ y in A, g (bourgainParabolaPhaseScale scale y)) ≤
      ENNReal.ofReal |(scale ^ (6 : ℕ))⁻¹| *
        ∫⁻ z in B, g z
  calc
    (∫⁻ y in A, g (bourgainParabolaPhaseScale scale y)) =
        ∫⁻ y in A, g (Matrix.toLin' M y) := by
          apply lintegral_congr
          intro y
          rw [hcoord]
    _ ≤ ∫⁻ y in (Matrix.toLin' M) ⁻¹' B,
          g (Matrix.toLin' M y) :=
      lintegral_mono_set hsubset
    _ = ∫⁻ z in B, g z ∂
          Measure.map (Matrix.toLin' M) volume := by
          symm
          exact setLIntegral_map hB hg hM
    _ = ∫⁻ z in B, g z ∂
          (ENNReal.ofReal |(scale ^ (6 : ℕ))⁻¹| • volume) := by
          rw [show Matrix.toLin' M =
              Matrix.toLin' (bourgainParabolaPhaseScaleMatrix scale) by rfl,
            map_bourgainParabolaPhaseScaleMatrix_volume hscale]
    _ =
        ENNReal.ofReal |(scale ^ (6 : ℕ))⁻¹| *
          ∫⁻ z in B, g z := by
          rw [setLIntegral_smul_measure]
          rfl

/-- Combined physical-box estimate after osculating coordinates and the
anisotropic phase dilation.  Both determinant losses are explicit. -/
theorem setLIntegral_comp_scaledPhaseCoordinates_bilinear_subpower
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {a₀ b₀ N scale : ℝ},
        (ha₀ : 0 < a₀) → (ha₀b₀ : a₀ < b₀) →
        (hscale : scale ≠ 0) →
      ∀ (H : ℕ), 0 < H → ∀ (a b : Fin H → ℂ),
      ‖(bourgainParabolaPhaseScaleContinuousLinearEquiv hscale :
          (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ))‖ *
        (‖(bourgainSquareRootPhaseCoordinateContinuousLinearEquiv
            (a := a₀) (b := b₀) ha₀ ha₀b₀ :
            (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ))‖ * N) ≤
          (H : ℝ) ^ (2 : ℕ) / 2 →
      (∫⁻ x in {x : Fin 4 → ℝ | ‖x‖ ≤ N},
        ENNReal.ofReal
          (bourgainScaledIndependentPlanarBilinearIntegrand H a b
            (bourgainParabolaPhaseScale scale
              (bourgainSquareRootPhaseCoordinates a₀ b₀ x)))) ≤
        ENNReal.ofReal
            |(3 * (b₀ - a₀) ^ (4 : ℕ) /
              (32 * a₀ ^ (3 : ℕ) * b₀ ^ (3 : ℕ)))⁻¹| *
          ENNReal.ofReal |(scale ^ (6 : ℕ))⁻¹| *
          ENNReal.ofReal
            ((H : ℝ) ^ (8 : ℕ) *
              (C * (H : ℝ) ^ ε *
                (∑ n : Fin H, ‖a n‖ ^ (2 : ℕ)) ^ (3 : ℕ) *
                (∑ n : Fin H, ‖b n‖ ^ (2 : ℕ)) ^ (3 : ℕ))) := by
  obtain ⟨C, hC, hmass⟩ :=
    integral_scaledIndependentPlanarBilinear_subpower hε
  refine ⟨C, hC, ?_⟩
  intro a₀ b₀ N scale ha₀ ha₀b₀ hscale H hH a b hfit
  let g : (Fin 4 → ℝ) → ENNReal := fun y =>
    ENNReal.ofReal
      (bourgainScaledIndependentPlanarBilinearIntegrand H a b y)
  let C₁ : ℝ :=
    ‖(bourgainSquareRootPhaseCoordinateContinuousLinearEquiv ha₀ ha₀b₀ :
      (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ))‖
  let C₂ : ℝ :=
    ‖(bourgainParabolaPhaseScaleContinuousLinearEquiv hscale :
      (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ))‖
  have hg : Measurable g :=
    measurable_ofReal_bourgainScaledIndependentPlanarBilinearIntegrand
      H a b
  have hgscale : Measurable fun y =>
      g (bourgainParabolaPhaseScale scale y) := by
    apply hg.comp
    have heq :
        bourgainParabolaPhaseScale scale =
          bourgainParabolaPhaseScaleContinuousLinearEquiv hscale := by
      funext y
      symm
      exact bourgainParabolaPhaseScaleContinuousLinearEquiv_apply hscale y
    rw [heq]
    exact
      (bourgainParabolaPhaseScaleContinuousLinearEquiv hscale).continuous.measurable
  have hphase :=
    setLIntegral_comp_bourgainSquareRootPhaseCoordinates_le
      (N := N) ha₀ ha₀b₀
      (fun y => g (bourgainParabolaPhaseScale scale y)) hgscale
  have hscaleChange :=
    setLIntegral_comp_bourgainParabolaPhaseScale_le
      (R := C₁ * N) hscale g hg
  calc
    (∫⁻ x in {x : Fin 4 → ℝ | ‖x‖ ≤ N},
        ENNReal.ofReal
          (bourgainScaledIndependentPlanarBilinearIntegrand H a b
            (bourgainParabolaPhaseScale scale
              (bourgainSquareRootPhaseCoordinates a₀ b₀ x)))) ≤
        ENNReal.ofReal
            |(3 * (b₀ - a₀) ^ (4 : ℕ) /
              (32 * a₀ ^ (3 : ℕ) * b₀ ^ (3 : ℕ)))⁻¹| *
          ∫⁻ y in {y : Fin 4 → ℝ | ‖y‖ ≤ C₁ * N},
            g (bourgainParabolaPhaseScale scale y) := by
              simpa [g, C₁] using hphase
    _ ≤
        ENNReal.ofReal
            |(3 * (b₀ - a₀) ^ (4 : ℕ) /
              (32 * a₀ ^ (3 : ℕ) * b₀ ^ (3 : ℕ)))⁻¹| *
          (ENNReal.ofReal |(scale ^ (6 : ℕ))⁻¹| *
            ∫⁻ z in {z : Fin 4 → ℝ | ‖z‖ ≤ C₂ * (C₁ * N)}, g z) := by
              exact mul_le_mul_right hscaleChange _
    _ ≤
        ENNReal.ofReal
            |(3 * (b₀ - a₀) ^ (4 : ℕ) /
              (32 * a₀ ^ (3 : ℕ) * b₀ ^ (3 : ℕ)))⁻¹| *
          (ENNReal.ofReal |(scale ^ (6 : ℕ))⁻¹| *
            ∫⁻ z in
              {z : Fin 4 → ℝ |
                ‖z‖ ≤ (H : ℝ) ^ (2 : ℕ) / 2}, g z) := by
              apply mul_le_mul_right
              apply mul_le_mul_right
              exact lintegral_mono_set fun z hz => hz.trans hfit
    _ ≤ _ := by
      rw [show g = fun y =>
          ENNReal.ofReal
            (bourgainScaledIndependentPlanarBilinearIntegrand H a b y) by
        rfl]
      rw [setLIntegral_scaledIndependentPlanarBilinear_normCube_eq
        H hH a b]
      conv_lhs => rw [← mul_assoc]
      apply mul_le_mul_right
      exact ENNReal.ofReal_le_ofReal (hmass H hH a b)

/-- One localized pair of quadratic square-root sums satisfies the physical
bilinear sixth-moment estimate after the exact coordinate changes. -/
theorem setLIntegral_bourgainSquareRootQuadraticLocalSum_bilinear_subpower
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {a₀ b₀ N D : ℝ},
        (ha₀ : 0 < a₀) → (ha₀b₀ : a₀ < b₀) →
        (hD : D ≠ 0) →
      ∀ (H : ℕ), (hH : 0 < H) → ∀ (c₁ c₂ : Fin H → ℂ),
      ‖(bourgainParabolaPhaseScaleContinuousLinearEquiv
          (div_ne_zero (Nat.cast_ne_zero.mpr hH.ne') hD) :
          (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ))‖ *
        (‖(bourgainSquareRootPhaseCoordinateContinuousLinearEquiv
            (a := a₀) (b := b₀) ha₀ ha₀b₀ :
            (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ))‖ * N) ≤
          (H : ℝ) ^ (2 : ℕ) / 2 →
      (∫⁻ x in {x : Fin 4 → ℝ | ‖x‖ ≤ N},
        ENNReal.ofReal
          (‖bourgainSquareRootQuadraticLocalSum H D a₀ c₁ x‖ ^ (6 : ℕ) *
            ‖bourgainSquareRootQuadraticLocalSum H D b₀ c₂ x‖ ^
              (6 : ℕ))) ≤
        ENNReal.ofReal
            |(3 * (b₀ - a₀) ^ (4 : ℕ) /
              (32 * a₀ ^ (3 : ℕ) * b₀ ^ (3 : ℕ)))⁻¹| *
          ENNReal.ofReal |(((H : ℝ) / D) ^ (6 : ℕ))⁻¹| *
          ENNReal.ofReal
            ((H : ℝ) ^ (8 : ℕ) *
              (C * (H : ℝ) ^ ε *
                (∑ n : Fin H, ‖c₁ n‖ ^ (2 : ℕ)) ^ (3 : ℕ) *
                (∑ n : Fin H, ‖c₂ n‖ ^ (2 : ℕ)) ^ (3 : ℕ))) := by
  obtain ⟨C, hC, htransfer⟩ :=
    setLIntegral_comp_scaledPhaseCoordinates_bilinear_subpower hε
  refine ⟨C, hC, ?_⟩
  intro a₀ b₀ N D ha₀ ha₀b₀ hD H hH c₁ c₂ hfit
  have hscale : (H : ℝ) / D ≠ 0 :=
    div_ne_zero (Nat.cast_ne_zero.mpr hH.ne') hD
  have hbound :=
    htransfer ha₀ ha₀b₀ hscale H hH c₁ c₂ hfit
  calc
    (∫⁻ x in {x : Fin 4 → ℝ | ‖x‖ ≤ N},
        ENNReal.ofReal
          (‖bourgainSquareRootQuadraticLocalSum H D a₀ c₁ x‖ ^ (6 : ℕ) *
            ‖bourgainSquareRootQuadraticLocalSum H D b₀ c₂ x‖ ^
              (6 : ℕ))) =
        ∫⁻ x in {x : Fin 4 → ℝ | ‖x‖ ≤ N},
          ENNReal.ofReal
            (bourgainScaledIndependentPlanarBilinearIntegrand H c₁ c₂
              (bourgainParabolaPhaseScale ((H : ℝ) / D)
                (bourgainSquareRootPhaseCoordinates a₀ b₀ x))) := by
      apply lintegral_congr
      intro x
      rw [quadraticLocalSum_bilinearIntegrand_eq H hH hD]
    _ ≤ _ := hbound

end

end RHTower
