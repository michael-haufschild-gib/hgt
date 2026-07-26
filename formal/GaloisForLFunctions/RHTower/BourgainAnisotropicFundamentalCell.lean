/-
# Anisotropic fundamental cell in osculating coordinates

Bourgain's Section 2 uses the periods `H,H²,H,H²`, whose product is `H⁶`.
This module defines that exact cell and pulls it back through the combined
osculating-coordinate and parabola-dilation map.  Both Jacobians and the
sharp cell volume are retained exactly.
-/
import GaloisForLFunctions.RHTower.BourgainParabolaFundamentalCell
import GaloisForLFunctions.RHTower.BourgainA6FirstSpacingBridge
import GaloisForLFunctions.RHTower.BourgainAnisotropicPlanarTransfer

open MeasureTheory

namespace RHTower

noncomputable section

/-- Half-widths of one centered physical period cell. -/
def bourgainParabolaFundamentalHalfWidth
    (H : ℕ) : BourgainPhaseSpace :=
  ![(H : ℝ) / 2, (H : ℝ) ^ (2 : ℕ) / 2,
    (H : ℝ) / 2, (H : ℝ) ^ (2 : ℕ) / 2]

/-- Centered fundamental period cell with side lengths `H,H²,H,H²`. -/
def bourgainParabolaFundamentalCell
    (H : ℕ) : Set BourgainPhaseSpace :=
  bourgainFullBox (bourgainParabolaFundamentalHalfWidth H)

theorem measurableSet_bourgainParabolaFundamentalCell
    (H : ℕ) :
    MeasurableSet (bourgainParabolaFundamentalCell H) := by
  exact measurableSet_bourgainFullBox _

/-- Exact volume `H⁶` of the anisotropic fundamental cell. -/
theorem volume_bourgainParabolaFundamentalCell
    (H : ℕ) :
    volume (bourgainParabolaFundamentalCell H) =
      ENNReal.ofReal ((H : ℝ) ^ (6 : ℕ)) := by
  unfold bourgainParabolaFundamentalCell bourgainFullBox
    bourgainParabolaFundamentalHalfWidth
  rw [Real.volume_pi_Ioc, Fin.prod_univ_four]
  simp [Matrix.cons_val]
  ring

/-- Every point of the period cell has sup norm at most `H²/2`. -/
theorem norm_le_sq_half_of_mem_bourgainParabolaFundamentalCell
    {H : ℕ} (hH : 0 < H) {y : BourgainPhaseSpace}
    (hy : y ∈ bourgainParabolaFundamentalCell H) :
    ‖y‖ ≤ (H : ℝ) ^ (2 : ℕ) / 2 := by
  let R : NNReal :=
    ⟨(H : ℝ) ^ (2 : ℕ) / 2, by positivity⟩
  rw [Pi.norm_def]
  change
    (↑((Finset.univ : Finset (Fin 4)).sup fun j => ‖y j‖₊) : ℝ) ≤
      (R : ℝ)
  rw [NNReal.coe_le_coe]
  apply Finset.sup_le
  intro j hj
  rw [← NNReal.coe_le_coe]
  change ‖y j‖ ≤ (H : ℝ) ^ (2 : ℕ) / 2
  have hyj :
      y j ∈ Set.Ioc
      (-(bourgainParabolaFundamentalHalfWidth H j))
        (bourgainParabolaFundamentalHalfWidth H j) := by
    exact hy (Set.mem_univ j)
  have habs :
      |y j| ≤ bourgainParabolaFundamentalHalfWidth H j :=
    abs_le.2 ⟨hyj.1.le, hyj.2⟩
  rw [Real.norm_eq_abs]
  refine habs.trans ?_
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
  fin_cases j <;>
    simp [bourgainParabolaFundamentalHalfWidth, Matrix.cons_val] <;>
    nlinarith [sq_nonneg ((H : ℝ) - 1)]

/-- Inverse distortion estimate for the diagonal parabola phase scale. -/
theorem norm_le_inverseNorm_mul_norm_bourgainParabolaPhaseScale
    {scale : ℝ} (hscale : scale ≠ 0) (y : BourgainPhaseSpace) :
    ‖y‖ ≤
      ‖((bourgainParabolaPhaseScaleContinuousLinearEquiv hscale).symm :
          BourgainPhaseSpace →L[ℝ] BourgainPhaseSpace)‖ *
        ‖bourgainParabolaPhaseScale scale y‖ := by
  have h :=
    ((bourgainParabolaPhaseScaleContinuousLinearEquiv hscale).symm :
      BourgainPhaseSpace →L[ℝ] BourgainPhaseSpace).le_opNorm
        (bourgainParabolaPhaseScale scale y)
  calc
    ‖y‖ =
        ‖(bourgainParabolaPhaseScaleContinuousLinearEquiv hscale).symm
          (bourgainParabolaPhaseScaleContinuousLinearEquiv hscale y)‖ := by
      rw [ContinuousLinearEquiv.symm_apply_apply]
    _ =
        ‖(bourgainParabolaPhaseScaleContinuousLinearEquiv hscale).symm
          (bourgainParabolaPhaseScale scale y)‖ := by
      rw [bourgainParabolaPhaseScaleContinuousLinearEquiv_apply]
    _ ≤ _ := h

/-- Real integral over the centered anisotropic bilinear period cell, in
the coordinate order produced by the finite-product measure. -/
def bourgainScaledParabolaBilinearCenteredMoment
    (H : ℕ) (a₁ a₂ : Fin H → ℂ) : ℝ :=
  ∫ z₀ in (-(H : ℝ) / 2)..((H : ℝ) / 2),
    ∫ z₁ in (-((H : ℝ) ^ (2 : ℕ)) / 2)..
        ((H : ℝ) ^ (2 : ℕ) / 2),
      ∫ z₂ in (-(H : ℝ) / 2)..((H : ℝ) / 2),
        ∫ z₃ in (-((H : ℝ) ^ (2 : ℕ)) / 2)..
            ((H : ℝ) ^ (2 : ℕ) / 2),
          bourgainScaledIndependentPlanarBilinearIntegrand
            H a₁ a₂ ![z₀, z₁, z₂, z₃]

/-- The centered four-coordinate cell is exactly the product fundamental
moment from `BourgainParabolaFundamentalCell`. -/
theorem bourgainScaledParabolaBilinearCenteredMoment_eq_fundamental
    (H : ℕ) (hH : 0 < H) (a₁ a₂ : Fin H → ℂ) :
    bourgainScaledParabolaBilinearCenteredMoment H a₁ a₂ =
      bourgainScaledParabolaBilinearFundamentalMoment H a₁ a₂ := by
  let R₀ : ℝ := (H : ℝ) / 2
  let R₁ : ℝ := (H : ℝ) ^ (2 : ℕ) / 2
  let f : BourgainPhaseSpace → ℝ := fun z =>
    bourgainScaledIndependentPlanarBilinearIntegrand H a₁ a₂ z
  have hR₀ : 0 ≤ R₀ := by positivity
  have hR₁ : 0 ≤ R₁ := by positivity
  have hf : Continuous f := by
    unfold f bourgainScaledIndependentPlanarBilinearIntegrand
      bourgainScaledPlanarSixthMass
      bourgainScaledParabolaExtension
      bourgainDiscreteParabolaExtension bourgainUnitCharacter
    fun_prop
  have hreorder :=
    intervalIntegral_four_reorder_two_three_one_zero
      hR₀ hR₁ hR₀ hR₁ f hf
  let I₁ : ℝ :=
    ∫ y in (-R₁)..R₁,
      ∫ x in (-R₀)..R₀,
        bourgainScaledPlanarSixthMass H a₁ x y
  let J₂ : ℝ :=
    ∫ x in (-R₀)..R₀,
      ∫ y in (-R₁)..R₁,
        bourgainScaledPlanarSixthMass H a₂ x y
  have hfactor :
      (∫ z₂ in (-R₀)..R₀,
        ∫ z₃ in (-R₁)..R₁,
          ∫ z₁ in (-R₁)..R₁,
            ∫ z₀ in (-R₀)..R₀,
              f ![z₀, z₁, z₂, z₃]) =
        I₁ * J₂ := by
    simp [f, I₁, J₂,
      bourgainScaledIndependentPlanarBilinearIntegrand,
      Matrix.cons_val]
  have hswap₂ :
      J₂ =
        ∫ y in (-R₁)..R₁,
          ∫ x in (-R₀)..R₀,
            bourgainScaledPlanarSixthMass H a₂ x y := by
    unfold J₂
    exact intervalIntegral_intervalIntegral_swap
      (neg_le_self hR₀) (neg_le_self hR₁)
      (bourgainScaledPlanarSixthMass H a₂)
      (continuous_uncurry_bourgainScaledPlanarSixthMass H a₂)
  have hcenter₁ :
      I₁ =
        ∫ y in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
          ∫ x in (0 : ℝ)..(H : ℝ),
            bourgainScaledPlanarSixthMass H a₁ x y := by
    simpa [I₁, R₀, R₁, bourgainScaledPlanarSixthMass,
      neg_div] using
      (integral_scaledParabola_centeredFundamentalCell_eq H hH a₁)
  have hcenter₂ :
      J₂ =
        ∫ y in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
          ∫ x in (0 : ℝ)..(H : ℝ),
            bourgainScaledPlanarSixthMass H a₂ x y := by
    rw [hswap₂]
    simpa [R₀, R₁, bourgainScaledPlanarSixthMass,
      neg_div] using
      (integral_scaledParabola_centeredFundamentalCell_eq H hH a₂)
  calc
    bourgainScaledParabolaBilinearCenteredMoment H a₁ a₂ =
        ∫ z₂ in (-R₀)..R₀,
          ∫ z₃ in (-R₁)..R₁,
            ∫ z₁ in (-R₁)..R₁,
              ∫ z₀ in (-R₀)..R₀,
                f ![z₀, z₁, z₂, z₃] := by
      simpa [bourgainScaledParabolaBilinearCenteredMoment,
        R₀, R₁, f, neg_div] using hreorder
    _ = I₁ * J₂ := hfactor
    _ =
        (∫ y in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
          ∫ x in (0 : ℝ)..(H : ℝ),
            bourgainScaledPlanarSixthMass H a₁ x y) *
        (∫ y in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
          ∫ x in (0 : ℝ)..(H : ℝ),
            bourgainScaledPlanarSixthMass H a₂ x y) := by
      rw [hcenter₁, hcenter₂]
    _ = bourgainScaledParabolaBilinearFundamentalMoment H a₁ a₂ := by
      rw [bourgainScaledParabolaBilinearFundamentalMoment_eq_mul]
      rfl

/-- The nonnegative Lebesgue integral over the centered anisotropic cell is
the `ENNReal` lift of the exact real fundamental moment. -/
theorem setLIntegral_bourgainParabolaFundamentalCell_eq
    (H : ℕ) (hH : 0 < H) (a₁ a₂ : Fin H → ℂ) :
    (∫⁻ z in bourgainParabolaFundamentalCell H,
      ENNReal.ofReal
        (bourgainScaledIndependentPlanarBilinearIntegrand H a₁ a₂ z)) =
      ENNReal.ofReal
        (bourgainScaledParabolaBilinearFundamentalMoment H a₁ a₂) := by
  let X := bourgainParabolaFundamentalHalfWidth H
  let f : BourgainPhaseSpace → ℝ := fun z =>
    bourgainScaledIndependentPlanarBilinearIntegrand H a₁ a₂ z
  have hf : Continuous f := by
    unfold f bourgainScaledIndependentPlanarBilinearIntegrand
      bourgainScaledPlanarSixthMass
      bourgainScaledParabolaExtension
      bourgainDiscreteParabolaExtension bourgainUnitCharacter
    fun_prop
  have hn : ∀ z, 0 ≤ f z := by
    intro z
    unfold f bourgainScaledIndependentPlanarBilinearIntegrand
      bourgainScaledPlanarSixthMass
    positivity
  rw [show bourgainParabolaFundamentalCell H =
      bourgainFullBox X by rfl]
  rw [setLIntegral_bourgainFullBox_eq_iterated X
    (fun z => ENNReal.ofReal (f z)) hf.measurable.ennreal_ofReal]
  have hconvert :=
    lintegral_Ioc_four_ofReal_eq_ofReal_intervalIntegral
      (by simp [X, bourgainParabolaFundamentalHalfWidth]; positivity :
        0 ≤ X 0)
      (by simp [X, bourgainParabolaFundamentalHalfWidth]; positivity :
        0 ≤ X 1)
      (by simp [X, bourgainParabolaFundamentalHalfWidth]; positivity :
        0 ≤ X 2)
      (by simp [X, bourgainParabolaFundamentalHalfWidth]; positivity :
        0 ≤ X 3)
      f hf hn
  rw [hconvert]
  congr 1
  simpa [X, f, bourgainParabolaFundamentalHalfWidth,
    bourgainScaledParabolaBilinearCenteredMoment,
    Matrix.cons_val, neg_div] using
    (bourgainScaledParabolaBilinearCenteredMoment_eq_fundamental
      H hH a₁ a₂)

/-- Matrix of the combined osculating-coordinate and physical parabola
dilation map. -/
def bourgainScaledOsculatingPhaseMatrix
    (scale a b : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  bourgainParabolaPhaseScaleMatrix scale *
    bourgainSquareRootPhaseCoordinateMatrix a b

/-- Function represented by the combined matrix. -/
def bourgainScaledOsculatingPhaseCoordinates
    (scale a b : ℝ) (x : BourgainPhaseSpace) : BourgainPhaseSpace :=
  bourgainParabolaPhaseScale scale
    (bourgainSquareRootPhaseCoordinates a b x)

theorem bourgainScaledOsculatingPhaseMatrix_mulVec
    (scale a b : ℝ) (x : BourgainPhaseSpace) :
    (bourgainScaledOsculatingPhaseMatrix scale a b).mulVec x =
      bourgainScaledOsculatingPhaseCoordinates scale a b x := by
  unfold bourgainScaledOsculatingPhaseMatrix
    bourgainScaledOsculatingPhaseCoordinates
  rw [← Matrix.mulVec_mulVec,
    bourgainParabolaPhaseScaleMatrix_mulVec]
  rfl

/-- Exact determinant of the combined phase map. -/
theorem det_bourgainScaledOsculatingPhaseMatrix
    {scale a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (bourgainScaledOsculatingPhaseMatrix scale a b).det =
      scale ^ (6 : ℕ) *
        (3 * (b - a) ^ (4 : ℕ) /
          (32 * a ^ (3 : ℕ) * b ^ (3 : ℕ))) := by
  unfold bourgainScaledOsculatingPhaseMatrix
  rw [Matrix.det_mul, det_bourgainParabolaPhaseScaleMatrix,
    det_bourgainSquareRootPhaseCoordinateMatrix ha hb]

/-- Pullback of one fundamental period cell. -/
def bourgainOsculatingFundamentalCell
    (H : ℕ) (scale a b : ℝ) : Set BourgainPhaseSpace :=
  bourgainScaledOsculatingPhaseCoordinates scale a b ⁻¹'
    bourgainParabolaFundamentalCell H

/-- Uniform norm radius of a pulled-back period cell, expressed through the
two exact inverse operator norms. -/
theorem norm_le_of_mem_bourgainOsculatingFundamentalCell
    {H : ℕ} (hH : 0 < H) {scale a b : ℝ}
    (hscale : scale ≠ 0) (ha : 0 < a) (hab : a < b)
    {x : BourgainPhaseSpace}
    (hx : x ∈ bourgainOsculatingFundamentalCell H scale a b) :
    ‖x‖ ≤
      ‖((bourgainSquareRootPhaseCoordinateContinuousLinearEquiv
          ha hab).symm : BourgainPhaseSpace →L[ℝ] BourgainPhaseSpace)‖ *
        (‖((bourgainParabolaPhaseScaleContinuousLinearEquiv
            hscale).symm : BourgainPhaseSpace →L[ℝ] BourgainPhaseSpace)‖ *
          ((H : ℝ) ^ (2 : ℕ) / 2)) := by
  have hcell :
      bourgainScaledOsculatingPhaseCoordinates scale a b x ∈
        bourgainParabolaFundamentalCell H :=
    hx
  have hscaled :
      ‖bourgainScaledOsculatingPhaseCoordinates scale a b x‖ ≤
        (H : ℝ) ^ (2 : ℕ) / 2 :=
    norm_le_sq_half_of_mem_bourgainParabolaFundamentalCell hH hcell
  have hphase :
      ‖bourgainSquareRootPhaseCoordinates a b x‖ ≤
        ‖((bourgainParabolaPhaseScaleContinuousLinearEquiv
            hscale).symm : BourgainPhaseSpace →L[ℝ] BourgainPhaseSpace)‖ *
          ((H : ℝ) ^ (2 : ℕ) / 2) := by
    refine
      (norm_le_inverseNorm_mul_norm_bourgainParabolaPhaseScale
        hscale (bourgainSquareRootPhaseCoordinates a b x)).trans ?_
    exact mul_le_mul_of_nonneg_left hscaled (norm_nonneg _)
  refine
    (norm_le_inverseNorm_mul_norm_bourgainSquareRootPhaseCoordinates
      ha hab x).trans ?_
  exact mul_le_mul_of_nonneg_left hphase (norm_nonneg _)

/-- Exact Lebesgue pushforward under the combined phase map. -/
theorem map_bourgainScaledOsculatingPhaseMatrix_volume
    {scale a b : ℝ} (hscale : scale ≠ 0)
    (ha : 0 < a) (hab : a < b) :
    Measure.map
        (Matrix.toLin'
          (bourgainScaledOsculatingPhaseMatrix scale a b))
        volume =
      ENNReal.ofReal
          |(scale ^ (6 : ℕ) *
            (3 * (b - a) ^ (4 : ℕ) /
              (32 * a ^ (3 : ℕ) * b ^ (3 : ℕ))))⁻¹| •
        volume := by
  have hb : 0 < b := ha.trans hab
  have hdet :
      (bourgainScaledOsculatingPhaseMatrix scale a b).det ≠ 0 := by
    rw [det_bourgainScaledOsculatingPhaseMatrix ha.ne' hb.ne']
    apply mul_ne_zero (pow_ne_zero 6 hscale)
    exact ne_of_gt
      (div_pos
        (mul_pos (by norm_num) (pow_pos (sub_pos.mpr hab) 4))
        (mul_pos (mul_pos (by norm_num) (pow_pos ha 3))
          (pow_pos hb 3)))
  rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hdet]
  rw [det_bourgainScaledOsculatingPhaseMatrix ha.ne' hb.ne']

/-- Exact volume of the pulled-back anisotropic fundamental cell. -/
theorem volume_bourgainOsculatingFundamentalCell
    (H : ℕ) {scale a b : ℝ} (hscale : scale ≠ 0)
    (ha : 0 < a) (hab : a < b) :
    volume (bourgainOsculatingFundamentalCell H scale a b) =
      ENNReal.ofReal
          |(scale ^ (6 : ℕ) *
            (3 * (b - a) ^ (4 : ℕ) /
              (32 * a ^ (3 : ℕ) * b ^ (3 : ℕ))))⁻¹| *
        ENNReal.ofReal ((H : ℝ) ^ (6 : ℕ)) := by
  let M := bourgainScaledOsculatingPhaseMatrix scale a b
  have hM : Measurable (Matrix.toLin' M) :=
    (Matrix.toLin' M).continuous_of_finiteDimensional.measurable
  have hcell := measurableSet_bourgainParabolaFundamentalCell H
  have hcoord (x : BourgainPhaseSpace) :
      Matrix.toLin' M x =
        bourgainScaledOsculatingPhaseCoordinates scale a b x := by
    rw [Matrix.toLin'_apply]
    exact bourgainScaledOsculatingPhaseMatrix_mulVec scale a b x
  have hset :
      bourgainOsculatingFundamentalCell H scale a b =
        (Matrix.toLin' M) ⁻¹'
          bourgainParabolaFundamentalCell H := by
    ext x
    simp only [bourgainOsculatingFundamentalCell, Set.mem_preimage]
    rw [hcoord]
  calc
    volume (bourgainOsculatingFundamentalCell H scale a b) =
        volume ((Matrix.toLin' M) ⁻¹'
          bourgainParabolaFundamentalCell H) := by
      rw [hset]
    _ = (Measure.map (Matrix.toLin' M) volume)
          (bourgainParabolaFundamentalCell H) := by
      exact (Measure.map_apply hM hcell).symm
    _ =
        (ENNReal.ofReal
            |(scale ^ (6 : ℕ) *
              (3 * (b - a) ^ (4 : ℕ) /
                (32 * a ^ (3 : ℕ) * b ^ (3 : ℕ))))⁻¹| •
          volume) (bourgainParabolaFundamentalCell H) := by
      rw [show M =
          bourgainScaledOsculatingPhaseMatrix scale a b by rfl,
        map_bourgainScaledOsculatingPhaseMatrix_volume hscale ha hab]
    _ = _ := by
      rw [Measure.smul_apply,
        volume_bourgainParabolaFundamentalCell]
      rfl

/-- Exact change of variables for the bilinear integrand on one pulled-back
anisotropic period cell. -/
theorem setLIntegral_bourgainOsculatingFundamentalCell_eq
    (H : ℕ) (hH : 0 < H) {scale a b : ℝ}
    (hscale : scale ≠ 0) (ha : 0 < a) (hab : a < b)
    (c₁ c₂ : Fin H → ℂ) :
    (∫⁻ x in bourgainOsculatingFundamentalCell H scale a b,
      ENNReal.ofReal
        (bourgainScaledIndependentPlanarBilinearIntegrand H c₁ c₂
          (bourgainScaledOsculatingPhaseCoordinates scale a b x))) =
      ENNReal.ofReal
          |(scale ^ (6 : ℕ) *
            (3 * (b - a) ^ (4 : ℕ) /
              (32 * a ^ (3 : ℕ) * b ^ (3 : ℕ))))⁻¹| *
        ENNReal.ofReal
          (bourgainScaledParabolaBilinearFundamentalMoment H c₁ c₂) := by
  let M := bourgainScaledOsculatingPhaseMatrix scale a b
  let g : BourgainPhaseSpace → ENNReal := fun y =>
    ENNReal.ofReal
      (bourgainScaledIndependentPlanarBilinearIntegrand H c₁ c₂ y)
  have hM : Measurable (Matrix.toLin' M) :=
    (Matrix.toLin' M).continuous_of_finiteDimensional.measurable
  have hg : Measurable g :=
    measurable_ofReal_bourgainScaledIndependentPlanarBilinearIntegrand
      H c₁ c₂
  have hcell := measurableSet_bourgainParabolaFundamentalCell H
  have hcoord (x : BourgainPhaseSpace) :
      Matrix.toLin' M x =
        bourgainScaledOsculatingPhaseCoordinates scale a b x := by
    rw [Matrix.toLin'_apply]
    exact bourgainScaledOsculatingPhaseMatrix_mulVec scale a b x
  have hset :
      bourgainOsculatingFundamentalCell H scale a b =
        (Matrix.toLin' M) ⁻¹'
          bourgainParabolaFundamentalCell H := by
    ext x
    simp only [bourgainOsculatingFundamentalCell, Set.mem_preimage]
    rw [hcoord]
  calc
    (∫⁻ x in bourgainOsculatingFundamentalCell H scale a b,
      ENNReal.ofReal
        (bourgainScaledIndependentPlanarBilinearIntegrand H c₁ c₂
          (bourgainScaledOsculatingPhaseCoordinates scale a b x))) =
        ∫⁻ x in (Matrix.toLin' M) ⁻¹'
            bourgainParabolaFundamentalCell H,
          g (Matrix.toLin' M x) := by
      rw [hset]
      apply setLIntegral_congr_fun (hcell.preimage hM)
      intro x hx
      simp only [g]
      rw [hcoord]
    _ =
        ∫⁻ y in bourgainParabolaFundamentalCell H, g y ∂
          Measure.map (Matrix.toLin' M) volume := by
      symm
      exact setLIntegral_map hcell hg hM
    _ =
        ∫⁻ y in bourgainParabolaFundamentalCell H, g y ∂
          (ENNReal.ofReal
              |(scale ^ (6 : ℕ) *
                (3 * (b - a) ^ (4 : ℕ) /
                  (32 * a ^ (3 : ℕ) * b ^ (3 : ℕ))))⁻¹| •
            volume) := by
      rw [show M =
          bourgainScaledOsculatingPhaseMatrix scale a b by rfl,
        map_bourgainScaledOsculatingPhaseMatrix_volume hscale ha hab]
    _ =
        ENNReal.ofReal
            |(scale ^ (6 : ℕ) *
              (3 * (b - a) ^ (4 : ℕ) /
                (32 * a ^ (3 : ℕ) * b ^ (3 : ℕ))))⁻¹| *
          ∫⁻ y in bourgainParabolaFundamentalCell H, g y := by
      rw [setLIntegral_smul_measure]
      rfl
    _ = _ := by
      rw [show
          (∫⁻ y in bourgainParabolaFundamentalCell H, g y) =
            ENNReal.ofReal
              (bourgainScaledParabolaBilinearFundamentalMoment H c₁ c₂) by
        exact setLIntegral_bourgainParabolaFundamentalCell_eq
          H hH c₁ c₂]

/-- Unconditional sharp-cell bilinear estimate after both exact
Jacobians.  Its physical-cell factor is `H⁶`, not `H⁸`. -/
theorem setLIntegral_bourgainOsculatingFundamentalCell_subpower
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (H : ℕ), 0 < H →
      ∀ {scale a b : ℝ}, scale ≠ 0 → 0 < a → a < b →
      ∀ (c₁ c₂ : Fin H → ℂ),
        (∫⁻ x in bourgainOsculatingFundamentalCell H scale a b,
          ENNReal.ofReal
            (bourgainScaledIndependentPlanarBilinearIntegrand H c₁ c₂
              (bourgainScaledOsculatingPhaseCoordinates scale a b x))) ≤
          ENNReal.ofReal
              |(scale ^ (6 : ℕ) *
                (3 * (b - a) ^ (4 : ℕ) /
                  (32 * a ^ (3 : ℕ) * b ^ (3 : ℕ))))⁻¹| *
            ENNReal.ofReal
              (((H : ℝ) ^ (3 : ℕ) *
                (C * (H : ℝ) ^ (ε / 2) *
                  (∑ n : Fin H, ‖c₁ n‖ ^ (2 : ℕ)) ^ (3 : ℕ))) *
              ((H : ℝ) ^ (3 : ℕ) *
                (C * (H : ℝ) ^ (ε / 2) *
                  (∑ n : Fin H, ‖c₂ n‖ ^ (2 : ℕ)) ^ (3 : ℕ)))) := by
  obtain ⟨C, hC, hfund⟩ :=
    bourgainScaledParabolaBilinearFundamentalMoment_subpower hε
  refine ⟨C, hC, ?_⟩
  intro H hH scale a b hscale ha hab c₁ c₂
  rw [setLIntegral_bourgainOsculatingFundamentalCell_eq
    H hH hscale ha hab c₁ c₂]
  exact mul_le_mul_right
    (ENNReal.ofReal_le_ofReal (hfund H hH c₁ c₂)) _

/-- Exact sharp-cell identity for the literal quadratic osculating sums. -/
theorem setLIntegral_bourgainSquareRootQuadraticLocalSum_fundamentalCell_eq
    (H : ℕ) (hH : 0 < H) {D a b : ℝ}
    (hD : D ≠ 0) (ha : 0 < a) (hab : a < b)
    (c₁ c₂ : Fin H → ℂ) :
    (∫⁻ x in bourgainOsculatingFundamentalCell
        H ((H : ℝ) / D) a b,
      ENNReal.ofReal
        (‖bourgainSquareRootQuadraticLocalSum H D a c₁ x‖ ^
              (6 : ℕ) *
          ‖bourgainSquareRootQuadraticLocalSum H D b c₂ x‖ ^
              (6 : ℕ))) =
      ENNReal.ofReal
          |((((H : ℝ) / D) ^ (6 : ℕ)) *
            (3 * (b - a) ^ (4 : ℕ) /
              (32 * a ^ (3 : ℕ) * b ^ (3 : ℕ))))⁻¹| *
        ENNReal.ofReal
          (bourgainScaledParabolaBilinearFundamentalMoment H c₁ c₂) := by
  have hscale : (H : ℝ) / D ≠ 0 :=
    div_ne_zero (Nat.cast_ne_zero.mpr hH.ne') hD
  have hbase :=
    setLIntegral_bourgainOsculatingFundamentalCell_eq
      H hH hscale ha hab c₁ c₂
  have hcellMeas :
      MeasurableSet
        (bourgainOsculatingFundamentalCell H ((H : ℝ) / D) a b) := by
    unfold bourgainOsculatingFundamentalCell
    apply
      (measurableSet_bourgainParabolaFundamentalCell H).preimage
    unfold bourgainScaledOsculatingPhaseCoordinates
      bourgainParabolaPhaseScale
      bourgainSquareRootPhaseCoordinates
      bourgainSquareRootPhaseCoordinateMatrix
    fun_prop
  calc
    (∫⁻ x in bourgainOsculatingFundamentalCell
        H ((H : ℝ) / D) a b,
      ENNReal.ofReal
        (‖bourgainSquareRootQuadraticLocalSum H D a c₁ x‖ ^
              (6 : ℕ) *
          ‖bourgainSquareRootQuadraticLocalSum H D b c₂ x‖ ^
              (6 : ℕ))) =
        ∫⁻ x in bourgainOsculatingFundamentalCell
            H ((H : ℝ) / D) a b,
          ENNReal.ofReal
            (bourgainScaledIndependentPlanarBilinearIntegrand H c₁ c₂
              (bourgainScaledOsculatingPhaseCoordinates
                ((H : ℝ) / D) a b x)) := by
      apply setLIntegral_congr_fun hcellMeas
      intro x hx
      change
        ENNReal.ofReal
            (‖bourgainSquareRootQuadraticLocalSum H D a c₁ x‖ ^
                (6 : ℕ) *
              ‖bourgainSquareRootQuadraticLocalSum H D b c₂ x‖ ^
                (6 : ℕ)) =
          ENNReal.ofReal
            (bourgainScaledIndependentPlanarBilinearIntegrand H c₁ c₂
              (bourgainScaledOsculatingPhaseCoordinates
                ((H : ℝ) / D) a b x))
      rw [quadraticLocalSum_bilinearIntegrand_eq H hH hD]
      rfl
    _ = _ := hbase

/-- Unconditional sharp anisotropic-cell estimate for the quadratic local
square-root model. -/
theorem setLIntegral_bourgainSquareRootQuadraticLocalSum_fundamentalCell_subpower
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (H : ℕ), 0 < H →
      ∀ {D a b : ℝ}, D ≠ 0 → 0 < a → a < b →
      ∀ (c₁ c₂ : Fin H → ℂ),
        (∫⁻ x in bourgainOsculatingFundamentalCell
            H ((H : ℝ) / D) a b,
          ENNReal.ofReal
            (‖bourgainSquareRootQuadraticLocalSum H D a c₁ x‖ ^
                  (6 : ℕ) *
              ‖bourgainSquareRootQuadraticLocalSum H D b c₂ x‖ ^
                  (6 : ℕ))) ≤
          ENNReal.ofReal
              |((((H : ℝ) / D) ^ (6 : ℕ)) *
                (3 * (b - a) ^ (4 : ℕ) /
                  (32 * a ^ (3 : ℕ) * b ^ (3 : ℕ))))⁻¹| *
            ENNReal.ofReal
              (((H : ℝ) ^ (3 : ℕ) *
                (C * (H : ℝ) ^ (ε / 2) *
                  (∑ n : Fin H, ‖c₁ n‖ ^ (2 : ℕ)) ^ (3 : ℕ))) *
              ((H : ℝ) ^ (3 : ℕ) *
                (C * (H : ℝ) ^ (ε / 2) *
                  (∑ n : Fin H, ‖c₂ n‖ ^ (2 : ℕ)) ^ (3 : ℕ)))) := by
  obtain ⟨C, hC, hbound⟩ :=
    setLIntegral_bourgainOsculatingFundamentalCell_subpower hε
  refine ⟨C, hC, ?_⟩
  intro H hH D a b hD ha hab c₁ c₂
  rw [setLIntegral_bourgainSquareRootQuadraticLocalSum_fundamentalCell_eq
    H hH hD ha hab c₁ c₂]
  have hb := hbound H hH
    (div_ne_zero (Nat.cast_ne_zero.mpr hH.ne') hD)
    ha hab c₁ c₂
  rw [setLIntegral_bourgainOsculatingFundamentalCell_eq
    H hH
      (div_ne_zero (Nat.cast_ne_zero.mpr hH.ne') hD)
      ha hab c₁ c₂] at hb
  exact hb

end

end RHTower
