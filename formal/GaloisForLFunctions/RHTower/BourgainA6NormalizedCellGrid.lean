/-
# Explicit grid for sharp affine A6 cells

The two exact coordinate maps compose to a continuous linear equivalence
from literal affine `A₆` phase space to the independent-parabola phase
space.  Pulling back the existing anisotropic product grid gives a finite
cover by translated sharp cells with the same exact cardinality.
-/
import GaloisForLFunctions.RHTower.BourgainA6NormalizedCellTranslation
import GaloisForLFunctions.RHTower.BourgainAnisotropicCellGrid

open MeasureTheory

namespace RHTower

noncomputable section

/-- The transpose affine Taylor matrix as a continuous linear equivalence. -/
noncomputable def bourgainA6NormalizedTaylorContinuousLinearEquiv
    {G N₀ M : ℝ} (hG : 0 < G) (hN₀ : 0 < N₀) (hM : 0 < M) :
    BourgainPhaseSpace ≃L[ℝ] BourgainPhaseSpace :=
  let A := (bourgainA6NormalizedTaylorCoordinateMatrix G N₀ M).transpose
  let hA : IsUnit A := by
    dsimp [A]
    exact
      (Matrix.isUnit_transpose
        (bourgainA6NormalizedTaylorCoordinateMatrix G N₀ M)).mpr
          (isUnit_bourgainA6NormalizedTaylorCoordinateMatrix hG hN₀ hM)
  (LinearEquiv.ofBijective A.mulVecLin
    ⟨Matrix.mulVec_injective_iff_isUnit.mpr hA,
      Matrix.mulVec_surjective_iff_isUnit.mpr hA⟩).toContinuousLinearEquiv

@[simp] theorem bourgainA6NormalizedTaylorContinuousLinearEquiv_apply
    {G N₀ M : ℝ} (hG : 0 < G) (hN₀ : 0 < N₀) (hM : 0 < M)
    (x : BourgainPhaseSpace) :
    bourgainA6NormalizedTaylorContinuousLinearEquiv hG hN₀ hM x =
      (bourgainA6NormalizedTaylorCoordinateMatrix
        G N₀ M).transpose.mulVec x := by
  rfl

/-- Full coordinate map from literal affine `A₆` phase space to the
independent-parabola phase space. -/
def bourgainA6AffinePhysicalCellCoordinates
    (G N₀ M : ℝ) (φ₃ φ₄ : ℝ → ℝ)
    (scale a b : ℝ) (x : BourgainPhaseSpace) :
    BourgainPhaseSpace :=
  bourgainGenericScaledPhaseCoordinates φ₃ φ₄ scale a b
    (Matrix.toLin'
      (bourgainA6NormalizedTaylorCoordinateMatrix
        G N₀ M).transpose x)

/-- Continuous linear equivalence represented by the full two-stage
coordinate map. -/
noncomputable def
    bourgainA6AffinePhysicalCellContinuousLinearEquiv
    {G N₀ M scale a b : ℝ} (φ₃ φ₄ : ℝ → ℝ)
    (hG : 0 < G) (hN₀ : 0 < N₀) (hM : 0 < M)
    (hscale : scale ≠ 0)
    (hunit : IsUnit
      (bourgainGenericPhaseCoordinateMatrix φ₃ φ₄ a b)) :
    BourgainPhaseSpace ≃L[ℝ] BourgainPhaseSpace :=
  (bourgainA6NormalizedTaylorContinuousLinearEquiv
      hG hN₀ hM).trans
    (bourgainGenericScaledPhaseContinuousLinearEquiv
      φ₃ φ₄ hscale hunit)

@[simp] theorem
    bourgainA6AffinePhysicalCellContinuousLinearEquiv_apply
    {G N₀ M scale a b : ℝ} (φ₃ φ₄ : ℝ → ℝ)
    (hG : 0 < G) (hN₀ : 0 < N₀) (hM : 0 < M)
    (hscale : scale ≠ 0)
    (hunit : IsUnit
      (bourgainGenericPhaseCoordinateMatrix φ₃ φ₄ a b))
    (x : BourgainPhaseSpace) :
    bourgainA6AffinePhysicalCellContinuousLinearEquiv
        φ₃ φ₄ hG hN₀ hM hscale hunit x =
      bourgainA6AffinePhysicalCellCoordinates
        G N₀ M φ₃ φ₄ scale a b x := by
  rw [bourgainA6AffinePhysicalCellContinuousLinearEquiv,
    ContinuousLinearEquiv.trans_apply,
    bourgainA6NormalizedTaylorContinuousLinearEquiv_apply,
    bourgainGenericScaledPhaseContinuousLinearEquiv_apply]
  unfold bourgainA6AffinePhysicalCellCoordinates
  rw [Matrix.toLin'_apply]

/-- The affine physical cell is exactly the preimage of the standard
independent-parabola fundamental cell under the full coordinate map. -/
theorem bourgainA6AffinePhysicalFundamentalCell_eq_preimage
    (H : ℕ) (G N₀ M D a b : ℝ) :
    bourgainA6AffinePhysicalFundamentalCell H G N₀ M D a b =
      bourgainA6AffinePhysicalCellCoordinates G N₀ M
        (bourgainNormalizedCubicRemainder (M / N₀))
        (bourgainNormalizedQuarticRemainder (M / N₀))
        ((H : ℝ) / D) a b ⁻¹'
          bourgainParabolaFundamentalCell H := by
  rfl

/-- Pullback of an anisotropic phase-grid center through both exact
coordinate maps. -/
def bourgainA6AffinePhysicalGridCenter
    {G N₀ M scale a b : ℝ} (φ₃ φ₄ : ℝ → ℝ)
    (hG : 0 < G) (hN₀ : 0 < N₀) (hM : 0 < M)
    (hscale : scale ≠ 0)
    (hunit : IsUnit
      (bourgainGenericPhaseCoordinateMatrix φ₃ φ₄ a b))
    (H : ℕ) (m : Fin 4 → ℕ)
    (k : BourgainAnisotropicGridIndex m) : BourgainPhaseSpace :=
  (bourgainA6AffinePhysicalCellContinuousLinearEquiv
    φ₃ φ₄ hG hN₀ hM hscale hunit).symm
      (bourgainAnisotropicPhaseGridCenter H m k)

/-- Pulling back the explicit anisotropic grid gives a translated affine
physical-cell cover with unchanged cardinality. -/
theorem
    preimage_bourgainAnisotropicBox_subset_bourgainA6AffinePhysicalGridCover
    (H : ℕ) (m : Fin 4 → ℕ)
    {G N₀ M D a b : ℝ}
    (hG : 0 < G) (hN₀ : 0 < N₀) (hM : 0 < M)
    (hD : 0 < D) (hH : 0 < H)
    (hunit : IsUnit
      (bourgainGenericPhaseCoordinateMatrix
        (bourgainNormalizedCubicRemainder (M / N₀))
        (bourgainNormalizedQuarticRemainder (M / N₀)) a b)) :
    bourgainA6AffinePhysicalCellCoordinates G N₀ M
        (bourgainNormalizedCubicRemainder (M / N₀))
        (bourgainNormalizedQuarticRemainder (M / N₀))
        ((H : ℝ) / D) a b ⁻¹'
          bourgainAnisotropicBox
            (bourgainAnisotropicGridRadius H m) ⊆
      ⋃ k : BourgainAnisotropicGridIndex m,
        bourgainA6TranslatedAffinePhysicalFundamentalCell
          H G N₀ M D a b
          (bourgainA6AffinePhysicalGridCenter
            (bourgainNormalizedCubicRemainder (M / N₀))
            (bourgainNormalizedQuarticRemainder (M / N₀))
            hG hN₀ hM
            (div_ne_zero (Nat.cast_ne_zero.mpr hH.ne') hD.ne')
            hunit H m k) := by
  let φ₃ := bourgainNormalizedCubicRemainder (M / N₀)
  let φ₄ := bourgainNormalizedQuarticRemainder (M / N₀)
  let scale := (H : ℝ) / D
  let hscale : scale ≠ 0 :=
    div_ne_zero (Nat.cast_ne_zero.mpr hH.ne') hD.ne'
  let e :=
    bourgainA6AffinePhysicalCellContinuousLinearEquiv
      φ₃ φ₄ hG hN₀ hM hscale hunit
  intro x hx
  have hphase :=
    bourgainAnisotropicBox_subset_phaseGridCover H m hx
  obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hphase
  apply Set.mem_iUnion.2
  refine ⟨k, ?_⟩
  obtain ⟨w, hw, hwy⟩ := hk
  let c := bourgainAnisotropicPhaseGridCenter H m k
  let y :=
    bourgainA6AffinePhysicalGridCenter φ₃ φ₄
      hG hN₀ hM hscale hunit H m k
  refine ⟨x - y, ?_, sub_add_cancel x y⟩
  · rw [bourgainA6AffinePhysicalFundamentalCell_eq_preimage]
    change
      bourgainA6AffinePhysicalCellCoordinates
        G N₀ M φ₃ φ₄ scale a b (x - y) ∈
          bourgainParabolaFundamentalCell H
    have hey : e y = c := by
      dsimp [e, y, c, bourgainA6AffinePhysicalGridCenter]
      rw [ContinuousLinearEquiv.apply_symm_apply]
    have hex :
        e x =
          bourgainA6AffinePhysicalCellCoordinates
            G N₀ M φ₃ φ₄ scale a b x :=
      bourgainA6AffinePhysicalCellContinuousLinearEquiv_apply
        φ₃ φ₄ hG hN₀ hM hscale hunit x
    have hwy' : w + c = e x := by
      simpa [c, hex] using hwy
    have hdiff : e (x - y) = w := by
      rw [map_sub, hey]
      exact sub_eq_of_eq_add hwy'.symm
    rw [← bourgainA6AffinePhysicalCellContinuousLinearEquiv_apply
      φ₃ φ₄ hG hN₀ hM hscale hunit]
    rw [hdiff]
    exact hw

/-- Integrating over the pullback of an anisotropic target box costs
exactly the product-grid cardinality once every translated affine physical
cell obeys the same local bound. -/
theorem
    setLIntegral_bourgainA6AffinePhysicalBox_le_gridCard_mul
    (H : ℕ) (m : Fin 4 → ℕ)
    {G N₀ M D a b : ℝ}
    (hG : 0 < G) (hN₀ : 0 < N₀) (hM : 0 < M)
    (hD : 0 < D) (hH : 0 < H)
    (hunit : IsUnit
      (bourgainGenericPhaseCoordinateMatrix
        (bourgainNormalizedCubicRemainder (M / N₀))
        (bourgainNormalizedQuarticRemainder (M / N₀)) a b))
    (f : BourgainPhaseSpace → ENNReal) {B : ENNReal}
    (hlocal :
      ∀ k : BourgainAnisotropicGridIndex m,
        (∫⁻ x in bourgainA6TranslatedAffinePhysicalFundamentalCell
            H G N₀ M D a b
            (bourgainA6AffinePhysicalGridCenter
              (bourgainNormalizedCubicRemainder (M / N₀))
              (bourgainNormalizedQuarticRemainder (M / N₀))
              hG hN₀ hM
              (div_ne_zero
                (Nat.cast_ne_zero.mpr hH.ne') hD.ne')
              hunit H m k),
          f x) ≤ B) :
    (∫⁻ x in
      bourgainA6AffinePhysicalCellCoordinates G N₀ M
          (bourgainNormalizedCubicRemainder (M / N₀))
          (bourgainNormalizedQuarticRemainder (M / N₀))
          ((H : ℝ) / D) a b ⁻¹'
        bourgainAnisotropicBox
          (bourgainAnisotropicGridRadius H m),
      f x) ≤
        ((∏ j : Fin 4, (m j + 1) : ℕ) : ENNReal) * B := by
  have hbound :=
    setLIntegral_le_card_mul_of_bourgainA6AffinePhysicalFundamentalCell_cover
      (bourgainA6AffinePhysicalCellCoordinates G N₀ M
          (bourgainNormalizedCubicRemainder (M / N₀))
          (bourgainNormalizedQuarticRemainder (M / N₀))
          ((H : ℝ) / D) a b ⁻¹'
        bourgainAnisotropicBox
          (bourgainAnisotropicGridRadius H m))
      H G N₀ M D a b
      (bourgainA6AffinePhysicalGridCenter
        (bourgainNormalizedCubicRemainder (M / N₀))
        (bourgainNormalizedQuarticRemainder (M / N₀))
        hG hN₀ hM
        (div_ne_zero (Nat.cast_ne_zero.mpr hH.ne') hD.ne')
        hunit H m)
      f
      (preimage_bourgainAnisotropicBox_subset_bourgainA6AffinePhysicalGridCover
        H m hG hN₀ hM hD hH hunit)
      hlocal
  simpa [card_bourgainAnisotropicGridIndex] using hbound

end

end RHTower
