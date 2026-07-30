import GaloisForLFunctions.HTGeometry.ContinuousEquivariantGramRigidity
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Topology.ContinuousMap.Basic

open Matrix
open scoped ComplexOrder Matrix Matrix.Norms.L2Operator MatrixOrder

noncomputable section

namespace GaloisForLFunctions.HTGeometry

noncomputable local instance matrixTwoCStarAlgebra :
    CStarAlgebra (Matrix (Fin 2) (Fin 2) ℂ) where

/-- The inner product after applying an event matrix is computed by its Gram matrix. -/
theorem inner_color_mulVec_eq_gram
    (X : ColorEventMatrix) (v w : Fin 2 → ℂ) :
    inner ℂ (WithLp.toLp 2 (X *ᵥ v)) (WithLp.toLp 2 (X *ᵥ w)) =
      inner ℂ (WithLp.toLp 2 v) (WithLp.toLp 2 ((Xᴴ * X) *ᵥ w)) := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Matrix.mulVec, Matrix.mul_apply, Fin.sum_univ_succ]
  ring

/-- Equal kernels identify the ranges of two event matrices through their common quotient. -/
def colorRangeEquiv
    (X Y : ColorEventMatrix)
    (hker : LinearMap.ker X.toEuclideanLin = LinearMap.ker Y.toEuclideanLin) :
    LinearMap.range X.toEuclideanLin ≃ₗ[ℂ] LinearMap.range Y.toEuclideanLin :=
  X.toEuclideanLin.quotKerEquivRange.symm.trans <|
    (Submodule.quotEquivOfEq _ _ hker).trans Y.toEuclideanLin.quotKerEquivRange

/-- Equal Gram matrices force equal kernels. -/
theorem color_toEuclideanLin_ker_eq_of_gram_eq
    (X Y : ColorEventMatrix) (hGram : Xᴴ * X = Yᴴ * Y) :
    LinearMap.ker X.toEuclideanLin = LinearMap.ker Y.toEuclideanLin := by
  ext v
  simp only [LinearMap.mem_ker, Matrix.toLpLin_apply, WithLp.toLp_eq_zero]
  rw [← Matrix.conjTranspose_mul_self_mulVec_eq_zero,
    hGram, Matrix.conjTranspose_mul_self_mulVec_eq_zero]

/-- The range equivalence sends the image of `v` under `X` to its image under `Y`. -/
theorem colorRangeEquiv_apply
    (X Y : ColorEventMatrix)
    (hker : LinearMap.ker X.toEuclideanLin = LinearMap.ker Y.toEuclideanLin)
    (v : EuclideanSpace ℂ (Fin 2)) :
    colorRangeEquiv X Y hker
        ⟨X.toEuclideanLin v, LinearMap.mem_range_self X.toEuclideanLin v⟩ =
      ⟨Y.toEuclideanLin v, LinearMap.mem_range_self Y.toEuclideanLin v⟩ := by
  apply Subtype.ext
  simp [colorRangeEquiv]

/-- Equal Gram matrices give equal inner products on the images of all vectors. -/
theorem inner_color_toEuclideanLin_eq_of_gram_eq
    (X Y : ColorEventMatrix) (hGram : Xᴴ * X = Yᴴ * Y)
    (v w : EuclideanSpace ℂ (Fin 2)) :
    inner ℂ (X.toEuclideanLin v) (X.toEuclideanLin w) =
      inner ℂ (Y.toEuclideanLin v) (Y.toEuclideanLin w) := by
  rw [Matrix.toLpLin_apply, Matrix.toLpLin_apply,
    inner_color_mulVec_eq_gram, hGram,
    ← inner_color_mulVec_eq_gram,
    ← Matrix.toLpLin_apply, ← Matrix.toLpLin_apply]

/-- The isometry from the range of `X` to the ambient color space carrying `X` to `Y`. -/
noncomputable def colorRangeIsometry
    (X Y : ColorEventMatrix) (hGram : Xᴴ * X = Yᴴ * Y) :
    LinearMap.range X.toEuclideanLin →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 3) := by
  let hker := color_toEuclideanLin_ker_eq_of_gram_eq X Y hGram
  let e := colorRangeEquiv X Y hker
  let f : LinearMap.range X.toEuclideanLin →ₗ[ℂ] EuclideanSpace ℂ (Fin 3) :=
    (LinearMap.range Y.toEuclideanLin).subtype.comp e.toLinearMap
  refine LinearMap.isometryOfInner (𝕜 := ℂ)
    (E := LinearMap.range X.toEuclideanLin)
    (E' := EuclideanSpace ℂ (Fin 3)) f ?_
  intro u v
  obtain ⟨u₀, hu₀⟩ := u.property
  obtain ⟨v₀, hv₀⟩ := v.property
  have hu : u =
      ⟨X.toEuclideanLin u₀, LinearMap.mem_range_self X.toEuclideanLin u₀⟩ :=
    Subtype.ext hu₀.symm
  have hv : v =
      ⟨X.toEuclideanLin v₀, LinearMap.mem_range_self X.toEuclideanLin v₀⟩ :=
    Subtype.ext hv₀.symm
  rw [hu, hv]
  change inner ℂ
      ((e ⟨X.toEuclideanLin u₀, LinearMap.mem_range_self X.toEuclideanLin u₀⟩ :
        LinearMap.range Y.toEuclideanLin) :
        EuclideanSpace ℂ (Fin 3))
      ((e ⟨X.toEuclideanLin v₀, LinearMap.mem_range_self X.toEuclideanLin v₀⟩ :
        LinearMap.range Y.toEuclideanLin) :
        EuclideanSpace ℂ (Fin 3)) =
    inner ℂ (X.toEuclideanLin u₀) (X.toEuclideanLin v₀)
  rw [colorRangeEquiv_apply X Y hker, colorRangeEquiv_apply X Y hker]
  exact (inner_color_toEuclideanLin_eq_of_gram_eq X Y hGram u₀ v₀).symm

/-- The range isometry agrees with `Y` on every vector represented by `X`. -/
theorem colorRangeIsometry_apply
    (X Y : ColorEventMatrix) (hGram : Xᴴ * X = Yᴴ * Y)
    (v : EuclideanSpace ℂ (Fin 2)) :
    colorRangeIsometry X Y hGram
        ⟨X.toEuclideanLin v, LinearMap.mem_range_self X.toEuclideanLin v⟩ =
      Y.toEuclideanLin v := by
  let hker := color_toEuclideanLin_ker_eq_of_gram_eq X Y hGram
  change ((LinearMap.range Y.toEuclideanLin).subtype.comp
      (colorRangeEquiv X Y hker).toLinearMap)
      ⟨X.toEuclideanLin v, LinearMap.mem_range_self X.toEuclideanLin v⟩ =
    Y.toEuclideanLin v
  rw [LinearMap.comp_apply]
  exact congrArg Subtype.val (colorRangeEquiv_apply X Y hker v)

/-- The range isometry extended to the full three-dimensional color carrier. -/
noncomputable def colorAmbientIsometry
    (X Y : ColorEventMatrix) (hGram : Xᴴ * X = Yᴴ * Y) :
    EuclideanSpace ℂ (Fin 3) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 3) :=
  (colorRangeIsometry X Y hGram).extend

/-- The ambient isometry transforms the linear map represented by `X` into that of `Y`. -/
theorem colorAmbientIsometry_comp
    (X Y : ColorEventMatrix) (hGram : Xᴴ * X = Yᴴ * Y) :
    (colorAmbientIsometry X Y hGram).toLinearMap.comp X.toEuclideanLin =
      Y.toEuclideanLin := by
  apply LinearMap.ext
  intro v
  change colorAmbientIsometry X Y hGram (X.toEuclideanLin v) =
    Y.toEuclideanLin v
  rw [show X.toEuclideanLin v =
      (⟨X.toEuclideanLin v, LinearMap.mem_range_self X.toEuclideanLin v⟩ :
        LinearMap.range X.toEuclideanLin) by rfl,
    colorAmbientIsometry, LinearIsometry.extend_apply,
    colorRangeIsometry_apply]

/-- A square unitary matrix extending the range isometry associated to equal Gram records. -/
noncomputable def colorOrbitUnitary
    (X Y : ColorEventMatrix) (hGram : Xᴴ * X = Yᴴ * Y) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.toEuclideanLin.symm (colorAmbientIsometry X Y hGram).toLinearMap

/-- The linear map represented by `colorOrbitUnitary` is the ambient isometry. -/
theorem colorOrbitUnitary_toEuclideanLin
    (X Y : ColorEventMatrix) (hGram : Xᴴ * X = Yᴴ * Y) :
    (colorOrbitUnitary X Y hGram).toEuclideanLin =
      (colorAmbientIsometry X Y hGram).toLinearMap := by
  simp [colorOrbitUnitary]

/-- The orbit unitary sends `X` exactly to `Y`. -/
theorem colorOrbitUnitary_mul
    (X Y : ColorEventMatrix) (hGram : Xᴴ * X = Yᴴ * Y) :
    colorOrbitUnitary X Y hGram * X = Y := by
  apply Matrix.toEuclideanLin.injective
  rw [Matrix.toLpLin_mul_same]
  rw [colorOrbitUnitary_toEuclideanLin]
  exact colorAmbientIsometry_comp X Y hGram

/-- The orbit transporter has orthonormal columns. -/
theorem colorOrbitUnitary_conjTranspose_mul_self
    (X Y : ColorEventMatrix) (hGram : Xᴴ * X = Yᴴ * Y) :
    (colorOrbitUnitary X Y hGram)ᴴ * colorOrbitUnitary X Y hGram = 1 := by
  apply Matrix.toEuclideanLin.injective
  rw [Matrix.toLpLin_mul_same, Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  rw [colorOrbitUnitary_toEuclideanLin]
  simpa only [Matrix.toLpLin_one] using
    (colorAmbientIsometry X Y hGram).adjoint_comp_self'

/-- Two color events have the same Gram record exactly when they differ by a left unitary. -/
theorem colorGramMatrix_eq_iff_exists_left_unitary
    (X Y : ColorEventMatrix) :
    Xᴴ * X = Yᴴ * Y ↔
      ∃ U : Matrix (Fin 3) (Fin 3) ℂ, Uᴴ * U = 1 ∧ U * X = Y := by
  constructor
  · intro hGram
    exact ⟨colorOrbitUnitary X Y hGram,
      colorOrbitUnitary_conjTranspose_mul_self X Y hGram,
      colorOrbitUnitary_mul X Y hGram⟩
  · rintro ⟨U, hU, rfl⟩
    simpa [colorGramMatrix] using (colorGramMatrix_left_invariant U X hU).symm

/-- Embed a two-by-two matrix into the first two rows of a color event matrix. -/
def colorEmbedSquare
    (B : Matrix (Fin 2) (Fin 2) ℂ) : ColorEventMatrix :=
  fun i j =>
    Fin.cases (B 0 j)
      (fun i' => Fin.cases (B 1 j) (fun _ => 0) i') i

/-- Embedding a square factor into the color event carrier preserves its Gram matrix. -/
theorem colorEmbedSquare_gram
    (B : Matrix (Fin 2) (Fin 2) ℂ) :
    (colorEmbedSquare B)ᴴ * colorEmbedSquare B = Bᴴ * B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [colorEmbedSquare, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Every positive-semidefinite two-by-two Hermitian matrix is a color-event Gram record. -/
theorem exists_colorEventMatrix_gram_eq
    (H : Matrix (Fin 2) (Fin 2) ℂ) (hH : H.PosSemidef) :
    ∃ X : ColorEventMatrix, Xᴴ * X = H := by
  obtain ⟨B, hB⟩ :=
    CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hH.nonneg
  refine ⟨colorEmbedSquare B, ?_⟩
  rw [colorEmbedSquare_gram]
  simpa using! hB.symm

/-- The cone of nonnegative two-by-two complex matrices. -/
abbrev PositiveTwoCone :=
  {H : Matrix (Fin 2) (Fin 2) ℂ // 0 ≤ H}

/-- The color Gram record depends continuously on its event matrix. -/
theorem continuous_colorGramMatrix : Continuous colorGramMatrix := by
  unfold colorGramMatrix
  fun_prop

/-- The continuous map from color events to their positive public Gram records. -/
def colorGramRecordMap : C(ColorEventMatrix, PositiveTwoCone) where
  toFun X := ⟨colorGramMatrix X, (colorGramMatrix_posSemidef X).nonneg⟩
  continuous_toFun := by
    exact Continuous.subtype_mk continuous_colorGramMatrix _

/-- Embedding a square factor as an event is continuous. -/
theorem continuous_colorEmbedSquare : Continuous colorEmbedSquare := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i
  · simpa [colorEmbedSquare] using!
      (show Continuous (fun B : Matrix (Fin 2) (Fin 2) ℂ => B 0 j) by
        fun_prop)
  · simpa [colorEmbedSquare] using!
      (show Continuous (fun B : Matrix (Fin 2) (Fin 2) ℂ => B 1 j) by
        fun_prop)
  · simpa [colorEmbedSquare] using!
      (show Continuous (fun _ : Matrix (Fin 2) (Fin 2) ℂ => (0 : ℂ)) by
        fun_prop)

/-- A continuous square-root section from positive records back to event representatives. -/
noncomputable def colorGramSection : C(PositiveTwoCone, ColorEventMatrix) where
  toFun H := colorEmbedSquare (CFC.sqrt H.1)
  continuous_toFun := by
    have hSqrt : Continuous (fun H : PositiveTwoCone => CFC.sqrt H.1) :=
      by
        exact CFC.continuousOn_sqrt.comp_continuous continuous_subtype_val
          (fun H : PositiveTwoCone => H.2)
    exact continuous_colorEmbedSquare.comp hSqrt

/-- Taking the Gram record after the square-root section recovers the positive record. -/
theorem colorGramSection_rightInverse :
    Function.RightInverse colorGramSection colorGramRecordMap := by
  intro H
  apply Subtype.ext
  dsimp only [colorGramRecordMap, colorGramSection]
  change colorGramMatrix (colorEmbedSquare (CFC.sqrt H.1)) = H.1
  unfold colorGramMatrix
  rw [colorEmbedSquare_gram]
  rw [← Matrix.star_eq_conjTranspose]
  rw [(CFC.sqrt_nonneg H.1).star_eq]
  simpa [pow_two] using CFC.sq_sqrt H.1 H.2

/-- The event space modulo equality of public records is homeomorphic to the positive record cone. -/
noncomputable def colorGramQuotientHomeomorph :
    Quotient (Setoid.ker colorGramRecordMap) ≃ₜ PositiveTwoCone :=
  Function.RightInverse.homeomorph
    (f := colorGramRecordMap) (f' := colorGramSection)
    colorGramSection_rightInverse

/-- The kernel classes of the public record map are exactly the left-unitary event orbits. -/
theorem colorGramRecordMap_ker_iff_exists_left_unitary
    (X Y : ColorEventMatrix) :
    Setoid.ker colorGramRecordMap X Y ↔
      ∃ U : Matrix (Fin 3) (Fin 3) ℂ, Uᴴ * U = 1 ∧ U * X = Y := by
  change colorGramRecordMap X = colorGramRecordMap Y ↔ _
  constructor
  · intro h
    exact (colorGramMatrix_eq_iff_exists_left_unitary X Y).mp
      (congrArg Subtype.val h)
  · intro h
    apply Subtype.ext
    exact (colorGramMatrix_eq_iff_exists_left_unitary X Y).mpr h

end GaloisForLFunctions.HTGeometry
