import GaloisForLFunctions.HTGeometry.PaperSL2PolynomialFrame
import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.QuadricFactorization
import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.FrameNormalization

/-!+# Exact reconstruction of polynomial SL₂ families

The source's gcd factorization provides a frame over every polynomial quadric
point. Constant-unit normalization gives any compatible initial matrix, and
reduced-ring uniqueness makes this construction inverse to taking observables.
-/

namespace GaloisForLFunctions.HTGeometry

open StableCoordinate FrameLift MvPolynomial

noncomputable section

/-- The determinant frame is exactly a native special-linear matrix. -/
def paperFrameSL2 {R : Type*} [CommRing R] (F : Frame R) :
    Matrix.SpecialLinearGroup (Fin 2) R :=
  ⟨!![F.a, F.b; F.d, F.c], by simpa [Matrix.det_fin_two] using F.determinant⟩

@[simp] theorem paperSL2Frame_frameSL2 {R : Type*} [CommRing R] (F : Frame R) :
    paperSL2Frame (paperFrameSL2 F) = F := by
  apply Frame.ext <;> rfl

/-- Precisely the admissible quadratic observations and initial matrix. -/
structure PaperSL2PolynomialData (σ : Type*) where
  quadric : Fin 3 → MvPolynomial σ ℂ
  relation : quadric 0 * quadric 1 = quadric 2 * (quadric 2 + 1)
  origin : Matrix.SpecialLinearGroup (Fin 2) ℂ
  compatible : ∀ i, constantCoeff (quadric i) = paperSL2QuadricPoint origin i

@[ext] theorem PaperSL2PolynomialData.ext {σ : Type*}
    {d e : PaperSL2PolynomialData σ} (hq : d.quadric = e.quadric)
    (ho : d.origin = e.origin) : d = e := by
  cases d
  cases e
  cases hq
  cases ho
  rfl

/-- A polynomial matrix determines admissible reconstruction data. -/
def paperSL2PolynomialData {σ : Type*}
    (g : Matrix.SpecialLinearGroup (Fin 2) (MvPolynomial σ ℂ)) :
    PaperSL2PolynomialData σ where
  quadric := paperSL2QuadricPoint g
  relation := paperSL2QuadricPoint_relation g
  origin := Matrix.SpecialLinearGroup.map constantCoeff g
  compatible i := by
    fin_cases i <;> simp [paperSL2QuadricPoint, Matrix.SpecialLinearGroup.map]

private def rawFrame {σ : Type*} (d : PaperSL2PolynomialData σ) :
    Frame (MvPolynomial σ ℂ) :=
  QuadricFactorization.frameAbove (d.quadric 0) (d.quadric 1) (d.quadric 2) d.relation

private theorem rawFrame_ab {σ : Type*} (d : PaperSL2PolynomialData σ) :
    (rawFrame d).a * (rawFrame d).b = d.quadric 0 :=
  QuadricFactorization.frameAbove_ab _ _ _ _

private theorem rawFrame_dc {σ : Type*} (d : PaperSL2PolynomialData σ) :
    (rawFrame d).d * (rawFrame d).c = d.quadric 1 :=
  QuadricFactorization.frameAbove_dc _ _ _ _

private theorem rawFrame_db {σ : Type*} (d : PaperSL2PolynomialData σ) :
    (rawFrame d).d * (rawFrame d).b = d.quadric 2 :=
  QuadricFactorization.frameAbove_db _ _ _ _

private theorem rawFrame_compatible {σ : Type*} (d : PaperSL2PolynomialData σ) :
    SameBase ((rawFrame d).map constantCoeff) (paperSL2Frame d.origin) := by
  refine ⟨?_, ?_, ?_⟩
  · change constantCoeff (rawFrame d).a * constantCoeff (rawFrame d).b = _
    rw [← map_mul, rawFrame_ab]
    exact d.compatible 0
  · change constantCoeff (rawFrame d).d * constantCoeff (rawFrame d).c = _
    rw [← map_mul, rawFrame_dc]
    exact d.compatible 1
  · change constantCoeff (rawFrame d).d * constantCoeff (rawFrame d).b = _
    rw [← map_mul, rawFrame_db]
    exact d.compatible 2

/-- Reconstruct the polynomial matrix from every admissible data set. -/
def paperSL2PolynomialLift {σ : Type*} (d : PaperSL2PolynomialData σ) :
    Matrix.SpecialLinearGroup (Fin 2) (MvPolynomial σ ℂ) :=
  paperFrameSL2 (normalizeFrame (rawFrame d) (paperSL2Frame d.origin) (rawFrame_compatible d))

/-- Reconstruction returns exactly the prescribed observables and initial matrix. -/
@[simp] theorem paperSL2PolynomialData_lift {σ : Type*} (d : PaperSL2PolynomialData σ) :
    paperSL2PolynomialData (paperSL2PolynomialLift d) = d := by
  apply PaperSL2PolynomialData.ext
  · have h := normalizeFrame_sameBase (rawFrame d) (paperSL2Frame d.origin)
      (rawFrame_compatible d)
    funext i
    fin_cases i
    · exact h.1.trans (rawFrame_ab d)
    · exact h.2.1.trans (rawFrame_dc d)
    · exact h.2.2.trans (rawFrame_db d)
  · apply paperSL2Frame_injective
    change paperSL2Frame (Matrix.SpecialLinearGroup.map constantCoeff
      (paperSL2PolynomialLift d)) = paperSL2Frame d.origin
    rw [paperSL2Frame_map, paperSL2PolynomialLift, paperSL2Frame_frameSL2]
    exact normalizeFrame_at_zero _ _ _

/-- Taking data and reconstructing returns the original matrix. -/
@[simp] theorem paperSL2PolynomialLift_data {σ : Type*}
    (g : Matrix.SpecialLinearGroup (Fin 2) (MvPolynomial σ ℂ)) :
    paperSL2PolynomialLift (paperSL2PolynomialData g) = g := by
  apply paperSL2NormalizedData_injective
  have h := paperSL2PolynomialData_lift (paperSL2PolynomialData g)
  exact Prod.ext (congrArg PaperSL2PolynomialData.quadric h)
    (congrArg PaperSL2PolynomialData.origin h)

/-- Complete classification by polynomial quadric data and compatible origin. -/
def paperSL2PolynomialDataEquiv (σ : Type*) :
    Matrix.SpecialLinearGroup (Fin 2) (MvPolynomial σ ℂ) ≃ PaperSL2PolynomialData σ where
  toFun := paperSL2PolynomialData
  invFun := paperSL2PolynomialLift
  left_inv := paperSL2PolynomialLift_data
  right_inv := paperSL2PolynomialData_lift

end

end GaloisForLFunctions.HTGeometry
