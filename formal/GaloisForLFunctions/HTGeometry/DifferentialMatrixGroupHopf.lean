import GaloisForLFunctions.HTGeometry.DifferentialMatrixGroupCoordinateAlgebra
import GaloisForLFunctions.HTGeometry.AdjointStableZariskiClosure

/-!
# Hopf operations on a differential matrix-group coordinate algebra

Multiplication and inversion of a determinant-one matrix group preserve its differential coordinate
algebra.  The unique separated-function tensor representing multiplication therefore defines the
comultiplication, evaluation at the identity defines the counit, and pullback by inversion defines
the antipode.  All three operations commute with the distinguished differential.
-/

open scoped Differential TensorProduct

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open GaloisForLFunctions

universe u

variable {C G : Type u} [Field C] [Differential C] [Group G]

namespace DifferentialMatrixGroupRepresentation

variable (r : DifferentialMatrixGroupRepresentation (C := C) (G := G))

local instance hopfAmbientFunctionDifferential : Differential (G → C) :=
  pointwiseFunctionDifferential G

local instance hopfAmbientFunctionDifferentialAlgebra : DifferentialAlgebra C (G → C) :=
  pointwiseFunctionDifferentialAlgebra G

local instance hopfCoordinateDifferential : Differential r.coordinateAlgebra :=
  r.coordinateAlgebraDifferential

/-- The unique tensor representing multiplication pullback. -/
def coordinateComulValue (f : r.coordinateAlgebra) :
    r.coordinateAlgebra ⊗[C] r.coordinateAlgebra :=
  Classical.choose (r.exists_unique_coordinateTensor_mulPullback f)

theorem coordinateTensorEval_coordinateComulValue (f : r.coordinateAlgebra) :
    r.coordinateTensorEval (r.coordinateComulValue f) =
      r.multiplicationPullback f.1 :=
  (Classical.choose_spec (r.exists_unique_coordinateTensor_mulPullback f)).1

/-- Comultiplication induced by pullback along group multiplication. -/
def coordinateComul :
    r.coordinateAlgebra →ₐ[C] r.coordinateAlgebra ⊗[C] r.coordinateAlgebra where
  toFun := r.coordinateComulValue
  map_one' := by
    apply r.coordinateTensorEval_injective
    rw [r.coordinateTensorEval_coordinateComulValue]
    ext z
    simp [coordinateTensorEval, multiplicationPullback]
  map_mul' f g := by
    apply r.coordinateTensorEval_injective
    rw [map_mul, r.coordinateTensorEval_coordinateComulValue,
      r.coordinateTensorEval_coordinateComulValue,
      r.coordinateTensorEval_coordinateComulValue]
    rfl
  map_zero' := by
    apply r.coordinateTensorEval_injective
    rw [r.coordinateTensorEval_coordinateComulValue, map_zero]
    rfl
  map_add' f g := by
    apply r.coordinateTensorEval_injective
    rw [map_add, r.coordinateTensorEval_coordinateComulValue,
      r.coordinateTensorEval_coordinateComulValue,
      r.coordinateTensorEval_coordinateComulValue]
    rfl
  commutes' c := by
    apply r.coordinateTensorEval_injective
    rw [r.coordinateTensorEval_coordinateComulValue]
    ext z
    simp [coordinateTensorEval, coordinateLeftFunction,
      coordinateRightFunction, multiplicationPullback]

theorem coordinateTensorEval_coordinateComul
    (f : r.coordinateAlgebra) (g h : G) :
    r.coordinateTensorEval (r.coordinateComul f) (g, h) = f.1 (g * h) := by
  change r.coordinateTensorEval (r.coordinateComulValue f) (g, h) = _
  rw [r.coordinateTensorEval_coordinateComulValue]
  rfl

/-- Counit: evaluation at the identity element. -/
def coordinateCounit : r.coordinateAlgebra →ₐ[C] C where
  toFun f := f.1 1
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- A represented inverse is the adjugate because every represented matrix has determinant one. -/
theorem matrix_inv_eq_adjugate (g : G) :
    r.matrix g⁻¹ = Matrix.adjugate (r.matrix g) := by
  have hright : r.matrix g * r.matrix g⁻¹ = 1 := by
    calc
      r.matrix g * r.matrix g⁻¹ = r.matrix (g * g⁻¹) := (r.matrix.map_mul g g⁻¹).symm
      _ = 1 := by simp
  have hleft : Matrix.adjugate (r.matrix g) * r.matrix g = 1 := by
    rw [Matrix.adjugate_mul, r.det_eq_one, one_smul]
  calc
    r.matrix g⁻¹ = 1 * r.matrix g⁻¹ := (one_mul _).symm
    _ = (Matrix.adjugate (r.matrix g) * r.matrix g) * r.matrix g⁻¹ := by rw [hleft]
    _ = Matrix.adjugate (r.matrix g) * (r.matrix g * r.matrix g⁻¹) :=
      Matrix.mul_assoc _ _ _
    _ = Matrix.adjugate (r.matrix g) := by rw [hright, Matrix.mul_one]

/-- Pullback of functions along inversion. -/
def inversionPullback
    (_r : DifferentialMatrixGroupRepresentation (C := C) (G := G)) :
    (G → C) →ₐ[C] (G → C) where
  toFun f g := f g⁻¹
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- Functions whose inversion pullback remains in the coordinate algebra. -/
def inversionRepresentable : Subalgebra C (G → C) :=
  r.coordinateAlgebra.comap r.inversionPullback

theorem inversionPullback_deriv (f : G → C) :
    r.inversionPullback (Differential.deriv f) =
      Differential.deriv (r.inversionPullback f) := by
  funext g
  rfl

theorem deriv_mem_inversionRepresentable
    (f : G → C) (hf : f ∈ r.inversionRepresentable) :
    Differential.deriv f ∈ r.inversionRepresentable := by
  change r.inversionPullback (Differential.deriv f) ∈ r.coordinateAlgebra
  rw [r.inversionPullback_deriv]
  exact r.deriv_mem_coordinateAlgebra _ hf

theorem inversionPullback_coordinate_zero_zero :
    r.inversionPullback (r.coordinate (0, 0)) = r.coordinate (1, 1) := by
  funext g
  change r.matrix g⁻¹ 0 0 = r.matrix g 1 1
  rw [r.matrix_inv_eq_adjugate, adjugate_two]
  simp

theorem inversionPullback_coordinate_zero_one :
    r.inversionPullback (r.coordinate (0, 1)) = -r.coordinate (0, 1) := by
  funext g
  change r.matrix g⁻¹ 0 1 = -r.matrix g 0 1
  rw [r.matrix_inv_eq_adjugate, adjugate_two]
  rfl

theorem inversionPullback_coordinate_one_zero :
    r.inversionPullback (r.coordinate (1, 0)) = -r.coordinate (1, 0) := by
  funext g
  change r.matrix g⁻¹ 1 0 = -r.matrix g 1 0
  rw [r.matrix_inv_eq_adjugate, adjugate_two]
  rfl

theorem inversionPullback_coordinate_one_one :
    r.inversionPullback (r.coordinate (1, 1)) = r.coordinate (0, 0) := by
  funext g
  change r.matrix g⁻¹ 1 1 = r.matrix g 0 0
  rw [r.matrix_inv_eq_adjugate, adjugate_two]
  simp

private theorem finTwo_eq_zero_or_one (i : Fin 2) : i = 0 ∨ i = 1 := by
  omega

theorem coordinate_mem_inversionRepresentable (q : Fin 2 × Fin 2) :
    r.coordinate q ∈ r.inversionRepresentable := by
  rcases q with ⟨i, j⟩
  rcases finTwo_eq_zero_or_one i with rfl | rfl <;>
    rcases finTwo_eq_zero_or_one j with rfl | rfl
  · change r.inversionPullback (r.coordinate (0, 0)) ∈ r.coordinateAlgebra
    rw [r.inversionPullback_coordinate_zero_zero]
    exact Algebra.subset_adjoin ⟨((1, 1), 0), by
      funext g
      exact (differentialJet_zero _).symm⟩
  · change r.inversionPullback (r.coordinate (0, 1)) ∈ r.coordinateAlgebra
    rw [r.inversionPullback_coordinate_zero_one]
    exact (r.coordinateAlgebra).neg_mem
      (Algebra.subset_adjoin ⟨((0, 1), 0), by
        funext g
        exact (differentialJet_zero _).symm⟩)
  · change r.inversionPullback (r.coordinate (1, 0)) ∈ r.coordinateAlgebra
    rw [r.inversionPullback_coordinate_one_zero]
    exact (r.coordinateAlgebra).neg_mem
      (Algebra.subset_adjoin ⟨((1, 0), 0), by
        funext g
        exact (differentialJet_zero _).symm⟩)
  · change r.inversionPullback (r.coordinate (1, 1)) ∈ r.coordinateAlgebra
    rw [r.inversionPullback_coordinate_one_one]
    exact Algebra.subset_adjoin ⟨((0, 0), 0), by
      funext g
      exact (differentialJet_zero _).symm⟩

theorem coordinateJet_mem_inversionRepresentable
    (q : Fin 2 × Fin 2) (n : ℕ) :
    r.coordinateJet q n ∈ r.inversionRepresentable := by
  induction n with
  | zero =>
      have hzero : r.coordinateJet q 0 = r.coordinate q := by
        funext g
        exact differentialJet_zero _
      rw [hzero]
      exact r.coordinate_mem_inversionRepresentable q
  | succ n ih =>
      have h := r.deriv_mem_inversionRepresentable _ ih
      rw [r.deriv_coordinateJet] at h
      simpa only [Nat.add_comm] using h

/-- Inversion preserves every differential coordinate function. -/
theorem inversionPullback_mem_coordinateAlgebra (f : r.coordinateAlgebra) :
    r.inversionPullback f.1 ∈ r.coordinateAlgebra := by
  have hle : r.coordinateAlgebra ≤ r.inversionRepresentable := by
    apply Algebra.adjoin_le
    rintro _ ⟨qn, rfl⟩
    exact r.coordinateJet_mem_inversionRepresentable qn.1 qn.2
  exact hle f.2

/-- Antipode induced by pullback along inversion. -/
def coordinateAntipode : r.coordinateAlgebra →ₐ[C] r.coordinateAlgebra where
  toFun f := ⟨r.inversionPullback f.1, r.inversionPullback_mem_coordinateAlgebra f⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp] theorem coordinateAntipode_coe (f : r.coordinateAlgebra) :
    (r.coordinateAntipode f : G → C) = r.inversionPullback f.1 :=
  rfl

theorem coordinateAntipode_apply (f : r.coordinateAlgebra) (g : G) :
    (r.coordinateAntipode f).1 g = f.1 g⁻¹ :=
  rfl

/-- Comultiplication commutes with the distinguished differential. -/
theorem coordinateComul_deriv (f : r.coordinateAlgebra) :
    r.coordinateComul (Differential.deriv f) =
      tensorProductDerivation (K := C) (r.coordinateComul f) := by
  apply r.coordinateTensorEval_injective
  change r.coordinateTensorEval
      (r.coordinateComulValue (Differential.deriv f)) =
    r.coordinateTensorEval
      (tensorProductDerivation (K := C) (r.coordinateComulValue f))
  rw [r.coordinateTensorEval_coordinateComulValue, r.coordinateTensorEval_deriv,
    r.coordinateTensorEval_coordinateComulValue]
  change r.multiplicationPullback
      ((Differential.deriv f : r.coordinateAlgebra) : G → C) =
    Differential.deriv (r.multiplicationPullback f.1)
  rw [coordinateAlgebra_deriv_coe, r.multiplicationPullback_deriv]

/-- Antipode commutes with the distinguished differential. -/
theorem coordinateAntipode_deriv (f : r.coordinateAlgebra) :
    r.coordinateAntipode (Differential.deriv f) =
      Differential.deriv (r.coordinateAntipode f) := by
  apply Subtype.ext
  change r.inversionPullback
      ((Differential.deriv f : r.coordinateAlgebra) : G → C) =
    Differential.deriv (r.inversionPullback f.1)
  rw [coordinateAlgebra_deriv_coe, r.inversionPullback_deriv]

end DifferentialMatrixGroupRepresentation

end

end GaloisForLFunctions.HTGeometry
