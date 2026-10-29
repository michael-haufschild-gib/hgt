import GaloisForLFunctions.HTGeometry.DualZLatticeCovolume
import GaloisForLFunctions.HTGeometry.DeterminantOneLatticeShortVector

/-!
# Diagonal scaling of intrinsic dual lattices

Real linear maps paired by the standard coordinate form transport integer duals.
For a positive diagonal map the paired map has reciprocal weights. Mapping an
actual real lattice basis also gives the covolume transformation, whose factor
is the product of the positive coordinate weights.
-/

noncomputable section
open Module
open scoped Classical

namespace GaloisForLFunctions.HTGeometry.DualZLattice

variable {ι : Type*} [Fintype ι]
local notation "X" => ι → ℝ

/-- The actual integer-submodule image under a real linear equivalence. -/
def linearImage (A : X ≃ₗ[ℝ] X) (L : Submodule ℤ X) : Submodule ℤ X :=
  L.map (A.toLinearMap.restrictScalars ℤ)

omit [Fintype ι] in
theorem mem_linearImage (A : X ≃ₗ[ℝ] X) (L : Submodule ℤ X) {y : X} :
    y ∈ linearImage A L ↔ ∃ x, x ∈ L ∧ A x = y := Iff.rfl

/-- Paired linear equivalences transport intrinsic integer duals. -/
theorem dual_linearImage_of_pairing (A D : X ≃ₗ[ℝ] X)
    (hAD : ∀ x y, pair (A x) (D y) = pair x y) (L : Submodule ℤ X) :
    dual (linearImage A L) = linearImage D (dual L) := by
  ext y
  constructor
  · intro hy
    refine ⟨D.symm y, ?_, D.apply_symm_apply y⟩
    intro x hx
    obtain ⟨m, hm⟩ := hy (A x) ⟨x, hx, rfl⟩
    refine ⟨m, ?_⟩
    rw [← hAD x (D.symm y), D.apply_symm_apply]
    exact hm
  · rintro ⟨z, hz, rfl⟩ x ⟨w, hw, rfl⟩
    obtain ⟨m, hm⟩ := hz w hw
    exact ⟨m, (hAD w z).trans hm⟩

omit [Fintype ι] in
theorem linearImage_span (A : X ≃ₗ[ℝ] X) (b : Basis ι ℝ X) :
    linearImage A (Submodule.span ℤ (Set.range b)) =
      Submodule.span ℤ (Set.range (b.map A)) := by
  rw [linearImage, Submodule.map_span, ← Set.range_comp]
  rfl

/-- A real linear equivalence changes a full lattice covolume by its absolute determinant. -/
theorem covolume_linearImage_span (A : X ≃ₗ[ℝ] X) (b : Basis ι ℝ X) :
    ZLattice.covolume (linearImage A (Submodule.span ℤ (Set.range b))) =
      |LinearMap.det (A : X →ₗ[ℝ] X)| * ZLattice.covolume (Submodule.span ℤ (Set.range b)) := by
  classical
  have hd : (Pi.basisFun ℝ ι).det ⇑(b.map A) =
      LinearMap.det (A : X →ₗ[ℝ] X) * (Pi.basisFun ℝ ι).det b := by
    rw [Basis.coe_map]
    exact (Pi.basisFun ℝ ι).det_comp A.toLinearMap b
  rw [linearImage_span, covolume_span_eq_abs_det, covolume_span_eq_abs_det]
  simp only [← Pi.basisFun_det_apply]
  rw [hd, abs_mul]

variable [DecidableEq ι]

/-- Reciprocal diagonal weights cancel in the standard coordinate pairing. -/
theorem pair_positiveDiagonal_inverse (s : ι → ℝ) (hs : ∀ i, 0 < s i) (x y : X) :
    pair (positiveDiagonalLinearEquiv s hs x)
      (positiveDiagonalLinearEquiv (fun i => (s i)⁻¹) (fun i => inv_pos.mpr (hs i)) y) =
        pair x y := by
  simp only [pair, positiveDiagonalLinearEquiv_apply]
  apply Finset.sum_congr rfl
  intro i _
  calc
    (s i * x i) * ((s i)⁻¹ * y i) = (s i * (s i)⁻¹) * (x i * y i) := by ring
    _ = x i * y i := by rw [mul_inv_cancel₀ (ne_of_gt (hs i)), one_mul]

/-- Positive diagonal scaling acts on the intrinsic dual by reciprocal weights. -/
theorem dual_positiveDiagonal (s : ι → ℝ) (hs : ∀ i, 0 < s i) (L : Submodule ℤ X) :
    dual (linearImage (positiveDiagonalLinearEquiv s hs) L) =
      linearImage
        (positiveDiagonalLinearEquiv (fun i => (s i)⁻¹) (fun i => inv_pos.mpr (hs i))) (dual L) :=
  dual_linearImage_of_pairing _ _ (pair_positiveDiagonal_inverse s hs) L

/-- A positive diagonal deformation multiplies a full lattice's covolume by its weight product. -/
theorem covolume_positiveDiagonal_span (s : ι → ℝ) (hs : ∀ i, 0 < s i)
    (b : Basis ι ℝ X) :
    ZLattice.covolume (linearImage (positiveDiagonalLinearEquiv s hs)
      (Submodule.span ℤ (Set.range b))) =
        (∏ i, s i) * ZLattice.covolume (Submodule.span ℤ (Set.range b)) := by
  rw [covolume_linearImage_span, det_positiveDiagonalLinearEquiv,
    abs_of_pos (Finset.prod_pos (fun i _ => hs i))]

end GaloisForLFunctions.HTGeometry.DualZLattice
