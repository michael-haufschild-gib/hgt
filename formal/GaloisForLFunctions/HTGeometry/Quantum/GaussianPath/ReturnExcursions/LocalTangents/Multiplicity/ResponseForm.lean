import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.LocalTangents.Multiplicity.CompressedPaulis
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-! # Pauli generators preserving all active quadratic readings -/

open Matrix Module Set
open scoped ComplexConjugate
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.LocalTangents.Multiplicity
noncomputable section
private abbrev Bits (n : ℕ) := Fin n → Bool
private abbrev Mat (I : Type*) := Matrix I I ℂ
variable {N : ℕ} {I : Type*} [Fintype I] [DecidableEq I]

/-- Twice the Hermitian part of the matrix of first variations on the
chosen left and right column families. -/
private def response (P Q : Matrix (Bits N) I ℂ) :
    selfAdjoint (Mat (Bits N)) →ₗ[ℝ] selfAdjoint (Mat I) where
  toFun B :=
    let Z := Pᴴ*((Complex.I • B.val)*Q)
    ⟨Z+Zᴴ,by change (Z+Zᴴ)ᴴ=_; rw [conjTranspose_add,conjTranspose_conjTranspose,add_comm]⟩
  map_add' B C := by
    apply Subtype.ext
    change _ = (_+_)+(_+_)
    simp only [AddSubgroup.coe_add,smul_add,Matrix.add_mul,Matrix.mul_add,conjTranspose_add]
    abel
  map_smul' r B := by
    apply Subtype.ext
    change _=r • (_+_)
    simp only [selfAdjoint.val_smul,smul_comm Complex.I r,Matrix.smul_mul,Matrix.mul_smul,
      conjTranspose_smul,star_trivial,smul_add]

omit [DecidableEq I] in
private theorem cross_re {J : Type*} [Fintype J] (P Q : Matrix J I ℂ) (c : I → ℂ) :
    (star c ⬝ᵥ ((Pᴴ*Q+(Pᴴ*Q)ᴴ) *ᵥ c)).re=
      2*(star (P *ᵥ c) ⬝ᵥ (Q *ᵥ c)).re := by
  have h (S T : Matrix J I ℂ) : star c ⬝ᵥ ((Sᴴ*T) *ᵥ c)=star (S *ᵥ c) ⬝ᵥ (T *ᵥ c) := by
    rw [←mulVec_mulVec,dotProduct_mulVec,vecMul_conjTranspose,star_star]
  rw [conjTranspose_mul,conjTranspose_conjTranspose,add_mulVec,dotProduct_add,h,h,Complex.add_re]
  have hh := congrArg Complex.re (star_dotProduct (Q *ᵥ c) (P *ᵥ c))
  simpa only [Complex.star_def,Complex.conj_re,two_mul] using
    (show _+_= _+_ from congrArg ((star (P *ᵥ c) ⬝ᵥ (Q *ᵥ c)).re+·) hh)

/-- A single combination of at most r² Pauli words exactly reproduces
the first variation for all superpositions of the r tested vectors. -/
theorem sparse_cross_readings (P Q : Matrix (Bits N) I ℂ) (B : selfAdjoint (Mat (Bits N))) :
    ∃ d ≤ Fintype.card I^2, ∃ (w : Fin d → Fin N → Option (Fin 3)) (a : Fin d → ℝ),
      let C := ∑ i, a i • finitePauliSelfAdjoint (w i)
      ∀ c : I → ℂ, (star (P *ᵥ c) ⬝ᵥ ((Complex.I • C.val)*ᵥ(Q *ᵥ c))).re=
        (star (P *ᵥ c) ⬝ᵥ ((Complex.I • B.val)*ᵥ(Q *ᵥ c))).re := by
  obtain ⟨d,hd,w,a,he⟩ := sparse_pauli_response (response P Q) B
  refine ⟨d,hd,w,a,?_⟩
  intro C c
  have hh := congrArg (fun H : selfAdjoint (Mat I) => (star c ⬝ᵥ (H.val *ᵥ c)).re) he
  change (star c ⬝ᵥ ((Pᴴ*((Complex.I • C.val)*Q)+(Pᴴ*((Complex.I • C.val)*Q))ᴴ) *ᵥ c)).re=
    (star c ⬝ᵥ ((Pᴴ*((Complex.I • B.val)*Q)+(Pᴴ*((Complex.I • B.val)*Q))ᴴ) *ᵥ c)).re at hh
  simpa only [cross_re,←mulVec_mulVec,mul_right_inj' (by norm_num : (2:ℝ)≠0)] using hh

#print axioms sparse_cross_readings
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.LocalTangents.Multiplicity
