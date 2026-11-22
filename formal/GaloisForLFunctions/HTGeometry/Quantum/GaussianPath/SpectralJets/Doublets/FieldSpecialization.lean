import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Doublets.PairPolynomial
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.LinearPencil

/-! # Longitudinal differentiation with polynomial background couplings -/
open MvPolynomial Matrix
namespace GaloisForLFunctions.HTGeometry.SpectralJets.Doublets
noncomputable section
variable {I κ ρ R S : Type*} [Fintype I] [DecidableEq I] [Fintype κ] [CommRing R] [CommRing S]

/-- The background matrix may already have polynomial entries in the Pauli couplings. -/
def fieldCharacteristic (H : Matrix I I R) (u : I → κ → R) : MvPolynomial (Option κ) R :=
  (scalar I (X none) - H.map C - diagonal (fun j => fieldPoly (u j))).det

theorem map_fieldCharacteristic (φ : R →+* S) (H : Matrix I I R) (u : I → κ → R) :
    MvPolynomial.map φ (fieldCharacteristic H u) = fieldCharacteristic (H.map φ) (fun j => φ ∘ u j) := by
  rw [fieldCharacteristic,fieldCharacteristic,RingHom.map_det]
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  by_cases he : i=j
  · subst j
    simp [RingHom.mapMatrix_apply,Matrix.map_apply,Matrix.scalar_apply,map_fieldPoly]
  · simp [RingHom.mapMatrix_apply,Matrix.map_apply,Matrix.scalar_apply,he]

theorem eval_fieldCharacteristic (H : Matrix I I R) (u : I → κ → R) (y : R) (h : κ → R) :
    eval (fun o : Option κ => o.elim y h) (fieldCharacteristic H u) =
      (scalar I y-(H+diagonal (fun j => ∑ i, u j i*h i))).det := by
  rw [fieldCharacteristic,RingHom.map_det]
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  by_cases he : i=j
  · subst j
    simp [RingHom.mapMatrix_apply,Matrix.scalar_apply,eval_fieldPoly,sub_add_eq_sub_sub]
  · simp [RingHom.mapMatrix_apply,Matrix.scalar_apply,he]

/-- Set the independent perturbations to zero and retain the energy variable and
the background couplings. This is applied after differentiating. -/
def atZeroField : MvPolynomial (Option κ) (MvPolynomial ρ R) →+* MvPolynomial (Option ρ) R :=
  eval₂Hom (rename (R := R) (some : ρ → Option ρ)).toRingHom
    (fun o : Option κ => o.elim (X none) (fun _ => 0))

omit [Fintype κ] in
theorem eval_atZeroField (φ : R →+* S) (x : ρ → S) (y : S)
    (q : MvPolynomial (Option κ) (MvPolynomial ρ R)) :
    eval₂ φ (fun o : Option ρ => o.elim y x) (atZeroField q) =
      eval (fun o : Option κ => o.elim y 0) (MvPolynomial.map (eval₂Hom φ x) q) := by
  induction q using MvPolynomial.induction_on with
  | C c =>
    simp only [atZeroField,eval₂Hom_C,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,eval₂_rename,
      MvPolynomial.map_C,eval_C]
    rfl
  | add a b ha hb => simpa only [map_add,eval₂_add] using congrArg₂ (·+·) ha hb
  | mul_X a i ha =>
    simp only [map_mul,eval₂_mul,MvPolynomial.map_X,eval_X,ha]
    congr 1
    cases i <;> simp [atZeroField]

/-- A polynomial row in the energy and couplings, with the common spectral denominator cleared. -/
def fieldRow (M : Matrix I I (MvPolynomial ρ R)) (u : I → κ → R) (L : ℕ) (w : List κ) :
    MvPolynomial (Option ρ) R :=
  atZeroField (jetRow (fieldCharacteristic M (fun j i => C (u j i))) L (some w))

theorem eval_fieldRow (φ : R →+* S) (x : ρ → S) (y : S) (M : Matrix I I (MvPolynomial ρ R))
    (u : I → κ → R) (L : ℕ) (w : List κ) :
    eval₂ φ (fun o : Option ρ => o.elim y x) (fieldRow M u L w) =
      eval (fun o : Option κ => o.elim y 0)
        (jetRow (fieldCharacteristic (M.map (eval₂Hom φ x)) (fun j => φ ∘ u j)) L (some w)) := by
  rw [fieldRow,eval_atZeroField,jetRow_map,map_fieldCharacteristic]
  simp only [Function.comp_def,eval₂Hom_C]


end
end GaloisForLFunctions.HTGeometry.SpectralJets.Doublets
