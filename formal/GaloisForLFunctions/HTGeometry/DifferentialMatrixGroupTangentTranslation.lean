import GaloisForLFunctions.HTGeometry.DifferentialMatrixGroupHopfAlgebra

/-!
# Translate a generic derivation to the identity of a differential matrix group

For a point `φ` of a represented group and a derivation `d` at `φ`, convolution with the
antipode translates `d` to a derivation at the identity.  The construction is algebraic and its
compatibility with the distinguished differential follows from compatibility of comultiplication
and antipode.
-/

open scoped Differential TensorProduct

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

variable {C G L : Type u} [Field C] [Differential C] [Group G]
  [Field L] [Algebra C L]

namespace DifferentialMatrixGroupRepresentation

variable (r : DifferentialMatrixGroupRepresentation (C := C) (G := G))

local instance tangentCoordinateDifferential : Differential r.coordinateAlgebra :=
  r.coordinateAlgebraDifferential

/-- The bilinear pairing `(a,b) ↦ φ(Sa) d(b)` used for tangent translation. -/
def tangentTranslationBilinear
    (φ : r.coordinateAlgebra →ₐ[C] L) (d : r.coordinateAlgebra →ₗ[C] L) :
    r.coordinateAlgebra →ₗ[C] r.coordinateAlgebra →ₗ[C] L where
  toFun a :=
    { toFun := fun b => φ (r.coordinateAntipode a) * d b
      map_add' := fun b c => by rw [map_add, mul_add]
      map_smul' := fun c b => by
        rw [map_smul]
        simp only [Algebra.smul_def, RingHom.id_apply]
        ring }
  map_add' a b := by
    ext c
    change φ (r.coordinateAntipode (a + b)) * d c =
      φ (r.coordinateAntipode a) * d c + φ (r.coordinateAntipode b) * d c
    have hS : r.coordinateAntipode (a + b) =
        r.coordinateAntipode a + r.coordinateAntipode b := by
      exact map_add _ _ _
    have hφ : φ (r.coordinateAntipode a + r.coordinateAntipode b) =
        φ (r.coordinateAntipode a) + φ (r.coordinateAntipode b) := by
      exact map_add _ _ _
    rw [hS, hφ, add_mul]
  map_smul' c a := by
    ext b
    change φ (r.coordinateAntipode (c • a)) * d b =
      c • (φ (r.coordinateAntipode a) * d b)
    have hS : r.coordinateAntipode (c • a) = c • r.coordinateAntipode a := by
      exact map_smul _ _ _
    have hφ : φ (c • r.coordinateAntipode a) = c • φ (r.coordinateAntipode a) := by
      exact map_smul _ _ _
    rw [hS, hφ]
    simp only [Algebra.smul_def]
    ring

/-- Linearized convolution pairing on the tensor square. -/
def tangentTranslationPairing
    (φ : r.coordinateAlgebra →ₐ[C] L) (d : r.coordinateAlgebra →ₗ[C] L) :
    r.coordinateAlgebra ⊗[C] r.coordinateAlgebra →ₗ[C] L :=
  TensorProduct.lift (r.tangentTranslationBilinear φ d)

@[simp] theorem tangentTranslationPairing_tmul
    (φ : r.coordinateAlgebra →ₐ[C] L) (d : r.coordinateAlgebra →ₗ[C] L)
    (a b : r.coordinateAlgebra) :
    r.tangentTranslationPairing φ d (a ⊗ₜ[C] b) =
      φ (r.coordinateAntipode a) * d b :=
  rfl

/-- Character at the pair `(φ⁻¹,φ)`. -/
def tangentTranslationCharacter (φ : r.coordinateAlgebra →ₐ[C] L) :
    r.coordinateAlgebra ⊗[C] r.coordinateAlgebra →ₐ[C] L :=
  Algebra.TensorProduct.lift (φ.comp r.coordinateAntipode) φ (fun _ _ => Commute.all _ _)

@[simp] theorem tangentTranslationCharacter_tmul
    (φ : r.coordinateAlgebra →ₐ[C] L) (a b : r.coordinateAlgebra) :
    r.tangentTranslationCharacter φ (a ⊗ₜ[C] b) =
      φ (r.coordinateAntipode a) * φ b :=
  rfl

/-- The tensor pairing is a derivation at the tensor character. -/
theorem tangentTranslationPairing_mul
    (φ : r.coordinateAlgebra →ₐ[C] L) (d : r.coordinateAlgebra →ₗ[C] L)
    (hd : ∀ a b, d (a * b) = φ a * d b + φ b * d a)
    (t u : r.coordinateAlgebra ⊗[C] r.coordinateAlgebra) :
    r.tangentTranslationPairing φ d (t * u) =
      r.tangentTranslationCharacter φ t * r.tangentTranslationPairing φ d u +
      r.tangentTranslationCharacter φ u * r.tangentTranslationPairing φ d t := by
  induction t using TensorProduct.induction_on with
  | zero => simp [tangentTranslationPairing, tangentTranslationCharacter]
  | add t₁ t₂ ht₁ ht₂ =>
      rw [add_mul, map_add, map_add, map_add, ht₁, ht₂]
      ring
  | tmul a b =>
      induction u using TensorProduct.induction_on with
      | zero => simp [tangentTranslationPairing, tangentTranslationCharacter]
      | add u₁ u₂ hu₁ hu₂ =>
          rw [mul_add, map_add, map_add, map_add, hu₁, hu₂]
          ring
      | tmul c e =>
          rw [Algebra.TensorProduct.tmul_mul_tmul,
            r.tangentTranslationPairing_tmul,
            r.tangentTranslationPairing_tmul,
            r.tangentTranslationPairing_tmul,
            r.tangentTranslationCharacter_tmul,
            r.tangentTranslationCharacter_tmul]
          have hS : r.coordinateAntipode (a * c) =
              r.coordinateAntipode a * r.coordinateAntipode c := by
            exact map_mul _ _ _
          have hφ : φ (r.coordinateAntipode a * r.coordinateAntipode c) =
              φ (r.coordinateAntipode a) * φ (r.coordinateAntipode c) := by
            exact map_mul _ _ _
          rw [hS, hφ, hd]
          ring

/-- The tensor character is evaluation after multiplying the antipode of the left factor. -/
theorem tangentTranslationCharacter_eq_phi_lift
    (φ : r.coordinateAlgebra →ₐ[C] L)
    (t : r.coordinateAlgebra ⊗[C] r.coordinateAlgebra) :
    r.tangentTranslationCharacter φ t =
      φ (Algebra.TensorProduct.lift r.coordinateAntipode
        (AlgHom.id C r.coordinateAlgebra) (fun _ _ => Commute.all _ _) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp [tangentTranslationCharacter]
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
  | tmul a b =>
      rw [r.tangentTranslationCharacter_tmul,
        Algebra.TensorProduct.lift_tmul, map_mul]
      rfl

/-- The translated tensor character restricts along comultiplication to the identity point. -/
theorem tangentTranslationCharacter_comul
    (φ : r.coordinateAlgebra →ₐ[C] L) (a : r.coordinateAlgebra) :
    r.tangentTranslationCharacter φ (r.coordinateComul a) =
      algebraMap C L (r.coordinateCounit a) := by
  rw [r.tangentTranslationCharacter_eq_phi_lift]
  have hconv :
      Algebra.TensorProduct.lift r.coordinateAntipode
          (AlgHom.id C r.coordinateAlgebra) (fun _ _ => Commute.all _ _)
          (r.coordinateComul a) =
        algebraMap C r.coordinateAlgebra (r.coordinateCounit a) := by
    apply Subtype.ext
    funext g
    rw [r.coordinateLift_antipode_id_apply,
      r.coordinateTensorEval_coordinateComul]
    simp
    rfl
  rw [hconv]
  exact φ.commutes _

/-- Character of the identity point, valued in `L`. -/
def tangentIdentityCharacter : r.coordinateAlgebra →ₐ[C] L :=
  (Algebra.ofId C L).comp r.coordinateCounit

/-- Linear map obtained by translating `d` from `φ` to the identity. -/
def tangentTranslatedLinear
    (φ : r.coordinateAlgebra →ₐ[C] L) (d : r.coordinateAlgebra →ₗ[C] L) :
    r.coordinateAlgebra →ₗ[C] L :=
  (r.tangentTranslationPairing φ d).comp r.coordinateComul.toLinearMap

theorem tangentTranslatedLinear_apply
    (φ : r.coordinateAlgebra →ₐ[C] L) (d : r.coordinateAlgebra →ₗ[C] L)
    (a : r.coordinateAlgebra) :
    r.tangentTranslatedLinear φ d a =
      r.tangentTranslationPairing φ d (r.coordinateComul a) :=
  rfl

/-- The translated linear map satisfies Leibniz at the identity character. -/
theorem tangentTranslatedLinear_mul
    (φ : r.coordinateAlgebra →ₐ[C] L) (d : r.coordinateAlgebra →ₗ[C] L)
    (hd : ∀ a b, d (a * b) = φ a * d b + φ b * d a)
    (a b : r.coordinateAlgebra) :
    r.tangentTranslatedLinear φ d (a * b) =
    r.tangentIdentityCharacter a * r.tangentTranslatedLinear φ d b +
      r.tangentIdentityCharacter b * r.tangentTranslatedLinear φ d a := by
  have hcomul : r.coordinateComul (a * b) =
      r.coordinateComul a * r.coordinateComul b := by
    exact map_mul _ _ _
  rw [tangentTranslatedLinear_apply, hcomul,
    r.tangentTranslationPairing_mul φ d hd,
    r.tangentTranslationCharacter_comul,
    r.tangentTranslationCharacter_comul]
  rfl

/-- Algebra structure on `L` induced by evaluation at the identity. -/
@[reducible] def tangentIdentityAlgebra : Algebra r.coordinateAlgebra L :=
  (r.tangentIdentityCharacter (L := L)).toRingHom.toAlgebra

/-- Generic-point derivation translated to an identity-point derivation. -/
def tangentTranslatedDerivation
    (φ : r.coordinateAlgebra →ₐ[C] L) (d : r.coordinateAlgebra →ₗ[C] L)
    (hd : ∀ a b, d (a * b) = φ a * d b + φ b * d a) :
    letI : Algebra r.coordinateAlgebra L := r.tangentIdentityAlgebra
    Derivation C r.coordinateAlgebra L := by
  letI : Algebra r.coordinateAlgebra L := r.tangentIdentityAlgebra
  apply Derivation.mk' (r.tangentTranslatedLinear φ d)
  intro a b
  rw [r.tangentTranslatedLinear_mul φ d hd]
  rfl

/-- The translation pairing intertwines the tensor differential with the target differential. -/
theorem tangentTranslationPairing_deriv
    [Differential L] [DifferentialAlgebra C L]
    (φ : r.coordinateAlgebra →ₐ[C] L) (d : r.coordinateAlgebra →ₗ[C] L)
    (hφ : ∀ a, φ (Differential.deriv a) = Differential.deriv (φ a))
    (hdδ : ∀ a, d (Differential.deriv a) = Differential.deriv (d a))
    (t : r.coordinateAlgebra ⊗[C] r.coordinateAlgebra) :
    r.tangentTranslationPairing φ d (tensorProductDerivation (K := C) t) =
      Differential.deriv (r.tangentTranslationPairing φ d t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp [tangentTranslationPairing]
  | add a b ha hb =>
      have hp : r.tangentTranslationPairing φ d (a + b) =
          r.tangentTranslationPairing φ d a + r.tangentTranslationPairing φ d b :=
        (r.tangentTranslationPairing φ d).map_add a b
      rw [map_add, map_add, ha, hb]
      rw [hp]
      exact (map_add (Differential.deriv : Derivation ℤ L L) _ _).symm
  | tmul a b =>
      rw [tensorProductDerivation_tmul, map_add,
        r.tangentTranslationPairing_tmul,
        r.tangentTranslationPairing_tmul,
        r.tangentTranslationPairing_tmul,
        r.coordinateAntipode_deriv, hφ, hdδ, Derivation.leibniz]
      ring

/-- Tangent translation preserves commutation with the distinguished differential. -/
theorem tangentTranslatedLinear_deriv
    [Differential L] [DifferentialAlgebra C L]
    (φ : r.coordinateAlgebra →ₐ[C] L) (d : r.coordinateAlgebra →ₗ[C] L)
    (hφ : ∀ a, φ (Differential.deriv a) = Differential.deriv (φ a))
    (hdδ : ∀ a, d (Differential.deriv a) = Differential.deriv (d a))
    (a : r.coordinateAlgebra) :
    r.tangentTranslatedLinear φ d (Differential.deriv a) =
      Differential.deriv (r.tangentTranslatedLinear φ d a) := by
  rw [tangentTranslatedLinear_apply, r.coordinateComul_deriv,
    r.tangentTranslationPairing_deriv φ d hφ hdδ]
  rfl

/-- Translation formula on a matrix coordinate. -/
theorem tangentTranslatedLinear_coordinate
    (φ : r.coordinateAlgebra →ₐ[C] L) (d : r.coordinateAlgebra →ₗ[C] L)
    (q : Fin 2 × Fin 2) :
    r.tangentTranslatedLinear φ d
        ⟨r.coordinate q, Algebra.subset_adjoin ⟨(q, 0), by
          funext g
          exact (differentialJet_zero _).symm⟩⟩ =
      ∑ k : Fin 2,
        φ (r.coordinateAntipode
          ⟨r.coordinate (q.1, k), Algebra.subset_adjoin ⟨((q.1, k), 0), by
            funext g
            exact (differentialJet_zero _).symm⟩⟩) *
        d ⟨r.coordinate (k, q.2), Algebra.subset_adjoin ⟨((k, q.2), 0), by
          funext g
          exact (differentialJet_zero _).symm⟩⟩ := by
  rw [tangentTranslatedLinear_apply]
  have hcomul : r.coordinateComul
        ⟨r.coordinate q, Algebra.subset_adjoin ⟨(q, 0), by
          funext g
          exact (differentialJet_zero _).symm⟩⟩ =
      ∑ k : Fin 2,
        (⟨r.coordinate (q.1, k), Algebra.subset_adjoin ⟨((q.1, k), 0), by
          funext g
          exact (differentialJet_zero _).symm⟩⟩ : r.coordinateAlgebra) ⊗ₜ[C]
        ⟨r.coordinate (k, q.2), Algebra.subset_adjoin ⟨((k, q.2), 0), by
          funext g
          exact (differentialJet_zero _).symm⟩⟩ := by
    apply r.coordinateTensorEval_injective
    ext z
    rw [r.coordinateTensorEval_coordinateComul]
    simp only [map_sum]
    change r.matrix (z.1 * z.2) q.1 q.2 =
      ∑ k : Fin 2, r.matrix z.1 q.1 k * r.matrix z.2 k q.2
    rw [r.matrix.map_mul, Matrix.mul_apply]
  rw [hcomul, map_sum]
  exact Finset.sum_congr rfl fun k _ => r.tangentTranslationPairing_tmul _ _ _ _

end DifferentialMatrixGroupRepresentation

end

end GaloisForLFunctions.HTGeometry
