import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalizedTypesCompatibility
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CuspidalLabelSymmetries

/-! Green's cuspidal label map supplies the symmetry laws and series idempotents
required by the normalized type data. -/

noncomputable section
open Polynomial GlobalTheory.GLq WindowedLandauTheory.CyclotomicNorms

namespace WindowedLandauTheory.NormalizedTypes

variable {g : ℕ} [Fact g.Prime]

/-- The label map defined by the elliptic character formula is equivariant under
Galois conjugation, duality and determinant twists, and gives Green's series idempotents. -/
theorem exists_equivariant_cuspidalLabelMap (L : LabelDatum g) (hg : 5 ≤ g) :
    ∃ O : CuspidalLabelMap g,
      LabelMapEquivariant O ∧ LabTwLawO L O ∧
      (∀ (χ : CuspidalCharacter g 1) (x : ZMod g), x ≠ 0 →
        (∀ (γ : Gn g 1) (m : ℕ), L.gen 1 ^ m = algebraMap (ZMod g) (Fbar g) γ.val.det →
          χ.val γ = L.teich (algebraMap (ZMod g) (Fbar g) x) ^ m) →
        (O.lab 1 χ).val = X - C x) ∧
      (∀ r f, eSerO O r f = eSerC L r f) ∧
      ∀ (d : ℕ) (χ : CuspidalCharacter g d), IsCuspOf L (O.lab d χ).val χ.val := by
  obtain ⟨O, hO⟩ := exists_cuspidalLabelMap L
  refine ⟨O, ⟨?_, ?_⟩, ?_, ?_, ?_, hO⟩
  · intro d α a hα χ χ' hχ
    exact rootsBar_of_cuspidal_galois L hg α a hα (hO d χ) (hO d χ') hχ
  · intro d χ χ' hχ
    exact rootsBar_of_cuspidal_dual L hg (hO d χ) (hO d χ') hχ
  · intro d χ χ' x hx hχ
    exact rootsBar_of_cuspidal_twist L hg (hO d χ) (hO d χ') x hx hχ
  · intro χ x hx hχ
    exact cuspLabel_rank_one L hg (hO 1 χ) x hx hχ
  · intro r f
    by_cases hf : f.Monic ∧ f.natDegree = r ∧ f.coeff 0 ≠ 0
    · rw [eSerO_eq_eSerC (σ := id) (π := id) O L hO hg (fun _ _ h => ⟨h, rfl⟩) hf.1 hf.2.2,
        relabelPolynomial_id hf.1]
    · rw [eSerO_eq_zero O f hf]
      symm
      unfold eSerC
      apply finsum_eq_zero_of_forall_eq_zero
      intro χ
      haveI : IsEmpty (χ ∈ {χ : Gn g r → ℂ | IsIrr χ ∧ HasLabel L χ f}) :=
        ⟨fun h => hf (hasLabel_polynomial_properties L h.2)⟩
      exact finsum_of_isEmpty _

end WindowedLandauTheory.NormalizedTypes
