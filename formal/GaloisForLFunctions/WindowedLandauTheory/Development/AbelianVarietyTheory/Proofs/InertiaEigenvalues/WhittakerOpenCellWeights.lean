import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerOpenCellOverlap
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockSuperdiagonal
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerVectors

/-! The Whittaker weight on the open-cell overlap is the product of the
weights on the two unitriangular Levi blocks. -/

noncomputable section
open scoped Classical

open GaloisForLFunctions WindowedLandauTheory.MainNotions.ArithmeticCylinders

namespace GlobalTheory.GLq

variable {g a b : ℕ} [Fact g.Prime]

private theorem wh_eq_restricted_pairing (ψ : AddChar (ZMod g) ℂ) {n : ℕ}
    {χ : Gn g n → ℂ} (hχ : IsChar χ) :
    let U := upperUnitriangular g n
    wh ψ χ = characterPairing U (fun u => (whittakerCharacter ψ n u : ℂ)) (fun u => χ u.val) := by
  obtain ⟨V, hV⟩ := hχ
  rw [← funext hV, wh_eq_finrank]
  let U := upperUnitriangular g n
  let ρ := linearCharacterRepresentation (whittakerCharacter ψ n)
  let σ := V.ρ.comp U.subtype
  have hρ : Representation.character ρ = (fun u : U => (whittakerCharacter ψ n u : ℂ)) :=
    funext (linearCharacterRepresentation_character _)
  exact (representationCharacterPairing_eq_finrank U ρ σ).symm.trans
    (congrArg (fun f => characterPairing U f (Representation.character σ)) hρ)

/-- The open-cell Whittaker character factors through the two unitriangular blocks. -/
theorem whittakerCharacter_openCell (ψ : AddChar (ZMod g) ℂ) (u : openCellOverlap g a b) :
    (whittakerCharacter ψ (a + b) u.val : ℂ) =
      (whittakerCharacter ψ a (openCellProjection u).1 : ℂ) *
        (whittakerCharacter ψ b (openCellProjection u).2 : ℂ) := by
  let A : Mt g a := (openCellProjection u).1.val.val
  let B : Mt g b := (openCellProjection u).2.val.val
  let e := finCongr (Nat.add_comm b a)
  have hs : (∑ i ∈ Finset.range (a + b - 1), entN u.val.val.val i (i + 1)) =
      (∑ i ∈ Finset.range (b - 1), entN B i (i + 1)) +
        ∑ i ∈ Finset.range (a - 1), entN A i (i + 1) := by
    calc
      _ = ∑ i ∈ Finset.range (b + a - 1), entN (u.val.val.val.submatrix e e) i (i + 1) :=
        (superdiagonal_submatrix_finCongr (Nat.add_comm b a) u.val.val.val).symm
      _ = _ := by
        rw [openCellReindexedMatrix]
        exact superdiagonal_blockDiagonal B A
  change ψ (∑ i ∈ Finset.range (a + b - 1), entN u.val.val.val i (i + 1)) = _
  exact (congrArg ψ hs).trans ((AddChar.map_add_eq_mul ψ _ _).trans (mul_comm _ _))

/-- The open-cell overlap contributes the product of the two Whittaker traces. -/
theorem whittaker_overlap_openCell (ψ : AddChar (ZMod g) ℂ) {α : Gn g a → ℂ} {β : Gn g b → ℂ}
    (hα : IsChar α) (hβ : IsChar β) :
    doubleCosetPairing (upperUnitriangular g (a + b)) (twoBlockParabolic g a b)
      (fun u => (whittakerCharacter ψ (a + b) u : ℂ))
      (fun p => α (twoBlockLevi p).1 * β (twoBlockLevi p).2)
      (permutationUnit (openCellPermutation a b)) = wh ψ α * wh ψ β := by
  let O := openCellOverlap g a b
  letI : Fintype O := Fintype.ofFinite O
  let A := upperUnitriangular g a
  let B := upperUnitriangular g b
  let e : O ≃* A × B := openCellOverlapEquiv
  let f (x : A) := α x.val * (whittakerCharacter ψ a x⁻¹ : ℂ)
  let h (y : B) := β y.val * (whittakerCharacter ψ b y⁻¹ : ℂ)
  let c : ℂ := Nat.card A
  let d : ℂ := Nat.card B
  have hc : c ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hd : d ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hCard : (Nat.card O : ℂ) = c * d := by
    change _ = (Nat.card A : ℂ) * Nat.card B
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.cast_mul]
  have hSum : (∑ u : O, α (e u).1.val * β (e u).2.val *
      (whittakerCharacter ψ (a + b) (u⁻¹ : O).val : ℂ)) = (∑ x : A, f x) * ∑ y : B, h y := by
    calc
      _ = ∑ z : A × B, f z.1 * h z.2 := by
        refine Fintype.sum_equiv e.toEquiv _ _ fun u => ?_
        change α (e u).1.val * β (e u).2.val * (whittakerCharacter ψ (a + b) (u⁻¹ : O).val : ℂ) =
          f (e u).1 * h (e u).2
        rw [whittakerCharacter_openCell ψ (u⁻¹ : O),
          show openCellProjection (u⁻¹ : O) = (e u)⁻¹ from map_inv e u]
        dsimp only [f, h]
        let x := (e u).1
        let y := (e u).2
        let s : ℂ := whittakerCharacter ψ a x⁻¹
        let t : ℂ := whittakerCharacter ψ b y⁻¹
        change α x.val * β y.val * (s * t) = (α x.val * s) * (β y.val * t)
        ring
      _ = _ := by rw [Fintype.sum_prod_type, Finset.sum_mul]; simp only [Finset.mul_sum]
  rw [doubleCosetPairing_eq_pairing, wh_eq_restricted_pairing ψ hα, wh_eq_restricted_pairing ψ hβ]
  change (Nat.card O : ℂ)⁻¹ * (∑ u : O, α (e u).1.val * β (e u).2.val *
      (whittakerCharacter ψ (a + b) (u⁻¹ : O).val : ℂ)) =
    (c⁻¹ * ∑ x : A, f x) * (d⁻¹ * ∑ y : B, h y)
  rw [hCard, hSum]
  field_simp [hc, hd]

end GlobalTheory.GLq
