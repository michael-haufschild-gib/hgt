import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetColumnCoordinates
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerUpperBlocks
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerClassFunctions

/-! With the column cleared, the Jacquet trace is the Whittaker trace of
the twisted tail average on the leading block with an identity appended. -/

noncomputable section
open WindowedLandauTheory.MainNotions.ArithmeticCylinders GaloisForLFunctions
open scoped Classical

namespace GlobalTheory.GLq

variable {g k b : ℕ} [Fact g.Prime]

/-- The column-vanishing trace is the Whittaker trace on the leading
coordinates of the twisted trailing average. -/
theorem tr_eJ'_eq_wh_tailAverage (ψ : AddChar (ZMod g) ℂ) (F : Gn g (k + 1 + b) → ℂ) :
    tr (eJ' g (k + 1 + b) k ψ) F =
      wh ψ (fun A => tailAverage (a := k + 1) (b := b) ψ lastRowFirstColumn F (mirabolicBlock A 0)) := by
  let H := jacquetColumnSubgroup g (k + 1 + b) k
  let U := upperUnitriangular g k
  let R := Matrix (Fin (k + 1)) (Fin b) (ZMod g)
  let W := R × upperUnitriangular g b
  let e : H ≃ U × W := jacquetColumnEquiv
  let φ (M : Mt g (k + 1 + b)) := ∑ j ∈ Finset.range (k + 1 + b - 1), entN M j (j + 1)
  let T (A : U) (z : W) :=
    (whittakerCharacter ψ k A : ℂ)⁻¹ *
      (ψ (lastRowFirstColumn z.1) * (whittakerCharacter ψ b z.2 : ℂ))⁻¹ *
        F (upperBlockUnit (mirabolicBlock A.val 0) z.1 z.2.val)
  have hc : (Nat.card H : ℂ) = (Nat.card U : ℂ) * (Nat.card W : ℂ) := by
    rw [Nat.card_congr e, Nat.card_prod, Nat.cast_mul]
  have hsum : (∑ u : H, (ψ (φ u.val.val))⁻¹ * F u.val) = ∑ A : U, ∑ z : W, T A z := by
    calc
      _ = ∑ p : U × W, T p.1 p.2 := by
        symm
        refine Fintype.sum_equiv e.symm _ _ fun ⟨A, X, D⟩ => ?_
        change T A (X, D) =
          (ψ (φ (jacquetColumnBlock A X D).val.val))⁻¹ * F (jacquetColumnBlock A X D).val
        have hp := whittakerCharacter_upperBlocks ψ
          (unitriangularBlock A 0 (1 : upperUnitriangular g 1)) X D
        rw [whittakerCharacter_append_one] at hp
        change ψ (φ (jacquetColumnBlock A X D).val.val) =
          (whittakerCharacter ψ k A : ℂ) *
            (ψ (lastRowFirstColumn X) * (whittakerCharacter ψ b D : ℂ)) at hp
        rw [hp, jacquetColumnBlock_val, mul_inv]
      _ = _ := by rw [Fintype.sum_prod_type]
  have h : ∀ x : Gn g (k + 1 + b), IsUniUp x.val ∧ (∀ a, a < k → entN x.val a k = 0) ↔ x ∈ H :=
    fun x => (mem_jacquetColumnSubgroup_iff (by omega) x).symm
  unfold eJ'
  rw [tr_eDat_of_subgroup _ _ ψ H h F, wh_eq_restricted_pairing_of_function, characterPairing]
  change (Nat.card H : ℂ)⁻¹ * (∑ u : H, (ψ (φ u.val.val))⁻¹ * F u.val) =
    (Nat.card U : ℂ)⁻¹ * ∑ A : U,
      tailAverage (a := k + 1) (b := b) ψ lastRowFirstColumn F (mirabolicBlock A.val 0) *
        (whittakerCharacter ψ k A⁻¹ : ℂ)
  rw [hc, hsum, mul_inv]
  unfold tailAverage
  simp only [Finset.mul_sum, Finset.sum_mul, map_inv, Units.val_inv_eq_inv_val]
  refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun z _ => ?_
  dsimp only [T]
  ring

end GlobalTheory.GLq
