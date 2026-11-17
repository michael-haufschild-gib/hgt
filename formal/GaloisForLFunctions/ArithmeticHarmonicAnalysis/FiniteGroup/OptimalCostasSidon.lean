import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.CostasDifferenceFibers
import GaloisForLFunctions.HTGeometry.AdditiveCombinatorics.PollardSidon

/-!
# Optimal finite-field Sidon diagonals

The additive/multiplicative diagonal transfers to the existing representation-count
notion of a Sidon set. Its q−1 elements attain the maximum possible cardinality
in the ambient group of order q(q−1), by counting nonidentity differences.

This is an extremal consequence of the diagonal difference identity in
Low–Schmidt, arXiv:2611.20974, equation (2).
-/

noncomputable section
open scoped Pointwise
open Finset
open GaloisForLFunctions.HTGeometry.AddComb
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.Costas

/-- The elementary difference bound for Sidon subsets of any finite commutative group. -/
theorem sidon_card_bound {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
    (B : Finset G) (hB : ∀ y : G, 2 ≤ rep B B⁻¹ y → y = 1) :
    B.card ^ 2 + 1 ≤ B.card + Fintype.card G := by
  have h1 : rep B B⁻¹ 1 ≤ B.card := by
    simpa only [Finset.card_inv] using rep_le_card_right B B⁻¹ 1
  have ho (y : G) (hy : y ≠ 1) : rep B B⁻¹ y ≤ 1 := by
    by_contra h
    exact hy (hB y (by omega))
  have hs : ∑ y ∈ (Finset.univ : Finset G).erase 1, rep B B⁻¹ y ≤
      Fintype.card G - 1 := by
    calc
      _ ≤ ∑ _y ∈ (Finset.univ : Finset G).erase 1, 1 :=
        Finset.sum_le_sum (fun y hy => ho y (Finset.mem_erase.mp hy).1)
      _ = Fintype.card G - 1 := by simp
  have he := Finset.add_sum_erase (Finset.univ : Finset G)
    (fun y => rep B B⁻¹ y) (Finset.mem_univ (1 : G))
  rw [sum_rep, Finset.card_inv] at he
  have hG : 0 < Fintype.card G := Fintype.card_pos
  have hGsub : Fintype.card G - 1 + 1 = Fintype.card G := Nat.sub_add_cancel hG
  nlinarith only [h1, hs, he, hGsub]

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] (L : F ≃+ F)

/-- The additive/multiplicative diagonal inside the direct-product group. -/
def diagonalPoint (t : Fˣ) : Multiplicative F × Fˣ := (Multiplicative.ofAdd (L (t : F)), t)

/-- The finite diagonal set, parametrized without repetitions by nonzero field elements. -/
def diagonalSet : Finset (Multiplicative F × Fˣ) := Finset.univ.image (diagonalPoint L)

omit [Fintype F] [DecidableEq F] in
theorem diagonalPoint_injective : Function.Injective (diagonalPoint L) :=
  fun _ _ h => congrArg Prod.snd h

theorem diagonalSet_card : (diagonalSet L).card = Fintype.card F - 1 := by
  rw [diagonalSet, Finset.card_image_of_injective _ (diagonalPoint_injective L),
    Finset.card_univ, Fintype.card_units]

omit [Fintype F] [DecidableEq F] in
private theorem equal_diagonal_differences {s t u v : Fˣ}
    (hst : s ≠ t)
    (he : diagonalPoint L s * (diagonalPoint L t)⁻¹ =
      diagonalPoint L u * (diagonalPoint L v)⁻¹) : s = u ∧ t = v := by
  have hx : L (s : F) - L (t : F) ≠ 0 := by
    intro h
    exact hst (Units.ext (L.injective (sub_eq_zero.mp h)))
  have hr : s / t ≠ 1 := fun h => hst (div_eq_one.mp h)
  obtain ⟨z, _, hz⟩ := unique_difference L (L (s : F) - L (t : F)) (s / t) hx hr
  have hstz := hz (s, t) ⟨rfl, rfl⟩
  have hxy := congrArg (fun g : Multiplicative F × Fˣ => Multiplicative.toAdd g.1) he.symm
  change L (u : F) + -L (v : F) = L (s : F) + -L (t : F) at hxy
  have huvz := hz (u, v)
    ⟨by simpa only [sub_eq_add_neg] using hxy,
      (congrArg Prod.snd he).symm⟩
  have hp : (s, t) = (u, v) := hstz.trans huvz.symm
  exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩

/-- The finite-field diagonal is a Sidon set in the corpus's representation-count sense. -/
theorem diagonalSet_sidon (y : Multiplicative F × Fˣ)
    (hy : 2 ≤ rep (diagonalSet L) (diagonalSet L)⁻¹ y) : y = 1 := by
  classical
  by_contra hy1
  rw [rep] at hy
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hy
  obtain ⟨haP, hay⟩ := Finset.mem_filter.mp ha
  obtain ⟨ha1, ha2⟩ := Finset.mem_product.mp haP
  obtain ⟨hbP, hby⟩ := Finset.mem_filter.mp hb
  obtain ⟨hb1, hb2⟩ := Finset.mem_product.mp hbP
  obtain ⟨s, _, hs⟩ := Finset.mem_image.mp ha1
  obtain ⟨t, _, ht⟩ := Finset.mem_image.mp (Finset.mem_inv'.mp ha2)
  obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hb1
  obtain ⟨v, _, hv⟩ := Finset.mem_image.mp (Finset.mem_inv'.mp hb2)
  have hat : a.2 = (diagonalPoint L t)⁻¹ := by rw [ht, inv_inv]
  have hbv : b.2 = (diagonalPoint L v)⁻¹ := by rw [hv, inv_inv]
  have hst : s ≠ t := by
    intro h
    apply hy1
    rw [← hay, ← hs, hat, h, mul_inv_cancel]
  have he : diagonalPoint L s * (diagonalPoint L t)⁻¹ =
      diagonalPoint L u * (diagonalPoint L v)⁻¹ := by
    rw [hs, ← hat, hu, ← hbv, hay, hby]
  obtain ⟨rfl, rfl⟩ := equal_diagonal_differences L hst he
  apply hab
  exact Prod.ext (hs.symm.trans hu) (hat.trans hbv.symm)

/-- Every Sidon subset of the ambient group has at most q−1 elements; the diagonal attains the bound. -/
theorem sidon_card_le_diagonal (B : Finset (Multiplicative F × Fˣ))
    (hB : ∀ y, 2 ≤ rep B B⁻¹ y → y = 1) : B.card ≤ (diagonalSet L).card := by
  have hb := sidon_card_bound B hB
  have hq : 1 ≤ Fintype.card F := Fintype.card_pos
  rw [Fintype.card_prod, Fintype.card_units] at hb
  have hcard : Fintype.card (Multiplicative F) = Fintype.card F :=
    Fintype.card_congr (α := Multiplicative F) (β := F) (Equiv.refl F)
  rw [hcard] at hb
  rw [diagonalSet_card]
  by_contra h
  have hle : Fintype.card F ≤ B.card := by omega
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
  have hmul : d ≤ Fintype.card F * d := by
    simpa only [one_mul] using Nat.mul_le_mul_right d hq
  have he : Fintype.card F - 1 + 1 = Fintype.card F := Nat.sub_add_cancel hq
  have heMul := congrArg (fun n : ℕ => Fintype.card F * n) he
  simp only [Nat.mul_add, Nat.mul_one] at heMul
  rw [hd] at hb
  nlinarith only [hb, heMul, hmul, Nat.zero_le (d ^ 2), Nat.zero_le (Fintype.card F * d)]

#print axioms diagonalSet_sidon
#print axioms sidon_card_le_diagonal
end GaloisForLFunctions.ArithmeticHarmonicAnalysis.Costas
