import GaloisForLFunctions.WindowedLandauTheory.CyclotomicNorms.SquarefreeFrobeniusCycles
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TeichmullerReduction

/-! Injectivity on prime-to-residue-characteristic torsion transfers root
exclusions to the residual inertia polynomial and its inverse convention. -/

noncomputable section

open Polynomial
open WindowedLandauTheory.CyclotomicNorms.CycleTypeFiniteOrder

namespace WindowedLandauTheory.CyclotomicNorms

/-- A nonzero element of the algebraic closure of a prime field has finite order. -/
theorem fbar_isOfFinOrder {g : ℕ} [Fact g.Prime] {x : Fbar g} (hx : x ≠ 0) :
    IsOfFinOrder x := by
  obtain ⟨n, hn, -, hpow⟩ := GlobalTheory.TeichPlace.fbar_exists_coprime_pow_eq_one hx
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, hpow⟩

/-- Equality of residual images of prime-to-characteristic parts determines
the prime-to-characteristic parts themselves. -/
theorem primeToPart_eq_of_map_eq {g ℓ : ℕ} [Fact g.Prime] [Fact ℓ.Prime]
    (ι : Fbar g →* Fbar ℓ)
    (hι : ∀ x y, x ≠ 0 → y ≠ 0 → (orderOf x).Coprime ℓ → (orderOf y).Coprime ℓ →
      ι x = ι y → x = y)
    {x y : Fbar g} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : ι (primeToPart ℓ x) = ι (primeToPart ℓ y)) :
    primeToPart ℓ x = primeToPart ℓ y :=
  hι _ _ (pow_ne_zero _ hx) (pow_ne_zero _ hy)
    (primeToPart_coprime Fact.out _ (fbar_isOfFinOrder hx))
    (primeToPart_coprime Fact.out _ (fbar_isOfFinOrder hy)) h

private theorem primeToPart_inv {K : Type*} [Field K] (ℓ : ℕ) {x : K} (hx : x ≠ 0) :
    primeToPart ℓ x⁻¹ = (primeToPart ℓ x)⁻¹ := by
  let u := Units.mk0 x hx
  change primeToPart ℓ (↑u : K)⁻¹ = (primeToPart ℓ (↑u : K))⁻¹
  have ho : orderOf (↑u : K)⁻¹ = orderOf (↑u : K) := by
    rw [← Units.val_inv_eq_inv_val, orderOf_units, orderOf_inv, orderOf_units]
  unfold primeToPart
  rw [ho, inv_pow]

private theorem eq_of_root_product {K A : Type*} [Field K] (S : Multiset A) (f : A → K) {y : K}
    (h : ((S.map fun x => X - C (f x)).prod).IsRoot y) :
    ∃ x ∈ S, f x = y := by
  rw [IsRoot, eval_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.map_map] at h
  obtain ⟨x, hx, he⟩ := Multiset.mem_map.mp h
  refine ⟨x, hx, ?_⟩
  simp only [Function.comp_apply, eval_sub, eval_X, eval_C] at he
  exact (sub_eq_zero.mp he).symm

/-- Excluding a character value and its inverse among the prime-to-characteristic
parts excludes all combinations of the two inertia orientations. -/
theorem not_isRoot_of_signed_labels {g ℓ N : ℕ} [Fact g.Prime] [Fact ℓ.Prime]
    {f : (ZMod g)[X]} (hf : GoodPoly N f) (ι : Fbar g →* Fbar ℓ)
    (hι : ∀ x y, x ≠ 0 → y ≠ 0 → (orderOf x).Coprime ℓ → (orderOf y).Coprime ℓ →
      ι x = ι y → x = y)
    {c : Fbar g} (hc : c ≠ 0)
    (hex : ∀ x ∈ rootsBar f, primeToPart ℓ x ≠ primeToPart ℓ c)
    (hexi : ∀ x ∈ rootsBar f, primeToPart ℓ x ≠ primeToPart ℓ c⁻¹)
    {e₁ e₂ : ℤ} (he₁ : e₁ = 1 ∨ e₁ = -1) (he₂ : e₂ = 1 ∨ e₂ = -1) :
    ¬ (((rootsBar f).map fun x => X - C (ι (primeToPart ℓ x) ^ e₁)).prod).IsRoot
      (ι (primeToPart ℓ c) ^ e₂) := by
  intro hroot
  obtain ⟨x, hx, h⟩ := eq_of_root_product (rootsBar f) (fun x => ι (primeToPart ℓ x) ^ e₁) hroot
  have hx₀ := ne_zero_of_mem hf hx
  have hc₀ : primeToPart ℓ c ≠ 0 := pow_ne_zero _ hc
  have hinv : ι (primeToPart ℓ c⁻¹) = (ι (primeToPart ℓ c))⁻¹ := by
    rw [primeToPart_inv ℓ hc]
    exact eq_inv_of_mul_eq_one_right (by rw [← map_mul, mul_inv_cancel₀ hc₀, map_one])
  have hsame : ι (primeToPart ℓ x) ≠ ι (primeToPart ℓ c) :=
    fun he => hex x hx (primeToPart_eq_of_map_eq ι hι hx₀ hc he)
  have hflip : ι (primeToPart ℓ x) ≠ (ι (primeToPart ℓ c))⁻¹ := by
    rw [← hinv]
    exact fun he => hexi x hx (primeToPart_eq_of_map_eq ι hι hx₀ (inv_ne_zero hc) he)
  rcases he₁ with rfl | rfl <;> rcases he₂ with rfl | rfl
  · exact hsame (by simpa only [zpow_one] using h)
  · exact hflip (by simpa only [zpow_one, _root_.zpow_neg] using h)
  · apply hflip
    simp only [zpow_one, _root_.zpow_neg] at h
    rw [← h, inv_inv]
  · exact hsame (by simpa only [zpow_one, _root_.zpow_neg, _root_.inv_inj] using h)

end WindowedLandauTheory.CyclotomicNorms
