import GaloisForLFunctions.HTGeometry.AdditiveCombinatorics.PollardGrynkiewicz
import Mathlib.Data.Finset.Sym

/-!
# Products of a Sidon set

A finite subset `B` of a commutative group is a *Sidon set* when every quotient `b₁ b₂⁻¹ ≠ 1`
has a unique representation, i.e. `r_{B, B⁻¹}(y) ≤ 1` for `y ≠ 1`.  For such a set the
multiplication map from unordered pairs of elements of `B` to `B · B` is injective, so
`#(B · B) ≥ binom(#B + 1, 2)`.
-/

open scoped Pointwise
open Finset

namespace GaloisForLFunctions.HTGeometry.AddComb

variable {G : Type*} [CommGroup G] [DecidableEq G]

/-- The multiplication map on unordered pairs. -/
noncomputable def sym2Mul : Sym2 G → G :=
  Sym2.lift ⟨fun a b => a * b, fun a b => mul_comm a b⟩

omit [DecidableEq G] in
@[simp] theorem sym2Mul_mk (a b : G) : sym2Mul (s(a, b)) = a * b := rfl

/-- **A Sidon set has the maximal number of pairwise products.**  If every difference of two
elements of `B` has a unique representation, the multiplication map from unordered pairs of
elements of `B` to `B · B` is injective. -/
theorem card_choose_le_card_mul_self [Fintype G] {B : Finset G}
    (hSidon : ∀ y : G, 2 ≤ rep B B⁻¹ y → y = 1) :
    (B.card + 1).choose 2 ≤ (B * B).card := by
  classical
  rw [← Finset.card_sym2]
  refine Finset.card_le_card_of_injOn sym2Mul ?_ ?_
  · intro z hz
    induction z using Sym2.ind with
    | _ a b =>
      rw [Finset.mem_coe, Finset.mk_mem_sym2_iff] at hz
      exact Finset.mem_coe.2 (Finset.mul_mem_mul hz.1 hz.2)
  · intro z hz w hw hzw
    induction z using Sym2.ind with
    | _ a₁ a₂ =>
    induction w using Sym2.ind with
    | _ b₁ b₂ =>
      rw [Finset.mem_coe, Finset.mk_mem_sym2_iff] at hz hw
      simp only [sym2Mul_mk] at hzw
      by_cases hcase : a₁ = b₂ ∧ a₂ = b₁
      · rw [hcase.1, hcase.2]
        exact Sym2.eq_swap
      · have hy : 2 ≤ rep B B⁻¹ (a₁ * b₁⁻¹) := by
          rw [rep]
          refine Finset.one_lt_card.2 ⟨(a₁, b₁⁻¹), ?_, (b₂, a₂⁻¹), ?_, ?_⟩
          · rw [Finset.mem_filter, Finset.mem_product]
            exact ⟨⟨hz.1, Finset.mem_inv'.2 (by simpa using hw.1)⟩, rfl⟩
          · rw [Finset.mem_filter, Finset.mem_product]
            refine ⟨⟨hw.2, Finset.mem_inv'.2 (by simpa using hz.2)⟩, ?_⟩
            show b₂ * a₂⁻¹ = a₁ * b₁⁻¹
            rw [mul_inv_eq_iff_eq_mul, mul_comm a₁ b₁⁻¹, mul_assoc, hzw, inv_mul_cancel_left]
          · intro hcon
            apply hcase
            have h1 : a₁ = b₂ := congrArg Prod.fst hcon
            have h2 : b₁⁻¹ = a₂⁻¹ := congrArg Prod.snd hcon
            exact ⟨h1, (inv_injective h2).symm⟩
        have := hSidon _ hy
        have ha : a₁ = b₁ := by
          have : a₁ * b₁⁻¹ * b₁ = 1 * b₁ := by rw [this]
          simpa using this
        have hb : a₂ = b₂ := by
          rw [ha] at hzw
          exact mul_left_cancel hzw
        rw [ha, hb]

end GaloisForLFunctions.HTGeometry.AddComb
