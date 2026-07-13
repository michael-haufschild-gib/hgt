import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaLogKernel
import Mathlib.Data.Fintype.Option

/-!
# Summability of finite products of nonnegative series

A finite family of nonnegative summable sequences has a summable product family on the finite
Cartesian power.  This is the all-order geometric-majorant lemma for multiple elliptic gamma.
-/

open scoped BigOperators

namespace GaloisForLFunctions

set_option maxHeartbeats 800000 in
/-- Finite products of nonnegative summable sequences are summable over the corresponding
function space. -/
theorem summable_fintype_pi_product_of_nonneg
    (ι : Type) [Fintype ι]
    (w : ι → ℕ → ℝ)
    (hs : ∀ i, Summable (w i))
    (hn : ∀ i n, 0 ≤ w i n) :
    Summable (fun a : ι → ℕ => ∏ i, w i (a i)) := by
  classical
  let P : ∀ (α : Type) [Fintype α], Prop := fun α _ =>
    ∀ (w : α → ℕ → ℝ),
      (∀ i, Summable (w i)) →
      (∀ i n, 0 ≤ w i n) →
      Summable (fun a : α → ℕ => ∏ i, w i (a i))
  apply Fintype.induction_empty_option (P := P)
  · intro α β _ e h w hs hn
    letI : Fintype α := Fintype.ofEquiv β e.symm
    let W : α → ℕ → ℝ := fun i => w (e i)
    have hW := h W (fun i => hs (e i)) (fun i => hn (e i))
    let he : (α → ℕ) ≃ (β → ℕ) :=
      { toFun := fun a j => a (e.symm j)
        invFun := fun b i => b (e i)
        left_inv := by intro a; funext i; simp
        right_inv := by intro b; funext j; simp }
    apply (he.summable_iff).1
    convert hW using 1
    funext a
    change (∏ j : β, w j (a (e.symm j))) = ∏ i : α, w (e i) (a i)
    simpa using
      (Fintype.prod_equiv e
        (fun i : α => w (e i) (a i))
        (fun j : β => w j (a (e.symm j))) (by intro i; simp)).symm
  · intro w hs hn
    exact Summable.of_finite
  · intro α _ h w hs hn
    let rest : α → ℕ → ℝ := fun i => w (some i)
    have hrest : Summable (fun a : α → ℕ => ∏ i, rest i (a i)) :=
      h rest (fun i => hs (some i)) (fun i => hn (some i))
    have hprod : Summable (fun ka : ℕ × (α → ℕ) =>
        w none ka.1 * ∏ i, rest i (ka.2 i)) :=
      (hs none).mul_of_nonneg hrest (hn none)
        (fun a => Finset.prod_nonneg fun i _ => hn (some i) (a i))
    let e : (Option α → ℕ) ≃ ℕ × (α → ℕ) := Equiv.piOptionEquivProd
    have heSum := (e.summable_iff).2 hprod
    convert heSum using 1
    funext a
    rw [Fintype.prod_option]
    rfl
  · exact hs
  · exact hn

end GaloisForLFunctions
