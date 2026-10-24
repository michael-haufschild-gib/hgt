import GaloisForLFunctions.BiarithmeticGeometry.HorizonAffineActions
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Signed boundary loss at a finite horizon

Positive affine maps inject the surviving cells and absorb the others. Their bilinear defect is
exactly the signed pairing on escaped cells. Squaring gives contraction with an explicit loss.
An observable invariant under the absorbing successor is constant, since enough successors
erase every cell. Boundary terms are therefore essential even before arithmetic estimates.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.BiarithmeticGeometry

/-- The signed cell pairing, with no periodic completion. -/
def horizonPairing (N : ℕ) (v w : HorizonSpace N) : ℝ := ∑ i, v i * w i

/-- An affine pushforward reads the original coefficient at every surviving image cell. -/
theorem horizonAffine_apply_image (N : ℕ) (a : ℕ+) (b : ℕ) (v : HorizonSpace N)
    (j : Fin (N + 1)) (hj : (a : ℕ) * j.val + b ≤ N) :
    horizonAffine N a b v ⟨a * j.val + b, by omega⟩ = v j := by
  classical
  rw [horizonAffine_apply, sum_eq_single j]
  · simp only [if_true, mul_one]
  · intro k _ hkj
    rw [if_neg, mul_zero]
    intro he
    apply hkj
    apply Fin.ext
    exact (Nat.eq_of_mul_eq_mul_left a.pos (Nat.add_right_cancel he)).symm
  · exact fun h => False.elim (h (mem_univ j))

/-- An affine map preserves each surviving signed pairing coefficient exactly once. -/
theorem horizonPairing_affine (N : ℕ) (a : ℕ+) (b : ℕ) (v w : HorizonSpace N) :
    horizonPairing N (horizonAffine N a b v) (horizonAffine N a b w) =
      ∑ j : Fin (N + 1), if (a : ℕ) * j.val + b ≤ N then v j * w j else 0 := by
  classical
  unfold horizonPairing
  calc
    _ = ∑ i : Fin (N + 1), ∑ j : Fin (N + 1),
        (v j * (if i.val = (a : ℕ) * j.val + b then 1 else 0)) *
          horizonAffine N a b w i := by
      apply sum_congr rfl
      intro i _
      rw [horizonAffine_apply, sum_mul]
    _ = ∑ j : Fin (N + 1), ∑ i : Fin (N + 1),
        (v j * (if i.val = (a : ℕ) * j.val + b then 1 else 0)) *
          horizonAffine N a b w i := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro j _
      by_cases hj : (a : ℕ) * j.val + b ≤ N
      · rw [if_pos hj, sum_eq_single ⟨a * j.val + b, by omega⟩]
        · simp only [if_true, mul_one, horizonAffine_apply_image]
        · intro i _ hi
          rw [if_neg, mul_zero, zero_mul]
          exact fun h => hi (Fin.ext h)
        · exact fun h => False.elim (h (mem_univ _))
      · rw [if_neg hj]
        apply sum_eq_zero
        intro i _
        rw [if_neg, mul_zero, zero_mul]
        exact fun h => hj (by omega)

/-- The exact signed affine defect is the pairing carried out through the boundary. -/
theorem horizonPairing_affine_add_boundary (N : ℕ) (a : ℕ+) (b : ℕ)
    (v w : HorizonSpace N) :
    horizonPairing N (horizonAffine N a b v) (horizonAffine N a b w) +
      (∑ j : Fin (N + 1), if N < (a : ℕ) * j.val + b then v j * w j else 0) =
        horizonPairing N v w := by
  rw [horizonPairing_affine, ← sum_add_distrib]
  apply sum_congr rfl
  intro j _
  by_cases hj : (a : ℕ) * j.val + b ≤ N
  · simp only [if_pos hj, if_neg (not_lt.mpr hj), add_zero]
  · simp only [if_neg hj, if_pos (lt_of_not_ge hj), zero_add]

/-- Cell energy contracts, with no loss except the explicitly escaped tail. -/
theorem horizonPairing_affine_self_le (N : ℕ) (a : ℕ+) (b : ℕ)
    (v : HorizonSpace N) :
    horizonPairing N (horizonAffine N a b v) (horizonAffine N a b v) ≤
      horizonPairing N v v := by
  have h := horizonPairing_affine_add_boundary N a b v v
  have hboundary : 0 ≤ ∑ j : Fin (N + 1),
      if N < (a : ℕ) * j.val + b then v j * v j else 0 :=
    sum_nonneg fun j _ => by split_ifs <;> positivity
  linarith only [h, hboundary]

theorem horizonAffine_eq_zero_of_large_translation (N : ℕ) (a : ℕ+) (b : ℕ)
    (hb : N < b) : horizonAffine N a b = 0 := by
  apply LinearMap.ext
  intro v
  funext i
  rw [horizonAffine_apply]
  apply sum_eq_zero
  intro j _
  rw [if_neg, mul_zero]
  exact fun h => by omega

/-- Positive affine transport preserves every tail, despite its scalar common commutant. -/
theorem horizonAffine_preserves_tail (N : ℕ) (a : ℕ+) (b k : ℕ) (v : HorizonSpace N) :
    (∀ j : Fin (N + 1), j.val < k → v j = 0) →
      ∀ i : Fin (N + 1), i.val < k → horizonAffine N a b v i = 0 := by
  intro hv i hi
  rw [horizonAffine_apply]
  apply sum_eq_zero
  intro j _
  by_cases hij : i.val = (a : ℕ) * j.val + b
  · rw [if_pos hij, mul_one]
    apply hv
    have hj := Nat.le_mul_of_pos_left j.val a.pos
    omega
  · rw [if_neg hij, mul_zero]

/-- Absorbing-successor invariance characterizes constant observables, for any target type. -/
theorem horizon_successor_invariant_iff (N : ℕ) {α : Type*} (F : HorizonSpace N → α) :
    (∀ v, F (horizonAffine N 1 1 v) = F v) ↔ ∀ v, F v = F 0 := by
  constructor
  · intro h v
    have hshift : ∀ b : ℕ, F (horizonAffine N 1 b v) = F v := by
      intro b
      induction b with
      | zero => rw [horizonAffine_one_zero, LinearMap.id_apply]
      | succ b ih =>
        have he : horizonAffine N 1 (b + 1) v =
            horizonAffine N 1 1 (horizonAffine N 1 b v) := by
          have hc := congrArg (fun L : HorizonSpace N →ₗ[ℝ] HorizonSpace N => L v)
            (horizonAffine_comp N 1 1 1 b)
          simpa only [LinearMap.comp_apply, one_mul, PNat.val_ofNat] using hc.symm
        rw [he, h, ih]
    have hz := hshift (N + 1)
    rw [horizonAffine_eq_zero_of_large_translation N 1 (N + 1) (by omega),
      LinearMap.zero_apply] at hz
    exact hz.symm
  · intro h v
    exact (h _).trans (h v).symm

end GaloisForLFunctions.BiarithmeticGeometry
