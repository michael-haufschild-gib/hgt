import GaloisForLFunctions.RenormalizedBiarithmeticGeometry.TheCellHolonomyDefectCountsChargedCells

/-!
# The Liouville cell defect grows logarithmically

At the Liouville gauge the charged cells of the dyadic cell dilation are the `a` with
`λ(a) = λ(2a + 1)`. Successor sign changes of `λ` produce them:

* **Sign changes give charged cells** (`mem_liouvilleAgreements_of_sign_change`). If
  `λ(u) ≠ λ(u + 1)` then `a = 2u(u + 1)` is charged: `2a + 1 = (2u + 1)²` has `λ = 1`, and
  `λ(a) = λ(2)λ(u)λ(u + 1) = 1`.
* **Every dyadic block changes sign** (`exists_sign_change_dyadic`). `λ(2^{k+1}) = −λ(2^k)`, so `λ`
  changes sign between consecutive integers of `[2^k, 2^{k+1}]`.
* **Logarithmic growth** (`card_liouvilleAgreements_ge`, `hsDefect_liouville_ge_log`). There are at
  least `K + 1` charged cells below `4^{K+2}`, so the covariance defect of the dyadic cell dilation
  at the Liouville gauge is at least `2(K + 1)` on the horizon `[1, 4^{K+2}]`, for every scalar.

So the gauge charge seen by cells is unbounded along the horizon, unconditionally; the linear
growth `N₊ ≫ X` is a binary correlation statement for `λ` along `(+1, ×2)`.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.RenormalizedBiarithmeticGeometry

open BiarithmeticGaugeGeometry

/-- The Liouville sign `λ(n)` as a real character. -/
abbrev lam (n : ℕ) : ℝ := realSignChar PrimeGauge.liouvilleGauge n

theorem lam_hω : IsRealSignGauge PrimeGauge.liouvilleGauge := fun hp => isRealSignGauge_liouville hp

theorem lam_mul (m n : ℕ) : lam (m * n) = lam m * lam n := realSignChar_mul lam_hω m n

theorem lam_two : lam 2 = -1 := realSignChar_liouville_prime Nat.prime_two

theorem lam_sq_eq_one {n : ℕ} (hn : n ≠ 0) : lam n * lam n = 1 := by
  rw [← sq]; exact realSignChar_sq_eq_one lam_hω hn

theorem lam_eq_one_or {n : ℕ} (hn : n ≠ 0) : lam n = 1 ∨ lam n = -1 :=
  realSignChar_eq_one_or lam_hω hn

/-- **Sign changes give charged cells.** -/
theorem mem_liouvilleAgreements_of_sign_change {u X : ℕ} (hu : 1 ≤ u) (hX : 2 * u * (u + 1) ≤ X)
    (hch : lam u ≠ lam (u + 1)) : 2 * u * (u + 1) ∈ liouvilleAgreements X := by
  have hprod : lam u * lam (u + 1) = -1 := by
    rcases lam_eq_one_or (show u ≠ 0 by omega) with h | h <;>
      rcases lam_eq_one_or (show u + 1 ≠ 0 by omega) with h' | h' <;>
        simp_all
  simp only [liouvilleAgreements, mem_filter, mem_Icc]
  refine ⟨⟨by nlinarith, hX⟩, ?_⟩
  have ha : lam (2 * u * (u + 1)) = 1 := by
    rw [lam_mul, lam_mul, lam_two, mul_assoc, hprod]; norm_num
  have hsq : 2 * (2 * u * (u + 1)) + 1 = (2 * u + 1) * (2 * u + 1) := by ring
  have hb : lam (2 * (2 * u * (u + 1)) + 1) = 1 := by
    rw [hsq, lam_mul, lam_sq_eq_one (by omega)]
  change lam (2 * u * (u + 1)) * lam (2 * (2 * u * (u + 1)) + 1) = 1
  rw [ha, hb, one_mul]

/-- A sequence that differs at `A < B` changes between consecutive points of `[A, B]`. -/
theorem exists_consecutive_ne {f : ℕ → ℝ} {A B : ℕ} (hAB : A ≤ B) (h : f A ≠ f B) :
    ∃ u, A ≤ u ∧ u < B ∧ f u ≠ f (u + 1) := by
  induction B, hAB using Nat.le_induction with
  | base => exact absurd rfl h
  | succ B hAB ih =>
    by_cases hB : f A = f B
    · exact ⟨B, hAB, Nat.lt_succ_self B, fun h' => h (hB.trans h')⟩
    · obtain ⟨u, h1, h2, h3⟩ := ih hB
      exact ⟨u, h1, by omega, h3⟩

/-- **Every dyadic block changes sign.** -/
theorem exists_sign_change_dyadic (k : ℕ) :
    ∃ u, 2 ^ k ≤ u ∧ u < 2 ^ (k + 1) ∧ lam u ≠ lam (u + 1) := by
  refine exists_consecutive_ne (by gcongr <;> omega) ?_
  rw [pow_succ, mul_comm, lam_mul, lam_two]
  have h := lam_eq_one_or (show 2 ^ k ≠ 0 by positivity)
  rcases h with h | h <;> rw [h] <;> norm_num

/-- **At least `K + 1` charged cells below `4^{K+2}`.** -/
theorem card_liouvilleAgreements_ge (K : ℕ) : K + 1 ≤ (liouvilleAgreements (4 ^ (K + 2))).card := by
  choose u hu1 hu2 hu3 using exists_sign_change_dyadic
  -- The cells `2u_k(u_k + 1)`, `k ≤ K`, are distinct charged cells below `4^{K+2}`.
  have hmaps : ∀ k ∈ range (K + 1), 2 * u k * (u k + 1) ∈ liouvilleAgreements (4 ^ (K + 2)) := by
    intro k hk
    have hk' : k ≤ K := Nat.lt_succ_iff.mp (mem_range.mp hk)
    refine mem_liouvilleAgreements_of_sign_change (le_trans Nat.one_le_two_pow (hu1 k)) ?_ (hu3 k)
    have h1 : u k + 1 ≤ 2 ^ (K + 1) := by
      have := hu2 k
      have : 2 ^ (k + 1) ≤ 2 ^ (K + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have h2 : 4 ^ (K + 2) = 2 * (2 ^ (K + 1) * 2 ^ (K + 1)) * 2 := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]; ring_nf
    rw [h2]
    have h3 : u k ≤ 2 ^ (K + 1) := by omega
    calc 2 * u k * (u k + 1) ≤ 2 * 2 ^ (K + 1) * 2 ^ (K + 1) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 2 h3) h1
      _ ≤ 2 * (2 ^ (K + 1) * 2 ^ (K + 1)) * 2 := by nlinarith
  have hinj : Set.InjOn (fun k => 2 * u k * (u k + 1)) (range (K + 1) : Set ℕ) := by
    intro i _ j _ hij
    -- `u ↦ 2u(u + 1)` is injective, and `u_k` lies in the `k`-th dyadic block.
    have hu : u i = u j := by
      simp only at hij
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · have : 2 * u i * (u i + 1) < 2 * u j * (u j + 1) := by
          have := Nat.mul_lt_mul'' (Nat.mul_lt_mul_of_pos_left h (by norm_num : 0 < 2))
            (Nat.succ_lt_succ h)
          linarith
        omega
      · have : 2 * u j * (u j + 1) < 2 * u i * (u i + 1) := by
          have := Nat.mul_lt_mul'' (Nat.mul_lt_mul_of_pos_left h (by norm_num : 0 < 2))
            (Nat.succ_lt_succ h)
          linarith
        omega
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have : 2 ^ (i + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) h
      have := hu2 i; have := hu1 j; omega
    · have : 2 ^ (j + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) h
      have := hu2 j; have := hu1 i; omega
  calc K + 1 = ((range (K + 1)).image fun k => 2 * u k * (u k + 1)).card := by
        rw [card_image_of_injOn hinj, card_range]
    _ ≤ (liouvilleAgreements (4 ^ (K + 2))).card :=
        card_le_card fun a ha => by
          obtain ⟨k, hk, rfl⟩ := mem_image.mp ha
          exact hmaps k hk

/-- **The Liouville cell defect grows logarithmically**: on the horizon `[1, 4^{K+2}]` the covariance
defect of the dyadic cell dilation at the Liouville gauge is at least `2(K + 1)` for every scalar. -/
theorem hsDefect_liouville_ge_log (K : ℕ) (c : ℝ) :
    2 * ((K : ℝ) + 1) ≤ hsDefect PrimeGauge.liouvilleGauge (4 ^ (K + 2)) c := by
  have h := (hsDefect_liouville_sandwich (4 ^ (K + 2))).1 c
  have hK : ((K : ℝ) + 1) ≤ (liouvilleAgreements (4 ^ (K + 2))).card := by
    exact_mod_cast card_liouvilleAgreements_ge K
  linarith

end GaloisForLFunctions.RenormalizedBiarithmeticGeometry
