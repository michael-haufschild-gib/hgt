import GaloisForLFunctions.RHTower.Sieve.LargeSieveWeak
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# The sharp case: frequencies at the roots of unity

At the full set of `Q`-th roots of unity the exponential rows of length `Q` are exactly orthogonal.
Their correlation is a full geometric sum whose ratio is a `Q`-th root of unity, so it vanishes off
the diagonal by `(ζ^Q - 1)/(ζ - 1) = 0`, and equals `Q` on it.

Consequently the Gram rows are exactly `Q`, and the large sieve holds with `Δ = Q` — the sharp
constant `N + δ^{-1}` at `N = Q` and separation `δ = 1/Q`, with no logarithmic loss.  This is the
one configuration where the elementary route already gives the optimal answer, and it is a check on
the whole chain: `LargeSieveWeak.lean` specialises here to an equality-sharp inequality.
-/

namespace RHTower.Sieve

open Finset
open scoped InnerProductSpace

/-- A root of unity is unimodular. -/
theorem norm_eq_one_of_isPrimitiveRoot {ζ : ℂ} {Q : ℕ} (hQ : 0 < Q) (hζ : IsPrimitiveRoot ζ Q) :
    ‖ζ‖ = 1 := by
  have hpow : ‖ζ‖ ^ Q = 1 := by
    rw [← norm_pow, hζ.pow_eq_one, norm_one]
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have := pow_lt_one₀ (norm_nonneg ζ) hlt (by omega : Q ≠ 0)
    linarith [hpow]
  · have := one_lt_pow₀ hgt (by omega : Q ≠ 0)
    linarith [hpow]

/-- Powers of a root of unity are unimodular. -/
theorem norm_pow_eq_one_of_isPrimitiveRoot {ζ : ℂ} {Q : ℕ} (hQ : 0 < Q)
    (hζ : IsPrimitiveRoot ζ Q) (j : ℕ) : ‖ζ ^ j‖ = 1 := by
  rw [norm_pow, norm_eq_one_of_isPrimitiveRoot hQ hζ, one_pow]

/-- A full geometric sum over a nontrivial root of unity vanishes. -/
theorem sum_range_pow_eq_zero {ζ : ℂ} {Q : ℕ} (hpow : ζ ^ Q = 1) (hne : ζ ≠ 1) :
    ∑ n ∈ Finset.range Q, ζ ^ n = 0 := by
  rw [geom_sum_eq hne, hpow, sub_self, zero_div]

/-- Distinct powers of a primitive root give a nontrivial ratio. -/
theorem ratio_ne_one {ζ : ℂ} {Q : ℕ} (hQ : 0 < Q) (hζ : IsPrimitiveRoot ζ Q)
    {j k : ℕ} (hj : j < Q) (hk : k < Q) (hjk : j ≠ k) :
    (starRingEnd ℂ) (ζ ^ j) * ζ ^ k ≠ 1 := by
  intro hcon
  have hζ0 : ζ ^ j ≠ 0 := by
    intro h
    have := norm_pow_eq_one_of_isPrimitiveRoot hQ hζ j
    rw [h, norm_zero] at this
    norm_num at this
  have hconj : (starRingEnd ℂ) (ζ ^ j) * ζ ^ j = 1 := by
    rw [conj_mul_self, norm_pow_eq_one_of_isPrimitiveRoot hQ hζ j]
    norm_num
  have heq : ζ ^ k = ζ ^ j := by
    calc ζ ^ k = ((starRingEnd ℂ) (ζ ^ j) * ζ ^ j) * ζ ^ k := by rw [hconj, one_mul]
      _ = ζ ^ j * ((starRingEnd ℂ) (ζ ^ j) * ζ ^ k) := by ring
      _ = ζ ^ j := by rw [hcon, mul_one]
  exact hjk (hζ.pow_inj hj hk heq.symm)

/-- **Exact orthogonality.**  Off the diagonal the Gram entry vanishes. -/
theorem inner_expRow_root_eq_zero {ζ : ℂ} {Q : ℕ} (hQ : 0 < Q) (hζ : IsPrimitiveRoot ζ Q)
    {j k : ℕ} (hj : j < Q) (hk : k < Q) (hjk : j ≠ k) :
    ⟪expRow Q (ζ ^ j), expRow Q (ζ ^ k)⟫_ℂ = 0 := by
  rw [inner_expRow, sum_conj_pow_mul_pow]
  refine sum_range_pow_eq_zero ?_ (ratio_ne_one hQ hζ hj hk hjk)
  rw [mul_pow, ← map_pow, ← pow_mul, ← pow_mul, mul_comm j Q, mul_comm k Q, pow_mul, pow_mul,
    hζ.pow_eq_one, one_pow, one_pow, map_one, one_mul]

/-- **Exact diagonal.**  The Gram entry on the diagonal is the length. -/
theorem inner_expRow_root_self {ζ : ℂ} {Q : ℕ} (hQ : 0 < Q) (hζ : IsPrimitiveRoot ζ Q) (j : ℕ) :
    ⟪expRow Q (ζ ^ j), expRow Q (ζ ^ j)⟫_ℂ = (Q : ℂ) := by
  rw [inner_expRow]
  exact sum_conj_pow_mul_pow_self (norm_pow_eq_one_of_isPrimitiveRoot hQ hζ j) Q

/-- **Sharp large sieve at the roots of unity.**  The Gram rows are exactly `Q`. -/
theorem gram_row_root_eq {ζ : ℂ} {Q : ℕ} (hQ : 0 < Q) (hζ : IsPrimitiveRoot ζ Q)
    {j : ℕ} (hj : j ∈ Finset.range Q) :
    ∑ k ∈ Finset.range Q, ‖⟪expRow Q (ζ ^ j), expRow Q (ζ ^ k)⟫_ℂ‖ = (Q : ℝ) := by
  classical
  have hjQ : j < Q := Finset.mem_range.1 hj
  have hsplit : ∑ k ∈ Finset.range Q, ‖⟪expRow Q (ζ ^ j), expRow Q (ζ ^ k)⟫_ℂ‖
      = ‖⟪expRow Q (ζ ^ j), expRow Q (ζ ^ j)⟫_ℂ‖
        + ∑ k ∈ (Finset.range Q).erase j, ‖⟪expRow Q (ζ ^ j), expRow Q (ζ ^ k)⟫_ℂ‖ :=
    (Finset.add_sum_erase (Finset.range Q)
      (fun k => ‖⟪expRow Q (ζ ^ j), expRow Q (ζ ^ k)⟫_ℂ‖) hj).symm
  have hoff : ∑ k ∈ (Finset.range Q).erase j, ‖⟪expRow Q (ζ ^ j), expRow Q (ζ ^ k)⟫_ℂ‖ = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    obtain ⟨hkj, hkQ⟩ := Finset.mem_erase.1 hk
    rw [inner_expRow_root_eq_zero hQ hζ hjQ (Finset.mem_range.1 hkQ) fun hcon => hkj hcon.symm,
      norm_zero]
  rw [hsplit, hoff, add_zero, inner_expRow_root_self hQ hζ j]
  simp

/-- **The large sieve is sharp at the roots of unity.** -/
theorem largeSieve_roots {ζ : ℂ} {Q : ℕ} (hQ : 0 < Q) (hζ : IsPrimitiveRoot ζ Q) (c : ℕ → ℂ) :
    ‖∑ j ∈ Finset.range Q, c j • expRow Q (ζ ^ j)‖ ^ (2 : ℕ)
      ≤ (Q : ℝ) * ∑ j ∈ Finset.range Q, ‖c j‖ ^ (2 : ℕ) :=
  norm_sum_smul_sq_le_of_schur (Finset.range Q) (fun j => expRow Q (ζ ^ j))
    (fun _ hj => le_of_eq (gram_row_root_eq hQ hζ hj)) c

end RHTower.Sieve
