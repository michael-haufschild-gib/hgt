import GaloisForLFunctions.RigidArithmeticOfCuts.TheFakePrimeMeasureIsUnique

/-!
# The finite-level radius

How far from the pronic measure can a fake of level `K` be? Translation empties any window, so a radius needs a condition at infinity.
With one, the sieve behind uniqueness runs at finite level.

Let `W = 1/r − T` be the deviation of the tail from `1/r`, and suppose `W` is summable, with sum `S`. The moments up to level `K` give `k W(kℕ) = S` for
`k ≤ K`. Inclusion–exclusion over the primes `p < X` needs only `k ≤ n ∏_{p<X} p ≤ n 4^X`, and it leaves the multiples `n t` with `t = 1` or `t ≥ X`:

`|W(n)| ≤ (|S|/n) ∏_{p<X} (1 − 1/p) + Σ_{t ≥ X} |W(n t)|`, for `n 4^X ≤ K` (`abs_cutDeviation_le_of_level`).

By Mertens the product is `≍ 1/log X`, and the condition allows `X ≍ log(K/n)`. So a fake of level `K` under a uniform condition
at infinity is within `≍ 1/log log K` of the pronic measure, plus the tail of that condition.
-/

open Finset Filter Topology
open GaloisForLFunctions.ArithmeticAuxiliaryDynamics

noncomputable section

namespace GaloisForLFunctions.RigidArithmeticOfCuts

variable {W : ℕ → ℝ}

/-- The Euler product of the primes in `P`, for the sieve at finite level. -/
theorem mul_tsum_primePart_of_level {K : ℕ} (hW : Summable W) (hW0 : W 0 = 0) {S : ℝ}
    (hmul : ∀ k : ℕ, 1 ≤ k → k ≤ K → (k : ℝ) * ∑' t, W (k * t) = S) (P : Finset ℕ)
    (hPr : ∀ q ∈ P, q.Prime) :
    ∀ n : ℕ, 1 ≤ n → n * ∏ p ∈ P, p ≤ K →
      (n : ℝ) * ∑' t, primePart W n P t = S * ∏ p ∈ P, (1 - ((p : ℝ))⁻¹) := by
  induction P using Finset.induction_on with
  | empty =>
    intro n hn hsize
    rw [prod_empty, mul_one, ← hmul n hn (by simpa using hsize)]
    congr 1
    refine tsum_congr fun t => ?_
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp [primePart, hW0]
    · simp [primePart, ht]
  | insert p P hpP ih =>
    intro n hn hsize
    have hp : p.Prime := hPr p (mem_insert_self p P)
    have hPr' : ∀ q ∈ P, q.Prime := fun q hq => hPr q (mem_insert_of_mem hq)
    have hpR : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [prod_insert hpP] at hsize
    have hle : n * ∏ q ∈ P, q ≤ K := by
      refine le_trans ?_ hsize
      rw [mul_left_comm]
      exact Nat.le_mul_of_pos_left _ hp.pos
    have hle2 : n * p * ∏ q ∈ P, q ≤ K := by
      rwa [mul_assoc]
    have h1 := ih hPr' n hn hle
    have h2 := ih hPr' (n * p) (Nat.mul_pos hn hp.pos) hle2
    rw [tsum_primePart_insert hW hn hp hpP hPr', prod_insert hpP]
    push_cast at h2
    have h3 : (n : ℝ) * ∑' t, primePart W (n * p) P t =
        (S * ∏ q ∈ P, (1 - ((q : ℝ))⁻¹)) / p := by
      rw [eq_div_iff hpR, ← h2]
      ring
    rw [mul_sub, h1, h3]
    field_simp

/-- The product of the primes below `X` is at most `4^X`. -/
theorem prod_primesBelow_le (X : ℕ) : ∏ p ∈ X.primesBelow, p ≤ 4 ^ X := by
  rcases Nat.eq_zero_or_pos X with rfl | hX
  · simp
  · have h := primorial_le_four_pow (X - 1)
    have heq : ∏ p ∈ X.primesBelow, p = primorial (X - 1) := by
      rw [primorial, Nat.primesBelow]
      congr 1
      congr 1
      rw [Nat.sub_add_cancel hX]
    rw [heq]
    exact h.trans (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- **The radius at finite level.** A summable `W` with `k W(kℕ) = S` for `k ≤ K` is bounded at `n`, for `n 4^X ≤ K`, by the sieve term and
its tail. -/
theorem abs_le_of_uniform_multiples_level {K : ℕ} (hW : Summable W) (hW0 : W 0 = 0) {S : ℝ}
    (hmul : ∀ k : ℕ, 1 ≤ k → k ≤ K → (k : ℝ) * ∑' t, W (k * t) = S) {n X : ℕ} (hn : 1 ≤ n) (hX : 2 ≤ X)
    (hsize : n * 4 ^ X ≤ K) :
    |W n| ≤ |S| * (∏ p ∈ X.primesBelow, (1 - ((p : ℝ))⁻¹)) / n + ∑' t, ‖W (n * (t + X))‖ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hprod : n * ∏ p ∈ X.primesBelow, p ≤ K :=
    (Nat.mul_le_mul_left n (prod_primesBelow_le X)).trans hsize
  have hPr : ∀ q ∈ X.primesBelow, q.Prime := fun q hq => (Nat.mem_primesBelow.mp hq).2
  have hmain := mul_tsum_primePart_of_level hW hW0 hmul X.primesBelow hPr n hn hprod
  have hsm := summable_primePart hW hn X.primesBelow
  have hsW := summable_mul_left hW hn
  -- The part at `t < X` is the single term `W n`.
  have hlow : ∀ t < X, primePart W n X.primesBelow t = if t = 1 then W n else 0 := by
    intro t ht
    unfold primePart
    by_cases ht1 : t = 1
    · subst ht1
      rw [if_pos rfl, if_pos, mul_one]
      refine ⟨one_pos, fun p hp hd => ?_⟩
      exact (Nat.mem_primesBelow.mp hp).2.one_lt.ne' (Nat.dvd_one.mp hd)
    · rw [if_neg ht1, if_neg]
      rintro ⟨ht0, hall⟩
      have hprime := Nat.minFac_prime ht1
      have hmem : t.minFac ∈ X.primesBelow :=
        Nat.mem_primesBelow.mpr ⟨(Nat.minFac_le ht0).trans_lt ht, hprime⟩
      exact hall _ hmem (Nat.minFac_dvd t)
  have hsplit := hsm.sum_add_tsum_nat_add X
  have hhead : ∑ t ∈ range X, primePart W n X.primesBelow t = W n := by
    rw [sum_congr rfl fun t ht => hlow t (mem_range.mp ht), sum_ite_eq' (range X) 1]
    rw [if_pos (mem_range.mpr (by omega))]
  have htail : |∑' t, primePart W n X.primesBelow (t + X)| ≤ ∑' t, ‖W (n * (t + X))‖ := by
    have hbd : ∀ t, ‖primePart W n X.primesBelow (t + X)‖ ≤ ‖W (n * (t + X))‖ := fun t =>
      abs_primePart_le W n _ _
    have hsumm : Summable fun t => ‖W (n * (t + X))‖ := (summable_nat_add_iff X).mpr hsW.norm
    have hs2 : Summable fun t => ‖primePart W n X.primesBelow (t + X)‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbd hsumm
    rw [← Real.norm_eq_abs]
    exact (norm_tsum_le_tsum_norm hs2).trans (Summable.tsum_le_tsum hbd hs2 hsumm)
  have hval : ∑' t, primePart W n X.primesBelow t =
      S * (∏ p ∈ X.primesBelow, (1 - ((p : ℝ))⁻¹)) / n := by
    rw [eq_div_iff hnR.ne', mul_comm]
    exact hmain
  have hprodnn : 0 ≤ ∏ p ∈ X.primesBelow, (1 - ((p : ℝ))⁻¹) := by
    refine prod_nonneg fun p hp => ?_
    have hp' := (Nat.mem_primesBelow.mp hp).2
    have h1 : ((p : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hp'.one_lt.le)
    linarith
  have hWn : W n = S * (∏ p ∈ X.primesBelow, (1 - ((p : ℝ))⁻¹)) / n -
      ∑' t, primePart W n X.primesBelow (t + X) := by
    rw [← hval, ← hsplit, hhead]
    ring
  rw [hWn]
  refine (abs_sub _ _).trans (add_le_add ?_ htail)
  rw [abs_div, abs_mul, abs_of_nonneg hprodnn, abs_of_pos hnR]

/-- **The finite-level radius of a fake.** For a fake of level `K` whose deviation from `1/r` is summable, the deviation at `n` is bounded by the sieve term and
the tail, for `n 4^X ≤ K`. -/
theorem abs_cutDeviation_le_of_level {K : ℕ} {u : ℕ → ℝ} (hu : IsFakePrimeMeasure K u) (hs : Summable u)
    (hW : Summable (cutDeviation u)) {n X : ℕ} (hn : 1 ≤ n) (hX : 2 ≤ X) (hsize : n * 4 ^ X ≤ K) :
    |cutDeviation u n| ≤
      |∑' r, cutDeviation u r| * (∏ p ∈ X.primesBelow, (1 - ((p : ℝ))⁻¹)) / n +
        ∑' t, ‖cutDeviation u (n * (t + X))‖ := by
  have hW0 : cutDeviation u 0 = 0 := by
    simp [cutDeviation, cutTail]
  refine abs_le_of_uniform_multiples_level hW hW0 (fun k hk hkK => ?_) hn hX hsize
  refine uniform_multiple_of_tendsto hW hW0 hk ?_
  have h := (tendsto_cutDefect_inv hk).sub
    (tendsto_cutDefect_tail hs hk (hu.moment k (mem_Icc.mpr ⟨hk, hkK⟩)))
  rw [sub_self] at h
  refine h.congr fun J => ?_
  simp only [cutDefect, cutDeviation, sum_sub_distrib]
  ring

end GaloisForLFunctions.RigidArithmeticOfCuts
