import GaloisForLFunctions.RHTower.AdmissionBelowHalfDampingAboveTheZeroWidth
import GaloisForLFunctions.TransHorizonIncidenceMechanics.SignBlindDampingsStopAtHalfAndSignedDampingsReadTheZeros
import GaloisForLFunctions.TransHorizonIncidenceMechanics.MoebiusAndLiouvilleReceiversAreEquivalent
import GaloisForLFunctions.BezoutValuationIncidence.LittlewoodAdmitsTheReceiverAboveHalfTheZeroAbscissa

/-!
# Small-damping Möbius and Liouville cancellation laws

This module establishes the unconditional small-damping cancellation laws for the power-damped
Möbius weight `μ(d) d^{-ε}` and Liouville weight `λ(d) d^{-ε}` across the entire sub-half damping
range `0 < ε ≤ 1/2`:

1. **All-damping hyperbola rate transfer (`abs_weightCenteredPrefix_dampedSign_le_of_linear_pos`).**
   Removing the `ε ≥ 1/4` restriction from the hyperbola split, for every `0 < ε ≤ 1/2` and any
   sign pattern `|s(d)| ≤ 1` whose partial sums satisfy `|S(x)| ≤ L x` from `D ≥ 1` onward, the
   centred prefix of `s(d) d^{-ε}` obeys
   `|A_ε(n)| ≤ 3 D^{1-ε} + (7 + 6/ε) L n D^{-ε} ≤ 3 D^{1-ε} + (13/ε) L n D^{-ε}`.

2. **All-damping Vinogradov–Korobov prefix and zero-free band bounds
   (`exists_abs_weightCenteredPrefix_pmPowerDamped_le_all_pos`,
   `exists_receiver_le_on_zeroFreeBand_of_pos`).**
   There exist absolute constants `K ≥ 0` and `N₁` such that for **every** `0 < ε ≤ 1/2` and every
   `n ≥ N₁`,
   `|A_ε(n)| ≤ (K/ε) n^{1-ε} exp(-√(log n)/40)`.
   Consequently, for any positive damping floor `0 < ε₀ ≤ 1/2`, the Möbius receiver energy
   `E_T(ε)` is uniformly bounded over all horizons `T` and all `ε ∈ [ε₀, 1/2]` in the
   Vinogradov–Korobov zero-free band `ε ≥ 1/2 - 1/(80 √(log T))`.

3. **Zero-free band transfer to the damped Liouville receiver
   (`exists_liouville_receiver_le_on_zeroFreeBand_of_pos`,
   `exists_liouville_receiver_le_on_zeroFreeBand`).**
   Because `λ(d) d^{-ε} = (1_□(q) q^{-ε}) ⋆ (μ(d) d^{-ε})` and the critical-Wiener norm of the
   damped square kernel is uniformly bounded by `∑ j^{-(1+2ε₀)}` on `ε ≥ ε₀ > 0`, the zero-free
   band bound transfers with a cutoff- and `ε`-uniform constant to the damped Liouville receiver.

4. **General subpower partial-sum to small-damping receiver transfer
   (`receiverBounded_dampedSign_of_partialSum_rpow`).**
   For any sign pattern `|s(d)| ≤ 1` with `|∑_{e ≤ N} s(e)| ≤ C (N + 1)^β` (`0 ≤ β < 1`), the
   damped weight `s(d) d^{-ε}` has a bounded receiver for every `ε > β/2`, down to arbitrarily
   small positive damping when `β` is small.

5. **Exact zero-width admission and parity pairs for Möbius and Liouville receivers
   (`receiverBounded_moebius_of_zetaZeroAbscissa_sub_half_lt`,
   `receiverBounded_liouville_of_zetaZeroAbscissa_sub_half_lt`,
   `liouville_parityPair_of_zetaZeroAbscissa_sub_half_lt`,
   `riemannHypothesis_iff_forall_pos_receiverBounded_moebius_and_liouville`).**
   Every damping `ε > Θ - 1/2` admits both the Möbius and Liouville receivers and produces a
   Liouville parity pair at `ε ≤ 1/2`; the Riemann Hypothesis holds iff all `ε > 0` are admitted
   for both weights.
-/

open Finset Filter Topology
open GaloisForLFunctions.BezoutValuationIncidence
open _root_.RHTower
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### §1. All-damping hyperbola rate transfer (`0 < ε ≤ 1/2`) -/

/-- **All-damping hyperbola rate transfer.** If `|s(d)| ≤ 1` and `|∑_{e ≤ x} s(e)| ≤ L x` for
`x ≥ D ≥ 1`, then for every `0 < ε ≤ 1/2` and `D ≤ n`,
`|A_ε(n)| ≤ 3 D^{1-ε} + (13/ε) L n D^{-ε}`. -/
theorem abs_weightCenteredPrefix_dampedSign_le_of_linear_pos {s : ℕ → ℝ} {L ε : ℝ} (hL : 0 ≤ L)
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hs1 : ∀ d, |s d| ≤ 1) {n D : ℕ} (hD : 1 ≤ D)
    (hDn : D ≤ n) (hS : ∀ x, D ≤ x → |∑ e ∈ Icc 1 x, s e| ≤ L * x) :
    |weightCenteredPrefix (dampedSignWeight s ε) (∑' d : ℕ, dampedSignWeight s ε d / d) n| ≤
      3 * (D : ℝ) ^ (1 - ε) + 13 / ε * L * n * (D : ℝ) ^ (-ε) := by
  set c := dampedSignWeight s ε
  have hsum := summable_dampedSignWeight_div_of_abs_le_one hε hs1
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hmean : ∑' d : ℕ, c d / d = ∑ d ∈ Icc 1 D, c d / d +
      ∑' i : ℕ, c (i + (D + 1)) / ((i + (D + 1) : ℕ) : ℝ) := by
    rw [← hsum.sum_add_tsum_nat_add (D + 1), dampedSign_sum_range_succ_eq_add_Icc]
    simp [c, dampedSignWeight]
  have hsplit : ∑ d ∈ Icc 1 n, c d * ((n / d : ℕ) : ℝ) =
      ∑ d ∈ Icc 1 D, c d * ((n / d : ℕ) : ℝ) + ∑ d ∈ Ioc D n, c d * ((n / d : ℕ) : ℝ) := by
    have h1 : Icc 1 n = Ioc 0 n := by ext d; simp only [mem_Icc, mem_Ioc]; omega
    have h2 : Icc 1 D = Ioc 0 D := by ext d; simp only [mem_Icc, mem_Ioc]; omega
    rw [h1, h2, sum_Ioc_consecutive _ (Nat.zero_le D) hDn]
  have hlong : ∑ d ∈ Ioc D n, c d * ((n / d : ℕ) : ℝ) =
      ∑ k ∈ Icc 1 n, ∑ d ∈ Ioc D (n / k), c d := by
    have hcount : ∀ d, c d * ((n / d : ℕ) : ℝ) = ∑ _k ∈ Icc 1 (n / d), c d := fun d => by
      rw [sum_const, Nat.card_Icc, nsmul_eq_mul, mul_comm]; simp
    simp_rw [hcount]
    refine sum_comm' fun d k => ?_
    simp only [mem_Ioc, mem_Icc]
    constructor
    · rintro ⟨⟨hDd, hdn⟩, hk1, hkd⟩
      have hd0 : 0 < d := by omega
      have hkd' : k * d ≤ n := (Nat.le_div_iff_mul_le hd0).mp hkd
      refine ⟨⟨hDd, (Nat.le_div_iff_mul_le (by omega)).mpr (by linarith [mul_comm k d])⟩,
        hk1, le_trans hkd (Nat.div_le_self n d)⟩
    · rintro ⟨⟨hDd, hdk⟩, hk1, hkn⟩
      have hd0 : 0 < d := by omega
      have hdk' : d * k ≤ n := (Nat.le_div_iff_mul_le (by omega)).mp hdk
      refine ⟨⟨hDd, le_trans hdk (Nat.div_le_self n k)⟩, hk1,
        (Nat.le_div_iff_mul_le hd0).mpr (by linarith [mul_comm k d])⟩
  -- Piece (a): short moduli d ≤ D
  have ha : |∑ d ∈ Icc 1 D, c d * ((n / d : ℕ) : ℝ) - n * ∑ d ∈ Icc 1 D, c d / d| ≤
      3 * (D : ℝ) ^ (1 - ε) := by
    rw [mul_sum, ← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ d ∈ Icc 1 D, |c d * ((n / d : ℕ) : ℝ) - n * (c d / d)| ≤ (d : ℝ) ^ (-ε) := by
      intro d hd
      rw [mem_Icc] at hd
      have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
      have hfl1 : ((n / d : ℕ) : ℝ) ≤ (n : ℝ) / d := Nat.cast_div_le
      have hfl2 : (n : ℝ) / d - 1 < ((n / d : ℕ) : ℝ) := by
        have h := Nat.lt_div_mul_add (a := n) (show 0 < d by omega)
        have h' : (n : ℝ) < ((n / d : ℕ) : ℝ) * d + d := by exact_mod_cast h
        rw [div_sub_one hd0.ne', div_lt_iff₀ hd0]; linarith
      have hc : |c d| ≤ (d : ℝ) ^ (-ε) := by
        rw [show c d = s d * (d : ℝ) ^ (-ε) from rfl, abs_mul,
          abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
        exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg d) _) (hs1 d)
      have heq : c d * ((n / d : ℕ) : ℝ) - n * (c d / d) = c d * (((n / d : ℕ) : ℝ) - n / d) := by
        field_simp
      rw [heq, abs_mul]
      have hfr : |((n / d : ℕ) : ℝ) - n / d| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      exact (mul_le_mul hc hfr (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg d) _)).trans
        (le_of_eq (mul_one _))
    exact (sum_le_sum hterm).trans (sum_Icc_rpow_neg_le_three hε hε2 hD)
  -- Piece (b): long moduli D < d ≤ n, summed along cofactors k ≤ n/(D+1)
  have hb : |∑ k ∈ Icc 1 n, ∑ d ∈ Ioc D (n / k), c d| ≤
      (10 / ε) * L * n * (D : ℝ) ^ (-ε) := by
    have hblock : ∀ k ∈ Icc 1 n, |∑ d ∈ Ioc D (n / k), c d| ≤
        (if D + 1 ≤ n / k then 5 * L * (n : ℝ) ^ (1 - ε) * (k : ℝ) ^ (-(1 - ε)) else 0) := by
      intro k hk
      rw [mem_Icc] at hk
      have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      split_ifs with h
      · have h5 := abs_sum_Ioc_rpow_le_of_linear (X := n / k) hD (by omega) hL hε hε2 hS
        have hX : ((n / k : ℕ) : ℝ) ^ (1 - ε) ≤ (n : ℝ) ^ (1 - ε) * (k : ℝ) ^ (-(1 - ε)) := by
          have hle : ((n / k : ℕ) : ℝ) ≤ (n : ℝ) / k := Nat.cast_div_le
          calc ((n / k : ℕ) : ℝ) ^ (1 - ε) ≤ ((n : ℝ) / k) ^ (1 - ε) :=
                Real.rpow_le_rpow (Nat.cast_nonneg _) hle (by linarith)
            _ = (n : ℝ) ^ (1 - ε) * (k : ℝ) ^ (-(1 - ε)) := by
                rw [Real.div_rpow hn0.le hk0.le, Real.rpow_neg hk0.le, div_eq_mul_inv]
        calc |∑ d ∈ Ioc D (n / k), c d| = |∑ d ∈ Ioc D (n / k), s d * (d : ℝ) ^ (-ε)| := rfl
          _ ≤ 5 * L * ((n / k : ℕ) : ℝ) ^ (1 - ε) := h5
          _ ≤ 5 * L * ((n : ℝ) ^ (1 - ε) * (k : ℝ) ^ (-(1 - ε))) := by gcongr
          _ = _ := by ring
      · rw [Ioc_eq_empty (by omega), sum_empty, abs_zero]
    refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hblock).trans ?_)
    rw [← sum_filter, ← mul_sum]
    set K := n / (D + 1)
    have hsub : filter (fun k => D + 1 ≤ n / k) (Icc 1 n) ⊆ Icc 1 K := by
      intro k hk
      simp only [mem_filter, mem_Icc] at hk ⊢
      refine ⟨hk.1.1, (Nat.le_div_iff_mul_le (by omega)).mpr ?_⟩
      have := (Nat.le_div_iff_mul_le (by omega : 0 < k)).mp hk.2
      linarith [mul_comm k (D + 1)]
    have hKle : (K : ℝ) ≤ (n : ℝ) / D := by
      calc (K : ℝ) ≤ (n : ℝ) / ((D + 1 : ℕ) : ℝ) := Nat.cast_div_le
        _ ≤ (n : ℝ) / D := div_le_div_of_nonneg_left hn0.le hD0 (by push_cast; linarith)
    have hnD1 : (1 : ℝ) ≤ (n : ℝ) / D := by
      rw [le_div_iff₀ hD0, one_mul]; exact_mod_cast hDn
    have hksum : ∑ k ∈ filter (fun k => D + 1 ≤ n / k) (Icc 1 n), (k : ℝ) ^ (-(1 - ε)) ≤
        (2 / ε) * ((n : ℝ) / D) ^ ε := by
      have h1 : ∑ k ∈ filter (fun k => D + 1 ≤ n / k) (Icc 1 n), (k : ℝ) ^ (-(1 - ε)) ≤
          ∑ k ∈ Icc 1 K, (k : ℝ) ^ (-(1 - ε)) :=
        sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => Real.rpow_nonneg (Nat.cast_nonneg k) _
      have h2 := RHTower.sum_rpow_neg_head_le (c := 1 - ε) (by linarith) (by linarith) K
      rw [show (1 : ℝ) - (1 - ε) = ε by ring] at h2
      have h3 : (K : ℝ) ^ ε ≤ ((n : ℝ) / D) ^ ε :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hKle hε.le
      have h4 : (1 : ℝ) ≤ ((n : ℝ) / D) ^ ε := Real.one_le_rpow hnD1 hε.le
      have h5 : 1 + (K : ℝ) ^ ε / ε ≤ (2 / ε) * ((n : ℝ) / D) ^ ε := by
        have h4' : 1 ≤ 1 / ε * ((n : ℝ) / D) ^ ε := by
          rw [one_div_mul_eq_div, le_div_iff₀ hε]
          nlinarith [h4]
        have h3' : (K : ℝ) ^ ε / ε ≤ 1 / ε * ((n : ℝ) / D) ^ ε := by
          rw [one_div_mul_eq_div]
          exact div_le_div_of_nonneg_right h3 hε.le
        calc 1 + (K : ℝ) ^ ε / ε ≤ 1 / ε * ((n : ℝ) / D) ^ ε + 1 / ε * ((n : ℝ) / D) ^ ε :=
              add_le_add h4' h3'
          _ = (2 / ε) * ((n : ℝ) / D) ^ ε := by ring
      linarith
    have hpow : (n : ℝ) ^ (1 - ε) * ((n : ℝ) / D) ^ ε = n * (D : ℝ) ^ (-ε) := by
      rw [Real.div_rpow hn0.le hD0.le, Real.rpow_neg hD0.le, mul_div_assoc', ← Real.rpow_add hn0,
        show 1 - ε + ε = 1 by ring, Real.rpow_one, div_eq_mul_inv]
    have hcoef : 0 ≤ 5 * L * (n : ℝ) ^ (1 - ε) := by
      have := Real.rpow_nonneg hn0.le (1 - ε); positivity
    calc 5 * L * (n : ℝ) ^ (1 - ε) *
          ∑ k ∈ filter (fun k => D + 1 ≤ n / k) (Icc 1 n), (k : ℝ) ^ (-(1 - ε))
        ≤ 5 * L * (n : ℝ) ^ (1 - ε) * ((2 / ε) * ((n : ℝ) / D) ^ ε) :=
          mul_le_mul_of_nonneg_left hksum hcoef
      _ = (10 / ε) * L * ((n : ℝ) ^ (1 - ε) * ((n : ℝ) / D) ^ ε) := by ring
      _ = (10 / ε) * L * n * (D : ℝ) ^ (-ε) := by rw [hpow]; ring
  -- Piece (c): tail of the mean d > D
  have hc : |(n : ℝ) * ∑' i : ℕ, c (i + (D + 1)) / ((i + (D + 1) : ℕ) : ℝ)| ≤
      (3 / ε) * L * n * (D : ℝ) ^ (-ε) := by
    have ht := (abs_tsum_tail_rpow_le_of_linear hD hL hε hs1 hS).2
    have heq : ∑' i : ℕ, c (i + (D + 1)) / ((i + (D + 1) : ℕ) : ℝ) =
        ∑' i : ℕ, ((i + (D + 1) : ℕ) : ℝ) ^ (-(1 + ε)) * s (i + (D + 1)) :=
      tsum_congr fun i => dampedSignWeight_div hε _
    have h3 : 2 + 1 / ε ≤ 3 / ε := by
      rw [add_div' _ _ _ hε.ne', div_le_div_iff_of_pos_right hε]
      linarith
    have hDp : 0 ≤ L * (D : ℝ) ^ (-ε) := mul_nonneg hL (Real.rpow_nonneg hD0.le _)
    rw [heq, abs_mul, Nat.abs_cast]
    calc (n : ℝ) * |∑' i : ℕ, ((i + (D + 1) : ℕ) : ℝ) ^ (-(1 + ε)) * s (i + (D + 1))|
        ≤ n * ((2 + 1 / ε) * L * (D : ℝ) ^ (-ε)) := mul_le_mul_of_nonneg_left ht hn0.le
      _ ≤ n * ((3 / ε) * (L * (D : ℝ) ^ (-ε))) := by
          rw [mul_assoc (2 + 1 / ε)]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 hDp) hn0.le
      _ = (3 / ε) * L * n * (D : ℝ) ^ (-ε) := by ring
  -- Assemble the three pieces
  have hA : weightCenteredPrefix c (∑' d : ℕ, c d / d) n =
      (∑ d ∈ Icc 1 D, c d * ((n / d : ℕ) : ℝ) - n * ∑ d ∈ Icc 1 D, c d / d) +
        ∑ k ∈ Icc 1 n, ∑ d ∈ Ioc D (n / k), c d -
          (n : ℝ) * ∑' i : ℕ, c (i + (D + 1)) / ((i + (D + 1) : ℕ) : ℝ) := by
    rw [weightCenteredPrefix, sum_Icc_sum_divisors_eq_floor, hsplit, hlong, hmean]
    ring
  rw [hA]
  calc _ ≤ |∑ d ∈ Icc 1 D, c d * ((n / d : ℕ) : ℝ) - n * ∑ d ∈ Icc 1 D, c d / d| +
        |∑ k ∈ Icc 1 n, ∑ d ∈ Ioc D (n / k), c d| +
          |(n : ℝ) * ∑' i : ℕ, c (i + (D + 1)) / ((i + (D + 1) : ℕ) : ℝ)| := by
        refine (abs_sub _ _).trans ?_
        gcongr
        exact abs_add_le _ _
    _ ≤ 3 * (D : ℝ) ^ (1 - ε) + (10 / ε) * L * n * (D : ℝ) ^ (-ε) +
          (3 / ε) * L * n * (D : ℝ) ^ (-ε) := by linarith
    _ = 3 * (D : ℝ) ^ (1 - ε) + 13 / ε * L * n * (D : ℝ) ^ (-ε) := by ring

/-- Trivial all-damping prefix bound (`D = 1, L = 1`): for `0 < ε ≤ 1/2` and `n ≥ 1`,
`|A_ε(n)| ≤ 3 + (13/ε) n`. -/
theorem abs_weightCenteredPrefix_pmPowerDamped_le_trivial_pos {ε : ℝ} (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2) {n : ℕ} (hn : 1 ≤ n) :
    |weightCenteredPrefix (pmPowerDampedRealWeight ε) (dampedDensity ε) n| ≤
      3 + 13 / ε * n := by
  have hS : ∀ x, 1 ≤ x → |∑ e ∈ Icc 1 x, moebiusReal e| ≤ 1 * x := fun x _ => by
    rw [one_mul]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ e ∈ Icc 1 x, |moebiusReal e| ≤ ∑ _e ∈ Icc 1 x, (1 : ℝ) :=
          sum_le_sum fun e _ => abs_moebiusReal_le_one' e
      _ = x := by simp
  have h := abs_weightCenteredPrefix_dampedSign_le_of_linear_pos zero_le_one hε hε2
    (fun d => abs_moebiusReal_le_one' d) le_rfl hn hS
  rw [← dampedDensity_eq_tsum hε, ← pmPowerDampedRealWeight_eq_dampedSignWeight] at h
  simpa using h

/-! ### §2. All-damping Vinogradov–Korobov prefix and zero-free band bounds -/

/-- **All-damping Vinogradov–Korobov prefix bound.** There exist `K ≥ 0` and `N₁` such that for
**every** `0 < ε ≤ 1/2` and every `n ≥ N₁`,
`|A_ε(n)| ≤ (K / ε) n^{1-ε} exp(-√(log n)/40)`. -/
theorem exists_abs_weightCenteredPrefix_pmPowerDamped_le_all_pos :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N₁ : ℕ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∀ n : ℕ, N₁ ≤ n →
      |weightCenteredPrefix (pmPowerDampedRealWeight ε) (dampedDensity ε) n| ≤
        K / ε * (n : ℝ) ^ (1 - ε) * Real.exp (-(Real.sqrt (Real.log n) / 40)) := by
  obtain ⟨B, hB, N₀, hM⟩ := exists_abs_sum_moebiusReal_le_sqrtLog
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp
    ((hlog.eventually_ge_atTop 4).and (hlog.eventually_ge_atTop (9 / 4 * Real.log (N₀ + 2))))
  refine ⟨3 + 26 * B, by positivity, N₁, fun ε hε hε2 n hn => ?_⟩
  obtain ⟨hℓ4, hℓN⟩ := hN₁ n hn
  set ℓ := Real.log n with hℓdef
  set u := Real.sqrt ℓ with hudef
  have hn0 : (0 : ℝ) < n := by
    by_contra h
    have : (n : ℝ) = 0 := le_antisymm (not_lt.mp h) (Nat.cast_nonneg n)
    rw [hℓdef, this, Real.log_zero] at hℓ4; linarith
  have huu : u ^ 2 = ℓ := Real.sq_sqrt (by linarith)
  have hu2 : 2 ≤ u := by
    rw [hudef, show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hℓ4
  have hlog2 := Real.log_two_lt_d9
  have hlog2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set y := Real.exp (ℓ - u / 20) with hydef
  have hy0 : 0 < y := Real.exp_pos _
  have hlogy : Real.log y = ℓ - u / 20 := Real.log_exp _
  have hkey : 4 / 9 * ℓ ≤ ℓ - u / 20 - Real.log 2 := by nlinarith
  have hN2 : (0 : ℝ) < (N₀ : ℝ) + 2 := by positivity
  have hy2 : (N₀ : ℝ) + 2 ≤ y / 2 := by
    have h := Real.exp_le_exp.mpr (show Real.log ((N₀ : ℝ) + 2) ≤ ℓ - u / 20 - Real.log 2 by
      linarith)
    rwa [Real.exp_log hN2, Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h
  set D := ⌊y⌋₊ with hDdef
  have hDy : (D : ℝ) ≤ y := Nat.floor_le hy0.le
  have hyD : y / 2 ≤ (D : ℝ) := by
    have := Nat.lt_floor_add_one y
    linarith
  have hD0 : (0 : ℝ) < D := by linarith
  have hDN₀ : N₀ ≤ D := by
    have : (N₀ : ℝ) ≤ D := by linarith
    exact_mod_cast this
  have hD1 : 1 ≤ D := by
    have : (1 : ℝ) ≤ D := by linarith
    exact_mod_cast this
  have hDn : D ≤ n := by
    have hyn : y ≤ n := by
      rw [hydef, ← Real.exp_log hn0]
      exact Real.exp_le_exp.mpr (by rw [← hℓdef]; linarith [Real.sqrt_nonneg ℓ])
    exact_mod_cast hDy.trans hyn
  have hlogD_le : Real.log D ≤ ℓ - u / 20 := by
    rw [← hlogy]; exact Real.log_le_log hD0 hDy
  have hlogD_ge : ℓ - u / 20 - Real.log 2 ≤ Real.log D := by
    have h := Real.log_le_log (by positivity) hyD
    rwa [Real.log_div hy0.ne' (by norm_num), hlogy] at h
  have hsqD : 2 / 3 * u ≤ Real.sqrt (Real.log D) := by
    have h49 : (2 / 3 * u) ^ 2 = 4 / 9 * ℓ := by rw [mul_pow, huu]; ring
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2 / 3 * u), h49]
    exact Real.sqrt_le_sqrt (by linarith)
  set L := B * Real.exp (-(Real.sqrt (Real.log D) / 12)) with hLdef
  have hL0 : 0 ≤ L := by positivity
  have hS : ∀ x, D ≤ x → |∑ e ∈ Icc 1 x, moebiusReal e| ≤ L * x := by
    intro x hx
    have hxR : (D : ℝ) ≤ x := by exact_mod_cast hx
    have hmono : Real.exp (-(Real.sqrt (Real.log x) / 12)) ≤
        Real.exp (-(Real.sqrt (Real.log D) / 12)) :=
      Real.exp_le_exp.mpr (by
        have := Real.sqrt_le_sqrt (Real.log_le_log hD0 hxR)
        linarith)
    calc _ ≤ B * x * Real.exp (-(Real.sqrt (Real.log x) / 12)) := hM x (hDN₀.trans hx)
      _ ≤ B * x * Real.exp (-(Real.sqrt (Real.log D) / 12)) :=
          mul_le_mul_of_nonneg_left hmono (by positivity)
      _ = L * x := by rw [hLdef]; ring
  have hhyp := abs_weightCenteredPrefix_dampedSign_le_of_linear_pos hL0 hε hε2
    (fun d => abs_moebiusReal_le_one' d) hD1 hDn hS
  rw [← dampedDensity_eq_tsum hε, ← pmPowerDampedRealWeight_eq_dampedSignWeight] at hhyp
  have hnpow : (n : ℝ) ^ (1 - ε) = Real.exp (ℓ * (1 - ε)) := Real.rpow_def_of_pos hn0 _
  have hshort : (D : ℝ) ^ (1 - ε) ≤ (n : ℝ) ^ (1 - ε) * Real.exp (-(u / 40)) := by
    rw [Real.rpow_def_of_pos hD0, hnpow, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hu0 : 0 ≤ u := Real.sqrt_nonneg _
    nlinarith
  have hlong : (n : ℝ) * (D : ℝ) ^ (-ε) * Real.exp (-(Real.sqrt (Real.log D) / 12)) ≤
      2 * ((n : ℝ) ^ (1 - ε) * Real.exp (-(u / 40))) := by
    rw [Real.rpow_def_of_pos hD0, hnpow, ← Real.exp_log hn0, ← hℓdef, ← Real.exp_add,
      ← Real.exp_add, ← Real.exp_add, ← Real.exp_log (by norm_num : (0 : ℝ) < 2), ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hu0 : 0 ≤ u := Real.sqrt_nonneg _
    nlinarith
  have h3ε : (3 : ℝ) ≤ 3 / ε := by
    rw [le_div_iff₀ hε]; linarith
  have hterm0 : 0 ≤ (n : ℝ) ^ (1 - ε) * Real.exp (-(u / 40)) := by positivity
  calc _ ≤ 3 * (D : ℝ) ^ (1 - ε) + 13 / ε * L * n * (D : ℝ) ^ (-ε) := hhyp
    _ = 3 * (D : ℝ) ^ (1 - ε) +
          (13 / ε * B) * ((n : ℝ) * (D : ℝ) ^ (-ε) * Real.exp (-(Real.sqrt (Real.log D) / 12))) := by
        rw [hLdef]; ring
    _ ≤ (3 / ε) * ((n : ℝ) ^ (1 - ε) * Real.exp (-(u / 40))) +
          (13 / ε * B) * (2 * ((n : ℝ) ^ (1 - ε) * Real.exp (-(u / 40)))) := by
        refine add_le_add (mul_le_mul h3ε hshort (by positivity) (by positivity)) ?_
        exact mul_le_mul_of_nonneg_left hlong (by positivity)
    _ = (3 + 26 * B) / ε * (n : ℝ) ^ (1 - ε) * Real.exp (-(Real.sqrt (Real.log n) / 40)) := by
        rw [hudef, hℓdef]; ring

/-- **The Möbius receiver on the zero-free band above any positive damping floor `ε₀ > 0`.**
For every `0 < ε₀ ≤ 1/2` there exists `E ≥ 0` such that `E_T(ε) ≤ E` for all horizons `T` and all
`ε ∈ [ε₀, 1/2]` satisfying `ε ≥ 1/2 - 1/(80 √(log T))`. -/
theorem exists_receiver_le_on_zeroFreeBand_of_pos {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ E : ℝ, ∀ (T : ℕ) (ε : ℝ), ε₀ ≤ ε → ε ≤ 1 / 2 →
      1 / 2 - 1 / (80 * Real.sqrt (Real.log T)) ≤ ε →
        RHTower.pmPowerDampedDivisorDiscreteEnergy ε T ≤ E := by
  obtain ⟨K, hK, N₁, hpre⟩ := exists_abs_weightCenteredPrefix_pmPowerDamped_le_all_pos
  have hsum := GaloisForLFunctions.HTGeometry.summable_exp_neg_sqrt_log_div
    (show (0 : ℝ) < 1 / 40 by norm_num)
  set S := ∑' m : ℕ, Real.exp (-(1 / 40 * Real.sqrt (Real.log m))) / m
  refine ⟨(N₁ : ℝ) * (3 + 13 / ε₀ * N₁) ^ 2 + (K / ε₀) ^ 2 * S, fun T ε hε_ge hε2 hband => ?_⟩
  have hε : 0 < ε := hε₀.trans_le hε_ge
  rw [← weightPronicEnergy_pmPowerDamped, weightPronicEnergy]
  set f := fun n : ℕ => weightCenteredPrefix (pmPowerDampedRealWeight ε) (dampedDensity ε) n ^ 2 /
    ((n : ℝ) * ((n : ℝ) + 1)) with hfdef
  have hf0 : ∀ n, 0 ≤ f n := fun n => by simp only [hfdef]; positivity
  have hsplit : ∑ n ∈ Icc 1 T, f n ≤
      ∑ n ∈ Icc 1 T with n < N₁, f n + ∑ n ∈ Icc 1 T with ¬ n < N₁, f n :=
    (sum_filter_add_sum_filter_not _ _ _).ge
  have hsmall : ∑ n ∈ Icc 1 T with n < N₁, f n ≤ (N₁ : ℝ) * (3 + 13 / ε₀ * N₁) ^ 2 := by
    have hsub : (Icc 1 T).filter (fun n => n < N₁) ⊆ range N₁ := fun n hn => by
      simp only [mem_filter, mem_range] at hn ⊢; exact hn.2
    have hterm : ∀ n ∈ (Icc 1 T).filter (fun n => n < N₁), f n ≤ (3 + 13 / ε₀ * N₁) ^ 2 := by
      intro n hn
      simp only [mem_filter, mem_Icc] at hn
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1.1
      have hA := abs_weightCenteredPrefix_pmPowerDamped_le_trivial_pos hε hε2 hn.1.1
      have h13 : 13 / ε ≤ 13 / ε₀ := div_le_div_of_nonneg_left (by norm_num) hε₀ hε_ge
      have hA' : |weightCenteredPrefix (pmPowerDampedRealWeight ε) (dampedDensity ε) n| ≤
          3 + 13 / ε₀ * N₁ := by
        have hnN : (n : ℝ) ≤ N₁ := by exact_mod_cast hn.2.le
        have := mul_le_mul h13 hnN (Nat.cast_nonneg n) (by positivity)
        linarith
      have hA2 : weightCenteredPrefix (pmPowerDampedRealWeight ε) (dampedDensity ε) n ^ 2 ≤
          (3 + 13 / ε₀ * N₁) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hA' 2
      simp only [hfdef]
      rw [div_le_iff₀ (by positivity)]
      exact hA2.trans (le_mul_of_one_le_right (sq_nonneg _) (by nlinarith))
    calc ∑ n ∈ Icc 1 T with n < N₁, f n ≤ ∑ n ∈ Icc 1 T with n < N₁, (3 + 13 / ε₀ * (N₁ : ℝ)) ^ 2 :=
          sum_le_sum hterm
      _ = (((Icc 1 T).filter (fun n => n < N₁)).card : ℝ) * (3 + 13 / ε₀ * N₁) ^ 2 := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ (N₁ : ℝ) * (3 + 13 / ε₀ * N₁) ^ 2 := by
          gcongr
          exact_mod_cast (card_le_card hsub).trans (card_range N₁).le
  have hlarge : ∑ n ∈ Icc 1 T with ¬ n < N₁, f n ≤ (K / ε₀) ^ 2 * S := by
    have hKε : K / ε ≤ K / ε₀ := div_le_div_of_nonneg_left hK hε₀ hε_ge
    have hterm : ∀ n ∈ (Icc 1 T).filter (fun n => ¬ n < N₁),
        f n ≤ (K / ε₀) ^ 2 * (Real.exp (-(1 / 40 * Real.sqrt (Real.log n))) / n) := by
      intro n hn
      simp only [mem_filter, mem_Icc, not_lt] at hn
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1.1
      have hn0 : (0 : ℝ) < n := by linarith
      set ℓ := Real.log n with hℓ
      set u := Real.sqrt ℓ
      have hℓ0 : 0 ≤ ℓ := Real.log_nonneg hn1
      have huu : u ^ 2 = ℓ := Real.sq_sqrt hℓ0
      have hu0 : 0 ≤ u := Real.sqrt_nonneg _
      have hA := (hpre ε hε hε2 n hn.2).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hKε (Real.rpow_nonneg hn0.le _)) (Real.exp_pos _).le)
      have hA2 : weightCenteredPrefix (pmPowerDampedRealWeight ε) (dampedDensity ε) n ^ 2 ≤
          (K / ε₀ * (n : ℝ) ^ (1 - ε) * Real.exp (-(u / 40))) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hA 2
      have hbandn : (1 - 2 * ε) * ℓ ≤ u / 40 := by
        have huT : u ≤ Real.sqrt (Real.log T) := Real.sqrt_le_sqrt
          (Real.log_le_log hn0 (by exact_mod_cast hn.1.2))
        rcases (Real.sqrt_nonneg (Real.log T)).eq_or_lt with h0 | hpos
        · have hu00 : u = 0 := le_antisymm (h0 ▸ huT) hu0
          rw [← h0, mul_zero, div_zero] at hband
          rw [← huu, hu00]; nlinarith
        · have hb : 1 - 2 * ε ≤ 2 / (80 * Real.sqrt (Real.log T)) := by
            have : 2 / (80 * Real.sqrt (Real.log T)) = 2 * (1 / (80 * Real.sqrt (Real.log T))) := by
              ring
            rw [this]; linarith
          have hε' : 0 ≤ 1 - 2 * ε := by linarith
          calc (1 - 2 * ε) * ℓ = (1 - 2 * ε) * u * u := by rw [← huu]; ring
            _ ≤ 2 / (80 * Real.sqrt (Real.log T)) * u * u := by gcongr
            _ ≤ 2 / (80 * Real.sqrt (Real.log T)) * Real.sqrt (Real.log T) * u := by gcongr
            _ = u / 40 := by field_simp; ring
      have hpow : ((n : ℝ) ^ (1 - ε)) ^ 2 * Real.exp (-(u / 40)) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
          Real.exp (-(1 / 40 * u)) / n := by
        have hnpow : ((n : ℝ) ^ (1 - ε)) ^ 2 = Real.exp (2 * ((1 - ε) * ℓ)) := by
          rw [Real.rpow_def_of_pos hn0, ← Real.exp_nat_mul, hℓ]; congr 1; push_cast; ring
        have hex : Real.exp (-(u / 40)) ^ 2 = Real.exp (-(u / 20)) := by
          rw [← Real.exp_nat_mul]; push_cast; ring_nf
        rw [hnpow, hex, ← Real.exp_add]
        rw [div_le_div_iff₀ (by positivity) hn0]
        have hnn : (n : ℝ) * (n : ℝ) ≤ (n : ℝ) * ((n : ℝ) + 1) := by nlinarith
        have hnexp : (n : ℝ) = Real.exp ℓ := (Real.exp_log hn0).symm
        calc Real.exp (2 * ((1 - ε) * ℓ) + -(u / 20)) * n
            = Real.exp (-(1 / 40 * u)) * ((n : ℝ) * (n : ℝ)) *
                Real.exp ((1 - 2 * ε) * ℓ - u / 40) := by
              rw [hnexp, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
              congr 1; ring
          _ ≤ Real.exp (-(1 / 40 * u)) * ((n : ℝ) * (n : ℝ)) * 1 := by
              gcongr
              exact Real.exp_le_one_iff.mpr (by linarith)
          _ ≤ Real.exp (-(1 / 40 * u)) * ((n : ℝ) * ((n : ℝ) + 1)) := by
              rw [mul_one]; exact mul_le_mul_of_nonneg_left hnn (Real.exp_pos _).le
      calc f n ≤ (K / ε₀ * (n : ℝ) ^ (1 - ε) * Real.exp (-(u / 40))) ^ 2 /
            ((n : ℝ) * ((n : ℝ) + 1)) :=
            div_le_div_of_nonneg_right hA2 (by positivity)
        _ = (K / ε₀) ^ 2 * (((n : ℝ) ^ (1 - ε)) ^ 2 * Real.exp (-(u / 40)) ^ 2 /
              ((n : ℝ) * ((n : ℝ) + 1))) := by ring
        _ ≤ (K / ε₀) ^ 2 * (Real.exp (-(1 / 40 * Real.sqrt (Real.log n))) / n) :=
            mul_le_mul_of_nonneg_left hpow (sq_nonneg _)
    calc ∑ n ∈ Icc 1 T with ¬ n < N₁, f n
        ≤ ∑ n ∈ Icc 1 T with ¬ n < N₁,
            (K / ε₀) ^ 2 * (Real.exp (-(1 / 40 * Real.sqrt (Real.log n))) / n) :=
          sum_le_sum hterm
      _ = (K / ε₀) ^ 2 * ∑ n ∈ Icc 1 T with ¬ n < N₁,
            Real.exp (-(1 / 40 * Real.sqrt (Real.log n))) / n := by rw [mul_sum]
      _ ≤ (K / ε₀) ^ 2 * S := mul_le_mul_of_nonneg_left
          (hsum.sum_le_tsum _ fun m _ => by positivity) (sq_nonneg _)
  linarith

/-! ### §3. Zero-free band cancellation for the damped Liouville receiver -/

/-- The critical-Wiener norm of `1_□(q) q^{-ε}` is antitone in `ε > 0`. -/
theorem tsum_criticalWiener_dampedSquare_le {ε₀ ε : ℝ} (hε₀ : 0 < ε₀) (hε_ge : ε₀ ≤ ε) :
    ∑' q : ℕ, |dampedSignWeight RHTower.squareIndicatorR ε q| * (q : ℝ) ^ (-(1 / 2 : ℝ)) ≤
      ∑' q : ℕ, |dampedSignWeight RHTower.squareIndicatorR ε₀ q| * (q : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hε : 0 < ε := hε₀.trans_le hε_ge
  refine Summable.tsum_le_tsum (fun q => ?_) (criticalWiener_dampedSquare hε)
    (criticalWiener_dampedSquare hε₀)
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp [dampedSignWeight, RHTower.squareIndicatorR]
  · refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (Nat.cast_nonneg q) _)
    simp only [dampedSignWeight]
    rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg q) _),
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg q) _)]
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hq1 (by linarith))
      (abs_nonneg _)

/-- The Möbius mean `|1/ζ(1+ε)|` is bounded by `∑ d^{-(1+ε₀)}` for `ε ≥ ε₀ > 0`. -/
theorem abs_dampedDensity_le_of_le {ε₀ ε : ℝ} (hε₀ : 0 < ε₀) (hε_ge : ε₀ ≤ ε) :
    |dampedDensity ε| ≤ ∑' d : ℕ, (d : ℝ) ^ (-(1 + ε₀)) := by
  have hε : 0 < ε := hε₀.trans_le hε_ge
  rw [dampedDensity_eq_tsum hε, ← pmPowerDampedRealWeight_eq_dampedSignWeight]
  have hs0 : Summable (fun d : ℕ => (d : ℝ) ^ (-(1 + ε₀))) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hnorm : Summable (fun d : ℕ => ‖pmPowerDampedRealWeight ε d / (d : ℝ)‖) := by
    refine (summable_abs_pmPowerDamped_div hε).congr fun d => ?_
    rw [Real.norm_eq_abs]
  have habs : |∑' d : ℕ, pmPowerDampedRealWeight ε d / d| ≤
      ∑' d : ℕ, |pmPowerDampedRealWeight ε d / d| := by
    have h := norm_tsum_le_tsum_norm hnorm
    simpa only [Real.norm_eq_abs] using h
  refine habs.trans (Summable.tsum_le_tsum (fun d => ?_) (summable_abs_pmPowerDamped_div hε) hs0)
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rw [Nat.cast_zero, div_zero, abs_zero]
    exact Real.rpow_nonneg le_rfl _
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h := dampedSignWeight_div (s := moebiusReal) hε d
  simp only [dampedSignWeight] at h
  rw [show pmPowerDampedRealWeight ε d = moebiusReal d * (d : ℝ) ^ (-ε) from rfl, h, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
  exact (mul_le_of_le_one_right (Real.rpow_nonneg (Nat.cast_nonneg d) _)
    (abs_moebiusReal_le_one' d)).trans (Real.rpow_le_rpow_of_exponent_le hd1 (by linarith))

/-- **The damped Liouville receiver is uniformly bounded on the zero-free band above any `ε₀ > 0`.**
For every `0 < ε₀ ≤ 1/2` there exists `E_λ` such that the centred pronic energy of `λ(d) d^{-ε}` is
at most `E_λ` for every horizon `T` and every `ε ∈ [ε₀, 1/2]` with `ε ≥ 1/2 - 1/(80 √(log T))`. -/
theorem exists_liouville_receiver_le_on_zeroFreeBand_of_pos {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ E : ℝ, ∀ (T : ℕ) (ε : ℝ), ε₀ ≤ ε → ε ≤ 1 / 2 →
      1 / 2 - 1 / (80 * Real.sqrt (Real.log T)) ≤ ε →
        weightPronicEnergy (dampedSignWeight RHTower.liouvilleR ε)
          (∑' d : ℕ, dampedSignWeight RHTower.liouvilleR ε d / d) T ≤ E := by
  obtain ⟨Eμ, hEμ⟩ := exists_receiver_le_on_zeroFreeBand_of_pos hε₀
  set G₀ := ∑' q : ℕ, |dampedSignWeight RHTower.squareIndicatorR ε₀ q| * (q : ℝ) ^ (-(1 / 2 : ℝ))
  set M₀ := ∑' d : ℕ, (d : ℝ) ^ (-(1 + ε₀))
  have hG₀ : 0 ≤ G₀ := tsum_nonneg fun q =>
    mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg q) _)
  have hM₀ : 0 ≤ M₀ := tsum_nonneg fun d => Real.rpow_nonneg (Nat.cast_nonneg d) _
  refine ⟨(G₀ * Real.sqrt (max Eμ 0) + M₀ * ((Real.sqrt 2 + 1) * G₀)) ^ 2,
    fun T ε hε_ge hε2 hband => ?_⟩
  have hε : 0 < ε := hε₀.trans_le hε_ge
  set g := dampedSignWeight RHTower.squareIndicatorR ε
  set c := pmPowerDampedRealWeight ε
  have hgW := criticalWiener_dampedSquare hε
  have hconv : dampedSignWeight RHTower.liouvilleR ε = RHTower.dirichletConv g c :=
    funext (dampedLiouville_eq_dirichletConv ε)
  have hmean : ∑' d : ℕ, dampedSignWeight RHTower.liouvilleR ε d / d =
      (∑' q : ℕ, g q / q) * dampedDensity ε := by
    rw [hconv, (hasSum_dirichletConv_div hgW.summable_abs_div.of_abs.hasSum
      (hasSum_pmPowerDampedRealWeight_div hε) hgW.summable_abs_div
      (summable_abs_pmPowerDamped_div hε)).tsum_eq]
  rw [hmean, hconv, weightPronicEnergy_eq_sq_pronicNorm]
  have hnorm := pronicNorm_dirichletConv_le (c := c) hgW (dampedDensity ε) T
  have hAc : pronicNorm (weightCenteredPrefix c (dampedDensity ε)) T ≤ Real.sqrt (max Eμ 0) := by
    rw [← Real.sqrt_sq (pronicNorm_nonneg _ T), ← weightPronicEnergy_eq_sq_pronicNorm,
      weightPronicEnergy_pmPowerDamped]
    exact Real.sqrt_le_sqrt ((hEμ T ε hε_ge hε2 hband).trans (le_max_left _ _))
  have hG_le : ∑' q : ℕ, |g q| * (q : ℝ) ^ (-(1 / 2 : ℝ)) ≤ G₀ :=
    tsum_criticalWiener_dampedSquare_le hε₀ hε_ge
  have hM_le : |dampedDensity ε| ≤ M₀ := abs_dampedDensity_le_of_le hε₀ hε_ge
  have hG_nn : 0 ≤ ∑' q : ℕ, |g q| * (q : ℝ) ^ (-(1 / 2 : ℝ)) := tsum_nonneg fun q =>
    mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg q) _)
  have htot : pronicNorm (weightCenteredPrefix (RHTower.dirichletConv g c)
      ((∑' q : ℕ, g q / q) * dampedDensity ε)) T ≤
      G₀ * Real.sqrt (max Eμ 0) + M₀ * ((Real.sqrt 2 + 1) * G₀) := by
    refine hnorm.trans (add_le_add ?_ ?_)
    · exact mul_le_mul hG_le hAc (pronicNorm_nonneg _ T) hG₀
    · exact mul_le_mul hM_le (mul_le_mul_of_nonneg_left hG_le (by positivity))
        (by positivity) hM₀
  exact pow_le_pow_left₀ (pronicNorm_nonneg _ T) htot 2

/-- **The damped Liouville receiver on the `[1/4, 1/2]` zero-free band.** -/
theorem exists_liouville_receiver_le_on_zeroFreeBand :
    ∃ E : ℝ, ∀ (T : ℕ) (ε : ℝ), 1 / 4 ≤ ε → ε ≤ 1 / 2 →
      1 / 2 - 1 / (80 * Real.sqrt (Real.log T)) ≤ ε →
        weightPronicEnergy (dampedSignWeight RHTower.liouvilleR ε)
          (∑' d : ℕ, dampedSignWeight RHTower.liouvilleR ε d / d) T ≤ E :=
  exists_liouville_receiver_le_on_zeroFreeBand_of_pos (by norm_num)

/-! ### §4. General subpower partial-sum to small-damping receiver transfer -/

/-- **General subpower partial-sum transfer.** For any sign pattern `|s(d)| ≤ 1`, if
`|∑_{e ≤ N} s(e)| ≤ C (N + 1)^β` for some `0 ≤ β < 1` and `C ≥ 0`, then `s(d) d^{-ε}` has a bounded
receiver for every `ε > β / 2` (including arbitrarily small `ε > 0` when `β` is small). -/
theorem receiverBounded_dampedSign_of_partialSum_rpow {s : ℕ → ℝ} {β C ε : ℝ}
    (hs1 : ∀ d, |s d| ≤ 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hC0 : 0 ≤ C)
    (hS : ∀ N : ℕ, |∑ e ∈ Icc 1 N, s e| ≤ C * ((N : ℝ) + 1) ^ β)
    (hε : β / 2 < ε) :
    ReceiverBounded (dampedSignWeight s ε) := by
  have hε0 : 0 < ε := by linarith
  rcases lt_or_ge (1 / 2) ε with hgt | hε2
  · obtain ⟨E, hE⟩ := (uniformReceiverBound_iff_half_lt (K := 1) one_pos hε0).mpr hgt
    refine ⟨E, hE _ fun d => ?_⟩
    rw [dampedSignWeight, one_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg d) _) (hs1 d)
  -- For `β/2 < ε ≤ 1/2`, balance the all-damping hyperbola bound at `β' = min ((β + 2ε)/2) 1`
  set β' : ℝ := min ((β + 2 * ε) / 2) 1 with hβ'
  have hβ_le : β ≤ β' := le_min (by linarith) hβ1.le
  have hβ'2ε : β' < 2 * ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hβ'1 : β' ≤ 1 := min_le_right _ _
  have hβ'0 : 0 ≤ β' := hβ0.trans hβ_le
  have h2β : 0 < 2 - β' := by linarith
  set a : ℝ := 1 / (2 - β') with ha
  set γ : ℝ := a * (1 - ε) with hγ
  have ha0 : 0 < a := by rw [ha]; positivity
  have ha1 : a ≤ 1 := by rw [ha, div_le_one h2β]; linarith
  have hγhalf : γ < 1 / 2 := by
    rw [hγ, ha, div_mul_eq_mul_div, one_mul, div_lt_iff₀ h2β]; linarith
  have hγeq : 1 + a * (β' - 1 - ε) = γ := by
    rw [hγ, ha]; field_simp; ring
  have hpre : ∀ n : ℕ, 1 ≤ n →
      |weightCenteredPrefix (dampedSignWeight s ε) (∑' d : ℕ, dampedSignWeight s ε d / d) n| ≤
        (3 + 52 / ε * C) * (n : ℝ) ^ γ := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    set y : ℝ := (n : ℝ) ^ a with hy
    have hy1 : 1 ≤ y := by
      rw [hy, ← Real.one_rpow a]
      exact Real.rpow_le_rpow zero_le_one hn1 ha0.le
    have hy0 : 0 < y := by linarith
    set D : ℕ := ⌊y⌋₊ with hD
    have hD1 : 1 ≤ D := Nat.floor_pos.mpr hy1
    have hD0 : (0 : ℝ) < D := by exact_mod_cast hD1
    have hDy : (D : ℝ) ≤ y := Nat.floor_le hy0.le
    have hyD : y / 2 ≤ D := by
      have h1 := Nat.lt_floor_add_one y
      have h2 : (1 : ℝ) ≤ D := by exact_mod_cast hD1
      rw [← hD] at h1
      linarith
    have hyn : y ≤ n := by
      rw [hy]
      calc (n : ℝ) ^ a ≤ (n : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 ha1
        _ = n := Real.rpow_one _
    have hDn : D ≤ n := by exact_mod_cast hDy.trans hyn
    set L : ℝ := 2 * C * (D : ℝ) ^ (β' - 1) with hL
    have hL0 : 0 ≤ L := by positivity
    have hSl : ∀ x : ℕ, D ≤ x → |∑ e ∈ Icc 1 x, s e| ≤ L * x := by
      intro x hx
      have hx0 : (0 : ℝ) < x := by exact_mod_cast (hD1.trans hx)
      have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast (hD1.trans hx)
      have hDx : (D : ℝ) ≤ x := by exact_mod_cast hx
      have hxβ : (x : ℝ) ^ β' = (x : ℝ) ^ (β' - 1) * x := by
        rw [Real.rpow_sub_one hx0.ne']; field_simp
      have h2β' : (2 : ℝ) ^ β' ≤ 2 := by
        calc (2 : ℝ) ^ β' ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hβ'1
          _ = 2 := Real.rpow_one 2
      have hmon_β : ((x : ℝ) + 1) ^ β ≤ ((x : ℝ) + 1) ^ β' :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) hβ_le
      calc |∑ e ∈ Icc 1 x, s e| ≤ C * ((x : ℝ) + 1) ^ β := hS x
        _ ≤ C * ((x : ℝ) + 1) ^ β' := mul_le_mul_of_nonneg_left hmon_β hC0
        _ ≤ C * (2 * (x : ℝ)) ^ β' :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) (by linarith) hβ'0) hC0
        _ = C * (2 ^ β' * (x : ℝ) ^ β') := by rw [Real.mul_rpow (by norm_num) hx0.le]
        _ ≤ C * (2 * (x : ℝ) ^ β') :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right h2β' (Real.rpow_nonneg hx0.le _)) hC0
        _ = 2 * C * ((x : ℝ) ^ (β' - 1) * x) := by rw [hxβ]; ring
        _ ≤ 2 * C * ((D : ℝ) ^ (β' - 1) * x) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (rpow_sub_one_le_of_le hβ'1 hD0 hDx) hx0.le)
            (by positivity)
        _ = L * x := by rw [hL]; ring
    have hA := abs_weightCenteredPrefix_dampedSign_le_of_linear_pos hL0 hε0 hε2 hs1 hD1 hDn hSl
    refine hA.trans ?_
    have hT1 : (D : ℝ) ^ (1 - ε) ≤ (n : ℝ) ^ γ := by
      calc (D : ℝ) ^ (1 - ε) ≤ y ^ (1 - ε) := Real.rpow_le_rpow hD0.le hDy (by linarith)
        _ = (n : ℝ) ^ γ := by rw [hy, ← Real.rpow_mul hn0.le]
    have hpow : (D : ℝ) ^ (β' - 1 - ε) ≤ 2 * y ^ (β' - 1 - ε) := by
      have hexp0 : 0 ≤ 1 + ε - β' := by linarith
      have hexp1 : 1 + ε - β' ≤ 1 := by
        have : ε ≤ β' := by
          rw [hβ', le_min_iff]
          exact ⟨by linarith, by linarith⟩
        linarith
      have h2e : (2 : ℝ) ^ (1 + ε - β') ≤ 2 := by
        calc (2 : ℝ) ^ (1 + ε - β') ≤ 2 ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp1
          _ = 2 := Real.rpow_one 2
      have hylow : y ^ (1 + ε - β') / 2 ≤ (D : ℝ) ^ (1 + ε - β') := by
        calc y ^ (1 + ε - β') / 2 ≤ y ^ (1 + ε - β') / 2 ^ (1 + ε - β') :=
              div_le_div_of_nonneg_left (Real.rpow_nonneg hy0.le _) (by positivity) h2e
          _ = (y / 2) ^ (1 + ε - β') := (Real.div_rpow hy0.le (by norm_num) _).symm
          _ ≤ (D : ℝ) ^ (1 + ε - β') := Real.rpow_le_rpow (by positivity) hyD hexp0
      rw [show β' - 1 - ε = -(1 + ε - β') by ring, Real.rpow_neg hD0.le, Real.rpow_neg hy0.le]
      calc ((D : ℝ) ^ (1 + ε - β'))⁻¹ ≤ (y ^ (1 + ε - β') / 2)⁻¹ :=
            inv_anti₀ (by positivity) hylow
        _ = 2 * (y ^ (1 + ε - β'))⁻¹ := by rw [inv_div]; ring
    have hT2 : 13 / ε * L * (n : ℝ) * (D : ℝ) ^ (-ε) ≤ 52 / ε * C * (n : ℝ) ^ γ := by
      have hcomb : (D : ℝ) ^ (β' - 1) * (D : ℝ) ^ (-ε) = (D : ℝ) ^ (β' - 1 - ε) := by
        rw [← Real.rpow_add hD0]; ring_nf
      have hyγ : (n : ℝ) * y ^ (β' - 1 - ε) = (n : ℝ) ^ γ := by
        rw [hy, ← Real.rpow_mul hn0.le, ← hγeq, Real.rpow_add hn0, Real.rpow_one]
      calc 13 / ε * L * (n : ℝ) * (D : ℝ) ^ (-ε)
          = (26 / ε * C * (n : ℝ)) * ((D : ℝ) ^ (β' - 1) * (D : ℝ) ^ (-ε)) := by rw [hL]; ring
        _ = (26 / ε * C * (n : ℝ)) * (D : ℝ) ^ (β' - 1 - ε) := by rw [hcomb]
        _ ≤ (26 / ε * C * (n : ℝ)) * (2 * y ^ (β' - 1 - ε)) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
        _ = 52 / ε * C * ((n : ℝ) * y ^ (β' - 1 - ε)) := by ring
        _ = 52 / ε * C * (n : ℝ) ^ γ := by rw [hyγ]
    calc 3 * (D : ℝ) ^ (1 - ε) + 13 / ε * L * (n : ℝ) * (D : ℝ) ^ (-ε)
        ≤ 3 * (n : ℝ) ^ γ + 52 / ε * C * (n : ℝ) ^ γ :=
          add_le_add (mul_le_mul_of_nonneg_left hT1 (by norm_num)) hT2
      _ = (3 + 52 / ε * C) * (n : ℝ) ^ γ := by ring
  have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (2 * γ - 2)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  refine ⟨(3 + 52 / ε * C) ^ 2 * ∑' n : ℕ, (n : ℝ) ^ (2 * γ - 2), fun T => ?_⟩
  rw [weightPronicEnergy]
  calc ∑ n ∈ Icc 1 T,
        weightCenteredPrefix (dampedSignWeight s ε) (∑' d : ℕ, dampedSignWeight s ε d / d) n ^ 2 /
          ((n : ℝ) * ((n : ℝ) + 1))
      ≤ ∑ n ∈ Icc 1 T, (3 + 52 / ε * C) ^ 2 * (n : ℝ) ^ (2 * γ - 2) := by
        refine sum_le_sum fun n hn => ?_
        have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
        have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
        have hsq : weightCenteredPrefix (dampedSignWeight s ε)
            (∑' d : ℕ, dampedSignWeight s ε d / d) n ^ 2 ≤
            ((3 + 52 / ε * C) * (n : ℝ) ^ γ) ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hpre n hn1) 2
        have hpow : ((n : ℝ) ^ γ) ^ 2 / ((n : ℝ) * (n : ℝ)) = (n : ℝ) ^ (2 * γ - 2) := by
          have h1 : ((n : ℝ) ^ γ) ^ 2 = (n : ℝ) ^ (2 * γ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
            congr 1; push_cast; ring
          have h2 : (n : ℝ) * (n : ℝ) = (n : ℝ) ^ (2 : ℝ) := by rw [Real.rpow_two]; ring
          rw [h1, h2, Real.rpow_sub hn0 (2 * γ) 2]
        calc weightCenteredPrefix (dampedSignWeight s ε)
              (∑' d : ℕ, dampedSignWeight s ε d / d) n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))
            ≤ ((3 + 52 / ε * C) * (n : ℝ) ^ γ) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) :=
              div_le_div_of_nonneg_right hsq (by positivity)
          _ ≤ ((3 + 52 / ε * C) * (n : ℝ) ^ γ) ^ 2 / ((n : ℝ) * (n : ℝ)) :=
              div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by nlinarith)
          _ = (3 + 52 / ε * C) ^ 2 * (((n : ℝ) ^ γ) ^ 2 / ((n : ℝ) * (n : ℝ))) := by
              rw [mul_pow]; ring
          _ = (3 + 52 / ε * C) ^ 2 * (n : ℝ) ^ (2 * γ - 2) := by rw [hpow]
    _ = (3 + 52 / ε * C) ^ 2 * ∑ n ∈ Icc 1 T, (n : ℝ) ^ (2 * γ - 2) := by rw [mul_sum]
    _ ≤ (3 + 52 / ε * C) ^ 2 * ∑' n : ℕ, (n : ℝ) ^ (2 * γ - 2) :=
        mul_le_mul_of_nonneg_left
          (hsum.sum_le_tsum _ fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _) (by positivity)

/-! ### §5. Exact zero-width admission and parity pairs for Möbius and Liouville receivers -/

/-- **Admission of the Möbius receiver above the zero width `Θ - 1/2`.** -/
theorem receiverBounded_moebius_of_zetaZeroAbscissa_sub_half_lt {ε : ℝ}
    (hε : zetaZeroAbscissa - 1 / 2 < ε) :
    ReceiverBounded (pmPowerDampedRealWeight ε) := by
  have hε0 : 0 < ε := by linarith [half_le_zetaZeroAbscissa]
  exact (mem_receiverDampings_iff_receiverBounded hε0).mp
    (mem_receiverDampings_of_zetaZeroAbscissa_lt (by linarith))

/-- **Admission of the Liouville receiver above the zero width `Θ - 1/2`.** -/
theorem receiverBounded_liouville_of_zetaZeroAbscissa_sub_half_lt {ε : ℝ}
    (hε : zetaZeroAbscissa - 1 / 2 < ε) :
    ReceiverBounded (dampedSignWeight RHTower.liouvilleR ε) := by
  have hε0 : 0 < ε := by linarith [half_le_zetaZeroAbscissa]
  exact (receiverBounded_moebius_iff_liouville hε0).mp
    (receiverBounded_moebius_of_zetaZeroAbscissa_sub_half_lt hε)

/-- **The Liouville parity pair above the zero width.** For every `Θ - 1/2 < ε ≤ 1/2`, the damped
Liouville weight `λ(d) d^{-ε}` and its positive smooth-power twin `κ d^{-ε}` share all Ramanujan
amplitudes, the Liouville receiver is bounded, and the positive twin diverges. -/
theorem liouville_parityPair_of_zetaZeroAbscissa_sub_half_lt {ε : ℝ}
    (hε : zetaZeroAbscissa - 1 / 2 < ε) (hε2 : ε ≤ 1 / 2) :
    (∀ e : ℕ, |weightRamanujanCoeff (liouvilleTwin ε) e| =
        |weightRamanujanCoeff (dampedSignWeight RHTower.liouvilleR ε) e|) ∧
    (∀ d : ℕ, 0 ≤ liouvilleTwin ε d) ∧
    ReceiverBounded (dampedSignWeight RHTower.liouvilleR ε) ∧
    Tendsto (fun T => weightPronicEnergy (liouvilleTwin ε)
      (∑' d : ℕ, liouvilleTwin ε d / d) T) atTop atTop := by
  have hε0 : 0 < ε := by linarith [half_le_zetaZeroAbscissa]
  exact liouville_parityPair_of_moebius hε0 hε2
    (receiverBounded_moebius_of_zetaZeroAbscissa_sub_half_lt hε)

/-- **The set of admissible Liouville dampings coincides with `receiverDampings`.** -/
theorem setOf_pos_and_receiverBounded_liouville_eq_receiverDampings :
    {ε : ℝ | 0 < ε ∧ ReceiverBounded (dampedSignWeight RHTower.liouvilleR ε)} =
      receiverDampings := by
  ext ε
  constructor
  · rintro ⟨hε, hL⟩
    exact (mem_receiverDampings_iff_receiverBounded hε).mpr
      ((receiverBounded_moebius_iff_liouville hε).mpr hL)
  · intro hm
    exact ⟨hm.1, (receiverBounded_moebius_iff_liouville hm.1).mp
      ((mem_receiverDampings_iff_receiverBounded hm.1).mp hm)⟩

/-- **The Liouville receiver damping rate equals the zero width `Θ - 1/2`.** -/
theorem sInf_derivedSet_liouville_dampings_eq_zetaZeroAbscissa_sub_half :
    sInf (derivedSet {ε : ℝ | 0 < ε ∧ ReceiverBounded (dampedSignWeight RHTower.liouvilleR ε)}) =
      zetaZeroAbscissa - 1 / 2 := by
  rw [setOf_pos_and_receiverBounded_liouville_eq_receiverDampings, ← receiverDampingRate,
    receiverDampingRate_eq_zetaZeroAbscissa_sub_half]

/-- **All-damping Möbius and Liouville equivalences with the Riemann Hypothesis.** -/
theorem riemannHypothesis_iff_forall_pos_receiverBounded_moebius :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ReceiverBounded (pmPowerDampedRealWeight ε) := by
  constructor
  · intro hRH ε hε
    exact (mem_receiverDampings_iff_receiverBounded hε).mp
      (Ioi_zero_subset_receiverDampings_of_riemannHypothesis hRH hε)
  · intro h
    rw [riemannHypothesis_iff_cofinal_budget]
    intro δ hδ
    refine ⟨δ / 2, by linarith, by linarith, ?_⟩
    exact ((mem_receiverDampings_iff_receiverBounded (by linarith)).mpr (h (δ / 2) (by linarith))).2

theorem riemannHypothesis_iff_forall_pos_receiverBounded_liouville :
    RiemannHypothesis ↔
      ∀ ε : ℝ, 0 < ε → ReceiverBounded (dampedSignWeight RHTower.liouvilleR ε) := by
  rw [riemannHypothesis_iff_forall_pos_receiverBounded_moebius]
  exact forall₂_congr fun ε hε => receiverBounded_moebius_iff_liouville hε

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics

