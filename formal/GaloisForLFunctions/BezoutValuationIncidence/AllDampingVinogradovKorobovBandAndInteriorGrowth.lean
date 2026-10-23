import GaloisForLFunctions.BezoutValuationIncidence.TheReceiverEquivalenceAndZeroWidthLaw
import GaloisForLFunctions.BezoutValuationIncidence.ReceiverGrowthBelowHalfDampingAgainstThePeriodEnergy
import GaloisForLFunctions.BezoutValuationIncidence.ParityPairSeparatedOnTheVinogradovKorobovBand

/-!
# All-Damping Vinogradov–Korobov Band and Sub-Half-Damping Growth Laws for the Receiver

The unconditional sub-half-damping theorems of `ReceiverBoundedInTheZeroFreeBandBelowHalfDamping`,
`ReceiverBoundedInTheVinogradovKorobovBand`, `ParityPairSeparatedOnTheVinogradovKorobovBand`, and
`ReceiverGrowthBelowHalfDampingAgainstThePeriodEnergy` were restricted to `1/4 ≤ ε ≤ 1/2` because
their hyperbola rate-transfer lemma replaced `1/ε` by `4`.

This module eliminates the `1/4` barrier across the entire sub-half-damping range `0 < ε ≤ 1/2` and
transports every Vinogradov–Korobov band and growth estimate simultaneously to the actual discrete
energy `E_T(ε)`, the pure-interior pronic energy `E_T^{int}(ε)`, and the compensated Bézout interior
martingale bracket `2 M_T^{int}(ε) + 2 c^{int}(ε) H_T^{comp}`:

1. **All-Damping Hyperbola Rate Transfer (`abs_weightCenteredPrefix_dampedSign_le_of_linear_all_pos`)**:
   For every `0 < ε ≤ ½`, `1 ≤ D ≤ n`, and `|S(x)| ≤ Lx` from `D` on,
   `|A(n)| ≤ 3 D^{1−ε} + (13/ε) L n D^{−ε}`.
2. **All-Damping Vinogradov–Korobov Prefix Bounds
   (`exists_abs_weightCenteredPrefix_pmPowerDamped_le_vk_all_pos`,
   `exists_abs_pmBezoutInteriorPrefix_le_vk_all_pos`)**:
   There exist `K ≥ 0` and `N₁ : ℕ` such that for all `0 < ε ≤ ½` and `n ≥ N₁`,
   `|A_ε(n)| ≤ (K/ε) n^{1−ε} exp(−κ σ(n)/240)` and
   `|F_ε^{int}(n)| ≤ (K/ε + ½) n^{1−ε} exp(−κ σ(n)/240)`.
3. **All-Damping Vinogradov–Korobov Band Boundedness
   (`exists_receiver_le_on_vinogradovKorobovBand_of_pos`,
   `exists_interiorPronic_le_on_vinogradovKorobovBand_of_pos`,
   `exists_compensatedMartingale_le_on_vinogradovKorobovBand_of_pos`)**:
   For every damping floor `ε₀ ∈ (0, ½]`, `E_T(ε)`, `E_T^{int}(ε)`, and
   `2 M_T^{int}(ε) + 2 c^{int}(ε) H_T^{comp}` are bounded uniformly across all horizons `T` and all
   `ε ∈ [ε₀, ½]` on the Vinogradov–Korobov band `ε ≥ ½ − κ σ(T)/(480 log T)`.
4. **All-Damping Parity-Pair Separation on the Vinogradov–Korobov Band
   (`parityPair_separated_on_vinogradovKorobovBand_of_pos`)**:
   For every `ε₀ ∈ (0, ½]`, the damped Möbius receiver is uniformly bounded on the band while its
   Ramanujan-isometric parity twin grows at least as `c_{ε₀} (log(T+1) − log 100)`.
5. **All-Damping Sub-Half-Damping Growth and Period-Energy Cancellation
   (`eventually_receiver_le_growth_of_pos`,
   `eventually_interiorPronic_le_growth_of_pos`,
   `eventually_receiver_le_mul_periodEnergy_of_pos`,
   `eventually_interiorPronic_le_mul_periodEnergy_of_pos`)**:
   For **every** fixed `0 < ε < ½`, both `E_T(ε)` and `E_T^{int}(ε)` are bounded by
   `C_ε T^{1−2ε} exp(−κ σ(T)/270)` for all large `T`, and their ratios against the primitive period
   energy `E_prim(N)` decay as `O_ε(exp(−κ σ(N)/270)) → 0`.
-/

open Finset Filter Topology RHTower RHTower.Sieve
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. All-Damping Hyperbola Rate Transfer for `0 < ε ≤ 1/2` -/

/-- **All-damping rate hyperbola bound.** If `|s| ≤ 1` and `|S(x)| ≤ Lx` for `x ≥ D`, then for
every `0 < ε ≤ 1/2` and `1 ≤ D ≤ n`,
`|A(n)| ≤ 3 D^{1−ε} + (13/ε) L n D^{−ε}`. -/
theorem abs_weightCenteredPrefix_dampedSign_le_of_linear_all_pos
    {s : ℕ → ℝ} {L ε : ℝ} (hL : 0 ≤ L) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hs1 : ∀ d, |s d| ≤ 1) {n D : ℕ} (hD : 1 ≤ D) (hDn : D ≤ n)
    (hS : ∀ x, D ≤ x → |∑ e ∈ Icc 1 x, s e| ≤ L * x) :
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
  have hb : |∑ k ∈ Icc 1 n, ∑ d ∈ Ioc D (n / k), c d| ≤ 10 / ε * L * n * (D : ℝ) ^ (-ε) := by
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
      have h3 : (K : ℝ) ^ ε / ε ≤ ((n : ℝ) / D) ^ ε / ε :=
        div_le_div_of_nonneg_right (Real.rpow_le_rpow (Nat.cast_nonneg _) hKle hε.le) hε.le
      have h4 : (1 : ℝ) ≤ ((n : ℝ) / D) ^ ε / ε := by
        have h1pow : (1 : ℝ) ≤ ((n : ℝ) / D) ^ ε := Real.one_le_rpow hnD1 hε.le
        rw [le_div_iff₀ hε]
        linarith
      have h5 : 1 + ((n : ℝ) / D) ^ ε / ε ≤ (2 / ε) * ((n : ℝ) / D) ^ ε := by
        have hdiv : ((n : ℝ) / D) ^ ε / ε + ((n : ℝ) / D) ^ ε / ε = (2 / ε) * ((n : ℝ) / D) ^ ε := by
          ring
        linarith
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
      _ = 10 / ε * L * ((n : ℝ) ^ (1 - ε) * ((n : ℝ) / D) ^ ε) := by ring
      _ = 10 / ε * L * n * (D : ℝ) ^ (-ε) := by rw [hpow]; ring
  have hc : |(n : ℝ) * ∑' i : ℕ, c (i + (D + 1)) / ((i + (D + 1) : ℕ) : ℝ)| ≤
      3 / ε * L * n * (D : ℝ) ^ (-ε) := by
    have ht := (abs_tsum_tail_rpow_le_of_linear hD hL hε hs1 hS).2
    have heq : ∑' i : ℕ, c (i + (D + 1)) / ((i + (D + 1) : ℕ) : ℝ) =
        ∑' i : ℕ, ((i + (D + 1) : ℕ) : ℝ) ^ (-(1 + ε)) * s (i + (D + 1)) :=
      tsum_congr fun i => dampedSignWeight_div hε _
    have h3 : 2 + 1 / ε ≤ 3 / ε := by
      rw [div_add', le_div_iff₀ hε, div_mul_cancel₀ _ hε.ne']
      linarith
    have hDp : 0 ≤ L * (D : ℝ) ^ (-ε) := mul_nonneg hL (Real.rpow_nonneg hD0.le _)
    rw [heq, abs_mul, Nat.abs_cast]
    calc (n : ℝ) * |∑' i : ℕ, ((i + (D + 1) : ℕ) : ℝ) ^ (-(1 + ε)) * s (i + (D + 1))|
        ≤ n * ((2 + 1 / ε) * L * (D : ℝ) ^ (-ε)) := mul_le_mul_of_nonneg_left ht hn0.le
      _ ≤ n * (3 / ε * (L * (D : ℝ) ^ (-ε))) := by
          rw [mul_assoc (2 + 1 / ε)]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 hDp) hn0.le
      _ = 3 / ε * L * n * (D : ℝ) ^ (-ε) := by ring
  have hA : weightCenteredPrefix c (∑' d : ℕ, c d / d) n =
      (∑ d ∈ Icc 1 D, c d * ((n / d : ℕ) : ℝ) - n * ∑ d ∈ Icc 1 D, c d / d) +
        ∑ k ∈ Icc 1 n, ∑ d ∈ Ioc D (n / k), c d -
          (n : ℝ) * ∑' i : ℕ, c (i + (D + 1)) / ((i + (D + 1) : ℕ) : ℝ) := by
    rw [weightCenteredPrefix, sum_Icc_sum_divisors_eq_floor, hsplit, hlong, hmean]
    ring
  rw [hA]
  have hcomb : 10 / ε * L * n * (D : ℝ) ^ (-ε) + 3 / ε * L * n * (D : ℝ) ^ (-ε) =
      13 / ε * L * n * (D : ℝ) ^ (-ε) := by ring
  calc _ ≤ |∑ d ∈ Icc 1 D, c d * ((n / d : ℕ) : ℝ) - n * ∑ d ∈ Icc 1 D, c d / d| +
        |∑ k ∈ Icc 1 n, ∑ d ∈ Ioc D (n / k), c d| +
          |(n : ℝ) * ∑' i : ℕ, c (i + (D + 1)) / ((i + (D + 1) : ℕ) : ℝ)| := by
        refine (abs_sub _ _).trans ?_
        gcongr
        exact abs_add_le _ _
    _ ≤ _ := by linarith

/-- **Trivial all-damping prefix bound (`D = 1`, `L = 1`).** For every `0 < ε ≤ 1/2` and `n ≥ 1`,
`|A_ε(n)| ≤ 3 + (13/ε) n`. -/
theorem abs_weightCenteredPrefix_pmPowerDamped_le_trivial_all_pos
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) {n : ℕ} (hn : 1 ≤ n) :
    |weightCenteredPrefix (pmPowerDampedRealWeight ε) (dampedDensity ε) n| ≤
      3 + 13 / ε * n := by
  have hS : ∀ x, 1 ≤ x → |∑ e ∈ Icc 1 x, moebiusReal e| ≤ 1 * (x : ℝ) := by
    intro x _
    calc |∑ e ∈ Icc 1 x, moebiusReal e| ≤ ∑ e ∈ Icc 1 x, |moebiusReal e| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ _e ∈ Icc 1 x, (1 : ℝ) := sum_le_sum fun e _ => abs_moebiusReal_le_one' e
      _ = 1 * (x : ℝ) := by rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; push_cast; ring
  have h := abs_weightCenteredPrefix_dampedSign_le_of_linear_all_pos zero_le_one hε hε2
    abs_moebiusReal_le_one' le_rfl hn hS
  rw [← dampedDensity_eq_tsum hε, ← pmPowerDampedRealWeight_eq_dampedSignWeight] at h
  simpa using h

/-! ## §2. All-Damping Vinogradov–Korobov Prefix Bounds for `A_ε(n)` and `F_ε^{int}(n)` -/

/-- **All-Damping Vinogradov–Korobov Prefix Bound:**
There exist `K ≥ 0` and `N₁ : ℕ` such that for **every** `0 < ε ≤ 1/2` and every `n ≥ N₁`,
`|A_ε(n)| ≤ (K / ε) n^{1−ε} exp(−κ σ(n)/240)`. -/
theorem exists_abs_weightCenteredPrefix_pmPowerDamped_le_vk_all_pos :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N₁ : ℕ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∀ n : ℕ, N₁ ≤ n →
      |weightCenteredPrefix (pmPowerDampedRealWeight ε) (dampedDensity ε) n| ≤
        K / ε * (n : ℝ) ^ (1 - ε) * Real.exp (-(vkKappa * vkScale n / 240)) := by
  obtain ⟨B, hB, hev⟩ := exists_abs_sum_moebius_le_vk_rate
  have hevN := tendsto_natCast_atTop_atTop.eventually
    (hev.and (eventually_ge_atTop (Real.exp (Real.exp (25 / 9)))))
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hevN
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp
    ((tendsto_natCast_atTop_atTop.eventually (eventually_vk_conditions one_pos 0)).and
      ((hlog.eventually_ge_atTop (9 / 4 * Real.log (N₀ + 2))).and
        (hlog.eventually_ge_atTop (27 / 4))))
  refine ⟨3 + 26 * B, by positivity, N₁, fun ε hε hε2 n hn => ?_⟩
  obtain ⟨hvk, hℓN, hℓ3⟩ := hN₁ n hn
  obtain ⟨-, -, -, -, hsq, hle, -⟩ := hvk
  rw [log_vkHeight] at hsq hle
  set ℓ := Real.log n with hℓdef
  set g := vkKappa * vkScale n / 24 with hgdef
  have hn0 : (0 : ℝ) < n := by
    by_contra h
    have : (n : ℝ) = 0 := le_antisymm (not_lt.mp h) (Nat.cast_nonneg n)
    rw [hℓdef, this, Real.log_zero] at hℓ3; linarith
  have hg0 : 0 ≤ g := by have := Real.sqrt_nonneg ℓ; rw [hgdef]; linarith
  have hgℓ : g ≤ ℓ / 24 := by rw [hgdef]; linarith
  have hlog2 := Real.log_two_lt_d9
  set y := Real.exp (ℓ - g / 5) with hydef
  have hy0 : 0 < y := Real.exp_pos _
  have hlogy : Real.log y = ℓ - g / 5 := Real.log_exp _
  have hkey : 4 / 9 * ℓ ≤ ℓ - g / 5 - Real.log 2 := by nlinarith
  have hN2 : (0 : ℝ) < (N₀ : ℝ) + 2 := by positivity
  have hy2 : (N₀ : ℝ) + 2 ≤ y / 2 := by
    have h := Real.exp_le_exp.mpr (show Real.log ((N₀ : ℝ) + 2) ≤ ℓ - g / 5 - Real.log 2 by
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
      exact Real.exp_le_exp.mpr (by rw [← hℓdef]; linarith)
    exact_mod_cast hDy.trans hyn
  have hlogD_le : Real.log D ≤ ℓ - g / 5 := by
    rw [← hlogy]; exact Real.log_le_log hD0 hDy
  have hlogD_ge : ℓ - g / 5 - Real.log 2 ≤ Real.log D := by
    have h := Real.log_le_log (by positivity) hyD
    rwa [Real.log_div hy0.ne' (by norm_num), hlogy] at h
  have hgD : 4 / 9 * g ≤ vkKappa * vkScale D / 24 := by
    have h := four_ninths_mul_vkScale_le (x := n) (z := D) (by linarith) (by linarith) (by linarith)
    have hκ := vkKappa_pos
    rw [hgdef]; nlinarith
  set L := B * Real.exp (-(4 / 9 * g)) with hLdef
  have hL0 : 0 ≤ L := by positivity
  have hS : ∀ x, D ≤ x → |∑ e ∈ Icc 1 x, moebiusReal e| ≤ L * x := by
    intro x hx
    have hxR : (D : ℝ) ≤ x := by exact_mod_cast hx
    obtain ⟨hMx, -⟩ := hN₀ x (hDN₀.trans hx)
    obtain ⟨-, hDexp⟩ := hN₀ D hDN₀
    rw [Nat.floor_natCast, sum_range_moebius_eq_sum_Icc_moebiusReal] at hMx
    have hmono : vkScale D ≤ vkScale x := vkScale_le_vkScale hDexp hxR
    have hκ := vkKappa_pos
    have hexp : Real.exp (-(vkKappa * vkScale x / 24)) ≤ Real.exp (-(4 / 9 * g)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    calc _ ≤ B * x * Real.exp (-(vkKappa * vkScale x / 24)) := hMx
      _ ≤ B * x * Real.exp (-(4 / 9 * g)) := mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = L * x := by rw [hLdef]; ring
  have hhyp := abs_weightCenteredPrefix_dampedSign_le_of_linear_all_pos hL0 hε hε2
    (fun d => abs_moebiusReal_le_one' d) hD1 hDn hS
  rw [← dampedDensity_eq_tsum hε, ← pmPowerDampedRealWeight_eq_dampedSignWeight] at hhyp
  have hnpow : (n : ℝ) ^ (1 - ε) = Real.exp (ℓ * (1 - ε)) := Real.rpow_def_of_pos hn0 _
  have hshort : (D : ℝ) ^ (1 - ε) ≤ (n : ℝ) ^ (1 - ε) * Real.exp (-(g / 10)) := by
    rw [Real.rpow_def_of_pos hD0, hnpow, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hlong : (n : ℝ) * (D : ℝ) ^ (-ε) * Real.exp (-(4 / 9 * g)) ≤
      2 * ((n : ℝ) ^ (1 - ε) * Real.exp (-(g / 10))) := by
    rw [Real.rpow_def_of_pos hD0, hnpow, ← Real.exp_log hn0, ← hℓdef, ← Real.exp_add,
      ← Real.exp_add, ← Real.exp_add, ← Real.exp_log (by norm_num : (0 : ℝ) < 2), ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hsave : g / 10 = vkKappa * vkScale n / 240 := by rw [hgdef]; ring
  have h3ε : (3 : ℝ) ≤ 3 / ε := by rw [le_div_iff₀ hε]; linarith
  calc _ ≤ 3 * (D : ℝ) ^ (1 - ε) + 13 / ε * L * n * (D : ℝ) ^ (-ε) := hhyp
    _ = 3 * (D : ℝ) ^ (1 - ε) +
          (13 / ε * B) * ((n : ℝ) * (D : ℝ) ^ (-ε) * Real.exp (-(4 / 9 * g))) := by
        rw [hLdef]; ring
    _ ≤ (3 / ε) * ((n : ℝ) ^ (1 - ε) * Real.exp (-(g / 10))) +
          (13 / ε * B) * (2 * ((n : ℝ) ^ (1 - ε) * Real.exp (-(g / 10)))) :=
        add_le_add (mul_le_mul h3ε hshort (by positivity) (by positivity))
          (mul_le_mul_of_nonneg_left hlong (by positivity))
    _ = (3 + 26 * B) / ε * (n : ℝ) ^ (1 - ε) * Real.exp (-(vkKappa * vkScale n / 240)) := by
        rw [← hsave]; ring

/-! ## §3. All-Damping Vinogradov–Korobov Band Bounds for `E_T(ε)` and `E_T^{int}(ε)` -/

/-- **All-Damping Receiver Bound on the Vinogradov–Korobov Band:**
For every damping floor `ε₀ > 0`, there exists `E ≥ 0` such that `E_T(ε) ≤ E` for every horizon `T`
and every `ε ∈ [ε₀, 1/2]` on the Vinogradov–Korobov band
`ε ≥ 1/2 − κ σ(T)/(480 log T)`. -/
theorem exists_receiver_le_on_vinogradovKorobovBand_of_pos {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (T : ℕ) (ε : ℝ), ε₀ ≤ ε → ε ≤ 1 / 2 →
      1 / 2 - vkKappa * vkScale T / (480 * Real.log T) ≤ ε →
        RHTower.pmPowerDampedDivisorDiscreteEnergy ε T ≤ E := by
  obtain ⟨K, hK, N₂, hpre⟩ := exists_abs_weightCenteredPrefix_pmPowerDamped_le_vk_all_pos
  obtain ⟨N₃, hN₃⟩ := Filter.eventually_atTop.mp
    ((tendsto_natCast_atTop_atTop.eventually (eventually_vk_conditions one_pos 0)).and
      (tendsto_natCast_atTop_atTop.eventually
        (eventually_ge_atTop (Real.exp (Real.exp 1)))))
  set N₁ := max N₂ N₃
  have hsum := GaloisForLFunctions.HTGeometry.summable_exp_neg_sqrt_log_div
    (show (0 : ℝ) < 1 / 120 by norm_num)
  set S := ∑' m : ℕ, Real.exp (-(1 / 120 * Real.sqrt (Real.log m))) / m
  have hS0 : 0 ≤ S := tsum_nonneg fun m => by positivity
  refine ⟨(N₁ : ℝ) * (3 + 13 / ε₀ * N₁) ^ 2 + (K / ε₀) ^ 2 * S, by positivity,
    fun T ε hε_ge hε2 hband => ?_⟩
  have hε : 0 < ε := hε₀.trans_le hε_ge
  rw [← weightPronicEnergy_pmPowerDamped, weightPronicEnergy]
  set f := fun n : ℕ => weightCenteredPrefix (pmPowerDampedRealWeight ε) (dampedDensity ε) n ^ 2 /
    ((n : ℝ) * ((n : ℝ) + 1)) with hfdef
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
      have hA := abs_weightCenteredPrefix_pmPowerDamped_le_trivial_all_pos hε hε2 hn.1.1
      have h13 : 13 / ε ≤ 13 / ε₀ := div_le_div_of_nonneg_left (by norm_num) hε₀ hε_ge
      have hA' : |weightCenteredPrefix (pmPowerDampedRealWeight ε) (dampedDensity ε) n| ≤
          3 + 13 / ε₀ * N₁ := by
        have hnN : (n : ℝ) ≤ N₁ := by exact_mod_cast hn.2.le
        have := mul_le_mul h13 hnN (Nat.cast_nonneg n) (by positivity)
        linarith
      have hA2 : weightCenteredPrefix (pmPowerDampedRealWeight ε) (dampedDensity ε) n ^ 2 ≤
          (3 + 13 / ε₀ * N₁) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hA' 2
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
        f n ≤ (K / ε₀) ^ 2 * (Real.exp (-(1 / 120 * Real.sqrt (Real.log n))) / n) := by
      intro n hn
      simp only [mem_filter, mem_Icc, not_lt] at hn
      have hn2 : N₂ ≤ n := le_trans (le_max_left _ _) hn.2
      have hn3 : N₃ ≤ n := le_trans (le_max_right _ _) hn.2
      obtain ⟨hvk, hnexp⟩ := hN₃ n hn3
      obtain ⟨-, -, -, -, hsq, -⟩ := hvk
      rw [log_vkHeight] at hsq
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1.1
      have hn0 : (0 : ℝ) < n := by linarith
      have hnT : (n : ℝ) ≤ T := by exact_mod_cast hn.1.2
      set ℓ := Real.log n with hℓ
      have hℓe : Real.exp 1 ≤ ℓ := by
        rw [hℓ, ← Real.log_exp (Real.exp 1)]; exact Real.log_le_log (Real.exp_pos _) hnexp
      have hℓ0 : 0 < ℓ := lt_of_lt_of_le (Real.exp_pos 1) hℓe
      have hlogT : ℓ ≤ Real.log T := Real.log_le_log hn0 hnT
      have hA := (hpre ε hε hε2 n hn2).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hKε (Real.rpow_nonneg hn0.le _)) (Real.exp_pos _).le)
      set s := vkKappa * vkScale n / 240 with hsdef
      have hA2 : weightCenteredPrefix (pmPowerDampedRealWeight ε) (dampedDensity ε) n ^ 2 ≤
          (K / ε₀ * (n : ℝ) ^ (1 - ε) * Real.exp (-s)) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hA 2
      have hratio : vkScale T / Real.log T ≤ vkScale n / ℓ := vkScale_div_log_le hnexp hnT
      have hbandn : (1 - 2 * ε) * ℓ ≤ s := by
        have hb : 1 - 2 * ε ≤ vkKappa / 240 * (vkScale T / Real.log T) := by
          have : vkKappa / 240 * (vkScale T / Real.log T) =
              2 * (vkKappa * vkScale T / (480 * Real.log T)) := by ring
          rw [this]; linarith
        have hκ := vkKappa_pos
        calc (1 - 2 * ε) * ℓ ≤ vkKappa / 240 * (vkScale T / Real.log T) * ℓ :=
              mul_le_mul_of_nonneg_right hb hℓ0.le
          _ ≤ vkKappa / 240 * (vkScale n / ℓ) * ℓ := by gcongr
          _ = s := by rw [hsdef]; field_simp
      have hs_sqrt : 1 / 120 * Real.sqrt ℓ ≤ s := by rw [hsdef]; linarith
      have hpow : ((n : ℝ) ^ (1 - ε)) ^ 2 * Real.exp (-s) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
          Real.exp (-(1 / 120 * Real.sqrt ℓ)) / n := by
        have hnpow : ((n : ℝ) ^ (1 - ε)) ^ 2 = Real.exp (2 * ((1 - ε) * ℓ)) := by
          rw [Real.rpow_def_of_pos hn0, ← Real.exp_nat_mul, hℓ]; congr 1; push_cast; ring
        have hex : Real.exp (-s) ^ 2 = Real.exp (-(2 * s)) := by
          rw [← Real.exp_nat_mul]; push_cast; ring_nf
        rw [hnpow, hex, ← Real.exp_add]
        rw [div_le_div_iff₀ (by positivity) hn0]
        have hnn : (n : ℝ) * (n : ℝ) ≤ (n : ℝ) * ((n : ℝ) + 1) := by nlinarith
        have hnexp' : (n : ℝ) = Real.exp ℓ := (Real.exp_log hn0).symm
        calc Real.exp (2 * ((1 - ε) * ℓ) + -(2 * s)) * n
            = Real.exp (-s) * ((n : ℝ) * (n : ℝ)) * Real.exp ((1 - 2 * ε) * ℓ - s) := by
              rw [hnexp', ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
              congr 1; ring
          _ ≤ Real.exp (-(1 / 120 * Real.sqrt ℓ)) * ((n : ℝ) * (n : ℝ)) * 1 := by
              gcongr
              · linarith
              · exact Real.exp_le_one_iff.mpr (by linarith)
          _ ≤ Real.exp (-(1 / 120 * Real.sqrt ℓ)) * ((n : ℝ) * ((n : ℝ) + 1)) := by
              rw [mul_one]; exact mul_le_mul_of_nonneg_left hnn (Real.exp_pos _).le
      calc f n ≤ (K / ε₀ * (n : ℝ) ^ (1 - ε) * Real.exp (-s)) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) :=
            div_le_div_of_nonneg_right hA2 (by positivity)
        _ = (K / ε₀) ^ 2 * (((n : ℝ) ^ (1 - ε)) ^ 2 * Real.exp (-s) ^ 2 /
              ((n : ℝ) * ((n : ℝ) + 1))) := by ring
        _ ≤ (K / ε₀) ^ 2 * (Real.exp (-(1 / 120 * Real.sqrt (Real.log n))) / n) :=
            mul_le_mul_of_nonneg_left hpow (sq_nonneg _)
    calc ∑ n ∈ Icc 1 T with ¬ n < N₁, f n
        ≤ ∑ n ∈ Icc 1 T with ¬ n < N₁,
            (K / ε₀) ^ 2 * (Real.exp (-(1 / 120 * Real.sqrt (Real.log n))) / n) :=
          sum_le_sum hterm
      _ = (K / ε₀) ^ 2 * ∑ n ∈ Icc 1 T with ¬ n < N₁,
            Real.exp (-(1 / 120 * Real.sqrt (Real.log n))) / n := by rw [mul_sum]
      _ ≤ (K / ε₀) ^ 2 * S := mul_le_mul_of_nonneg_left
          (hsum.sum_le_tsum _ fun m _ => by positivity) (sq_nonneg _)
  linarith

/-- **All-Damping Pure-Interior Pronic Energy Bound on the Vinogradov–Korobov Band:**
For every damping floor `ε₀ > 0`, there exists `E ≥ 0` such that
`pmBezoutInteriorPronicEnergy ε T ≤ E` for all `T : ℕ` and all `ε ∈ [ε₀, 1/2]` on the
Vinogradov–Korobov band `ε ≥ 1/2 − κ σ(T)/(480 log T)`. -/
theorem exists_interiorPronic_le_on_vinogradovKorobovBand_of_pos {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (T : ℕ) (ε : ℝ), ε₀ ≤ ε → ε ≤ 1 / 2 →
      1 / 2 - vkKappa * vkScale T / (480 * Real.log T) ≤ ε →
        pmBezoutInteriorPronicEnergy ε T ≤ E := by
  obtain ⟨E, hE0, hE⟩ := exists_receiver_le_on_vinogradovKorobovBand_of_pos hε₀
  refine ⟨E + Real.sqrt E + 1 / 4, by positivity, fun T ε hε_ge hε2 hband => ?_⟩
  have hε0 : 0 ≤ ε := (hε₀.trans_le hε_ge).le
  have hstep := pmBezoutInteriorPronicEnergy_le_discreteEnergy_add_sqrt_add_quarter hε0 T
  have hET := hE T ε hε_ge hε2 hband
  have hsq := Real.sqrt_le_sqrt hET
  linarith

/-! ## §4. All-Damping Parity-Pair Separation on the Vinogradov–Korobov Band -/

/-- The twin's drift constant at damping floor `ε₀`: `K⋆(ε₀) = ρ_{ε₀} / U_{ε₀} > 0`. -/
def twinDriftConstantAt (ε₀ : ℝ) : ℝ := dampedDensity ε₀ / parityTwinCoprimeMass ε₀ 1

theorem twinDriftConstantAt_pos {ε₀ : ℝ} (hε₀ : 0 < ε₀) : 0 < twinDriftConstantAt ε₀ :=
  div_pos (RHTower.pmPowerDampedDivisorDensity_re_pos hε₀)
    (parityTwinCoprimeMass_one_pos hε₀)

theorem twinDriftConstantAt_le {ε₀ ε : ℝ} (hε₀ : 0 < ε₀) (hε : ε₀ ≤ ε) :
    twinDriftConstantAt ε₀ ≤ dampedDensity ε / parityTwinCoprimeMass ε 1 := by
  unfold twinDriftConstantAt
  exact div_le_div₀ (RHTower.pmPowerDampedDivisorDensity_re_pos (hε₀.trans_le hε)).le
    (dampedDensity_le_dampedDensity hε₀ hε) (parityTwinCoprimeMass_one_pos (hε₀.trans_le hε))
    (parityTwinCoprimeMass_one_le hε₀ hε)

/-- **The parity twin's receiver on `[ε₀, 1/2]`.** For any `ε₀ > 0` and `ε ∈ [ε₀, 1/2]`,
`(K⋆(ε₀)/16)² / 4 · (log(T+1) − log 100) ≤ E_T(c'_ε)`. -/
theorem parityTwin_receiver_ge_of_pos {ε₀ ε : ℝ} (hε₀ : 0 < ε₀) (hε_ge : ε₀ ≤ ε)
    (hε2 : ε ≤ 1 / 2) (T : ℕ) :
    (twinDriftConstantAt ε₀ / 16) ^ 2 / 4 * (Real.log ((T : ℝ) + 1) - Real.log 100) ≤
      weightPronicEnergy (parityTwinWeight ε) (dampedDensity ε) T := by
  have hε : 0 < ε := hε₀.trans_le hε_ge
  set c := (twinDriftConstantAt ε₀ / 16) ^ 2 / 4 with hcdef
  have hc0 : 0 ≤ c := by positivity
  have hK0 := twinDriftConstantAt_pos hε₀
  have hcell : ∀ n : ℕ, 100 ≤ n → c * (1 / (n : ℝ)) ≤
      weightCenteredPrefix (parityTwinWeight ε) (dampedDensity ε) n ^ 2 /
        ((n : ℝ) * ((n : ℝ) + 1)) := by
    intro n hn
    have hdrift : twinDriftConstantAt ε₀ / 16 * n * (2 * (n : ℝ)) ^ (-ε) ≤
        (n : ℝ) * ∑ d ∈ Ioc n (2 * n), parityTwinWeight ε d / d := by
      refine le_trans ?_ (parityTwin_drift_ge hε hn)
      have hK := twinDriftConstantAt_le hε₀ hε_ge
      have hP : 0 ≤ (n : ℝ) * (2 * (n : ℝ)) ^ (-ε) :=
        mul_nonneg (Nat.cast_nonneg n) (Real.rpow_nonneg (by positivity) _)
      nlinarith
    have h := weightCell_ge_of_drift (parityTwinWeight_nonneg hε) (hasSum_parityTwinWeight_div hε)
      (by positivity) hε2 (by omega) hdrift
    rw [hcdef]
    calc (twinDriftConstantAt ε₀ / 16) ^ 2 / 4 * (1 / (n : ℝ)) =
        (twinDriftConstantAt ε₀ / 16) ^ 2 / 4 / n := by ring
      _ ≤ _ := h
  rw [weightPronicEnergy]
  rcases lt_or_ge T 99 with hT | hT
  · have hlog : Real.log ((T : ℝ) + 1) ≤ Real.log 100 :=
      Real.log_le_log (by positivity)
        (by have : (T : ℝ) ≤ 98 := by exact_mod_cast (by omega : T ≤ 98)
            linarith)
    have hnn : 0 ≤ ∑ n ∈ Icc 1 T, weightCenteredPrefix (parityTwinWeight ε) (dampedDensity ε) n ^ 2 /
        ((n : ℝ) * ((n : ℝ) + 1)) := sum_nonneg fun n _ => by positivity
    nlinarith
  · have hsub : Icc 100 T ⊆ Icc 1 T := Icc_subset_Icc (by norm_num) le_rfl
    have hlog := log_sub_log_le_sum_Icc_inv (a := 100) (by norm_num) (T := T) (by omega)
    push_cast at hlog
    calc c * (Real.log ((T : ℝ) + 1) - Real.log 100) ≤ c * ∑ n ∈ Icc 100 T, (1 : ℝ) / n :=
          mul_le_mul_of_nonneg_left hlog hc0
      _ = ∑ n ∈ Icc 100 T, c * (1 / (n : ℝ)) := by rw [mul_sum]
      _ ≤ ∑ n ∈ Icc 100 T, weightCenteredPrefix (parityTwinWeight ε) (dampedDensity ε) n ^ 2 /
            ((n : ℝ) * ((n : ℝ) + 1)) :=
          sum_le_sum fun n hn => hcell n (mem_Icc.mp hn).1
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => by positivity

/-- **All-Damping Parity-Pair Separation on the Vinogradov–Korobov Band:**
For every damping floor `ε₀ > 0`, there exist `E ≥ 0` and `c > 0` such that on the band
`ε₀ ≤ ε ≤ 1/2`, `ε ≥ 1/2 − κ σ(T)/(480 log T)`, the damped Möbius receiver satisfies
`E_T(c_ε) ≤ E` while its Ramanujan-isometric parity twin satisfies
`E_T(c'_ε) ≥ c (log(T+1) − log 100)`. -/
theorem parityPair_separated_on_vinogradovKorobovBand_of_pos {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    (∀ ε : ℝ, 0 < ε → ∀ e : ℕ, 0 < e →
      |weightRamanujanCoeff (parityTwinWeight ε) e| =
        |weightRamanujanCoeff (pmPowerDampedRealWeight ε) e|) ∧
    ∃ E c : ℝ, 0 < c ∧ ∀ (T : ℕ) (ε : ℝ), ε₀ ≤ ε → ε ≤ 1 / 2 →
      1 / 2 - vkKappa * vkScale T / (480 * Real.log T) ≤ ε →
        weightPronicEnergy (pmPowerDampedRealWeight ε) (dampedDensity ε) T ≤ E ∧
        c * (Real.log ((T : ℝ) + 1) - Real.log 100) ≤
          weightPronicEnergy (parityTwinWeight ε) (dampedDensity ε) T := by
  refine ⟨fun ε hε e he => abs_weightRamanujanCoeff_parityTwin hε he, ?_⟩
  obtain ⟨E, _, hE⟩ := exists_receiver_le_on_vinogradovKorobovBand_of_pos hε₀
  refine ⟨E, (twinDriftConstantAt ε₀ / 16) ^ 2 / 4,
    by have := twinDriftConstantAt_pos hε₀; positivity,
    fun T ε h_ge h2 hb => ⟨?_, parityTwin_receiver_ge_of_pos hε₀ h_ge h2 T⟩⟩
  rw [weightPronicEnergy_pmPowerDamped]
  exact hE T ε h_ge h2 hb

/-! ## §5. All-Damping Sub-Half-Damping Growth Laws (`0 < ε < 1/2`) -/

/-- Cells below `N` carry at most `N (3 + (13/ε) N)²` in total for every `0 < ε ≤ 1/2`. -/
theorem sum_receiverCell_lt_le_of_pos {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (T N : ℕ) :
    ∑ n ∈ Icc 1 T with n < N, receiverCell ε n ≤ (N : ℝ) * (3 + 13 / ε * N) ^ 2 := by
  have hsub : (Icc 1 T).filter (fun n => n < N) ⊆ range N := fun n hn => by
    simp only [mem_filter, mem_range] at hn ⊢; exact hn.2
  have hterm : ∀ n ∈ (Icc 1 T).filter (fun n => n < N),
      receiverCell ε n ≤ (3 + 13 / ε * N) ^ 2 := by
    intro n hn
    simp only [mem_filter, mem_Icc] at hn
    have hA := abs_weightCenteredPrefix_pmPowerDamped_le_trivial_all_pos hε hε2 hn.1.1
    have hA2 : weightCenteredPrefix (pmPowerDampedRealWeight ε) (dampedDensity ε) n ^ 2 ≤
        (3 + 13 / ε * N) ^ 2 := by
      rw [← sq_abs]
      refine pow_le_pow_left₀ (abs_nonneg _) (hA.trans ?_) 2
      have hnN : (n : ℝ) ≤ N := by exact_mod_cast hn.2.le
      have := mul_le_mul_of_nonneg_left hnN (by positivity : (0 : ℝ) ≤ 13 / ε)
      linarith
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1.1
    unfold receiverCell
    rw [div_le_iff₀ (by positivity)]
    exact hA2.trans (le_mul_of_one_le_right (sq_nonneg _) (by nlinarith))
  calc ∑ n ∈ Icc 1 T with n < N, receiverCell ε n
      ≤ ∑ n ∈ Icc 1 T with n < N, (3 + 13 / ε * (N : ℝ)) ^ 2 := sum_le_sum hterm
    _ = (((Icc 1 T).filter (fun n => n < N)).card : ℝ) * (3 + 13 / ε * N) ^ 2 := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) * (3 + 13 / ε * N) ^ 2 := mul_le_mul_of_nonneg_right
        (by exact_mod_cast (card_le_card hsub).trans (card_range N).le) (sq_nonneg _)

theorem sum_Icc_rpow_neg_two_mul_le_of_pos {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) (X : ℕ) :
    ∑ n ∈ Icc 1 X, (n : ℝ) ^ (-(2 * ε)) ≤ 1 + (X : ℝ) ^ (1 - 2 * ε) / (1 - 2 * ε) :=
  RHTower.sum_rpow_neg_head_le (c := 2 * ε) (by linarith) (by linarith) X

theorem sum_receiverCell_mid_le_of_pos {ε K : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) {N T : ℕ}
    (hcell : ∀ n, N ≤ n → receiverCell ε n ≤ K ^ 2 * (n : ℝ) ^ (-(2 * ε))) :
    ∑ n ∈ (Icc 1 T).filter (fun n => ¬ n < N) with n * n ≤ T, receiverCell ε n ≤
      K ^ 2 * (1 + (T : ℝ) ^ ((1 - 2 * ε) / 2) / (1 - 2 * ε)) := by
  have ha0 : 0 < 1 - 2 * ε := by linarith
  have hsub : ((Icc 1 T).filter (fun n => ¬ n < N)).filter (fun n => n * n ≤ T) ⊆
      Icc 1 (Nat.sqrt T) := fun n hn => by
    simp only [mem_filter, mem_Icc] at hn ⊢
    exact ⟨hn.1.1.1, Nat.le_sqrt.mpr hn.2⟩
  calc _ ≤ ∑ n ∈ ((Icc 1 T).filter (fun n => ¬ n < N)).filter (fun n => n * n ≤ T),
          K ^ 2 * (n : ℝ) ^ (-(2 * ε)) :=
        sum_le_sum fun n hn => hcell n (not_lt.mp (mem_filter.mp (mem_filter.mp hn).1).2)
    _ ≤ ∑ n ∈ Icc 1 (Nat.sqrt T), K ^ 2 * (n : ℝ) ^ (-(2 * ε)) :=
        sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => by positivity
    _ = K ^ 2 * ∑ n ∈ Icc 1 (Nat.sqrt T), (n : ℝ) ^ (-(2 * ε)) := by rw [mul_sum]
    _ ≤ K ^ 2 * (1 + (T : ℝ) ^ ((1 - 2 * ε) / 2) / (1 - 2 * ε)) := by
        refine mul_le_mul_of_nonneg_left ((sum_Icc_rpow_neg_two_mul_le_of_pos hε hε2 _).trans ?_)
          (sq_nonneg K)
        have := div_le_div_of_nonneg_right (natSqrt_rpow_le ha0.le T) ha0.le
        linarith

theorem sum_receiverCell_top_le_of_pos {ε K s : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) {N T : ℕ}
    (hcell : ∀ n, N ≤ n → n ≤ T → T < n * n →
      receiverCell ε n ≤ K ^ 2 * ((n : ℝ) ^ (-(2 * ε)) * Real.exp (-s))) :
    ∑ n ∈ (Icc 1 T).filter (fun n => ¬ n < N) with ¬ n * n ≤ T, receiverCell ε n ≤
      K ^ 2 * Real.exp (-s) * (1 + (T : ℝ) ^ (1 - 2 * ε) / (1 - 2 * ε)) := by
  calc _ ≤ ∑ n ∈ ((Icc 1 T).filter (fun n => ¬ n < N)).filter (fun n => ¬ n * n ≤ T),
          K ^ 2 * ((n : ℝ) ^ (-(2 * ε)) * Real.exp (-s)) := by
        refine sum_le_sum fun n hn => ?_
        simp only [mem_filter, mem_Icc, not_lt, not_le] at hn
        exact hcell n hn.1.2 hn.1.1.2 hn.2
    _ ≤ ∑ n ∈ Icc 1 T, K ^ 2 * ((n : ℝ) ^ (-(2 * ε)) * Real.exp (-s)) :=
        sum_le_sum_of_subset_of_nonneg (fun n hn => (mem_filter.mp (mem_filter.mp hn).1).1)
          fun n _ _ => by positivity
    _ = K ^ 2 * Real.exp (-s) * ∑ n ∈ Icc 1 T, (n : ℝ) ^ (-(2 * ε)) := by
        rw [mul_sum]; exact sum_congr rfl fun n _ => by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_Icc_rpow_neg_two_mul_le_of_pos hε hε2 T) (by positivity)

/-- **All-Damping Growth of the Receiver Below Half Damping:**
For **every** `0 < ε < 1/2`, there exists `C ≥ 0` such that
`E_T(ε) ≤ C T^{1−2ε} exp(−κ σ(T)/270)` for all large `T`. -/
theorem eventually_receiver_le_growth_of_pos {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℕ in atTop, RHTower.pmPowerDampedDivisorDiscreteEnergy ε T ≤
      C * (T : ℝ) ^ (1 - 2 * ε) * Real.exp (-(vkKappa * vkScale T / 270)) := by
  obtain ⟨K₀, hK₀, N₀, hpre₀⟩ := exists_abs_weightCenteredPrefix_pmPowerDamped_le_vk_all_pos
  set K := K₀ / ε
  set N := max N₀ 3
  have hN3 : 3 ≤ N := le_max_right _ _
  have hκ := vkKappa_pos
  have hcell : ∀ n, N ≤ n → receiverCell ε n ≤
      K ^ 2 * ((n : ℝ) ^ (-(2 * ε)) * Real.exp (-(2 * (vkKappa * vkScale n / 240)))) :=
    fun n hn => receiverCell_le_of_abs_le (by omega)
      (hpre₀ ε hε hε2.le n (le_trans (le_max_left _ _) hn))
  have hcell' : ∀ n, N ≤ n → receiverCell ε n ≤ K ^ 2 * (n : ℝ) ^ (-(2 * ε)) := by
    intro n hn
    have hvk := vkScale_nonneg (one_le_log_natCast_of_three_le (n := n) (hN3.trans hn))
    refine (hcell n hn).trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg K))
    exact mul_le_of_le_one_right (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (Real.exp_le_one_iff.mpr (by nlinarith))
  set a := 1 - 2 * ε with hadef
  have ha0 : 0 < a := by rw [hadef]; linarith
  set C₀ := (N : ℝ) * (3 + 13 / ε * N) ^ 2
  have hC₀ : 0 ≤ C₀ := by positivity
  refine ⟨C₀ + 2 * K ^ 2 + 2 * K ^ 2 / a, by positivity, ?_⟩
  have hratio := (tendsto_vkScale_div_log.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_le_nhds (show (0 : ℝ) < a * 270 / (2 * vkKappa) by positivity))
  have hlog : Tendsto (fun T : ℕ => Real.log T) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hratio, hlog.eventually_ge_atTop 3,
    (tendsto_natCast_atTop_atTop.eventually (eventually_vk_conditions one_pos 0))]
    with T hTr hT3 hvkT
  obtain ⟨-, -, -, -, hsqT, -⟩ := hvkT
  rw [log_vkHeight] at hsqT
  simp only [Function.comp_apply] at hTr
  have hT0 : (0 : ℝ) < T := by
    by_contra h
    have : (T : ℝ) = 0 := le_antisymm (not_lt.mp h) (Nat.cast_nonneg T)
    rw [this, Real.log_zero] at hT3; linarith
  set s := vkKappa * vkScale T / 270 with hsdef
  have hs0 : 0 ≤ s := by rw [hsdef]; have := Real.sqrt_nonneg (Real.log T); nlinarith
  have hsa : s ≤ a / 2 * Real.log T := by
    have hσ' : vkScale T ≤ a * 270 / (2 * vkKappa) * Real.log T := by
      rwa [div_le_iff₀ (by linarith)] at hTr
    rw [hsdef]
    calc vkKappa * vkScale T / 270 ≤ vkKappa * (a * 270 / (2 * vkKappa) * Real.log T) / 270 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hσ' hκ.le) (by norm_num)
      _ = a / 2 * Real.log T := by field_simp
  set G := (T : ℝ) ^ a * Real.exp (-s) with hGdef
  have hGsq : (T : ℝ) ^ (a / 2) ≤ G := by
    rw [hGdef, Real.rpow_def_of_pos hT0, Real.rpow_def_of_pos hT0, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hG1 : 1 ≤ G := le_trans (Real.one_le_rpow (by
    have := Real.add_one_le_exp (Real.log T)
    rw [Real.exp_log hT0] at this; linarith) (by positivity)) hGsq
  have hsplit : ∑ n ∈ Icc 1 T, receiverCell ε n = ∑ n ∈ Icc 1 T with n < N, receiverCell ε n +
      (∑ n ∈ (Icc 1 T).filter (fun n => ¬ n < N) with n * n ≤ T, receiverCell ε n +
        ∑ n ∈ (Icc 1 T).filter (fun n => ¬ n < N) with ¬ n * n ≤ T, receiverCell ε n) := by
    rw [sum_filter_add_sum_filter_not, sum_filter_add_sum_filter_not]
  rw [pmPowerDampedDivisorDiscreteEnergy_eq_sum_receiverCell, hsplit]
  have h1 : ∑ n ∈ Icc 1 T with n < N, receiverCell ε n ≤ C₀ :=
    sum_receiverCell_lt_le_of_pos hε hε2.le T N
  have h2 := sum_receiverCell_mid_le_of_pos hε hε2 (T := T) hcell'
  have h3 := sum_receiverCell_top_le_of_pos (s := s) hε hε2 (N := N) (T := T) fun n hn hnT hsq => by
    refine (hcell n hn).trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (sq_nonneg K))
    have := vkScale_comparable_of_sq_gt (by omega) hnT hsq hT3
    rw [hsdef]; nlinarith
  rw [← hadef] at h2 h3
  have hmid : K ^ 2 * (1 + (T : ℝ) ^ (a / 2) / a) ≤ K ^ 2 * (1 + G / a) :=
    mul_le_mul_of_nonneg_left (by have := div_le_div_of_nonneg_right hGsq ha0.le; linarith)
      (sq_nonneg K)
  have htop : K ^ 2 * Real.exp (-s) * (1 + (T : ℝ) ^ a / a) ≤ K ^ 2 * (1 + G / a) := by
    have hes : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hGe : Real.exp (-s) * ((T : ℝ) ^ a / a) = G / a := by rw [hGdef]; ring
    calc K ^ 2 * Real.exp (-s) * (1 + (T : ℝ) ^ a / a)
        = K ^ 2 * Real.exp (-s) + K ^ 2 * (Real.exp (-s) * ((T : ℝ) ^ a / a)) := by ring
      _ = K ^ 2 * Real.exp (-s) + K ^ 2 * (G / a) := by rw [hGe]
      _ ≤ K ^ 2 * 1 + K ^ 2 * (G / a) :=
          add_le_add (mul_le_mul_of_nonneg_left hes (sq_nonneg K)) le_rfl
      _ = K ^ 2 * (1 + G / a) := by ring
  have hdiff : (C₀ + 2 * K ^ 2 + 2 * K ^ 2 / a) * G -
      (C₀ + K ^ 2 * (1 + G / a) + K ^ 2 * (1 + G / a)) = (C₀ + 2 * K ^ 2) * (G - 1) := by
    field_simp; ring
  have hpos := mul_nonneg (add_nonneg hC₀ (by positivity : (0 : ℝ) ≤ 2 * K ^ 2))
    (sub_nonneg.mpr hG1)
  have hfin : (C₀ + 2 * K ^ 2 + 2 * K ^ 2 / a) * G =
      (C₀ + 2 * K ^ 2 + 2 * K ^ 2 / a) * (T : ℝ) ^ a * Real.exp (-s) := by rw [hGdef]; ring
  linarith

/-- **All-Damping Growth of the Pure-Interior Pronic Energy Below Half Damping:**
For **every** `0 < ε < 1/2`, there exists `C ≥ 0` such that
`pmBezoutInteriorPronicEnergy ε T ≤ C T^{1−2ε} exp(−κ σ(T)/270)` for all large `T`. -/
theorem eventually_interiorPronic_le_growth_of_pos {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℕ in atTop, pmBezoutInteriorPronicEnergy ε T ≤
      C * (T : ℝ) ^ (1 - 2 * ε) * Real.exp (-(vkKappa * vkScale T / 270)) := by
  obtain ⟨C, hC0, hC⟩ := eventually_receiver_le_growth_of_pos hε hε2
  set a := 1 - 2 * ε with hadef
  have ha0 : 0 < a := by rw [hadef]; linarith
  have hκ := vkKappa_pos
  have hratio := (tendsto_vkScale_div_log.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_le_nhds (show (0 : ℝ) < a * 270 / (2 * vkKappa) by positivity))
  have hlog : Tendsto (fun T : ℕ => Real.log T) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨2 * C + 1 / 2, by positivity, ?_⟩
  filter_upwards [hC, hratio, hlog.eventually_ge_atTop 3] with T hET hTr hT3
  simp only [Function.comp_apply] at hTr
  have hT0 : (0 : ℝ) < T := by
    by_contra h
    have : (T : ℝ) = 0 := le_antisymm (not_lt.mp h) (Nat.cast_nonneg T)
    rw [this, Real.log_zero] at hT3; linarith
  set s := vkKappa * vkScale T / 270 with hsdef
  have hsa : s ≤ a / 2 * Real.log T := by
    have hσ' : vkScale T ≤ a * 270 / (2 * vkKappa) * Real.log T := by
      rwa [div_le_iff₀ (by linarith)] at hTr
    rw [hsdef]
    calc vkKappa * vkScale T / 270 ≤ vkKappa * (a * 270 / (2 * vkKappa) * Real.log T) / 270 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hσ' hκ.le) (by norm_num)
      _ = a / 2 * Real.log T := by field_simp
  set G := (T : ℝ) ^ a * Real.exp (-s) with hGdef
  have hGsq : (T : ℝ) ^ (a / 2) ≤ G := by
    rw [hGdef, Real.rpow_def_of_pos hT0, Real.rpow_def_of_pos hT0, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hG1 : 1 ≤ G := le_trans (Real.one_le_rpow (by
    have := Real.add_one_le_exp (Real.log T)
    rw [Real.exp_log hT0] at this; linarith) (by positivity)) hGsq
  have hint := pmBezoutInteriorPronicEnergy_le_two_mul_discreteEnergy_add_half hε.le T
  calc pmBezoutInteriorPronicEnergy ε T
      ≤ 2 * (C * G) + 1 / 2 := by
        have hET' : pmPowerDampedDivisorDiscreteEnergy ε T ≤ C * G := by
          rw [hGdef, ← hadef, ← hsdef]; exact le_trans hET (le_of_eq (by ring))
        linarith
    _ ≤ 2 * (C * G) + (1 / 2) * G := by linarith
    _ = (2 * C + 1 / 2) * (T : ℝ) ^ (1 - 2 * ε) * Real.exp (-(vkKappa * vkScale T / 270)) := by
        rw [hGdef, ← hadef, ← hsdef]; ring

/-- **All-Damping Receiver Ratio Against the Period Energy (`0 < ε < 1/2`):**
For **every** `0 < ε < 1/2`, there exists `C ≥ 0` such that for all large `N`,
`E_N(ε) ≤ C exp(−κ σ(N)/270) E_prim(N)`. -/
theorem eventually_receiver_le_mul_periodEnergy_of_pos {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop, RHTower.pmPowerDampedDivisorDiscreteEnergy ε N ≤
      C * Real.exp (-(vkKappa * vkScale N / 270)) *
        sievePrimitiveEnergy N (pmPowerDampedRealWeight ε) := by
  obtain ⟨C, hC0, hC⟩ := eventually_receiver_le_growth_of_pos hε hε2
  refine ⟨10368 * C, by positivity, ?_⟩
  filter_upwards [hC, eventually_sievePrimitiveEnergy_pmPowerDamped_growth hε hε2]
    with N hN hP
  have hlow := hP.1
  have he : 0 ≤ Real.exp (-(vkKappa * vkScale N / 270)) := (Real.exp_pos _).le
  calc _ ≤ C * (N : ℝ) ^ (1 - 2 * ε) * Real.exp (-(vkKappa * vkScale N / 270)) := hN
    _ ≤ C * (10368 * sievePrimitiveEnergy N (pmPowerDampedRealWeight ε)) *
          Real.exp (-(vkKappa * vkScale N / 270)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hC0) he
    _ = _ := by ring

/-- **All-Damping Pure-Interior Pronic Energy Ratio Against the Period Energy (`0 < ε < 1/2`):**
For **every** `0 < ε < 1/2`, there exists `C ≥ 0` such that for all large `N`,
`E_N^{int}(ε) ≤ C exp(−κ σ(N)/270) E_prim(N)`. -/
theorem eventually_interiorPronic_le_mul_periodEnergy_of_pos
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop, pmBezoutInteriorPronicEnergy ε N ≤
      C * Real.exp (-(vkKappa * vkScale N / 270)) *
        sievePrimitiveEnergy N (pmPowerDampedRealWeight ε) := by
  obtain ⟨C, hC0, hC⟩ := eventually_interiorPronic_le_growth_of_pos hε hε2
  refine ⟨10368 * C, by positivity, ?_⟩
  filter_upwards [hC, eventually_sievePrimitiveEnergy_pmPowerDamped_growth hε hε2]
    with N hN hP
  have hlow := hP.1
  have he : 0 ≤ Real.exp (-(vkKappa * vkScale N / 270)) := (Real.exp_pos _).le
  calc _ ≤ C * (N : ℝ) ^ (1 - 2 * ε) * Real.exp (-(vkKappa * vkScale N / 270)) := hN
    _ ≤ C * (10368 * sievePrimitiveEnergy N (pmPowerDampedRealWeight ε)) *
          Real.exp (-(vkKappa * vkScale N / 270)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hC0) he
    _ = _ := by ring

#print axioms abs_weightCenteredPrefix_dampedSign_le_of_linear_all_pos
#print axioms exists_abs_weightCenteredPrefix_pmPowerDamped_le_vk_all_pos
#print axioms exists_receiver_le_on_vinogradovKorobovBand_of_pos
#print axioms exists_interiorPronic_le_on_vinogradovKorobovBand_of_pos
#print axioms parityPair_separated_on_vinogradovKorobovBand_of_pos
#print axioms eventually_receiver_le_growth_of_pos
#print axioms eventually_interiorPronic_le_growth_of_pos
#print axioms eventually_receiver_le_mul_periodEnergy_of_pos
#print axioms eventually_interiorPronic_le_mul_periodEnergy_of_pos

end

end GaloisForLFunctions.BezoutValuationIncidence
