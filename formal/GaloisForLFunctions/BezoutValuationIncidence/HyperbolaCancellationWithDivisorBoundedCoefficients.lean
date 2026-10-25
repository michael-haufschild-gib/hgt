import GaloisForLFunctions.BezoutValuationIncidence.AllDampingVinogradovKorobovBandAndInteriorGrowth
import GaloisForLFunctions.RHTower.Sieve.CriticalDivisorAffineMeanSquare

/-!
# Hyperbola cancellation with divisor-bounded coefficients

Finite Abel summation bounds the reciprocal tail and the long floor blocks by
the partial-sum modulus. Keeping the exact weighted head allows square-divisor
coefficient bounds, whose head cost is only four logarithms.
-/
open Finset Filter RHTower
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

/-- A linear partial-sum bound controls the reciprocal tail whenever that tail converges. -/
theorem abs_tsum_tail_rpow_le_of_linear_of_summable
    {s : ℕ → ℝ} {L ε : ℝ} {D : ℕ} (hD : 1 ≤ D) (hL : 0 ≤ L) (hε : 0 < ε)
    (hsum : Summable (fun i : ℕ =>
      ((i + (D + 1) : ℕ) : ℝ) ^ (-(1 + ε)) * s (i + (D + 1))))
    (hS : ∀ x, D ≤ x → |∑ e ∈ Icc 1 x, s e| ≤ L * x) :
    |∑' i : ℕ, ((i + (D + 1) : ℕ) : ℝ) ^ (-(1 + ε)) * s (i + (D + 1))| ≤
      (2 + 1 / ε) * L * (D : ℝ) ^ (-ε) := by
  refine le_of_tendsto' hsum.hasSum.tendsto_sum_nat.abs fun K => ?_
  have hshift : ∑ i ∈ range K, ((i + (D + 1) : ℕ) : ℝ) ^ (-(1 + ε)) * s (i + (D + 1)) =
      ∑ d ∈ Ioc D (D + K), s d * (d : ℝ) ^ (-(1 + ε)) := by
    rw [dampedSign_sum_Ioc_eq_sum_range_shift]
    exact sum_congr rfl fun i _ => mul_comm _ _
  rw [hshift]
  have hab := abs_sum_Ioc_mul_le_of_linear (s := s) (w := fun d : ℕ => (d : ℝ) ^ (-(1 + ε)))
    (Nat.le_add_right D K) (fun x hx _ => hS x hx) (fun d => Real.rpow_nonneg (Nat.cast_nonneg d) _)
    (fun d hd => Real.rpow_le_rpow_of_nonpos (by exact_mod_cast (by omega : 0 < d))
      (by exact_mod_cast (Nat.le_succ d)) (by linarith))
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hhead : (D : ℝ) * ((D + 1 : ℕ) : ℝ) ^ (-(1 + ε)) ≤ (D : ℝ) ^ (-ε) := by
    have hle : ((D + 1 : ℕ) : ℝ) ^ (-(1 + ε)) ≤ (D : ℝ) ^ (-(1 + ε)) :=
      Real.rpow_le_rpow_of_nonpos hD0 (by push_cast; linarith) (by linarith)
    have he : (D : ℝ) * (D : ℝ) ^ (-(1 + ε)) = (D : ℝ) ^ (-ε) := by
      rw [show -(1 + ε) = -ε - 1 by ring, Real.rpow_sub_one hD0.ne']
      field_simp
    calc (D : ℝ) * ((D + 1 : ℕ) : ℝ) ^ (-(1 + ε)) ≤ (D : ℝ) * (D : ℝ) ^ (-(1 + ε)) :=
          mul_le_mul_of_nonneg_left hle hD0.le
      _ = _ := he
  have htail := sum_Ioc_rpow_neg_one_sub_le hε (X := D + K) hD
  calc _ ≤ L * (2 * D * ((D + 1 : ℕ) : ℝ) ^ (-(1 + ε)) +
          ∑ d ∈ Ioc D (D + K), (d : ℝ) ^ (-(1 + ε))) := by simpa using hab
    _ ≤ L * (2 * (D : ℝ) ^ (-ε) + (D : ℝ) ^ (-ε) / ε) :=
        mul_le_mul_of_nonneg_left (by linarith only [hhead, htail]) hL
    _ = (2 + 1 / ε) * L * (D : ℝ) ^ (-ε) := by ring

/-- Reversing the hyperbola sums expresses a floor tail through partial-sum blocks. -/
theorem sum_Ioc_mul_natDiv_eq_sum_Icc_Ioc (f : ℕ → ℝ) (D n : ℕ) :
    (∑ d ∈ Ioc D n, f d * ((n / d : ℕ) : ℝ)) =
      ∑ k ∈ Icc 1 n, ∑ d ∈ Ioc D (n / k), f d := by
  have hcount : ∀ d, f d * ((n / d : ℕ) : ℝ) = ∑ _k ∈ Icc 1 (n / d), f d := fun d => by
    rw [sum_const, Nat.card_Icc, nsmul_eq_mul, mul_comm]; simp
  simp_rw [hcount]
  refine sum_comm' fun d k => ?_
  simp only [mem_Ioc, mem_Icc]
  constructor
  · rintro ⟨⟨hDd, hdn⟩, hk1, hkd⟩
    have hd0 : 0 < d := by omega
    have hkd' : k * d ≤ n := (Nat.le_div_iff_mul_le hd0).mp hkd
    refine ⟨⟨hDd, (Nat.le_div_iff_mul_le (by omega)).mpr (by simpa only [Nat.mul_comm] using hkd')⟩,
      hk1, le_trans hkd (Nat.div_le_self n d)⟩
  · rintro ⟨⟨hDd, hdk⟩, hk1, hkn⟩
    have hd0 : 0 < d := by omega
    have hdk' : d * k ≤ n := (Nat.le_div_iff_mul_le (by omega)).mp hdk
    refine ⟨⟨hDd, le_trans hdk (Nat.div_le_self n k)⟩, hk1,
      (Nat.le_div_iff_mul_le hd0).mpr (by simpa only [Nat.mul_comm] using hdk')⟩

/-- The head keeps its exact absolute mass; only the tail uses cancellation in partial sums. -/
theorem abs_weightCenteredPrefix_dampedSign_le_head_of_linear
    {s : ℕ → ℝ} {L ε : ℝ} (hL : 0 ≤ L) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hsum : Summable (fun d : ℕ => dampedSignWeight s ε d / d)) {n D : ℕ} (hD : 1 ≤ D) (hDn : D ≤ n)
    (hS : ∀ x, D ≤ x → |∑ e ∈ Icc 1 x, s e| ≤ L * x) :
    |weightCenteredPrefix (dampedSignWeight s ε) (∑' d : ℕ, dampedSignWeight s ε d / d) n| ≤
      (∑ d ∈ Icc 1 D, |s d| * (d : ℝ) ^ (-ε)) + 13 / ε * L * n * (D : ℝ) ^ (-ε) := by
  set c := dampedSignWeight s ε
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
  have hlong := sum_Ioc_mul_natDiv_eq_sum_Icc_Ioc c D n
  have ha : |∑ d ∈ Icc 1 D, c d * ((n / d : ℕ) : ℝ) - n * ∑ d ∈ Icc 1 D, c d / d| ≤
      (∑ d ∈ Icc 1 D, |s d| * (d : ℝ) ^ (-ε)) := by
    rw [mul_sum, ← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ d ∈ Icc 1 D, |c d * ((n / d : ℕ) : ℝ) - n * (c d / d)| ≤ |s d| * (d : ℝ) ^ (-ε) := by
      intro d hd
      rw [mem_Icc] at hd
      have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
      have hfl1 : ((n / d : ℕ) : ℝ) ≤ (n : ℝ) / d := Nat.cast_div_le
      have hfl2 : (n : ℝ) / d - 1 < ((n / d : ℕ) : ℝ) := by
        have h := Nat.lt_div_mul_add (a := n) (show 0 < d by omega)
        have h' : (n : ℝ) < ((n / d : ℕ) : ℝ) * d + d := by exact_mod_cast h
        rw [div_sub_one hd0.ne', div_lt_iff₀ hd0]; linarith
      have hc : |c d| = |s d| * (d : ℝ) ^ (-ε) := by
        rw [show c d = s d * (d : ℝ) ^ (-ε) from rfl, abs_mul,
          abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
      have heq : c d * ((n / d : ℕ) : ℝ) - n * (c d / d) = c d * (((n / d : ℕ) : ℝ) - n / d) := by
        field_simp
      rw [heq, abs_mul]
      have hfr : |((n / d : ℕ) : ℝ) - n / d| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      calc |c d| * |((n / d : ℕ) : ℝ) - n / d| ≤ |c d| * 1 :=
          mul_le_mul_of_nonneg_left hfr (abs_nonneg _)
        _ = _ := by rw [mul_one, hc]
    exact sum_le_sum hterm
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
      simpa only [Nat.mul_comm] using this
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
        linarith only [h1pow, hε2]
      have h5 : 1 + ((n : ℝ) / D) ^ ε / ε ≤ (2 / ε) * ((n : ℝ) / D) ^ ε := by
        have hdiv : ((n : ℝ) / D) ^ ε / ε + ((n : ℝ) / D) ^ ε / ε = (2 / ε) * ((n : ℝ) / D) ^ ε := by
          ring
        linarith only [h4, hdiv]
      linarith only [h1, h2, h3, h5]
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
    have htail : Summable (fun i : ℕ =>
        ((i + (D + 1) : ℕ) : ℝ) ^ (-(1 + ε)) * s (i + (D + 1))) := by
      have hshift := (summable_nat_add_iff
        (f := fun d : ℕ => dampedSignWeight s ε d / d) (D + 1)).mpr hsum
      simpa only [dampedSignWeight_div hε] using hshift
    have ht := abs_tsum_tail_rpow_le_of_linear_of_summable hD hL hε htail hS
    have heq : ∑' i : ℕ, c (i + (D + 1)) / ((i + (D + 1) : ℕ) : ℝ) =
        ∑' i : ℕ, ((i + (D + 1) : ℕ) : ℝ) ^ (-(1 + ε)) * s (i + (D + 1)) :=
      tsum_congr fun i => dampedSignWeight_div hε _
    have h3 : 2 + 1 / ε ≤ 3 / ε := by
      rw [le_div_iff₀ hε]
      have : 1 / ε * ε = 1 := div_mul_cancel₀ 1 hε.ne'
      nlinarith only [hε2, this]
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
    _ ≤ _ := by linarith only [ha, hb, hc, hcomb]

/-- A square-divisor coefficient majorant costs only four logarithms in the hyperbola head. -/
theorem sum_abs_mul_rpow_le_divisor_square_head {s : ℕ → ℝ} {ε C : ℝ}
    (hε : ε ≤ 1) (hC : 0 ≤ C)
    (hs : ∀ d : ℕ, 1 ≤ d → |s d| ≤ C * (d.divisors.card : ℝ) ^ 2)
    {D : ℕ} (hD : 1 ≤ D) :
    (∑ d ∈ Icc 1 D, |s d| * (d : ℝ) ^ (-ε)) ≤
      C * (D : ℝ) ^ (1 - ε) * (1 + Real.log D) ^ 4 := by
  have hterm (d : ℕ) (hd : d ∈ Icc 1 D) :
      |s d| * (d : ℝ) ^ (-ε) ≤
        (C * (D : ℝ) ^ (1 - ε)) * ((d.divisors.card : ℝ) ^ 2 / d) := by
    have hd1 := (mem_Icc.mp hd).1
    have hdD := (mem_Icc.mp hd).2
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
    have hp : (d : ℝ) ^ (1 - ε) ≤ (D : ℝ) ^ (1 - ε) :=
      Real.rpow_le_rpow hd0.le (by exact_mod_cast hdD) (by linarith only [hε])
    calc
      _ ≤ C * (d.divisors.card : ℝ) ^ 2 * (d : ℝ) ^ (-ε) :=
        mul_le_mul_of_nonneg_right (hs d hd1) (Real.rpow_nonneg hd0.le _)
      _ = (C * ((d.divisors.card : ℝ) ^ 2 / d)) * (d : ℝ) ^ (1 - ε) := by
        rw [show -ε = (1 - ε) - 1 by ring, Real.rpow_sub_one hd0.ne']
        ring
      _ ≤ (C * ((d.divisors.card : ℝ) ^ 2 / d)) * (D : ℝ) ^ (1 - ε) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ∑ d ∈ Icc 1 D,
        (C * (D : ℝ) ^ (1 - ε)) * ((d.divisors.card : ℝ) ^ 2 / d) := sum_le_sum hterm
    _ = (C * (D : ℝ) ^ (1 - ε)) * ∑ d ∈ Icc 1 D, (d.divisors.card : ℝ) ^ 2 / d :=
      (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (RHTower.Sieve.sum_card_divisors_sq_div_le_polylog D hD) (by positivity)

end GaloisForLFunctions.BezoutValuationIncidence
