import GaloisForLFunctions.TransHorizonIncidenceMechanics.CriticalWienerKernelsRepairAPositiveDriftOnlyAtItsPole
import GaloisForLFunctions.TransHorizonIncidenceMechanics.FinitePerturbationsOfTheSmoothPowerAreDecidedAtThePole
import GaloisForLFunctions.TransHorizonIncidenceMechanics.TheHorizonLimitCommutesWithTheReceiverExactlyFromHalfDamping

/-!
# Critical Wiener perturbations of the smooth power are decided at the pole

Let `0 < ε < 1/2` and `q(d) = d^{-ε}`. For every kernel `k` of the critical Wiener algebra
`Σ_j |k(j)| j^{-1/2} < ∞` the receiver of `k ⋆ q` is bounded **if and only if**
`K(1 − ε) = Σ_j k(j) j^{-(1−ε)} = 0` (`receiverBounded_dirichletConv_unit_iff_critical`). The case of
finite kernels is `receiverBounded_dirichletConv_unit_iff`; the pole law of the algebra
(`not_receiverBounded_dirichletConv_of_drift_critical`) is the necessity half.

**Sufficiency.** When the pole value vanishes, `k = Σ_j k(j) (δ_j − j^{-(1−ε)} δ_1)`, and each
*pole-free dilation* `b_j = (δ_j − j^{-(1−ε)} δ_1) ⋆ q` has receiver energy at most `C/j`
(`weightPronicEnergy_poleFreeDilation_le`); Minkowski's inequality gives
`‖A_{k⋆q}‖ ≤ √C Σ_j |k(j)| j^{-1/2}` on every truncation, and the truncations converge at every fixed
cutoff.

* `b_j(d) = d^{-ε}(j^ε [j ∣ d] − j^{-(1−ε)})` (`dirichletConv_poleFreeKernel`), a damped sign whose
  partial sums are `j^ε(⌊N/j⌋ − N/j)`, bounded by `j^ε`.
* Below the dilation, `n < j`: `A_{b_j}(n) = −j^{-(1−ε)} A_q(n) − m_q n/j` with `|A_q(n)| ≤ C n^{1−ε}`,
  so the energy below `j` is `O(j^{2ε−2} Σ_{n<j} n^{-2ε}) = O(1/j)`; here `ε < 1/2` is used.
* Beyond it, `n ≥ j`: the sharp hyperbola bound `|A_c(n)| ≤ Σ_{d≤D} |c(d)| + 4Bn(D+1)^{-1-ε}`
  (`abs_weightCenteredPrefix_dampedSign_le_sum`) at the split `D = ⌊√(jn)⌋` gives
  `|A_{b_j}(n)| ≤ 2 + C (n/j)^{(1−ε)/2}`, whose pronic tail is `O(1/j)`.

So on the whole critical Wiener algebra the dilations enter the receiver of the smooth power only
through the value of the kernel at the pole: the paid perturbations form the hyperplane
`K(1 − ε) = 0`.
-/

open Finset Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### The sharp hyperbola bound for damped signs -/

/-- **The sharp hyperbola bound.** For `c = s d^{-ε}` with partial sums of `s` bounded by `B`, its
mean `m = Σ_d c(d)/d` and every split `1 ≤ D ≤ n`,
`|A_c(n)| ≤ Σ_{d ≤ D} |c(d)| + 4Bn(D+1)^{-1-ε}`: the short moduli cost their own mass, the long
moduli and the tail are Abel sums. -/
theorem abs_weightCenteredPrefix_dampedSign_le_sum {s : ℕ → ℝ} {B ε : ℝ} (hB : 0 ≤ B)
    (hε : 0 < ε) (hS : ∀ x, |∑ d ∈ range x, s d| ≤ B) {n D : ℕ} (hD : 1 ≤ D) (hDn : D ≤ n) :
    |weightCenteredPrefix (dampedSignWeight s ε) (∑' d : ℕ, dampedSignWeight s ε d / d) n| ≤
      ∑ d ∈ Icc 1 D, |dampedSignWeight s ε d| + 4 * B * n * ((D + 1 : ℕ) : ℝ) ^ (-(1 + ε)) := by
  set c := dampedSignWeight s ε
  have hsum := summable_dampedSignWeight_div hB hε hS
  -- the mean splits at `D`
  have hmean : ∑' d : ℕ, c d / d = ∑ d ∈ Icc 1 D, c d / d +
      ∑' i : ℕ, c (i + (D + 1)) / ((i + (D + 1) : ℕ) : ℝ) := by
    rw [← hsum.sum_add_tsum_nat_add (D + 1), dampedSign_sum_range_succ_eq_add_Icc]
    simp [c, dampedSignWeight]
  -- the floor sum splits at `D`
  have hsplit : ∑ d ∈ Icc 1 n, c d * ((n / d : ℕ) : ℝ) =
      ∑ d ∈ Icc 1 D, c d * ((n / d : ℕ) : ℝ) + ∑ d ∈ Ioc D n, c d * ((n / d : ℕ) : ℝ) := by
    have h1 : Icc 1 n = Ioc 0 n := by ext d; simp only [mem_Icc, mem_Ioc]; omega
    have h2 : Icc 1 D = Ioc 0 D := by ext d; simp only [mem_Icc, mem_Ioc]; omega
    rw [h1, h2, sum_Ioc_consecutive _ (Nat.zero_le D) hDn]
  -- long moduli counted along the cofactor
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
  -- piece (a): short moduli cost their mass
  have ha : |∑ d ∈ Icc 1 D, c d * ((n / d : ℕ) : ℝ) - n * ∑ d ∈ Icc 1 D, c d / d| ≤
      ∑ d ∈ Icc 1 D, |c d| := by
    rw [mul_sum, ← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d hd => ?_)
    rw [mem_Icc] at hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    have heq : c d * ((n / d : ℕ) : ℝ) - n * (c d / d) = c d * (((n / d : ℕ) : ℝ) - n / d) := by
      field_simp
    rw [heq, abs_mul]
    calc |c d| * |((n / d : ℕ) : ℝ) - n / d| ≤ |c d| * 1 :=
          mul_le_mul_of_nonneg_left (abs_natDiv_sub_div_le n d (by omega)) (abs_nonneg _)
      _ = |c d| := mul_one _
  -- piece (b): long moduli
  have hb : |∑ k ∈ Icc 1 n, ∑ d ∈ Ioc D (n / k), c d| ≤
      2 * B * n * ((D + 1 : ℕ) : ℝ) ^ (-(1 + ε)) := by
    have hblock : ∀ k ∈ Icc 1 n, |∑ d ∈ Ioc D (n / k), c d| ≤
        (if D + 1 ≤ n / k then 2 * B * ((D + 1 : ℕ) : ℝ) ^ (-ε) else 0) := by
      intro k _
      split_ifs with h
      · obtain ⟨K, hK⟩ : ∃ K, n / k = D + K := ⟨n / k - D, by omega⟩
        rw [hK, dampedSign_sum_Ioc_eq_sum_range_shift]
        have := abs_sum_block_rpow_le hB hε.le hS (k := D + 1) (by omega) K
        simpa [c, dampedSignWeight, mul_comm] using this
      · rw [Ioc_eq_empty (by omega), sum_empty, abs_zero]
    refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hblock).trans ?_)
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    have hcard : ((filter (fun k => D + 1 ≤ n / k) (Icc 1 n)).card : ℝ) ≤ (n : ℝ) / (D + 1) := by
      have hsub : filter (fun k => D + 1 ≤ n / k) (Icc 1 n) ⊆ Icc 1 (n / (D + 1)) := by
        intro k hk
        simp only [mem_filter, mem_Icc] at hk ⊢
        refine ⟨hk.1.1, (Nat.le_div_iff_mul_le (by omega)).mpr ?_⟩
        have := (Nat.le_div_iff_mul_le (by omega : 0 < k)).mp hk.2
        linarith [mul_comm k (D + 1)]
      calc ((filter (fun k => D + 1 ≤ n / k) (Icc 1 n)).card : ℝ) ≤ (Icc 1 (n / (D + 1))).card := by
            exact_mod_cast card_le_card hsub
        _ = ((n / (D + 1) : ℕ) : ℝ) := by rw [Nat.card_Icc]; simp
        _ ≤ (n : ℝ) / (D + 1) := by
            have := Nat.cast_div_le (α := ℝ) (m := n) (n := D + 1)
            push_cast at this; exact this
    have hD1 : (0 : ℝ) < ((D + 1 : ℕ) : ℝ) := by positivity
    have hpow : ((D + 1 : ℕ) : ℝ) ^ (-(1 + ε)) = ((D + 1 : ℕ) : ℝ) ^ (-ε) / ((D + 1 : ℕ) : ℝ) := by
      rw [show -(1 + ε) = -ε - 1 by ring, Real.rpow_sub_one hD1.ne']
    rw [hpow]
    have hB2 : 0 ≤ 2 * B * ((D + 1 : ℕ) : ℝ) ^ (-ε) := by positivity
    calc ((filter (fun k => D + 1 ≤ n / k) (Icc 1 n)).card : ℝ) * (2 * B * ((D + 1 : ℕ) : ℝ) ^ (-ε))
        ≤ (n : ℝ) / (D + 1) * (2 * B * ((D + 1 : ℕ) : ℝ) ^ (-ε)) :=
          mul_le_mul_of_nonneg_right hcard hB2
      _ = 2 * B * n * (((D + 1 : ℕ) : ℝ) ^ (-ε) / ((D + 1 : ℕ) : ℝ)) := by push_cast; ring
  -- piece (c): the tail
  have hc : |(n : ℝ) * ∑' i : ℕ, c (i + (D + 1)) / ((i + (D + 1) : ℕ) : ℝ)| ≤
      2 * B * n * ((D + 1 : ℕ) : ℝ) ^ (-(1 + ε)) := by
    have ht := (abs_tsum_tail_rpow_le hB (by linarith : 1 < 1 + ε) hS (k := D + 1) (by omega)).2
    have heq : ∑' i : ℕ, c (i + (D + 1)) / ((i + (D + 1) : ℕ) : ℝ) =
        ∑' i : ℕ, ((i + (D + 1) : ℕ) : ℝ) ^ (-(1 + ε)) * s (i + (D + 1)) :=
      tsum_congr fun i => dampedSignWeight_div hε _
    rw [heq, abs_mul, Nat.abs_cast]
    calc (n : ℝ) * |∑' i : ℕ, ((i + (D + 1) : ℕ) : ℝ) ^ (-(1 + ε)) * s (i + (D + 1))|
        ≤ n * (2 * B * ((D + 1 : ℕ) : ℝ) ^ (-(1 + ε))) :=
          mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg n)
      _ = 2 * B * n * ((D + 1 : ℕ) : ℝ) ^ (-(1 + ε)) := by ring
  -- assemble
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
    _ ≤ _ := by linarith

/-! ### Pole-free dilations of the smooth power -/

/-- The pole-free elementary kernel `δ_j − j^{-(1−ε)} δ_1`. -/
def poleFreeKernel (ε : ℝ) (j i : ℕ) : ℝ :=
  (if i = j then 1 else 0) - (if i = 1 then (j : ℝ) ^ (-(1 - ε)) else 0)

/-- The pole-free dilation `b_j = (δ_j − j^{-(1−ε)} δ_1) ⋆ d^{-ε}`. -/
def poleFreeDilation (ε : ℝ) (j : ℕ) : ℕ → ℝ :=
  RHTower.dirichletConv (poleFreeKernel ε j) (dampedSignWeight unitSign ε)

/-- The undamped sign of `b_j`: `j^ε [j ∣ d] − j^{-(1−ε)}`, and `0` at `d = 0`. -/
def poleFreeSign (ε : ℝ) (j d : ℕ) : ℝ :=
  if d = 0 then 0 else (j : ℝ) ^ ε * (if j ∣ d then 1 else 0) - (j : ℝ) ^ (-(1 - ε))

/-- The mean `m_{b_j} = (1/j − j^{-(1−ε)}) m_q`. -/
def poleFreeMean (ε : ℝ) (j : ℕ) : ℝ :=
  (1 / (j : ℝ) - (j : ℝ) ^ (-(1 - ε))) * ∑' d : ℕ, dampedSignWeight unitSign ε d / d

/-- On a multiple of `j`, `(d/j)^{-ε} = j^ε d^{-ε}`. -/
theorem cast_div_rpow_neg {ε : ℝ} {j d : ℕ} (hj : 1 ≤ j) (hjd : j ∣ d) :
    ((d / j : ℕ) : ℝ) ^ (-ε) = (j : ℝ) ^ ε * (d : ℝ) ^ (-ε) := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  rw [Nat.cast_div hjd hj0.ne', Real.div_rpow (Nat.cast_nonneg d) hj0.le, Real.rpow_neg hj0.le ε,
    div_inv_eq_mul, mul_comm]

/-- `b_j(d) = d^{-ε}(j^ε [j ∣ d] − j^{-(1−ε)})`. -/
theorem dirichletConv_poleFreeKernel {ε : ℝ} {j : ℕ} (hj : 1 ≤ j) :
    RHTower.dirichletConv (poleFreeKernel ε j) (dampedSignWeight unitSign ε) =
      dampedSignWeight (poleFreeSign ε j) ε := by
  funext d
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [RHTower.dirichletConv, dampedSignWeight, poleFreeSign]
  have hd0 : d ≠ 0 := hd.ne'
  have hsplit : RHTower.dirichletConv (poleFreeKernel ε j) (dampedSignWeight unitSign ε) d =
      (if j ∣ d then dampedSignWeight unitSign ε (d / j) else 0) -
        (j : ℝ) ^ (-(1 - ε)) * dampedSignWeight unitSign ε d := by
    simp only [RHTower.dirichletConv, poleFreeKernel, sub_mul, sum_sub_distrib, ite_mul, one_mul,
      zero_mul, sum_ite_eq', Nat.mem_divisors, Nat.one_dvd, ne_eq, hd0, not_false_eq_true,
      and_true, if_true, Nat.div_one]
  rw [hsplit]
  simp only [dampedSignWeight, unitSign, one_mul, poleFreeSign, hd0, if_false]
  by_cases hjd : j ∣ d
  · rw [if_pos hjd, if_pos hjd, cast_div_rpow_neg hj hjd]
    ring
  · rw [if_neg hjd, if_neg hjd]
    ring

/-- The partial sums of the sign are `j^ε (⌊N/j⌋ − N/j)`, bounded by `j^ε`. -/
theorem abs_sum_range_poleFreeSign_le {ε : ℝ} {j : ℕ} (hj : 1 ≤ j) (x : ℕ) :
    |∑ d ∈ range x, poleFreeSign ε j d| ≤ (j : ℝ) ^ ε := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hjε : 0 < (j : ℝ) ^ ε := Real.rpow_pos_of_pos hj0 ε
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp only [range_zero, sum_empty, abs_zero]; exact hjε.le
  obtain ⟨N, rfl⟩ : ∃ N, x = N + 1 := ⟨x - 1, by omega⟩
  rw [dampedSign_sum_range_succ_eq_add_Icc]
  have h0 : poleFreeSign ε j 0 = 0 := by simp [poleFreeSign]
  have hterm : ∀ d ∈ Icc 1 N, poleFreeSign ε j d =
      (j : ℝ) ^ ε * (if j ∣ d then 1 else 0) - (j : ℝ) ^ (-(1 - ε)) := fun d hd => by
    have : d ≠ 0 := by have := (mem_Icc.mp hd).1; omega
    simp [poleFreeSign, this]
  have hcard : ((Icc 1 N).filter (fun d => j ∣ d)).card = N / j := by
    rw [show Icc 1 N = Ioc 0 N by ext d; simp only [mem_Icc, mem_Ioc]; omega]
    exact Nat.Ioc_filter_dvd_card_eq_div N j
  have hpow : (j : ℝ) ^ (-(1 - ε)) = (j : ℝ) ^ ε / j := by
    rw [show -(1 - ε) = ε - 1 by ring, Real.rpow_sub_one hj0.ne']
  have hsum : ∑ d ∈ Icc 1 N, poleFreeSign ε j d = (j : ℝ) ^ ε * (((N / j : ℕ) : ℝ) - (N : ℝ) / j) := by
    rw [sum_congr rfl hterm, sum_sub_distrib, ← mul_sum, sum_boole, hcard, sum_const, Nat.card_Icc,
      Nat.add_sub_cancel, nsmul_eq_mul, hpow]
    ring
  rw [h0, zero_add, hsum, abs_mul, abs_of_pos hjε]
  calc (j : ℝ) ^ ε * |((N / j : ℕ) : ℝ) - (N : ℝ) / j| ≤ (j : ℝ) ^ ε * 1 :=
        mul_le_mul_of_nonneg_left (abs_natDiv_sub_div_le N j hj) hjε.le
    _ = (j : ℝ) ^ ε := mul_one _

/-- The mean of the pole-free dilation. -/
theorem hasSum_poleFreeDilation_div {ε : ℝ} (hε : 0 < ε) (j : ℕ) :
    HasSum (fun d : ℕ => poleFreeDilation ε j d / d) (poleFreeMean ε j) := by
  have hk : (fun i : ℕ => poleFreeKernel ε j i / i) =
      fun i => (if i = j then 1 / (j : ℝ) else 0) - (if i = 1 then (j : ℝ) ^ (-(1 - ε)) else 0) := by
    funext i
    simp only [poleFreeKernel]
    rcases eq_or_ne i j with rfl | h1 <;> rcases eq_or_ne i 1 with rfl | h2 <;> simp [*]
  have hkh : HasSum (fun i : ℕ => poleFreeKernel ε j i / i) (1 / j - (j : ℝ) ^ (-(1 - ε))) := by
    rw [hk]; exact (hasSum_ite_eq j _).sub (hasSum_ite_eq 1 _)
  have hq := summable_unit_weight hε
  exact hasSum_dirichletConv_div hkh hq.hasSum hkh.summable.abs hq.abs

/-- The smooth power lies in `𝒞(1, ε)`. -/
theorem dampedClass_unit (ε : ℝ) : DampedClass 1 ε (dampedSignWeight unitSign ε) := fun d => by
  simp [dampedSignWeight, unitSign, abs_of_nonneg, Real.rpow_nonneg]

/-! ### The energy of a pole-free dilation -/

/-- **Below the dilation**, `n < j`: `|A_{b_j}(n)| ≤ j^{-(1−ε)} C n^{1−ε} + m_q n/j`. -/
theorem abs_weightCenteredPrefix_poleFreeDilation_le_of_lt {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    {j n : ℕ} (hn : 1 ≤ n) (hnj : n < j) :
    |weightCenteredPrefix (poleFreeDilation ε j) (poleFreeMean ε j) n| ≤
      (j : ℝ) ^ (-(1 - ε)) * ((1 + 1 / (1 - ε) + 1 / ε) * (n : ℝ) ^ (1 - ε)) +
        (∑' d : ℕ, dampedSignWeight unitSign ε d / d) * n / j := by
  have hj : 1 ≤ j := by omega
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have ha0 : 0 ≤ (j : ℝ) ^ (-(1 - ε)) := Real.rpow_nonneg hj0.le _
  have hZ0 : 0 ≤ ∑' d : ℕ, dampedSignWeight unitSign ε d / d := tsum_nonneg fun d => by
    simp only [dampedSignWeight, unitSign, one_mul]; positivity
  -- below `j` no modulus is a multiple of `j`
  have hbj : ∀ d ∈ Icc 1 n, poleFreeDilation ε j d =
      -((j : ℝ) ^ (-(1 - ε))) * dampedSignWeight unitSign ε d := by
    intro d hd
    have hd := mem_Icc.mp hd
    have hd0 : d ≠ 0 := by omega
    have hnd : ¬ j ∣ d := fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)
    rw [poleFreeDilation, dirichletConv_poleFreeKernel hj]
    simp only [dampedSignWeight, poleFreeSign, hd0, if_false, hnd, mul_zero, zero_sub, unitSign,
      one_mul]
  have hfloor : ∑ d ∈ Icc 1 n, poleFreeDilation ε j d * ((n / d : ℕ) : ℝ) =
      -((j : ℝ) ^ (-(1 - ε))) * ∑ d ∈ Icc 1 n, dampedSignWeight unitSign ε d * ((n / d : ℕ) : ℝ) := by
    rw [mul_sum]
    exact sum_congr rfl fun d hd => by rw [hbj d hd]; ring
  have hA : weightCenteredPrefix (poleFreeDilation ε j) (poleFreeMean ε j) n =
      -((j : ℝ) ^ (-(1 - ε))) * weightCenteredPrefix (dampedSignWeight unitSign ε)
          (∑' d : ℕ, dampedSignWeight unitSign ε d / d) n -
        (∑' d : ℕ, dampedSignWeight unitSign ε d / d) * n / j := by
    simp only [weightCenteredPrefix, sum_Icc_sum_divisors_eq_floor]
    rw [hfloor, poleFreeMean]
    ring
  have hAq := abs_weightCenteredPrefix_le_of_dampedClass hε hε1 (dampedClass_unit ε) hn
  rw [one_mul] at hAq
  rw [hA]
  calc |-((j : ℝ) ^ (-(1 - ε))) * weightCenteredPrefix (dampedSignWeight unitSign ε)
          (∑' d : ℕ, dampedSignWeight unitSign ε d / d) n -
        (∑' d : ℕ, dampedSignWeight unitSign ε d / d) * n / j|
      ≤ |-((j : ℝ) ^ (-(1 - ε))) * weightCenteredPrefix (dampedSignWeight unitSign ε)
          (∑' d : ℕ, dampedSignWeight unitSign ε d / d) n| +
        |(∑' d : ℕ, dampedSignWeight unitSign ε d / d) * n / j| := abs_sub _ _
    _ = (j : ℝ) ^ (-(1 - ε)) * |weightCenteredPrefix (dampedSignWeight unitSign ε)
          (∑' d : ℕ, dampedSignWeight unitSign ε d / d) n| +
        (∑' d : ℕ, dampedSignWeight unitSign ε d / d) * n / j := by
        rw [abs_mul, abs_neg, abs_of_nonneg ha0,
          abs_of_nonneg (div_nonneg (mul_nonneg hZ0 (Nat.cast_nonneg n)) hj0.le)]
    _ ≤ (j : ℝ) ^ (-(1 - ε)) * ((1 + 1 / (1 - ε) + 1 / ε) * (n : ℝ) ^ (1 - ε)) +
        (∑' d : ℕ, dampedSignWeight unitSign ε d / d) * n / j := by
        gcongr

/-- Reindexing the multiples of `j` below `D`. -/
theorem sum_Icc_ite_dvd_eq {j : ℕ} (hj : 0 < j) (f : ℕ → ℝ) (D : ℕ) :
    ∑ d ∈ Icc 1 D, (if j ∣ d then f d else 0) = ∑ e ∈ Icc 1 (D / j), f (j * e) := by
  rw [← sum_filter]
  have hfilt : (Icc 1 D).filter (fun d => j ∣ d) =
      (Icc 1 (D / j)).map ⟨(j * ·), mul_right_injective₀ hj.ne'⟩ := by
    ext d
    simp only [mem_filter, mem_Icc, Finset.mem_map, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨⟨h1, h2⟩, e, rfl⟩
      refine ⟨e, ⟨?_, (Nat.le_div_iff_mul_le hj).mpr (by rw [mul_comm]; exact h2)⟩, rfl⟩
      rcases Nat.eq_zero_or_pos e with rfl | he
      · simp at h1
      · exact he
    · rintro ⟨e, ⟨he1, he2⟩, rfl⟩
      refine ⟨⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hj.ne' (by omega)), ?_⟩, dvd_mul_right j e⟩
      have := (Nat.le_div_iff_mul_le hj).mp he2
      rw [mul_comm]; exact this
  rw [hfilt, sum_map]
  rfl

/-- The mass of the sign below `D`: `Σ_{d ≤ D} |b_j(d)| ≤ 1 + j^{-(1−ε)} + 2 j^{-(1−ε)} D^{1−ε}/(1−ε)`. -/
theorem sum_abs_poleFreeDilation_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) {j : ℕ} (hj : 1 ≤ j)
    (D : ℕ) :
    ∑ d ∈ Icc 1 D, |dampedSignWeight (poleFreeSign ε j) ε d| ≤
      1 + (j : ℝ) ^ (-(1 - ε)) + 2 * ((j : ℝ) ^ (-(1 - ε)) * (D : ℝ) ^ (1 - ε)) / (1 - ε) := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have ha0 : 0 ≤ (j : ℝ) ^ (-(1 - ε)) := Real.rpow_nonneg hj0.le _
  have hjε : 0 < (j : ℝ) ^ ε := Real.rpow_pos_of_pos hj0 ε
  have h1ε : 0 < 1 - ε := by linarith
  -- pointwise: `|b_j(d)| ≤ j^ε [j ∣ d] d^{-ε} + j^{-(1−ε)} d^{-ε}`
  have hpt : ∀ d ∈ Icc 1 D, |dampedSignWeight (poleFreeSign ε j) ε d| ≤
      (j : ℝ) ^ ε * (if j ∣ d then (d : ℝ) ^ (-ε) else 0) + (j : ℝ) ^ (-(1 - ε)) * (d : ℝ) ^ (-ε) := by
    intro d hd
    have hd0 : d ≠ 0 := by have := (mem_Icc.mp hd).1; omega
    have hdε : 0 ≤ (d : ℝ) ^ (-ε) := Real.rpow_nonneg (Nat.cast_nonneg d) _
    simp only [dampedSignWeight, poleFreeSign, hd0, if_false]
    rw [abs_mul, abs_of_nonneg hdε]
    by_cases hjd : j ∣ d
    · rw [if_pos hjd, if_pos hjd, mul_one]
      have habs : |(j : ℝ) ^ ε - (j : ℝ) ^ (-(1 - ε))| ≤ (j : ℝ) ^ ε + (j : ℝ) ^ (-(1 - ε)) := by
        rw [abs_le]; constructor <;> linarith
      nlinarith [mul_le_mul_of_nonneg_right habs hdε]
    · rw [if_neg hjd, if_neg hjd, mul_zero, zero_sub, abs_neg,
        abs_of_nonneg (Real.rpow_nonneg hj0.le _)]
      linarith
  -- the multiples of `j`
  have hmult : ∑ d ∈ Icc 1 D, (j : ℝ) ^ ε * (if j ∣ d then (d : ℝ) ^ (-ε) else 0) ≤
      1 + (j : ℝ) ^ (-(1 - ε)) * (D : ℝ) ^ (1 - ε) / (1 - ε) := by
    rw [← mul_sum, sum_Icc_ite_dvd_eq hj]
    have hre : ∀ e ∈ Icc 1 (D / j), ((j * e : ℕ) : ℝ) ^ (-ε) = (j : ℝ) ^ (-ε) * (e : ℝ) ^ (-ε) :=
      fun e _ => by push_cast; exact Real.mul_rpow hj0.le (Nat.cast_nonneg e)
    rw [sum_congr rfl hre, ← mul_sum, ← mul_assoc, ← Real.rpow_add hj0, add_neg_cancel,
      Real.rpow_zero, one_mul]
    refine (RHTower.sum_rpow_neg_head_le hε hε1 (D / j)).trans ?_
    have hdiv : (((D / j : ℕ) : ℝ)) ^ (1 - ε) ≤ (j : ℝ) ^ (-(1 - ε)) * (D : ℝ) ^ (1 - ε) := by
      calc (((D / j : ℕ) : ℝ)) ^ (1 - ε) ≤ ((D : ℝ) / j) ^ (1 - ε) :=
            Real.rpow_le_rpow (Nat.cast_nonneg _) Nat.cast_div_le h1ε.le
        _ = (j : ℝ) ^ (-(1 - ε)) * (D : ℝ) ^ (1 - ε) := by
            rw [Real.div_rpow (Nat.cast_nonneg D) hj0.le, Real.rpow_neg hj0.le]
            ring
    gcongr
  -- the constant part
  have hconst : ∑ d ∈ Icc 1 D, (j : ℝ) ^ (-(1 - ε)) * (d : ℝ) ^ (-ε) ≤
      (j : ℝ) ^ (-(1 - ε)) * (1 + (D : ℝ) ^ (1 - ε) / (1 - ε)) := by
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left (RHTower.sum_rpow_neg_head_le hε hε1 D) ha0
  calc ∑ d ∈ Icc 1 D, |dampedSignWeight (poleFreeSign ε j) ε d|
      ≤ ∑ d ∈ Icc 1 D, ((j : ℝ) ^ ε * (if j ∣ d then (d : ℝ) ^ (-ε) else 0) +
          (j : ℝ) ^ (-(1 - ε)) * (d : ℝ) ^ (-ε)) := sum_le_sum hpt
    _ = ∑ d ∈ Icc 1 D, (j : ℝ) ^ ε * (if j ∣ d then (d : ℝ) ^ (-ε) else 0) +
          ∑ d ∈ Icc 1 D, (j : ℝ) ^ (-(1 - ε)) * (d : ℝ) ^ (-ε) := sum_add_distrib
    _ ≤ (1 + (j : ℝ) ^ (-(1 - ε)) * (D : ℝ) ^ (1 - ε) / (1 - ε)) +
          (j : ℝ) ^ (-(1 - ε)) * (1 + (D : ℝ) ^ (1 - ε) / (1 - ε)) := add_le_add hmult hconst
    _ = 1 + (j : ℝ) ^ (-(1 - ε)) + 2 * ((j : ℝ) ^ (-(1 - ε)) * (D : ℝ) ^ (1 - ε)) / (1 - ε) := by
        ring

/-- **Beyond the dilation**, `j ≤ n`: `|A_{b_j}(n)| ≤ 2 + (2/(1−ε) + 4) (n/j)^{(1−ε)/2}`. -/
theorem abs_weightCenteredPrefix_poleFreeDilation_le_of_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    {j n : ℕ} (hj : 1 ≤ j) (hjn : j ≤ n) :
    |weightCenteredPrefix (poleFreeDilation ε j) (poleFreeMean ε j) n| ≤
      2 + (2 / (1 - ε) + 4) * Real.sqrt ((n : ℝ) / j) ^ (1 - ε) := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hj0' : (j : ℝ) ≠ 0 := hj0.ne'
  have hn1 : 1 ≤ n := hj.trans hjn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have h1ε : 0 < 1 - ε := by linarith
  have ha0 : 0 ≤ (j : ℝ) ^ (-(1 - ε)) := Real.rpow_nonneg hj0.le _
  have ha1 : (j : ℝ) ^ (-(1 - ε)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hj) (by linarith)
  -- the prefix in damped-sign form
  have hmean : poleFreeMean ε j = ∑' d : ℕ, dampedSignWeight (poleFreeSign ε j) ε d / d := by
    rw [← dirichletConv_poleFreeKernel hj]
    exact (hasSum_poleFreeDilation_div hε j).tsum_eq.symm
  rw [poleFreeDilation, dirichletConv_poleFreeKernel hj, hmean]
  -- the split `D = ⌊√(jn)⌋`
  have hjD : j ≤ Nat.sqrt (j * n) := Nat.le_sqrt.mpr (Nat.mul_le_mul_left j hjn)
  have hDn : Nat.sqrt (j * n) ≤ n :=
    (Nat.sqrt_le_sqrt (Nat.mul_le_mul_right n hjn)).trans (Nat.sqrt_eq n).le
  have hmain := abs_weightCenteredPrefix_dampedSign_le_sum (Real.rpow_pos_of_pos hj0 ε).le hε
    (abs_sum_range_poleFreeSign_le (ε := ε) hj) (hj.trans hjD) hDn
  refine hmain.trans ?_
  have hpa := sum_abs_poleFreeDilation_le hε hε1 hj (Nat.sqrt (j * n))
  -- the real square root `√(jn) = j √(n/j)`
  have hρ1 : 1 ≤ (n : ℝ) / j := by rw [le_div_iff₀ hj0, one_mul]; exact_mod_cast hjn
  have hr0 : 0 < Real.sqrt ((n : ℝ) / j) := Real.sqrt_pos.mpr (by linarith)
  have hs : Real.sqrt (((j * n : ℕ) : ℝ)) = j * Real.sqrt ((n : ℝ) / j) := by
    have hcast : (((j * n : ℕ) : ℝ)) = (j : ℝ) * j * ((n : ℝ) / j) := by push_cast; field_simp
    rw [hcast, Real.sqrt_mul (by positivity), Real.sqrt_mul_self hj0.le]
  have hD1 : ((Nat.sqrt (j * n) : ℕ) : ℝ) ≤ j * Real.sqrt ((n : ℝ) / j) :=
    hs ▸ Real.nat_sqrt_le_real_sqrt
  have hD2 : (j : ℝ) * Real.sqrt ((n : ℝ) / j) ≤ ((Nat.sqrt (j * n) + 1 : ℕ) : ℝ) := by
    have := hs ▸ (Real.real_sqrt_lt_nat_sqrt_succ (a := j * n))
    push_cast; linarith
  -- `j^{-(1−ε)} D^{1−ε} ≤ (n/j)^{(1−ε)/2}`
  have hT1 : (j : ℝ) ^ (-(1 - ε)) * ((Nat.sqrt (j * n) : ℕ) : ℝ) ^ (1 - ε) ≤
      Real.sqrt ((n : ℝ) / j) ^ (1 - ε) := by
    calc (j : ℝ) ^ (-(1 - ε)) * ((Nat.sqrt (j * n) : ℕ) : ℝ) ^ (1 - ε)
        ≤ (j : ℝ) ^ (-(1 - ε)) * ((j : ℝ) * Real.sqrt ((n : ℝ) / j)) ^ (1 - ε) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hD1 h1ε.le) ha0
      _ = Real.sqrt ((n : ℝ) / j) ^ (1 - ε) := by
          rw [Real.mul_rpow hj0.le hr0.le, ← mul_assoc, ← Real.rpow_add hj0, neg_add_cancel,
            Real.rpow_zero, one_mul]
  -- `j^ε n (D+1)^{-1-ε} ≤ (n/j)^{(1−ε)/2}`
  have key : ∀ x : ℝ, 0 < x →
      (j : ℝ) ^ ε * (j * x ^ (2 : ℝ)) * ((j : ℝ) * x) ^ (-(1 + ε)) = x ^ (1 - ε) := by
    intro x hx
    rw [Real.mul_rpow hj0.le hx.le]
    have e1 : (j : ℝ) ^ ε * j * (j : ℝ) ^ (-(1 + ε)) = 1 := by
      rw [← Real.rpow_add_one hj0', ← Real.rpow_add hj0, show ε + 1 + -(1 + ε) = 0 by ring,
        Real.rpow_zero]
    have e2 : x ^ (2 : ℝ) * x ^ (-(1 + ε)) = x ^ (1 - ε) := by
      rw [← Real.rpow_add hx]; congr 1; ring
    calc (j : ℝ) ^ ε * (j * x ^ (2 : ℝ)) * ((j : ℝ) ^ (-(1 + ε)) * x ^ (-(1 + ε)))
        = ((j : ℝ) ^ ε * j * (j : ℝ) ^ (-(1 + ε))) * (x ^ (2 : ℝ) * x ^ (-(1 + ε))) := by ring
      _ = x ^ (1 - ε) := by rw [e1, e2, one_mul]
  have hT2 : (j : ℝ) ^ ε * n * ((Nat.sqrt (j * n) + 1 : ℕ) : ℝ) ^ (-(1 + ε)) ≤
      Real.sqrt ((n : ℝ) / j) ^ (1 - ε) := by
    have hjr : 0 < (j : ℝ) * Real.sqrt ((n : ℝ) / j) := by positivity
    calc (j : ℝ) ^ ε * n * ((Nat.sqrt (j * n) + 1 : ℕ) : ℝ) ^ (-(1 + ε))
        ≤ (j : ℝ) ^ ε * n * ((j : ℝ) * Real.sqrt ((n : ℝ) / j)) ^ (-(1 + ε)) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hjr hD2 (by linarith))
            (by positivity)
      _ = (j : ℝ) ^ ε * (j * Real.sqrt ((n : ℝ) / j) ^ (2 : ℝ)) *
            ((j : ℝ) * Real.sqrt ((n : ℝ) / j)) ^ (-(1 + ε)) := by
          have hn : (j : ℝ) * Real.sqrt ((n : ℝ) / j) ^ (2 : ℝ) = n := by
            rw [Real.rpow_two, Real.sq_sqrt (by linarith)]; field_simp
          rw [hn]
      _ = Real.sqrt ((n : ℝ) / j) ^ (1 - ε) := key _ hr0
  have hrε : 0 ≤ Real.sqrt ((n : ℝ) / j) ^ (1 - ε) := Real.rpow_nonneg hr0.le _
  have hfour : 4 * (j : ℝ) ^ ε * n * ((Nat.sqrt (j * n) + 1 : ℕ) : ℝ) ^ (-(1 + ε)) =
      4 * ((j : ℝ) ^ ε * n * ((Nat.sqrt (j * n) + 1 : ℕ) : ℝ) ^ (-(1 + ε))) := by ring
  rw [hfour]
  have h2 : 2 * ((j : ℝ) ^ (-(1 - ε)) * ((Nat.sqrt (j * n) : ℕ) : ℝ) ^ (1 - ε)) / (1 - ε) ≤
      2 * Real.sqrt ((n : ℝ) / j) ^ (1 - ε) / (1 - ε) := by gcongr
  have h3 : (2 / (1 - ε) + 4) * Real.sqrt ((n : ℝ) / j) ^ (1 - ε) =
      2 * Real.sqrt ((n : ℝ) / j) ^ (1 - ε) / (1 - ε) + 4 * Real.sqrt ((n : ℝ) / j) ^ (1 - ε) := by
    ring
  rw [h3]
  linarith

/-- `Σ_{j ≤ n ≤ T} n^{-1-ε} ≤ (1 + 1/ε) j^{-ε}`. -/
theorem sum_Icc_rpow_neg_one_sub_le {ε : ℝ} (hε : 0 < ε) {j : ℕ} (hj : 1 ≤ j) (T : ℕ) :
    ∑ n ∈ Icc j T, (n : ℝ) ^ (-(1 + ε)) ≤ (1 + 1 / ε) * (j : ℝ) ^ (-ε) := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hjε : 0 ≤ (j : ℝ) ^ (-ε) := Real.rpow_nonneg hj0.le _
  -- the telescoping tail beyond `j`
  have htail : ∀ T : ℕ, j ≤ T → ∑ n ∈ Icc (j + 1) T, (n : ℝ) ^ (-(1 + ε)) ≤
      ((j : ℝ) ^ (-ε) - (T : ℝ) ^ (-ε)) / ε := by
    intro T hT
    induction T, hT using Nat.le_induction with
    | base => rw [Icc_eq_empty (by omega), sum_empty]; simp
    | succ T hjT ih =>
      rw [sum_Icc_succ_top (by omega)]
      have hT0 : (0 : ℝ) < T := by exact_mod_cast (hj.trans hjT)
      have hstep := (HTGeometry.rpow_unit_step_bounds (q := -ε) (by linarith) hT0).1
      rw [show -ε - 1 = -(1 + ε) by ring, neg_neg] at hstep
      push_cast
      rw [le_div_iff₀ hε]
      rw [le_div_iff₀ hε] at ih
      linarith [ih, hstep]
  rcases lt_or_ge T j with hT | hT
  · rw [Icc_eq_empty (by omega), sum_empty]; positivity
  · have hsplit : Icc j T = insert j (Icc (j + 1) T) := by
      ext n; simp only [mem_insert, mem_Icc]; omega
    rw [hsplit, sum_insert (by simp)]
    have h1 := htail T hT
    have hTε : 0 ≤ (T : ℝ) ^ (-ε) := Real.rpow_nonneg (Nat.cast_nonneg T) _
    have h2 : (j : ℝ) ^ (-(1 + ε)) ≤ (j : ℝ) ^ (-ε) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hj) (by linarith)
    have h3 : ((j : ℝ) ^ (-ε) - (T : ℝ) ^ (-ε)) / ε ≤ (j : ℝ) ^ (-ε) / ε := by
      gcongr; linarith
    calc (j : ℝ) ^ (-(1 + ε)) + ∑ n ∈ Icc (j + 1) T, (n : ℝ) ^ (-(1 + ε))
        ≤ (j : ℝ) ^ (-ε) + (j : ℝ) ^ (-ε) / ε := by linarith
      _ = (1 + 1 / ε) * (j : ℝ) ^ (-ε) := by ring

/-- **A pole-free dilation has receiver energy `O(1/j)`.** For `0 < ε < 1/2` there is `C` with
`E_T(b_j) ≤ C/j` for every `j ≥ 1` and every cutoff `T`. -/
theorem exists_weightPronicEnergy_poleFreeDilation_le {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ, 1 ≤ j → ∀ T : ℕ,
      weightPronicEnergy (poleFreeDilation ε j) (poleFreeMean ε j) T ≤ C / j := by
  have hε1 : ε < 1 := by linarith
  have h1ε : 0 < 1 - ε := by linarith
  have h12ε : 0 < 1 - 2 * ε := by linarith
  set Cq := 1 + 1 / (1 - ε) + 1 / ε with hCq
  set Z := ∑' d : ℕ, dampedSignWeight unitSign ε d / d with hZ
  set C₁ := 2 / (1 - ε) + 4 with hC₁
  have hZ0 : 0 ≤ Z := tsum_nonneg fun d => by
    simp only [dampedSignWeight, unitSign, one_mul]; positivity
  have hCq0 : 0 ≤ Cq := by
    rw [hCq]; have := one_div_pos.mpr h1ε; have := one_div_pos.mpr hε; linarith
  have hC₁0 : 0 ≤ C₁ := by
    rw [hC₁]; have := div_pos (by norm_num : (0 : ℝ) < 2) h1ε; linarith
  have hK1 : 0 ≤ 1 + 1 / (1 - 2 * ε) := by have := one_div_pos.mpr h12ε; linarith
  have hK2 : 0 ≤ 1 + 1 / ε := by have := one_div_pos.mpr hε; linarith
  refine ⟨2 * Cq ^ 2 * (1 + 1 / (1 - 2 * ε)) + 2 * Z ^ 2 + (8 + 2 * C₁ ^ 2 * (1 + 1 / ε)),
    add_nonneg (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hK1)
      (mul_nonneg (by norm_num) (sq_nonneg _)))
      (add_nonneg (by norm_num) (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hK2)),
    fun j hj T => ?_⟩
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  set A := weightCenteredPrefix (poleFreeDilation ε j) (poleFreeMean ε j) with hAdef
  set a := (j : ℝ) ^ (-(1 - ε)) with hadef
  have ha0 : 0 ≤ a := Real.rpow_nonneg hj0.le _
  rw [weightPronicEnergy, ← sum_filter_add_sum_filter_not (Icc 1 T) (· < j)]
  -- below the dilation
  have hlow : ∑ n ∈ (Icc 1 T).filter (· < j), A n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
      (2 * Cq ^ 2 * (1 + 1 / (1 - 2 * ε)) + 2 * Z ^ 2) / j := by
    have hterm : ∀ n ∈ (Icc 1 T).filter (· < j), A n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
        2 * a ^ 2 * Cq ^ 2 * (n : ℝ) ^ (-(2 * ε)) + 2 * Z ^ 2 / (j : ℝ) ^ 2 := by
      intro n hn
      simp only [mem_filter, mem_Icc] at hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1.1
      have hpr : (0 : ℝ) < (n : ℝ) * ((n : ℝ) + 1) := by positivity
      have hb := abs_weightCenteredPrefix_poleFreeDilation_le_of_lt hε hε1 hn.1.1 hn.2
      have hsq : A n ^ 2 ≤ 2 * (a * (Cq * (n : ℝ) ^ (1 - ε))) ^ 2 + 2 * (Z * n / j) ^ 2 := by
        have h0 : 0 ≤ a * (Cq * (n : ℝ) ^ (1 - ε)) :=
          mul_nonneg ha0 (mul_nonneg hCq0 (Real.rpow_nonneg hn0.le _))
        have h0' : 0 ≤ Z * n / j := div_nonneg (mul_nonneg hZ0 hn0.le) hj0.le
        have : A n ^ 2 ≤ (a * (Cq * (n : ℝ) ^ (1 - ε)) + Z * n / j) ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hb 2
        have key : ∀ X Y : ℝ, (X + Y) ^ 2 ≤ 2 * X ^ 2 + 2 * Y ^ 2 := fun X Y => by
          nlinarith [sq_nonneg (X - Y)]
        exact this.trans (key _ _)
      have hpow : ((n : ℝ) ^ (1 - ε)) ^ 2 = (n : ℝ) ^ 2 * (n : ℝ) ^ (-(2 * ε)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le, ← Real.rpow_natCast (n : ℝ) 2,
          ← Real.rpow_add hn0]
        congr 1; push_cast; ring
      rw [div_le_iff₀ hpr]
      have hn2 : (n : ℝ) ^ 2 ≤ (n : ℝ) * ((n : ℝ) + 1) := by nlinarith
      have hnε : 0 ≤ (n : ℝ) ^ (-(2 * ε)) := Real.rpow_nonneg hn0.le _
      calc A n ^ 2 ≤ 2 * (a * (Cq * (n : ℝ) ^ (1 - ε))) ^ 2 + 2 * (Z * n / j) ^ 2 := hsq
        _ = 2 * a ^ 2 * Cq ^ 2 * (n : ℝ) ^ (-(2 * ε)) * (n : ℝ) ^ 2 +
              2 * Z ^ 2 / (j : ℝ) ^ 2 * (n : ℝ) ^ 2 := by rw [mul_pow, mul_pow, hpow]; ring
        _ ≤ (2 * a ^ 2 * Cq ^ 2 * (n : ℝ) ^ (-(2 * ε)) + 2 * Z ^ 2 / (j : ℝ) ^ 2) *
              ((n : ℝ) * ((n : ℝ) + 1)) := by
            have h1 : 0 ≤ 2 * a ^ 2 * Cq ^ 2 * (n : ℝ) ^ (-(2 * ε)) + 2 * Z ^ 2 / (j : ℝ) ^ 2 :=
              add_nonneg (mul_nonneg (by positivity) hnε) (by positivity)
            rw [← add_mul]
            exact mul_le_mul_of_nonneg_left hn2 h1
    have hsub : (Icc 1 T).filter (· < j) ⊆ Icc 1 (j - 1) := fun n hn => by
      simp only [mem_filter, mem_Icc] at hn ⊢; omega
    have hcard : (((Icc 1 T).filter (· < j)).card : ℝ) ≤ j := by
      have := card_le_card hsub
      rw [Nat.card_Icc] at this
      have : ((Icc 1 T).filter (· < j)).card ≤ j := by omega
      exact_mod_cast this
    have hhead : ∑ n ∈ (Icc 1 T).filter (· < j), (n : ℝ) ^ (-(2 * ε)) ≤
        1 + (j : ℝ) ^ (1 - 2 * ε) / (1 - 2 * ε) := by
      calc ∑ n ∈ (Icc 1 T).filter (· < j), (n : ℝ) ^ (-(2 * ε))
          ≤ ∑ n ∈ Icc 1 (j - 1), (n : ℝ) ^ (-(2 * ε)) :=
            sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => Real.rpow_nonneg (Nat.cast_nonneg n) _
        _ ≤ 1 + ((j - 1 : ℕ) : ℝ) ^ (1 - 2 * ε) / (1 - 2 * ε) :=
            RHTower.sum_rpow_neg_head_le (by linarith) (by linarith) _
        _ ≤ 1 + (j : ℝ) ^ (1 - 2 * ε) / (1 - 2 * ε) := by
            gcongr
            exact_mod_cast Nat.sub_le j 1
    have ha2 : a ^ 2 = (j : ℝ) ^ (-(2 - 2 * ε)) := by
      rw [hadef, ← Real.rpow_natCast, ← Real.rpow_mul hj0.le]; congr 1; push_cast; ring
    have ha2j : a ^ 2 * (j : ℝ) ^ (1 - 2 * ε) = 1 / j := by
      rw [ha2, ← Real.rpow_add hj0, show -(2 - 2 * ε) + (1 - 2 * ε) = -1 by ring,
        Real.rpow_neg_one, one_div]
    have ha2le : a ^ 2 ≤ 1 / j := by
      rw [ha2, one_div, ← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hj) (by linarith)
    calc ∑ n ∈ (Icc 1 T).filter (· < j), A n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))
        ≤ ∑ n ∈ (Icc 1 T).filter (· < j),
            (2 * a ^ 2 * Cq ^ 2 * (n : ℝ) ^ (-(2 * ε)) + 2 * Z ^ 2 / (j : ℝ) ^ 2) := sum_le_sum hterm
      _ = 2 * a ^ 2 * Cq ^ 2 * ∑ n ∈ (Icc 1 T).filter (· < j), (n : ℝ) ^ (-(2 * ε)) +
            (((Icc 1 T).filter (· < j)).card : ℝ) * (2 * Z ^ 2 / (j : ℝ) ^ 2) := by
          rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
      _ ≤ 2 * a ^ 2 * Cq ^ 2 * (1 + (j : ℝ) ^ (1 - 2 * ε) / (1 - 2 * ε)) +
            (j : ℝ) * (2 * Z ^ 2 / (j : ℝ) ^ 2) := by
          gcongr
      _ = 2 * Cq ^ 2 * (a ^ 2 + a ^ 2 * (j : ℝ) ^ (1 - 2 * ε) / (1 - 2 * ε)) + 2 * Z ^ 2 / j := by
          have hjj : (j : ℝ) * (2 * Z ^ 2 / (j : ℝ) ^ 2) = 2 * Z ^ 2 / j := by
            field_simp <;> ring_nf
          rw [hjj]; ring
      _ ≤ 2 * Cq ^ 2 * (1 / j + 1 / j / (1 - 2 * ε)) + 2 * Z ^ 2 / j := by
          rw [ha2j]; gcongr
      _ = (2 * Cq ^ 2 * (1 + 1 / (1 - 2 * ε)) + 2 * Z ^ 2) / j := by ring
  -- beyond the dilation
  have hhigh : ∑ n ∈ (Icc 1 T).filter (fun n => ¬ n < j), A n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
      (8 + 2 * C₁ ^ 2 * (1 + 1 / ε)) / j := by
    have hfil : (Icc 1 T).filter (fun n => ¬ n < j) = Icc j T := by
      ext n; simp only [mem_filter, mem_Icc, not_lt]; omega
    rw [hfil]
    have hterm : ∀ n ∈ Icc j T, A n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
        8 * (1 / ((n : ℝ) * ((n : ℝ) + 1))) + 2 * C₁ ^ 2 * a * (n : ℝ) ^ (-(1 + ε)) := by
      intro n hn
      have hjn := (mem_Icc.mp hn).1
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hj.trans hjn
      have hpr : (0 : ℝ) < (n : ℝ) * ((n : ℝ) + 1) := by positivity
      have hb := abs_weightCenteredPrefix_poleFreeDilation_le_of_le hε hε1 hj hjn
      have hr0 : 0 ≤ Real.sqrt ((n : ℝ) / j) := Real.sqrt_nonneg _
      have hr2 : (Real.sqrt ((n : ℝ) / j) ^ (1 - ε)) ^ 2 = a * (n : ℝ) ^ (1 - ε) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hr0, Real.sqrt_eq_rpow, ← Real.rpow_mul
          (div_nonneg (Nat.cast_nonneg n) hj0.le), Real.div_rpow (Nat.cast_nonneg n) hj0.le, hadef,
          Real.rpow_neg hj0.le]
        push_cast
        rw [show 1 / 2 * ((1 - ε) * 2) = 1 - ε by ring]
        ring
      have hsq : A n ^ 2 ≤ 8 + 2 * C₁ ^ 2 * (a * (n : ℝ) ^ (1 - ε)) := by
        have h0 : 0 ≤ C₁ * Real.sqrt ((n : ℝ) / j) ^ (1 - ε) :=
          mul_nonneg hC₁0 (Real.rpow_nonneg hr0 _)
        have : A n ^ 2 ≤ (2 + C₁ * Real.sqrt ((n : ℝ) / j) ^ (1 - ε)) ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hb 2
        have key : ∀ X : ℝ, (2 + X) ^ 2 ≤ 8 + 2 * X ^ 2 := fun X => by nlinarith [sq_nonneg (X - 2)]
        calc A n ^ 2 ≤ (2 + C₁ * Real.sqrt ((n : ℝ) / j) ^ (1 - ε)) ^ 2 := this
          _ ≤ 8 + 2 * (C₁ * Real.sqrt ((n : ℝ) / j) ^ (1 - ε)) ^ 2 := key _
          _ = 8 + 2 * C₁ ^ 2 * (a * (n : ℝ) ^ (1 - ε)) := by rw [mul_pow, hr2]; ring
      have hpow : (n : ℝ) ^ (1 - ε) / ((n : ℝ) * ((n : ℝ) + 1)) ≤ (n : ℝ) ^ (-(1 + ε)) := by
        rw [div_le_iff₀ hpr]
        have : (n : ℝ) ^ (1 - ε) = (n : ℝ) ^ (-(1 + ε)) * ((n : ℝ) * n) := by
          rw [show (1 - ε) = -(1 + ε) + 1 + 1 by ring, Real.rpow_add_one hn0.ne',
            Real.rpow_add_one hn0.ne']
          ring
        rw [this]
        have hnε : 0 ≤ (n : ℝ) ^ (-(1 + ε)) := Real.rpow_nonneg hn0.le _
        exact mul_le_mul_of_nonneg_left (by nlinarith) hnε
      calc A n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))
          ≤ (8 + 2 * C₁ ^ 2 * (a * (n : ℝ) ^ (1 - ε))) / ((n : ℝ) * ((n : ℝ) + 1)) := by gcongr
        _ = 8 * (1 / ((n : ℝ) * ((n : ℝ) + 1))) +
              2 * C₁ ^ 2 * a * ((n : ℝ) ^ (1 - ε) / ((n : ℝ) * ((n : ℝ) + 1))) := by ring
        _ ≤ 8 * (1 / ((n : ℝ) * ((n : ℝ) + 1))) + 2 * C₁ ^ 2 * a * (n : ℝ) ^ (-(1 + ε)) := by
            gcongr
    have hpron := sum_Icc_pronic_tail_le hj T
    have hrp := sum_Icc_rpow_neg_one_sub_le hε hj T
    have haj : a * (j : ℝ) ^ (-ε) = 1 / j := by
      rw [hadef, ← Real.rpow_add hj0, show -(1 - ε) + -ε = -1 by ring, Real.rpow_neg_one, one_div]
    calc ∑ n ∈ Icc j T, A n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))
        ≤ ∑ n ∈ Icc j T, (8 * (1 / ((n : ℝ) * ((n : ℝ) + 1))) +
            2 * C₁ ^ 2 * a * (n : ℝ) ^ (-(1 + ε))) := sum_le_sum hterm
      _ = 8 * ∑ n ∈ Icc j T, 1 / ((n : ℝ) * ((n : ℝ) + 1)) +
            2 * C₁ ^ 2 * a * ∑ n ∈ Icc j T, (n : ℝ) ^ (-(1 + ε)) := by
          rw [sum_add_distrib, ← mul_sum, ← mul_sum]
      _ ≤ 8 * (1 / (j : ℝ)) + 2 * C₁ ^ 2 * a * ((1 + 1 / ε) * (j : ℝ) ^ (-ε)) :=
          add_le_add (mul_le_mul_of_nonneg_left hpron (by norm_num))
            (mul_le_mul_of_nonneg_left hrp (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) ha0))
      _ = 8 / j + 2 * C₁ ^ 2 * (1 + 1 / ε) * (a * (j : ℝ) ^ (-ε)) := by ring
      _ = (8 + 2 * C₁ ^ 2 * (1 + 1 / ε)) / j := by rw [haj]; ring
  calc _ ≤ (2 * Cq ^ 2 * (1 + 1 / (1 - 2 * ε)) + 2 * Z ^ 2) / j +
        (8 + 2 * C₁ ^ 2 * (1 + 1 / ε)) / j := add_le_add hlow hhigh
    _ = _ := by ring

/-! ### Assembly over the critical Wiener algebra -/

/-- The prefix of a finite sum of weights is the sum of the prefixes. -/
theorem weightCenteredPrefix_finset_sum {ι : Type*} (s : Finset ι) (c : ι → ℕ → ℝ) (m : ι → ℝ)
    (n : ℕ) :
    weightCenteredPrefix (fun d => ∑ i ∈ s, c i d) (∑ i ∈ s, m i) n =
      ∑ i ∈ s, weightCenteredPrefix (c i) (m i) n := by
  unfold weightCenteredPrefix
  rw [sum_sub_distrib, ← sum_mul]
  congr 1
  have h : ∀ j ∈ Icc 1 n, ∑ d ∈ j.divisors, ∑ i ∈ s, c i d = ∑ i ∈ s, ∑ d ∈ j.divisors, c i d :=
    fun j _ => sum_comm
  rw [sum_congr rfl h, sum_comm]

/-- **Critical Wiener kernels with a vanishing pole value pay the smooth power.** For
`0 < ε < 1/2`, a kernel with `Σ_j |k(j)| j^{-1/2} < ∞` and `Σ_j k(j) j^{-(1−ε)} = 0` makes
`k ⋆ d^{-ε}` paid. -/
theorem receiverBounded_dirichletConv_unit_of_critical {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2)
    {k : ℕ → ℝ} (hk : CriticalWiener k) (hK : ∑' j : ℕ, k j * (j : ℝ) ^ (-(1 - ε)) = 0) :
    ReceiverBounded (RHTower.dirichletConv k (dampedSignWeight unitSign ε)) := by
  obtain ⟨C, hC0, hC⟩ := exists_weightPronicEnergy_poleFreeDilation_le hε hε2
  have hS0 : 0 ≤ ∑' j : ℕ, |k j| * (j : ℝ) ^ (-(1 / 2 : ℝ)) := tsum_nonneg fun j => by positivity
  -- the kernel converges absolutely at the pole and at `s = 1`
  have hkpole : Summable (fun j : ℕ => k j * (j : ℝ) ^ (-(1 - ε))) := by
    refine hk.of_norm_bounded fun j => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg j) _)]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp only [Nat.cast_zero, Real.zero_rpow (show -(1 - ε) ≠ 0 by linarith),
        Real.zero_rpow (show -(1 / 2 : ℝ) ≠ 0 by norm_num), le_refl]
    · exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hj) (by linarith)
  have hkdiv : Summable (fun j : ℕ => k j / j) := hk.summable_abs_div.of_abs
  refine ⟨C * (∑' j : ℕ, |k j| * (j : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2, fun T => ?_⟩
  -- the truncated energies are bounded by Minkowski
  have hbound : ∀ J : ℕ, weightPronicEnergy (fun d => ∑ j ∈ Icc 1 J, k j * poleFreeDilation ε j d)
      (∑ j ∈ Icc 1 J, k j * poleFreeMean ε j) T ≤
        C * (∑' j : ℕ, |k j| * (j : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 := by
    intro J
    have hpre : weightCenteredPrefix (fun d => ∑ j ∈ Icc 1 J, k j * poleFreeDilation ε j d)
        (∑ j ∈ Icc 1 J, k j * poleFreeMean ε j) = fun n => ∑ j ∈ Icc 1 J,
          k j * weightCenteredPrefix (poleFreeDilation ε j) (poleFreeMean ε j) n := by
      funext n
      rw [weightCenteredPrefix_finset_sum (Icc 1 J) (fun j d => k j * poleFreeDilation ε j d)
        (fun j => k j * poleFreeMean ε j) n]
      exact sum_congr rfl fun j _ => weightCenteredPrefix_smul _ _ _ _
    have hnorm : pronicNorm (weightCenteredPrefix (fun d => ∑ j ∈ Icc 1 J,
        k j * poleFreeDilation ε j d) (∑ j ∈ Icc 1 J, k j * poleFreeMean ε j)) T ≤
        Real.sqrt C * ∑' j : ℕ, |k j| * (j : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [hpre]
      refine (pronicNorm_sum_le _ _ T).trans ?_
      have hj : ∀ j ∈ Icc 1 J, pronicNorm (fun n => k j *
          weightCenteredPrefix (poleFreeDilation ε j) (poleFreeMean ε j) n) T ≤
          Real.sqrt C * (|k j| * (j : ℝ) ^ (-(1 / 2 : ℝ))) := by
        intro j hj
        have hj1 := (mem_Icc.mp hj).1
        have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
        rw [pronicNorm_smul]
        have hE := hC j hj1 T
        rw [weightPronicEnergy_eq_sq_pronicNorm] at hE
        have hsq : pronicNorm (weightCenteredPrefix (poleFreeDilation ε j) (poleFreeMean ε j)) T ≤
            Real.sqrt C * (j : ℝ) ^ (-(1 / 2 : ℝ)) := by
          have h1 := Real.sqrt_le_sqrt hE
          rw [Real.sqrt_sq (pronicNorm_nonneg _ _), Real.sqrt_div' C hj0.le] at h1
          rwa [Real.sqrt_eq_rpow (j : ℝ), div_eq_mul_inv, ← Real.rpow_neg hj0.le] at h1
        calc |k j| * pronicNorm (weightCenteredPrefix (poleFreeDilation ε j) (poleFreeMean ε j)) T
            ≤ |k j| * (Real.sqrt C * (j : ℝ) ^ (-(1 / 2 : ℝ))) :=
              mul_le_mul_of_nonneg_left hsq (abs_nonneg _)
          _ = Real.sqrt C * (|k j| * (j : ℝ) ^ (-(1 / 2 : ℝ))) := by ring
      refine (sum_le_sum hj).trans ?_
      rw [← mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg C)
      exact hk.sum_le_tsum _ fun j _ => by positivity
    rw [weightPronicEnergy_eq_sq_pronicNorm]
    calc pronicNorm (weightCenteredPrefix (fun d => ∑ j ∈ Icc 1 J, k j * poleFreeDilation ε j d)
          (∑ j ∈ Icc 1 J, k j * poleFreeMean ε j)) T ^ 2
        ≤ (Real.sqrt C * ∑' j : ℕ, |k j| * (j : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 :=
          pow_le_pow_left₀ (pronicNorm_nonneg _ _) hnorm 2
      _ = C * (∑' j : ℕ, |k j| * (j : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hC0]
  -- the partial pole values tend to `0`
  have hpartial : Tendsto (fun J => ∑ j ∈ Icc 1 J, k j * (j : ℝ) ^ (-(1 - ε))) atTop (𝓝 0) := by
    have h := hkpole.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    rw [hK] at h
    refine h.congr fun J => ?_
    simp only [Function.comp_apply]
    exact sum_range_succ_eq_sum_Icc_one (f := fun j => k j * (j : ℝ) ^ (-(1 - ε)))
      (by rw [Nat.cast_zero, Real.zero_rpow (show -(1 - ε) ≠ 0 by linarith), mul_zero]) J
  -- the truncations converge to the convolution
  have hconv : ∀ d, Tendsto (fun J => ∑ j ∈ Icc 1 J, k j * poleFreeDilation ε j d) atTop
      (𝓝 (RHTower.dirichletConv k (dampedSignWeight unitSign ε) d)) := by
    intro d
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · have h0 : ∀ J : ℕ, ∑ j ∈ Icc 1 J, k j * poleFreeDilation ε j 0 = 0 := fun J => by
        simp [poleFreeDilation, RHTower.dirichletConv]
      have h1 : RHTower.dirichletConv k (dampedSignWeight unitSign ε) 0 = 0 := by
        simp [RHTower.dirichletConv]
      rw [h1]
      exact tendsto_const_nhds.congr fun J => (h0 J).symm
    have hd0 : d ≠ 0 := hd.ne'
    -- the target in sign form
    have htarget : RHTower.dirichletConv k (dampedSignWeight unitSign ε) d =
        (d : ℝ) ^ (-ε) * ∑ i ∈ d.divisors, k i * (i : ℝ) ^ ε := by
      simp only [RHTower.dirichletConv, mul_sum]
      refine sum_congr rfl fun i hi => ?_
      have hid : i ∣ d := Nat.dvd_of_mem_divisors hi
      have hi1 : 1 ≤ i := Nat.pos_of_mem_divisors hi
      simp only [dampedSignWeight, unitSign, one_mul, cast_div_rpow_neg hi1 hid]
      ring
    -- the truncation in sign form
    have htrunc : ∀ J : ℕ, d ≤ J → ∑ j ∈ Icc 1 J, k j * poleFreeDilation ε j d =
        (d : ℝ) ^ (-ε) * ∑ i ∈ d.divisors, k i * (i : ℝ) ^ ε -
          (d : ℝ) ^ (-ε) * ∑ j ∈ Icc 1 J, k j * (j : ℝ) ^ (-(1 - ε)) := by
      intro J hJ
      have hterm : ∀ j ∈ Icc 1 J, k j * poleFreeDilation ε j d =
          (d : ℝ) ^ (-ε) * (if j ∣ d then k j * (j : ℝ) ^ ε else 0) -
            (d : ℝ) ^ (-ε) * (k j * (j : ℝ) ^ (-(1 - ε))) := by
        intro j hj
        rw [poleFreeDilation, dirichletConv_poleFreeKernel (mem_Icc.mp hj).1]
        simp only [dampedSignWeight, poleFreeSign, hd0, if_false]
        split_ifs <;> ring
      rw [sum_congr rfl hterm, sum_sub_distrib, ← mul_sum, ← mul_sum, ← sum_filter]
      congr 2
      refine sum_congr ?_ fun _ _ => rfl
      ext i
      simp only [mem_filter, mem_Icc, Nat.mem_divisors]
      constructor
      · rintro ⟨-, h⟩; exact ⟨h, hd0⟩
      · rintro ⟨h, -⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos h hd, (Nat.le_of_dvd hd h).trans hJ⟩, h⟩
    rw [htarget]
    have hlim := ((hpartial.const_mul ((d : ℝ) ^ (-ε))).const_sub
      ((d : ℝ) ^ (-ε) * ∑ i ∈ d.divisors, k i * (i : ℝ) ^ ε))
    rw [mul_zero, sub_zero] at hlim
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop d] with J hJ
    exact (htrunc J hJ).symm
  -- the truncated means converge to the mean
  have hmean : Tendsto (fun J => ∑ j ∈ Icc 1 J, k j * poleFreeMean ε j) atTop
      (𝓝 (∑' d : ℕ, RHTower.dirichletConv k (dampedSignWeight unitSign ε) d / d)) := by
    have hmk : HasSum (fun j : ℕ => k j / j) (∑' j : ℕ, k j / j) := hkdiv.hasSum
    have hq := summable_unit_weight hε
    rw [(hasSum_dirichletConv_div hmk hq.hasSum hk.summable_abs_div hq.abs).tsum_eq]
    have hdivlim : Tendsto (fun J => ∑ j ∈ Icc 1 J, k j / j) atTop (𝓝 (∑' j : ℕ, k j / j)) := by
      refine (hmk.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)).congr fun J => ?_
      simp only [Function.comp_apply]
      exact sum_range_succ_eq_sum_Icc_one (f := fun j => k j / j) (by simp) J
    have hlim := (hdivlim.sub hpartial).mul_const (∑' d : ℕ, dampedSignWeight unitSign ε d / d)
    rw [sub_zero] at hlim
    refine hlim.congr fun J => ?_
    simp only [poleFreeMean]
    rw [← sum_sub_distrib, sum_mul]
    refine sum_congr rfl fun j _ => ?_
    ring
  exact le_of_tendsto' (tendsto_weightPronicEnergy_of_tendsto hconv hmean T) hbound

/-- **Critical Wiener perturbations of the smooth power are decided at the pole.** For
`0 < ε < 1/2` and `Σ_j |k(j)| j^{-1/2} < ∞`, the receiver of `k ⋆ d^{-ε}` is bounded if and only if
`Σ_j k(j) j^{-(1−ε)} = 0`. -/
theorem receiverBounded_dirichletConv_unit_iff_critical {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2)
    {k : ℕ → ℝ} (hk : CriticalWiener k) :
    ReceiverBounded (RHTower.dirichletConv k (dampedSignWeight unitSign ε)) ↔
      ∑' j : ℕ, k j * (j : ℝ) ^ (-(1 - ε)) = 0 := by
  constructor
  · intro hB
    by_contra hK
    exact not_receiverBounded_dirichletConv_of_drift_critical hε hε2.le
      (q := dampedSignWeight unitSign ε)
      (fun d => by simp [dampedSignWeight, unitSign, Real.rpow_nonneg]) (dampedClass_unit ε)
      (κ := (2 : ℝ) ^ (-(1 + ε))) (by positivity)
      (by filter_upwards [eventually_ge_atTop 1] with n hn using unit_drift hε.le hn) hk hK hB
  · exact receiverBounded_dirichletConv_unit_of_critical hε hε2 hk

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
