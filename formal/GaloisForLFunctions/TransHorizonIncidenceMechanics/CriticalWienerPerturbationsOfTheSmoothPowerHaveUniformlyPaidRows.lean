import GaloisForLFunctions.TransHorizonIncidenceMechanics.CriticalWienerPerturbationsOfTheSmoothPowerAreDecidedAtThePole

/-!
# Critical Wiener perturbations of the smooth power have uniformly paid rows

Below half damping the horizon limit does not commute with the receiver on the damped class
`𝒞(1, ε)`: lacunary dipoles give a paid weight whose dyadic rows `c · 1_{d ≤ 2^J}`, each centred at
its own mean, have unbounded receivers (`horizonLimit_commutes_with_receiver_iff`). On the
convolution class `k ⋆ d^{-ε}`, `Σ_j |k(j)| j^{-1/2} < ∞`, this dipole obstruction never occurs:
for every `0 < ε < 1/2`

`rows of k ⋆ d^{-ε} uniformly paid ⇔ k ⋆ d^{-ε} paid ⇔ K(1 − ε) = 0`

(`rows_bounded_iff_receiverBounded_dirichletConv_unit`,
`rows_bounded_iff_dirichletConv_unit_poleValue_eq_zero`).

* **Rows of a pole-free dilation.** The row of horizon `N` of `b_j = (δ_j − j^{-(1−ε)}δ_1) ⋆ d^{-ε}`
  has energy `O(1/j)` uniformly in `N` (`exists_weightPronicEnergy_dyadicRow_poleFreeDilation_le`).
  For `N < j` the row is `−j^{-(1−ε)}` times the row of the smooth power, whose energy is
  `O(N^{1−2ε})`. For `N ≥ j`, below `j` the row is `b_j` plus the drift `τn` with
  `|τ| ≤ 2j^ε (N+1)^{-1-ε} ≤ 2/j`; beyond `j` the row is again a damped sign with partial sums at
  most `j^ε`, dominated by `b_j`, so the sharp hyperbola bound applies to it unchanged.
* **The finite decomposition.** On the row of horizon `N` only the kernel values `j ≤ N` enter:
  `row(k ⋆ q) = Σ_{j ≤ N} k(j) row(b_j) + P_N row(q)`, `P_N = Σ_{j ≤ N} k(j) j^{-(1−ε)}`. When
  `K(1 − ε) = 0`, `|P_N| ≤ N^{-(1/2−ε)} Σ_j |k(j)| j^{-1/2}`, which exactly pays the growth
  `N^{1/2−ε}` of the smooth power's row. Minkowski gives one bound for all rows.

The convolution structure of the weight, which ties every dilation to the pole through the single
number `K(1 − ε)`, is what excludes cancelling dipoles: a horizon can only cut the weight into a
finite combination of rows of pole-free dilations and one row of the smooth power.
-/

open Finset Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### Rows of weights -/

/-- **Below its horizon a row is the weight plus a drift**: for `n ≤ 2^J`,
`A_{row}(n) = A_c(n) + (m − m_J) n`. -/
theorem weightCenteredPrefix_dyadicRow_of_le (c : ℕ → ℝ) (m : ℝ) {J n : ℕ} (hn : n ≤ 2 ^ J) :
    weightCenteredPrefix (dyadicRow c J) (dyadicRowMean c J) n =
      weightCenteredPrefix c m n + (m - dyadicRowMean c J) * n := by
  rw [weightCenteredPrefix, weightCenteredPrefix, sum_Icc_sum_divisors_eq_floor,
    sum_Icc_sum_divisors_eq_floor]
  have h : ∑ d ∈ Icc 1 n, dyadicRow c J d * ((n / d : ℕ) : ℝ) =
      ∑ d ∈ Icc 1 n, c d * ((n / d : ℕ) : ℝ) := sum_congr rfl fun d hd => by
    have : d ≤ 2 ^ J := (mem_Icc.mp hd).2.trans hn
    simp [dyadicRow, this]
  rw [h]; ring

/-- **Beyond its horizon a row is a sawtooth sum**: for `n > 2^J`, `|A_{row}(n)| ≤ Σ_{d ≤ 2^J} |c(d)|`. -/
theorem abs_weightCenteredPrefix_dyadicRow_le_of_lt (c : ℕ → ℝ) {J n : ℕ} (hn : 2 ^ J < n) :
    |weightCenteredPrefix (dyadicRow c J) (dyadicRowMean c J) n| ≤ ∑ d ∈ Icc 1 (2 ^ J), |c d| := by
  set N := 2 ^ J with hNdef
  have hN1 : 1 ≤ N := Nat.one_le_two_pow
  have heq : weightCenteredPrefix (dyadicRow c J) (dyadicRowMean c J) n =
      ∑ d ∈ Icc 1 N, c d * (((n / d : ℕ) : ℝ) - (n : ℝ) / d) := by
    rw [weightCenteredPrefix, sum_Icc_sum_divisors_eq_floor, dyadicRowMean_eq]
    have hsplit : Icc 1 n = Icc 1 N ∪ Ioc N n := by
      ext d; simp only [mem_union, mem_Icc, mem_Ioc]; omega
    have hdisj : Disjoint (Icc 1 N) (Ioc N n) := by
      rw [disjoint_left]; intro d h1 h2; simp only [mem_Icc, mem_Ioc] at h1 h2; omega
    rw [hsplit, sum_union hdisj]
    have hz : ∑ d ∈ Ioc N n, dyadicRow c J d * ((n / d : ℕ) : ℝ) = 0 :=
      sum_eq_zero fun d hd => by
        have : ¬ d ≤ 2 ^ J := by rw [← hNdef]; simp only [mem_Ioc] at hd; omega
        simp [dyadicRow, this]
    have hc' : ∑ d ∈ Icc 1 N, dyadicRow c J d * ((n / d : ℕ) : ℝ) =
        ∑ d ∈ Icc 1 N, c d * ((n / d : ℕ) : ℝ) := sum_congr rfl fun d hd => by
      have : d ≤ 2 ^ J := (mem_Icc.mp hd).2
      simp [dyadicRow, this]
    rw [hz, add_zero, hc', sum_mul, ← sum_sub_distrib]
    exact sum_congr rfl fun d _ => by ring
  rw [heq]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d hd => ?_)
  rw [abs_mul]
  calc |c d| * |((n / d : ℕ) : ℝ) - (n : ℝ) / d| ≤ |c d| * 1 :=
        mul_le_mul_of_nonneg_left (abs_natDiv_sub_div_le n d (mem_Icc.mp hd).1) (abs_nonneg _)
    _ = |c d| := mul_one _

/-- The row of a damped sign is the damped row of the sign. -/
theorem dyadicRow_dampedSignWeight (s : ℕ → ℝ) (ε : ℝ) (J : ℕ) :
    dyadicRow (dampedSignWeight s ε) J = dampedSignWeight (dyadicRow s J) ε := by
  funext d
  simp only [dyadicRow, dampedSignWeight]
  split_ifs <;> simp

/-- Truncation keeps the partial sums of a sign bounded. -/
theorem abs_sum_range_dyadicRow_le {s : ℕ → ℝ} {B : ℝ} (hS : ∀ x, |∑ d ∈ range x, s d| ≤ B)
    (J x : ℕ) : |∑ d ∈ range x, dyadicRow s J d| ≤ B := by
  have h : ∑ d ∈ range x, dyadicRow s J d = ∑ d ∈ range (min x (2 ^ J + 1)), s d := by
    simp only [dyadicRow]
    rw [← sum_filter]
    congr 1
    ext d; simp only [mem_filter, mem_range]; omega
  rw [h]; exact hS _

/-! ### Rows of the smooth power -/

/-- **The rows of the smooth power have energy `O(N^{1−2ε})`.** Below the horizon the row is the
smooth power plus the drift `τn`, `0 ≤ τ ≤ N^{-ε}/ε`; beyond it a sawtooth sum of mass
`Σ_{d ≤ N} d^{-ε}`. -/
theorem weightPronicEnergy_dyadicRow_unit_le {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) (J T : ℕ) :
    weightPronicEnergy (dyadicRow (dampedSignWeight unitSign ε) J)
        (dyadicRowMean (dampedSignWeight unitSign ε) J) T ≤
      ((1 + 1 / (1 - ε) + 1 / ε + 1 / ε) ^ 2 * (1 + 1 / (1 - 2 * ε)) + (1 + 1 / (1 - ε)) ^ 2) *
        ((2 ^ J : ℕ) : ℝ) ^ (1 - 2 * ε) := by
  have hε1 : ε < 1 := by linarith
  have h1ε : 0 < 1 - ε := by linarith
  have h12ε : 0 < 1 - 2 * ε := by linarith
  set q := dampedSignWeight unitSign ε with hqdef
  set N := 2 ^ J with hNdef
  have hN1 : 1 ≤ N := Nat.one_le_two_pow
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  set Cε := 1 + 1 / (1 - ε) + 1 / ε with hCε
  have hCε0 : 0 ≤ Cε := by
    rw [hCε]; have := one_div_pos.mpr h1ε; have := one_div_pos.mpr hε; linarith
  set m := ∑' d : ℕ, q d / d with hm
  have hsum : Summable (fun d : ℕ => q d / d) := summable_unit_weight hε
  -- the drift `τ = m − m_N`
  set τ := m - dyadicRowMean q J with hτ
  have hτeq : τ = ∑' k : ℕ, ((N : ℝ) + 1 + (k : ℝ)) ^ (-ε - 1) := by
    rw [hτ, hm, ← hsum.sum_add_tsum_nat_add (N + 1),
      sum_range_succ_eq_sum_Icc_one (f := fun d : ℕ => q d / d) (by simp) N, dyadicRowMean_eq]
    have : ∀ k : ℕ, q (k + (N + 1)) / ((k + (N + 1) : ℕ) : ℝ) = ((N : ℝ) + 1 + (k : ℝ)) ^ (-ε - 1) := by
      intro k
      have hk : (0 : ℝ) < (N : ℝ) + 1 + k := by positivity
      have hcast : ((k + (N + 1) : ℕ) : ℝ) = (N : ℝ) + 1 + k := by push_cast; ring
      rw [hqdef, dampedSignWeight_div hε, hcast, unitSign, mul_one, show -(1 + ε) = -ε - 1 by ring]
    rw [tsum_congr this]; ring
  have hτ0 : 0 ≤ τ := by
    rw [hτeq]; exact tsum_nonneg fun k => Real.rpow_nonneg (by positivity) _
  have hτle : τ ≤ (N : ℝ) ^ (-ε) / ε := by
    have h := HTGeometry.tsum_shift_rpow_le (q := -ε) (by linarith) hN1
    rw [neg_neg] at h
    rw [hτeq]; exact h
  have hτn : ∀ n : ℕ, 1 ≤ n → n ≤ N → τ * n ≤ (1 / ε) * (n : ℝ) ^ (1 - ε) := by
    intro n hn hnN
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have h1 : (N : ℝ) ^ (-ε) ≤ (n : ℝ) ^ (-ε) :=
      Real.rpow_le_rpow_of_nonpos hn0 (by exact_mod_cast hnN) (by linarith)
    have h2 : (n : ℝ) ^ (-ε) * n = (n : ℝ) ^ (1 - ε) := by
      rw [show (1 - ε) = -ε + 1 by ring, Real.rpow_add_one hn0.ne']
    calc τ * n ≤ (N : ℝ) ^ (-ε) / ε * n := mul_le_mul_of_nonneg_right hτle hn0.le
      _ ≤ (n : ℝ) ^ (-ε) / ε * n := by gcongr
      _ = (1 / ε) * (n : ℝ) ^ (1 - ε) := by rw [← h2]; ring
  rw [weightPronicEnergy, ← sum_filter_add_sum_filter_not (Icc 1 T) (· ≤ N)]
  -- below the horizon
  have hlow : ∑ n ∈ (Icc 1 T).filter (· ≤ N),
      weightCenteredPrefix (dyadicRow q J) (dyadicRowMean q J) n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
        (Cε + 1 / ε) ^ 2 * (1 + 1 / (1 - 2 * ε)) * (N : ℝ) ^ (1 - 2 * ε) := by
    have hterm : ∀ n ∈ (Icc 1 T).filter (· ≤ N),
        weightCenteredPrefix (dyadicRow q J) (dyadicRowMean q J) n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
          (Cε + 1 / ε) ^ 2 * (n : ℝ) ^ (-(2 * ε)) := by
      intro n hn
      simp only [mem_filter, mem_Icc] at hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1.1
      have hpr : (0 : ℝ) < (n : ℝ) * ((n : ℝ) + 1) := by positivity
      have hA := abs_weightCenteredPrefix_le_of_dampedClass hε hε1 (dampedClass_unit ε) hn.1.1
      rw [one_mul] at hA
      have hrow := weightCenteredPrefix_dyadicRow_of_le q m (J := J) hn.2
      have hb : |weightCenteredPrefix (dyadicRow q J) (dyadicRowMean q J) n| ≤
          (Cε + 1 / ε) * (n : ℝ) ^ (1 - ε) := by
        rw [hrow]
        have h1 := hτn n hn.1.1 hn.2
        have h2 : 0 ≤ τ * n := mul_nonneg hτ0 hn0.le
        calc |weightCenteredPrefix q m n + (m - dyadicRowMean q J) * n|
            ≤ |weightCenteredPrefix q m n| + |τ * n| := abs_add_le _ _
          _ ≤ Cε * (n : ℝ) ^ (1 - ε) + (1 / ε) * (n : ℝ) ^ (1 - ε) := by
              rw [abs_of_nonneg h2]; exact add_le_add hA h1
          _ = (Cε + 1 / ε) * (n : ℝ) ^ (1 - ε) := by ring
      have hpow : ((n : ℝ) ^ (1 - ε)) ^ 2 = (n : ℝ) ^ 2 * (n : ℝ) ^ (-(2 * ε)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le, ← Real.rpow_natCast (n : ℝ) 2,
          ← Real.rpow_add hn0]
        congr 1; push_cast; ring
      have hsq : weightCenteredPrefix (dyadicRow q J) (dyadicRowMean q J) n ^ 2 ≤
          (Cε + 1 / ε) ^ 2 * ((n : ℝ) ^ 2 * (n : ℝ) ^ (-(2 * ε))) := by
        rw [← hpow, ← mul_pow, ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hb 2
      rw [div_le_iff₀ hpr]
      have hnε : 0 ≤ (n : ℝ) ^ (-(2 * ε)) := Real.rpow_nonneg hn0.le _
      calc _ ≤ (Cε + 1 / ε) ^ 2 * ((n : ℝ) ^ 2 * (n : ℝ) ^ (-(2 * ε))) := hsq
        _ = (Cε + 1 / ε) ^ 2 * (n : ℝ) ^ (-(2 * ε)) * ((n : ℝ) * n) := by ring
        _ ≤ (Cε + 1 / ε) ^ 2 * (n : ℝ) ^ (-(2 * ε)) * ((n : ℝ) * ((n : ℝ) + 1)) := by
            gcongr; linarith
    have hsub : (Icc 1 T).filter (· ≤ N) ⊆ Icc 1 N := fun n hn => by
      simp only [mem_filter, mem_Icc] at hn ⊢; exact ⟨hn.1.1, hn.2⟩
    have hhead : ∑ n ∈ (Icc 1 T).filter (· ≤ N), (n : ℝ) ^ (-(2 * ε)) ≤
        (1 + 1 / (1 - 2 * ε)) * (N : ℝ) ^ (1 - 2 * ε) := by
      have hge : 1 ≤ (N : ℝ) ^ (1 - 2 * ε) := Real.one_le_rpow hNR h12ε.le
      calc ∑ n ∈ (Icc 1 T).filter (· ≤ N), (n : ℝ) ^ (-(2 * ε))
          ≤ ∑ n ∈ Icc 1 N, (n : ℝ) ^ (-(2 * ε)) :=
            sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => Real.rpow_nonneg (Nat.cast_nonneg n) _
        _ ≤ 1 + (N : ℝ) ^ (1 - 2 * ε) / (1 - 2 * ε) :=
            RHTower.sum_rpow_neg_head_le (by linarith) (by linarith) N
        _ ≤ (1 + 1 / (1 - 2 * ε)) * (N : ℝ) ^ (1 - 2 * ε) := by
            rw [add_mul, one_mul, div_eq_mul_one_div, mul_comm ((N : ℝ) ^ (1 - 2 * ε))]
            linarith
    calc _ ≤ ∑ n ∈ (Icc 1 T).filter (· ≤ N), (Cε + 1 / ε) ^ 2 * (n : ℝ) ^ (-(2 * ε)) :=
          sum_le_sum hterm
      _ = (Cε + 1 / ε) ^ 2 * ∑ n ∈ (Icc 1 T).filter (· ≤ N), (n : ℝ) ^ (-(2 * ε)) := by
          rw [mul_sum]
      _ ≤ (Cε + 1 / ε) ^ 2 * ((1 + 1 / (1 - 2 * ε)) * (N : ℝ) ^ (1 - 2 * ε)) :=
          mul_le_mul_of_nonneg_left hhead (sq_nonneg _)
      _ = _ := by ring
  -- beyond the horizon
  have hhigh : ∑ n ∈ (Icc 1 T).filter (fun n => ¬ n ≤ N),
      weightCenteredPrefix (dyadicRow q J) (dyadicRowMean q J) n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
        (1 + 1 / (1 - ε)) ^ 2 * (N : ℝ) ^ (1 - 2 * ε) := by
    have hmass : ∑ d ∈ Icc 1 N, |q d| ≤ (1 + 1 / (1 - ε)) * (N : ℝ) ^ (1 - ε) := by
      have hge : 1 ≤ (N : ℝ) ^ (1 - ε) := Real.one_le_rpow hNR h1ε.le
      have h := RHTower.sum_rpow_neg_head_le hε hε1 N
      have heq : ∑ d ∈ Icc 1 N, |q d| = ∑ d ∈ Icc 1 N, (d : ℝ) ^ (-ε) :=
        sum_congr rfl fun d _ => by
          simp only [hqdef, dampedSignWeight, unitSign, one_mul]
          exact abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)
      rw [heq]
      calc _ ≤ 1 + (N : ℝ) ^ (1 - ε) / (1 - ε) := h
        _ ≤ (1 + 1 / (1 - ε)) * (N : ℝ) ^ (1 - ε) := by
            rw [add_mul, one_mul, div_eq_mul_one_div, mul_comm ((N : ℝ) ^ (1 - ε))]
            linarith
    have hterm : ∀ n ∈ (Icc 1 T).filter (fun n => ¬ n ≤ N),
        weightCenteredPrefix (dyadicRow q J) (dyadicRowMean q J) n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
          ((1 + 1 / (1 - ε)) * (N : ℝ) ^ (1 - ε)) ^ 2 * (1 / ((n : ℝ) * ((n : ℝ) + 1))) := by
      intro n hn
      simp only [mem_filter, mem_Icc, not_le] at hn
      have hb := (abs_weightCenteredPrefix_dyadicRow_le_of_lt q (J := J) hn.2).trans hmass
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 1 ≤ n by omega)
      rw [mul_one_div]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hb 2
    have htail : ∑ n ∈ (Icc 1 T).filter (fun n => ¬ n ≤ N), 1 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
        1 / (N : ℝ) := by
      have hfil : (Icc 1 T).filter (fun n => ¬ n ≤ N) = Icc (N + 1) T := by
        ext n; simp only [mem_filter, mem_Icc, not_le]; omega
      rw [hfil]
      have h := sum_Icc_pronic_tail_le (X := N + 1) (by omega) T
      refine h.trans ?_
      push_cast
      exact one_div_le_one_div_of_le hN0 (by linarith)
    have hNpow : ((N : ℝ) ^ (1 - ε)) ^ 2 * (1 / (N : ℝ)) = (N : ℝ) ^ (1 - 2 * ε) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le, one_div, ← Real.rpow_neg_one,
        ← Real.rpow_add hN0]
      congr 1; push_cast; ring
    calc _ ≤ ∑ n ∈ (Icc 1 T).filter (fun n => ¬ n ≤ N),
          ((1 + 1 / (1 - ε)) * (N : ℝ) ^ (1 - ε)) ^ 2 * (1 / ((n : ℝ) * ((n : ℝ) + 1))) :=
          sum_le_sum hterm
      _ = ((1 + 1 / (1 - ε)) * (N : ℝ) ^ (1 - ε)) ^ 2 *
            ∑ n ∈ (Icc 1 T).filter (fun n => ¬ n ≤ N), 1 / ((n : ℝ) * ((n : ℝ) + 1)) := by
          rw [mul_sum]
      _ ≤ ((1 + 1 / (1 - ε)) * (N : ℝ) ^ (1 - ε)) ^ 2 * (1 / (N : ℝ)) :=
          mul_le_mul_of_nonneg_left htail (sq_nonneg _)
      _ = (1 + 1 / (1 - ε)) ^ 2 * (((N : ℝ) ^ (1 - ε)) ^ 2 * (1 / (N : ℝ))) := by ring
      _ = (1 + 1 / (1 - ε)) ^ 2 * (N : ℝ) ^ (1 - 2 * ε) := by rw [hNpow]
  have := add_le_add hlow hhigh
  calc _ ≤ _ := this
    _ = _ := by rw [hCε]; ring

/-! ### Rows of the pole-free dilations -/

/-- **Beyond the dilation, for every sign dominated by the pole-free sign**: a damped sign `σ` with
partial sums at most `j^ε` and `|σ(d)| d^{-ε} ≤ |b_j(d)|` has, for `n ≥ j`,
`|A_σ(n)| ≤ 2 + (2/(1−ε) + 4)(n/j)^{(1−ε)/2}`. -/
theorem abs_weightCenteredPrefix_dominated_le_of_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    {j n : ℕ} (hj : 1 ≤ j) (hjn : j ≤ n) {σ : ℕ → ℝ}
    (hS : ∀ x, |∑ d ∈ range x, σ d| ≤ (j : ℝ) ^ ε)
    (hdom : ∀ d, |dampedSignWeight σ ε d| ≤ |dampedSignWeight (poleFreeSign ε j) ε d|) :
    |weightCenteredPrefix (dampedSignWeight σ ε) (∑' d : ℕ, dampedSignWeight σ ε d / d) n| ≤
      2 + (2 / (1 - ε) + 4) * Real.sqrt ((n : ℝ) / j) ^ (1 - ε) := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hj0' : (j : ℝ) ≠ 0 := hj0.ne'
  have h1ε : 0 < 1 - ε := by linarith
  have ha0 : 0 ≤ (j : ℝ) ^ (-(1 - ε)) := Real.rpow_nonneg hj0.le _
  have ha1 : (j : ℝ) ^ (-(1 - ε)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hj) (by linarith)
  -- the split `D = ⌊√(jn)⌋`
  have hjD : j ≤ Nat.sqrt (j * n) := Nat.le_sqrt.mpr (Nat.mul_le_mul_left j hjn)
  have hDn : Nat.sqrt (j * n) ≤ n :=
    (Nat.sqrt_le_sqrt (Nat.mul_le_mul_right n hjn)).trans (Nat.sqrt_eq n).le
  have hmain := abs_weightCenteredPrefix_dampedSign_le_sum (Real.rpow_pos_of_pos hj0 ε).le hε
    hS (hj.trans hjD) hDn
  refine hmain.trans ?_
  have hpa := (sum_le_sum fun d (_ : d ∈ Icc 1 (Nat.sqrt (j * n))) => hdom d).trans
    (sum_abs_poleFreeDilation_le hε hε1 hj (Nat.sqrt (j * n)))
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
  have hT1 : (j : ℝ) ^ (-(1 - ε)) * ((Nat.sqrt (j * n) : ℕ) : ℝ) ^ (1 - ε) ≤
      Real.sqrt ((n : ℝ) / j) ^ (1 - ε) := by
    calc (j : ℝ) ^ (-(1 - ε)) * ((Nat.sqrt (j * n) : ℕ) : ℝ) ^ (1 - ε)
        ≤ (j : ℝ) ^ (-(1 - ε)) * ((j : ℝ) * Real.sqrt ((n : ℝ) / j)) ^ (1 - ε) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hD1 h1ε.le) ha0
      _ = Real.sqrt ((n : ℝ) / j) ^ (1 - ε) := by
          rw [Real.mul_rpow hj0.le hr0.le, ← mul_assoc, ← Real.rpow_add hj0, neg_add_cancel,
            Real.rpow_zero, one_mul]
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

/-- **The pronic tail of the beyond bound is `O(1/j)`**: any `f` with
`|f(n)| ≤ 2 + C₁ (n/j)^{(1−ε)/2}` on `n ≥ j` has `Σ_{j ≤ n ≤ T} f(n)²/(n(n+1)) ≤ (8 + 2C₁²(1+1/ε))/j`. -/
theorem sum_Icc_sq_le_of_beyond_bound {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) {j : ℕ} (hj : 1 ≤ j)
    {f : ℕ → ℝ}
    (hf : ∀ n, j ≤ n → |f n| ≤ 2 + (2 / (1 - ε) + 4) * Real.sqrt ((n : ℝ) / j) ^ (1 - ε))
    (T : ℕ) :
    ∑ n ∈ Icc j T, f n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
      (8 + 2 * (2 / (1 - ε) + 4) ^ 2 * (1 + 1 / ε)) / j := by
  have h1ε : 0 < 1 - ε := by linarith
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  set C₁ := 2 / (1 - ε) + 4 with hC₁
  have hC₁0 : 0 ≤ C₁ := by
    rw [hC₁]; have := div_pos (by norm_num : (0 : ℝ) < 2) h1ε; linarith
  set a := (j : ℝ) ^ (-(1 - ε)) with hadef
  have ha0 : 0 ≤ a := Real.rpow_nonneg hj0.le _
  have hterm : ∀ n ∈ Icc j T, f n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
      8 * (1 / ((n : ℝ) * ((n : ℝ) + 1))) + 2 * C₁ ^ 2 * a * (n : ℝ) ^ (-(1 + ε)) := by
    intro n hn
    have hjn := (mem_Icc.mp hn).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hj.trans hjn
    have hpr : (0 : ℝ) < (n : ℝ) * ((n : ℝ) + 1) := by positivity
    have hb := hf n hjn
    have hr0 : 0 ≤ Real.sqrt ((n : ℝ) / j) := Real.sqrt_nonneg _
    have hr2 : (Real.sqrt ((n : ℝ) / j) ^ (1 - ε)) ^ 2 = a * (n : ℝ) ^ (1 - ε) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hr0, Real.sqrt_eq_rpow, ← Real.rpow_mul
        (div_nonneg (Nat.cast_nonneg n) hj0.le), Real.div_rpow (Nat.cast_nonneg n) hj0.le, hadef,
        Real.rpow_neg hj0.le]
      push_cast
      rw [show 1 / 2 * ((1 - ε) * 2) = 1 - ε by ring]
      ring
    have hsq : f n ^ 2 ≤ 8 + 2 * C₁ ^ 2 * (a * (n : ℝ) ^ (1 - ε)) := by
      have h0 : 0 ≤ C₁ * Real.sqrt ((n : ℝ) / j) ^ (1 - ε) :=
        mul_nonneg hC₁0 (Real.rpow_nonneg hr0 _)
      have : f n ^ 2 ≤ (2 + C₁ * Real.sqrt ((n : ℝ) / j) ^ (1 - ε)) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hb 2
      have key : ∀ X : ℝ, (2 + X) ^ 2 ≤ 8 + 2 * X ^ 2 := fun X => by nlinarith [sq_nonneg (X - 2)]
      calc f n ^ 2 ≤ (2 + C₁ * Real.sqrt ((n : ℝ) / j) ^ (1 - ε)) ^ 2 := this
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
    calc f n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))
        ≤ (8 + 2 * C₁ ^ 2 * (a * (n : ℝ) ^ (1 - ε))) / ((n : ℝ) * ((n : ℝ) + 1)) := by gcongr
      _ = 8 * (1 / ((n : ℝ) * ((n : ℝ) + 1))) +
            2 * C₁ ^ 2 * a * ((n : ℝ) ^ (1 - ε) / ((n : ℝ) * ((n : ℝ) + 1))) := by ring
      _ ≤ 8 * (1 / ((n : ℝ) * ((n : ℝ) + 1))) + 2 * C₁ ^ 2 * a * (n : ℝ) ^ (-(1 + ε)) := by
          gcongr
  have hpron := sum_Icc_pronic_tail_le hj T
  have hrp := sum_Icc_rpow_neg_one_sub_le hε hj T
  have haj : a * (j : ℝ) ^ (-ε) = 1 / j := by
    rw [hadef, ← Real.rpow_add hj0, show -(1 - ε) + -ε = -1 by ring, Real.rpow_neg_one, one_div]
  calc ∑ n ∈ Icc j T, f n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))
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

/-- The drift of a row of a pole-free dilation: `|m_{b_j} − m_N| ≤ 2 j^ε (N+1)^{-1-ε}`. -/
theorem abs_poleFreeMean_sub_dyadicRowMean_le {ε : ℝ} (hε : 0 < ε) {j : ℕ} (hj : 1 ≤ j)
    (J : ℕ) :
    |poleFreeMean ε j - dyadicRowMean (poleFreeDilation ε j) J| ≤
      2 * (j : ℝ) ^ ε * ((2 ^ J + 1 : ℕ) : ℝ) ^ (-(1 + ε)) := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hb : poleFreeDilation ε j = dampedSignWeight (poleFreeSign ε j) ε := by
    rw [poleFreeDilation, dirichletConv_poleFreeKernel hj]
  have hS := abs_sum_range_poleFreeSign_le (ε := ε) hj
  have hsum := summable_dampedSignWeight_div (Real.rpow_pos_of_pos hj0 ε).le hε hS
  have htail := (abs_tsum_tail_rpow_le (Real.rpow_pos_of_pos hj0 ε).le
    (by linarith : 1 < 1 + ε) hS (k := 2 ^ J + 1) (Nat.le_add_left 1 _)).2
  have hmean : poleFreeMean ε j = ∑' d : ℕ, dampedSignWeight (poleFreeSign ε j) ε d / d := by
    rw [← hb]; exact (hasSum_poleFreeDilation_div hε j).tsum_eq.symm
  have hdiff : poleFreeMean ε j - dyadicRowMean (poleFreeDilation ε j) J =
      ∑' i : ℕ, ((i + (2 ^ J + 1) : ℕ) : ℝ) ^ (-(1 + ε)) * poleFreeSign ε j (i + (2 ^ J + 1)) := by
    rw [hmean, ← hsum.sum_add_tsum_nat_add (2 ^ J + 1),
      sum_range_succ_eq_sum_Icc_one (f := fun d : ℕ => dampedSignWeight (poleFreeSign ε j) ε d / d)
        (by simp) (2 ^ J), dyadicRowMean_eq, hb]
    rw [add_sub_cancel_left]
    exact tsum_congr fun i => dampedSignWeight_div hε _
  rw [hdiff]
  exact htail

/-- **The rows of a pole-free dilation have energy `O(1/j)`**, uniformly in the horizon: for
`0 < ε < 1/2` there is `C` with `E_T(row_J(b_j)) ≤ C/j` for all `j ≥ 1`, `J` and `T`. -/
theorem exists_weightPronicEnergy_dyadicRow_poleFreeDilation_le {ε : ℝ} (hε : 0 < ε)
    (hε2 : ε < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ, 1 ≤ j → ∀ J T : ℕ,
      weightPronicEnergy (dyadicRow (poleFreeDilation ε j) J)
        (dyadicRowMean (poleFreeDilation ε j) J) T ≤ C / j := by
  have hε1 : ε < 1 := by linarith
  have h1ε : 0 < 1 - ε := by linarith
  have h12ε : 0 < 1 - 2 * ε := by linarith
  obtain ⟨C2, hC20, hC2⟩ := exists_weightPronicEnergy_poleFreeDilation_le hε hε2
  set Cq := (1 + 1 / (1 - ε) + 1 / ε + 1 / ε) ^ 2 * (1 + 1 / (1 - 2 * ε)) +
    (1 + 1 / (1 - ε)) ^ 2 with hCq
  have hCq0 : 0 ≤ Cq := by
    rw [hCq]
    have : 0 ≤ 1 + 1 / (1 - 2 * ε) := by have := one_div_pos.mpr h12ε; linarith
    positivity
  set Cb := 8 + 2 * (2 / (1 - ε) + 4) ^ 2 * (1 + 1 / ε) with hCb
  have hCb0 : 0 ≤ Cb := by
    rw [hCb]; have : 0 ≤ 1 + 1 / ε := by have := one_div_pos.mpr hε; linarith
    positivity
  refine ⟨2 * C2 + 8 + Cb + Cq, by positivity, fun j hj J T => ?_⟩
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  set N := 2 ^ J with hNdef
  have hN1 : 1 ≤ N := Nat.one_le_two_pow
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  rcases lt_or_ge N j with hNj | hjN
  · -- below the dilation the row is a multiple of the smooth power's row
    set t := -(j : ℝ) ^ (-(1 - ε)) with ht
    have hrow : dyadicRow (poleFreeDilation ε j) J =
        fun d => t * dyadicRow (dampedSignWeight unitSign ε) J d := by
      funext d
      simp only [dyadicRow]
      split_ifs with hd
      · rcases Nat.eq_zero_or_pos d with rfl | hd0
        · simp [poleFreeDilation, RHTower.dirichletConv, dampedSignWeight,
            Real.zero_rpow (neg_ne_zero.mpr hε.ne')]
        · have hnd : ¬ j ∣ d := fun h => absurd (Nat.le_of_dvd hd0 h) (by omega)
          rw [poleFreeDilation, dirichletConv_poleFreeKernel hj]
          simp only [dampedSignWeight, poleFreeSign, hd0.ne', if_false, hnd, mul_zero, zero_sub,
            unitSign, ht]
          ring
      · ring
    have hmean : dyadicRowMean (poleFreeDilation ε j) J =
        t * dyadicRowMean (dampedSignWeight unitSign ε) J := by
      rw [dyadicRowMean, dyadicRowMean, hrow, mul_sum]
      exact sum_congr rfl fun d _ => by ring
    have hE := weightPronicEnergy_dyadicRow_unit_le hε hε2 J T
    rw [← hCq] at hE
    have ht2 : t ^ 2 = (j : ℝ) ^ (-(2 - 2 * ε)) := by
      rw [ht, neg_sq, ← Real.rpow_natCast, ← Real.rpow_mul hj0.le]; congr 1; push_cast; ring
    have hpow : (j : ℝ) ^ (-(2 - 2 * ε)) * (N : ℝ) ^ (1 - 2 * ε) ≤ 1 / j := by
      calc (j : ℝ) ^ (-(2 - 2 * ε)) * (N : ℝ) ^ (1 - 2 * ε)
          ≤ (j : ℝ) ^ (-(2 - 2 * ε)) * (j : ℝ) ^ (1 - 2 * ε) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hN0.le (by exact_mod_cast hNj.le)
              h12ε.le) (Real.rpow_nonneg hj0.le _)
        _ = 1 / j := by
            rw [← Real.rpow_add hj0, show -(2 - 2 * ε) + (1 - 2 * ε) = -1 by ring,
              Real.rpow_neg_one, one_div]
    have hscale : weightPronicEnergy (dyadicRow (poleFreeDilation ε j) J)
        (dyadicRowMean (poleFreeDilation ε j) J) T =
        t ^ 2 * weightPronicEnergy (dyadicRow (dampedSignWeight unitSign ε) J)
          (dyadicRowMean (dampedSignWeight unitSign ε) J) T := by
      rw [weightPronicEnergy, weightPronicEnergy, hrow, hmean, mul_sum]
      exact sum_congr rfl fun n _ => by rw [weightCenteredPrefix_smul]; ring
    rw [hscale, ht2]
    have hjε : 0 ≤ (j : ℝ) ^ (-(2 - 2 * ε)) := Real.rpow_nonneg hj0.le _
    calc (j : ℝ) ^ (-(2 - 2 * ε)) * weightPronicEnergy _ _ T
        ≤ (j : ℝ) ^ (-(2 - 2 * ε)) * (Cq * (N : ℝ) ^ (1 - 2 * ε)) :=
          mul_le_mul_of_nonneg_left hE hjε
      _ = Cq * ((j : ℝ) ^ (-(2 - 2 * ε)) * (N : ℝ) ^ (1 - 2 * ε)) := by ring
      _ ≤ Cq * (1 / j) := mul_le_mul_of_nonneg_left hpow hCq0
      _ ≤ (2 * C2 + 8 + Cb + Cq) / j := by
          rw [mul_one_div]
          exact div_le_div_of_nonneg_right (by linarith) hj0.le
  · -- at or beyond the dilation
    set A := weightCenteredPrefix (dyadicRow (poleFreeDilation ε j) J)
      (dyadicRowMean (poleFreeDilation ε j) J) with hAdef
    set τ := poleFreeMean ε j - dyadicRowMean (poleFreeDilation ε j) J with hτ
    have hτb : |τ| ≤ 2 / j := by
      have h := abs_poleFreeMean_sub_dyadicRowMean_le hε hj J
      have hle : ((2 ^ J + 1 : ℕ) : ℝ) ^ (-(1 + ε)) ≤ (j : ℝ) ^ (-(1 + ε)) :=
        Real.rpow_le_rpow_of_nonpos hj0
          (by push_cast; exact_mod_cast (show j ≤ 2 ^ J + 1 by rw [← hNdef]; omega)) (by linarith)
      have hjj : (j : ℝ) ^ ε * (j : ℝ) ^ (-(1 + ε)) = 1 / j := by
        rw [← Real.rpow_add hj0, show ε + -(1 + ε) = -1 by ring, Real.rpow_neg_one, one_div]
      calc |τ| ≤ 2 * (j : ℝ) ^ ε * ((2 ^ J + 1 : ℕ) : ℝ) ^ (-(1 + ε)) := h
        _ ≤ 2 * (j : ℝ) ^ ε * (j : ℝ) ^ (-(1 + ε)) :=
            mul_le_mul_of_nonneg_left hle (by positivity)
        _ = 2 / j := by rw [mul_assoc, hjj]; ring
    rw [weightPronicEnergy, ← sum_filter_add_sum_filter_not (Icc 1 T) (· < j)]
    -- below `j`: the dilation plus the drift
    have hlow : ∑ n ∈ (Icc 1 T).filter (· < j), A n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
        (2 * C2 + 8) / j := by
      have hterm : ∀ n ∈ (Icc 1 T).filter (· < j), A n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
          2 * (weightCenteredPrefix (poleFreeDilation ε j) (poleFreeMean ε j) n ^ 2 /
            ((n : ℝ) * ((n : ℝ) + 1))) + 2 * τ ^ 2 := by
        intro n hn
        simp only [mem_filter, mem_Icc] at hn
        have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1.1
        have hp : (0 : ℝ) < (n : ℝ) * ((n : ℝ) + 1) := by positivity
        have heq : A n = weightCenteredPrefix (poleFreeDilation ε j) (poleFreeMean ε j) n +
            τ * n := weightCenteredPrefix_dyadicRow_of_le _ _ (by omega)
        rw [heq, div_le_iff₀ hp]
        have hfrac : 2 * (weightCenteredPrefix (poleFreeDilation ε j) (poleFreeMean ε j) n ^ 2 /
            ((n : ℝ) * ((n : ℝ) + 1))) * ((n : ℝ) * ((n : ℝ) + 1)) =
            2 * weightCenteredPrefix (poleFreeDilation ε j) (poleFreeMean ε j) n ^ 2 := by
          field_simp
        rw [add_mul, hfrac]
        nlinarith [sq_nonneg (weightCenteredPrefix (poleFreeDilation ε j) (poleFreeMean ε j) n -
          τ * n), sq_nonneg τ]
      have hfull : ∑ n ∈ (Icc 1 T).filter (· < j),
          weightCenteredPrefix (poleFreeDilation ε j) (poleFreeMean ε j) n ^ 2 /
            ((n : ℝ) * ((n : ℝ) + 1)) ≤ C2 / j :=
        (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun n _ _ => by positivity).trans
          (hC2 j hj T)
      have hcard : (((Icc 1 T).filter (· < j)).card : ℝ) ≤ j := by
        have hsub : (Icc 1 T).filter (· < j) ⊆ Icc 1 j := fun n hn => by
          simp only [mem_filter, mem_Icc] at hn ⊢; omega
        have h := card_le_card hsub
        rw [Nat.card_Icc, Nat.add_sub_cancel] at h
        exact_mod_cast h
      have hτ2 : τ ^ 2 * j ≤ 4 / j := by
        have h1 : τ ^ 2 ≤ (2 / j) ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hτb 2
        calc τ ^ 2 * j ≤ (2 / j) ^ 2 * j := mul_le_mul_of_nonneg_right h1 hj0.le
          _ = 4 / j := by field_simp; ring
      calc ∑ n ∈ (Icc 1 T).filter (· < j), A n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))
          ≤ ∑ n ∈ (Icc 1 T).filter (· < j),
              (2 * (weightCenteredPrefix (poleFreeDilation ε j) (poleFreeMean ε j) n ^ 2 /
                ((n : ℝ) * ((n : ℝ) + 1))) + 2 * τ ^ 2) := sum_le_sum hterm
        _ = 2 * ∑ n ∈ (Icc 1 T).filter (· < j),
              weightCenteredPrefix (poleFreeDilation ε j) (poleFreeMean ε j) n ^ 2 /
                ((n : ℝ) * ((n : ℝ) + 1)) +
              (((Icc 1 T).filter (· < j)).card : ℝ) * (2 * τ ^ 2) := by
            rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
        _ ≤ 2 * (C2 / j) + (j : ℝ) * (2 * τ ^ 2) := by
            gcongr
        _ = 2 * (C2 / j) + 2 * (τ ^ 2 * j) := by ring
        _ ≤ 2 * (C2 / j) + 2 * (4 / j) := by gcongr
        _ = (2 * C2 + 8) / j := by ring
    -- beyond `j`: the row is a damped sign dominated by the pole-free sign
    have hhigh : ∑ n ∈ (Icc 1 T).filter (fun n => ¬ n < j), A n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
        Cb / j := by
      have hb : poleFreeDilation ε j = dampedSignWeight (poleFreeSign ε j) ε := by
        rw [poleFreeDilation, dirichletConv_poleFreeKernel hj]
      have hform : A = weightCenteredPrefix (dampedSignWeight (dyadicRow (poleFreeSign ε j) J) ε)
          (∑' d : ℕ, dampedSignWeight (dyadicRow (poleFreeSign ε j) J) ε d / d) := by
        rw [hAdef, hb, ← tsum_dyadicRow_div, dyadicRow_dampedSignWeight]
      have hS := abs_sum_range_dyadicRow_le (abs_sum_range_poleFreeSign_le (ε := ε) hj) J
      have hdom : ∀ d, |dampedSignWeight (dyadicRow (poleFreeSign ε j) J) ε d| ≤
          |dampedSignWeight (poleFreeSign ε j) ε d| := fun d => by
        rw [← dyadicRow_dampedSignWeight]
        simp only [dyadicRow]
        split_ifs <;> simp
      have hf : ∀ n, j ≤ n → |A n| ≤ 2 + (2 / (1 - ε) + 4) * Real.sqrt ((n : ℝ) / j) ^ (1 - ε) :=
        fun n hjn => by
          rw [hform]; exact abs_weightCenteredPrefix_dominated_le_of_le hε hε1 hj hjn hS hdom
      have hfil : (Icc 1 T).filter (fun n => ¬ n < j) = Icc j T := by
        ext n; simp only [mem_filter, mem_Icc, not_lt]; omega
      rw [hfil, hCb]
      exact sum_Icc_sq_le_of_beyond_bound hε hε1 hj hf T
    calc _ ≤ (2 * C2 + 8) / j + Cb / j := add_le_add hlow hhigh
      _ ≤ (2 * C2 + 8 + Cb + Cq) / j := by
          rw [← add_div]
          exact div_le_div_of_nonneg_right (by linarith) hj0.le

/-! ### The rows of the critical Wiener perturbations -/

/-- **The finite decomposition of a row.** Only `j ≤ 2^J` enter the row of horizon `2^J`:
`row(k ⋆ q) = Σ_{j ≤ 2^J} k(j) row(b_j) + P row(q)`, `P = Σ_{j ≤ 2^J} k(j) j^{-(1−ε)}`. -/
theorem dyadicRow_dirichletConv_unit_eq (k : ℕ → ℝ) {ε : ℝ} (hε : 0 < ε) (J : ℕ) :
    dyadicRow (RHTower.dirichletConv k (dampedSignWeight unitSign ε)) J = fun d =>
      ∑ j ∈ Icc 1 (2 ^ J), k j * dyadicRow (poleFreeDilation ε j) J d +
        (∑ j ∈ Icc 1 (2 ^ J), k j * (j : ℝ) ^ (-(1 - ε))) *
          dyadicRow (dampedSignWeight unitSign ε) J d := by
  funext d
  simp only [dyadicRow]
  split_ifs with hd
  · rw [sum_mul, ← sum_add_distrib]
    rcases Nat.eq_zero_or_pos d with rfl | hd0
    · simp [RHTower.dirichletConv, poleFreeDilation, dampedSignWeight,
        Real.zero_rpow (neg_ne_zero.mpr hε.ne')]
    -- the divisors of `d` lie below the horizon
    have hterm : ∀ j ∈ Icc 1 (2 ^ J), k j * poleFreeDilation ε j d +
        k j * (j : ℝ) ^ (-(1 - ε)) * dampedSignWeight unitSign ε d =
        if j ∣ d then k j * dampedSignWeight unitSign ε (d / j) else 0 := by
      intro j hj
      have hsplit : poleFreeDilation ε j d =
          (if j ∣ d then dampedSignWeight unitSign ε (d / j) else 0) -
            (j : ℝ) ^ (-(1 - ε)) * dampedSignWeight unitSign ε d := by
        simp only [poleFreeDilation, RHTower.dirichletConv, poleFreeKernel, sub_mul,
          sum_sub_distrib, ite_mul, one_mul, zero_mul, sum_ite_eq', Nat.mem_divisors,
          Nat.one_dvd, ne_eq, hd0.ne', not_false_eq_true, and_true, if_true, Nat.div_one]
      rw [hsplit]
      split_ifs <;> ring
    have hset : (Icc 1 (2 ^ J)).filter (fun j => j ∣ d) = d.divisors := by
      ext j
      simp only [mem_filter, mem_Icc, Nat.mem_divisors]
      constructor
      · rintro ⟨-, h⟩; exact ⟨h, hd0.ne'⟩
      · rintro ⟨h, -⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos h hd0, (Nat.le_of_dvd hd0 h).trans hd⟩, h⟩
    rw [sum_congr rfl hterm, ← sum_filter, hset]
    rfl
  · simp

/-- **Critical Wiener perturbations with a vanishing pole value have uniformly paid rows.** For
`0 < ε < 1/2`, `Σ_j |k(j)| j^{-1/2} < ∞` and `K(1 − ε) = 0`, every dyadic row of `k ⋆ d^{-ε}`,
centred at its own mean, has energy at most `(√C + √C_q)² (Σ_j |k(j)| j^{-1/2})²`. -/
theorem rows_bounded_of_critical {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) {k : ℕ → ℝ}
    (hk : CriticalWiener k) (hK : ∑' j : ℕ, k j * (j : ℝ) ^ (-(1 - ε)) = 0) :
    ∃ E : ℝ, ∀ J T : ℕ,
      weightPronicEnergy (dyadicRow (RHTower.dirichletConv k (dampedSignWeight unitSign ε)) J)
        (dyadicRowMean (RHTower.dirichletConv k (dampedSignWeight unitSign ε)) J) T ≤ E := by
  have h1ε : 0 < 1 - ε := by linarith
  have h12ε : 0 < 1 - 2 * ε := by linarith
  obtain ⟨C, hC0, hC⟩ := exists_weightPronicEnergy_dyadicRow_poleFreeDilation_le hε hε2
  set Cq := (1 + 1 / (1 - ε) + 1 / ε + 1 / ε) ^ 2 * (1 + 1 / (1 - 2 * ε)) +
    (1 + 1 / (1 - ε)) ^ 2 with hCq
  have hCq0 : 0 ≤ Cq := by
    rw [hCq]
    have : 0 ≤ 1 + 1 / (1 - 2 * ε) := by have := one_div_pos.mpr h12ε; linarith
    positivity
  have hW : Summable (fun j : ℕ => |k j| * (j : ℝ) ^ (-(1 / 2 : ℝ))) := hk
  set G := ∑' j : ℕ, |k j| * (j : ℝ) ^ (-(1 / 2 : ℝ)) with hG
  have hG0 : 0 ≤ G := tsum_nonneg fun j => by positivity
  refine ⟨((Real.sqrt C + Real.sqrt Cq) * G) ^ 2, fun J T => ?_⟩
  set q := dampedSignWeight unitSign ε with hqdef
  set N := 2 ^ J with hNdef
  have hN1 : 1 ≤ N := Nat.one_le_two_pow
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  set P := ∑ j ∈ Icc 1 N, k j * (j : ℝ) ^ (-(1 - ε)) with hP
  -- the prefix of the row in the finite decomposition
  have hrow := dyadicRow_dirichletConv_unit_eq k hε J
  have hmean : dyadicRowMean (RHTower.dirichletConv k q) J =
      ∑ j ∈ Icc 1 N, k j * dyadicRowMean (poleFreeDilation ε j) J + P * dyadicRowMean q J := by
    rw [dyadicRowMean, hrow]
    simp only [dyadicRowMean, add_div, sum_add_distrib, sum_div, mul_sum]
    rw [sum_comm]
    congr 1
    · exact sum_congr rfl fun j _ => sum_congr rfl fun d _ => by ring
    · exact sum_congr rfl fun d _ => by ring
  have hpre : weightCenteredPrefix (dyadicRow (RHTower.dirichletConv k q) J)
      (dyadicRowMean (RHTower.dirichletConv k q) J) = fun n =>
        ∑ j ∈ Icc 1 N, k j * weightCenteredPrefix (dyadicRow (poleFreeDilation ε j) J)
          (dyadicRowMean (poleFreeDilation ε j) J) n +
        P * weightCenteredPrefix (dyadicRow q J) (dyadicRowMean q J) n := by
    funext n
    rw [hrow, hmean, weightCenteredPrefix_add, weightCenteredPrefix_finset_sum,
      weightCenteredPrefix_smul]
    congr 1
    exact sum_congr rfl fun j _ => weightCenteredPrefix_smul _ _ _ _
  -- the pole part of the row: `|P| ≤ (N+1)^{-(1/2−ε)} G`
  set a := 1 / 2 - ε with ha
  have ha0 : 0 ≤ a := by rw [ha]; linarith
  have hPb : |P| ≤ ((N : ℝ) + 1) ^ (-a) * G := by
    have hs : Summable (fun j : ℕ => k j * (j : ℝ) ^ (-(1 - ε))) := by
      refine hk.of_norm_bounded fun j => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg j) _)]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · simp only [Nat.cast_zero, Real.zero_rpow (show -(1 - ε) ≠ 0 by linarith),
          Real.zero_rpow (show -(1 / 2 : ℝ) ≠ 0 by norm_num), le_refl]
      · exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hj) (by linarith)
    have hsplit := hs.sum_add_tsum_nat_add (N + 1)
    rw [sum_range_succ_eq_sum_Icc_one (f := fun j : ℕ => k j * (j : ℝ) ^ (-(1 - ε)))
      (by simp only [Nat.cast_zero, Real.zero_rpow (show -(1 - ε) ≠ 0 by linarith), mul_zero])
      N, ← hP, hK] at hsplit
    have hPeq : P = -∑' i : ℕ, k (i + (N + 1)) * ((i + (N + 1) : ℕ) : ℝ) ^ (-(1 - ε)) := by
      linarith
    have hbound : ∀ i : ℕ, ‖k (i + (N + 1)) * ((i + (N + 1) : ℕ) : ℝ) ^ (-(1 - ε))‖ ≤
        ((N : ℝ) + 1) ^ (-a) * (|k (i + (N + 1))| * ((i + (N + 1) : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) := by
      intro i
      have hi0 : (0 : ℝ) < ((i + (N + 1) : ℕ) : ℝ) := by positivity
      have hge : (N : ℝ) + 1 ≤ ((i + (N + 1) : ℕ) : ℝ) := by
        push_cast; linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
      have hsplitpow : ((i + (N + 1) : ℕ) : ℝ) ^ (-(1 - ε)) =
          ((i + (N + 1) : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) * ((i + (N + 1) : ℕ) : ℝ) ^ (-a) := by
        rw [← Real.rpow_add hi0, ha]; congr 1; ring
      have hle : ((i + (N + 1) : ℕ) : ℝ) ^ (-a) ≤ ((N : ℝ) + 1) ^ (-a) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hge (by linarith)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hi0.le _), hsplitpow]
      have h1 : 0 ≤ |k (i + (N + 1))| * ((i + (N + 1) : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) :=
        mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hi0.le _)
      calc |k (i + (N + 1))| * (((i + (N + 1) : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) *
            ((i + (N + 1) : ℕ) : ℝ) ^ (-a))
          = (|k (i + (N + 1))| * ((i + (N + 1) : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) *
              ((i + (N + 1) : ℕ) : ℝ) ^ (-a) := by ring
        _ ≤ (|k (i + (N + 1))| * ((i + (N + 1) : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) *
              ((N : ℝ) + 1) ^ (-a) := mul_le_mul_of_nonneg_left hle h1
        _ = _ := by ring
    have htailW : Summable (fun i : ℕ => |k (i + (N + 1))| * ((i + (N + 1) : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) :=
      hW.comp_injective (add_left_injective (N + 1))
    have htailG : ∑' i : ℕ, |k (i + (N + 1))| * ((i + (N + 1) : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) ≤ G := by
      have h := hW.sum_add_tsum_nat_add (N + 1)
      have h0 : 0 ≤ ∑ i ∈ range (N + 1), |k i| * (i : ℝ) ^ (-(1 / 2 : ℝ)) :=
        sum_nonneg fun i _ => by positivity
      rw [hG]; linarith
    have hnorm := tsum_of_norm_bounded ((htailW.mul_left (((N : ℝ) + 1) ^ (-a))).hasSum) hbound
    rw [tsum_mul_left] at hnorm
    rw [hPeq, abs_neg]
    calc |∑' i : ℕ, k (i + (N + 1)) * ((i + (N + 1) : ℕ) : ℝ) ^ (-(1 - ε))|
        ≤ ((N : ℝ) + 1) ^ (-a) *
            ∑' i : ℕ, |k (i + (N + 1))| * ((i + (N + 1) : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := hnorm
      _ ≤ ((N : ℝ) + 1) ^ (-a) * G :=
          mul_le_mul_of_nonneg_left htailG (Real.rpow_nonneg (by positivity) _)
  -- the norms of the pieces
  have hnormj : ∀ j ∈ Icc 1 N, pronicNorm (weightCenteredPrefix (dyadicRow (poleFreeDilation ε j) J)
      (dyadicRowMean (poleFreeDilation ε j) J)) T ≤ Real.sqrt C * (j : ℝ) ^ (-(1 / 2 : ℝ)) := by
    intro j hj
    have hj1 := (mem_Icc.mp hj).1
    have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
    have hE := hC j hj1 J T
    rw [weightPronicEnergy_eq_sq_pronicNorm] at hE
    have h1 := Real.sqrt_le_sqrt hE
    rw [Real.sqrt_sq (pronicNorm_nonneg _ _)] at h1
    refine h1.trans (le_of_eq ?_)
    rw [Real.sqrt_div' _ hj0.le, Real.rpow_neg hj0.le, ← Real.sqrt_eq_rpow, div_eq_mul_inv]
  have hnormq : pronicNorm (weightCenteredPrefix (dyadicRow q J) (dyadicRowMean q J)) T ≤
      Real.sqrt Cq * (N : ℝ) ^ a := by
    have hE := weightPronicEnergy_dyadicRow_unit_le hε hε2 J T
    rw [← hCq, weightPronicEnergy_eq_sq_pronicNorm] at hE
    have h1 := Real.sqrt_le_sqrt hE
    rw [Real.sqrt_sq (pronicNorm_nonneg _ _)] at h1
    refine h1.trans (le_of_eq ?_)
    rw [Real.sqrt_mul hCq0, Real.sqrt_eq_rpow ((N : ℝ) ^ (1 - 2 * ε)), ← Real.rpow_mul hN0.le, ha]
    congr 2; ring
  have hNa : ((N : ℝ) + 1) ^ (-a) * (N : ℝ) ^ a ≤ 1 := by
    have h1 : ((N : ℝ) + 1) ^ (-a) ≤ (N : ℝ) ^ (-a) :=
      Real.rpow_le_rpow_of_nonpos hN0 (by linarith) (by linarith)
    calc ((N : ℝ) + 1) ^ (-a) * (N : ℝ) ^ a ≤ (N : ℝ) ^ (-a) * (N : ℝ) ^ a :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hN0.le _)
      _ = 1 := by rw [← Real.rpow_add hN0, neg_add_cancel, Real.rpow_zero]
  have hsumj : ∑ j ∈ Icc 1 N, |k j| * (Real.sqrt C * (j : ℝ) ^ (-(1 / 2 : ℝ))) ≤
      Real.sqrt C * G := by
    have h1 : ∑ j ∈ Icc 1 N, |k j| * (Real.sqrt C * (j : ℝ) ^ (-(1 / 2 : ℝ))) =
        Real.sqrt C * ∑ j ∈ Icc 1 N, |k j| * (j : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [mul_sum]; exact sum_congr rfl fun j _ => by ring
    rw [h1]
    exact mul_le_mul_of_nonneg_left (hW.sum_le_tsum _ fun j _ => by positivity)
      (Real.sqrt_nonneg _)
  -- Minkowski over the finite decomposition
  have hnorm : pronicNorm (weightCenteredPrefix (dyadicRow (RHTower.dirichletConv k q) J)
      (dyadicRowMean (RHTower.dirichletConv k q) J)) T ≤ (Real.sqrt C + Real.sqrt Cq) * G := by
    rw [hpre]
    refine (pronicNorm_add_le _ _ T).trans ?_
    have h1 := pronicNorm_sum_le (Icc 1 N) (fun j n => k j * weightCenteredPrefix
      (dyadicRow (poleFreeDilation ε j) J) (dyadicRowMean (poleFreeDilation ε j) J) n) T
    have h2 : ∑ j ∈ Icc 1 N, pronicNorm (fun n => k j * weightCenteredPrefix
        (dyadicRow (poleFreeDilation ε j) J) (dyadicRowMean (poleFreeDilation ε j) J) n) T ≤
        Real.sqrt C * G := by
      refine le_trans (sum_le_sum fun j hj => ?_) hsumj
      rw [pronicNorm_smul]
      exact mul_le_mul_of_nonneg_left (hnormj j hj) (abs_nonneg _)
    have h3 : pronicNorm (fun n => P * weightCenteredPrefix (dyadicRow q J) (dyadicRowMean q J) n) T ≤
        Real.sqrt Cq * G := by
      rw [pronicNorm_smul]
      have hPG : 0 ≤ ((N : ℝ) + 1) ^ (-a) * G := mul_nonneg (Real.rpow_nonneg (by positivity) _) hG0
      have hCG : 0 ≤ Real.sqrt Cq * G := mul_nonneg (Real.sqrt_nonneg _) hG0
      calc |P| * pronicNorm (weightCenteredPrefix (dyadicRow q J) (dyadicRowMean q J)) T
          ≤ (((N : ℝ) + 1) ^ (-a) * G) * (Real.sqrt Cq * (N : ℝ) ^ a) :=
            mul_le_mul hPb hnormq (pronicNorm_nonneg _ _) hPG
        _ = Real.sqrt Cq * G * (((N : ℝ) + 1) ^ (-a) * (N : ℝ) ^ a) := by ring
        _ ≤ Real.sqrt Cq * G * 1 := mul_le_mul_of_nonneg_left hNa hCG
        _ = Real.sqrt Cq * G := mul_one _
    calc _ ≤ Real.sqrt C * G + Real.sqrt Cq * G := add_le_add (h1.trans h2) h3
      _ = (Real.sqrt C + Real.sqrt Cq) * G := by ring
  rw [weightPronicEnergy_eq_sq_pronicNorm]
  exact pow_le_pow_left₀ (pronicNorm_nonneg _ _) hnorm 2

/-- **The convolution structure prevents the dipole obstruction.** For `0 < ε < 1/2` and every
kernel of the critical Wiener algebra, the dyadic rows of `k ⋆ d^{-ε}`, each centred at its own
mean, are uniformly paid if and only if `k ⋆ d^{-ε}` is paid. -/
theorem rows_bounded_iff_receiverBounded_dirichletConv_unit {ε : ℝ} (hε : 0 < ε)
    (hε2 : ε < 1 / 2) {k : ℕ → ℝ} (hk : CriticalWiener k) :
    (∃ E : ℝ, ∀ J T : ℕ,
      weightPronicEnergy (dyadicRow (RHTower.dirichletConv k (dampedSignWeight unitSign ε)) J)
        (dyadicRowMean (RHTower.dirichletConv k (dampedSignWeight unitSign ε)) J) T ≤ E) ↔
      ReceiverBounded (RHTower.dirichletConv k (dampedSignWeight unitSign ε)) := by
  constructor
  · rintro ⟨E, hE⟩
    have hq := summable_unit_weight hε
    have hm := hasSum_dirichletConv_div hk.summable_abs_div.of_abs.hasSum hq.hasSum
      hk.summable_abs_div hq.abs
    exact ⟨E, fun T => weightPronicEnergy_le_of_rows_le hm.summable.hasSum hE T⟩
  · intro hB
    exact rows_bounded_of_critical hε hε2 hk
      ((receiverBounded_dirichletConv_unit_iff_critical hε hε2 hk).1 hB)

/-- **The rows are decided at the pole.** For `0 < ε < 1/2` and `Σ_j |k(j)| j^{-1/2} < ∞`, the rows
of `k ⋆ d^{-ε}` are uniformly paid iff `K(1 − ε) = Σ_j k(j) j^{-(1−ε)} = 0`. -/
theorem rows_bounded_iff_dirichletConv_unit_poleValue_eq_zero {ε : ℝ} (hε : 0 < ε)
    (hε2 : ε < 1 / 2) {k : ℕ → ℝ} (hk : CriticalWiener k) :
    (∃ E : ℝ, ∀ J T : ℕ,
      weightPronicEnergy (dyadicRow (RHTower.dirichletConv k (dampedSignWeight unitSign ε)) J)
        (dyadicRowMean (RHTower.dirichletConv k (dampedSignWeight unitSign ε)) J) T ≤ E) ↔
      ∑' j : ℕ, k j * (j : ℝ) ^ (-(1 - ε)) = 0 :=
  (rows_bounded_iff_receiverBounded_dirichletConv_unit hε hε2 hk).trans
    (receiverBounded_dirichletConv_unit_iff_critical hε hε2 hk)

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
