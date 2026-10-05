import GaloisForLFunctions.RHTower.StepFunctionCarrier
import GaloisForLFunctions.RHTower.DetectorDuality
import GaloisForLFunctions.RHTower.BaezDuarteDistance

/-!
# Dual sequences for the discrete Báez--Duarte distances

In the discrete carrier `ℓ²(ℕ≥1, 1/(k(k+1)))` the target is the constant sequence `1` and the
generators are `e_m(k) = (k mod m)/m`.  For a finitely supported sequence `A` put
`W_k = k(k+1)(A_k − A_{k+1})` and `w = stepVec W`.  Summation by parts gives

* `⟪w, 1⟫ = A_1`,
* `⟪w, e_m⟫ = (1/m) Σ_k A_k − Σ_{m ∣ k} A_k`  (since `e_m(k) − e_m(k−1) = 1/m − [m ∣ k]`),
* `‖w‖² = Σ_k k(k+1)(A_k − A_{k+1})²`.

So if `Σ_{m ∣ k} A_k = (1/m) Σ_k A_k` for `2 ≤ m ≤ N` and `A_1 = 1`, the vector `w` annihilates the
first `N` generators and `1 ≤ d_N² Σ_k k(k+1)(A_k − A_{k+1})²`
(`one_le_bdDistDiscrete_sq_mul_energy`).

The constraints are linear in `A`.  For a prime `P > N` the sequences `δ_d − δ_P` have defects
`[m ∣ d]`, and Möbius inversion over the divisor lattice gives an exact right inverse with
`|x_d| ≤ Σ |v|` (`bdModDefect_bdMoebiusCorrection`): any small defect vector is cancelled by a
correction of comparable size, supported on `[2, N] ∪ {P}` and vanishing at `1`.
-/

open Finset

namespace RHTower

noncomputable section

/-! ## Dual sequences in the discrete carrier -/

/-- The dual weight `W_k = k(k+1)(A_k − A_{k+1})` of a sequence `A`. -/
def bdDualWeight (A : ℕ → ℝ) (k : ℕ) : ℝ := (k : ℝ) * ((k : ℝ) + 1) * (A k - A (k + 1))

/-- The weighted energy `Σ_{k ≤ K} k(k+1)(A_k − A_{k+1})²`. -/
def bdDualEnergy (A : ℕ → ℝ) (K : ℕ) : ℝ :=
  ∑ n ∈ range K, ((n : ℝ) + 1) * ((n : ℝ) + 2) * (A (n + 1) - A (n + 2)) ^ 2

theorem bdDualWeight_eq_zero {A : ℕ → ℝ} {K : ℕ} (hA : ∀ k, K < k → A k = 0) {k : ℕ}
    (hk : K < k) : bdDualWeight A k = 0 := by
  simp [bdDualWeight, hA k hk, hA (k + 1) (by omega)]

theorem abs_bdDualWeight_le {A : ℕ → ℝ} {K : ℕ} (hA : ∀ k, K < k → A k = 0) (k : ℕ) :
    |bdDualWeight A k| ≤ ∑ j ∈ range (K + 1), |bdDualWeight A j| := by
  by_cases hk : k ≤ K
  · exact single_le_sum (f := fun j => |bdDualWeight A j|) (fun j _ => abs_nonneg _)
      (mem_range.mpr (by omega))
  · rw [bdDualWeight_eq_zero hA (by omega), abs_zero]
    exact sum_nonneg fun j _ => abs_nonneg _

/-- Summation by parts on `range K`. -/
theorem sum_range_dualDiff_mul_eq (A f : ℕ → ℝ) (hf : f 0 = 0) (K : ℕ) :
    ∑ n ∈ range K, (A (n + 1) - A (n + 2)) * f (n + 1) =
      ∑ n ∈ range K, A (n + 1) * (f (n + 1) - f n) - A (K + 1) * f K := by
  induction K with
  | zero => simp [hf]
  | succ K ih =>
    rw [sum_range_succ, ih, sum_range_succ]
    ring

theorem modSeq_succ_sub (m k : ℕ) (hm : 1 ≤ m) :
    (((k + 1) % m : ℕ) : ℝ) / (m : ℝ) - ((k % m : ℕ) : ℝ) / (m : ℝ) =
      1 / (m : ℝ) - if m ∣ k + 1 then 1 else 0 := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have h1 := Nat.mod_add_div (k + 1) m
  have h2 := Nat.mod_add_div k m
  have h3 := Nat.succ_div (a := k) (b := m)
  have e1 : (((k + 1) % m : ℕ) : ℝ) = (k : ℝ) + 1 - (m : ℝ) * (((k + 1) / m : ℕ) : ℝ) := by
    have : (((k + 1) % m : ℕ) : ℝ) + (m : ℝ) * (((k + 1) / m : ℕ) : ℝ) = (k : ℝ) + 1 := by
      exact_mod_cast h1
    linarith
  have e2 : ((k % m : ℕ) : ℝ) = (k : ℝ) - (m : ℝ) * ((k / m : ℕ) : ℝ) := by
    have : ((k % m : ℕ) : ℝ) + (m : ℝ) * ((k / m : ℕ) : ℝ) = (k : ℝ) := by exact_mod_cast h2
    linarith
  rw [e1, e2, h3]
  split_ifs <;> push_cast <;> field_simp <;> ring

/-- The pairing of a finitely supported dual sequence with a modular generator. -/
theorem sum_dual_mul_modSeq {A : ℕ → ℝ} {K : ℕ} (hA : ∀ k, K < k → A k = 0) {m : ℕ}
    (hm : 1 ≤ m) :
    ∑ n ∈ range K, (A (n + 1) - A (n + 2)) * ((((n + 1) % m : ℕ) : ℝ) / (m : ℝ)) =
      (1 / (m : ℝ)) * ∑ n ∈ range K, A (n + 1) -
        ∑ n ∈ (range K).filter (fun n => m ∣ n + 1), A (n + 1) := by
  have h := sum_range_dualDiff_mul_eq A (fun k => ((k % m : ℕ) : ℝ) / (m : ℝ)) (by simp) K
  rw [h, hA (K + 1) (by omega), zero_mul, sub_zero, sum_filter, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun n _ => ?_
  rw [modSeq_succ_sub m n hm]
  split_ifs <;> ring

/-! ## The pairings in the carrier -/

theorem hasSum_dual_one {A : ℕ → ℝ} {K : ℕ} (hA : ∀ k, K < k → A k = 0) :
    HasSum (fun n : ℕ => bdDualWeight A (n + 1) * 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2)))
      (A 1 - A (K + 1)) := by
  have hterm : ∀ n : ℕ, bdDualWeight A (n + 1) * 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) =
      A (n + 1) - A (n + 2) := by
    intro n
    unfold bdDualWeight
    push_cast
    field_simp
    ring
  simp_rw [hterm]
  have hsum : ∑ n ∈ range K, (A (n + 1) - A (n + 2)) = A 1 - A (K + 1) := by
    have := sum_range_sub (fun n => -A (n + 1)) K
    linarith [show ∑ n ∈ range K, (A (n + 1) - A (n + 2)) =
      ∑ n ∈ range K, (-A (n + 1 + 1) - -A (n + 1)) from sum_congr rfl fun n _ => by ring]
  rw [← hsum]
  exact hasSum_sum_of_ne_finset_zero fun n hn => by
    have : K ≤ n := by simpa using hn
    rw [hA (n + 1) (by omega), hA (n + 2) (by omega), sub_zero]

theorem hasSum_dual_modSeq {A : ℕ → ℝ} {K : ℕ} (hA : ∀ k, K < k → A k = 0) {m : ℕ}
    (hm : 1 ≤ m) :
    HasSum (fun n : ℕ => bdDualWeight A (n + 1) * ((((n + 1) % m : ℕ) : ℝ) / (m : ℝ)) /
        (((n : ℝ) + 1) * ((n : ℝ) + 2)))
      ((1 / (m : ℝ)) * ∑ n ∈ range K, A (n + 1) -
        ∑ n ∈ (range K).filter (fun n => m ∣ n + 1), A (n + 1)) := by
  have hterm : ∀ n : ℕ, bdDualWeight A (n + 1) * ((((n + 1) % m : ℕ) : ℝ) / (m : ℝ)) /
      (((n : ℝ) + 1) * ((n : ℝ) + 2)) =
      (A (n + 1) - A (n + 2)) * ((((n + 1) % m : ℕ) : ℝ) / (m : ℝ)) := by
    intro n
    unfold bdDualWeight
    push_cast
    field_simp
    ring
  simp_rw [hterm]
  rw [← sum_dual_mul_modSeq hA hm]
  exact hasSum_sum_of_ne_finset_zero fun n hn => by
    have : K ≤ n := by simpa using hn
    rw [hA (n + 1) (by omega), hA (n + 2) (by omega), sub_zero, zero_mul]

theorem hasSum_dual_self {A : ℕ → ℝ} {K : ℕ} (hA : ∀ k, K < k → A k = 0) :
    HasSum (fun n : ℕ => bdDualWeight A (n + 1) * bdDualWeight A (n + 1) /
        (((n : ℝ) + 1) * ((n : ℝ) + 2)))
      (bdDualEnergy A K) := by
  have hterm : ∀ n : ℕ, bdDualWeight A (n + 1) * bdDualWeight A (n + 1) /
      (((n : ℝ) + 1) * ((n : ℝ) + 2)) =
      ((n : ℝ) + 1) * ((n : ℝ) + 2) * (A (n + 1) - A (n + 2)) ^ 2 := by
    intro n
    unfold bdDualWeight
    push_cast
    field_simp
    ring
  simp_rw [hterm]
  exact hasSum_sum_of_ne_finset_zero fun n hn => by
    have : K ≤ n := by simpa using hn
    rw [hA (n + 1) (by omega), hA (n + 2) (by omega), sub_zero]
    ring

/-! ## The detector bound -/

/-- **The dual-sequence lower bound.**  Let `A` vanish beyond `K`, with `A 1 = 1`, and suppose
`Σ_{m ∣ j} A_j = (1/m) Σ_j A_j` for `2 ≤ m ≤ N`.  Then
`1 ≤ d_N² · Σ_{k ≤ K} k(k+1)(A_k − A_{k+1})²`. -/
theorem one_le_bdDistDiscrete_sq_mul_energy {A : ℕ → ℝ} {K N : ℕ}
    (hA : ∀ k, K < k → A k = 0) (hA1 : A 1 = 1)
    (hC : ∀ m, 2 ≤ m → m ≤ N →
      ∑ n ∈ (range K).filter (fun n => m ∣ n + 1), A (n + 1) =
        (1 / (m : ℝ)) * ∑ n ∈ range K, A (n + 1)) :
    1 ≤ bdDistDiscrete N ^ 2 * bdDualEnergy A K := by
  set B : ℝ := ∑ j ∈ range (K + 1), |bdDualWeight A j| with hB
  have hb : ∀ n, |bdDualWeight A n| ≤ B := abs_bdDualWeight_le hA
  set w : BDCarrier := stepVec (bdDualWeight A) hb with hw
  -- the pairing with the target
  have hpair : inner ℂ w bdTarget = 1 := by
    rw [bdTarget_eq_stepVec, hw, inner_stepVec]
    have h := (hasSum_stepGram hb abs_one_le).unique (hasSum_dual_one hA)
    rw [h, hA (K + 1) (by omega), sub_zero, hA1]
    simp
  -- orthogonality
  have horth : ∀ s ∈ Set.range (fun i : {x // x ∈ range N} => bdGen (bdDiscrete i)),
      inner ℂ w s = 0 := by
    rintro s ⟨⟨i, hi⟩, rfl⟩
    have hiN : i < N := mem_range.mp hi
    simp only
    rw [bdGen_bdDiscrete_eq_stepVec, hw, inner_stepVec]
    have h := (hasSum_stepGram hb (abs_modSeq_le (i + 1))).unique
      (hasSum_dual_modSeq hA (m := i + 1) (by omega))
    rw [h]
    rcases Nat.lt_or_ge i 1 with h0 | h1
    · have : i = 0 := by omega
      subst this
      simp
    · rw [hC (i + 1) (by omega) (by omega)]
      simp
  -- the norm
  have hnorm : ‖w‖ ^ 2 = bdDualEnergy A K := by
    have hin : inner ℂ w w = ((bdDualEnergy A K : ℝ) : ℂ) := by
      rw [hw, inner_stepVec, (hasSum_stepGram hb hb).unique (hasSum_dual_self hA)]
    rw [← @inner_self_eq_norm_sq ℂ, hin]
    simp
  have hmain := norm_inner_le_norm_mul_infDist_span (𝕜 := ℂ) _ bdTarget w horth
  rw [hpair, norm_one] at hmain
  have hd : bdDistDiscrete N = Metric.infDist bdTarget
      (Submodule.span ℂ (Set.range (fun i : {x // x ∈ range N} => bdGen (bdDiscrete i))) :
        Set BDCarrier) := rfl
  rw [← hd] at hmain
  have h0 : 0 ≤ bdDistDiscrete N := (bdDistDiscrete_mem_Icc N).1
  calc (1 : ℝ) = 1 ^ 2 := (one_pow 2).symm
    _ ≤ (‖w‖ * bdDistDiscrete N) ^ 2 := pow_le_pow_left₀ zero_le_one hmain 2
    _ = bdDistDiscrete N ^ 2 * bdDualEnergy A K := by rw [mul_pow, hnorm]; ring

/-! ## Complex dual sequences and their real parts -/

/-- The defect `Σ_{m ∣ k ≤ K} a_k − (1/m) Σ_{k ≤ K} a_k` of a sequence against the modulus `m`. -/
def bdModDefect (a : ℕ → ℂ) (K m : ℕ) : ℂ :=
  ∑ k ∈ (Icc 1 K).filter (fun k => m ∣ k), a k - (1 / (m : ℂ)) * ∑ k ∈ Icc 1 K, a k

theorem sum_range_filter_succ_eq {β : Type*} [AddCommMonoid β] (f : ℕ → β) (p : ℕ → Prop)
    [DecidablePred p] (K : ℕ) :
    ∑ n ∈ (range K).filter (fun n => p (n + 1)), f (n + 1) =
      ∑ k ∈ (Icc 1 K).filter p, f k := by
  rw [sum_filter, sum_filter, range_eq_Ico]
  have := sum_Ico_add' (fun k => if p k then f k else 0) 0 K 1
  simp only [zero_add] at this
  rw [this, Ico_add_one_right_eq_Icc]

/-- If the complex defects vanish, the real part satisfies the dual constraint. -/
theorem dual_constraint_re {a : ℕ → ℂ} {K m : ℕ} (h : bdModDefect a K m = 0) :
    ∑ n ∈ (range K).filter (fun n => m ∣ n + 1), (a (n + 1)).re =
      (1 / (m : ℝ)) * ∑ n ∈ range K, (a (n + 1)).re := by
  have h1 := sum_range_filter_succ_eq (fun k => (a k).re) (fun k => m ∣ k) K
  have h2 := sum_range_filter_succ_eq (fun k => (a k).re) (fun _ => True) K
  rw [filter_true_of_mem (fun _ _ => trivial), filter_true_of_mem (fun _ _ => trivial)] at h2
  rw [h1, h2]
  have hre := congrArg Complex.re h
  unfold bdModDefect at hre
  rw [Complex.sub_re, Complex.re_sum, Complex.zero_re] at hre
  have hmul : (1 / (m : ℂ) * ∑ k ∈ Icc 1 K, a k).re = (1 / (m : ℝ)) * ∑ k ∈ Icc 1 K, (a k).re := by
    rw [show (1 / (m : ℂ)) = ((1 / (m : ℝ) : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul,
      Complex.re_sum]
  rw [hmul] at hre
  linarith

/-! ## The Möbius correction -/

/-- `Σ_{m ∣ k ∣ n₀, 2 ≤ k ≤ N} μ(n₀/k) = [m = n₀]` for `2 ≤ m, n₀ ≤ N`. -/
theorem sum_moebius_dvd_between {N m n₀ : ℕ} (hm : 2 ≤ m) (hn₀ : n₀ ≤ N) (hn₀2 : 2 ≤ n₀) :
    ∑ k ∈ (Icc 2 N).filter (fun k => m ∣ k ∧ k ∣ n₀),
        ((ArithmeticFunction.moebius (n₀ / k) : ℤ) : ℂ) = if m = n₀ then 1 else 0 := by
  by_cases hmn : m ∣ n₀
  · obtain ⟨q, rfl⟩ := hmn
    have hq : 1 ≤ q := by
      rcases Nat.eq_zero_or_pos q with h | h
      · subst h; omega
      · exact h
    have hbij : ∑ k ∈ (Icc 2 N).filter (fun k => m ∣ k ∧ k ∣ m * q),
        ((ArithmeticFunction.moebius (m * q / k) : ℤ) : ℂ) =
        ∑ e ∈ q.divisors, ((ArithmeticFunction.moebius (q / e) : ℤ) : ℂ) := by
      refine sum_nbij' (fun k => k / m) (fun e => m * e) ?_ ?_ ?_ ?_ ?_
      · intro k hk
        simp only [mem_filter, mem_Icc] at hk
        obtain ⟨⟨hk2, _⟩, ⟨e, rfl⟩, hdvd⟩ := hk
        have hm0 : 0 < m := by omega
        simp only [Nat.mem_divisors]
        rw [Nat.mul_div_cancel_left e hm0]
        exact ⟨(Nat.mul_dvd_mul_iff_left hm0).mp hdvd, by omega⟩
      · intro e he
        simp only [Nat.mem_divisors] at he
        obtain ⟨hdvd, hq0⟩ := he
        simp only [mem_filter, mem_Icc]
        have he1 : 1 ≤ e := Nat.pos_of_dvd_of_pos hdvd (by omega)
        refine ⟨⟨by nlinarith, ?_⟩, dvd_mul_right m e, Nat.mul_dvd_mul_left m hdvd⟩
        calc m * e ≤ m * q := Nat.mul_le_mul_left m (Nat.le_of_dvd (by omega) hdvd)
          _ ≤ N := hn₀
      · intro k hk
        simp only [mem_filter] at hk
        obtain ⟨_, ⟨e, rfl⟩, _⟩ := hk
        rw [Nat.mul_div_cancel_left e (by omega)]
      · intro e _
        exact Nat.mul_div_cancel_left e (by omega)
      · intro k hk
        simp only [mem_filter] at hk
        obtain ⟨_, ⟨e, rfl⟩, _⟩ := hk
        rw [Nat.mul_div_cancel_left e (by omega), Nat.mul_div_mul_left q e (by omega)]
    rw [hbij, Nat.sum_div_divisors q (fun e => ((ArithmeticFunction.moebius e : ℤ) : ℂ))]
    have hmz := congrArg (fun f : ArithmeticFunction ℤ => f q)
      ArithmeticFunction.moebius_mul_coe_zeta
    simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at hmz
    have hcast : ∑ e ∈ q.divisors, ((ArithmeticFunction.moebius e : ℤ) : ℂ) =
        (((∑ e ∈ q.divisors, ArithmeticFunction.moebius e : ℤ)) : ℂ) := by push_cast; rfl
    rw [hcast, hmz]
    by_cases hq1 : q = 1
    · subst hq1; simp
    · have : m ≠ m * q := by
        intro h
        have : m * 1 = m * q := by rw [mul_one]; exact h
        exact hq1 (Nat.eq_of_mul_eq_mul_left (by omega) this).symm
      simp [hq1, this]
  · have hempty : (Icc 2 N).filter (fun k => m ∣ k ∧ k ∣ n₀) = ∅ := by
      ext k
      simp only [mem_filter, notMem_empty, iff_false]
      rintro ⟨_, hmk, hkn⟩
      exact hmn (hmk.trans hkn)
    rw [hempty, sum_empty]
    have : m ≠ n₀ := fun h => hmn (h ▸ dvd_rfl)
    simp [this]

/-- The Möbius coefficients of the correction. -/
def bdMoebiusCoeff (N : ℕ) (v : ℕ → ℂ) (d : ℕ) : ℂ :=
  ∑ n₀ ∈ (Icc 2 N).filter (fun n₀ => d ∣ n₀),
    ((ArithmeticFunction.moebius (n₀ / d) : ℤ) : ℂ) * v n₀

/-- The correction `Σ_{2 ≤ d ≤ N} x_d (δ_d − δ_P)`. -/
def bdMoebiusCorrection (N P : ℕ) (v : ℕ → ℂ) (k : ℕ) : ℂ :=
  (if k ∈ Icc 2 N then bdMoebiusCoeff N v k else 0) -
    (if k = P then ∑ d ∈ Icc 2 N, bdMoebiusCoeff N v d else 0)

/-- **The correction has prescribed defects.**  For a prime `P > N` and `K ≥ P`, the defect of the
correction against every modulus `2 ≤ m ≤ N` is `v m`. -/
theorem bdModDefect_bdMoebiusCorrection {N P K : ℕ} (hP : P.Prime) (hNP : N < P) (hPK : P ≤ K)
    (v : ℕ → ℂ) {m : ℕ} (hm2 : 2 ≤ m) (hmN : m ≤ N) :
    bdModDefect (bdMoebiusCorrection N P v) K m = v m := by
  have hsub : Icc 2 N ⊆ Icc 1 K := fun k hk => by
    simp only [mem_Icc] at hk ⊢; omega
  have hPmem : P ∈ Icc 1 K := by simp only [mem_Icc]; exact ⟨hP.one_lt.le, hPK⟩
  have hPnot : P ∉ Icc 2 N := by simp only [mem_Icc]; omega
  have hmP : ¬ m ∣ P := by
    intro h
    rcases (Nat.dvd_prime hP).mp h with h1 | h1 <;> omega
  -- the total sum vanishes
  have htot : ∑ k ∈ Icc 1 K, bdMoebiusCorrection N P v k = 0 := by
    unfold bdMoebiusCorrection
    rw [sum_sub_distrib, ← sum_filter, ← sum_filter]
    rw [filter_mem_eq_inter, inter_eq_right.mpr hsub]
    rw [filter_eq' (Icc 1 K) P, if_pos hPmem, sum_singleton]
    ring
  -- the divisible part
  have hdiv : ∑ k ∈ (Icc 1 K).filter (fun k => m ∣ k), bdMoebiusCorrection N P v k =
      ∑ d ∈ (Icc 2 N).filter (fun d => m ∣ d), bdMoebiusCoeff N v d := by
    unfold bdMoebiusCorrection
    rw [sum_sub_distrib, ← sum_filter, ← sum_filter, filter_filter, filter_filter]
    have h1 : (Icc 1 K).filter (fun k => m ∣ k ∧ k ∈ Icc 2 N) =
        (Icc 2 N).filter (fun d => m ∣ d) := by
      ext k; simp only [mem_filter]; constructor
      · rintro ⟨_, h1, h2⟩; exact ⟨h2, h1⟩
      · rintro ⟨h2, h1⟩; exact ⟨hsub h2, h1, h2⟩
    have h2 : (Icc 1 K).filter (fun k => m ∣ k ∧ k = P) = ∅ := by
      ext k; simp only [mem_filter, notMem_empty, iff_false]
      rintro ⟨_, hk, rfl⟩; exact hmP hk
    rw [h1, h2, sum_empty, sub_zero]
  unfold bdModDefect
  rw [htot, mul_zero, sub_zero, hdiv]
  unfold bdMoebiusCoeff
  rw [sum_comm' (t' := Icc 2 N) (s' := fun n₀ => (Icc 2 N).filter (fun d => m ∣ d ∧ d ∣ n₀))]
  · have : ∀ n₀ ∈ Icc 2 N, ∑ d ∈ (Icc 2 N).filter (fun d => m ∣ d ∧ d ∣ n₀),
        ((ArithmeticFunction.moebius (n₀ / d) : ℤ) : ℂ) * v n₀ =
        (if m = n₀ then 1 else 0) * v n₀ := by
      intro n₀ hn₀
      simp only [mem_Icc] at hn₀
      rw [← sum_mul, sum_moebius_dvd_between hm2 hn₀.2 hn₀.1]
    rw [sum_congr rfl this]
    simp only [ite_mul, one_mul, zero_mul]
    rw [sum_ite_eq]
    simp only [mem_Icc]
    rw [if_pos ⟨hm2, hmN⟩]
  · intro d n₀
    simp only [mem_filter, mem_Icc]
    tauto

theorem norm_bdMoebiusCoeff_le (N : ℕ) (v : ℕ → ℂ) (d : ℕ) :
    ‖bdMoebiusCoeff N v d‖ ≤ ∑ n₀ ∈ Icc 2 N, ‖v n₀‖ := by
  unfold bdMoebiusCoeff
  refine (norm_sum_le _ _).trans ?_
  refine (sum_le_sum fun n₀ _ => ?_).trans (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
    fun _ _ _ => norm_nonneg _)
  rw [norm_mul]
  have : ‖((ArithmeticFunction.moebius (n₀ / d) : ℤ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  nlinarith [norm_nonneg (v n₀)]

theorem norm_bdMoebiusCorrection_le (N P : ℕ) (v : ℕ → ℂ) (k : ℕ) :
    ‖bdMoebiusCorrection N P v k‖ ≤ ((N : ℝ) + 1) * ∑ n₀ ∈ Icc 2 N, ‖v n₀‖ := by
  set V := ∑ n₀ ∈ Icc 2 N, ‖v n₀‖ with hV
  have hV0 : 0 ≤ V := sum_nonneg fun _ _ => norm_nonneg _
  have h1 : ‖(if k ∈ Icc 2 N then bdMoebiusCoeff N v k else 0)‖ ≤ V := by
    split_ifs
    · exact norm_bdMoebiusCoeff_le N v k
    · simpa using hV0
  have h2 : ‖(if k = P then ∑ d ∈ Icc 2 N, bdMoebiusCoeff N v d else 0)‖ ≤ (N : ℝ) * V := by
    split_ifs
    · refine (norm_sum_le _ _).trans ?_
      refine (sum_le_sum fun d _ => norm_bdMoebiusCoeff_le N v d).trans ?_
      rw [sum_const, nsmul_eq_mul, Nat.card_Icc]
      refine mul_le_mul_of_nonneg_right ?_ hV0
      exact_mod_cast (by omega : N + 1 - 2 ≤ N)
    · simp; positivity
  unfold bdMoebiusCorrection
  refine (norm_sub_le _ _).trans ?_
  linarith

theorem bdMoebiusCorrection_eq_zero {N P : ℕ} (hNP : N < P) (v : ℕ → ℂ) {k : ℕ} (hk : P < k) :
    bdMoebiusCorrection N P v k = 0 := by
  unfold bdMoebiusCorrection
  have h1 : k ∉ Icc 2 N := by simp only [mem_Icc]; omega
  rw [if_neg h1, if_neg (by omega)]
  simp

theorem bdMoebiusCorrection_one {N P : ℕ} (hP : 2 ≤ P) (v : ℕ → ℂ) :
    bdMoebiusCorrection N P v 1 = 0 := by
  unfold bdMoebiusCorrection
  have h1 : (1 : ℕ) ∉ Icc 2 N := by simp
  rw [if_neg h1, if_neg (by omega)]
  simp

/-! ## Complex energies -/

/-- The weighted energy `Σ_{k ≤ K} k(k+1)|a_k − a_{k+1}|²` of a complex sequence. -/
def bdDualEnergyC (a : ℕ → ℂ) (K : ℕ) : ℝ :=
  ∑ n ∈ range K, ((n : ℝ) + 1) * ((n : ℝ) + 2) * ‖a (n + 1) - a (n + 2)‖ ^ 2

theorem bdDualEnergy_re_le (a : ℕ → ℂ) (K : ℕ) :
    bdDualEnergy (fun k => (a k).re) K ≤ bdDualEnergyC a K := by
  unfold bdDualEnergy bdDualEnergyC
  refine sum_le_sum fun n _ => mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [← Complex.sub_re]
  have h := Complex.abs_re_le_norm (a (n + 1) - a (n + 2))
  calc (a (n + 1) - a (n + 2)).re ^ 2 = |(a (n + 1) - a (n + 2)).re| ^ 2 := (sq_abs _).symm
    _ ≤ ‖a (n + 1) - a (n + 2)‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2

theorem bdDualEnergyC_add_le (a b : ℕ → ℂ) (K : ℕ) :
    bdDualEnergyC (a + b) K ≤ 2 * bdDualEnergyC a K + 2 * bdDualEnergyC b K := by
  unfold bdDualEnergyC
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun n _ => ?_
  have hw : 0 ≤ ((n : ℝ) + 1) * ((n : ℝ) + 2) := by positivity
  have h : ‖(a + b) (n + 1) - (a + b) (n + 2)‖ ^ 2 ≤
      2 * ‖a (n + 1) - a (n + 2)‖ ^ 2 + 2 * ‖b (n + 1) - b (n + 2)‖ ^ 2 := by
    have e : (a + b) (n + 1) - (a + b) (n + 2) =
        (a (n + 1) - a (n + 2)) + (b (n + 1) - b (n + 2)) := by
      simp only [Pi.add_apply]; ring
    rw [e]
    have := norm_add_le (a (n + 1) - a (n + 2)) (b (n + 1) - b (n + 2))
    nlinarith [norm_nonneg (a (n + 1) - a (n + 2)), norm_nonneg (b (n + 1) - b (n + 2)),
      sq_nonneg (‖a (n + 1) - a (n + 2)‖ - ‖b (n + 1) - b (n + 2)‖),
      norm_nonneg ((a (n + 1) - a (n + 2)) + (b (n + 1) - b (n + 2)))]
  nlinarith [mul_le_mul_of_nonneg_left h hw]

/-- The energy of a bounded sequence supported in `[1, P]`. -/
theorem bdDualEnergyC_le_of_bounded {b : ℕ → ℂ} {P K : ℕ} {B : ℝ} (hb : ∀ k, P < k → b k = 0)
    (hB : ∀ k, ‖b k‖ ≤ B) :
    bdDualEnergyC b K ≤ (P : ℝ) * ((P : ℝ) + 1) ^ 2 * (2 * B) ^ 2 := by
  unfold bdDualEnergyC
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hterm : ∀ n ∈ range K, ((n : ℝ) + 1) * ((n : ℝ) + 2) * ‖b (n + 1) - b (n + 2)‖ ^ 2 ≤
      if n < P then ((P : ℝ) + 1) ^ 2 * (2 * B) ^ 2 else 0 := by
    intro n _
    split_ifs with hn
    · have h1 : ((n : ℝ) + 1) * ((n : ℝ) + 2) ≤ ((P : ℝ) + 1) ^ 2 := by
        have : (n : ℝ) + 1 ≤ P := by exact_mod_cast hn
        nlinarith
      have h2 : ‖b (n + 1) - b (n + 2)‖ ≤ 2 * B := by
        have := norm_sub_le (b (n + 1)) (b (n + 2))
        linarith [hB (n + 1), hB (n + 2)]
      exact mul_le_mul h1 (pow_le_pow_left₀ (norm_nonneg _) h2 2) (by positivity) (by positivity)
    · rw [hb (n + 1) (by omega), hb (n + 2) (by omega), sub_zero, norm_zero]
      simp
  refine (sum_le_sum hterm).trans ?_
  rw [← sum_filter]
  have hsub : (range K).filter (fun n => n < P) ⊆ range P := fun n hn => by
    simp only [mem_filter, mem_range] at hn ⊢; exact hn.2
  refine (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity).trans ?_
  rw [sum_const, card_range, nsmul_eq_mul]
  ring_nf
  rfl

theorem bdModDefect_add (a b : ℕ → ℂ) (K m : ℕ) :
    bdModDefect (a + b) K m = bdModDefect a K m + bdModDefect b K m := by
  unfold bdModDefect
  simp only [Pi.add_apply, sum_add_distrib]
  ring

end

end RHTower
