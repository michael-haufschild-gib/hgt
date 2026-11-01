import GaloisForLFunctions.RenormalizedIntersectionTheory.TheZeroDensityTwinCarriesTheConductorSeries

/-!
# The conductor series converges below a quarter

Let `P` have upper relative logarithmic density `κ < 1/4`:
`Σ_{p ∈ P, p ≤ n} log p/p ≤ κ log n + C`. Then for `0 ≤ s < 2 log 2` the conductor series
`W_P(s) = Σ_{m ≥ 2} w_P(m)/(E_m − γ − s)` converges (`summable_conductorSeries`).

* **Prime sums** (`exists_sum_primeSetCutoff_rpow_le`): `Σ_{p ∈ P} p^{−1−σ} ≤ κ log(1/σ) + K` for
  `σ ∈ (0, 1]`, by Abel summation against the decreasing weight `n^{−σ}/log n`;
  `Δlog n/log n ≤ Δ log log n` below `e^{1/σ}` and `σ Δlog n · n^{−σ} ≤ Δ(−n^{−σ})` above.
* **Euler product** (`sum_conductorLaplace_le`): `w_P(m) e^{−σ(E_m − γ)}` is multiplicative, the
  prime-power factors are at most `1 + 4p^{1−σ}/(p − 1)²`, so every packet has
  `Σ_{m ∈ S} w_P(m) e^{−σ(E_m − γ)} ≤ exp(4 Σ_{p ∈ P} p^{−1−σ} + 32) ≤ M σ^{−4κ}`.
* **Laplace** (`inv_le_dyadic`): `1/x ≤ e^{−x}/x₀ + Σ_{j < J} 2^{−j−1} e^{−2^{−j−1} x} + 2^{−J}` for
  `x ≥ x₀ > 0`; at `σ = 2^{−j−1}` the dyadic terms are `(2^{4κ}/2)^{j+1}`, summable as `4κ < 1`.

With the spectral-weight theorems this makes the asymptotic unconditional: for relative log density
`κ ∈ (0, 1/4)`, `ρ_{i₀}(v_P)/c_N² → W_P(s)` (`eventually_abs_excitedResolvent_div_sub_conductorSeries_le`),
`⟨w, v_P⟩² ≤ c_N² (W_P(s) + ε)(Q_N(w) − s|w|²)` off the ground (`eventually_inner_sq_le_tsum_conductorSeries`),
and the twin is separated iff `W_P(s) > 1/s` for some `s ∈ (0, 2 log 2)`
(`hodgeSeparates_primeSetFlip_iff_conductorSeries`).
-/

noncomputable section

open Finset Filter Topology
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.RenormalizedIntersectionTheory

open GaloisForLFunctions.ArithmeticCountingPositivity
open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory (PrimeHorizonIndex
  ramanujanAdjunctionEnergy)
open GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity (tameDifferent_one
  tameDifferent_nonneg)
open GaloisForLFunctions.ArithmeticIntersectionTheory (tameDifferent tameDifferent_mul)

local notation "γ" => Real.eulerMascheroniConstant

section Telescoping

/-- `Σ_{a ≤ k ≤ M} (F k − F (k − 1)) = F M − F (a − 1)`. -/
theorem sum_Icc_sub_pred (F : ℕ → ℝ) {a M : ℕ} (ha : 1 ≤ a) (haM : a - 1 ≤ M) :
    ∑ k ∈ Icc a M, (F k - F (k - 1)) = F M - F (a - 1) := by
  induction M, haM using Nat.le_induction with
  | base => rw [Icc_eq_empty (by omega), sum_empty, sub_self]
  | succ M hM ih =>
    rw [sum_Icc_succ_top (by omega), ih, Nat.add_sub_cancel]
    ring

theorem natCast_pred {k : ℕ} (hk : 1 ≤ k) : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
  rw [Nat.cast_sub hk, Nat.cast_one]

/-- `Σ_{p ∈ F} 1/(p(p − 1)) ≤ 1` for a finite set of integers `≥ 2`. -/
theorem sum_inv_mul_pred_le (F : Finset ℕ) (hF : ∀ p ∈ F, 2 ≤ p) :
    ∑ p ∈ F, 1 / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 1 := by
  set M := F.sup id + 2
  have hsub : F ⊆ Icc 2 M := fun p hp => mem_Icc.mpr ⟨hF p hp, by
    have := Finset.le_sup (f := id) hp; simp only [id] at this; omega⟩
  have hnn : ∀ k ∈ Icc 2 M, k ∉ F → 0 ≤ 1 / ((k : ℝ) * ((k : ℝ) - 1)) := fun k hk _ => by
    have : (2 : ℝ) ≤ k := by exact_mod_cast (mem_Icc.mp hk).1
    exact div_nonneg zero_le_one (mul_nonneg (by linarith) (by linarith))
  refine (sum_le_sum_of_subset_of_nonneg hsub hnn).trans ?_
  have htel := sum_Icc_sub_pred (fun k => -(1 / (k : ℝ))) (a := 2) (M := M) (by norm_num) (by omega)
  have e : ∀ k ∈ Icc 2 M, 1 / ((k : ℝ) * ((k : ℝ) - 1)) =
      -(1 / (k : ℝ)) - -(1 / ((k - 1 : ℕ) : ℝ)) := fun k hk => by
    have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (mem_Icc.mp hk).1
    rw [natCast_pred (by have := (mem_Icc.mp hk).1; omega)]
    have h1 : (k : ℝ) - 1 ≠ 0 := by linarith
    have h0 : (k : ℝ) ≠ 0 := by linarith
    rw [neg_sub_neg, div_sub_div _ _ h1 h0]
    congr 1 <;> ring
  rw [sum_congr rfl e, htel]
  have hM : (0 : ℝ) < M := by positivity
  simp only [show (2 - 1 : ℕ) = 1 by rfl, Nat.cast_one]
  have : 0 < 1 / (M : ℝ) := by positivity
  linarith

end Telescoping

section PrimeSums

/-- `Δlog k/log k ≤ Δ log log k` for `k ≥ 3`. -/
theorem logIncrement_div_log_le {k : ℕ} (hk : 3 ≤ k) :
    (Real.log k - Real.log ((k : ℝ) - 1)) / Real.log k ≤
      Real.log (Real.log k) - Real.log (Real.log ((k : ℝ) - 1)) := by
  have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hu : 0 < Real.log ((k : ℝ) - 1) := Real.log_pos (by linarith)
  have hv : 0 < Real.log k := Real.log_pos (by linarith)
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hv hu)
  rw [Real.log_div hv.ne' hu.ne', inv_div] at h
  rw [sub_div, div_self hv.ne']
  linarith

/-- `σ Δlog k · k^{−σ} ≤ (k − 1)^{−σ} − k^{−σ}`. -/
theorem logIncrement_mul_rpow_le {k : ℕ} (hk : 2 ≤ k) {σ : ℝ} :
    σ * ((Real.log k - Real.log ((k : ℝ) - 1)) * (k : ℝ) ^ (-σ)) ≤
      ((k : ℝ) - 1) ^ (-σ) - (k : ℝ) ^ (-σ) := by
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  rw [Real.rpow_def_of_pos (by linarith : (0 : ℝ) < (k : ℝ) - 1),
    Real.rpow_def_of_pos (by linarith : (0 : ℝ) < k)]
  set y := σ * (Real.log k - Real.log ((k : ℝ) - 1))
  have hy : Real.exp (Real.log ((k : ℝ) - 1) * -σ) = Real.exp (Real.log k * -σ) * Real.exp y := by
    rw [← Real.exp_add]; congr 1; simp only [y]; ring
  rw [hy]
  have h1 := Real.add_one_le_exp y
  have he := Real.exp_pos (Real.log k * -σ)
  calc σ * ((Real.log k - Real.log ((k : ℝ) - 1)) * Real.exp (Real.log k * -σ)) =
        Real.exp (Real.log k * -σ) * y := by simp only [y]; ring
    _ ≤ Real.exp (Real.log k * -σ) * (Real.exp y - 1) :=
        mul_le_mul_of_nonneg_left (by linarith) he.le
    _ = _ := by ring

/-- **The logarithmic integral at scale `σ`**:
`Σ_{2 ≤ k ≤ X} Δlog k · k^{−σ}/log k ≤ log(1/σ) + K₀` for `σ ∈ (0, 1]`. -/
theorem exists_sum_logIncrement_rpow_div_log_le :
    ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ σ : ℝ, 0 < σ → σ ≤ 1 → ∀ X : ℕ,
      ∑ k ∈ Icc 2 X, (Real.log k - Real.log ((k : ℝ) - 1)) * ((k : ℝ) ^ (-σ) / Real.log k) ≤
        Real.log (1 / σ) + K₀ := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hl21 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  refine ⟨2 + Real.log (Real.log 2 + 1) - Real.log (Real.log 2), ?_, fun σ hσ hσ1 X => ?_⟩
  · have h1 : 0 ≤ Real.log (Real.log 2 + 1) := Real.log_nonneg (by linarith)
    have h2 : Real.log (Real.log 2) ≤ 0 := Real.log_nonpos hl2.le hl21.le
    linarith
  have hσ' : 1 ≤ 1 / σ := by rw [le_div_iff₀ hσ]; linarith
  have hlogσ : 0 ≤ Real.log (1 / σ) := Real.log_nonneg hσ'
  set g : ℕ → ℝ := fun k => (Real.log k - Real.log ((k : ℝ) - 1)) * ((k : ℝ) ^ (-σ) / Real.log k)
  rcases lt_or_ge X 2 with hX | hX
  · rw [Icc_eq_empty (by omega), sum_empty]
    have h1 : 0 ≤ Real.log (Real.log 2 + 1) := Real.log_nonneg (by linarith)
    have h2 : Real.log (Real.log 2) ≤ 0 := Real.log_nonpos hl2.le hl21.le
    linarith
  -- the crossover `K = ⌈e^{1/σ}⌉`
  set K : ℕ := ⌈Real.exp (1 / σ)⌉₊
  have hK1 : Real.exp (1 / σ) ≤ K := Nat.le_ceil _
  have hK2 : (K : ℝ) < Real.exp (1 / σ) + 1 := Nat.ceil_lt_add_one (Real.exp_pos _).le
  have he1 : Real.exp 1 ≤ Real.exp (1 / σ) := Real.exp_le_exp.mpr hσ'
  have hK3 : 3 ≤ K := by
    have : (2 : ℝ) < K := by have := Real.exp_one_gt_d9; linarith
    have : 2 < K := by exact_mod_cast this
    omega
  have hK0 : (0 : ℝ) < K := by positivity
  have hlogK : Real.log (Real.log K) ≤ Real.log (Real.log 2 + 1) + Real.log (1 / σ) := by
    have h1e : 1 ≤ Real.exp (1 / σ) := Real.one_le_exp (by positivity)
    have hlK : Real.log K ≤ Real.log 2 + 1 / σ := by
      calc Real.log K ≤ Real.log (2 * Real.exp (1 / σ)) := Real.log_le_log hK0 (by linarith)
        _ = Real.log 2 + 1 / σ := by
          rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp]
    have hlK' : Real.log K ≤ (Real.log 2 + 1) * (1 / σ) := by nlinarith
    have hlK0 : 0 < Real.log K := Real.log_pos (by exact_mod_cast (show 1 < K by omega))
    calc Real.log (Real.log K) ≤ Real.log ((Real.log 2 + 1) * (1 / σ)) := Real.log_le_log hlK0 hlK'
      _ = Real.log (Real.log 2 + 1) + Real.log (1 / σ) :=
        Real.log_mul (by positivity) (by positivity)
  -- the term `k = 2`
  have hg2 : g 2 ≤ 1 := by
    simp only [g]
    rw [show ((2 : ℕ) : ℝ) - 1 = 1 by norm_num, Real.log_one, sub_zero]
    push_cast
    rw [mul_div_cancel₀ _ hl2.ne']
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have hsplit : ∑ k ∈ Icc 2 X, g k = g 2 + ∑ k ∈ Icc 3 X, g k := by
    rw [← add_sum_Ioc_eq_sum_Icc hX]
    rfl
  -- below the crossover: `g k ≤ Δ log log k`
  have hlow : ∑ k ∈ (Icc 3 X).filter (· ≤ K), g k ≤
      Real.log (Real.log K) - Real.log (Real.log 2) := by
    set F : ℕ → ℝ := fun k => Real.log (Real.log k)
    have hterm : ∀ k ∈ Icc 3 K, g k ≤ F k - F (k - 1) := by
      intro k hk
      have hk3 := (mem_Icc.mp hk).1
      have hk3' : (3 : ℝ) ≤ k := by exact_mod_cast hk3
      have hd : 0 ≤ Real.log k - Real.log ((k : ℝ) - 1) :=
        sub_nonneg.mpr (Real.log_le_log (by linarith) (by linarith))
      have hl : 0 < Real.log k := Real.log_pos (by linarith)
      have hpow : (k : ℝ) ^ (-σ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
      simp only [g, F]
      rw [natCast_pred (by omega)]
      calc (Real.log k - Real.log ((k : ℝ) - 1)) * ((k : ℝ) ^ (-σ) / Real.log k) ≤
            (Real.log k - Real.log ((k : ℝ) - 1)) * (1 / Real.log k) :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hpow hl.le) hd
        _ = (Real.log k - Real.log ((k : ℝ) - 1)) / Real.log k := by ring
        _ ≤ _ := logIncrement_div_log_le hk3
    have hsub : (Icc 3 X).filter (· ≤ K) ⊆ Icc 3 K := fun k hk => by
      obtain ⟨hk1, hk2⟩ := mem_filter.mp hk
      exact mem_Icc.mpr ⟨(mem_Icc.mp hk1).1, hk2⟩
    have hnn : ∀ k ∈ Icc 3 K, k ∉ (Icc 3 X).filter (· ≤ K) → 0 ≤ F k - F (k - 1) := by
      intro k hk _
      have hk3 := (mem_Icc.mp hk).1
      have hk3' : (3 : ℝ) ≤ k := by exact_mod_cast hk3
      simp only [F]
      rw [natCast_pred (by omega)]
      exact sub_nonneg.mpr (Real.log_le_log (Real.log_pos (by linarith))
        (Real.log_le_log (by linarith) (by linarith)))
    calc ∑ k ∈ (Icc 3 X).filter (· ≤ K), g k ≤ ∑ k ∈ (Icc 3 X).filter (· ≤ K), (F k - F (k - 1)) :=
          sum_le_sum fun k hk => hterm k (hsub hk)
      _ ≤ ∑ k ∈ Icc 3 K, (F k - F (k - 1)) := sum_le_sum_of_subset_of_nonneg hsub hnn
      _ = F K - F 2 := sum_Icc_sub_pred F (by norm_num) (by omega)
      _ = _ := by simp only [F]; norm_num
  -- above the crossover: `g k ≤ (k − 1)^{−σ} − k^{−σ}`
  have hhigh : ∑ k ∈ (Icc 3 X).filter (fun k => ¬ k ≤ K), g k ≤ 1 := by
    set F : ℕ → ℝ := fun k => -(k : ℝ) ^ (-σ)
    have hterm : ∀ k, K < k → g k ≤ F k - F (k - 1) := by
      intro k hk
      have hkK : (K : ℝ) < k := by exact_mod_cast hk
      have hk2 : 2 ≤ k := by omega
      have hk2' : (2 : ℝ) ≤ k := by exact_mod_cast hk2
      have hl : 0 < Real.log k := Real.log_pos (by linarith)
      have hlk : 1 / σ ≤ Real.log k := by
        rw [← Real.log_exp (1 / σ)]
        exact Real.log_le_log (Real.exp_pos _) (by linarith)
      have hinv : 1 / Real.log k ≤ σ := by
        rw [div_le_iff₀ hl]; rw [div_le_iff₀ hσ] at hlk; linarith
      have hd : 0 ≤ (Real.log k - Real.log ((k : ℝ) - 1)) * (k : ℝ) ^ (-σ) :=
        mul_nonneg (sub_nonneg.mpr (Real.log_le_log (by linarith) (by linarith)))
          (Real.rpow_nonneg (by linarith) _)
      simp only [g, F]
      rw [natCast_pred (by omega)]
      calc (Real.log k - Real.log ((k : ℝ) - 1)) * ((k : ℝ) ^ (-σ) / Real.log k) =
            ((Real.log k - Real.log ((k : ℝ) - 1)) * (k : ℝ) ^ (-σ)) * (1 / Real.log k) := by ring
        _ ≤ ((Real.log k - Real.log ((k : ℝ) - 1)) * (k : ℝ) ^ (-σ)) * σ :=
            mul_le_mul_of_nonneg_left hinv hd
        _ = σ * ((Real.log k - Real.log ((k : ℝ) - 1)) * (k : ℝ) ^ (-σ)) := by ring
        _ ≤ _ := by have := logIncrement_mul_rpow_le hk2 (σ := σ); linarith
    rcases lt_or_ge X (K + 1) with hXK | hXK
    · have : (Icc 3 X).filter (fun k => ¬ k ≤ K) = ∅ := by
        ext k; simp only [mem_filter, mem_Icc, notMem_empty, iff_false]; omega
      rw [this, sum_empty]; norm_num
    have hsub : (Icc 3 X).filter (fun k => ¬ k ≤ K) ⊆ Icc (K + 1) X := fun k hk => by
      obtain ⟨hk1, hk2⟩ := mem_filter.mp hk
      exact mem_Icc.mpr ⟨by omega, (mem_Icc.mp hk1).2⟩
    have hnn : ∀ k ∈ Icc (K + 1) X, k ∉ (Icc 3 X).filter (fun k => ¬ k ≤ K) →
        0 ≤ F k - F (k - 1) := by
      intro k hk _
      have hk1 := (mem_Icc.mp hk).1
      have hk2' : (2 : ℝ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
      simp only [F]
      rw [natCast_pred (by omega)]
      have := Real.rpow_le_rpow_of_nonpos (by linarith : (0 : ℝ) < (k : ℝ) - 1)
        (show (k : ℝ) - 1 ≤ k by linarith) (by linarith : -σ ≤ 0)
      linarith
    calc _ ≤ ∑ k ∈ (Icc 3 X).filter (fun k => ¬ k ≤ K), (F k - F (k - 1)) :=
          sum_le_sum fun k hk => hterm k (by have := (mem_filter.mp hk).2; omega)
      _ ≤ ∑ k ∈ Icc (K + 1) X, (F k - F (k - 1)) := sum_le_sum_of_subset_of_nonneg hsub hnn
      _ = F X - F K := by rw [sum_Icc_sub_pred F (by omega) (by omega), Nat.add_sub_cancel]
      _ ≤ 1 := by
          simp only [F]
          have h1 : (K : ℝ) ^ (-σ) ≤ 1 :=
            Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (show 1 ≤ K by omega)) (by linarith)
          have h2 : 0 ≤ (X : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
          linarith
  rw [hsplit, ← sum_filter_add_sum_filter_not (Icc 3 X) (· ≤ K)]
  linarith

/-- **Prime sums from an upper logarithmic density.** If `Σ_{p ∈ P, p ≤ n} log p/p ≤ κ log n + C`
with `κ ≥ 0`, then `Σ_{p ∈ P, p ≤ X} p^{−1−σ} ≤ κ log(1/σ) + K` for all `σ ∈ (0, 1]` and `X`. -/
theorem exists_sum_primeSetCutoff_rpow_le (P : Set ℕ) {κ C : ℝ} (hκ : 0 ≤ κ)
    (hP : ∀ n : ℕ, 1 ≤ n → primeSetLogMass P n ≤ κ * Real.log n + C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ σ : ℝ, 0 < σ → σ ≤ 1 → ∀ X : ℕ,
      ∑ p ∈ primeSetCutoff P X, (p : ℝ) ^ (-(1 + σ)) ≤ κ * Real.log (1 / σ) + K := by
  classical
  obtain ⟨K₀, hK₀, hJ⟩ := exists_sum_logIncrement_rpow_div_log_le
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hmass1 : primeSetLogMass P 1 = 0 := by
    unfold primeSetLogMass
    rw [primeSetCutoff_eq_filter]
    simp [Nat.not_prime_one, Finset.filter_singleton]
  have hC0 : 0 ≤ C := by have := hP 1 le_rfl; rw [hmass1] at this; simpa using this
  refine ⟨κ * K₀ + C / Real.log 2, by positivity, fun σ hσ hσ1 X => ?_⟩
  have hlogσ : 0 ≤ Real.log (1 / σ) := Real.log_nonneg (by rw [le_div_iff₀ hσ]; linarith)
  rcases lt_or_ge X 2 with hX | hX
  · have hemp : primeSetCutoff P X = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro k hk
      have h1 := (mem_primeSetCutoff.mp hk).1.1
      have h2 := (mem_primeSetCutoff.mp hk).1.2.two_le
      omega
    rw [hemp, sum_empty]
    positivity
  set a : ℕ → ℝ := fun k => if k.Prime ∧ k ∈ P then Real.log k / k else 0
  set g : ℕ → ℝ := fun k => (k : ℝ) ^ (-σ) / Real.log k
  set b : ℕ → ℝ := fun k => Real.log k - Real.log ((k : ℝ) - 1)
  have ha1 : a 1 = 0 := by simp [a, Nat.not_prime_one]
  have hb1 : b 1 = 0 := by simp [b]
  have hA : ∀ n, ∑ i ∈ Icc 1 n, a i = primeSetLogMass P n := fun n => by
    rw [primeSetLogMass, primeSetCutoff_eq_filter, filter_filter, sum_filter]
  have hB : ∀ n, 1 ≤ n → ∑ i ∈ Icc 1 n, b i = Real.log n := fun n hn => by
    have h := sum_Icc_sub_pred (fun k => Real.log k) (a := 1) (M := n) le_rfl (by omega)
    have e : ∀ i ∈ Icc 1 n, b i = Real.log i - Real.log ((i - 1 : ℕ) : ℝ) := fun i hi => by
      simp only [b]; rw [natCast_pred (mem_Icc.mp hi).1]
    rw [sum_congr rfl e, h]
    simp
  have hanti : ∀ k, 2 ≤ k → g (k + 1) ≤ g k := by
    intro k hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hl : 0 < Real.log k := Real.log_pos (by exact_mod_cast (show 1 < k by omega))
    have hl' : Real.log k ≤ Real.log ((k + 1 : ℕ) : ℝ) :=
      Real.log_le_log hk0 (by push_cast; linarith)
    have hnum : ((k + 1 : ℕ) : ℝ) ^ (-σ) ≤ (k : ℝ) ^ (-σ) :=
      Real.rpow_le_rpow_of_nonpos hk0 (by push_cast; linarith) (by linarith)
    exact div_le_div₀ (Real.rpow_nonneg hk0.le _) hnum hl hl'
  have hg0 : ∀ k, 2 ≤ k → 0 ≤ g k := fun k _ =>
    div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg k) _) (Real.log_natCast_nonneg k)
  -- the prime sum is the Abel sum `Σ a g`
  have hsum : ∑ p ∈ primeSetCutoff P X, (p : ℝ) ^ (-(1 + σ)) = ∑ k ∈ Icc 2 X, a k * g k := by
    have h1 : ∑ p ∈ primeSetCutoff P X, (p : ℝ) ^ (-(1 + σ)) = ∑ k ∈ Icc 1 X, a k * g k := by
      rw [primeSetCutoff_eq_filter, filter_filter, sum_filter]
      refine sum_congr rfl fun k _ => ?_
      simp only [a, g]
      split_ifs with hp
      · have hk0 : (0 : ℝ) < k := by exact_mod_cast hp.1.pos
        have hl : 0 < Real.log k := Real.log_pos (by exact_mod_cast hp.1.one_lt)
        rw [show -(1 + σ) = -1 + -σ by ring, Real.rpow_add hk0, Real.rpow_neg_one]
        field_simp
      · simp
    rw [h1, ← add_sum_Ioc_eq_sum_Icc (show 1 ≤ X by omega), ha1, zero_mul, zero_add]
    rfl
  -- Abel summation against `A(k) ≤ κ log k + C`
  have habel := sum_Icc_two_mul_eq_abel a g ha1 hX
  have habel' := sum_Icc_two_mul_eq_abel b g hb1 hX
  rw [hA] at habel
  rw [hB X (by omega)] at habel'
  have hB' : ∑ k ∈ Ico 2 X, (∑ i ∈ Icc 1 k, b i) * (g k - g (k + 1)) =
      ∑ k ∈ Ico 2 X, Real.log k * (g k - g (k + 1)) :=
    sum_congr rfl fun k hk => by rw [hB k (by have := (mem_Ico.mp hk).1; omega)]
  rw [hB'] at habel'
  have htel : ∑ k ∈ Ico 2 X, (g k - g (k + 1)) = g 2 - g X := by
    have h := sum_Ico_sub_eq (f := g) hX
    rw [← neg_sub, ← h, ← sum_neg_distrib]
    exact sum_congr rfl fun k _ => by ring
  have h1 : ∑ k ∈ Ico 2 X, (∑ i ∈ Icc 1 k, a i) * (g k - g (k + 1)) ≤
      κ * ∑ k ∈ Ico 2 X, Real.log k * (g k - g (k + 1)) + (C * g 2 - C * g X) := by
    calc _ ≤ ∑ k ∈ Ico 2 X, (κ * Real.log k + C) * (g k - g (k + 1)) := by
          refine sum_le_sum fun k hk => ?_
          have hk2 := (mem_Ico.mp hk).1
          rw [hA k]
          exact mul_le_mul_of_nonneg_right (hP k (by omega)) (sub_nonneg.mpr (hanti k hk2))
      _ = κ * ∑ k ∈ Ico 2 X, Real.log k * (g k - g (k + 1)) +
          C * ∑ k ∈ Ico 2 X, (g k - g (k + 1)) := by
          rw [mul_sum, mul_sum, ← sum_add_distrib]
          exact sum_congr rfl fun k _ => by ring
      _ = _ := by rw [htel]; ring
  have h2 : primeSetLogMass P X * g X ≤ κ * (Real.log X * g X) + C * g X := by
    calc primeSetLogMass P X * g X ≤ (κ * Real.log X + C) * g X :=
          mul_le_mul_of_nonneg_right (hP X (by omega)) (hg0 X hX)
      _ = _ := by ring
  have hJX := hJ σ hσ hσ1 X
  have hbg : ∑ k ∈ Icc 2 X, b k * g k ≤ Real.log (1 / σ) + K₀ := hJX
  have hgg2 : g 2 ≤ 1 / Real.log 2 := by
    simp only [g]
    push_cast
    exact div_le_div_of_nonneg_right
      (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)) hl2.le
  have hκb := mul_le_mul_of_nonneg_left hbg hκ
  have hCg := mul_le_mul_of_nonneg_left hgg2 hC0
  rw [hsum, habel]
  have e2 : κ * ∑ k ∈ Icc 2 X, b k * g k =
      κ * (Real.log X * g X) + κ * ∑ k ∈ Ico 2 X, Real.log k * (g k - g (k + 1)) := by
    rw [habel', mul_add]
  rw [mul_one_div] at hCg
  nlinarith

end PrimeSums

section Euler

/-- The Laplace-weighted conductor term `w_F(m) e^{−σ(log m + Σ_{p ∣ m} log p/(p − 1))}`. -/
def conductorLaplaceTerm (F : Finset ℕ) (σ : ℝ) (m : ℕ) : ℝ :=
  finiteFlipSpectralWeight F m * Real.exp (-(σ * (Real.log m + tameDifferent m)))

theorem ramanujanAdjunctionEnergy_sub_gamma (m : ℕ) :
    ramanujanAdjunctionEnergy m - γ = Real.log m + tameDifferent m := by
  unfold ramanujanAdjunctionEnergy; ring

theorem conductorLaplaceTerm_nonneg (F : Finset ℕ) (σ : ℝ) (m : ℕ) :
    0 ≤ conductorLaplaceTerm F σ m :=
  mul_nonneg (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) (Real.exp_pos _).le

theorem conductorLaplaceTerm_one (F : Finset ℕ) (σ : ℝ) : conductorLaplaceTerm F σ 1 = 1 := by
  simp [conductorLaplaceTerm, finiteFlipSpectralWeight,
    (finiteFlipMobius_isMultiplicative F).map_one, tameDifferent_one]

theorem conductorLaplaceTerm_mul (F : Finset ℕ) (σ : ℝ) {m n : ℕ} (h : m.Coprime n) :
    conductorLaplaceTerm F σ (m * n) = conductorLaplaceTerm F σ m * conductorLaplaceTerm F σ n := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [Nat.coprime_zero_left] at h; subst h; simp [conductorLaplaceTerm_one]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.coprime_zero_right] at h; subst h; simp [conductorLaplaceTerm_one]
  unfold conductorLaplaceTerm finiteFlipSpectralWeight
  rw [(finiteFlipMobius_isMultiplicative F).map_mul_of_coprime h, Nat.totient_mul h,
    tameDifferent_mul h]
  have hm' : (m : ℝ) ≠ 0 := by positivity
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have hlog : Real.log ((m * n : ℕ) : ℝ) = Real.log m + Real.log n := by
    push_cast; exact Real.log_mul hm' hn'
  rw [hlog]
  have hexp : Real.exp (-(σ * (Real.log m + Real.log n + (tameDifferent m + tameDifferent n)))) =
      Real.exp (-(σ * (Real.log m + tameDifferent m))) *
        Real.exp (-(σ * (Real.log n + tameDifferent n))) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hexp]
  push_cast
  rw [mul_pow, mul_div_mul_comm]
  ring

/-- On prime powers: `f(p^{n+1}) ≤ (4/(p − 1)) p^{−σ} p^{−n}`. -/
theorem conductorLaplaceTerm_prime_pow_le (F : Finset ℕ) {σ : ℝ} (hσ : 0 ≤ σ) {p : ℕ}
    (hp : p.Prime) (n : ℕ) :
    conductorLaplaceTerm F σ (p ^ (n + 1)) ≤
      4 / ((p : ℝ) - 1) * (p : ℝ) ^ (-σ) * (1 / (p : ℝ)) ^ n := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hrhs : 0 ≤ 4 / ((p : ℝ) - 1) * (p : ℝ) ^ (-σ) * (1 / (p : ℝ)) ^ n := by
    have : 0 < (p : ℝ) - 1 := by linarith
    positivity
  unfold conductorLaplaceTerm
  rw [finiteFlipSpectralWeight_eq]
  split_ifs with hmem
  · rw [Nat.primeFactors_prime_pow (by omega) hp, card_singleton, pow_one,
      Nat.totient_prime_pow_succ hp, Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hp.one_le, Nat.cast_one]
    have hexp : Real.exp (-(σ * (Real.log ((p ^ (n + 1) : ℕ) : ℝ) + tameDifferent (p ^ (n + 1))))) ≤
        (p : ℝ) ^ (-σ) := by
      rw [Real.rpow_def_of_pos (by linarith)]
      refine Real.exp_le_exp.mpr ?_
      have h1 : Real.log p ≤ Real.log ((p ^ (n + 1) : ℕ) : ℝ) :=
        Real.log_le_log (by linarith) (by push_cast; exact le_self_pow₀ (by linarith) (by omega))
      have h2 := tameDifferent_nonneg (p ^ (n + 1))
      nlinarith
    have hw : (4 : ℝ) / ((p : ℝ) ^ n * ((p : ℝ) - 1)) = 4 / ((p : ℝ) - 1) * (1 / (p : ℝ)) ^ n := by
      have : (p : ℝ) - 1 ≠ 0 := by linarith
      rw [one_div_pow]; field_simp
    rw [hw]
    calc 4 / ((p : ℝ) - 1) * (1 / (p : ℝ)) ^ n *
          Real.exp (-(σ * (Real.log ((p ^ (n + 1) : ℕ) : ℝ) + tameDifferent (p ^ (n + 1))))) ≤
          4 / ((p : ℝ) - 1) * (1 / (p : ℝ)) ^ n * (p : ℝ) ^ (-σ) :=
          mul_le_mul_of_nonneg_left hexp (by
            have : (0 : ℝ) < (p : ℝ) - 1 := (by linarith)
            positivity)
      _ = _ := by ring
  · rw [zero_mul]; exact hrhs

theorem conductorLaplaceTerm_prime_pow_le_half (F : Finset ℕ) {σ : ℝ} (hσ : 0 ≤ σ) {p : ℕ}
    (hp : p.Prime) (n : ℕ) : conductorLaplaceTerm F σ (p ^ (n + 1)) ≤ 4 * (1 / 2 : ℝ) ^ n := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  refine (conductorLaplaceTerm_prime_pow_le F hσ hp n).trans ?_
  have h1 : 4 / ((p : ℝ) - 1) ≤ 4 := div_le_self (by norm_num) (by linarith)
  have h2 : (p : ℝ) ^ (-σ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have h3 : (1 / (p : ℝ)) ^ n ≤ (1 / 2 : ℝ) ^ n :=
    pow_le_pow_left₀ (by positivity) (one_div_le_one_div_of_le (by norm_num) hp2) n
  have h4 : 0 ≤ 4 / ((p : ℝ) - 1) := div_nonneg (by norm_num) (by linarith)
  have h5 : 0 ≤ (p : ℝ) ^ (-σ) := Real.rpow_nonneg (by linarith) _
  calc 4 / ((p : ℝ) - 1) * (p : ℝ) ^ (-σ) * (1 / (p : ℝ)) ^ n ≤ 4 * 1 * (1 / 2 : ℝ) ^ n :=
        mul_le_mul (mul_le_mul h1 h2 h5 (by norm_num)) h3 (by positivity) (by norm_num)
    _ = _ := by ring

theorem summable_conductorLaplaceTerm_prime_pow (F : Finset ℕ) {σ : ℝ} (hσ : 0 ≤ σ) {p : ℕ}
    (hp : p.Prime) : Summable fun n => ‖conductorLaplaceTerm F σ (p ^ n)‖ := by
  rw [← summable_nat_add_iff 1]
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num : (1 / 2 : ℝ) < 1)).mul_left 4)
  rw [Real.norm_of_nonneg (conductorLaplaceTerm_nonneg F σ _)]
  exact conductorLaplaceTerm_prime_pow_le_half F hσ hp n

/-- The Euler factor: `Σ_n f(p^n) ≤ 1 + 4 p^{−σ} p/(p − 1)²`. -/
theorem tsum_conductorLaplaceTerm_prime_pow_le (F : Finset ℕ) {σ : ℝ} (hσ : 0 ≤ σ) {p : ℕ}
    (hp : p.Prime) :
    ∑' n, conductorLaplaceTerm F σ (p ^ n) ≤ 1 + 4 * (p : ℝ) ^ (-σ) * p / ((p : ℝ) - 1) ^ 2 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hs : Summable fun n => conductorLaplaceTerm F σ (p ^ n) :=
    (summable_conductorLaplaceTerm_prime_pow F hσ hp).of_norm
  rw [hs.tsum_eq_zero_add, pow_zero, conductorLaplaceTerm_one]
  have hr0 : (0 : ℝ) ≤ 1 / p := by positivity
  have hr1 : (1 : ℝ) / p < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hgeo := (summable_geometric_of_lt_one hr0 hr1).mul_left (4 / ((p : ℝ) - 1) * (p : ℝ) ^ (-σ))
  have hle := Summable.tsum_le_tsum (fun n => conductorLaplaceTerm_prime_pow_le F hσ hp n)
    ((summable_nat_add_iff 1).mpr hs) hgeo
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1] at hle
  have e : 4 / ((p : ℝ) - 1) * (p : ℝ) ^ (-σ) * (1 - 1 / (p : ℝ))⁻¹ =
      4 * (p : ℝ) ^ (-σ) * p / ((p : ℝ) - 1) ^ 2 := by
    have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
    have h2 : (p : ℝ) ≠ 0 := by linarith
    rw [show (1 : ℝ) - 1 / p = ((p : ℝ) - 1) / p by field_simp]
    field_simp
  linarith

/-- `4 p^{−σ} p/(p − 1)² ≤ 4 p^{−1−σ} + 32/(p(p − 1))`. -/
theorem flipLaplaceFactor_le {p : ℕ} (hp : p.Prime) {σ : ℝ} (hσ : 0 ≤ σ) :
    4 * (p : ℝ) ^ (-σ) * p / ((p : ℝ) - 1) ^ 2 ≤
      4 * (p : ℝ) ^ (-(1 + σ)) + 32 * (1 / ((p : ℝ) * ((p : ℝ) - 1))) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  set q := (p : ℝ) ^ (-σ)
  have hq0 : 0 ≤ q := Real.rpow_nonneg (by linarith) _
  have hq1 : q ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have e : (p : ℝ) ^ (-(1 + σ)) = q / p := by
    rw [show -(1 + σ) = -σ + -1 by ring, Real.rpow_add (by linarith), Real.rpow_neg_one]; ring
  rw [e]
  have hp1 : 0 < (p : ℝ) - 1 := by linarith
  have key : 4 * (p : ℝ) / ((p : ℝ) - 1) ^ 2 ≤ 4 / p + 32 / ((p : ℝ) * ((p : ℝ) - 1)) := by
    rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos (by linarith : (0 : ℝ) < p) hp1]
  calc 4 * q * p / ((p : ℝ) - 1) ^ 2 = q * (4 * (p : ℝ) / ((p : ℝ) - 1) ^ 2) := by ring
    _ ≤ q * (4 / p + 32 / ((p : ℝ) * ((p : ℝ) - 1))) := mul_le_mul_of_nonneg_left key hq0
    _ = 4 * (q / p) + q * (32 / ((p : ℝ) * ((p : ℝ) - 1))) := by ring
    _ ≤ 4 * (q / p) + 32 * (1 / ((p : ℝ) * ((p : ℝ) - 1))) := by
        have h32 : 0 ≤ 32 / ((p : ℝ) * ((p : ℝ) - 1)) := by positivity
        have := mul_le_mul_of_nonneg_right hq1 h32
        rw [mul_one_div]; linarith

/-- **The Euler-product bound for packets.** For `σ ≥ 0` and a packet `S` below `Q`,
`Σ_{m ∈ S} w_P(m) e^{−σ(E_m − γ)} ≤ exp(4 Σ_{p ∈ P, p ≤ Q} p^{−1−σ} + 32)`. -/
theorem sum_conductorLaplace_le (P : Set ℕ) {σ : ℝ} (hσ : 0 ≤ σ) (S : Finset ℕ) {Q : ℕ}
    (hQ : ∀ m ∈ S, m ≤ Q) :
    ∑ m ∈ S, primeSetSpectralWeight P m * Real.exp (-(σ * (ramanujanAdjunctionEnergy m - γ))) ≤
      Real.exp (4 * ∑ p ∈ primeSetCutoff P Q, (p : ℝ) ^ (-(1 + σ)) + 32) := by
  classical
  set F := primeSetCutoff P Q
  set f := conductorLaplaceTerm F σ
  have hS : ∑ m ∈ S, primeSetSpectralWeight P m *
      Real.exp (-(σ * (ramanujanAdjunctionEnergy m - γ))) = ∑ m ∈ S, f m :=
    sum_congr rfl fun m hm => by
      rw [primeSetSpectralWeight, primeSetMobius_eq_finiteCutoff P (hQ m hm),
        ramanujanAdjunctionEnergy_sub_gamma]
      rfl
  rw [hS]
  obtain ⟨-, hhas⟩ := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (conductorLaplaceTerm_one F σ) (fun h => conductorLaplaceTerm_mul F σ h)
    (fun hp => summable_conductorLaplaceTerm_prime_pow F hσ hp) F
  have hfilt : ∑ m ∈ S, f m = ∑ m ∈ S with m ∈ Nat.factoredNumbers F, f m := by
    rw [sum_filter]
    refine sum_congr rfl fun m _ => ?_
    split_ifs with h
    · rfl
    · simp only [f, conductorLaplaceTerm]
      rw [finiteFlipSpectralWeight_eq, if_neg h, zero_mul]
  rw [hfilt, ← sum_subtype_eq_sum_filter]
  refine (sum_le_hasSum _ (fun x _ => conductorLaplaceTerm_nonneg _ _ _) hhas).trans ?_
  have hFp : F.filter Nat.Prime = F := filter_true_of_mem fun p hp => primeSetCutoff_prime' P Q p hp
  rw [hFp]
  have hF2 : ∀ p ∈ F, 2 ≤ p := fun p hp => (primeSetCutoff_prime' P Q p hp).two_le
  calc ∏ p ∈ F, ∑' n, f (p ^ n) ≤
        ∏ p ∈ F, Real.exp (4 * (p : ℝ) ^ (-(1 + σ)) + 32 * (1 / ((p : ℝ) * ((p : ℝ) - 1)))) := by
        refine prod_le_prod (fun p _ => tsum_nonneg fun n => conductorLaplaceTerm_nonneg _ _ _)
          fun p hp => ?_
        have hpp := primeSetCutoff_prime' P Q p hp
        have h1 := tsum_conductorLaplaceTerm_prime_pow_le F hσ hpp
        have h2 := flipLaplaceFactor_le hpp hσ
        have h3 := Real.add_one_le_exp
          (4 * (p : ℝ) ^ (-(1 + σ)) + 32 * (1 / ((p : ℝ) * ((p : ℝ) - 1))))
        linarith
    _ = Real.exp (∑ p ∈ F, (4 * (p : ℝ) ^ (-(1 + σ)) + 32 * (1 / ((p : ℝ) * ((p : ℝ) - 1))))) :=
        (Real.exp_sum _ _).symm
    _ ≤ _ := by
        refine Real.exp_le_exp.mpr ?_
        rw [sum_add_distrib, ← mul_sum, ← mul_sum]
        have := sum_inv_mul_pred_le F hF2
        linarith

end Euler

section Laplace

/-- **Dyadic upper Laplace bound**: for `x ≥ x₀ > 0` and every `J`,
`1/x ≤ e^{−x}/x₀ + Σ_{j < J} 2^{−j−1} e^{−2^{−j−1} x} + 2^{−J}`. -/
theorem inv_le_dyadic {x x₀ : ℝ} (hx₀ : 0 < x₀) (hx : x₀ ≤ x) (J : ℕ) :
    1 / x ≤ Real.exp (-x) / x₀ +
      ∑ j ∈ range J, (1 / 2 : ℝ) ^ (j + 1) * Real.exp (-((1 / 2 : ℝ) ^ (j + 1) * x)) +
        (1 / 2 : ℝ) ^ J := by
  have hx0 : 0 < x := hx₀.trans_le hx
  have hstep : ∀ j : ℕ, (Real.exp (-((1 / 2 : ℝ) ^ (j + 1) * x)) -
      Real.exp (-((1 / 2 : ℝ) ^ j * x))) / x ≤
        (1 / 2 : ℝ) ^ (j + 1) * Real.exp (-((1 / 2 : ℝ) ^ (j + 1) * x)) := by
    intro j
    set a := (1 / 2 : ℝ) ^ (j + 1) * x
    have ha : (1 / 2 : ℝ) ^ j * x = 2 * a := by simp only [a, pow_succ]; ring
    rw [ha, div_le_iff₀ hx0]
    have h1 : Real.exp (-(2 * a)) = Real.exp (-a) * Real.exp (-a) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [h1]
    have h2 := Real.add_one_le_exp (-a)
    have h3 := Real.exp_pos (-a)
    have h4 := mul_le_mul_of_nonneg_left h2 h3.le
    have e : (1 / 2 : ℝ) ^ (j + 1) * Real.exp (-a) * x = a * Real.exp (-a) := by simp only [a]; ring
    rw [e]
    nlinarith
  have htel : (Real.exp (-((1 / 2 : ℝ) ^ J * x)) - Real.exp (-((1 / 2 : ℝ) ^ 0 * x))) / x =
      ∑ j ∈ range J, (Real.exp (-((1 / 2 : ℝ) ^ (j + 1) * x)) -
        Real.exp (-((1 / 2 : ℝ) ^ j * x))) / x := by
    rw [← sum_div, sum_range_sub (fun j => Real.exp (-((1 / 2 : ℝ) ^ j * x)))]
  have hsum := sum_le_sum fun j (_ : j ∈ range J) => hstep j
  have hlast : (1 - Real.exp (-((1 / 2 : ℝ) ^ J * x))) / x ≤ (1 / 2 : ℝ) ^ J := by
    rw [div_le_iff₀ hx0]
    have := Real.add_one_le_exp (-((1 / 2 : ℝ) ^ J * x))
    linarith
  have hfirst : Real.exp (-((1 / 2 : ℝ) ^ 0 * x)) / x ≤ Real.exp (-x) / x₀ := by
    rw [pow_zero, one_mul]
    exact div_le_div_of_nonneg_left (Real.exp_pos _).le hx₀ hx
  have e : 1 / x = Real.exp (-((1 / 2 : ℝ) ^ 0 * x)) / x +
      (Real.exp (-((1 / 2 : ℝ) ^ J * x)) - Real.exp (-((1 / 2 : ℝ) ^ 0 * x))) / x +
        (1 - Real.exp (-((1 / 2 : ℝ) ^ J * x))) / x := by
    field_simp; ring
  rw [e, htel]
  linarith

end Laplace

section Summable

/-- **The conductor series converges below a quarter.** If
`Σ_{p ∈ P, p ≤ n} log p/p ≤ κ log n + C` with `0 ≤ κ < 1/4`, then for `0 ≤ s < 2 log 2` the series
`Σ_{m ≥ 2} w_P(m)/(E_m − γ − s)` is summable. -/
theorem summable_conductorSeries (P : Set ℕ) {κ C : ℝ} (hκ0 : 0 ≤ κ) (hκ : κ < 1 / 4)
    (hP : ∀ n : ℕ, 1 ≤ n → primeSetLogMass P n ≤ κ * Real.log n + C) {s : ℝ} (hs : 0 ≤ s)
    (hs2 : s < 2 * Real.log 2) :
    Summable fun k : ℕ => primeSetSpectralWeight P (k + 2) /
      (ramanujanAdjunctionEnergy (k + 2) - γ - s) := by
  obtain ⟨K, hK0, hK⟩ := exists_sum_primeSetCutoff_rpow_le P hκ0 hP
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set x₀ := 2 * Real.log 2 - s
  have hx₀ : 0 < x₀ := by simp only [x₀]; linarith
  set M₀ := Real.exp (4 * K + 32)
  set e4 := Real.exp (4 * κ * Real.log 2)
  set q := e4 / 2
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by
    simp only [q, e4]
    rw [div_lt_one two_pos]
    calc Real.exp (4 * κ * Real.log 2) < Real.exp (Real.log 2) :=
          Real.exp_lt_exp.mpr (by nlinarith)
      _ = 2 := Real.exp_log two_pos
  have hw0 : ∀ m, 0 ≤ primeSetSpectralWeight P m := fun m =>
    div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  -- the packet Laplace bound at `σ = 2^{−j}`
  have hlap : ∀ (S : Finset ℕ) (Q : ℕ), (∀ m ∈ S, m ≤ Q) → ∀ j : ℕ,
      ∑ m ∈ S, primeSetSpectralWeight P m *
        Real.exp (-((1 / 2 : ℝ) ^ j * (ramanujanAdjunctionEnergy m - γ))) ≤ M₀ * e4 ^ j := by
    intro S Q hQ j
    have hσ0 : (0 : ℝ) < (1 / 2) ^ j := by positivity
    have hσ1 : ((1 : ℝ) / 2) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    refine (sum_conductorLaplace_le P hσ0.le S hQ).trans ?_
    have hp := hK _ hσ0 hσ1 Q
    have hlog : Real.log (1 / (1 / 2 : ℝ) ^ j) = j * Real.log 2 := by
      rw [one_div_pow, one_div_one_div, Real.log_pow]
    rw [hlog] at hp
    calc Real.exp (4 * ∑ p ∈ primeSetCutoff P Q, (p : ℝ) ^ (-(1 + (1 / 2 : ℝ) ^ j)) + 32) ≤
          Real.exp (4 * (κ * (j * Real.log 2) + K) + 32) := Real.exp_le_exp.mpr (by linarith)
      _ = M₀ * e4 ^ j := by
          simp only [M₀, e4]
          rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
  set B := Real.exp s * M₀ / x₀ + Real.exp s * M₀ / (1 - q) + 1
  have hf0 : ∀ k : ℕ, 0 ≤ primeSetSpectralWeight P (k + 2) /
      (ramanujanAdjunctionEnergy (k + 2) - γ - s) := fun k => by
    refine div_nonneg (hw0 _) ?_
    have := conductorEnergy_gap (m := k + 2) (by omega); linarith
  refine summable_of_sum_range_le (c := B) hf0 fun n => ?_
  set S := (range n).image (· + 2)
  have hSQ : ∀ m ∈ S, m ≤ n + 2 := fun m hm => by
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hm; have := mem_range.mp hk; omega
  have hS2 : ∀ m ∈ S, 2 ≤ m := fun m hm => by obtain ⟨k, -, rfl⟩ := mem_image.mp hm; omega
  set Wt := ∑ m ∈ S, primeSetSpectralWeight P m
  have hWt : 0 ≤ Wt := sum_nonneg fun m _ => hw0 m
  obtain ⟨J, hJ⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / (Wt + 1) by positivity)
    (by norm_num : (1 / 2 : ℝ) < 1)
  have hJW : (1 / 2 : ℝ) ^ J * Wt ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hJ.le hWt
    have : 1 / (Wt + 1) * Wt ≤ 1 := by rw [one_div_mul_eq_div, div_le_one (by linarith)]; linarith
    linarith
  have hrw : ∑ m ∈ S, primeSetSpectralWeight P m / (ramanujanAdjunctionEnergy m - γ - s) =
      ∑ k ∈ range n, primeSetSpectralWeight P (k + 2) /
        (ramanujanAdjunctionEnergy (k + 2) - γ - s) :=
    sum_image fun a _ b _ h => by omega
  rw [← hrw]
  -- termwise dyadic bound
  have hshift : ∀ (σ : ℝ) (m : ℕ), Real.exp (-(σ * (ramanujanAdjunctionEnergy m - γ - s))) =
      Real.exp (σ * s) * Real.exp (-(σ * (ramanujanAdjunctionEnergy m - γ))) := fun σ m => by
    rw [← Real.exp_add]; congr 1; ring
  have hterm : ∀ m ∈ S, primeSetSpectralWeight P m / (ramanujanAdjunctionEnergy m - γ - s) ≤
      Real.exp s / x₀ * (primeSetSpectralWeight P m * Real.exp (-((1 / 2 : ℝ) ^ 0 *
          (ramanujanAdjunctionEnergy m - γ)))) +
        ∑ j ∈ range J, (1 / 2 : ℝ) ^ (j + 1) * Real.exp ((1 / 2 : ℝ) ^ (j + 1) * s) *
          (primeSetSpectralWeight P m * Real.exp (-((1 / 2 : ℝ) ^ (j + 1) *
            (ramanujanAdjunctionEnergy m - γ)))) +
        (1 / 2 : ℝ) ^ J * primeSetSpectralWeight P m := by
    intro m hm
    have hx : x₀ ≤ ramanujanAdjunctionEnergy m - γ - s := by
      have := conductorEnergy_gap (hS2 m hm); simp only [x₀]; linarith
    have h := inv_le_dyadic hx₀ hx J
    have h' := mul_le_mul_of_nonneg_left h (hw0 m)
    have e1 : Real.exp (-(ramanujanAdjunctionEnergy m - γ - s)) =
        Real.exp s * Real.exp (-((1 / 2 : ℝ) ^ 0 * (ramanujanAdjunctionEnergy m - γ))) := by
      have := hshift 1 m; simp only [one_mul, pow_zero] at this ⊢; exact this
    rw [e1] at h'
    simp only [hshift] at h'
    rw [div_eq_mul_one_div]
    refine h'.trans (le_of_eq ?_)
    rw [mul_add, mul_add, mul_sum]
    congr 1
    · congr 1
      · ring
      · exact sum_congr rfl fun j _ => by ring
    · ring
  refine (sum_le_sum hterm).trans ?_
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum, sum_comm, ← mul_sum]
  -- the three pieces
  have hp1 : Real.exp s / x₀ * ∑ m ∈ S, primeSetSpectralWeight P m *
      Real.exp (-((1 / 2 : ℝ) ^ 0 * (ramanujanAdjunctionEnergy m - γ))) ≤
      Real.exp s * M₀ / x₀ := by
    have h := hlap S (n + 2) hSQ 0
    rw [pow_zero e4, mul_one] at h
    calc _ ≤ Real.exp s / x₀ * M₀ := mul_le_mul_of_nonneg_left h (by positivity)
      _ = _ := by ring
  have hp2 : ∑ j ∈ range J, ∑ m ∈ S, (1 / 2 : ℝ) ^ (j + 1) * Real.exp ((1 / 2 : ℝ) ^ (j + 1) * s) *
      (primeSetSpectralWeight P m * Real.exp (-((1 / 2 : ℝ) ^ (j + 1) *
        (ramanujanAdjunctionEnergy m - γ)))) ≤ Real.exp s * M₀ / (1 - q) := by
    have hj : ∀ j ∈ range J, ∑ m ∈ S, (1 / 2 : ℝ) ^ (j + 1) * Real.exp ((1 / 2 : ℝ) ^ (j + 1) * s) *
        (primeSetSpectralWeight P m * Real.exp (-((1 / 2 : ℝ) ^ (j + 1) *
          (ramanujanAdjunctionEnergy m - γ)))) ≤ Real.exp s * M₀ * q ^ j := by
      intro j _
      rw [← mul_sum]
      have hσ1 : ((1 : ℝ) / 2) ^ (j + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have hes : Real.exp ((1 / 2 : ℝ) ^ (j + 1) * s) ≤ Real.exp s :=
        Real.exp_le_exp.mpr (by nlinarith)
      have hL := hlap S (n + 2) hSQ (j + 1)
      have hq : (1 / 2 : ℝ) ^ (j + 1) * e4 ^ (j + 1) ≤ q ^ j := by
        rw [← mul_pow]
        have : (1 / 2 : ℝ) * e4 = q := by simp only [q]; ring
        rw [this, pow_succ]
        exact mul_le_of_le_one_right (pow_nonneg hq0 _) hq1.le
      calc (1 / 2 : ℝ) ^ (j + 1) * Real.exp ((1 / 2 : ℝ) ^ (j + 1) * s) *
            ∑ m ∈ S, primeSetSpectralWeight P m * Real.exp (-((1 / 2 : ℝ) ^ (j + 1) *
              (ramanujanAdjunctionEnergy m - γ))) ≤
            (1 / 2 : ℝ) ^ (j + 1) * Real.exp s * (M₀ * e4 ^ (j + 1)) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hes (by positivity)) hL
              (sum_nonneg fun m _ => mul_nonneg (hw0 m) (Real.exp_pos _).le) (by positivity)
        _ = Real.exp s * M₀ * ((1 / 2 : ℝ) ^ (j + 1) * e4 ^ (j + 1)) := by ring
        _ ≤ Real.exp s * M₀ * q ^ j := mul_le_mul_of_nonneg_left hq (by positivity)
    refine (sum_le_sum hj).trans ?_
    rw [← mul_sum]
    have hgeo : ∑ j ∈ range J, q ^ j ≤ (1 - q)⁻¹ := by
      rw [← tsum_geometric_of_lt_one hq0 hq1]
      exact (summable_geometric_of_lt_one hq0 hq1).sum_le_tsum _ fun j _ => pow_nonneg hq0 _
    calc Real.exp s * M₀ * ∑ j ∈ range J, q ^ j ≤ Real.exp s * M₀ * (1 - q)⁻¹ :=
          mul_le_mul_of_nonneg_left hgeo (by positivity)
      _ = _ := by rw [div_eq_mul_inv]
  have hp3 : (1 / 2 : ℝ) ^ J * Wt ≤ 1 := hJW
  simp only [B]
  linarith

end Summable

section Unconditional

theorem primeSetLogMass_le_of_abs (P : Set ℕ) {κ C : ℝ}
    (hP : ∀ n, 1 ≤ n → |primeSetLogMass P n - κ * Real.log n| ≤ C) :
    ∀ n : ℕ, 1 ≤ n → primeSetLogMass P n ≤ κ * Real.log n + C := fun n hn => by
  have := (abs_le.mp (hP n hn)).2; linarith

/-- **The excited spectral weight is the conductor series.** For relative log density
`κ ∈ (0, 1/4)` and `0 < s < t < 2 log 2`: for every `ε > 0`, eventually, for every ground index `i₀`
below `γ + t`, `|ρ_{i₀}(v_P)/c_N² − W_P(s)| ≤ ε`, with `W_P(s) = Σ_{m ≥ 2} w_P(m)/(E_m − γ − s) < ∞`. -/
theorem eventually_abs_excitedResolvent_div_sub_conductorSeries_le (P : Set ℕ) {κ C : ℝ}
    (hκ0 : 0 < κ) (hκ : κ < 1 / 4)
    (hP : ∀ n, 1 ≤ n → |primeSetLogMass P n - κ * Real.log n| ≤ C)
    {s t : ℝ} (hs : 0 < s) (hst : s < t) (ht2 : t < 2 * Real.log 2) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ i₀ : PrimeHorizonIndex N, IsGroundBelow N t i₀ →
      |excitedResolvent N s i₀ (primeSetHorizonVector P N) /
          harmonicCorrelation (primeSetFlip P) N ^ 2 -
        ∑' k : ℕ, primeSetSpectralWeight P (k + 2) / (ramanujanAdjunctionEnergy (k + 2) - γ - s)| ≤
        ε :=
  eventually_abs_excitedResolvent_div_sub_le P hκ0 hκ hP hs hst ht2
    (summable_conductorSeries P hκ0.le hκ (primeSetLogMass_le_of_abs P hP) hs.le (hst.trans ht2)) hε

/-- **The spectral-weight estimate with the exact constant**: off the ground,
`⟨w, v_P⟩² ≤ c_N² (W_P(s) + ε)(Q_N(w) − s|w|²)` eventually. -/
theorem eventually_inner_sq_le_tsum_conductorSeries (P : Set ℕ) {κ C : ℝ} (hκ0 : 0 < κ)
    (hκ : κ < 1 / 4) (hP : ∀ n, 1 ≤ n → |primeSetLogMass P n - κ * Real.log n| ≤ C)
    {s t : ℝ} (hs : 0 < s) (hst : s < t) (ht2 : t < 2 * Real.log 2) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ i₀ : PrimeHorizonIndex N, IsGroundBelow N t i₀ →
      ∀ w : EuclideanSpace ℝ (PrimeHorizonIndex N), ⟪w, primeEigen N i₀⟫ = 0 →
        ⟪w, primeSetHorizonVector P N⟫ ^ 2 ≤ harmonicCorrelation (primeSetFlip P) N ^ 2 *
          ((∑' k : ℕ, primeSetSpectralWeight P (k + 2) /
            (ramanujanAdjunctionEnergy (k + 2) - γ - s)) + ε) * (primeEnergy N w - s * ‖w‖ ^ 2) := by
  have hsum := summable_conductorSeries P hκ0.le hκ (primeSetLogMass_le_of_abs P hP) hs.le
    (hst.trans ht2)
  refine eventually_inner_sq_le_conductorSeries P hκ0 hκ hP hs hst ht2 (fun K => ?_) hε
  refine hsum.sum_le_tsum _ fun k _ => div_nonneg (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) ?_
  have := conductorEnergy_gap (m := k + 2) (by omega)
  linarith [hst.trans ht2]

/-- **Classification by the value of the conductor series.** A flip twin of relative log density
`κ ∈ (0, 1/4)` is separated from `ζ` by the atomic Hodge index iff `W_P(s) > 1/s` for some
`s ∈ (0, 2 log 2)`. -/
theorem hodgeSeparates_primeSetFlip_iff_conductorSeries (P : Set ℕ) {κ C : ℝ} (hκ0 : 0 < κ)
    (hκ : κ < 1 / 4) (hP : ∀ n, 1 ≤ n → |primeSetLogMass P n - κ * Real.log n| ≤ C) :
    HodgeSeparates (primeSetFlip P) ↔ ∃ s, 0 < s ∧ s < 2 * Real.log 2 ∧
      1 / s < ∑' k : ℕ, primeSetSpectralWeight P (k + 2) /
        (ramanujanAdjunctionEnergy (k + 2) - γ - s) := by
  rw [hodgeSeparates_primeSetFlip_iff_packet P hκ0 hκ hP]
  have hf0 : ∀ s, s < 2 * Real.log 2 → ∀ k : ℕ, 0 ≤ primeSetSpectralWeight P (k + 2) /
      (ramanujanAdjunctionEnergy (k + 2) - γ - s) := fun s hs2 k => by
    refine div_nonneg (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) ?_
    have := conductorEnergy_gap (m := k + 2) (by omega); linarith
  constructor
  · rintro ⟨s, hs, hs2, S, hS, h⟩
    refine ⟨s, hs, hs2, h.trans_le ?_⟩
    have hsum := summable_conductorSeries P hκ0.le hκ (primeSetLogMass_le_of_abs P hP) hs.le hs2
    have himg : ∑ m ∈ S, primeSetSpectralWeight P m / (ramanujanAdjunctionEnergy m - γ - s) =
        ∑ k ∈ S.image (· - 2), primeSetSpectralWeight P (k + 2) /
          (ramanujanAdjunctionEnergy (k + 2) - γ - s) := by
      rw [sum_image fun a ha b hb h => by have := hS a ha; have := hS b hb; omega]
      exact sum_congr rfl fun m hm => by rw [Nat.sub_add_cancel (hS m hm)]
    rw [himg]
    exact hsum.sum_le_tsum _ fun k _ => hf0 s hs2 k
  · rintro ⟨s, hs, hs2, h⟩
    have hsum := summable_conductorSeries P hκ0.le hκ (primeSetLogMass_le_of_abs P hP) hs.le hs2
    obtain ⟨K, hK⟩ := (hsum.hasSum.tendsto_sum_nat.eventually (Ioi_mem_nhds h)).exists
    refine ⟨s, hs, hs2, (range K).image (· + 2), fun m hm => by
      obtain ⟨k, -, rfl⟩ := mem_image.mp hm; omega, ?_⟩
    rw [sum_image fun a _ b _ h => by omega]
    exact hK

end Unconditional

end GaloisForLFunctions.RenormalizedIntersectionTheory
