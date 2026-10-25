import GaloisForLFunctions.ArithmeticDefectRigidity.TheOriginTraceControlsMovingSuccessors
import GaloisForLFunctions.HTGeometry.UniformSmallBudgetsVanishAfterNormalization

/-!
# Recentered successors vanish at the energy scale

A head, middle, and tail decomposition makes the actual additive-defect energy
uniformly little-oh of the translation length. Bounded energy-relative shifts
therefore disappear along every escaping receiver.
-/
noncomputable section
set_option autoImplicit false
open Finset Filter Topology RHTower
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
open GaloisForLFunctions.ArithmeticCompensationTheory

namespace GaloisForLFunctions.ArithmeticDefectRigidity

private theorem pronic_tail_indicator_le {N : ℕ} (hN : 1 ≤ N) (T : ℕ) :
    (∑ n ∈ Icc 1 T, if N ≤ n then 1 / ((n : ℝ) * ((n : ℝ) + 1)) else 0) ≤
      1 / (N : ℝ) := by
  classical
  have heq : (Icc 1 T).filter (fun n => N ≤ n) = Icc N T := by
    ext n
    simp only [mem_filter, mem_Icc]
    omega
  rw [← sum_filter, heq]
  by_cases hNT : N ≤ T + 1
  · rw [sum_Icc_pronic_tail_mass hN hNT]
    exact sub_le_self _ (by positivity)
  · rw [Icc_eq_empty (by omega), sum_empty]
    positivity

private theorem head_indicator_le (L T : ℕ) :
    (∑ n ∈ Icc 1 T, if n ≤ L then (1 : ℝ) else 0) ≤ L := by
  classical
  have heq : (Icc 1 T).filter (fun n => n ≤ L) = Icc 1 (min T L) := by
    ext n
    simp only [mem_filter, mem_Icc, le_min_iff]
    tauto
  rw [← sum_filter, heq]
  simpa only [sum_const, nsmul_eq_mul, mul_one, Nat.card_Icc, Nat.add_sub_cancel] using
    (show ((min T L : ℕ) : ℝ) ≤ (L : ℝ) by exact_mod_cast min_le_right T L)

/-- A small linear head, a bounded middle, and a capped tail give a uniform energy estimate. -/
theorem pronicNorm_three_region_sq_le (v : ℕ → ℝ) (L U k T : ℕ) (M : ℝ)
    (hLU : L ≤ U)
    (hhead : ∀ n, n ≤ L → |v n| ≤ (n : ℝ))
    (hmiddle : ∀ n, L < n → n ≤ U → |v n| ≤ M)
    (htail : ∀ n, U < n → |v n| ≤ (k : ℝ)) :
    pronicNorm T v ^ 2 ≤ (L : ℝ) + M ^ 2 / ((L : ℝ) + 1) +
      (k : ℝ) ^ 2 / ((U : ℝ) + 1) := by
  have hcell (n : ℕ) (hn : n ∈ Icc 1 T) :
      v n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
        (if n ≤ L then (1 : ℝ) else 0) +
        M ^ 2 * (if L + 1 ≤ n then 1 / ((n : ℝ) * ((n : ℝ) + 1)) else 0) +
        (k : ℝ) ^ 2 * (if U + 1 ≤ n then 1 / ((n : ℝ) * ((n : ℝ) + 1)) else 0) := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hd : (0 : ℝ) < (n : ℝ) * ((n : ℝ) + 1) := by positivity
    by_cases hL : n ≤ L
    · rw [if_pos hL, if_neg (by omega : ¬ L + 1 ≤ n),
        if_neg (by omega : ¬ U + 1 ≤ n), mul_zero, mul_zero, add_zero, add_zero]
      apply (div_le_one hd).mpr
      have hs := pow_le_pow_left₀ (abs_nonneg _) (hhead n hL) 2
      rw [sq_abs] at hs
      nlinarith only [hs, hn0.le]
    · have hLn : L < n := by omega
      rw [if_neg hL, if_pos (by omega : L + 1 ≤ n), zero_add]
      by_cases hU : n ≤ U
      · rw [if_neg (by omega : ¬ U + 1 ≤ n), mul_zero, add_zero, mul_one_div]
        apply div_le_div_of_nonneg_right _ hd.le
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hmiddle n hLn hU) 2
      · rw [if_pos (by omega : U + 1 ≤ n)]
        have hs : v n ^ 2 ≤ (k : ℝ) ^ 2 := by
          simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _)
            (htail n (by omega)) 2
        exact (div_le_div_of_nonneg_right hs hd.le).trans (by
          rw [mul_one_div, mul_one_div]
          exact le_add_of_nonneg_left (by positivity))
  calc
    _ ≤ ∑ n ∈ Icc 1 T,
        ((if n ≤ L then (1 : ℝ) else 0) +
        M ^ 2 * (if L + 1 ≤ n then 1 / ((n : ℝ) * ((n : ℝ) + 1)) else 0) +
        (k : ℝ) ^ 2 * (if U + 1 ≤ n then 1 / ((n : ℝ) * ((n : ℝ) + 1)) else 0)) := by
      rw [pronicNorm_sq]
      exact sum_le_sum hcell
    _ ≤ _ := by
      rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum]
      simpa only [Nat.cast_add, Nat.cast_one, mul_one_div] using
        add_le_add
          (add_le_add (head_indicator_le L T)
            (mul_le_mul_of_nonneg_left (pronic_tail_indicator_le (by omega : 1 ≤ L + 1) T)
              (sq_nonneg M)))
          (mul_le_mul_of_nonneg_left (pronic_tail_indicator_le (by omega : 1 ≤ U + 1) T)
            (sq_nonneg (k : ℝ)))

/-- Sublinearity is uniform beyond one fixed source index. -/
theorem exists_receiver_linear_tail (ε : SubcriticalDamping) {a : ℝ} (ha : 0 < a) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      |pmPowerDampedCenteredDivisorPrefix ε n| ≤ a * n := by
  have h := (receiver_div_nat_tendsto_zero ε).abs
  rw [abs_zero] at h
  obtain ⟨N, hN⟩ := eventually_atTop.mp (h.eventually (gt_mem_nhds ha))
  refine ⟨max 1 N, le_max_left _ _, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := (le_max_left 1 N).trans hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hbound := (hN n ((le_max_right 1 N).trans hn)).le
  rw [abs_div, abs_of_pos hn0] at hbound
  exact (div_le_iff₀ hn0).mp hbound

/-- A wide middle segment has arbitrarily small linear energy cost at large translations. -/
theorem recentered_three_region_bound (ε : SubcriticalDamping) {q N k : ℕ}
    (hq : 1 ≤ q) (hN : 1 ≤ N) {a : ℝ} (ha : 0 ≤ a)
    (hA : ∀ n : ℕ, N ≤ n → |pmPowerDampedCenteredDivisorPrefix ε n| ≤ a * n)
    (hk : q * N ≤ k) (T : ℕ) :
    pronicNorm T (fun n => receiverAdditiveDefect ε n k) ^ 2 ≤
      (2 / (q : ℝ) + 4 * a ^ 2 * q * ((q : ℝ) + 1) ^ 2) * k := by
  have hq0 : 0 < q := by omega
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
  have hNk : N ≤ k := (Nat.le_mul_of_pos_left N hq0).trans hk
  have hk0 : 0 < k := by omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have hL : N ≤ k / q := (Nat.le_div_iff_mul_le hq0).mpr (by simpa only [Nat.mul_comm] using hk)
  have hLU : k / q ≤ q * k :=
    (Nat.div_le_self k q).trans (Nat.le_mul_of_pos_left k hq0)
  have hmid (n : ℕ) (hLn : k / q < n) (hnU : n ≤ q * k) :
      |receiverAdditiveDefect ε n k| ≤ 2 * a * ((q : ℝ) + 1) * k := by
    have hNn : N ≤ n := hL.trans hLn.le
    have hAn := hA n hNn
    have hAk := hA k hNk
    have hAnk := hA (n + k) (hNn.trans (Nat.le_add_right n k))
    have hnR : (n : ℝ) ≤ (q : ℝ) * k := by exact_mod_cast hnU
    unfold receiverAdditiveDefect
    calc
      _ ≤ |pmPowerDampedCenteredDivisorPrefix ε (n + k) -
          pmPowerDampedCenteredDivisorPrefix ε n| +
          |pmPowerDampedCenteredDivisorPrefix ε k| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          abs_sub_le (pmPowerDampedCenteredDivisorPrefix ε (n + k) -
            pmPowerDampedCenteredDivisorPrefix ε n) 0 (pmPowerDampedCenteredDivisorPrefix ε k)
      _ ≤ |pmPowerDampedCenteredDivisorPrefix ε (n + k)| +
          |pmPowerDampedCenteredDivisorPrefix ε n| +
          |pmPowerDampedCenteredDivisorPrefix ε k| := by
        exact add_le_add (abs_sub _ _) le_rfl
      _ ≤ a * (n + k : ℕ) + a * n + a * k := add_le_add (add_le_add hAnk hAn) hAk
      _ ≤ _ := by
        push_cast
        nlinarith only [mul_le_mul_of_nonneg_left hnR ha]
  have hb := pronicNorm_three_region_sq_le (fun n => receiverAdditiveDefect ε n k)
    (k / q) (q * k) k T (2 * a * ((q : ℝ) + 1) * k) hLU
    (fun n _ => abs_receiverAdditiveDefect_le_left ε n k) hmid
    (fun n _ => by rw [receiverAdditiveDefect_symm]; exact abs_receiverAdditiveDefect_le_left ε k n)
  have hhead : ((k / q : ℕ) : ℝ) ≤ (k : ℝ) / q := by
    apply (le_div_iff₀ hqR).mpr
    exact_mod_cast Nat.div_mul_le_self k q
  have hfloor : (k : ℝ) ≤ (q : ℝ) * (((k / q : ℕ) : ℝ) + 1) := by
    have hrem := Nat.mod_lt k hq0
    have hid := Nat.div_add_mod k q
    have hnat : k ≤ q * (k / q) + q := by omega
    exact_mod_cast (show k ≤ q * (k / q + 1) by simpa only [Nat.mul_add, Nat.mul_one] using hnat)
  have hmiddle : (2 * a * ((q : ℝ) + 1) * k) ^ 2 / (((k / q : ℕ) : ℝ) + 1) ≤
      4 * a ^ 2 * ((q : ℝ) + 1) ^ 2 * q * k := by
    have hratio : (k : ℝ) / (((k / q : ℕ) : ℝ) + 1) ≤ q :=
      (div_le_iff₀ (by positivity)).mpr hfloor
    calc
      _ = (4 * a ^ 2 * ((q : ℝ) + 1) ^ 2 * k) *
          ((k : ℝ) / (((k / q : ℕ) : ℝ) + 1)) := by ring
      _ ≤ (4 * a ^ 2 * ((q : ℝ) + 1) ^ 2 * k) * q :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = _ := by ring
  have htail : (k : ℝ) ^ 2 / ((q * k : ℕ) + 1) ≤ (k : ℝ) / q := by
    apply (div_le_div_iff₀ (by positivity) hqR).mpr
    push_cast
    nlinarith only [hkR.le]
  exact hb.trans ((add_le_add (add_le_add hhead hmiddle) htail).trans_eq (by ring))

/-- Every positive linear coefficient admits a horizon-independent remainder. -/
theorem exists_uniform_sublinear_recentered_budget (ε : SubcriticalDamping)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k T : ℕ,
      pronicNorm T (fun n => receiverAdditiveDefect ε n k) ^ 2 ≤ δ * k + B := by
  obtain ⟨q, hq⟩ := exists_nat_gt (max 1 (4 / δ))
  have hqR : (0 : ℝ) < q := lt_trans (by norm_num : (0 : ℝ) < 1)
    ((le_max_left 1 (4 / δ)).trans_lt hq)
  have hqN : 1 ≤ q := by exact_mod_cast hqR
  let a : ℝ := Real.sqrt (δ / (8 * q * ((q : ℝ) + 1) ^ 2))
  have ha : 0 < a := Real.sqrt_pos.mpr (by positivity)
  obtain ⟨N, hN, hA⟩ := exists_receiver_linear_tail ε ha
  have hsmall : 2 / (q : ℝ) ≤ δ / 2 := by
    have h := (div_lt_iff₀ hδ).mp ((le_max_right 1 (4 / δ)).trans_lt hq)
    apply (div_le_iff₀ hqR).mpr
    nlinarith only [h]
  have haeq : 4 * a ^ 2 * q * ((q : ℝ) + 1) ^ 2 = δ / 2 := by
    dsimp only [a]
    rw [Real.sq_sqrt (by positivity)]
    field_simp
    norm_num
  have hc : 2 / (q : ℝ) + 4 * a ^ 2 * q * ((q : ℝ) + 1) ^ 2 ≤ δ := by
    rw [haeq]
    linarith only [hsmall]
  refine ⟨2 * (q * N : ℕ), by positivity, fun k T => ?_⟩
  by_cases hk : q * N ≤ k
  · have hb := recentered_three_region_bound ε hqN hN ha.le hA hk T
    have hcoef := mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg k)
    exact (hb.trans hcoef).trans (le_add_of_nonneg_right (by positivity))
  · have hkR : (k : ℝ) ≤ (q * N : ℕ) := by exact_mod_cast le_of_lt (lt_of_not_ge hk)
    exact (pronicNorm_receiverAdditiveDefect_sq_le ε k T).trans (by
      nlinarith only [hkR, mul_nonneg hδ.le (Nat.cast_nonneg k)])

/-- Recentered translations of bounded energy-relative length still disappear on escape. -/
theorem admits_or_energyScale_recentered_successors_disappear (ε : SubcriticalDamping) :
    Admits dampedMobiusEnergy ε ∨ ∀ k : ℕ → ℕ,
      (∃ C : ℝ, ∀ᶠ T : ℕ in atTop,
        (k T : ℝ) / dampedMobiusEnergy ε T ≤ C) →
      Tendsto (fun T => pronicNorm T (fun n => receiverAdditiveDefect ε n (k T)) ^ 2 /
        dampedMobiusEnergy ε T) atTop (𝓝 0) := by
  rcases admits_or_tendsto_atTop (ε : ℝ) with h | hE
  · exact Or.inl h
  · refine Or.inr fun k hk => HTGeometry.normalized_cost_tendsto_zero_of_uniform_small_budget
      (fun k T => pronicNorm T (fun n => receiverAdditiveDefect ε n k) ^ 2)
      (fun k => (k : ℝ)) (dampedMobiusEnergy ε) (fun k T => sq_nonneg _) ?_ hE k hk
    intro δ hδ
    obtain ⟨B, _, hB⟩ := exists_uniform_sublinear_recentered_budget ε hδ
    exact ⟨B, hB⟩

end GaloisForLFunctions.ArithmeticDefectRigidity
