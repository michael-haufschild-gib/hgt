import GaloisForLFunctions.ArithmeticDefectRigidity.TheOriginTraceControlsMovingSuccessors
import GaloisForLFunctions.RHTower.SqrtCarrierCertificate
import GaloisForLFunctions.HTGeometry.UniformSmallBudgetsVanishAfterNormalization

/-!
# Source power savings control moving successors

The arithmetic Vinogradov–Korobov saving makes the centered prefix little-oh
of its trivial power scale. A capped head estimate and a summable power tail
give uniform little-oh translation energy. Consequently larger moving shifts
remain invisible after division by an escaping receiver's energy.
-/

noncomputable section
set_option autoImplicit false

open Finset Filter Topology RHTower RHTower.Sieve
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
open GaloisForLFunctions.ArithmeticCompensationTheory

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- The arithmetic saving makes the actual prefix little-oh of its trivial power scale. -/
theorem receiver_div_sublinear_power_tendsto_zero (ε : SubcriticalDamping) :
    Tendsto (fun n : ℕ => pmPowerDampedCenteredDivisorPrefix ε n /
      (n : ℝ) ^ (1 - (ε : ℝ))) atTop (𝓝 0) := by
  have hg : Tendsto (fun x : ℝ => vkKappa * vkScale x / 240) atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [eventually_vk_conditions (δ := 1) zero_lt_one (240 * b)] with x hx
    have h := hx.2.2.1
    rw [log_vkHeight] at h
    linarith only [h]
  have hs : Tendsto (fun n : ℕ => Real.exp (-(vkKappa * vkScale n / 240)))
      atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
      (hg.comp (tendsto_natCast_atTop_atTop (R := ℝ))))
  obtain ⟨K, hK, N, hbound⟩ := exists_abs_weightCenteredPrefix_pmPowerDamped_le_vk_all_pos
  have hlim := hs.const_mul (K / (ε : ℝ))
  simp only [mul_zero] at hlim
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  refine squeeze_zero' (Eventually.of_forall fun n => abs_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop N, eventually_ge_atTop 1] with n hn hn1
  have hp : 0 < (n : ℝ) ^ (1 - (ε : ℝ)) := Real.rpow_pos_of_pos (by positivity) _
  have h := hbound ε ε.property.1 ε.property.2.le n hn
  have heq : TransHorizonIncidenceMechanics.weightCenteredPrefix
      (pmPowerDampedRealWeight ε) (TransHorizonIncidenceMechanics.dampedDensity ε) n =
      pmPowerDampedCenteredDivisorPrefix ε n := by
    rw [TransHorizonIncidenceMechanics.weightCenteredPrefix,
      pmPowerDampedCenteredDivisorPrefix_eq]
    rfl
  rw [heq] at h
  change |pmPowerDampedCenteredDivisorPrefix ε n / (n : ℝ) ^ (1 - (ε : ℝ))| ≤ _
  rw [abs_div, abs_of_pos hp]
  apply (div_le_iff₀ hp).mpr
  simpa only [mul_assoc, mul_comm, mul_left_comm] using h

end GaloisForLFunctions.ArithmeticDefectRigidity

open Finset Filter Topology RHTower
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

namespace GaloisForLFunctions.ArithmeticDefectRigidity

private theorem finite_power_tail_le {a : ℝ} (ha : a < 1) {k : ℕ} (hk : 1 ≤ k) (T : ℕ) :
    (∑ n ∈ Icc (k + 1) T, (n : ℝ) ^ (a - 2)) ≤
      (k : ℝ) ^ (a - 1) / (1 - a) := by
  have heq : (∑ n ∈ Icc (k + 1) T, (n : ℝ) ^ (a - 2)) =
      ∑ i ∈ range (T - k), ((i + (k + 1) : ℕ) : ℝ) ^ (a - 2) := by
    refine sum_bij (fun n _ => n - (k + 1)) ?_ ?_ ?_ ?_
    · intro n hn
      have h := mem_Icc.mp hn
      simp only [mem_range]
      omega
    · intro n hn m hm hnm
      have h1 := mem_Icc.mp hn
      have h2 := mem_Icc.mp hm
      omega
    · intro i hi
      have h := mem_range.mp hi
      refine ⟨i + (k + 1), ?_, by omega⟩
      simp only [mem_Icc]
      omega
    · intro n hn
      rw [Nat.sub_add_cancel (mem_Icc.mp hn).1]
  rw [heq]
  have h := sum_range_add_rpow_neg_le (c := 2 - a) (by linarith only [ha]) hk (T - k)
  simpa only [show -(2 - a) = a - 2 by ring,
    show 1 - (2 - a) = a - 1 by ring, show (2 - a) - 1 = 1 - a by ring] using h

private theorem finite_pronic_tail_le {k : ℕ} (hk : 1 ≤ k) (T : ℕ) :
    (∑ n ∈ Icc (k + 1) T, 1 / ((n : ℝ) * ((n : ℝ) + 1))) ≤ 1 / (k : ℝ) := by
  by_cases h : k ≤ T
  · rw [sum_Icc_pronic_tail_mass (by omega : 1 ≤ k + 1) (by omega)]
    simp only [Nat.cast_add, Nat.cast_one]
    exact (sub_le_self _ (by positivity)).trans
      (one_div_le_one_div_of_le (by positivity) (by linarith))
  · rw [Icc_eq_empty (by omega), sum_empty]
    positivity

/-- A capped head and a sublinear power tail control every pronic horizon. -/
theorem pronicNorm_head_power_tail_sq_le (v : ℕ → ℝ) {a A B M : ℝ}
    (ha : a < 1) (hA : 0 ≤ A) (hB : 0 ≤ B) (hM : 0 ≤ M)
    {k : ℕ} (hk : 1 ≤ k)
    (hcap : ∀ n, |v n| ≤ (min n k : ℕ))
    (hhead : ∀ n, n ≤ k → |v n| ≤ M)
    (htail : ∀ n, k < n → |v n| ≤ A * (n : ℝ) ^ a + B) (T : ℕ) :
    pronicNorm T v ^ 2 ≤ 2 * (M + 1) + A / (1 - a) * (k : ℝ) ^ a + B := by
  have hkR : (0 : ℝ) < k := by positivity
  have hheadBound : pronicNorm (min T k) v ^ 2 ≤ 2 * (M + 1) := by
    have hrow (n : ℕ) (hn : n ∈ Icc 1 (min T k)) :
        |v n| ≤ (min n ⌈M⌉₊ : ℕ) := by
      rw [Nat.cast_min]
      refine le_min ((hcap n).trans ?_) ((hhead n ?_).trans (Nat.le_ceil M))
      · exact_mod_cast min_le_left n k
      · exact (mem_Icc.mp hn).2.trans (min_le_right T k)
    calc
      _ ≤ pronicNorm (min T k) (fun n => ((min n ⌈M⌉₊ : ℕ) : ℝ)) ^ 2 := by
        rw [pronicNorm_sq, pronicNorm_sq]
        apply sum_le_sum
        intro n hn
        apply div_le_div_of_nonneg_right _ (by positivity)
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hrow n hn) 2
      _ ≤ 2 * (⌈M⌉₊ : ℝ) := pronicNorm_cappedLinear_sq_le _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (Nat.ceil_lt_add_one hM).le (by norm_num)
  have htailCell (n : ℕ) (hn : n ∈ Icc (k + 1) T) :
      v n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
        (A * k) * (n : ℝ) ^ (a - 2) +
          (B * k) * (1 / ((n : ℝ) * ((n : ℝ) + 1))) := by
    have hkn : k < n := by have := (mem_Icc.mp hn).1; omega
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hvk : |v n| ≤ (k : ℝ) := by
      exact (hcap n).trans (by exact_mod_cast min_le_right n k)
    have hvn := htail n hkn
    have hsq : v n ^ 2 ≤ (k : ℝ) * (A * (n : ℝ) ^ a + B) := by
      simpa only [← pow_two, sq_abs] using
        mul_le_mul hvk hvn (abs_nonneg _) hkR.le
    have hp : (n : ℝ) ^ a = (n : ℝ) ^ (a - 2) * (n : ℝ) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hnR]
      congr 1
      norm_num
    apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) * ((n : ℝ) + 1))).mpr
    have hd : (n : ℝ) ^ 2 ≤ (n : ℝ) * ((n : ℝ) + 1) := by
      nlinarith only [hnR.le]
    have heq : ((A * k) * (n : ℝ) ^ (a - 2) +
        (B * k) * (1 / ((n : ℝ) * ((n : ℝ) + 1)))) *
          ((n : ℝ) * ((n : ℝ) + 1)) =
        (A * k) * (n : ℝ) ^ (a - 2) * ((n : ℝ) * ((n : ℝ) + 1)) + B * k := by
      field_simp
    rw [heq]
    calc
      _ ≤ (k : ℝ) * (A * (n : ℝ) ^ a + B) := hsq
      _ = (A * k) * (n : ℝ) ^ (a - 2) * (n : ℝ) ^ 2 + B * k := by rw [hp]; ring
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hd (by positivity)) le_rfl
  have htailBound : (∑ n ∈ Icc (k + 1) T,
      v n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) ≤
        A / (1 - a) * (k : ℝ) ^ a + B := by
    calc
      _ ≤ ∑ n ∈ Icc (k + 1) T,
          ((A * k) * (n : ℝ) ^ (a - 2) +
            (B * k) * (1 / ((n : ℝ) * ((n : ℝ) + 1)))) := sum_le_sum htailCell
      _ = (A * k) * (∑ n ∈ Icc (k + 1) T, (n : ℝ) ^ (a - 2)) +
          (B * k) * (∑ n ∈ Icc (k + 1) T, 1 / ((n : ℝ) * ((n : ℝ) + 1))) := by
        rw [sum_add_distrib, ← mul_sum, ← mul_sum]
      _ ≤ (A * k) * ((k : ℝ) ^ (a - 1) / (1 - a)) +
          (B * k) * (1 / (k : ℝ)) :=
        add_le_add (mul_le_mul_of_nonneg_left (finite_power_tail_le ha hk T) (by positivity))
          (mul_le_mul_of_nonneg_left (finite_pronic_tail_le hk T) (by positivity))
      _ = _ := by
        have hp : (k : ℝ) ^ a = (k : ℝ) ^ (a - 1) * k := by
          rw [← Real.rpow_add_one hkR.ne']
          congr 1
          ring
        rw [hp]
        field_simp
  have hsplit : Icc 1 T = Icc 1 (min T k) ∪ Icc (k + 1) T := by
    ext n
    simp only [mem_Icc, mem_union, le_min_iff]
    omega
  have hdisj : Disjoint (Icc 1 (min T k)) (Icc (k + 1) T) := by
    rw [disjoint_left]
    intro n hn hm
    have h1 := (mem_Icc.mp hn).2.trans (min_le_right T k)
    have h2 := (mem_Icc.mp hm).1
    omega
  rw [pronicNorm_sq, hsplit, sum_union hdisj]
  rw [pronicNorm_sq] at hheadBound
  exact (add_le_add hheadBound htailBound).trans_eq (by ring)

end GaloisForLFunctions.ArithmeticDefectRigidity

open Finset Filter Topology RHTower
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
open GaloisForLFunctions.ArithmeticCompensationTheory

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- The little-oh source estimate gives an arbitrarily small power coefficient with a fixed remainder. -/
theorem exists_receiver_small_power_envelope (ε : SubcriticalDamping) {b : ℝ} (hb : 0 < b) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ,
      |pmPowerDampedCenteredDivisorPrefix ε n| ≤ b * (n : ℝ) ^ (1 - (ε : ℝ)) + B := by
  have h := (receiver_div_sublinear_power_tendsto_zero ε).abs
  rw [abs_zero] at h
  obtain ⟨N₀, hN⟩ := eventually_atTop.mp (h.eventually (gt_mem_nhds hb))
  let N := max 1 N₀
  let B := ∑ n ∈ range N, |pmPowerDampedCenteredDivisorPrefix ε n|
  have hB : 0 ≤ B := sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨B, hB, fun n => ?_⟩
  by_cases hn : N ≤ n
  · have hn1 : 1 ≤ n := (le_max_left 1 N₀).trans hn
    have hp : 0 < (n : ℝ) ^ (1 - (ε : ℝ)) := Real.rpow_pos_of_pos (by positivity) _
    have hbound := (hN n ((le_max_right 1 N₀).trans hn)).le
    rw [abs_div, abs_of_pos hp] at hbound
    exact ((div_le_iff₀ hp).mp hbound).trans (le_add_of_nonneg_right hB)
  · have hsingle : |pmPowerDampedCenteredDivisorPrefix ε n| ≤ B :=
      single_le_sum (fun j _ => abs_nonneg (pmPowerDampedCenteredDivisorPrefix ε j))
        (mem_range.mpr (lt_of_not_ge hn))
    exact hsingle.trans (le_add_of_nonneg_left (by positivity))

/-- The additive defect inherits a power envelope from the source prefix. -/
theorem receiverAdditiveDefect_le_power_envelope (ε : SubcriticalDamping)
    {b B : ℝ} (hb : 0 ≤ b)
    (hA : ∀ n : ℕ, |pmPowerDampedCenteredDivisorPrefix ε n| ≤
      b * (n : ℝ) ^ (1 - (ε : ℝ)) + B)
    (n k m : ℕ) (hnm : n ≤ m) (hkm : k ≤ m) :
    |receiverAdditiveDefect ε n k| ≤ 4 * b * (m : ℝ) ^ (1 - (ε : ℝ)) + 3 * B := by
  have ha : 0 ≤ 1 - (ε : ℝ) := by linarith only [ε.property.2]
  have ha1 : 1 - (ε : ℝ) ≤ 1 := by linarith only [ε.property.1]
  have htwo : (2 : ℝ) ^ (1 - (ε : ℝ)) ≤ 2 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ha1
  have hpow (x : ℕ) (hxm : x ≤ m) :
      (x : ℝ) ^ (1 - (ε : ℝ)) ≤ (m : ℝ) ^ (1 - (ε : ℝ)) :=
    Real.rpow_le_rpow (Nat.cast_nonneg x) (by exact_mod_cast hxm) ha
  have hsum : ((n + k : ℕ) : ℝ) ^ (1 - (ε : ℝ)) ≤
      2 * (m : ℝ) ^ (1 - (ε : ℝ)) := by
    calc
      _ ≤ (2 * (m : ℝ)) ^ (1 - (ε : ℝ)) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast (show n + k ≤ 2 * m by omega)) ha
      _ = (2 : ℝ) ^ (1 - (ε : ℝ)) * (m : ℝ) ^ (1 - (ε : ℝ)) :=
        Real.mul_rpow (by norm_num) (Nat.cast_nonneg m)
      _ ≤ _ := mul_le_mul_of_nonneg_right htwo (by positivity)
  unfold receiverAdditiveDefect
  calc
    _ ≤ |pmPowerDampedCenteredDivisorPrefix ε (n + k) - pmPowerDampedCenteredDivisorPrefix ε n| +
        |pmPowerDampedCenteredDivisorPrefix ε k| := abs_sub _ _
    _ ≤ |pmPowerDampedCenteredDivisorPrefix ε (n + k)| +
        |pmPowerDampedCenteredDivisorPrefix ε n| + |pmPowerDampedCenteredDivisorPrefix ε k| :=
      add_le_add (abs_sub _ _) le_rfl
    _ ≤ (b * ((n + k : ℕ) : ℝ) ^ (1 - (ε : ℝ)) + B) +
        (b * (n : ℝ) ^ (1 - (ε : ℝ)) + B) +
        (b * (k : ℝ) ^ (1 - (ε : ℝ)) + B) :=
      add_le_add (add_le_add (hA (n + k)) (hA n)) (hA k)
    _ ≤ _ := by
      nlinarith only [mul_le_mul_of_nonneg_left hsum hb,
        mul_le_mul_of_nonneg_left (hpow n hnm) hb,
        mul_le_mul_of_nonneg_left (hpow k hkm) hb]

/-- Recentered source translations have uniformly little-oh energy at the source power scale. -/
theorem exists_uniform_subpower_recentered_budget (ε : SubcriticalDamping)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k T : ℕ,
      pronicNorm T (fun n => receiverAdditiveDefect ε n k) ^ 2 ≤
        δ * (k : ℝ) ^ (1 - (ε : ℝ)) + C := by
  have hε : 0 < (ε : ℝ) := ε.property.1
  have hcoef : 0 < 8 + 4 / (ε : ℝ) := by positivity
  let b := δ / (8 + 4 / (ε : ℝ))
  have hb : 0 < b := div_pos hδ hcoef
  obtain ⟨B, hB, hA⟩ := exists_receiver_small_power_envelope ε hb
  refine ⟨9 * B + 2, by positivity, fun k T => ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have hz : (fun n => receiverAdditiveDefect ε n 0) = fun _ => 0 := by
      funext n
      simp only [receiverAdditiveDefect, Nat.add_zero,
        ArithmeticContinuationAndCriticalEnergy.pmPowerDampedCenteredDivisorPrefix_zero,
        sub_self]
    rw [hz, pronicNorm_sq]
    simp only [zero_pow two_ne_zero, zero_div, sum_const_zero]
    positivity
  · have h := pronicNorm_head_power_tail_sq_le
      (fun n => receiverAdditiveDefect ε n k) (a := 1 - (ε : ℝ))
      (A := 4 * b) (B := 3 * B) (M := 4 * b * (k : ℝ) ^ (1 - (ε : ℝ)) + 3 * B)
      (by linarith only [ε.property.1]) (by positivity) (by positivity) (by positivity)
      (show 1 ≤ k by omega) (fun n => abs_receiverAdditiveDefect_le_min ε n k)
      (fun n hn => receiverAdditiveDefect_le_power_envelope ε hb.le hA n k k hn le_rfl)
      (fun n hn => receiverAdditiveDefect_le_power_envelope ε hb.le hA n k n le_rfl hn.le) T
    have hc : (8 + 4 / (ε : ℝ)) * b = δ := by
      dsimp only [b]
      field_simp
    refine h.trans_eq ?_
    rw [show 1 - (1 - (ε : ℝ)) = (ε : ℝ) by ring]
    calc
      _ = ((8 + 4 / (ε : ℝ)) * b) * (k : ℝ) ^ (1 - (ε : ℝ)) + (9 * B + 2) := by ring
      _ = _ := by rw [hc]

/-- Bounded source-power-relative translations still disappear on escape after recentering. -/
theorem admits_or_sourcePower_recentered_successors_disappear (ε : SubcriticalDamping) :
    Admits dampedMobiusEnergy ε ∨ ∀ k : ℕ → ℕ,
      (∃ C : ℝ, ∀ᶠ T : ℕ in atTop,
        (k T : ℝ) ^ (1 - (ε : ℝ)) / dampedMobiusEnergy ε T ≤ C) →
      Tendsto (fun T => pronicNorm T (fun n => receiverAdditiveDefect ε n (k T)) ^ 2 /
        dampedMobiusEnergy ε T) atTop (𝓝 0) := by
  rcases admits_or_tendsto_atTop (ε : ℝ) with h | hE
  · exact Or.inl h
  · refine Or.inr fun k hk => HTGeometry.normalized_cost_tendsto_zero_of_uniform_small_budget
      (fun k T => pronicNorm T (fun n => receiverAdditiveDefect ε n k) ^ 2)
      (fun k => (k : ℝ) ^ (1 - (ε : ℝ))) (dampedMobiusEnergy ε)
      (fun k T => sq_nonneg _) ?_ hE k hk
    intro δ hδ
    obtain ⟨B, _, hB⟩ := exists_uniform_subpower_recentered_budget ε hδ
    exact ⟨B, hB⟩

end GaloisForLFunctions.ArithmeticDefectRigidity

open Filter Topology RHTower
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
open GaloisForLFunctions.ArithmeticCompensationTheory

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- The raw translation envelope at the square of the source power scale. -/
def successorPowerRatioBudget (ε : SubcriticalDamping) (k : ℕ) : ℝ :=
  (4 * (k : ℝ) + 2 * pmPowerDampedCenteredDivisorPrefix ε k ^ 2) /
    (k : ℝ) ^ (2 * (1 - (ε : ℝ)))

theorem successorPowerRatioBudget_tendsto_zero (ε : SubcriticalDamping) :
    Tendsto (successorPowerRatioBudget ε) atTop (𝓝 0) := by
  have hexp : 0 < 2 * (1 - (ε : ℝ)) - 1 := by linarith only [ε.property.2]
  have hfirst := ((tendsto_rpow_neg_atTop hexp).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul 4
  have hsecond := ((receiver_div_sublinear_power_tendsto_zero ε).pow 2).const_mul 2
  have h := hfirst.add hsecond
  simp only [zero_pow two_ne_zero, mul_zero, zero_add] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hkR : (0 : ℝ) < k := by positivity
  have hp2 : ((k : ℝ) ^ (1 - (ε : ℝ))) ^ 2 =
      (k : ℝ) ^ (2 * (1 - (ε : ℝ))) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hkR.le]
    congr 1
    norm_num
    ring
  have hrecip : (k : ℝ) / (k : ℝ) ^ (2 * (1 - (ε : ℝ))) =
      (k : ℝ) ^ (-(2 * (1 - (ε : ℝ)) - 1)) := by
    have hp : (k : ℝ) ^ (2 * (1 - (ε : ℝ))) =
        (k : ℝ) ^ (2 * (1 - (ε : ℝ)) - 1) * k := by
      rw [← Real.rpow_add_one hkR.ne']
      congr 1
      ring
    rw [hp, Real.rpow_neg hkR.le]
    field_simp
  change 4 * (k : ℝ) ^ (-(2 * (1 - (ε : ℝ)) - 1)) +
    2 * (pmPowerDampedCenteredDivisorPrefix ε k / (k : ℝ) ^ (1 - (ε : ℝ))) ^ 2 = _
  rw [← hrecip, div_pow, hp2]
  unfold successorPowerRatioBudget
  ring

/-- The raw displacement has arbitrarily small source-power coefficient and a uniform remainder. -/
theorem exists_uniform_subpower_successor_budget (ε : SubcriticalDamping)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k T : ℕ,
      successorDisplacementEnergy ε k T ≤
        δ * (k : ℝ) ^ (2 * (1 - (ε : ℝ))) + B := by
  obtain ⟨K₀, hK⟩ := eventually_atTop.mp
    ((successorPowerRatioBudget_tendsto_zero ε).eventually (gt_mem_nhds hδ))
  let K := max 1 K₀
  refine ⟨(K : ℝ) ^ 2, sq_nonneg _, fun k T => ?_⟩
  by_cases hk : K ≤ k
  · have hk1 : 1 ≤ k := (le_max_left 1 K₀).trans hk
    have hp : 0 < (k : ℝ) ^ (2 * (1 - (ε : ℝ))) := Real.rpow_pos_of_pos (by positivity) _
    have h := (hK k ((le_max_right 1 K₀).trans hk)).le
    have hprod := mul_le_mul_of_nonneg_left h hp.le
    have heq : (k : ℝ) ^ (2 * (1 - (ε : ℝ))) * successorPowerRatioBudget ε k =
        4 * (k : ℝ) + 2 * pmPowerDampedCenteredDivisorPrefix ε k ^ 2 := by
      unfold successorPowerRatioBudget
      field_simp
    rw [heq] at hprod
    exact (successorDisplacementEnergy_le_origin_trace ε k T).trans
      (hprod.trans (by nlinarith only [sq_nonneg (K : ℝ)]))
  · have hkR : (k : ℝ) ≤ K := by exact_mod_cast le_of_lt (lt_of_not_ge hk)
    have hsq := pow_le_pow_left₀ (Nat.cast_nonneg k) hkR 2
    exact (successorDisplacementEnergy_le ε k T).trans
      (hsq.trans (le_add_of_nonneg_left (by positivity)))

/-- Even bounded translation length at the square source-power scale vanishes on escape. -/
theorem admits_or_sourcePower_successors_disappear (ε : SubcriticalDamping) :
    Admits dampedMobiusEnergy ε ∨ ∀ k : ℕ → ℕ,
      (∃ C : ℝ, ∀ᶠ T : ℕ in atTop,
        (k T : ℝ) ^ (2 * (1 - (ε : ℝ))) / dampedMobiusEnergy ε T ≤ C) →
      Tendsto (fun T => successorDisplacementEnergy ε (k T) T /
        dampedMobiusEnergy ε T) atTop (𝓝 0) := by
  rcases admits_or_tendsto_atTop (ε : ℝ) with h | hE
  · exact Or.inl h
  · refine Or.inr fun k hk => HTGeometry.normalized_cost_tendsto_zero_of_uniform_small_budget
      (successorDisplacementEnergy ε) (fun k => (k : ℝ) ^ (2 * (1 - (ε : ℝ))))
      (dampedMobiusEnergy ε) (fun k T => sq_nonneg _) ?_ hE k hk
    intro δ hδ
    obtain ⟨B, _, hB⟩ := exists_uniform_subpower_successor_budget ε hδ
    exact ⟨B, hB⟩

end GaloisForLFunctions.ArithmeticDefectRigidity
