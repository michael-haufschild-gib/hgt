import GaloisForLFunctions.RHTower.MoebiusFloorSummatory
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-!
# Completeness of normalized residue profiles

Truncated Möbius inversion has a uniform linear majorant. This permits inversion
against every absolutely summable row, without any cancellation hypothesis.
Dual separation then proves density of the residue modes in the uniform `c₀` norm.
This does not assert density in the critical pronic receiver norm.
-/

open Finset Filter Topology
open ArithmeticFunction (moebius abs_moebius_le_one)
open scoped ZeroAtInfty

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

private def rmMoebiusFloor (K m : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 K, ((moebius k : ℤ) : ℝ) * ((m / k : ℕ) : ℝ)

private theorem rmMoebiusFloor_eq (K m : ℕ) (hmK : m ≤ K) :
    rmMoebiusFloor K m = if m = 0 then 0 else 1 := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [rmMoebiusFloor]
  rw [if_neg hm]
  have he : rmMoebiusFloor m m = rmMoebiusFloor K m := by
    apply sum_subset (Icc_subset_Icc_right hmK)
    intro k hk hkm
    have hmk : m < k := by
      have hk1 := (mem_Icc.mp hk).1
      simp only [mem_Icc, hk1, true_and, not_le] at hkm
      exact hkm
    simp only [Nat.div_eq_of_lt hmk, Nat.cast_zero, mul_zero]
  rw [← he]
  exact RHTower.moebius_floor_summatory m (by omega)

private theorem rmMoebiusFloor_bound (K m : ℕ) :
    |rmMoebiusFloor K m| ≤ 2 * (m : ℝ) := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [rmMoebiusFloor]
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  by_cases hmk : m ≤ K
  · rw [rmMoebiusFloor_eq K m hmk, if_neg hm, abs_one]
    linarith
  rcases eq_or_ne K 0 with rfl | hK
  · simp [rmMoebiusFloor]
  have hH := RHTower.abs_sum_moebius_div_le_one K (by omega)
  have hsplit : rmMoebiusFloor K m =
      (m : ℝ) * (∑ k ∈ Icc 1 K, ((moebius k : ℤ) : ℝ) / k) -
        ∑ k ∈ Icc 1 K, ((moebius k : ℤ) : ℝ) * ((m % k : ℕ) : ℝ) / k := by
    rw [mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro k hk
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by
      have := (mem_Icc.mp hk).1
      omega)
    have he : (k : ℝ) * (m / k : ℕ) + (m % k : ℕ) = m := by
      exact_mod_cast Nat.div_add_mod m k
    field_simp
    nlinarith only [congrArg (fun x : ℝ => ((moebius k : ℤ) : ℝ) * x) he]
  have hR : |∑ k ∈ Icc 1 K,
      ((moebius k : ℤ) : ℝ) * ((m % k : ℕ) : ℝ) / k| ≤ K := by
    calc
      _ ≤ ∑ k ∈ Icc 1 K,
          |((moebius k : ℤ) : ℝ) * ((m % k : ℕ) : ℝ) / k| :=
        abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k ∈ Icc 1 K, (1 : ℝ) := by
        apply sum_le_sum
        intro k hk
        have hkpos : 0 < k := (mem_Icc.mp hk).1
        have hk' : (0 : ℝ) < k := by exact_mod_cast hkpos
        have hmu : |((moebius k : ℤ) : ℝ)| ≤ 1 := by
          rw [← Int.cast_abs]
          exact_mod_cast abs_moebius_le_one (n := k)
        rw [abs_div, abs_mul,
          abs_of_nonneg (a := ((m % k : ℕ) : ℝ)) (Nat.cast_nonneg _), abs_of_pos hk']
        apply (div_le_one hk').mpr
        calc
          _ ≤ 1 * ((m % k : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_right hmu (Nat.cast_nonneg _)
          _ ≤ k := by simpa only [one_mul] using
            (show ((m % k : ℕ) : ℝ) ≤ k by exact_mod_cast (Nat.mod_lt m hkpos).le)
      _ = K := by simp
  rw [hsplit]
  calc
    _ ≤ |(m : ℝ) * (∑ k ∈ Icc 1 K, ((moebius k : ℤ) : ℝ) / k)| +
        |∑ k ∈ Icc 1 K, ((moebius k : ℤ) : ℝ) * ((m % k : ℕ) : ℝ) / k| :=
      abs_sub _ _
    _ ≤ (m : ℝ) * 1 + K := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg m)]
      exact add_le_add (mul_le_mul_of_nonneg_left hH (Nat.cast_nonneg m)) hR
    _ ≤ 2 * (m : ℝ) := by
      have : (K : ℝ) ≤ m := by exact_mod_cast (show K ≤ m by omega)
      linarith

/-- Floor profiles with their constant limits removed. -/
def normalizedResidueProfile (d n : ℕ) : ℝ :=
  (((n + 1) / d : ℕ) : ℝ) / (n + 1 : ℕ) - 1 / (d : ℝ)

@[simp] theorem normalizedResidueProfile_zero (n : ℕ) : normalizedResidueProfile 0 n = 0 := by
  simp [normalizedResidueProfile]

@[simp] theorem normalizedResidueProfile_one (n : ℕ) : normalizedResidueProfile 1 n = 0 := by
  unfold normalizedResidueProfile
  simp only [Nat.div_one, Nat.cast_one, div_one]
  rw [div_self (by positivity), sub_self]

private theorem rmProfile_mod {d : ℕ} (hd : 0 < d) (n : ℕ) :
    normalizedResidueProfile d n =
      -(((n + 1) % d : ℕ) : ℝ) / ((d : ℝ) * (n + 1 : ℕ)) := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hn0 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have he : (((n + 1) % d : ℕ) : ℝ) +
      (d : ℝ) * ((n + 1) / d : ℕ) = (n + 1 : ℕ) := by
    exact_mod_cast Nat.mod_add_div (n + 1) d
  unfold normalizedResidueProfile
  field_simp
  nlinarith

private theorem rmProfile_bound (d n : ℕ) :
    |normalizedResidueProfile d n| ≤ 1 / (n + 1 : ℕ) := by
  rcases eq_or_ne d 0 with rfl | hd
  · simp [normalizedResidueProfile]
    positivity
  have hd' : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
  have hn' : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  rw [rmProfile_mod (Nat.pos_of_ne_zero hd), abs_div, abs_neg,
    abs_of_nonneg (Nat.cast_nonneg _), abs_of_pos (mul_pos hd' hn')]
  calc
    _ ≤ (d : ℝ) / ((d : ℝ) * (n + 1 : ℕ)) :=
      div_le_div_of_nonneg_right
        (by exact_mod_cast (Nat.mod_lt (n + 1) (Nat.pos_of_ne_zero hd)).le)
        (mul_pos hd' hn').le
    _ = 1 / (n + 1 : ℕ) := by field_simp

/-- The normalized residue profiles are genuine vanishing-at-infinity observables. -/
def normalizedResidueMode (d : ℕ) : C₀(ℕ, ℝ) :=
  ⟨⟨normalizedResidueProfile d, continuous_of_discreteTopology⟩, by
    rw [cocompact_eq_cofinite, Nat.cofinite_eq_atTop]
    apply squeeze_zero_norm (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [Real.norm_eq_abs, Nat.cast_add, Nat.cast_one, Nat.cast_succ] using
      rmProfile_bound d n⟩

@[simp] theorem normalizedResidueMode_apply (d n : ℕ) :
    normalizedResidueMode d n = normalizedResidueProfile d n := rfl

@[simp] theorem normalizedResidueMode_zero : normalizedResidueMode 0 = 0 := by
  ext n
  simp only [normalizedResidueMode_apply, normalizedResidueProfile_zero,
    ZeroAtInftyContinuousMap.zero_apply]

@[simp] theorem normalizedResidueMode_one : normalizedResidueMode 1 = 0 := by
  ext n
  simp only [normalizedResidueMode_apply, normalizedResidueProfile_one,
    ZeroAtInftyContinuousMap.zero_apply]

private def rmFloorProfile (d n : ℕ) : ℝ :=
  (((n + 1) / d : ℕ) : ℝ) / (n + 1 : ℕ)

private theorem rmFloor_nonneg (d n : ℕ) : 0 ≤ rmFloorProfile d n := by
  unfold rmFloorProfile
  positivity

private theorem rmFloor_le_one (d n : ℕ) : rmFloorProfile d n ≤ 1 := by
  apply (div_le_one (by positivity : (0 : ℝ) < (n + 1 : ℕ))).mpr
  exact_mod_cast Nat.div_le_self (n + 1) d

private theorem rmScaledFloor_le_one (d n : ℕ) :
    (d : ℝ) * rmFloorProfile d n ≤ 1 := by
  unfold rmFloorProfile
  rw [← mul_div_assoc]
  apply (div_le_one (by positivity : (0 : ℝ) < (n + 1 : ℕ))).mpr
  exact_mod_cast Nat.mul_div_le (n + 1) d

private theorem rmFloor_summable {a : ℕ → ℝ} (ha : Summable a) (d : ℕ) :
    Summable (fun n => a n * rmFloorProfile d n) := by
  apply ha.abs.of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (a := rmFloorProfile d n) (rmFloor_nonneg d n)]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (rmFloor_le_one d n) (abs_nonneg (a n))

private theorem rmPairing_floor {a : ℕ → ℝ} (ha : Summable a)
    (hz : ∀ d, (∑' n, a n * normalizedResidueProfile d n) = 0) (d : ℕ) :
    (∑' n, a n * rmFloorProfile d n) = (∑' n, a n) / d := by
  have h := hz d
  change (∑' n, a n * (rmFloorProfile d n - 1 / (d : ℝ))) = 0 at h
  simp_rw [mul_sub] at h
  rw [(rmFloor_summable ha d).tsum_sub (ha.mul_right (1 / (d : ℝ))),
    ha.tsum_mul_right] at h
  simpa only [mul_one_div] using sub_eq_zero.mp h

private theorem rmPairing_total_zero {a : ℕ → ℝ} (ha : Summable a)
    (hz : ∀ d, (∑' n, a n * normalizedResidueProfile d n) = 0) :
    (∑' n, a n) = 0 := by
  have ht : Tendsto (fun d : ℕ => ∑' n, a n * ((d : ℝ) * rmFloorProfile d n))
      atTop (𝓝 0) := by
    have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (f := fun (d n : ℕ) =>
      a n * ((d : ℝ) * rmFloorProfile d n)) (g := fun _ => (0 : ℝ)) ha.abs
    apply (by simpa only [tsum_zero] using h)
    · intro n
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop (n + 2)] with d hd
      simp only [rmFloorProfile, Nat.div_eq_of_lt (show n + 1 < d by omega),
        Nat.cast_zero, zero_div, mul_zero]
    · apply Eventually.of_forall
      intro d n
      rw [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (a := (d : ℝ) * rmFloorProfile d n)
          (mul_nonneg (Nat.cast_nonneg _) (rmFloor_nonneg d n))]
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (rmScaledFloor_le_one d n) (abs_nonneg (a n))
  have he : (fun d : ℕ => ∑' n, a n * ((d : ℝ) * rmFloorProfile d n)) =ᶠ[atTop]
      fun _ => ∑' n, a n := by
    filter_upwards [eventually_ge_atTop 1] with d hd
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
    calc
      _ = ∑' n, (d : ℝ) * (a n * rmFloorProfile d n) := by
        apply tsum_congr
        intro n
        ring
      _ = (d : ℝ) * ((∑' n, a n) / d) := by
        rw [(rmFloor_summable ha d).tsum_mul_left, rmPairing_floor ha hz]
      _ = ∑' n, a n := by field_simp
  exact (tendsto_nhds_unique (ht.congr' he) tendsto_const_nhds).symm

private def rmTail (a : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑' n, if d ≤ n + 1 then a n / (n + 1 : ℕ) else 0

private theorem rmTail_summable {a : ℕ → ℝ} (ha : Summable a) (d : ℕ) :
    Summable (fun n => if d ≤ n + 1 then a n / (n + 1 : ℕ) else 0) := by
  apply ha.abs.of_norm_bounded
  intro n
  by_cases hdn : d ≤ n + 1
  · rw [if_pos hdn, Real.norm_eq_abs, abs_div,
      abs_of_pos (a := ((n + 1 : ℕ) : ℝ)) (by positivity)]
    exact div_le_self (abs_nonneg _) (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
  · simp only [if_neg hdn, norm_zero]
    exact abs_nonneg _

private theorem rmFloor_inversion {a : ℕ → ℝ} (ha : Summable a)
    (hz : ∀ d, (∑' n, a n * rmFloorProfile d n) = 0) {d : ℕ} (hd : 0 < d) :
    rmTail a d = 0 := by
  have hzero (K : ℕ) :
      (∑' n, a n / (n + 1 : ℕ) * rmMoebiusFloor K ((n + 1) / d)) = 0 := by
    calc
      _ = ∑' n, ∑ k ∈ Icc 1 K,
          ((moebius k : ℤ) : ℝ) * (a n * rmFloorProfile (d * k) n) := by
        apply tsum_congr
        intro n
        unfold rmMoebiusFloor
        rw [mul_sum]
        apply sum_congr rfl
        intro k _
        rw [Nat.div_div_eq_div_mul]
        unfold rmFloorProfile
        ring
      _ = ∑ k ∈ Icc 1 K, ((moebius k : ℤ) : ℝ) *
          (∑' n, a n * rmFloorProfile (d * k) n) := by
        rw [Summable.tsum_finsetSum (fun k _ =>
          (rmFloor_summable ha (d * k)).mul_left (((moebius k : ℤ) : ℝ)))]
        apply sum_congr rfl
        intro k _
        exact (rmFloor_summable ha (d * k)).tsum_mul_left _
      _ = 0 := by simp only [hz, mul_zero, sum_const_zero]
  have ht : Tendsto (fun K : ℕ =>
      ∑' n, a n / (n + 1 : ℕ) * rmMoebiusFloor K ((n + 1) / d))
      atTop (𝓝 (rmTail a d)) := by
    apply tendsto_tsum_of_dominated_convergence (ha.abs.mul_left 2)
    · intro n
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop ((n + 1) / d)] with K hK
      rw [rmMoebiusFloor_eq K _ hK]
      by_cases hdn : d ≤ n + 1
      · rw [if_pos hdn, if_neg (Nat.div_pos hdn hd).ne', mul_one]
      · rw [if_neg hdn, Nat.div_eq_of_lt (by omega : n + 1 < d), if_pos rfl,
          mul_zero]
    · apply Eventually.of_forall
      intro K n
      rw [Real.norm_eq_abs, abs_mul, abs_div,
        abs_of_pos (by positivity : (0 : ℝ) < (n + 1 : ℕ))]
      calc
        _ ≤ |a n| / (n + 1 : ℕ) * (2 * (((n + 1) / d : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left (rmMoebiusFloor_bound K _)
            (div_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
        _ ≤ |a n| / (n + 1 : ℕ) * (2 * (n + 1 : ℕ)) := by
          gcongr
          exact_mod_cast Nat.div_le_self (n + 1) d
        _ = 2 * |a n| := by field_simp
  have hc := ht.congr (fun K => hzero K)
  exact tendsto_nhds_unique hc tendsto_const_nhds

private theorem rmPairing_injective {a : ℕ → ℝ} (ha : Summable a)
    (hz : ∀ d, (∑' n, a n * normalizedResidueProfile d n) = 0) : ∀ n, a n = 0 := by
  have htotal := rmPairing_total_zero ha hz
  have hfloor (d : ℕ) : (∑' n, a n * rmFloorProfile d n) = 0 := by
    rw [rmPairing_floor ha hz, htotal, zero_div]
  have htail (d : ℕ) (hd : 0 < d) : rmTail a d = 0 := rmFloor_inversion ha hfloor hd
  intro n
  have he : a n / (n + 1 : ℕ) = rmTail a (n + 1) - rmTail a (n + 2) := by
    calc
      _ = ∑' k, if k = n then a n / (n + 1 : ℕ) else 0 := by simp
      _ = ∑' k, ((if n + 1 ≤ k + 1 then a k / (k + 1 : ℕ) else 0) -
          (if n + 2 ≤ k + 1 then a k / (k + 1 : ℕ) else 0)) := by
        apply tsum_congr
        intro k
        by_cases hkn : k = n
        · subst k
          simp
        · by_cases hnk : n < k
          · simp only [if_neg hkn, if_pos (by omega : n + 1 ≤ k + 1),
              if_pos (by omega : n + 2 ≤ k + 1), sub_self]
          · simp only [if_neg hkn, if_neg (by omega : ¬n + 1 ≤ k + 1),
              if_neg (by omega : ¬n + 2 ≤ k + 1), sub_zero]
      _ = rmTail a (n + 1) - rmTail a (n + 2) :=
        (rmTail_summable ha (n + 1)).tsum_sub (rmTail_summable ha (n + 2))
  rw [htail _ (by omega), htail _ (by omega), sub_self] at he
  exact (div_eq_zero_iff.mp he).resolve_right (by positivity)

/-- Every absolutely summable row is determined by its normalized residue pairings. -/
theorem normalizedResidue_annihilator_iff (a : lp (fun _ : ℕ => ℝ) 1) :
    (∀ d, 2 ≤ d → (∑' n, a n * normalizedResidueProfile d n) = 0) ↔ a = 0 := by
  constructor
  · intro hz
    have hn : Summable (fun n => ‖a n‖) := by
      simpa only [ENNReal.toReal_one, Real.rpow_one] using
        (lp.memℓp a).summable (by simp : 0 < (1 : ENNReal).toReal)
    have hall : ∀ d, (∑' n, a n * normalizedResidueProfile d n) = 0 := by
      intro d
      by_cases hd : 2 ≤ d
      · exact hz d hd
      · rcases (by omega : d = 0 ∨ d = 1) with rfl | rfl <;>
          simp only [normalizedResidueProfile_zero, normalizedResidueProfile_one,
            mul_zero, tsum_zero]
    ext n
    exact rmPairing_injective hn.of_norm hall n
  · rintro rfl
    simp

private def rmBasis (n : ℕ) : C₀(ℕ, ℝ) :=
  ⟨⟨fun k => if k = n then 1 else 0, continuous_of_discreteTopology⟩, by
    rw [cocompact_eq_cofinite, Nat.cofinite_eq_atTop]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (n + 1)] with k hk
    simp only [if_neg (by omega : k ≠ n)]⟩

private def rmFinite (s : Finset ℕ) (b : ℕ → ℝ) : C₀(ℕ, ℝ) :=
  ⟨⟨fun k => if k ∈ s then b k else 0, continuous_of_discreteTopology⟩, by
    rw [cocompact_eq_cofinite]
    apply tendsto_const_nhds.congr'
    filter_upwards [s.finite_toSet.compl_mem_cofinite] with k hk
    simp only [Set.mem_compl_iff, mem_coe] at hk
    simp only [if_neg hk]⟩

private theorem rmEval_sum {ι : Type*} (s : Finset ι) (f : ι → C₀(ℕ, ℝ)) (n : ℕ) :
    (∑ i ∈ s, f i) n = ∑ i ∈ s, f i n := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert i s hi ih =>
    rw [sum_insert hi, sum_insert hi]
    change f i n + (∑ j ∈ s, f j) n = _
    rw [ih]

private theorem rmFinite_eq_sum (s : Finset ℕ) (b : ℕ → ℝ) :
    rmFinite s b = ∑ n ∈ s, b n • rmBasis n := by
  apply ZeroAtInftyContinuousMap.ext
  intro n
  rw [rmEval_sum]
  change (if n ∈ s then b n else 0) = ∑ k ∈ s, b k * (if n = k then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero, sum_ite_eq]

private theorem rmFinite_norm_le (s : Finset ℕ) (b : ℕ → ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ n ∈ s, |b n| ≤ C) : ‖rmFinite s b‖ ≤ C := by
  change ‖(rmFinite s b).toBCF‖ ≤ C
  apply (BoundedContinuousFunction.norm_le hC).mpr
  intro n
  change ‖if n ∈ s then b n else (0 : ℝ)‖ ≤ C
  by_cases hn : n ∈ s
  · simpa only [if_pos hn, Real.norm_eq_abs] using hb n hn
  · simpa only [if_neg hn, norm_zero] using hC

private theorem rmDual_summable (f : C₀(ℕ, ℝ) →L[ℝ] ℝ) :
    Summable (fun n => f (rmBasis n)) := by
  have hs : Summable (fun n => |f (rmBasis n)|) := by
    apply summable_of_sum_le (fun _ => abs_nonneg _) (c := ‖f‖)
    intro s
    let b : ℕ → ℝ := fun n => if 0 ≤ f (rmBasis n) then 1 else -1
    have hn : ‖rmFinite s b‖ ≤ 1 := by
      apply rmFinite_norm_le s b zero_le_one
      intro n _
      dsimp only [b]
      split_ifs <;> simp only [abs_one, abs_neg, le_refl]
    have he : f (rmFinite s b) = ∑ n ∈ s, |f (rmBasis n)| := by
      rw [rmFinite_eq_sum, map_sum]
      apply sum_congr rfl
      intro n _
      rw [map_smul]
      change b n * f (rmBasis n) = _
      dsimp only [b]
      by_cases hf : 0 ≤ f (rmBasis n)
      · rw [if_pos hf, one_mul, abs_of_nonneg hf]
      · rw [if_neg hf, neg_one_mul, abs_of_neg (lt_of_not_ge hf)]
    rw [← he]
    calc
      _ ≤ |f (rmFinite s b)| := le_abs_self _
      _ ≤ ‖f‖ * ‖rmFinite s b‖ := f.le_opNorm _
      _ ≤ ‖f‖ * 1 := mul_le_mul_of_nonneg_left hn (norm_nonneg f)
      _ = ‖f‖ := mul_one _
  exact hs.of_norm

private theorem rmFinite_tendsto (b : C₀(ℕ, ℝ)) :
    Tendsto (fun N => rmFinite (range N) b) atTop (𝓝 b) := by
  have hz := b.zero_at_infty'
  rw [cocompact_eq_cofinite, Nat.cofinite_eq_atTop] at hz
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (Metric.tendsto_nhds.mp hz (ε / 2) (half_pos hε))
  filter_upwards [eventually_ge_atTop N] with M hM
  rw [dist_eq_norm]
  have hn : ‖rmFinite (range M) b - b‖ ≤ ε / 2 := by
    change ‖(rmFinite (range M) b - b).toBCF‖ ≤ ε / 2
    apply (BoundedContinuousFunction.norm_le (half_pos hε).le).mpr
    intro n
    change ‖(if n ∈ range M then b n else 0) - b n‖ ≤ ε / 2
    simp only [mem_range]
    by_cases hnm : n < M
    · simpa only [if_pos hnm, sub_self, norm_zero] using (half_pos hε).le
    · have hb := hN n (by omega : N ≤ n)
      rw [dist_zero_right] at hb
      have hb' : ‖b n‖ < ε / 2 := hb
      simpa only [if_neg hnm, zero_sub, norm_neg] using le_of_lt hb'
  exact hn.trans_lt (half_lt_self hε)

private theorem rmDual_representation (f : C₀(ℕ, ℝ) →L[ℝ] ℝ) (b : C₀(ℕ, ℝ)) :
    f b = ∑' n, f (rmBasis n) * b n := by
  have hs : Summable (fun n => f (rmBasis n) * b n) := by
    apply ((rmDual_summable f).abs.mul_right ‖b‖).of_norm_bounded
    intro n
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left
      (BoundedContinuousFunction.norm_coe_le_norm b.toBCF n) (abs_nonneg _)
  have ht := (f.continuous.tendsto b).comp (rmFinite_tendsto b)
  have he (N : ℕ) : f (rmFinite (range N) b) =
      ∑ n ∈ range N, f (rmBasis n) * b n := by
    rw [rmFinite_eq_sum, map_sum]
    apply sum_congr rfl
    intro n _
    rw [map_smul]
    exact mul_comm _ _
  exact tendsto_nhds_unique (ht.congr he) hs.hasSum.tendsto_sum_nat

private theorem rmDual_eq_zero (f : C₀(ℕ, ℝ) →L[ℝ] ℝ)
    (hf : ∀ d, f (normalizedResidueMode d) = 0) : f = 0 := by
  have ha : ∀ n, f (rmBasis n) = 0 := by
    apply rmPairing_injective (rmDual_summable f)
    intro d
    exact (rmDual_representation f (normalizedResidueMode d)).symm.trans (hf d)
  ext b
  rw [rmDual_representation]
  simp only [ha, zero_mul, tsum_zero, _root_.zero_apply]

private theorem rmDense_span :
    (Submodule.span ℝ (Set.range normalizedResidueMode)).topologicalClosure = ⊤ := by
  let S := Submodule.span ℝ (Set.range normalizedResidueMode)
  let P := S.topologicalClosure
  letI : IsClosed (P : Set C₀(ℕ, ℝ)) := S.isClosed_topologicalClosure
  apply top_unique
  intro b _
  change b ∈ P
  by_contra hb
  have hq : P.mkQ b ≠ 0 := by
    intro h
    exact hb ((Submodule.Quotient.mk_eq_zero P).mp h)
  have hqnorm : ‖P.mkQ b‖ ≠ 0 := (norm_ne_zero_iff (a := P.mkQ b)).mpr hq
  obtain ⟨g, _, hg⟩ := exists_dual_vector ℝ (P.mkQ b) hqnorm
  let f : C₀(ℕ, ℝ) →L[ℝ] ℝ := g.comp P.mkQL
  have hf : f = 0 := by
    apply rmDual_eq_zero
    intro d
    have hv : normalizedResidueMode d ∈ P :=
      S.le_topologicalClosure (Submodule.subset_span ⟨d, rfl⟩)
    change g (P.mkQ (normalizedResidueMode d)) = 0
    have hvq : P.mkQ (normalizedResidueMode d) = 0 :=
      (Submodule.Quotient.mk_eq_zero P).mpr hv
    rw [hvq, map_zero]
  have hfb : g (P.mkQ b) = 0 := congrArg (fun t : C₀(ℕ, ℝ) →L[ℝ] ℝ => t b) hf
  exact hqnorm (hg.symm.trans hfb)

/-- Modes of moduli at least two span a dense subspace in the actual uniform `c₀` norm. -/
theorem normalizedResidueMode_dense_span :
    (Submodule.span ℝ (normalizedResidueMode '' Set.Ici 2)).topologicalClosure = ⊤ := by
  have hs : Submodule.span ℝ (Set.range normalizedResidueMode) ≤
      Submodule.span ℝ (normalizedResidueMode '' Set.Ici 2) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨d, rfl⟩
    by_cases hd : 2 ≤ d
    · exact Submodule.subset_span ⟨d, hd, rfl⟩
    · rcases (by omega : d = 0 ∨ d = 1) with rfl | rfl <;>
        simp only [normalizedResidueMode_zero, normalizedResidueMode_one] <;>
        exact Submodule.zero_mem _
  apply top_unique
  rw [← rmDense_span]
  exact Submodule.topologicalClosure_mono hs

end
end GaloisForLFunctions.BezoutValuationIncidence
