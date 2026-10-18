import GaloisForLFunctions.TransHorizonIncidenceMechanics.HorizonRadicalStateAndDefectNormalForm
import GaloisForLFunctions.TransHorizonIncidenceMechanics.TransHorizonRoughAbsorptionAndReset

/-!
# Radical checkpoint sign rigidity and the unit-coefficient law

Changing only the coefficient at one leaves every additive sieve jump unchanged,
while prefix defect changes affinely by the endpoint-response difference. Equal
endpoint responses are exactly the locus where every such shift has nonpositive
defect. Outside this locus the affine orbit realizes every real value.

For positive observation k, the radical state is one exactly when k is rough.
These, and only these, are weight-universal nonpositive checkpoints. The converse
already holds for squarefree weights supported at one and one visible prime,
with c(1)=1 and every coefficient in [0,1]. The specific Moebius and damped
families impose further coefficient relations; no counterexample for them is claimed.
The entire active sawtooth profile is blind to unit shifts, so even all its horizons
and observation positions together cannot determine defect at a nonrough checkpoint.
-/

open Finset
open GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-- Change only the coefficient of the unit divisor. -/
def sieveUnitShiftWeight (c : ℕ → ℝ) (a : ℝ) (d : ℕ) : ℝ :=
  c d + if d = 1 then a else 0

/-- Every active sawtooth observable is blind to the unit coefficient, at every horizon and position. -/
theorem activeCenteredSawtoothSum_unitShiftWeight (N m k : ℕ) (c : ℕ → ℝ) (a : ℝ) :
    activeCenteredSawtoothSum N (sieveUnitShiftWeight c a) m k =
      activeCenteredSawtoothSum N c m k := by
  unfold activeCenteredSawtoothSum
  congr 1
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases hd1 : d = 1
  · subst d
    simp [GaloisForLFunctions.BiScaleUncertainty.centeredDiscreteSawtooth_one]
  · simp [sieveUnitShiftWeight, hd1]

/-- Unit shifts preserve squarefree support. -/
theorem sieveUnitShiftWeight_squarefree_support {c : ℕ → ℝ}
    (hc : ∀ d : ℕ, ¬ Squarefree d → c d = 0) (a : ℝ) :
    ∀ d : ℕ, ¬ Squarefree d → sieveUnitShiftWeight c a d = 0 := by
  intro d hd
  have hd1 : d ≠ 1 := by
    rintro rfl
    exact hd squarefree_one
  simp [sieveUnitShiftWeight, hc d hd, hd1]

/-- A nonnegative unit shift preserves nonnegative coefficients. -/
theorem sieveUnitShiftWeight_nonneg {c : ℕ → ℝ} (hc : ∀ d, 0 ≤ c d)
    {a : ℝ} (ha : 0 ≤ a) (d : ℕ) : 0 ≤ sieveUnitShiftWeight c a d := by
  unfold sieveUnitShiftWeight
  split_ifs <;> linarith [hc d]

/-- At positive horizon the unit coefficient shifts every sieve response equally. -/
theorem sieveSeq_unitShiftWeight {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) (a : ℝ)
    (k : ℕ) : sieveSeq N (sieveUnitShiftWeight c a) k = sieveSeq N c k + a := by
  simp [sieveSeq, sieveUnitShiftWeight, Finset.sum_add_distrib, hN]

/-- Every additive response difference is invariant under the unit coefficient. -/
theorem sieveSeq_unitShiftWeight_sub (N k l : ℕ) (c : ℕ → ℝ) (a : ℝ) :
    sieveSeq N (sieveUnitShiftWeight c a) k - sieveSeq N (sieveUnitShiftWeight c a) l =
      sieveSeq N c k - sieveSeq N c l := by
  by_cases hN : 1 ≤ N
  · rw [sieveSeq_unitShiftWeight hN, sieveSeq_unitShiftWeight hN]
    ring
  · have hN0 : N = 0 := by omega
    subst N
    simp [sieveSeq]

/-- Exact affine dependence of prefix defect on the coefficient at one, at every horizon. -/
theorem sieveRenormalizedPrefixDefect_unitShiftWeight (N M : ℕ) (c : ℕ → ℝ) (a : ℝ) :
    sieveRenormalizedPrefixDefect N M (sieveUnitShiftWeight c a) =
      sieveRenormalizedPrefixDefect N M c + a * (sieveSeq N c (M + 1) - sieveSeq N c 1) := by
  by_cases hN : 1 ≤ N
  · induction M with
    | zero => simp [sieveRenormalizedPrefixDefect_eq_sum_mul_addDiff]
    | succ M ih =>
      have hshift := sieveRenormalizedPrefixDefect_succ_sub_eq N M (sieveUnitShiftWeight c a)
      have hbase := sieveRenormalizedPrefixDefect_succ_sub_eq N M c
      simp only [sieveSeq_unitShiftWeight hN] at hshift
      nlinarith only [hshift, hbase, ih]
  · have hN0 : N = 0 := by omega
    subst N
    simp [sieveRenormalizedPrefixDefect_eq_sum_mul_addDiff, sieveSeq]

/-- Sieve response is homogeneous in its coefficient weight. -/
theorem sieveSeq_scale_weight (N k : ℕ) (c : ℕ → ℝ) (t : ℝ) :
    sieveSeq N (fun d => t * c d) k = t * sieveSeq N c k := by
  simp [sieveSeq, Finset.mul_sum]

/-- Prefix defect is quadratic in its coefficient weight. -/
theorem sieveRenormalizedPrefixDefect_scale_weight (N M : ℕ) (c : ℕ → ℝ) (t : ℝ) :
    sieveRenormalizedPrefixDefect N M (fun d => t * c d) =
      t ^ (2 : ℕ) * sieveRenormalizedPrefixDefect N M c := by
  simp only [sieveRenormalizedPrefixDefect_eq_sum_mul_addDiff,
    sieveSeq_scale_weight, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Equal endpoint responses turn the defect into negative additive energy, including empty prefixes. -/
theorem two_mul_sieveRenormalizedPrefixDefect_eq_neg_energy_of_equal_response
    (N M : ℕ) (c : ℕ → ℝ) (h : sieveSeq N c (M + 1) = sieveSeq N c 1) :
    2 * sieveRenormalizedPrefixDefect N M c =
      -(∑ j ∈ Finset.Icc 1 M, (sieveSeq N c (j + 1) - sieveSeq N c j) ^ (2 : ℕ)) := by
  by_cases hM : 1 ≤ M
  · rw [two_mul_sieveRenormalizedPrefixDefect_eq_neg_dirichlet_add_boundary N hM c, h]
    ring
  · have hM0 : M = 0 := by omega
    subst M
    simp [sieveRenormalizedPrefixDefect_eq_sum_mul_addDiff]

/-- Away from equal endpoint responses, changing only the unit coefficient realizes every real defect. -/
theorem sieveRenormalizedPrefixDefect_unitShiftWeight_surjective_iff (N M : ℕ)
    (c : ℕ → ℝ) :
    Function.Surjective (fun a : ℝ =>
      sieveRenormalizedPrefixDefect N M (sieveUnitShiftWeight c a)) ↔
      sieveSeq N c (M + 1) ≠ sieveSeq N c 1 := by
  constructor
  · intro h heq
    obtain ⟨a, ha⟩ := h (sieveRenormalizedPrefixDefect N M c + 1)
    dsimp only at ha
    rw [sieveRenormalizedPrefixDefect_unitShiftWeight, heq] at ha
    linarith
  · intro h t
    refine ⟨(t - sieveRenormalizedPrefixDefect N M c) /
      (sieveSeq N c (M + 1) - sieveSeq N c 1), ?_⟩
    dsimp only
    rw [sieveRenormalizedPrefixDefect_unitShiftWeight,
      div_mul_cancel₀ _ (sub_ne_zero.mpr h)]
    ring

/-- Nonpositivity survives every unit shift exactly on the equal-response hyperplane. -/
theorem sieveRenormalizedPrefixDefect_all_unitShifts_nonpos_iff (N M : ℕ)
    (c : ℕ → ℝ) :
    (∀ a : ℝ, sieveRenormalizedPrefixDefect N M (sieveUnitShiftWeight c a) ≤ 0) ↔
      sieveSeq N c (M + 1) = sieveSeq N c 1 := by
  constructor
  · intro h
    by_contra hne
    obtain ⟨a, ha⟩ :=
      (sieveRenormalizedPrefixDefect_unitShiftWeight_surjective_iff N M c).mpr hne 1
    dsimp only at ha
    have hle := h a
    rw [ha] at hle
    linarith
  · intro h a
    have hpol := two_mul_sieveRenormalizedPrefixDefect_eq_neg_energy_of_equal_response N M c h
    have hnonneg : 0 ≤ ∑ j ∈ Finset.Icc 1 M,
        (sieveSeq N c (j + 1) - sieveSeq N c j) ^ (2 : ℕ) :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    rw [sieveRenormalizedPrefixDefect_unitShiftWeight, h]
    nlinarith only [hpol, hnonneg]

/-- The trivial radical state is exactly arithmetic roughness for positive observations. -/
theorem horizonRadicalState_eq_one_iff_isTransHorizonRough {N k : ℕ} (hk : 1 ≤ k) :
    horizonRadicalState N k = 1 ↔ IsTransHorizonRough N k := by
  constructor
  · intro h d hdk hdN
    by_contra hd1
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd1
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdk (by omega)
    have hpN : p ≤ N := (Nat.le_of_dvd hdpos hpd).trans hdN
    have hpR := (prime_dvd_horizonRadicalState_iff N k hp).mpr ⟨hpd.trans hdk, hpN⟩
    rw [h] at hpR
    exact hp.ne_one (Nat.eq_one_of_dvd_one hpR)
  · intro h
    have heq := (horizonRadicalState_eq_iff_all_squarefree_sieveSeq N k 1).mpr
      (fun c _ => sieveSeq_of_isTransHorizonRough h c)
    simpa [horizonRadicalState] using heq

private theorem prime_indicator_support {p : ℕ} (hp : p.Prime) :
    ∀ d : ℕ, ¬ Squarefree d → (if d = p then (1 : ℝ) else 0) = 0 := by
  intro d hd
  split_ifs with hdp
  · subst d
    exact (hd hp.squarefree).elim
  · rfl

/-- A visible prime at an endpoint provides a two-coefficient affine chart for the whole defect line. -/
theorem exists_prime_unitShift_defect_chart {N k : ℕ} (hk : 1 ≤ k)
    (hR : horizonRadicalState N k ≠ 1) :
    ∃ p : ℕ, p.Prime ∧ p ≤ N ∧ p ∣ k ∧
      ∀ a : ℝ,
        sieveRenormalizedPrefixDefect N (k - 1)
          (sieveUnitShiftWeight (fun d => if d = p then 1 else 0) a) =
            sieveRenormalizedPrefixDefect N (k - 1) (fun d => if d = p then 1 else 0) + a := by
  obtain ⟨p, hp, hpR⟩ := Nat.exists_prime_and_dvd hR
  obtain ⟨hpk, hpN⟩ := (prime_dvd_horizonRadicalState_iff N k hp).mp hpR
  refine ⟨p, hp, hpN, hpk, ?_⟩
  intro a
  have hpI : p ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨hp.one_le, hpN⟩
  rw [sieveRenormalizedPrefixDefect_unitShiftWeight, Nat.sub_add_cancel hk]
  simp [sieveSeq, hpI, hpk, hp.ne_one]

/-- Every real defect is attained while fixing the entire active sawtooth profile across all horizons. -/
theorem exists_squarefree_same_active_sawtooth_defect_eq {N k : ℕ} (hk : 1 ≤ k)
    (hR : horizonRadicalState N k ≠ 1) (t : ℝ) :
    ∃ (p : ℕ) (c : ℕ → ℝ), p.Prime ∧ p ≤ N ∧ p ∣ k ∧
      (∀ d, d ≠ 1 → d ≠ p → c d = 0) ∧
      (∀ d : ℕ, ¬ Squarefree d → c d = 0) ∧
      (∀ H m j, activeCenteredSawtoothSum H c m j =
        activeCenteredSawtoothSum H (fun d => if d = p then 1 else 0) m j) ∧
      sieveRenormalizedPrefixDefect N (k - 1) c = t := by
  obtain ⟨p, hp, hpN, hpk, hchart⟩ := exists_prime_unitShift_defect_chart hk hR
  let c : ℕ → ℝ := fun d => if d = p then 1 else 0
  let a := t - sieveRenormalizedPrefixDefect N (k - 1) c
  refine ⟨p, sieveUnitShiftWeight c a, hp, hpN, hpk, ?_,
    sieveUnitShiftWeight_squarefree_support (prime_indicator_support hp) a, ?_, ?_⟩
  · intro d hd1 hdp
    simp [sieveUnitShiftWeight, c, hd1, hdp]
  · intro H m j
    exact activeCenteredSawtoothSum_unitShiftWeight H m j c a
  · rw [hchart]
    dsimp [a, c]
    ring

/-- Nonnegative squarefree weights already have unbounded positive defects at every nonrough endpoint. -/
theorem exists_nonneg_squarefree_defect_gt_of_radicalState_ne_one {N k : ℕ} (hk : 1 ≤ k)
    (hR : horizonRadicalState N k ≠ 1) (B : ℝ) :
    ∃ (p : ℕ) (c : ℕ → ℝ), p.Prime ∧ p ≤ N ∧ p ∣ k ∧
      (∀ d, d ≠ 1 → d ≠ p → c d = 0) ∧
      (∀ d : ℕ, ¬ Squarefree d → c d = 0) ∧
      (∀ d, 0 ≤ c d) ∧ B < sieveRenormalizedPrefixDefect N (k - 1) c := by
  obtain ⟨p, hp, hpN, hpk, hchart⟩ := exists_prime_unitShift_defect_chart hk hR
  let c : ℕ → ℝ := fun d => if d = p then 1 else 0
  let a := |B - sieveRenormalizedPrefixDefect N (k - 1) c| + 1
  refine ⟨p, sieveUnitShiftWeight c a, hp, hpN, hpk, ?_,
    sieveUnitShiftWeight_squarefree_support (prime_indicator_support hp) a, ?_, ?_⟩
  · intro d hd1 hdp
    simp [sieveUnitShiftWeight, c, hd1, hdp]
  · apply sieveUnitShiftWeight_nonneg
    · intro d
      dsimp [c]
      split_ifs <;> positivity
    · dsimp [a]
      positivity
  · rw [hchart]
    have hle := le_abs_self (B - sieveRenormalizedPrefixDefect N (k - 1) c)
    dsimp [a, c] at *
    linarith

/-- Roughness is exactly universal defect nonpositivity, even when tested only on nonnegative squarefree weights. -/
theorem isTransHorizonRough_iff_forall_nonneg_squarefree_defect_nonpos {N k : ℕ}
    (hk : 1 ≤ k) :
    IsTransHorizonRough N k ↔
      ∀ c : ℕ → ℝ, (∀ d : ℕ, ¬ Squarefree d → c d = 0) →
        (∀ d, 0 ≤ c d) → sieveRenormalizedPrefixDefect N (k - 1) c ≤ 0 := by
  constructor
  · intro h c _ _
    by_cases hk2 : 2 ≤ k
    · exact (sieveRenormalizedPrefixDefect_nonpos_of_isTransHorizonRough N c hk2 h).1
    · have hk1 : k = 1 := by omega
      subst k
      simp [sieveRenormalizedPrefixDefect_eq_sum_mul_addDiff]
  · intro h
    apply (horizonRadicalState_eq_one_iff_isTransHorizonRough hk).mp
    by_contra hR
    obtain ⟨p, c, _, _, _, _, hc, hnonneg, hpos⟩ :=
      exists_nonneg_squarefree_defect_gt_of_radicalState_ne_one hk hR 0
    exact (not_lt_of_ge (h c hc hnonneg)) hpos

/-- Testing all squarefree weights detects precisely the rough checkpoints. -/
theorem isTransHorizonRough_iff_forall_squarefree_defect_nonpos {N k : ℕ} (hk : 1 ≤ k) :
    IsTransHorizonRough N k ↔
      ∀ c : ℕ → ℝ, (∀ d : ℕ, ¬ Squarefree d → c d = 0) →
        sieveRenormalizedPrefixDefect N (k - 1) c ≤ 0 := by
  constructor
  · intro h c _
    by_cases hk2 : 2 ≤ k
    · exact (sieveRenormalizedPrefixDefect_nonpos_of_isTransHorizonRough N c hk2 h).1
    · have hk1 : k = 1 := by omega
      subst k
      simp [sieveRenormalizedPrefixDefect_eq_sum_mul_addDiff]
  · intro h
    exact (isTransHorizonRough_iff_forall_nonneg_squarefree_defect_nonpos hk).mpr
      (fun c hc _ => h c hc)

/-- Rough checkpoints are the complete weight-independent sign locus. -/
theorem isTransHorizonRough_iff_forall_defect_nonpos {N k : ℕ} (hk : 1 ≤ k) :
    IsTransHorizonRough N k ↔
      ∀ c : ℕ → ℝ, sieveRenormalizedPrefixDefect N (k - 1) c ≤ 0 := by
  constructor
  · intro h c
    by_cases hk2 : 2 ≤ k
    · exact (sieveRenormalizedPrefixDefect_nonpos_of_isTransHorizonRough N c hk2 h).1
    · have hk1 : k = 1 := by omega
      subst k
      simp [sieveRenormalizedPrefixDefect_eq_sum_mul_addDiff]
  · intro h
    exact (isTransHorizonRough_iff_forall_squarefree_defect_nonpos hk).mpr (fun c _ => h c)

/-- A finite universal upper bound exists exactly at rough checkpoints, and its sharp value is zero. -/
theorem forall_nonneg_squarefree_defect_le_iff {N k : ℕ} (hk : 1 ≤ k) (B : ℝ) :
    (∀ c : ℕ → ℝ, (∀ d : ℕ, ¬ Squarefree d → c d = 0) →
      (∀ d, 0 ≤ c d) → sieveRenormalizedPrefixDefect N (k - 1) c ≤ B) ↔
        IsTransHorizonRough N k ∧ 0 ≤ B := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · apply (horizonRadicalState_eq_one_iff_isTransHorizonRough hk).mp
      by_contra hR
      obtain ⟨p, c, _, _, _, _, hc, hnonneg, hgt⟩ :=
        exists_nonneg_squarefree_defect_gt_of_radicalState_ne_one hk hR B
      exact (not_lt_of_ge (h c hc hnonneg)) hgt
    · have hz := h (fun _ => 0) (fun _ _ => rfl) (fun _ => le_refl 0)
      simpa [sieveRenormalizedPrefixDefect_eq_sum_mul_addDiff, sieveSeq] using hz
  · rintro ⟨hrough, hB⟩ c _ _
    exact ((isTransHorizonRough_iff_forall_defect_nonpos hk).mp hrough c).trans hB

/-- The sign obstruction persists with unit coefficient one and every coefficient in the unit interval. -/
theorem exists_normalized_nonneg_squarefree_positive_defect {N k : ℕ} (hk : 1 ≤ k)
    (hR : horizonRadicalState N k ≠ 1) :
    ∃ (p : ℕ) (c : ℕ → ℝ), p.Prime ∧ p ≤ N ∧ p ∣ k ∧
      (∀ d, d ≠ 1 → d ≠ p → c d = 0) ∧
      (∀ d : ℕ, ¬ Squarefree d → c d = 0) ∧
      (∀ d, 0 ≤ c d) ∧ (∀ d, c d ≤ 1) ∧ c 1 = 1 ∧
      0 < sieveRenormalizedPrefixDefect N (k - 1) c := by
  obtain ⟨p, hp, hpN, hpk, _⟩ := exists_prime_unitShift_defect_chart hk hR
  let u : ℕ → ℝ := fun d => if d = p then 1 else 0
  let D := sieveRenormalizedPrefixDefect N (k - 1) u
  let t : ℝ := 1 / (|D| + 1)
  let c := sieveUnitShiftWeight (fun d => t * u d) 1
  have ht : 0 < t := by dsimp [t]; positivity
  have hden : |D| + 1 ≠ 0 := ne_of_gt (by positivity : 0 < |D| + 1)
  have hcancel : t * (|D| + 1) = 1 := div_mul_cancel₀ 1 hden
  have htle : t ≤ 1 := by
    have hmul : 0 ≤ t * |D| := mul_nonneg ht.le (abs_nonneg D)
    nlinarith only [hcancel, hmul]
  have hcancel' := congrArg (fun x : ℝ => t * x) hcancel
  have hpositive : 0 < t ^ (2 : ℕ) * (D + |D| + 1) := by
    apply mul_pos (sq_pos_of_pos ht)
    have hlow := neg_abs_le D
    linarith
  have hvalue : sieveRenormalizedPrefixDefect N (k - 1) c = t ^ (2 : ℕ) * D + t := by
    dsimp [c]
    rw [sieveRenormalizedPrefixDefect_unitShiftWeight,
      sieveRenormalizedPrefixDefect_scale_weight, sieveSeq_scale_weight,
      sieveSeq_scale_weight, Nat.sub_add_cancel hk]
    have hpI : p ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨hp.one_le, hpN⟩
    simp [u, D, sieveSeq, hpI, hpk, hp.ne_one]
  refine ⟨p, c, hp, hpN, hpk, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro d hd1 hdp
    simp [c, sieveUnitShiftWeight, u, hd1, hdp]
  · apply sieveUnitShiftWeight_squarefree_support
    intro d hd
    rw [show u d = 0 from prime_indicator_support hp d hd]
    ring
  · apply sieveUnitShiftWeight_nonneg
    · intro d
      dsimp [u]
      split_ifs <;> positivity
    · positivity
  · intro d
    by_cases hd1 : d = 1
    · subst d
      simp [c, sieveUnitShiftWeight, u, Ne.symm hp.ne_one]
    · by_cases hdp : d = p
      · simpa [c, sieveUnitShiftWeight, u, hdp, hp.ne_one] using htle
      · simp [c, sieveUnitShiftWeight, u, hd1, hdp]
  · simp [c, sieveUnitShiftWeight, u, Ne.symm hp.ne_one]
  · rw [hvalue]
    nlinarith only [hpositive, hcancel']

/-- Normalized squarefree weights with coefficients in the unit interval detect exactly rough checkpoints. -/
theorem isTransHorizonRough_iff_forall_normalized_bounded_squarefree_defect_nonpos
    {N k : ℕ} (hk : 1 ≤ k) :
    IsTransHorizonRough N k ↔
      ∀ c : ℕ → ℝ, (∀ d : ℕ, ¬ Squarefree d → c d = 0) →
        (∀ d, 0 ≤ c d) → (∀ d, c d ≤ 1) → c 1 = 1 →
          sieveRenormalizedPrefixDefect N (k - 1) c ≤ 0 := by
  constructor
  · intro h c _ _ _ _
    exact (isTransHorizonRough_iff_forall_defect_nonpos hk).mp h c
  · intro h
    apply (horizonRadicalState_eq_one_iff_isTransHorizonRough hk).mp
    by_contra hR
    obtain ⟨p, c, _, _, _, _, hc, hnonneg, hupper, hunit, hpos⟩ :=
      exists_normalized_nonneg_squarefree_positive_defect hk hR
    exact (not_lt_of_ge (h c hc hnonneg hupper hunit)) hpos

end
end GaloisForLFunctions.TransHorizonIncidenceMechanics
