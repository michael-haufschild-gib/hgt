import GaloisForLFunctions.BezoutValuationIncidence.DampingWorkAsArithmeticMarkovBoundaryFlux
import GaloisForLFunctions.RHTower.Sieve.MoebiusScaledReindex

/-!
# Finite arithmetic damping transition kernel

The exact Cesàro transform of the damped divisor transition has nonnegative
rows of mass one at nonnegative damping. These are finite identities for the
literal Möbius source; no critical Hilbert-space bound is assumed.
-/

open Finset ArithmeticFunction RHTower

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

private def adtTwist (η : ℝ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ where
  toFun n := f n * (n : ℝ) ^ (-η)
  map_zero' := by simp

private theorem adtTwist_mul (η : ℝ) (f g : ArithmeticFunction ℝ) :
    adtTwist η (f * g) = adtTwist η f * adtTwist η g := by
  ext n
  change (f * g) n * (n : ℝ) ^ (-η) = _
  simp only [ArithmeticFunction.mul_apply, sum_mul]
  apply sum_congr rfl
  intro x hx
  have he := (pmNaturalRpowHom η).map_mul x.1 x.2
  change ((x.1 * x.2 : ℕ) : ℝ) ^ (-η) =
    (x.1 : ℝ) ^ (-η) * (x.2 : ℝ) ^ (-η) at he
  rw [(Nat.mem_divisorsAntidiagonal.mp hx).1] at he
  change f x.1 * g x.2 * (n : ℝ) ^ (-η) =
    (f x.1 * (x.1 : ℝ) ^ (-η)) * (g x.2 * (x.2 : ℝ) ^ (-η))
  rw [he]
  ring

private theorem adtTwist_one (η : ℝ) : adtTwist η 1 = 1 := by
  ext n
  change (1 : ArithmeticFunction ℝ) n * (n : ℝ) ^ (-η) =
    (1 : ArithmeticFunction ℝ) n
  by_cases hn : n = 1 <;> simp [hn]

private theorem adtTwist_moebius_zeta (η : ℝ) (n : ℕ) :
    (adtTwist η ((moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ) *
      ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)) n =
      pmPowerDampedDivisorCoeff η n := by
  rw [coe_mul_zeta_apply]
  rfl

/-- The positive divisor transition has total mass one. The identity itself
holds for every real damping, without a positivity restriction. -/
theorem arithmeticDamping_divisor_mass (η : ℝ) {n : ℕ} (hn : 0 < n) :
    (∑ d ∈ n.divisors, (d : ℝ) ^ (-η) *
      pmPowerDampedDivisorCoeff η (n / d)) = 1 := by
  have h : adtTwist η ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) *
      (adtTwist η ((moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ) *
        ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)) =
      ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) := by
    rw [← mul_assoc, ← adtTwist_mul, coe_zeta_mul_coe_moebius,
      adtTwist_one, one_mul]
  have he := congrArg (fun f : ArithmeticFunction ℝ => f n) h
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (f := fun a b =>
      adtTwist η ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) a *
        (adtTwist η ((moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ) *
          ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)) b)] at he
  simp_rw [adtTwist_moebius_zeta] at he
  have hz : (((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) n) = 1 := by
    simp [natCoe_apply, zeta_apply_ne hn.ne']
  rw [hz] at he
  convert he using 1
  apply sum_congr rfl
  intro d hd
  have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
  simp [adtTwist, natCoe_apply, hd0]

theorem arithmeticDampingPrefix_nonneg {η : ℝ} (hη : 0 ≤ η) (n : ℕ) :
    0 ≤ arithmeticDampingPrefix η n :=
  sum_nonneg fun k _ => pmPowerDampedDivisorCoeff_nonneg hη k

theorem arithmeticDampingPrefix_mono {η : ℝ} (hη : 0 ≤ η) :
    Monotone (arithmeticDampingPrefix η) := by
  intro m n hmn
  apply sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right hmn)
  intro k _ _
  exact pmPowerDampedDivisorCoeff_nonneg hη k

/-- Normalization of the exact weighted divisor prefixes. -/
theorem arithmeticDampingPrefix_weighted_sum (η : ℝ) (n : ℕ) :
    (∑ k ∈ Icc 1 n, (k : ℝ) ^ (-η) * arithmeticDampingPrefix η (n / k)) = n := by
  have h := Sieve.sum_divisors_swap n
    (fun d k => (d : ℝ) ^ (-η) * pmPowerDampedDivisorCoeff η k)
  simp only [← mul_sum] at h
  change (∑ k ∈ Icc 1 n, ∑ d ∈ k.divisors,
    (d : ℝ) ^ (-η) * pmPowerDampedDivisorCoeff η (k / d)) =
      ∑ d ∈ Icc 1 n, (d : ℝ) ^ (-η) * arithmeticDampingPrefix η (n / d) at h
  rw [← h]
  have hs : (∑ k ∈ Icc 1 n, ∑ d ∈ k.divisors,
      (d : ℝ) ^ (-η) * pmPowerDampedDivisorCoeff η (k / d)) =
      ∑ _k ∈ Icc 1 n, (1 : ℝ) := by
    exact sum_congr rfl fun k hk => arithmeticDamping_divisor_mass η (mem_Icc.mp hk).1
  rw [hs]
  simp

/-- The finite Cesàro transition. State zero has zero weight, and a positive
row is supported on the positive states at most its starting state. -/
def arithmeticDampingTransition (η : ℝ) (n k : ℕ) : ℝ :=
  (k : ℝ) / n *
    ((k : ℝ) ^ (-η) * arithmeticDampingPrefix η (n / k) -
      ((k + 1 : ℕ) : ℝ) ^ (-η) * arithmeticDampingPrefix η (n / (k + 1)))

@[simp] theorem arithmeticDampingTransition_zero_right (η : ℝ) (n : ℕ) :
    arithmeticDampingTransition η n 0 = 0 := by
  simp [arithmeticDampingTransition]

@[simp] theorem arithmeticDampingTransition_zero_left (η : ℝ) (k : ℕ) :
    arithmeticDampingTransition η 0 k = 0 := by
  simp [arithmeticDampingTransition]

theorem arithmeticDampingTransition_eq_zero_of_lt (η : ℝ) {n k : ℕ} (hnk : n < k) :
    arithmeticDampingTransition η n k = 0 := by
  simp [arithmeticDampingTransition, Nat.div_eq_of_lt hnk,
    Nat.div_eq_of_lt (show n < k + 1 by omega), arithmeticDampingPrefix]

theorem arithmeticDampingTransition_nonneg {η : ℝ} (hη : 0 ≤ η) (n k : ℕ) :
    0 ≤ arithmeticDampingTransition η n k := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  apply mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  apply sub_nonneg.mpr
  apply mul_le_mul
  · apply Real.rpow_le_rpow_of_nonpos
    · exact_mod_cast Nat.pos_of_ne_zero hk
    · exact_mod_cast Nat.le_succ k
    · linarith
  · apply arithmeticDampingPrefix_mono hη
    exact Nat.div_le_div_left (Nat.le_succ k) (Nat.pos_of_ne_zero hk)
  · exact arithmeticDampingPrefix_nonneg hη _
  · exact Real.rpow_nonneg (Nat.cast_nonneg _) _

private theorem adt_weighted_telescope (a : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Icc 1 n, (k : ℝ) * (a k - a (k + 1))) =
      (∑ k ∈ Icc 1 n, a k) - (n : ℝ) * a (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_Icc_succ_top (by omega), sum_Icc_succ_top (by omega), ih]
    push_cast
    ring

/-- Every positive row has total probability one. -/
theorem arithmeticDampingTransition_sum (η : ℝ) {n : ℕ} (hn : 0 < n) :
    (∑ k ∈ Icc 1 n, arithmeticDampingTransition η n k) = 1 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold arithmeticDampingTransition
  simp_rw [div_mul_eq_mul_div]
  rw [← sum_div, adt_weighted_telescope, arithmeticDampingPrefix_weighted_sum]
  simp [Nat.div_eq_of_lt (Nat.lt_succ_self n), arithmeticDampingPrefix, hn0]

@[simp] theorem arithmeticDampingPrefix_zero (η : ℝ) :
    arithmeticDampingPrefix η 0 = 0 := by
  simp [arithmeticDampingPrefix]

@[simp] theorem arithmeticDampingPrefix_one (η : ℝ) :
    arithmeticDampingPrefix η 1 = 1 := by
  simp [arithmeticDampingPrefix, pmPowerDampedDivisorCoeff_one]

theorem arithmeticDampingTransition_diagonal (η : ℝ) {n : ℕ} (hn : 0 < n) :
    arithmeticDampingTransition η n n = (n : ℝ) ^ (-η) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp [arithmeticDampingTransition, Nat.div_self hn,
    Nat.div_eq_of_lt (Nat.lt_succ_self n), hn0]

private theorem adt_prefix_zero_damping {n : ℕ} (hn : 0 < n) :
    arithmeticDampingPrefix 0 n = 1 := by
  unfold arithmeticDampingPrefix
  simp_rw [pmPowerDampedDivisorCoeff_zero_damping]
  rw [sum_ite_eq']
  simp [hn.ne']

/-- Zero damping is the identity on every positive finite state space. -/
theorem arithmeticDampingTransition_zero_damping {n : ℕ} (hn : 0 < n) (k : ℕ) :
    arithmeticDampingTransition 0 n k = if k = n then 1 else 0 := by
  by_cases hkn : k = n
  · subst k
    simp [arithmeticDampingTransition_diagonal _ hn]
  rw [if_neg hkn]
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  by_cases hnk : n < k
  · exact arithmeticDampingTransition_eq_zero_of_lt _ hnk
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  have hq : 0 < n / k := Nat.div_pos (by omega) hkpos
  have hq' : 0 < n / (k + 1) := Nat.div_pos (by omega) (by omega)
  simp [arithmeticDampingTransition, adt_prefix_zero_damping hq,
    adt_prefix_zero_damping hq']

private theorem adt_telescope (a : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Icc 1 n, (a k - a (k + 1))) = a 1 - a (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_Icc_succ_top (by omega), ih]
    ring

/-- Applying the transition to `1/k` recovers the literal normalized divisor
prefix, rather than a substituted or freely chosen source. -/
theorem arithmeticDampingTransition_source (η : ℝ) {n : ℕ} (hn : 0 < n) :
    (∑ k ∈ Icc 1 n, arithmeticDampingTransition η n k / k) =
      arithmeticDampingMean η n := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have he (k : ℕ) (hk : k ∈ Icc 1 n) :
      arithmeticDampingTransition η n k / k =
        ((k : ℝ) ^ (-η) * arithmeticDampingPrefix η (n / k) -
          ((k + 1 : ℕ) : ℝ) ^ (-η) * arithmeticDampingPrefix η (n / (k + 1))) / n := by
    have hkpos : 0 < k := (mem_Icc.mp hk).1
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hkpos.ne'
    unfold arithmeticDampingTransition
    field_simp
  rw [sum_congr rfl he, ← sum_div, adt_telescope]
  simp [Nat.div_eq_of_lt (Nat.lt_succ_self n), arithmeticDampingMean]

/-- The sampled normalized floor profile. -/
def arithmeticDampingFloorProfile (d n : ℕ) : ℝ := (n / d : ℕ) / (n : ℝ)

private theorem adt_floor_telescope (a : ℕ → ℝ) (n d : ℕ) :
    (∑ k ∈ Icc 1 n, (a k - a (k + 1)) * (k / d : ℕ)) =
      (∑ k ∈ Icc 1 n, if d ∣ k then a k else 0) -
        (n / d : ℕ) * a (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_Icc_succ_top (by omega), sum_Icc_succ_top (by omega), ih]
    by_cases h : d ∣ n + 1 <;> simp [Nat.succ_div, h] <;> ring

/-- Every floor profile is an exact finite eigenfunction. The identity holds
for all real damping; positivity is needed only for the Markov interpretation. -/
theorem arithmeticDampingTransition_floorProfile (η : ℝ) {n d : ℕ}
    (hn : 0 < n) (hd : 0 < d) :
    (∑ k ∈ Icc 1 n,
      arithmeticDampingTransition η n k * arithmeticDampingFloorProfile d k) =
      (d : ℝ) ^ (-η) * arithmeticDampingFloorProfile d n := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have he (k : ℕ) (hk : k ∈ Icc 1 n) :
      arithmeticDampingTransition η n k * arithmeticDampingFloorProfile d k =
        (((k : ℝ) ^ (-η) * arithmeticDampingPrefix η (n / k) -
          ((k + 1 : ℕ) : ℝ) ^ (-η) * arithmeticDampingPrefix η (n / (k + 1))) *
          (k / d : ℕ)) / n := by
    have hkpos : 0 < k := (mem_Icc.mp hk).1
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hkpos.ne'
    unfold arithmeticDampingTransition arithmeticDampingFloorProfile
    field_simp
  rw [sum_congr rfl he, ← sum_div, adt_floor_telescope]
  simp only [Nat.div_eq_of_lt (Nat.lt_succ_self n), arithmeticDampingPrefix_zero,
    mul_zero, sub_zero]
  rw [← sum_filter, Sieve.sum_filter_dvd_eq_sum_scaled hd]
  have hm (j : ℕ) :
      ((d * j : ℕ) : ℝ) ^ (-η) * arithmeticDampingPrefix η (n / (d * j)) =
        (d : ℝ) ^ (-η) * ((j : ℝ) ^ (-η) *
          arithmeticDampingPrefix η ((n / d) / j)) := by
    have hp := (pmNaturalRpowHom η).map_mul d j
    change ((d * j : ℕ) : ℝ) ^ (-η) = (d : ℝ) ^ (-η) * (j : ℝ) ^ (-η) at hp
    rw [hp, Nat.div_div_eq_div_mul]
    ring
  simp_rw [hm]
  rw [← mul_sum, arithmeticDampingPrefix_weighted_sum]
  unfold arithmeticDampingFloorProfile
  ring

@[simp] theorem arithmeticDampingFloorProfile_zero (d : ℕ) :
    arithmeticDampingFloorProfile d 0 = 0 := by
  simp [arithmeticDampingFloorProfile]

theorem arithmeticDampingFloorProfile_eq_zero_of_lt {d n : ℕ} (h : n < d) :
    arithmeticDampingFloorProfile d n = 0 := by
  simp [arithmeticDampingFloorProfile, Nat.div_eq_of_lt h]

theorem arithmeticDampingFloorProfile_self {d : ℕ} (hd : 0 < d) :
    arithmeticDampingFloorProfile d d = 1 / (d : ℝ) := by
  simp [arithmeticDampingFloorProfile, Nat.div_self hd]

/-- Floor-profile moments determine a finite row. -/
theorem arithmeticDampingFloorProfile_separates (n : ℕ) (v : ℕ → ℝ)
    (h : ∀ d : ℕ, 0 < d →
      (∑ k ∈ Icc 1 n, v k * arithmeticDampingFloorProfile d k) = 0) :
    ∀ k ∈ Icc 1 n, v k = 0 := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
    have hv : v (n + 1) = 0 := by
      have hh := h (n + 1) (Nat.succ_pos n)
      rw [sum_Icc_succ_top (by omega)] at hh
      have hz : (∑ k ∈ Icc 1 n, v k * arithmeticDampingFloorProfile (n + 1) k) = 0 := by
        apply sum_eq_zero
        intro k hk
        rw [arithmeticDampingFloorProfile_eq_zero_of_lt
          (show k < n + 1 from Nat.lt_succ_of_le (mem_Icc.mp hk).2), mul_zero]
      rw [hz, zero_add, arithmeticDampingFloorProfile_self (Nat.succ_pos n)] at hh
      exact (mul_eq_zero.mp hh).resolve_right (by positivity)
    have hi : ∀ k ∈ Icc 1 n, v k = 0 := by
      apply ih v
      intro d hd
      have hh := h d hd
      rw [sum_Icc_succ_top (by omega), hv, zero_mul, add_zero] at hh
      exact hh
    intro k hk
    by_cases he : k = n + 1
    · simpa only [he] using hv
    · exact hi k (mem_Icc.mpr ⟨(mem_Icc.mp hk).1, by
        have := (mem_Icc.mp hk).2
        omega⟩)

private theorem adt_sum_extension (η : ℝ) (v : ℕ → ℝ) {j n : ℕ} (hjn : j ≤ n) :
    (∑ k ∈ Icc 1 n, arithmeticDampingTransition η j k * v k) =
      ∑ k ∈ Icc 1 j, arithmeticDampingTransition η j k * v k := by
  symm
  apply sum_subset (Icc_subset_Icc_right hjn)
  intro k hkn hkj
  have hjk : j < k := by
    have hk1 := (mem_Icc.mp hkn).1
    by_contra h
    exact hkj (mem_Icc.mpr ⟨hk1, by omega⟩)
  rw [arithmeticDampingTransition_eq_zero_of_lt _ hjk, zero_mul]

/-- The exact finite transition composition law. This is an algebraic identity
for all real parameters, and a Markov semigroup law at nonnegative parameters. -/
theorem arithmeticDampingTransition_semigroup (s t : ℝ) (n k : ℕ) :
    (∑ j ∈ Icc 1 n,
      arithmeticDampingTransition s n j * arithmeticDampingTransition t j k) =
      arithmeticDampingTransition (s + t) n k := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  by_cases hnk : n < k
  · rw [arithmeticDampingTransition_eq_zero_of_lt _ hnk]
    apply sum_eq_zero
    intro j hj
    rw [arithmeticDampingTransition_eq_zero_of_lt _
      (lt_of_le_of_lt (mem_Icc.mp hj).2 hnk), mul_zero]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hmoment (d : ℕ) (hd : 0 < d) :
      (∑ k ∈ Icc 1 n, (∑ j ∈ Icc 1 n,
        arithmeticDampingTransition s n j * arithmeticDampingTransition t j k) *
          arithmeticDampingFloorProfile d k) =
      ∑ k ∈ Icc 1 n, arithmeticDampingTransition (s + t) n k *
        arithmeticDampingFloorProfile d k := by
    calc
      _ = ∑ j ∈ Icc 1 n, arithmeticDampingTransition s n j *
          (∑ k ∈ Icc 1 n, arithmeticDampingTransition t j k *
            arithmeticDampingFloorProfile d k) := by
        simp only [sum_mul, mul_sum, mul_assoc]
        rw [sum_comm]
      _ = ∑ j ∈ Icc 1 n, arithmeticDampingTransition s n j *
          ((d : ℝ) ^ (-t) * arithmeticDampingFloorProfile d j) := by
        apply sum_congr rfl
        intro j hj
        rw [adt_sum_extension t _ (mem_Icc.mp hj).2,
          arithmeticDampingTransition_floorProfile t (mem_Icc.mp hj).1 hd]
      _ = (d : ℝ) ^ (-t) * ((d : ℝ) ^ (-s) * arithmeticDampingFloorProfile d n) := by
        rw [← arithmeticDampingTransition_floorProfile s hnpos hd, mul_sum]
        exact sum_congr rfl fun j _ => by ring
      _ = _ := by
        rw [arithmeticDampingTransition_floorProfile _ hnpos hd, neg_add,
          Real.rpow_add (by exact_mod_cast hd)]
        ring
  have hzero := arithmeticDampingFloorProfile_separates n
    (fun k => (∑ j ∈ Icc 1 n,
      arithmeticDampingTransition s n j * arithmeticDampingTransition t j k) -
      arithmeticDampingTransition (s + t) n k) (by
        intro d hd
        simp only [sub_mul, sum_sub_distrib]
        exact sub_eq_zero.mpr (hmoment d hd))
  exact sub_eq_zero.mp (hzero k (mem_Icc.mpr ⟨Nat.pos_of_ne_zero hk, by omega⟩))

end
end GaloisForLFunctions.BezoutValuationIncidence
