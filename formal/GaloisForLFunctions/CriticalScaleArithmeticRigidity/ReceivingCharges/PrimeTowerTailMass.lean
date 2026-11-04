import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.FiniteHorizonPrimeCharge
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.PrimeIncidenceHarmonicWindows
import GaloisForLFunctions.ArithmeticCouplingTheory.TheCompleteFormOnTheCoherentSector

/-!
# Bounded mass of the low-prime tower tails

Each Mangoldt-supported integer has exactly one prime divisor. Summing
the retained prime-tower heads therefore gives the Mertens sum exactly.
The remaining low-prime mass is bounded, since complete tower activity
and the Mertens sum have the same logarithmic leading term.
-/

noncomputable section

open Finset ArithmeticFunction
open scoped Classical

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory

/-- High-prime mass is a difference of cumulative masses, including cutoffs above the packet. -/
theorem highPrimePoleMass_eq_sub_min (Y Q : ℕ) :
    highPrimePoleMass Y Q = primePoleScale Q - primePoleScale (min Q Y) := by
  by_cases hYQ : Y ≤ Q
  · rw [min_eq_right hYQ, highPrimePoleMass_eq_sub hYQ]
  · have hQY : Q ≤ Y := (Nat.lt_of_not_ge hYQ).le
    rw [min_eq_left hQY, sub_self, highPrimePoleMass]
    exact sum_eq_zero fun p hp => if_neg (not_lt.mpr
      ((mem_Icc.mp (mem_filter.mp hp).1).2.trans hQY))

/-- The high-prime mass has a logarithmic ramp, with an absolute pointwise error. -/
theorem abs_highPrimePoleMass_sub_log_le {Y Q : ℕ} (hY : 1 ≤ Y) (hQ : 1 ≤ Q) :
    |highPrimePoleMass Y Q - max (Real.log Q - Real.log Y) 0| ≤
      2 * |(Real.log 4 + 4) + (8 + _root_.RHTower.Mertens.mertensTail)| := by
  let C := (Real.log 4 + 4) + (8 + _root_.RHTower.Mertens.mertensTail)
  by_cases hYQ : Y ≤ Q
  · have hlog : Real.log Y ≤ Real.log Q := Real.log_le_log
      (by exact_mod_cast hY) (by exact_mod_cast hYQ)
    rw [highPrimePoleMass_eq_sub hYQ, max_eq_left (sub_nonneg.mpr hlog)]
    have hid : primePoleScale Q - primePoleScale Y - (Real.log Q - Real.log Y) =
        (primePoleScale Q - Real.log Q) - (primePoleScale Y - Real.log Y) := by ring
    rw [hid]
    calc
      _ ≤ |primePoleScale Q - Real.log Q| + |primePoleScale Y - Real.log Y| := abs_sub _ _
      _ ≤ C + C := add_le_add (primePoleScale_logarithmic hQ) (primePoleScale_logarithmic hY)
      _ ≤ 2 * |C| := by linarith only [le_abs_self C]
  · have hQY := (Nat.lt_of_not_ge hYQ).le
    have hlog : Real.log Q ≤ Real.log Y := Real.log_le_log
      (by exact_mod_cast hQ) (by exact_mod_cast hQY)
    rw [highPrimePoleMass_eq_sub_min, min_eq_left hQY, sub_self,
      max_eq_right (sub_nonpos.mpr hlog), sub_self, abs_zero]
    positivity

/-- The finite prime-tower heads partition the entire reciprocal Mangoldt mass. -/
theorem sum_primeTower_head_eq_mertens (Y : ℕ) :
    (∑ p ∈ (Icc 1 Y).filter Nat.Prime,
      ∑ k ∈ Icc 1 Y, if p ∣ k then Λ k / (k : ℝ) else 0) = mertensSum Y := by
  rw [sum_comm, mertensSum]
  apply sum_congr rfl
  intro k hk
  by_cases hΛ : Λ k = 0
  · simp only [hΛ, zero_div, ite_self, sum_const_zero]
  · have hpow := vonMangoldt_ne_zero_iff.mp hΛ
    have hq : k.minFac.Prime := Nat.minFac_prime hpow.ne_one
    have hmem : k.minFac ∈ (Icc 1 Y).filter Nat.Prime := mem_filter.mpr
      ⟨mem_Icc.mpr ⟨hq.pos,
        (Nat.le_of_dvd (mem_Icc.mp hk).1 (Nat.minFac_dvd k)).trans (mem_Icc.mp hk).2⟩, hq⟩
    have hterm (p : ℕ) (hp : p ∈ (Icc 1 Y).filter Nat.Prime) :
        (if p ∣ k then Λ k / (k : ℝ) else 0) =
          if p = k.minFac then Λ k / (k : ℝ) else 0 := by
      have hp' := (mem_filter.mp hp).2
      have hiff : p ∣ k ↔ p = k.minFac := by
        constructor
        · intro hpk
          have h := hpow.minFac_pow_factorization_eq
          rw [← h] at hpk
          exact (Nat.prime_dvd_prime_iff_eq hp' hq).mp (hp'.dvd_of_dvd_pow hpk)
        · rintro rfl
          exact Nat.minFac_dvd k
      simp only [hiff]
    rw [sum_congr rfl hterm, sum_ite_eq', if_pos hmem]

/-- The full mass left in towers below the cutoff is an exact difference of Mertens sums. -/
theorem sum_primeTowerRemainder_eq (Y : ℕ) :
    (∑ p ∈ (Icc 1 Y).filter Nat.Prime, primeTowerRemainder p Y) =
      primeActivityMass Y - mertensSum Y := by
  simp only [primeTowerRemainder, sum_sub_distrib, sum_primeTower_head_eq_mertens]
  rfl

/-- An absolute bound for all low-prime tower tails. -/
def primeTowerTailMassConstant : ℝ :=
  |(Real.log 4 + 4) + (8 + _root_.RHTower.Mertens.mertensTail)| + |Real.log 4 + 4| + 8

theorem primeTowerTailMassConstant_nonneg : 0 ≤ primeTowerTailMassConstant := by
  unfold primeTowerTailMassConstant
  positivity

/-- Low-prime tower tails have bounded total mass, uniformly in their cutoff. -/
theorem sum_primeTowerRemainder_le (Y : ℕ) :
    (∑ p ∈ (Icc 1 Y).filter Nat.Prime, primeTowerRemainder p Y) ≤
      primeTowerTailMassConstant := by
  by_cases hY : Y = 0
  · subst Y
    simpa only [Icc_eq_empty_of_lt (by omega : (0 : ℕ) < 1), filter_empty, sum_empty]
      using primeTowerTailMassConstant_nonneg
  · have hY1 : 1 ≤ Y := Nat.one_le_iff_ne_zero.mpr hY
    rw [sum_primeTowerRemainder_eq]
    have hA := primeActivityMass_le_primePoleScale_add_eight Y
    have hB := (abs_le.mp (primePoleScale_logarithmic hY1)).2
    have hM := (abs_le.mp (_root_.RHTower.Mertens.mertens_first Y hY1)).1
    change -(Real.log 4 + 4) ≤ mertensSum Y - Real.log Y at hM
    unfold primeTowerTailMassConstant
    linarith only [hA, hB, hM,
      le_abs_self ((Real.log 4 + 4) + (8 + _root_.RHTower.Mertens.mertensTail)),
      le_abs_self (Real.log 4 + 4)]

/-- A single omitted tower has mass at most one. -/
theorem primeTowerRemainder_le_one {p : ℕ} (hp : p.Prime) (Y : ℕ) :
    primeTowerRemainder p Y ≤ 1 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hhead : 0 ≤ ∑ k ∈ Icc 1 Y, if p ∣ k then Λ k / (k : ℝ) else 0 :=
    sum_nonneg fun k _ => by
      split_ifs
      · exact div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg k)
      · exact le_rfl
  calc
    primeTowerRemainder p Y ≤ Real.log p / ((p : ℝ) - 1) := sub_le_self _ hhead
    _ ≤ 1 := (div_le_one (sub_pos.mpr hp1)).mpr (Real.log_le_sub_one_of_pos hp0)

private theorem prime_excess_nonneg {p : ℕ} (hp : p.Prime) :
    0 ≤ Real.log p / ((p : ℝ) - 1) - Real.log p / p := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  exact sub_nonneg.mpr (div_le_div_of_nonneg_left (Real.log_natCast_nonneg p)
    (sub_pos.mpr hp1) (sub_le_self _ zero_le_one))

/-- Discarding the nondivisibility indicators leaves the high-prime charge plus bounded mass. -/
theorem primeTower_mass_sub_highPrimePoleMass_bounds (Q Y : ℕ) :
    0 ≤ (∑ p ∈ (Icc 1 Q).filter Nat.Prime, primeTowerRemainder p Y) -
        highPrimePoleMass Y Q ∧
      (∑ p ∈ (Icc 1 Q).filter Nat.Prime, primeTowerRemainder p Y) -
        highPrimePoleMass Y Q ≤ primeTowerTailMassConstant + 8 := by
  let P := (Icc 1 Q).filter Nat.Prime
  let L := P.filter (fun p => p ≤ Y)
  have hL : L ⊆ (Icc 1 Y).filter Nat.Prime := by
    intro p hp
    obtain ⟨hpP, hpY⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp (mem_filter.mp hpP).1).1, hpY⟩,
      (mem_filter.mp hpP).2⟩
  have hlow : (∑ p ∈ L, primeTowerRemainder p Y) ≤ primeTowerTailMassConstant :=
    (sum_le_sum_of_subset_of_nonneg hL (fun p hp _ =>
      primeTowerRemainder_nonneg (mem_filter.mp hp).2 Y)).trans (sum_primeTowerRemainder_le Y)
  have hexcess : (∑ p ∈ P,
      (Real.log p / ((p : ℝ) - 1) - Real.log p / p)) ≤ 8 := by
    rw [sum_sub_distrib]
    change primeActivityMass Q - primePoleScale Q ≤ 8
    linarith only [primeActivityMass_le_primePoleScale_add_eight Q]
  have hid : (∑ p ∈ P, primeTowerRemainder p Y) - highPrimePoleMass Y Q =
      ∑ p ∈ P, if Y < p then
        Real.log p / ((p : ℝ) - 1) - Real.log p / p else primeTowerRemainder p Y := by
    rw [highPrimePoleMass, ← sum_sub_distrib]
    apply sum_congr rfl
    intro p _
    by_cases hp : Y < p
    · rw [if_pos hp, if_pos hp, primeTowerRemainder_eq_of_lt hp]
    · rw [if_neg hp, if_neg hp, sub_zero]
  change 0 ≤ (∑ p ∈ P, primeTowerRemainder p Y) - highPrimePoleMass Y Q ∧ _
  rw [hid]
  constructor
  · exact sum_nonneg fun p hp => by
      split_ifs
      · exact prime_excess_nonneg (mem_filter.mp hp).2
      · exact primeTowerRemainder_nonneg (mem_filter.mp hp).2 Y
  · calc
      _ ≤ (∑ p ∈ P, if p ≤ Y then primeTowerRemainder p Y else 0) +
          ∑ p ∈ P, (Real.log p / ((p : ℝ) - 1) - Real.log p / p) := by
        rw [← sum_add_distrib]
        apply sum_le_sum
        intro p hp
        by_cases hpY : Y < p
        · simp only [if_pos hpY, if_neg (not_le.mpr hpY), zero_add, le_refl]
        · simp only [if_neg hpY, if_pos (Nat.le_of_not_lt hpY)]
          exact le_add_of_nonneg_right (prime_excess_nonneg (mem_filter.mp hp).2)
      _ ≤ primeTowerTailMassConstant + 8 := by
        rw [← sum_filter]
        exact add_le_add hlow hexcess

/-- A coherent row has the high-prime receiving mass, up to bounded mass and prime incidence. -/
theorem abs_completedPrimeDilationTail_coherent_sub_le (Q Y n : ℕ) (b : ℝ) :
    |completedPrimeDilationTail Q (primeIncidenceCoefficients (fun _ => b)) Y n -
        b * highPrimePoleMass Y Q| ≤
      |b| * (primeTowerTailMassConstant + 8 +
        ∑ p ∈ (Icc 1 Q).filter Nat.Prime, if p ∣ n then (1 : ℝ) else 0) := by
  let P := (Icc 1 Q).filter Nat.Prime
  let T := ∑ p ∈ P, primeTowerRemainder p Y
  let V := ∑ p ∈ P, if p ∣ n then primeTowerRemainder p Y else 0
  let W := ∑ p ∈ P, if p ∣ n then (1 : ℝ) else 0
  have hV0 : 0 ≤ V := sum_nonneg fun p hp => by
    split_ifs
    · exact primeTowerRemainder_nonneg (mem_filter.mp hp).2 Y
    · exact le_rfl
  have hVW : V ≤ W := sum_le_sum fun p hp => by
    split_ifs
    · exact primeTowerRemainder_le_one (mem_filter.mp hp).2 Y
    · exact le_rfl
  have hW0 : 0 ≤ W := hV0.trans hVW
  have hT := primeTower_mass_sub_highPrimePoleMass_bounds Q Y
  have hrow : completedPrimeDilationTail Q (primeIncidenceCoefficients (fun _ => b)) Y n =
      b * (T - V) := by
    rw [completedPrimeDilationTail_primeIncidence_eq]
    dsimp only [T, V]
    rw [← sum_sub_distrib, mul_sum]
    apply sum_congr rfl
    intro p _
    split_ifs <;> ring
  have herror : |T - V - highPrimePoleMass Y Q| ≤ primeTowerTailMassConstant + 8 + W := by
    rw [abs_le]
    change 0 ≤ T - highPrimePoleMass Y Q ∧
      T - highPrimePoleMass Y Q ≤ primeTowerTailMassConstant + 8 at hT
    constructor <;> linarith only [hT.1, hT.2, hV0, hVW, hW0, primeTowerTailMassConstant_nonneg]
  rw [hrow, ← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_left herror (abs_nonneg b)

private theorem abs_positivePart_add_sub_le {x δ : ℝ} (hδ : 0 ≤ δ) :
    |max (x + δ) 0 - max x 0| ≤ δ := by
  by_cases hx : 0 ≤ x
  · rw [max_eq_left (add_nonneg hx hδ), max_eq_left hx]
    have he : x + δ - x = δ := by ring
    rw [he, abs_of_nonneg hδ]
  · have hx0 : x ≤ 0 := (lt_of_not_ge hx).le
    by_cases hy : 0 ≤ x + δ
    · rw [max_eq_left hy, max_eq_right hx0, sub_zero, abs_of_nonneg hy]
      linarith only [hx0]
    · rw [max_eq_right (lt_of_not_ge hy).le, max_eq_right hx0, sub_self, abs_zero]
      exact hδ

/-- The finite quotient changes the high-prime logarithmic ramp by at most `log 2`. -/
theorem abs_highPrimePoleMass_natDiv_sub_ramp_le {Q N n : ℕ}
    (hQ : 1 ≤ Q) (hn : 1 ≤ n) (hnN : n ≤ N) :
    |highPrimePoleMass (N / n) Q - max (Real.log Q + Real.log n - Real.log N) 0| ≤
      2 * |(Real.log 4 + 4) + (8 + _root_.RHTower.Mertens.mertensTail)| + Real.log 2 := by
  have hY : 1 ≤ N / n := (Nat.one_le_div_iff hn).mpr hnN
  have hmass := abs_highPrimePoleMass_sub_log_le hY hQ
  have hfloor := abs_positivePart_add_sub_le (x := Real.log Q + Real.log n - Real.log N)
    (floorDefect_nonneg hn hnN)
  have he : Real.log Q + Real.log n - Real.log N + floorDefect N n =
      Real.log Q - Real.log (N / n : ℕ) := by unfold floorDefect; ring
  rw [he] at hfloor
  exact (abs_sub_le _ _ _).trans (add_le_add hmass (hfloor.trans (floorDefect_le_log_two hn hnN)))

/-- The completed coherent row is the logarithmic ramp plus a bounded incidence error. -/
theorem abs_completedPrimeDilationTail_coherent_sub_ramp_le {Q N n : ℕ}
    (hQ : 1 ≤ Q) (hn : 1 ≤ n) (hnN : n ≤ N) (b : ℝ) :
    |completedPrimeDilationTail Q (primeIncidenceCoefficients (fun _ => b)) (N / n) n -
        b * max (Real.log Q + Real.log n - Real.log N) 0| ≤
      |b| * (primeTowerTailMassConstant + 8 +
        2 * |(Real.log 4 + 4) + (8 + _root_.RHTower.Mertens.mertensTail)| + Real.log 2 +
          ∑ p ∈ (Icc 1 Q).filter Nat.Prime, if p ∣ n then (1 : ℝ) else 0) := by
  have hmass := abs_completedPrimeDilationTail_coherent_sub_le Q (N / n) n b
  have hramp := mul_le_mul_of_nonneg_left
    (abs_highPrimePoleMass_natDiv_sub_ramp_le hQ hn hnN) (abs_nonneg b)
  rw [← abs_mul, mul_sub] at hramp
  refine (abs_sub_le _ (b * highPrimePoleMass (N / n) Q) _).trans
    ((add_le_add hmass hramp).trans_eq ?_)
  ring

/-- No row has more coherent tail mass than the complete prime activity. -/
theorem abs_completedPrimeDilationTail_coherent_le_activity (Q Y n : ℕ) (b : ℝ) :
    |completedPrimeDilationTail Q (primeIncidenceCoefficients (fun _ => b)) Y n| ≤
      |b| * primeActivityMass Q := by
  rw [completedPrimeDilationTail_primeIncidence_eq]
  have hsum : (∑ p ∈ (Icc 1 Q).filter Nat.Prime,
      if p ∣ n then (0 : ℝ) else b * primeTowerRemainder p Y) =
      b * ∑ p ∈ (Icc 1 Q).filter Nat.Prime,
        if p ∣ n then (0 : ℝ) else primeTowerRemainder p Y := by
    rw [mul_sum]
    exact sum_congr rfl fun p _ => by split_ifs <;> ring
  have hnonneg : 0 ≤ ∑ p ∈ (Icc 1 Q).filter Nat.Prime,
      if p ∣ n then (0 : ℝ) else primeTowerRemainder p Y := by
    apply sum_nonneg
    intro p hp
    split_ifs
    · exact le_rfl
    · exact primeTowerRemainder_nonneg (mem_filter.mp hp).2 Y
  rw [hsum, abs_mul, abs_of_nonneg hnonneg]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg b)
  apply sum_le_sum
  intro p hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2.one_lt
  split_ifs
  · exact div_nonneg (Real.log_natCast_nonneg p) (sub_nonneg.mpr hp1.le)
  · exact sub_le_self _ (sum_nonneg fun k _ => by
      split_ifs
      · exact div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg k)
      · exact le_rfl)

#print axioms sum_primeTowerRemainder_eq
#print axioms sum_primeTowerRemainder_le
#print axioms primeTower_mass_sub_highPrimePoleMass_bounds
#print axioms abs_completedPrimeDilationTail_coherent_sub_le
#print axioms abs_completedPrimeDilationTail_coherent_sub_ramp_le
#print axioms abs_completedPrimeDilationTail_coherent_le_activity

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
