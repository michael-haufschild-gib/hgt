import GaloisForLFunctions.RHTower.CCMPrimeDeficitCoprimeBalance
import GaloisForLFunctions.RHTower.CCMPrimeDeficitDilationLimit
import GaloisForLFunctions.RHTower.EulerDeletionTruncatedDivisorPairCorrelation
import GaloisForLFunctions.RHTower.Sieve.GcdSumTotient

/-!
# Cancellation of complete coprime rows

Every coprime row of the actual centered reconstruction collapses to the
source on the divisors of its row index. For an index greater than one,
the limiting source constant cancels exactly. This gives a decaying bound
for the entire row, retaining all its signed partners.
-/

noncomputable section
open scoped BigOperators

namespace RHTower

def ccmPrimeDeficitCoprimeRow (a : ℕ) (T : ℝ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 ⌊Real.exp T⌋₊).filter (fun n => a.Coprime n),
    ccmPrimeDeficitMobiusCenteredWork (T - Real.log n)

private theorem divisor_filter_eq {a N : ℕ} (ha : a ∈ Finset.Icc 1 N) :
    (Finset.Icc 1 N).filter (fun d => d ∣ a) = a.divisors := by
  have h := Sieve.divisors_gcd_eq_filter (b := a)
    (Finset.mem_Icc.mp ha).1 (Finset.mem_Icc.mp ha).2
  simpa only [Nat.gcd_self, and_self] using h.symm

/-- Every partner in the coprime row is included before the common-divisor
sum collapses to source values. -/
theorem ccmPrimeDeficitCoprimeRow_eq_divisor_source {a : ℕ} {T : ℝ}
    (ha : a ∈ Finset.Icc 1 ⌊Real.exp T⌋₊) :
    ccmPrimeDeficitCoprimeRow a T =
      ∑ d ∈ a.divisors, moebiusCoeff d * ccmPrimeDeficitDilationRemainder (T - Real.log d) := by
  rw [ccmPrimeDeficitCoprimeRow,
    ← weighted_moebius_divisor_filter_eq_coprime_filter _ a ha]
  have hrow (d : ℕ) (hd : d ∈ (Finset.Icc 1 ⌊Real.exp T⌋₊).filter (fun d => d ∣ a)) :
      (∑ n ∈ (Finset.Icc 1 ⌊Real.exp T⌋₊).filter (fun n => d ∣ n),
        ccmPrimeDeficitMobiusCenteredWork (T - Real.log n)) =
          ccmPrimeDeficitDilationRemainder (T - Real.log d) := by
    have hdm := Finset.mem_filter.mp hd
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hdm.1).1
    have hdT : (d : ℝ) ≤ Real.exp T :=
      (Nat.le_floor_iff (Real.exp_pos T).le).mp (Finset.mem_Icc.mp hdm.1).2
    rw [logarithmicDilationSum_eq_filteredMultiples _ T (Finset.mem_Icc.mp hdm.1).1,
      logarithmicDilationSum_ccmPrimeDeficitMobiusCenteredWork
        (sub_nonneg.mpr ((Real.log_le_iff_le_exp hdpos).mpr hdT))]
  rw [Finset.sum_congr rfl (fun d hd => congrArg (fun x => (ArithmeticFunction.moebius d : ℝ) * x)
    (hrow d hd)), divisor_filter_eq ha]
  rfl

/-- The constant source cancels on every nontrivial row. -/
theorem ccmPrimeDeficitCoprimeRow_eq_divisor_transient {a : ℕ} {T : ℝ}
    (ha : a ∈ Finset.Icc 1 ⌊Real.exp T⌋₊) (ha1 : a ≠ 1) :
    ccmPrimeDeficitCoprimeRow a T =
      ∑ d ∈ a.divisors, moebiusCoeff d *
        (ccmPrimeDeficitDilationRemainder (T - Real.log d) - ccmPrimeDeficitDilationLimit) := by
  have hm : (∑ d ∈ a.divisors, moebiusCoeff d) = 0 := by
    unfold moebiusCoeff
    rw [← Int.cast_sum, sum_moebius_divisors, if_neg ha1, Int.cast_zero]
  rw [ccmPrimeDeficitCoprimeRow_eq_divisor_source ha]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hm, zero_mul, sub_zero]

/-- A decaying bound for a complete signed coprime row, with the exact
divisor mass of its index. -/
theorem abs_ccmPrimeDeficitCoprimeRow_le {a : ℕ} {T : ℝ}
    (ha : a ∈ Finset.Icc 1 ⌊Real.exp T⌋₊) (ha1 : a ≠ 1) :
    |ccmPrimeDeficitCoprimeRow a T| ≤
      Real.exp (-T) * (T + 14) / 4 * ∑ d ∈ a.divisors, (d : ℝ) := by
  rw [ccmPrimeDeficitCoprimeRow_eq_divisor_transient ha ha1, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
  intro d hd
  have hapos : 0 < a := (Finset.mem_Icc.mp ha).1
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hd) hapos
  have hdposR : (0 : ℝ) < d := by exact_mod_cast hdpos
  have hdT : (d : ℝ) ≤ Real.exp T :=
    (Nat.le_floor_iff (Real.exp_pos T).le).mp
      ((Nat.le_of_dvd hapos (Nat.dvd_of_mem_divisors hd)).trans (Finset.mem_Icc.mp ha).2)
  have hlog : Real.log d ≤ T := (Real.log_le_iff_le_exp hdposR).mpr hdT
  have hlog0 : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast hdpos)
  have he : Real.exp (-(T - Real.log d)) = Real.exp (-T) * d := by
    rw [show -(T - Real.log d) = -T + Real.log d by ring,
      Real.exp_add, Real.exp_log hdposR]
  rw [abs_mul]
  calc
    _ ≤ Real.exp (-(T - Real.log d)) * (T - Real.log d + 14) / 4 := by
      simpa only [one_mul] using mul_le_mul (abs_moebiusCoeff_le_one d)
        (abs_ccmPrimeDeficitDilationRemainder_sub_limit_le (sub_nonneg.mpr hlog))
        (abs_nonneg _) zero_le_one
    _ ≤ Real.exp (-T) * d * (T + 14) / 4 := by
      rw [he]
      gcongr
      linarith only [hlog0]
    _ = _ := by ring

private theorem divisor_mass_le {a : ℕ} (ha : 0 < a) :
    (∑ d ∈ a.divisors, (d : ℝ)) ≤ (a : ℝ) * (1 + Real.log a) := by
  have hs : a.divisors ⊆ Finset.Icc 1 a := by
    intro d hd
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hd) ha,
      Nat.le_of_dvd ha (Nat.dvd_of_mem_divisors hd)⟩
  have hh : (∑ d ∈ a.divisors, (d : ℝ)⁻¹) ≤ 1 + Real.log a := by
    calc
      _ ≤ ∑ d ∈ Finset.Icc 1 a, (d : ℝ)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hs (fun d _ _ => by positivity)
      _ = harmonic a := by
        simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      _ ≤ _ := harmonic_le_one_add_log a
  have he : (∑ d ∈ a.divisors, (d : ℝ)) =
      (a : ℝ) * ∑ d ∈ a.divisors, (d : ℝ)⁻¹ := by
    rw [← Nat.sum_div_divisors a (fun d => (d : ℝ)), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Nat.cast_div_charZero (Nat.dvd_of_mem_divisors hd), div_eq_mul_inv]
  rw [he]
  exact mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg a)

theorem abs_ccmPrimeDeficitCoprimeRow_le_logMass {a : ℕ} {T : ℝ}
    (hT : 0 ≤ T) (ha : a ∈ Finset.Icc 1 ⌊Real.exp T⌋₊) (ha1 : a ≠ 1) :
    |ccmPrimeDeficitCoprimeRow a T| ≤
      Real.exp (-T) * (T + 14) / 4 * ((a : ℝ) * (1 + Real.log a)) :=
  (abs_ccmPrimeDeficitCoprimeRow_le ha ha1).trans
    (mul_le_mul_of_nonneg_left (divisor_mass_le (Finset.mem_Icc.mp ha).1) (by positivity))

/-- Every complete nontrivial row below the square-root cutoff decays
uniformly, even though each row includes all partners up to `exp T`. -/
theorem abs_ccmPrimeDeficitCoprimeRow_le_halfCutoff {a : ℕ} {T : ℝ}
    (hT : 0 ≤ T) (ha : a ∈ Finset.Icc 2 ⌊Real.exp (T / 2)⌋₊) :
    |ccmPrimeDeficitCoprimeRow a T| ≤
      Real.exp (-(T / 2)) * (T + 14) * (1 + T / 2) / 4 := by
  have hapos : 0 < a := by have := (Finset.mem_Icc.mp ha).1; omega
  have haT : (a : ℝ) ≤ Real.exp (T / 2) :=
    (Nat.le_floor_iff (Real.exp_pos _).le).mp (Finset.mem_Icc.mp ha).2
  have hlog : Real.log a ≤ T / 2 :=
    (Real.log_le_iff_le_exp (by exact_mod_cast hapos)).mpr haT
  have haFull : a ∈ Finset.Icc 1 ⌊Real.exp T⌋₊ := Finset.mem_Icc.mpr ⟨hapos,
    (Finset.mem_Icc.mp ha).2.trans
      (Nat.floor_mono (Real.exp_le_exp.mpr (by linarith only [hT])))⟩
  have hmass : (∑ d ∈ a.divisors, (d : ℝ)) ≤ Real.exp (T / 2) * (1 + T / 2) := by
    refine (divisor_mass_le hapos).trans ?_
    gcongr
  have he : Real.exp (-T) * Real.exp (T / 2) = Real.exp (-(T / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ Real.exp (-T) * (T + 14) / 4 * ∑ d ∈ a.divisors, (d : ℝ) :=
      abs_ccmPrimeDeficitCoprimeRow_le haFull (by have := (Finset.mem_Icc.mp ha).1; omega)
    _ ≤ Real.exp (-T) * (T + 14) / 4 * (Real.exp (T / 2) * (1 + T / 2)) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = _ := by
      calc
        _ = (Real.exp (-T) * Real.exp (T / 2)) * (T + 14) * (1 + T / 2) / 4 := by ring
        _ = _ := by rw [he]

end RHTower
