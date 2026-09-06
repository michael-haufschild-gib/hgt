import GaloisForLFunctions.RHTower.ChronologicalLambertRepair

/-!
# Arithmetic boundary of chronological response repair

The actual nonlinear repair after m steps is X-X^(m+1)/(1+X)^m.
Its unique Lambert inverse agrees with Möbius through m, changes by -1
at m+1, and equals μ(m+2)+m at m+2 for m≥2. A fixed coefficient
budget therefore confines deep repair truncations to Möbius prefixes,
with at most the single terminal correction. No L² convergence is asserted.
-/

noncomputable section
namespace RHTower

def chronologicalFermiRepairSeries : ℕ → PowerSeries ℤ
  | 0 => 0
  | n+1 => chronologicalFermiSeries * (1+chronologicalFermiRepairSeries n)

theorem chronologicalFermiRepairSeries_error (m : ℕ) :
    PowerSeries.X - chronologicalFermiRepairSeries m =
      PowerSeries.X * chronologicalFermiSeries ^ m := by
  induction m with
  | zero => simp [chronologicalFermiRepairSeries]
  | succ m ih =>
    have hf := chronologicalFermiSeries_equation
    rw [chronologicalFermiRepairSeries]
    calc
      _ = chronologicalFermiSeries * (PowerSeries.X-chronologicalFermiRepairSeries m) := by
        linear_combination -hf
      _ = _ := by rw [ih, pow_succ]; ring

theorem chronologicalFermiRepairSeries_closed (m : ℕ) :
    chronologicalFermiRepairSeries m = PowerSeries.X -
      PowerSeries.X ^ (m+1) * chronologicalAlternatingSeries ^ m := by
  have he := chronologicalFermiRepairSeries_error m
  have hmul : PowerSeries.X * chronologicalFermiSeries ^ m =
      PowerSeries.X ^ (m+1) * chronologicalAlternatingSeries ^ m := by
    rw [chronologicalFermiSeries, mul_pow, pow_succ]
    ring
  rw [hmul] at he
  linear_combination -he

theorem chronologicalFermiRepairSeries_prefix (m k : ℕ) (hk : k ≤ m) :
    PowerSeries.coeff k (chronologicalFermiRepairSeries m) =
      PowerSeries.coeff k (PowerSeries.X : PowerSeries ℤ) := by
  rw [chronologicalFermiRepairSeries_closed, map_sub, PowerSeries.coeff_X_pow_mul',
    if_neg (by omega), sub_zero]

theorem chronologicalAlternatingSeries_power_coeff_one (m : ℕ) :
    PowerSeries.coeff 1 (chronologicalAlternatingSeries ^ m) = -(m:ℤ) := by
  cases m with
  | zero => simp
  | succ m =>
    rw [chronologicalAlternatingSeries_rescale, ← map_pow,
      PowerSeries.mk_one_pow_eq_mk_choose_add, PowerSeries.coeff_rescale, PowerSeries.coeff_mk]
    simp

theorem chronologicalFermiRepairSeries_first_two_coefficients (m : ℕ) :
    PowerSeries.coeff (m+2) (chronologicalFermiRepairSeries (m+1)) = -1 ∧
    PowerSeries.coeff (m+3) (chronologicalFermiRepairSeries (m+1)) = ((m:ℤ)+1) := by
  constructor
  · rw [chronologicalFermiRepairSeries_closed, map_sub, PowerSeries.coeff_X_pow_mul']
    rw [if_pos (by omega), show m+2-(m+1+1)=0 by omega]
    simp [PowerSeries.coeff_X, show m+2 ≠ 1 by omega, chronologicalAlternatingSeries]
  · rw [chronologicalFermiRepairSeries_closed, map_sub, PowerSeries.coeff_X_pow_mul']
    rw [if_pos (by omega), show m+3-(m+1+1)=1 by omega,
      chronologicalAlternatingSeries_power_coeff_one]
    simp [PowerSeries.coeff_X, show m+3 ≠ 1 by omega]

def chronologicalRepairArithmeticSource (m : ℕ) : ArithmeticFunction ℤ :=
  ⟨fun k => PowerSeries.coeff k (chronologicalFermiRepairSeries m), by
    rw [chronologicalFermiRepairSeries_prefix m 0 (Nat.zero_le m)]
    simp⟩

def chronologicalRepairArithmetic (m : ℕ) : ArithmeticFunction ℤ :=
  ArithmeticFunction.moebius * chronologicalRepairArithmeticSource m

theorem chronologicalRepairArithmetic_reconstruct (m : ℕ) :
    chronologicalLambertSeries (chronologicalRepairArithmetic m) = chronologicalFermiRepairSeries m := by
  apply PowerSeries.ext
  intro k
  simp only [chronologicalLambertSeries, PowerSeries.coeff_mk]
  rw [← ArithmeticFunction.coe_zeta_mul_apply]
  have he : (ArithmeticFunction.zeta : ArithmeticFunction ℤ) * chronologicalRepairArithmetic m =
      chronologicalRepairArithmeticSource m := by
    rw [chronologicalRepairArithmetic, ← mul_assoc,
      ArithmeticFunction.coe_zeta_mul_moebius, one_mul]
  rw [he]
  rfl

theorem chronologicalRepairArithmetic_prefix (m k : ℕ) (hk : k ≤ m) :
    chronologicalRepairArithmetic m k = ArithmeticFunction.moebius k := by
  unfold chronologicalRepairArithmetic
  calc
    (ArithmeticFunction.moebius * chronologicalRepairArithmeticSource m) k =
        (ArithmeticFunction.moebius * 1) k := by
      rw [ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
      apply Finset.sum_congr rfl
      intro x hx
      congr 1
      change PowerSeries.coeff x.2 (chronologicalFermiRepairSeries m) = _
      rw [chronologicalFermiRepairSeries_prefix m x.2
        ((Nat.divisor_le (Nat.snd_mem_divisors_of_mem_antidiagonal hx)).trans hk)]
      simp [ArithmeticFunction.one_apply, PowerSeries.coeff_X]
    _ = _ := by rw [mul_one]

theorem chronologicalRepairArithmetic_first_change (m : ℕ) (hm : 1 ≤ m) :
    chronologicalRepairArithmetic m (m+1) = ArithmeticFunction.moebius (m+1) - 1 := by
  have he := congrArg (PowerSeries.coeff (m+1)) (chronologicalRepairArithmetic_reconstruct m)
  have hc : PowerSeries.coeff (m+1) (chronologicalFermiRepairSeries m) = -1 := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
    simpa [Nat.succ_eq_add_one, add_assoc] using (chronologicalFermiRepairSeries_first_two_coefficients j).1
  rw [hc] at he
  simp only [chronologicalLambertSeries, PowerSeries.coeff_mk] at he
  have hmem := Nat.mem_divisors_self (m+1) (by omega)
  have hmu : (∑ d ∈ (m+1).divisors, ArithmeticFunction.moebius d) = 0 := by
    rw [← ArithmeticFunction.coe_zeta_mul_apply, ArithmeticFunction.coe_zeta_mul_moebius]
    simp [show m ≠ 0 by omega]
  have hs : (∑ d ∈ (m+1).divisors.erase (m+1), chronologicalRepairArithmetic m d) =
      ∑ d ∈ (m+1).divisors.erase (m+1), ArithmeticFunction.moebius d := by
    apply Finset.sum_congr rfl
    intro d hd
    have hh := Finset.mem_erase.mp hd
    have hle := Nat.divisor_le hh.2
    exact chronologicalRepairArithmetic_prefix m d (by omega)
  rw [← Finset.sum_erase_add _ _ hmem] at he hmu
  rw [hs] at he
  linarith

theorem chronologicalProperDivisor_le (m d : ℕ) (hm : 2 ≤ m)
    (hd : d ∈ (m+2).divisors) (hne : d ≠ m+2) : d ≤ m := by
  have hdiv := (Nat.mem_divisors.mp hd).1
  have hdpos := Nat.pos_of_mem_divisors hd
  obtain ⟨j, hj⟩ := hdiv
  have hj2 : 2 ≤ j := by
    by_contra h
    have hj01 : j=0 ∨ j=1 := by omega
    rcases hj01 with rfl | rfl
    · simp at hj
    · simp at hj
      exact hne hj.symm
  have hh : 2*d ≤ m+2 := by nlinarith
  omega

theorem chronologicalRepairArithmetic_boundary (m : ℕ) (hm : 2 ≤ m) :
    chronologicalRepairArithmetic m (m+2) = ArithmeticFunction.moebius (m+2) + (m:ℤ) := by
  have he := congrArg (PowerSeries.coeff (m+2)) (chronologicalRepairArithmetic_reconstruct m)
  have hc : PowerSeries.coeff (m+2) (chronologicalFermiRepairSeries m) = (m:ℤ) := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
    simpa [Nat.succ_eq_add_one, add_assoc] using (chronologicalFermiRepairSeries_first_two_coefficients j).2
  rw [hc] at he
  simp only [chronologicalLambertSeries, PowerSeries.coeff_mk] at he
  have hmem := Nat.mem_divisors_self (m+2) (by omega)
  have hmu : (∑ d ∈ (m+2).divisors, ArithmeticFunction.moebius d) = 0 := by
    rw [← ArithmeticFunction.coe_zeta_mul_apply, ArithmeticFunction.coe_zeta_mul_moebius]
    simp
  have hs : (∑ d ∈ (m+2).divisors.erase (m+2), chronologicalRepairArithmetic m d) =
      ∑ d ∈ (m+2).divisors.erase (m+2), ArithmeticFunction.moebius d := by
    apply Finset.sum_congr rfl
    intro d hd
    have hh := Finset.mem_erase.mp hd
    exact chronologicalRepairArithmetic_prefix m d (chronologicalProperDivisor_le m d hm hh.2 hh.1)
  rw [← Finset.sum_erase_add _ _ hmem] at he hmu
  rw [hs] at he
  linarith

theorem chronologicalRepairArithmetic_boundary_cost (m : ℕ) (hm : 2 ≤ m) :
    (m:ℤ)-1 ≤ |chronologicalRepairArithmetic m (m+2)| := by
  rw [chronologicalRepairArithmetic_boundary m hm]
  have hb := ArithmeticFunction.abs_moebius_le_one (n := m+2)
  have hlo := (abs_le.mp hb).1
  have habs := le_abs_self (ArithmeticFunction.moebius (m+2)+(m:ℤ))
  linarith

theorem chronologicalRepairArithmetic_cutoff_boundary (m N B : ℕ) (hm : 2 ≤ m)
    (hB : ∀ k ≤ N, |chronologicalRepairArithmetic m k| ≤ (B:ℤ)) :
    N ≤ m+1 ∨ m ≤ B+1 := by
  by_cases hN : N ≤ m+1
  · exact Or.inl hN
  · have hh := hB (m+2) (by omega)
    have hlo := chronologicalRepairArithmetic_boundary_cost m hm
    right
    omega

theorem chronologicalRepairArithmetic_bounded_prefix_classification (m N B k : ℕ)
    (hm : B+1 < m) (hk : k ≤ N)
    (hB : ∀ j ≤ N, |chronologicalRepairArithmetic m j| ≤ (B:ℤ)) :
    chronologicalRepairArithmetic m k =
      ArithmeticFunction.moebius k - if k = m+1 then 1 else 0 := by
  have hm2 : 2 ≤ m := by omega
  have hN : N ≤ m+1 := (chronologicalRepairArithmetic_cutoff_boundary m N B hm2 hB).resolve_right (by omega)
  by_cases hkm : k = m+1
  · subst k
    simpa using chronologicalRepairArithmetic_first_change m (by omega)
  · rw [if_neg hkm, sub_zero]
    exact chronologicalRepairArithmetic_prefix m k (by omega)

end RHTower
