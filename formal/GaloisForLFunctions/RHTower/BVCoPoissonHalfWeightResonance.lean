import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Critical eta half-density resonance

The reflected critical eta Mellin vector is nonzero on every positive odd and even Gamma-pole
lattice point.  Therefore no nonzero Euler polynomial can cancel either infinite lattice.  This
is the exact algebraic obstruction behind exclusion of the critical half-weight seed from both
parities of Burnol's extended-property-S topology.
-/

open Complex

namespace RHTower
noncomputable section

def dirichletEta (s : ℂ) : ℂ :=
  (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s

lemma cos_pi_mul_three_halves_add_two_nat_div_two_ne_zero (n : ℕ) :
    Complex.cos ((Real.pi : ℂ) * ((3 / 2 : ℂ) + 2 * n) / 2) ≠ 0 := by
  rw [show (Real.pi : ℂ) * ((3 / 2 : ℂ) + 2 * n) / 2 =
      ((3 * Real.pi / 4 + n * Real.pi : ℝ) : ℂ) by
    push_cast
    ring]
  rw [← Complex.ofReal_cos]
  norm_cast
  rw [Real.cos_add_nat_mul_pi]
  rw [show 3 * Real.pi / 4 = -Real.pi / 4 + (1 : ℕ) * Real.pi by ring,
    Real.cos_add_nat_mul_pi]
  rw [show -Real.pi / 4 = -(Real.pi / 4) by ring, Real.cos_neg, Real.cos_pi_div_four]
  positivity

lemma riemannZeta_neg_half_sub_two_nat_ne_zero (n : ℕ) :
    riemannZeta (-(1 / 2 : ℂ) - 2 * n) ≠ 0 := by
  let s : ℂ := (3 / 2 : ℂ) + 2 * n
  have hsneg (m : ℕ) : s ≠ -m := by
    intro h
    have hre := congrArg Complex.re h
    dsimp [s] at hre
    norm_num at hre
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hsone : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    dsimp [s] at hre
    norm_num at hre
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hfe := riemannZeta_one_sub (s := s) hsneg hsone
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  have hbase : (2 * (Real.pi : ℂ) : ℂ) ≠ 0 :=
    mul_ne_zero htwo (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hpow : (2 * (Real.pi : ℂ) : ℂ) ^ (-s) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hbase)
  have hgamma : Complex.Gamma s ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    dsimp [s]
    norm_num
    positivity
  have hcos : Complex.cos ((Real.pi : ℂ) * s / 2) ≠ 0 := by
    dsimp [s]
    exact cos_pi_mul_three_halves_add_two_nat_div_two_ne_zero n
  have hzeta : riemannZeta s ≠ 0 := by
    apply riemannZeta_ne_zero_of_one_lt_re
    dsimp [s]
    norm_num
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hrhs : 2 * (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s *
      Complex.cos ((Real.pi : ℂ) * s / 2) * riemannZeta s ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero htwo hpow) hgamma) hcos) hzeta
  rw [← hfe] at hrhs
  have harg : 1 - s = -(1 / 2 : ℂ) - 2 * n := by
    dsimp [s]
    ring
  simpa only [harg] using hrhs

lemma cos_pi_mul_five_halves_add_two_nat_div_two_ne_zero (n : ℕ) :
    Complex.cos ((Real.pi : ℂ) * ((5 / 2 : ℂ) + 2 * n) / 2) ≠ 0 := by
  rw [show (Real.pi : ℂ) * ((5 / 2 : ℂ) + 2 * n) / 2 =
      ((5 * Real.pi / 4 + n * Real.pi : ℝ) : ℂ) by
    push_cast
    ring]
  rw [← Complex.ofReal_cos]
  norm_cast
  rw [Real.cos_add_nat_mul_pi]
  rw [show 5 * Real.pi / 4 = Real.pi / 4 + (1 : ℕ) * Real.pi by ring,
    Real.cos_add_nat_mul_pi, Real.cos_pi_div_four]
  positivity

lemma riemannZeta_neg_three_halves_sub_two_nat_ne_zero (n : ℕ) :
    riemannZeta (-(3 / 2 : ℂ) - 2 * n) ≠ 0 := by
  let s : ℂ := (5 / 2 : ℂ) + 2 * n
  have hsneg (m : ℕ) : s ≠ -m := by
    intro h
    have hre := congrArg Complex.re h
    dsimp [s] at hre
    norm_num at hre
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hsone : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    dsimp [s] at hre
    norm_num at hre
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hfe := riemannZeta_one_sub (s := s) hsneg hsone
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  have hbase : (2 * (Real.pi : ℂ) : ℂ) ≠ 0 :=
    mul_ne_zero htwo (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hpow : (2 * (Real.pi : ℂ) : ℂ) ^ (-s) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hbase)
  have hgamma : Complex.Gamma s ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    dsimp [s]
    norm_num
    positivity
  have hcos : Complex.cos ((Real.pi : ℂ) * s / 2) ≠ 0 := by
    dsimp [s]
    exact cos_pi_mul_five_halves_add_two_nat_div_two_ne_zero n
  have hzeta : riemannZeta s ≠ 0 := by
    apply riemannZeta_ne_zero_of_one_lt_re
    dsimp [s]
    norm_num
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hrhs : 2 * (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s *
      Complex.cos ((Real.pi : ℂ) * s / 2) * riemannZeta s ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero htwo hpow) hgamma) hcos) hzeta
  rw [← hfe] at hrhs
  have harg : 1 - s = -(3 / 2 : ℂ) - 2 * n := by
    dsimp [s]
    ring
  simpa only [harg] using hrhs

lemma one_sub_two_cpow_three_halves_add_two_nat_ne_zero (n : ℕ) :
    1 - (2 : ℂ) ^ ((3 / 2 : ℂ) + 2 * n) ≠ 0 := by
  have hrpos : 0 < (3 / 2 : ℝ) + 2 * n := by positivity
  have hgt : 1 < (2 : ℝ) ^ ((3 / 2 : ℝ) + 2 * n) :=
    Real.one_lt_rpow (by norm_num) hrpos
  intro h
  have hpow : (2 : ℂ) ^ ((3 / 2 : ℂ) + 2 * n) = 1 := by
    exact (sub_eq_zero.mp h).symm
  have hcast : (((2 : ℝ) ^ ((3 / 2 : ℝ) + 2 * n) : ℝ) : ℂ) = 1 := by
    rw [Complex.ofReal_cpow (by norm_num)]
    simpa only [ofReal_ofNat, ofReal_add, ofReal_div, ofReal_natCast, ofReal_mul] using hpow
  have hre := congrArg Complex.re hcast
  norm_num at hre
  linarith

lemma one_sub_two_cpow_five_halves_add_two_nat_ne_zero (n : ℕ) :
    1 - (2 : ℂ) ^ ((5 / 2 : ℂ) + 2 * n) ≠ 0 := by
  have hrpos : 0 < (5 / 2 : ℝ) + 2 * n := by positivity
  have hgt : 1 < (2 : ℝ) ^ ((5 / 2 : ℝ) + 2 * n) :=
    Real.one_lt_rpow (by norm_num) hrpos
  intro h
  have hpow : (2 : ℂ) ^ ((5 / 2 : ℂ) + 2 * n) = 1 := by
    exact (sub_eq_zero.mp h).symm
  have hcast : (((2 : ℝ) ^ ((5 / 2 : ℝ) + 2 * n) : ℝ) : ℂ) = 1 := by
    rw [Complex.ofReal_cpow (by norm_num)]
    simpa only [ofReal_ofNat, ofReal_add, ofReal_div, ofReal_natCast, ofReal_mul] using hpow
  have hre := congrArg Complex.re hcast
  norm_num at hre
  linarith

lemma dirichletEta_neg_half_sub_two_nat_ne_zero (n : ℕ) :
    dirichletEta (-(1 / 2 : ℂ) - 2 * n) ≠ 0 := by
  unfold dirichletEta
  apply mul_ne_zero
  · convert one_sub_two_cpow_three_halves_add_two_nat_ne_zero n using 1
    all_goals ring
  · exact riemannZeta_neg_half_sub_two_nat_ne_zero n

lemma dirichletEta_neg_three_halves_sub_two_nat_ne_zero (n : ℕ) :
    dirichletEta (-(3 / 2 : ℂ) - 2 * n) ≠ 0 := by
  unfold dirichletEta
  apply mul_ne_zero
  · convert one_sub_two_cpow_five_halves_add_two_nat_ne_zero n using 1
    all_goals ring
  · exact riemannZeta_neg_three_halves_sub_two_nat_ne_zero n

def criticalEtaMellin (s : ℂ) : ℂ :=
  dirichletEta (s - 1 / 2) / (s - 1 / 2)

def positiveOddPole (n : ℕ) : ℂ := 1 + 2 * n

def positiveEvenPole (n : ℕ) : ℂ := 2 + 2 * n

lemma criticalEtaMellin_one_sub_positiveOddPole_ne_zero (n : ℕ) :
    criticalEtaMellin (1 - positiveOddPole n) ≠ 0 := by
  unfold criticalEtaMellin positiveOddPole
  apply div_ne_zero
  · convert dirichletEta_neg_half_sub_two_nat_ne_zero n using 1
    all_goals ring
  · norm_num
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith

lemma criticalEtaMellin_one_sub_positiveEvenPole_ne_zero (n : ℕ) :
    criticalEtaMellin (1 - positiveEvenPole n) ≠ 0 := by
  unfold criticalEtaMellin positiveEvenPole
  apply div_ne_zero
  · convert dirichletEta_neg_three_halves_sub_two_nat_ne_zero n using 1
    all_goals ring
  · norm_num
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith

lemma positiveOddPole_injective : Function.Injective positiveOddPole := by
  intro m n h
  unfold positiveOddPole at h
  have hre := congrArg Complex.re h
  norm_num at hre
  exact_mod_cast hre

lemma positiveEvenPole_injective : Function.Injective positiveEvenPole := by
  intro m n h
  unfold positiveEvenPole at h
  have hre := congrArg Complex.re h
  norm_num at hre
  exact_mod_cast hre

theorem polynomial_eq_zero_of_cancels_criticalEta_even_poles
    (p : Polynomial ℂ)
    (hcancel : ∀ n : ℕ,
      p.eval (positiveOddPole n) * criticalEtaMellin (1 - positiveOddPole n) = 0) :
    p = 0 := by
  apply Polynomial.eq_zero_of_infinite_isRoot
  apply (Set.infinite_range_of_injective positiveOddPole_injective).mono
  rintro z ⟨n, rfl⟩
  change p.eval (positiveOddPole n) = 0
  exact (mul_eq_zero.mp (hcancel n)).resolve_right
    (criticalEtaMellin_one_sub_positiveOddPole_ne_zero n)

theorem polynomial_eq_zero_of_cancels_criticalEta_odd_poles
    (p : Polynomial ℂ)
    (hcancel : ∀ n : ℕ,
      p.eval (positiveEvenPole n) * criticalEtaMellin (1 - positiveEvenPole n) = 0) :
    p = 0 := by
  apply Polynomial.eq_zero_of_infinite_isRoot
  apply (Set.infinite_range_of_injective positiveEvenPole_injective).mono
  rintro z ⟨n, rfl⟩
  change p.eval (positiveEvenPole n) = 0
  exact (mul_eq_zero.mp (hcancel n)).resolve_right
    (criticalEtaMellin_one_sub_positiveEvenPole_ne_zero n)

end
end RHTower
