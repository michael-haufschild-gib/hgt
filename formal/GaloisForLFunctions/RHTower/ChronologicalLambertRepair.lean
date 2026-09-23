import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Tactic

/-!
# Arithmetic coefficient cost of nonlinear Fermi repair

The formal Fermi response is the unique rational series X/(1+X). Its nonlinear
powers have explicit binomial coefficients. Lambert inversion is unique; for
any power at least two its coefficient at a sufficiently large prime has
binomial magnitude. Hence no such power has a bounded real Lambert expansion.
These are exact formal-series assertions, not closure assertions in L².
-/

noncomputable section
open Finset
namespace RHTower

def chronologicalAlternatingSeries : PowerSeries ℤ :=
  PowerSeries.mk (fun n => (-1:ℤ)^n)

def chronologicalFermiSeries : PowerSeries ℤ :=
  PowerSeries.X * chronologicalAlternatingSeries

theorem chronologicalAlternatingSeries_inverse :
    (1 + PowerSeries.X) * chronologicalAlternatingSeries = 1 := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [add_mul, chronologicalAlternatingSeries]
  | succ n =>
    simp [add_mul, chronologicalAlternatingSeries, PowerSeries.coeff_succ_X_mul, pow_succ]

theorem chronologicalFermiSeries_equation :
    (1 + PowerSeries.X) * chronologicalFermiSeries = PowerSeries.X := by
  unfold chronologicalFermiSeries
  calc
    (1 + PowerSeries.X) * (PowerSeries.X * chronologicalAlternatingSeries) =
      PowerSeries.X * ((1 + PowerSeries.X) * chronologicalAlternatingSeries) := by ring
    _ = PowerSeries.X := by rw [chronologicalAlternatingSeries_inverse, mul_one]

theorem chronologicalAlternatingSeries_square_coeff (n : ℕ) :
    PowerSeries.coeff n (chronologicalAlternatingSeries ^ (2 : ℕ)) =
      (-1:ℤ)^n * ((n:ℤ)+1) := by
  rw [pow_two, PowerSeries.coeff_mul]
  have he : ∀ x ∈ Finset.antidiagonal n,
      PowerSeries.coeff x.1 chronologicalAlternatingSeries *
        PowerSeries.coeff x.2 chronologicalAlternatingSeries = (-1:ℤ)^n := by
    intro x hx
    simp only [chronologicalAlternatingSeries, PowerSeries.coeff_mk]
    rw [← pow_add, Finset.mem_antidiagonal.mp hx]
  rw [Finset.sum_congr rfl he]
  simp [Finset.Nat.card_antidiagonal, mul_comm]

theorem chronologicalFermiSeries_square_coeff_zero :
    PowerSeries.coeff 0 (chronologicalFermiSeries ^ (2 : ℕ)) = 0 := by
  simp [chronologicalFermiSeries, pow_two]

theorem chronologicalFermiSeries_square_coeff_succ (n : ℕ) :
    PowerSeries.coeff (n+1) (chronologicalFermiSeries ^ (2 : ℕ)) =
      (-1:ℤ)^(n+1) * (n:ℤ) := by
  cases n with
  | zero => simp [chronologicalFermiSeries, pow_two, PowerSeries.coeff_succ_X_mul, mul_assoc]
  | succ n =>
    have he : chronologicalFermiSeries ^ (2 : ℕ) =
        PowerSeries.X ^ (2 : ℕ) * chronologicalAlternatingSeries ^ (2 : ℕ) := by
      unfold chronologicalFermiSeries
      ring
    rw [he, show n+1+1=n+2 by omega, PowerSeries.coeff_X_pow_mul,
      chronologicalAlternatingSeries_square_coeff]
    simp [pow_succ]

def chronologicalLambertSeries {R : Type*} [Semiring R]
    (a : ArithmeticFunction R) : PowerSeries R :=
  PowerSeries.mk (fun n => ∑ d ∈ n.divisors, a d)

def chronologicalFermiSquareSource : ArithmeticFunction ℤ :=
  ⟨fun n => PowerSeries.coeff n (chronologicalFermiSeries ^ (2 : ℕ)),
    chronologicalFermiSeries_square_coeff_zero⟩

def chronologicalFermiSquareArithmetic : ArithmeticFunction ℤ :=
  ArithmeticFunction.moebius * chronologicalFermiSquareSource

theorem chronologicalFermiSquareArithmetic_reconstruct :
    chronologicalLambertSeries chronologicalFermiSquareArithmetic = chronologicalFermiSeries ^ (2 : ℕ) := by
  apply PowerSeries.ext
  intro n
  simp only [chronologicalLambertSeries, PowerSeries.coeff_mk]
  rw [← ArithmeticFunction.coe_zeta_mul_apply]
  have he : (ArithmeticFunction.zeta : ArithmeticFunction ℤ) * chronologicalFermiSquareArithmetic =
      chronologicalFermiSquareSource := by
    rw [chronologicalFermiSquareArithmetic, ← mul_assoc,
      ArithmeticFunction.coe_zeta_mul_moebius, one_mul]
  rw [he]
  rfl

theorem chronologicalLambertSeries_injective : Function.Injective (chronologicalLambertSeries (R := ℤ)) := by
  intro a b hab
  have he : (ArithmeticFunction.zeta : ArithmeticFunction ℤ)*a =
      (ArithmeticFunction.zeta : ArithmeticFunction ℤ)*b := by
    ext n
    simpa only [ArithmeticFunction.coe_zeta_mul_apply, chronologicalLambertSeries,
      PowerSeries.coeff_mk] using congrArg (PowerSeries.coeff n) hab
  have hm := congrArg (fun f : ArithmeticFunction ℤ => ArithmeticFunction.moebius * f) he
  simpa only [← mul_assoc, ArithmeticFunction.moebius_mul_coe_zeta, one_mul] using hm

theorem chronologicalFermiSquareArithmetic_unique :
    ∃! a : ArithmeticFunction ℤ,
      chronologicalLambertSeries a = chronologicalFermiSeries ^ (2 : ℕ) := by
  refine ⟨chronologicalFermiSquareArithmetic, chronologicalFermiSquareArithmetic_reconstruct, ?_⟩
  intro a ha
  exact chronologicalLambertSeries_injective (ha.trans chronologicalFermiSquareArithmetic_reconstruct.symm)

theorem chronologicalFermiSquareArithmetic_one : chronologicalFermiSquareArithmetic 1 = 0 := by
  have he := congrArg (PowerSeries.coeff 1) chronologicalFermiSquareArithmetic_reconstruct
  simpa [chronologicalLambertSeries, chronologicalFermiSeries_square_coeff_succ] using he

theorem chronologicalFermiSquareArithmetic_odd_prime (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    chronologicalFermiSquareArithmetic p = -((p:ℤ)-1) := by
  have he := congrArg (PowerSeries.coeff p) chronologicalFermiSquareArithmetic_reconstruct
  have hc : PowerSeries.coeff p (chronologicalFermiSeries ^ (2 : ℕ)) = -((p:ℤ)-1) := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne_zero
    rw [chronologicalFermiSeries_square_coeff_succ, (hp.odd_of_ne_two hp2).neg_one_pow]
    simp
  rw [hc] at he
  simpa [chronologicalLambertSeries, hp.divisors, hp.ne_one.symm,
    chronologicalFermiSquareArithmetic_one] using he

theorem chronologicalFermiSquareArithmetic_unbounded :
    ∀ B : ℕ, ∃ p : ℕ, p.Prime ∧ (B:ℤ) < |chronologicalFermiSquareArithmetic p| := by
  intro B
  obtain ⟨p, hpB, hp⟩ := Nat.exists_infinite_primes (B+3)
  refine ⟨p, hp, ?_⟩
  have hpos : (0:ℤ) ≤ (p:ℤ)-1 := by
    have h : (1:ℤ) ≤ p := by exact_mod_cast hp.one_lt.le
    linarith
  rw [chronologicalFermiSquareArithmetic_odd_prime p hp (by omega), abs_neg, abs_of_nonneg hpos]
  omega

theorem chronologicalFermiSquare_no_bounded_Lambert_representation :
    ¬ ∃ a : ArithmeticFunction ℤ, (∃ B : ℕ, ∀ n, |a n| ≤ (B:ℤ)) ∧
      chronologicalLambertSeries a = chronologicalFermiSeries ^ (2 : ℕ) := by
  rintro ⟨a, ⟨B, hB⟩, ha⟩
  have he := chronologicalLambertSeries_injective (ha.trans chronologicalFermiSquareArithmetic_reconstruct.symm)
  obtain ⟨p, _, hp⟩ := chronologicalFermiSquareArithmetic_unbounded B
  exact (not_lt_of_ge (he ▸ hB p)) hp


theorem chronologicalFermiSquare_no_bounded_real_Lambert_representation :
    ¬ ∃ a : ArithmeticFunction ℝ, (∃ B : ℝ, ∀ n, |a n| ≤ B) ∧
      chronologicalLambertSeries a =
        PowerSeries.map (Int.castRingHom ℝ) (chronologicalFermiSeries ^ (2 : ℕ)) := by
  rintro ⟨a, ⟨B, hB⟩, ha⟩
  have h1 := congrArg (PowerSeries.coeff 1) ha
  rw [PowerSeries.coeff_map] at h1
  have ha1 : a 1 = 0 := by
    simpa [chronologicalLambertSeries, PowerSeries.coeff_map,
      chronologicalFermiSeries_square_coeff_succ] using h1
  obtain ⟨M, hM⟩ := exists_nat_gt (B+3)
  obtain ⟨p, hpM, hp⟩ := Nat.exists_infinite_primes M
  have hpB : B+3 < (p:ℝ) := hM.trans_le (by exact_mod_cast hpM)
  have hp2 : p ≠ 2 := by
    have hB0 := hB 1
    rw [ha1, abs_zero] at hB0
    intro he
    subst p
    norm_cast at hpB
    linarith
  have he := congrArg (PowerSeries.coeff p) ha
  rw [PowerSeries.coeff_map] at he
  have hsrc := congrArg (PowerSeries.coeff p) chronologicalFermiSquareArithmetic_reconstruct
  have hcoef : PowerSeries.coeff p (chronologicalFermiSeries ^ (2 : ℕ)) = -((p:ℤ)-1) := by
    rw [← hsrc]
    simp [chronologicalLambertSeries, hp.divisors, hp.ne_one.symm,
      chronologicalFermiSquareArithmetic_one, chronologicalFermiSquareArithmetic_odd_prime p hp hp2]
  have hap : a p = -((p:ℝ)-1) := by
    simpa [chronologicalLambertSeries, PowerSeries.coeff_map, hp.divisors,
      hp.ne_one.symm, ha1, hcoef] using he
  have hh := hB p
  have hpos : (0:ℝ) ≤ (p:ℝ)-1 := by
    have h : (1:ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
    linarith
  rw [hap, abs_neg, abs_of_nonneg hpos] at hh
  linarith


theorem chronologicalAlternatingSeries_rescale :
    chronologicalAlternatingSeries = PowerSeries.rescale (-1) (PowerSeries.mk (1 : ℕ → ℤ)) := by
  apply PowerSeries.ext
  intro n
  simp [chronologicalAlternatingSeries, PowerSeries.coeff_rescale]

theorem chronologicalFermiSeries_power_coeff (m n : ℕ) :
    PowerSeries.coeff (n+(m+1)) (chronologicalFermiSeries ^ (m+1)) =
      (-1:ℤ)^n * ((Nat.choose (m+n) m : ℕ) : ℤ) := by
  rw [chronologicalFermiSeries, mul_pow, PowerSeries.coeff_X_pow_mul,
    chronologicalAlternatingSeries_rescale, ← map_pow,
    PowerSeries.mk_one_pow_eq_mk_choose_add, PowerSeries.coeff_rescale, PowerSeries.coeff_mk]

theorem chronologicalFermiSeries_power_coeff_one (m : ℕ) :
    PowerSeries.coeff 1 (chronologicalFermiSeries ^ (m+2)) = 0 := by
  rw [chronologicalFermiSeries, mul_pow, PowerSeries.coeff_X_pow_mul']
  simp

theorem chronologicalChoose_linear_lower (m n : ℕ) :
    n+1 ≤ Nat.choose (m+n+1) (m+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show m+(n+1)+1=(m+n+1)+1 by omega, Nat.choose_succ_succ']
    have hp : 0 < Nat.choose (m+n+1) m := Nat.choose_pos (by omega)
    omega

theorem chronologicalFermiPower_prime_cost (m p : ℕ) (hp : p.Prime) (hmp : m+2 ≤ p)
    (a : ArithmeticFunction ℝ)
    (ha : chronologicalLambertSeries a =
      PowerSeries.map (Int.castRingHom ℝ) (chronologicalFermiSeries ^ (m+2))) :
    |a p| = (Nat.choose (p-1) (m+1) : ℝ) := by
  have h1 := congrArg (PowerSeries.coeff 1) ha
  rw [PowerSeries.coeff_map, chronologicalFermiSeries_power_coeff_one] at h1
  have ha1 : a 1 = 0 := by simpa [chronologicalLambertSeries] using h1
  have he := congrArg (PowerSeries.coeff p) ha
  rw [PowerSeries.coeff_map] at he
  have hc := chronologicalFermiSeries_power_coeff (m+1) (p-(m+2))
  have hind : p-(m+2)+(m+1+1)=p := by omega
  have hind2 : m+1+(p-(m+2))=p-1 := by omega
  rw [hind, hind2] at hc
  rw [hc] at he
  have hav : a p = (-1:ℝ)^(p-(m+2)) * (Nat.choose (p-1) (m+1) : ℝ) := by
    simpa [chronologicalLambertSeries, hp.divisors, hp.ne_one.symm, ha1] using he
  rw [hav, abs_mul, abs_pow]
  simp

theorem chronologicalFermiPower_no_bounded_real_Lambert_representation (m : ℕ) :
    ¬ ∃ a : ArithmeticFunction ℝ, (∃ B : ℝ, ∀ n, |a n| ≤ B) ∧
      chronologicalLambertSeries a =
        PowerSeries.map (Int.castRingHom ℝ) (chronologicalFermiSeries ^ (m+2)) := by
  rintro ⟨a, ⟨B, hB⟩, ha⟩
  have hB0 : 0 ≤ B := (abs_nonneg (a 1)).trans (hB 1)
  obtain ⟨M, hM⟩ := exists_nat_gt (B+(m:ℝ)+3)
  obtain ⟨p, hpM, hp⟩ := Nat.exists_infinite_primes M
  have hpB : B+(m:ℝ)+3 < (p:ℝ) := hM.trans_le (by exact_mod_cast hpM)
  have hmp : m+2 ≤ p := by
    have hh : (m:ℝ)+2 < (p:ℝ) := by linarith
    exact_mod_cast hh.le
  have hlo := chronologicalChoose_linear_lower m (p-(m+2))
  have hind : m+(p-(m+2))+1=p-1 := by omega
  rw [hind] at hlo
  have hsmall := hB p
  rw [chronologicalFermiPower_prime_cost m p hp hmp a ha] at hsmall
  have hcast : ((p-(m+2):ℕ):ℝ)+1 ≤ (Nat.choose (p-1) (m+1):ℝ) := by exact_mod_cast hlo
  have hindR : ((p-(m+2):ℕ):ℝ) = (p:ℝ)-((m:ℝ)+2) := by
    rw [Nat.cast_sub hmp]
    simp
  rw [hindR] at hcast
  linarith

end RHTower
