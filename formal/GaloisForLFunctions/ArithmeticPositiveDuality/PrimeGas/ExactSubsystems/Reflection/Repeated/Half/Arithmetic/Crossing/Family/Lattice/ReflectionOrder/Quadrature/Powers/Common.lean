import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Tactic

/-! # Common quarter periods of positive integer harmonics -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Powers

open Finset Real

variable {I : Type*} [Fintype I]

/-- Fundamental occupation and its reduced positive harmonics. -/
def fundamental (k : I → ℕ+) := univ.gcd (fun i => (k i : ℕ))

def reduced (k : I → ℕ+) (i : I) := (k i : ℕ) / fundamental k

theorem restore (k : I → ℕ+) (i : I) : reduced k i * fundamental k = (k i : ℕ) :=
  Nat.div_mul_cancel (gcd_dvd (mem_univ i))

variable [Nonempty I]

theorem fundamental_pos (k : I → ℕ+) : 0 < fundamental k := by
  apply Nat.pos_of_ne_zero
  intro h
  let i : I := Classical.choice inferInstance
  have eq := restore k i
  rw [h,mul_zero] at eq
  exact (k i).ne_zero eq.symm

/-- Removing the common divisor leaves at least one odd occupation. -/
theorem some_odd (k : I → ℕ+) : ∃ i, Odd (reduced k i) := by
  by_contra! no
  have twice : 2 * fundamental k ∣ fundamental k := by
    apply Finset.dvd_gcd
    intro i _
    have d : 2 ∣ reduced k i := by
      have h := no i
      rw [Nat.odd_iff] at h
      omega
    obtain ⟨m,hm⟩ := d
    refine ⟨m,?_⟩
    rw [←restore k i,hm]
    ring
  have bound := Nat.le_of_dvd (fundamental_pos k) twice
  have pos := fundamental_pos k
  omega

/-- Oddness of every reduced occupation is equality of the two-adic
valuations of all original occupations. -/
theorem dyadic_iff (k : I → ℕ+) :
    (∀ i, Odd (reduced k i)) ↔ ∀ i j, (k i : ℕ).factorization 2 = (k j : ℕ).factorization 2 := by
  have split (i : I) : (k i : ℕ).factorization 2 =
      (reduced k i).factorization 2 + (fundamental k).factorization 2 := by
    have nz : reduced k i ≠ 0 := fun h => (k i).ne_zero (by rw [←restore k i,h,zero_mul])
    rw [←restore k i,Nat.factorization_mul nz (fundamental_pos k).ne',Finsupp.add_apply]
  have odd (i : I) : Odd (reduced k i) ↔ (reduced k i).factorization 2 = 0 := by
    have nz : reduced k i ≠ 0 := fun h => (k i).ne_zero (by rw [←restore k i,h,zero_mul])
    have iff := Nat.prime_two.dvd_iff_one_le_factorization nz
    rw [Nat.odd_iff]
    omega
  constructor
  · intro h i j; rw [split i,split j,(odd i).mp (h i),(odd j).mp (h j)]
  · intro h i
    obtain ⟨j,hj⟩ := some_odd k
    have eq := h i j
    rw [split i,split j,(odd j).mp hj] at eq
    exact (odd i).mpr (by omega)

private def phase (y : ℝ) := Complex.exp (((2*y : ℝ) : ℂ)*Complex.I)

private theorem phase_harmonic (n : ℕ) (y : ℝ) : phase (n*y)=(phase y)^n := by
  rw [phase,phase,←Complex.exp_nat_mul]
  push_cast
  congr 1
  ring

private theorem cos_zero (y : ℝ) : cos y=0 ↔ phase y= -1 := by
  have coords : ((((2*y : ℝ) : ℂ)*Complex.I).re=0) ∧
      ((((2*y : ℝ) : ℂ)*Complex.I).im=2*y) := by simp
  constructor
  · intro h
    apply Complex.ext
    · simp only [phase,Complex.exp_re,coords.1,coords.2,exp_zero,one_mul,cos_two_mul,h]
      norm_num
    · simp only [phase,Complex.exp_im,coords.1,coords.2,exp_zero,sin_two_mul,h,mul_zero]
      norm_num
  · intro h
    have eq := congrArg Complex.re h
    simp only [phase,Complex.exp_re,coords.1,coords.2,exp_zero,one_mul,cos_two_mul,
      Complex.neg_re,Complex.one_re] at eq
    nlinarith only [eq,sq_nonneg (cos y)]

private theorem roots (k : I → ℕ+) (z : ℂ) :
    (∀ i, z^(k i : ℕ)= -1) ↔ z^(fundamental k)= -1 ∧ ∀ i, Odd (reduced k i) := by
  have power (i : I) : (z^fundamental k)^(reduced k i)=z^(k i : ℕ) := by
    rw [←pow_mul,mul_comm,restore]
  constructor
  · intro h
    have ord : orderOf (z^2) ∣ fundamental k := by
      apply Finset.dvd_gcd
      intro i _
      apply orderOf_dvd_iff_pow_eq_one.mpr
      rw [pow_right_comm,h i]; norm_num
    have square := orderOf_dvd_iff_pow_eq_one.mp ord
    rw [pow_right_comm] at square
    have root : z^fundamental k= -1 := by
      rcases sq_eq_one_iff.mp square with one | neg
      · let i : I := Classical.choice inferInstance
        have eq := power i
        rw [one,one_pow,h i] at eq
        norm_num at eq
      · exact neg
    refine ⟨root,fun i => ?_⟩
    have eq := power i
    rw [root,h i] at eq
    rcases Nat.even_or_odd (reduced k i) with even | odd
    · rw [even.neg_one_pow] at eq; norm_num at eq
    · exact odd
  · rintro ⟨root,odd⟩ i
    rw [←power i,root,(odd i).neg_one_pow]

/-- Every blind phase is an odd quarter period of the fundamental
harmonic. Such phases exist exactly for one two-adic valuation class. -/
theorem common_phases (k : I → ℕ+) (y : ℝ) :
    (∀ i, cos ((k i : ℝ)*y)=0) ↔
      (∀ i j, (k i : ℕ).factorization 2=(k j : ℕ).factorization 2) ∧
      ∃ m : ℤ, (fundamental k : ℝ)*y=(2*(m : ℝ)+1)*π/2 := by
  simp only [cos_zero,phase_harmonic]
  rw [roots,and_comm,dyadic_iff,←phase_harmonic,←cos_zero,Real.cos_eq_zero_iff]

#print axioms restore
#print axioms fundamental_pos
#print axioms some_odd
#print axioms dyadic_iff
#print axioms common_phases

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Powers
