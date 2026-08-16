import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Products of commuting involutions

The exponential of a scalar multiple of an involution is a combination of the identity and the
involution.  For a finite family of pairwise commuting involutions the product of the family is
therefore a scalar multiple of the exponential of the sum, so anything commuting with the sum
commutes with the product.
-/

open NormedSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [NormedAlgebra ℚ A] [CompleteSpace A]

theorem pow_of_sq_eq_one {x : A} (hx : x * x = 1) :
    ∀ k : ℕ, x ^ (2 * k) = 1 ∧ x ^ (2 * k + 1) = x := by
  intro k
  induction k with
  | zero => exact ⟨pow_zero x, pow_one x⟩
  | succ k ih =>
      constructor
      · have hstep : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
        rw [hstep, pow_succ, ih.2, hx]
      · have hstep : 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 := by ring
        rw [hstep, pow_succ, pow_succ, ih.2, hx, one_mul]

/-- **The exponential of a multiple of an involution.** -/
theorem exp_smul_of_sq_eq_one {x : A} (hx : x * x = 1) (t : ℂ) :
    exp (t • x) = (Complex.cosh t) • (1 : A) + (Complex.sinh t) • x := by
  classical
  have hterm : ∀ n : ℕ, ((n.factorial : ℂ))⁻¹ • (t • x) ^ n =
      (t ^ n / (n.factorial : ℂ)) • x ^ n := by
    intro n
    rw [smul_pow, smul_smul, div_eq_mul_inv, mul_comm]
  have heven : HasSum (fun k : ℕ => ((2 * k).factorial : ℂ)⁻¹ • (t • x) ^ (2 * k))
      ((Complex.cosh t) • (1 : A)) := by
    have hbase := (Complex.hasSum_cosh t).smul_const (1 : A)
    refine hbase.congr_fun fun k => ?_
    rw [hterm, (pow_of_sq_eq_one hx k).1]
  have hodd : HasSum (fun k : ℕ => ((2 * k + 1).factorial : ℂ)⁻¹ • (t • x) ^ (2 * k + 1))
      ((Complex.sinh t) • x) := by
    have hbase := (Complex.hasSum_sinh t).smul_const x
    refine hbase.congr_fun fun k => ?_
    rw [hterm, (pow_of_sq_eq_one hx k).2]
  have hsum : HasSum (fun n : ℕ => ((n.factorial : ℂ))⁻¹ • (t • x) ^ n)
      ((Complex.cosh t) • (1 : A) + (Complex.sinh t) • x) := heven.even_add_odd hodd
  rw [exp_eq_tsum ℂ]
  exact hsum.tsum_eq

theorem exp_halfPi_smul_of_sq_eq_one {x : A} (hx : x * x = 1) :
    exp ((Complex.I * (Real.pi / 2 : ℝ)) • x) = Complex.I • x := by
  have hcosh : Complex.cosh (Complex.I * (Real.pi / 2 : ℝ)) = 0 := by
    rw [mul_comm, Complex.cosh_mul_I]
    simp
  have hsinh : Complex.sinh (Complex.I * (Real.pi / 2 : ℝ)) = Complex.I := by
    rw [mul_comm, Complex.sinh_mul_I]
    simp
  rw [exp_smul_of_sq_eq_one hx, hcosh, hsinh, zero_smul, zero_add]


variable {R : Type*} [DecidableEq R]

theorem noncommProd_smul (c : ℂ) (x : R → A) (hall : ∀ l m, Commute (x l) (x m))
    (s : Finset R) :
    s.noncommProd (fun l => c • x l)
        (fun i _ j _ _ => ((hall i j).smul_left c).smul_right c) =
      (c ^ s.card) • s.noncommProd x (fun i _ j _ _ => hall i j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
      rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha,
        Finset.noncommProd_insert_of_notMem _ _ _ _ ha, ih,
        Finset.card_insert_of_notMem ha, smul_mul_assoc, mul_smul_comm, smul_smul, pow_succ]
      congr 1
      ring

variable [Fintype R]

/-- **The product of commuting involutions is a scalar multiple of an exponential of their sum.** -/
theorem exp_halfPi_smul_sum (x : R → A) (hall : ∀ l m, Commute (x l) (x m))
    (hsq : ∀ l, x l * x l = 1) :
    exp ((Complex.I * (Real.pi / 2 : ℝ)) • ∑ l, x l) =
      (Complex.I ^ Fintype.card R) •
        Finset.univ.noncommProd x (fun i _ j _ _ => hall i j) := by
  classical
  rw [Finset.smul_sum, exp_sum_of_commute Finset.univ (fun l => (Complex.I * (Real.pi / 2 : ℝ)) • x l)
    (fun i _ j _ _ => ((hall i j).smul_left _).smul_right _)]
  rw [Finset.noncommProd_congr rfl (fun l _ => exp_halfPi_smul_of_sq_eq_one (hsq l))]
  rw [noncommProd_smul Complex.I x hall Finset.univ, Finset.card_univ]

/-- **Anything commuting with the sum commutes with the product.** -/
theorem commute_noncommProd_of_commute_sum (x : R → A) (hall : ∀ l m, Commute (x l) (x m))
    (hsq : ∀ l, x l * x l = 1) {s : A} (hs : Commute (∑ l, x l) s) :
    Commute (Finset.univ.noncommProd x (fun i _ j _ _ => hall i j)) s := by
  classical
  have hexp : Commute (exp ((Complex.I * (Real.pi / 2 : ℝ)) • ∑ l, x l)) s :=
    Commute.exp_left (hs.smul_left _)
  rw [exp_halfPi_smul_sum x hall hsq] at hexp
  have hI : (Complex.I ^ Fintype.card R) ≠ 0 := pow_ne_zero _ Complex.I_ne_zero
  have hscaled := hexp.smul_left ((Complex.I ^ Fintype.card R)⁻¹)
  rwa [smul_smul, inv_mul_cancel₀ hI, one_smul] at hscaled

end GaloisForLFunctions.HTGeometry
