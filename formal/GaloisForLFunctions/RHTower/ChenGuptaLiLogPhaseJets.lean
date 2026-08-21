/-
# Chen--Gupta--Li logarithmic additive-phase jets

This module gives a closed finite-polynomial description of every logarithmic
derivative of `exp(-2π i ξ exp(-u))`, with an explicit coefficient budget on
the source log-dyadic support. It supplies the reciprocal-parameter route in
CGL Lemma 4.3.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiHtReciprocalFirstDecay
import Mathlib.Analysis.Calculus.Deriv.Polynomial

noncomputable section

namespace RHTower

open Polynomial

def cglLogPhaseArgument (xi u : ℝ) : ℂ :=
  ((-2 * Real.pi * xi * Real.exp (-u) : ℝ) : ℂ) * Complex.I

theorem hasDerivAt_cglLogPhaseArgument (xi u : ℝ) :
    HasDerivAt (cglLogPhaseArgument xi) (-cglLogPhaseArgument xi u) u := by
  have hexpR : HasDerivAt (fun v : ℝ => Real.exp (-v)) (-Real.exp (-u)) u := by
    simpa only [Function.comp_def, mul_neg, mul_one] using
      (Real.hasDerivAt_exp (-u)).comp u (hasDerivAt_neg u)
  have hargR : HasDerivAt (fun v : ℝ => -2 * Real.pi * xi * Real.exp (-v))
      (-2 * Real.pi * xi * -Real.exp (-u)) u := by
    exact hexpR.const_mul (-2 * Real.pi * xi)
  have hargC : HasDerivAt
      (fun v : ℝ => ((-2 * Real.pi * xi * Real.exp (-v) : ℝ) : ℂ))
      ((-2 * Real.pi * xi * -Real.exp (-u) : ℝ) : ℂ) u :=
    hargR.ofReal_comp
  apply HasDerivAt.of_isLittleO
  simpa [cglLogPhaseArgument, mul_assoc] using (hargC.mul_const Complex.I).isLittleO

def cglLogPhasePolynomial : ℕ → Polynomial ℂ
  | 0 => 1
  | n + 1 => -(Polynomial.X * (cglLogPhasePolynomial n).derivative +
    Polynomial.X * cglLogPhasePolynomial n)

theorem cglLogPhasePolynomial_natDegree_le (n : ℕ) :
    (cglLogPhasePolynomial n).natDegree ≤ n := by
  induction n with
  | zero => simp [cglLogPhasePolynomial]
  | succ n ih =>
    rw [cglLogPhasePolynomial]
    simp only [Polynomial.natDegree_neg]
    calc
      (Polynomial.X * (cglLogPhasePolynomial n).derivative +
          Polynomial.X * cglLogPhasePolynomial n).natDegree ≤
          max (Polynomial.X * (cglLogPhasePolynomial n).derivative).natDegree
            (Polynomial.X * cglLogPhasePolynomial n).natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ max (1 + (cglLogPhasePolynomial n).derivative.natDegree)
            (1 + (cglLogPhasePolynomial n).natDegree) := by
          apply max_le
          · calc
              (Polynomial.X * (cglLogPhasePolynomial n).derivative).natDegree ≤
                  Polynomial.X.natDegree + (cglLogPhasePolynomial n).derivative.natDegree :=
                Polynomial.natDegree_mul_le
              _ = 1 + (cglLogPhasePolynomial n).derivative.natDegree := by simp
              _ ≤ max (1 + (cglLogPhasePolynomial n).derivative.natDegree)
                  (1 + (cglLogPhasePolynomial n).natDegree) := le_max_left _ _
          · calc
              (Polynomial.X * cglLogPhasePolynomial n).natDegree ≤
                  Polynomial.X.natDegree + (cglLogPhasePolynomial n).natDegree :=
                Polynomial.natDegree_mul_le
              _ = 1 + (cglLogPhasePolynomial n).natDegree := by simp
              _ ≤ max (1 + (cglLogPhasePolynomial n).derivative.natDegree)
                  (1 + (cglLogPhasePolynomial n).natDegree) := le_max_right _ _
      _ ≤ n + 1 := by
          have hder₀ : (cglLogPhasePolynomial n).derivative.natDegree ≤
              (cglLogPhasePolynomial n).natDegree - 1 :=
            Polynomial.natDegree_derivative_le _
          have hder₁ : (cglLogPhasePolynomial n).natDegree - 1 ≤
              (cglLogPhasePolynomial n).natDegree := Nat.sub_le _ _
          apply max_le
          · calc
              1 + (cglLogPhasePolynomial n).derivative.natDegree ≤
                  1 + ((cglLogPhasePolynomial n).natDegree - 1) :=
                Nat.add_le_add_left hder₀ 1
              _ ≤ 1 + n := Nat.add_le_add_left (hder₁.trans ih) 1
              _ = n + 1 := Nat.add_comm _ _
          · calc
              1 + (cglLogPhasePolynomial n).natDegree ≤ 1 + n :=
                Nat.add_le_add_left ih 1
              _ = n + 1 := Nat.add_comm _ _

theorem hasDerivAt_polynomial_eval_comp {p : Polynomial ℂ} {z : ℝ → ℂ} {z' : ℂ}
    (hz : HasDerivAt z z' u) :
    HasDerivAt (fun v : ℝ => p.eval (z v)) (p.derivative.eval (z u) * z') u := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    apply HasDerivAt.of_isLittleO
    simpa [Polynomial.eval_add, Polynomial.derivative_add, add_mul] using (hp.add hq).isLittleO
  | monomial n a =>
    simpa [Polynomial.eval_monomial, Polynomial.derivative_monomial, mul_assoc,
      mul_left_comm, mul_comm] using (hz.pow n).const_mul a

def cglLogPhaseJet (n : ℕ) (xi u : ℝ) : ℂ :=
  (cglLogPhasePolynomial n).eval (cglLogPhaseArgument xi u) * cglLogAdditivePhase xi u

theorem hasDerivAt_cglLogPhaseJet (n : ℕ) (xi u : ℝ) :
    HasDerivAt (cglLogPhaseJet n xi) (cglLogPhaseJet (n + 1) xi u) u := by
  have hpoly := hasDerivAt_polynomial_eval_comp
    (u := u) (p := cglLogPhasePolynomial n)
    (z := cglLogPhaseArgument xi) (z' := -cglLogPhaseArgument xi u)
    (hasDerivAt_cglLogPhaseArgument xi u)
  have hphase : HasDerivAt (cglLogAdditivePhase xi)
      (cglLogAdditivePhase xi u * (-cglLogPhaseArgument xi u)) u := by
    apply HasDerivAt.of_isLittleO
    simpa [cglLogPhaseArgument, mul_assoc] using
      (hasDerivAt_cglLogAdditivePhase xi u).isLittleO
  have hprod := hpoly.mul hphase
  have hderiv : cglLogPhaseJet (n + 1) xi u =
      ((cglLogPhasePolynomial n).derivative.eval (cglLogPhaseArgument xi u) *
          (-cglLogPhaseArgument xi u)) * cglLogAdditivePhase xi u +
        (cglLogPhasePolynomial n).eval (cglLogPhaseArgument xi u) *
          (cglLogAdditivePhase xi u * (-cglLogPhaseArgument xi u)) := by
    simp [cglLogPhaseJet, cglLogPhasePolynomial, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_neg, mul_assoc]
    ring
  apply HasDerivAt.of_isLittleO
  rw [hderiv]
  exact hprod.isLittleO

theorem iteratedDeriv_cglLogAdditivePhase (n : ℕ) (xi u : ℝ) :
    iteratedDeriv n (cglLogAdditivePhase xi) u = cglLogPhaseJet n xi u := by
  induction n generalizing u with
  | zero => simp [cglLogPhaseJet, cglLogPhasePolynomial]
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have hfun : iteratedDeriv n (cglLogAdditivePhase xi) = cglLogPhaseJet n xi := by
      funext v
      exact ih v
    rw [hfun]
    exact (hasDerivAt_cglLogPhaseJet n xi u).deriv

theorem norm_cglLogPhaseArgument_le (xi u : ℝ)
    (hu : u ∈ Set.Icc (-Real.log 2) 0) :
    ‖cglLogPhaseArgument xi u‖ ≤ 4 * Real.pi * |xi| := by
  have harg : -u ≤ Real.log 2 := by linarith [hu.1]
  have hexp : Real.exp (-u) ≤ 2 := by
    calc
      Real.exp (-u) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr harg
      _ = 2 := Real.exp_log (by norm_num)
  have hnorm : ‖cglLogPhaseArgument xi u‖ =
      2 * Real.pi * |xi| * Real.exp (-u) := by
    have hident : -2 * Real.pi * xi * Real.exp (-u) =
        -(2 * Real.pi * xi * Real.exp (-u)) := by ring
    rw [cglLogPhaseArgument, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      hident, Real.norm_eq_abs, abs_neg, abs_mul, abs_mul,
      abs_of_pos (mul_pos (by norm_num) Real.pi_pos),
      abs_of_nonneg (Real.exp_nonneg _)]
  calc
    ‖cglLogPhaseArgument xi u‖ = 2 * Real.pi * |xi| * Real.exp (-u) := hnorm
    _ ≤ 2 * Real.pi * |xi| * 2 := by gcongr
    _ = 4 * Real.pi * |xi| := by ring

def cglLogPhasePolynomialBudget (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range ((cglLogPhasePolynomial n).natDegree + 1),
    ‖(cglLogPhasePolynomial n).coeff k‖ * (4 * Real.pi) ^ k

theorem norm_cglLogPhasePolynomial_eval_le (n : ℕ) (xi u : ℝ)
    (hu : u ∈ Set.Icc (-Real.log 2) 0) :
    ‖(cglLogPhasePolynomial n).eval (cglLogPhaseArgument xi u)‖ ≤
      cglLogPhasePolynomialBudget n * (1 + |xi|) ^ n := by
  rw [Polynomial.eval_eq_sum_range]
  calc
    ‖∑ k ∈ Finset.range ((cglLogPhasePolynomial n).natDegree + 1),
        (cglLogPhasePolynomial n).coeff k * cglLogPhaseArgument xi u ^ k‖ ≤
        ∑ k ∈ Finset.range ((cglLogPhasePolynomial n).natDegree + 1),
          ‖(cglLogPhasePolynomial n).coeff k * cglLogPhaseArgument xi u ^ k‖ :=
      norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range ((cglLogPhasePolynomial n).natDegree + 1),
        (‖(cglLogPhasePolynomial n).coeff k‖ * (4 * Real.pi) ^ k) * (1 + |xi|) ^ n := by
      apply Finset.sum_le_sum
      intro k hk
      have hkdegree : k ≤ n :=
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)).trans
          (cglLogPhasePolynomial_natDegree_le n)
      have hbase : 1 ≤ 1 + |xi| := by linarith [abs_nonneg xi]
      have hpow : |xi| ^ k ≤ (1 + |xi|) ^ n := by
        calc
          |xi| ^ k ≤ (1 + |xi|) ^ k := by
            gcongr
            linarith [abs_nonneg xi]
          _ ≤ (1 + |xi|) ^ n := pow_le_pow_right₀ hbase hkdegree
      calc
        ‖(cglLogPhasePolynomial n).coeff k * cglLogPhaseArgument xi u ^ k‖ =
            ‖(cglLogPhasePolynomial n).coeff k‖ * ‖cglLogPhaseArgument xi u‖ ^ k := by
          rw [norm_mul, norm_pow]
        _ ≤ ‖(cglLogPhasePolynomial n).coeff k‖ * (4 * Real.pi * |xi|) ^ k := by
          gcongr
          exact norm_cglLogPhaseArgument_le xi u hu
        _ = (‖(cglLogPhasePolynomial n).coeff k‖ * (4 * Real.pi) ^ k) * |xi| ^ k := by
          rw [mul_pow]
          ring
        _ ≤ (‖(cglLogPhasePolynomial n).coeff k‖ * (4 * Real.pi) ^ k) *
            (1 + |xi|) ^ n := by
          gcongr
    _ = cglLogPhasePolynomialBudget n * (1 + |xi|) ^ n := by
      unfold cglLogPhasePolynomialBudget
      rw [Finset.sum_mul]

theorem norm_cglLogPhaseJet_le (n : ℕ) (xi u : ℝ)
    (hu : u ∈ Set.Icc (-Real.log 2) 0) :
    ‖cglLogPhaseJet n xi u‖ ≤
      cglLogPhasePolynomialBudget n * (1 + |xi|) ^ n := by
  rw [cglLogPhaseJet, norm_mul, norm_cglLogAdditivePhase, mul_one]
  exact norm_cglLogPhasePolynomial_eval_le n xi u hu

end RHTower
