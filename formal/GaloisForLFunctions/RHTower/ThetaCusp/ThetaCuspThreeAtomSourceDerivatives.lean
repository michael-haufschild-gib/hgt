import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFinitePrimeDerivatives
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspThreeAtomGaussianTail
import Mathlib.Tactic.IntervalCases

/-!
# Normalized theta-source derivatives and their infinite tails

The existing source differentiation polynomials factor through the
Gaussian coordinate `z = π t²`. The resulting polynomials obey
`Q₀ = 2z - 3` and `Qⱼ₊₁ = (5/2 - 2z) Qⱼ + 2z Qⱼ'`.

This factorization identifies the normalized atoms with the actual
derivatives of `thetaCuspSourceTerm` at every order. Coefficient bounds
through order four and the uniform Gaussian tail estimate then control
the complete derivative series beginning at the fourth positive atom.
-/

open Polynomial

namespace RHTower.ThetaCuspThreeAtomFourth

/-- Derivative polynomials in the normalized Gaussian coordinate. -/
noncomputable def atomJetPolynomial : ℕ → Polynomial ℝ
  | 0 => 2*X-3
  | j+1 => (C (5/2)-2*X)*atomJetPolynomial j + 2*X*(atomJetPolynomial j).derivative

/-- Exact coordinate factorization of the existing source derivative polynomials. -/
theorem derivativePolynomial_factor (j : ℕ) :
    thetaCuspLogDerivativePolynomial j =
      C (2*Real.pi)*X^2 * (atomJetPolynomial j).comp (C Real.pi*X^2) := by
  induction j with
  | zero =>
    apply Polynomial.funext
    intro y
    simp [thetaCuspLogDerivativePolynomial, thetaCuspSeedPolynomial, atomJetPolynomial]
    ring
  | succ j ih =>
    rw [thetaCuspLogDerivativePolynomial, ih]
    apply Polynomial.funext
    intro y
    simp [thetaCuspLogDerivativeStep, atomJetPolynomial, derivative_mul, derivative_comp]
    ring

/-- Coefficients of the first five normalized derivative polynomials. -/
noncomputable def atomCoefficient (j i : ℕ) : ℝ :=
  match j, i with
  | 0, 0 => -3
  | 0, 1 => 2
  | 1, 0 => -15/2
  | 1, 1 => 15
  | 1, 2 => -4
  | 2, 0 => -75/4
  | 2, 1 => 165/2
  | 2, 2 => -56
  | 2, 3 => 8
  | 3, 0 => -375/8
  | 3, 1 => 1635/4
  | 3, 2 => -529
  | 3, 3 => 180
  | 3, 4 => -16
  | 4, 0 => -1875/16
  | 4, 1 => 15465/8
  | 4, 2 => -4256
  | 4, 3 => 2588
  | 4, 4 => -528
  | 4, 5 => 32
  | _, _ => 0

/-- Uniform coefficient mass ceilings through derivative order four. -/
noncomputable def atomCoefficientBound (j : ℕ) : ℝ :=
  match j with
  | 0 => 5
  | 1 => 53
  | 2 => 661
  | 3 => 9445
  | 4 => 151269
  | _ => 0

theorem atomJetPolynomial_eval {j : ℕ} (hj : j ≤ 4) (z : ℝ) :
    (atomJetPolynomial j).eval z =
      ∑ i ∈ Finset.range (j+2), atomCoefficient j i * z^i := by
  interval_cases j <;>
    norm_num [atomJetPolynomial, derivative_mul, atomCoefficient, Finset.sum_range_succ] <;> ring

theorem atomCoefficientBound_pos {j : ℕ} (hj : j ≤ 4) : 0 < atomCoefficientBound j := by
  interval_cases j <;> norm_num [atomCoefficientBound]

theorem sum_abs_atomCoefficient_le {j : ℕ} (hj : j ≤ 4) :
    (∑ i ∈ Finset.range (j+2), |atomCoefficient j i|) ≤ atomCoefficientBound j := by
  interval_cases j <;> norm_num [atomCoefficient, atomCoefficientBound, Finset.sum_range_succ]

theorem abs_atomJetPolynomial_eval_le {j : ℕ} (hj : j ≤ 4) {z : ℝ} (hz : 1 ≤ z) :
    |(atomJetPolynomial j).eval z| ≤ atomCoefficientBound j * z^(j+1) := by
  have hz0 : 0 ≤ z := by linarith
  rw [atomJetPolynomial_eval hj]
  calc
    _ ≤ ∑ i ∈ Finset.range (j+2), |atomCoefficient j i * z^i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (j+2), |atomCoefficient j i| * z^(j+1) := by
      apply Finset.sum_le_sum
      intro i hi
      have hij : i ≤ j+1 := by have := Finset.mem_range.mp hi; omega
      rw [abs_mul, abs_pow, abs_of_nonneg hz0]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hz hij) (abs_nonneg _)
    _ = (∑ i ∈ Finset.range (j+2), |atomCoefficient j i|) * z^(j+1) :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (sum_abs_atomCoefficient_le hj) (pow_nonneg hz0 _)

/-- The actual atom derivative after removing the common positive source prefactor. -/
noncomputable def normalizedAtomJet (j : ℕ) (q : ℝ) (n : ℕ) : ℝ :=
  (n:ℝ)^2 * (atomJetPolynomial j).eval (q*(n:ℝ)^2) *
    Real.exp (-(((n:ℝ)^2-1)*q))

theorem normalizedAtomJet_abs_le {j n : ℕ} (hj : j ≤ 4) (hn : 1 ≤ n)
    {q : ℝ} (hq : Real.pi ≤ q) :
    |normalizedAtomJet j q n| ≤ atomCoefficientBound j * q^(j+1) *
      ((n:ℝ)^(2*j+4) * Real.exp (-(((n:ℝ)^2-1)*q))) := by
  have hq1 : 1 ≤ q := by linarith [Real.pi_gt_d2]
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hz : 1 ≤ q*(n:ℝ)^2 := by nlinarith [sq_nonneg ((n:ℝ)-1)]
  have hb := abs_atomJetPolynomial_eval_le hj hz
  have hp : (n:ℝ)^2 * ((n:ℝ)^2)^(j+1) = (n:ℝ)^(2*j+4) := by
    rw [← pow_succ', ← pow_mul]
    congr 1
  unfold normalizedAtomJet
  rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg (Nat.cast_nonneg n), abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ (n:ℝ)^2 * (atomCoefficientBound j * (q*(n:ℝ)^2)^(j+1)) *
        Real.exp (-(((n:ℝ)^2-1)*q)) := by gcongr
    _ = atomCoefficientBound j * q^(j+1) *
        ((n:ℝ)^2 * ((n:ℝ)^2)^(j+1)) * Real.exp (-(((n:ℝ)^2-1)*q)) := by
      rw [mul_pow]
      ring
    _ = _ := by rw [hp]; ring

theorem normalizedAtomJet_tail_abs_le {j : ℕ} (hj : j ≤ 4)
    {q : ℝ} (hq : Real.pi ≤ q) (k : ℕ) :
    |normalizedAtomJet j q (k+4)| ≤
      atomCoefficientBound j * q^(j+1) * gaussianTailWeight (2*j+4) q k := by
  simpa only [gaussianTailWeight, Nat.cast_add, Nat.cast_ofNat] using
    normalizedAtomJet_abs_le hj (show 1 ≤ k+4 by omega) hq

/-- Complete normalized derivative tail beginning at the fourth positive atom. -/
noncomputable def normalizedTailJet (j : ℕ) (q : ℝ) : ℝ :=
  ∑' k : ℕ, normalizedAtomJet j q (k+4)

theorem normalizedTailJet_abs_le {j : ℕ} (hj : j ≤ 4) {q : ℝ} (hq : Real.pi ≤ q) :
    |normalizedTailJet j q| ≤
      2 * atomCoefficientBound j * 4^(2*j+4) * q^(j+1) * Real.exp (-15*q) := by
  have hm : 2*j+4 ≤ 12 := by omega
  have hs := (summable_gaussianTailWeight hm hq).mul_left (atomCoefficientBound j * q^(j+1))
  have ha : Summable (fun k : ℕ => |normalizedAtomJet j q (k+4)|) :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (normalizedAtomJet_tail_abs_le hj hq) hs
  have hcoef : 0 ≤ atomCoefficientBound j * q^(j+1) :=
    mul_nonneg (atomCoefficientBound_pos hj).le (pow_nonneg (Real.pi_pos.le.trans hq) _)
  unfold normalizedTailJet
  calc
    _ ≤ ∑' k : ℕ, |normalizedAtomJet j q (k+4)| := by
      simpa only [Real.norm_eq_abs] using
        norm_tsum_le_tsum_norm (f := fun k : ℕ => normalizedAtomJet j q (k+4))
          (by simpa only [Real.norm_eq_abs] using ha)
    _ ≤ ∑' k : ℕ, atomCoefficientBound j * q^(j+1) * gaussianTailWeight (2*j+4) q k :=
      ha.tsum_le_tsum (normalizedAtomJet_tail_abs_le hj hq) hs
    _ = (atomCoefficientBound j * q^(j+1)) * ∑' k : ℕ, gaussianTailWeight (2*j+4) q k :=
      tsum_mul_left
    _ ≤ (atomCoefficientBound j * q^(j+1)) * (2*4^(2*j+4)*Real.exp (-15*q)) :=
      mul_le_mul_of_nonneg_left (tsum_gaussianTailWeight_le hm hq) hcoef
    _ = _ := by ring

noncomputable def sourceScale (x : ℝ) : ℝ := Real.pi * Real.exp (2*x)

noncomputable def sourcePrefactor (x : ℝ) : ℝ :=
  2*Real.pi * Real.exp (5*x/2-sourceScale x)

theorem sourceScale_ge_pi {x : ℝ} (hx : 0 ≤ x) : Real.pi ≤ sourceScale x := by
  have he : 1 ≤ Real.exp (2*x) := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (show 0 ≤ 2*x by linarith)
  unfold sourceScale
  simpa only [mul_one] using mul_le_mul_of_nonneg_left he Real.pi_pos.le

theorem sourcePrefactor_pos (x : ℝ) : 0 < sourcePrefactor x := by
  unfold sourcePrefactor
  positivity

/-- Identification with the literal source derivative, valid at every order and point. -/
theorem iteratedDeriv_sourceTerm_eq_normalized (j n : ℕ) (x : ℝ) :
    iteratedDeriv j (fun y => thetaCuspSourceTerm y n) x =
      sourcePrefactor x * normalizedAtomJet j (sourceScale x) n := by
  rw [iteratedDeriv_thetaCuspSourceTerm_eq_polynomialAtom]
  unfold thetaCuspPolynomialAtom
  rw [derivativePolynomial_factor]
  simp only [eval_mul, eval_C, eval_pow, eval_X, eval_comp]
  have hscale : Real.pi * ((n:ℝ)*Real.exp x)^2 = sourceScale x * (n:ℝ)^2 := by
    unfold sourceScale
    rw [show Real.exp (2*x) = Real.exp x^2 from Real.exp_nat_mul x 2]
    ring
  simp only [neg_mul]
  rw [hscale]
  have he : Real.exp (x/2) * Real.exp x^2 * Real.exp (-(sourceScale x*(n:ℝ)^2)) =
      Real.exp (5*x/2-sourceScale x) * Real.exp (-(((n:ℝ)^2-1)*sourceScale x)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  unfold sourcePrefactor normalizedAtomJet
  calc
    _ = 2*Real.pi*(n:ℝ)^2*(atomJetPolynomial j).eval (sourceScale x*(n:ℝ)^2) *
        (Real.exp (x/2)*Real.exp x^2*Real.exp (-(sourceScale x*(n:ℝ)^2))) := by
      rw [mul_pow]
      ring
    _ = _ := by rw [he]; ring

/-- Uniform derivative-tail bound for the literal theta source through order four. -/
theorem abs_source_derivative_tail_le {j : ℕ} (hj : j ≤ 4) {x : ℝ} (hx : 0 ≤ x) :
    |∑' k : ℕ, iteratedDeriv j (fun y => thetaCuspSourceTerm y (k+4)) x| ≤
      sourcePrefactor x * (2 * atomCoefficientBound j * 4^(2*j+4) *
        (sourceScale x)^(j+1) * Real.exp (-15*sourceScale x)) := by
  simp_rw [iteratedDeriv_sourceTerm_eq_normalized]
  rw [tsum_mul_left, abs_mul, abs_of_pos (sourcePrefactor_pos x)]
  exact mul_le_mul_of_nonneg_left (normalizedTailJet_abs_le hj (sourceScale_ge_pi hx))
    (sourcePrefactor_pos x).le

end RHTower.ThetaCuspThreeAtomFourth
