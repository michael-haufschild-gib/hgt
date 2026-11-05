import GaloisForLFunctions.RHTower.Jensen.ExplicitConcentration
import GaloisForLFunctions.RHTower.XiJensenHermiteLimit

/-!
# Quantitative Jensen–Hermite approximation

Finite fluctuation bounds propagate through the exact mixed Laguerre
recurrence. The constants account for both coefficient perturbations and
the denominator, giving explicit errors for the actual Xi Jensen family.
-/

open Polynomial
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

/-- A positive recurrence majorizing Hermite values on `[-R,R]`. -/
def hermiteValueBound (R : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => R
  | j + 2 => R * hermiteValueBound R (j + 1) + ((j : ℝ) + 1) * hermiteValueBound R j

theorem hermiteValueBound_nonneg {R : ℝ} (hR : 0 ≤ R) (j : ℕ) :
    0 ≤ hermiteValueBound R j := by
  induction j using Nat.twoStepInduction with
  | zero => norm_num [hermiteValueBound]
  | one => exact hR
  | more j h₀ h₁ => simp only [hermiteValueBound]; positivity

theorem abs_hermiteReal_eval_le {R x : ℝ} (hR : 0 ≤ R) (hx : |x| ≤ R) (j : ℕ) :
    |(hermiteReal j).eval x| ≤ hermiteValueBound R j := by
  induction j using Nat.twoStepInduction with
  | zero => simp [hermiteValueBound]
  | one => simpa only [eval_hermiteReal_one, hermiteValueBound] using hx
  | more j h₀ h₁ =>
    rw [eval_hermiteReal_add_two, hermiteValueBound]
    calc
      _ ≤ |x * (hermiteReal (j + 1)).eval x| +
          |((j : ℝ) + 1) * (hermiteReal j).eval x| := abs_sub _ _
      _ = |x| * |(hermiteReal (j + 1)).eval x| +
          ((j : ℝ) + 1) * |(hermiteReal j).eval x| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (j : ℝ) + 1)]
      _ ≤ _ := add_le_add (mul_le_mul hx h₁ (abs_nonneg _) hR)
        (mul_le_mul_of_nonneg_left h₀ (by positivity))

/-- Error amplification in the mixed Laguerre recurrence. -/
def xiJensenHermiteErrorConstant (R : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => 2 * R + 1
  | j + 2 =>
      (2 * R + 2 * ((j : ℝ) + 1) + 1) * xiJensenHermiteErrorConstant R (j + 1) +
        ((j : ℝ) + 1) * xiJensenHermiteErrorConstant R j +
        2 * ((j : ℝ) + 1) * hermiteValueBound R (j + 1) +
        ((j : ℝ) + 1) * hermiteValueBound R (j + 2)

theorem xiJensenHermiteErrorConstant_nonneg {R : ℝ} (hR : 0 ≤ R) (j : ℕ) :
    0 ≤ xiJensenHermiteErrorConstant R j := by
  induction j using Nat.twoStepInduction with
  | zero => norm_num [xiJensenHermiteErrorConstant]
  | one => simp only [xiJensenHermiteErrorConstant]; positivity
  | more j h₀ h₁ =>
    have hb₁ := hermiteValueBound_nonneg hR (j + 1)
    have hb₂ := hermiteValueBound_nonneg hR (j + 2)
    simp only [xiJensenHermiteErrorConstant]
    positivity

private theorem abs_delta_mul_sub_one_le {δ R x : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hx : |x| ≤ R) : |δ * x - 1| ≤ R + 1 := by
  calc
    _ ≤ |δ * x| + |(1 : ℝ)| := abs_sub _ _
    _ = δ * |x| + 1 := by rw [abs_mul, abs_of_nonneg hδ, abs_one]
    _ ≤ 1 * R + 1 := add_le_add (mul_le_mul hδ1 hx (abs_nonneg _) zero_le_one) (le_refl 1)
    _ = _ := by ring

private theorem abs_add_sub_add_sub_le (a b c d e : ℝ) :
    |a + b - c + d - e| ≤ |a| + |b| + |c| + |d| + |e| := by
  linarith only [abs_sub (a + b - c + d) e, abs_add_le (a + b - c) d,
    abs_sub (a + b) c, abs_add_le a b]

/-- Every mixed expectation error is controlled by the same finite moment accuracy. -/
theorem xiThetaHermiteMixed_error_bound (n D d k : ℕ) {R η x : ℝ}
    (hR : 0 ≤ R) (hη : 0 ≤ η) (hη1 : η ≤ 1) (hδ : xiJensenDelta n ≤ η)
    (hm : ∀ j ≤ D,
      |xiThetaExpectation n (xiThetaFluctuation n ^ j) - (if j = 0 then 1 else 0)| ≤ η)
    (hdk : d + k ≤ D) (hx : |x| ≤ R) :
    |xiThetaHermiteMixed n d k x - (if k = 0 then (hermiteReal d).eval x else 0)| ≤
      xiJensenHermiteErrorConstant R d * η := by
  have hδ0 := (xiJensenDelta_pos n).le
  have hδ1 := hδ.trans hη1
  have hlin := abs_delta_mul_sub_one_le hδ0 hδ1 hx
  induction d using Nat.twoStepInduction generalizing k with
  | zero =>
    simpa only [xiThetaHermiteMixed_zero, eval_hermiteReal_zero,
      xiJensenHermiteErrorConstant, one_mul] using hm k (by omega)
  | one =>
    have h₀ := hm k (by omega)
    have h₁ := hm (k + 1) (by omega)
    simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false, sub_zero] at h₁
    rw [xiThetaHermiteMixed_one, eval_hermiteReal_one, xiJensenHermiteErrorConstant]
    have he : x * xiThetaExpectation n (xiThetaFluctuation n ^ k) +
        (xiJensenDelta n * x - 1) * xiThetaExpectation n (xiThetaFluctuation n ^ (k + 1)) -
          (if k = 0 then x else 0) =
        x * (xiThetaExpectation n (xiThetaFluctuation n ^ k) - (if k = 0 then 1 else 0)) +
          (xiJensenDelta n * x - 1) * xiThetaExpectation n (xiThetaFluctuation n ^ (k + 1)) := by
      split_ifs <;> ring
    rw [he]
    calc
      _ ≤ |x * (xiThetaExpectation n (xiThetaFluctuation n ^ k) - (if k = 0 then 1 else 0))| +
          |(xiJensenDelta n * x - 1) * xiThetaExpectation n (xiThetaFluctuation n ^ (k + 1))| :=
        abs_add_le _ _
      _ ≤ R * η + (R + 1) * η := by
        rw [abs_mul, abs_mul]
        exact add_le_add (mul_le_mul hx h₀ (abs_nonneg _) hR)
          (mul_le_mul hlin h₁ (abs_nonneg _) (by positivity))
      _ = _ := by ring
  | more j ih₀ ih₁ =>
    have he₀ := ih₀ k (by omega)
    have he₁ := ih₁ k (by omega)
    have hshift := ih₁ (k + 1) (by omega)
    simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false, sub_zero] at hshift
    have hT₁ : |if k = 0 then (hermiteReal (j + 1)).eval x else 0| ≤
        hermiteValueBound R (j + 1) := by
      split_ifs
      · exact abs_hermiteReal_eval_le hR hx _
      · simpa only [abs_zero] using hermiteValueBound_nonneg hR (j + 1)
    have hT₂ : |if k = 0 then (hermiteReal (j + 2)).eval x else 0| ≤
        hermiteValueBound R (j + 2) := by
      split_ifs
      · exact abs_hermiteReal_eval_le hR hx _
      · simpa only [abs_zero] using hermiteValueBound_nonneg hR (j + 2)
    have hden : 0 < 1 + ((j : ℝ) + 1) * xiJensenDelta n ^ 2 := by positivity
    have hden1 : 1 ≤ 1 + ((j : ℝ) + 1) * xiJensenDelta n ^ 2 :=
      le_add_of_nonneg_right (by positivity)
    have hsq : xiJensenDelta n ^ 2 ≤ η := by
      have h := mul_le_mul_of_nonneg_left hδ1 hδ0
      nlinarith only [h, hδ]
    have hA : |x + 2 * ((j : ℝ) + 1) * xiJensenDelta n| ≤ R + 2 * ((j : ℝ) + 1) := by
      calc
        _ ≤ |x| + |2 * ((j : ℝ) + 1) * xiJensenDelta n| := abs_add_le _ _
        _ = |x| + 2 * ((j : ℝ) + 1) * xiJensenDelta n := by
          rw [abs_of_nonneg (by positivity : 0 ≤ 2 * ((j : ℝ) + 1) * xiJensenDelta n)]
        _ ≤ _ := add_le_add hx (by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hδ1
            (show 0 ≤ 2 * ((j : ℝ) + 1) by positivity))
    -- Multiplying by the positive denominator exposes all perturbation terms.
    have heq : (1 + ((j : ℝ) + 1) * xiJensenDelta n ^ 2) *
        (xiThetaHermiteMixed n (j + 2) k x - (if k = 0 then (hermiteReal (j + 2)).eval x else 0)) =
        (x + 2 * ((j : ℝ) + 1) * xiJensenDelta n) *
          (xiThetaHermiteMixed n (j + 1) k x - (if k = 0 then (hermiteReal (j + 1)).eval x else 0)) +
        (xiJensenDelta n * x - 1) * xiThetaHermiteMixed n (j + 1) (k + 1) x -
        ((j : ℝ) + 1) * (xiThetaHermiteMixed n j k x - (if k = 0 then (hermiteReal j).eval x else 0)) +
        2 * ((j : ℝ) + 1) * xiJensenDelta n * (if k = 0 then (hermiteReal (j + 1)).eval x else 0) -
        ((j : ℝ) + 1) * xiJensenDelta n ^ 2 * (if k = 0 then (hermiteReal (j + 2)).eval x else 0) := by
      rw [xiThetaHermiteMixed_add_two, mul_sub, ← mul_assoc, mul_inv_cancel₀ hden.ne', one_mul]
      cases k <;> simp only [Nat.succ_ne_zero, if_false, ite_true,
        eval_hermiteReal_add_two] <;> ring
    have hscale : |xiThetaHermiteMixed n (j + 2) k x -
        (if k = 0 then (hermiteReal (j + 2)).eval x else 0)| ≤
        |(1 + ((j : ℝ) + 1) * xiJensenDelta n ^ 2) *
          (xiThetaHermiteMixed n (j + 2) k x - (if k = 0 then (hermiteReal (j + 2)).eval x else 0))| := by
      rw [abs_mul, abs_of_pos hden]
      exact le_mul_of_one_le_left (abs_nonneg _) hden1
    rw [heq] at hscale
    have ht₁ : |(x + 2 * ((j : ℝ) + 1) * xiJensenDelta n) *
        (xiThetaHermiteMixed n (j + 1) k x - (if k = 0 then (hermiteReal (j + 1)).eval x else 0))| ≤
        (R + 2 * ((j : ℝ) + 1)) * (xiJensenHermiteErrorConstant R (j + 1) * η) := by
      rw [abs_mul]
      exact mul_le_mul hA he₁ (abs_nonneg _) (by positivity)
    have ht₂ : |(xiJensenDelta n * x - 1) * xiThetaHermiteMixed n (j + 1) (k + 1) x| ≤
        (R + 1) * (xiJensenHermiteErrorConstant R (j + 1) * η) := by
      rw [abs_mul]
      exact mul_le_mul hlin hshift (abs_nonneg _) (by positivity)
    have ht₃ : |((j : ℝ) + 1) *
        (xiThetaHermiteMixed n j k x - (if k = 0 then (hermiteReal j).eval x else 0))| ≤
        ((j : ℝ) + 1) * (xiJensenHermiteErrorConstant R j * η) := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (j : ℝ) + 1)]
      exact mul_le_mul_of_nonneg_left he₀ (by positivity)
    have ht₄ : |2 * ((j : ℝ) + 1) * xiJensenDelta n *
        (if k = 0 then (hermiteReal (j + 1)).eval x else 0)| ≤
        (2 * ((j : ℝ) + 1) * η) * hermiteValueBound R (j + 1) := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * ((j : ℝ) + 1) * xiJensenDelta n)]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hδ (by positivity)) hT₁
        (abs_nonneg _) (by positivity)
    have ht₅ : |((j : ℝ) + 1) * xiJensenDelta n ^ 2 *
        (if k = 0 then (hermiteReal (j + 2)).eval x else 0)| ≤
        (((j : ℝ) + 1) * η) * hermiteValueBound R (j + 2) := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ ((j : ℝ) + 1) * xiJensenDelta n ^ 2)]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hsq (by positivity)) hT₂
        (abs_nonneg _) (by positivity)
    exact (hscale.trans ((abs_add_sub_add_sub_le _ _ _ _ _).trans
      (add_le_add (add_le_add (add_le_add (add_le_add ht₁ ht₂) ht₃) ht₄) ht₅))).trans_eq
        (by rw [xiJensenHermiteErrorConstant]; ring)

/-- Explicit uniform evaluation error for the actual normalized Xi Jensen polynomial. -/
theorem xiJensenHermitePolynomial_eval_error_le (n d : ℕ) {R x : ℝ}
    (hR : 0 ≤ R) (hx : |x| ≤ R) (hs : 2 ≤ thetaJensenSaddle n)
    (hn : 4 * (d + 1) ≤ n) (hF : xiJensenFluctuationBound d ≤ thetaJensenSaddle n) :
    |(xiJensenHermitePolynomial n d).eval x - (hermiteReal d).eval x| ≤
      xiJensenHermiteErrorConstant R d * Real.sqrt (xiJensenFluctuationBound d / thetaJensenSaddle n) := by
  have hη1 : Real.sqrt (xiJensenFluctuationBound d / thetaJensenSaddle n) ≤ 1 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨zero_le_one, ?_⟩
    simpa only [one_pow] using (div_le_one (thetaJensenSaddle_pos n)).mpr hF
  have h := xiThetaHermiteMixed_error_bound n d d 0 hR (Real.sqrt_nonneg _) hη1
    (xiJensenDelta_le_fluctuationBound n d hs)
    (fun k hk => xiThetaExpectation_fluctuation_error_le n d k hs hn hk) (by omega) hx
  simpa only [xiThetaHermiteMixed, pow_zero, one_mul, if_pos rfl, ite_true,
    eval_xiJensenHermitePolynomial] using h

end RHTower

#print axioms RHTower.xiThetaHermiteMixed_error_bound
#print axioms RHTower.xiJensenHermitePolynomial_eval_error_le
