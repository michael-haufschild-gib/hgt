import GaloisForLFunctions.RHTower.LaguerreJensenRecurrence
import GaloisForLFunctions.HTGeometry.HermitePerturbationRealRoots

/-!
# Hermite normalization of the finite Laguerre recurrence

The recurrence remains regular at width zero, where it is exactly the
probabilists' Hermite recurrence.
-/

open Polynomial Filter Topology
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

def laguerreHermite (δ : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X
  | d + 2 => C ((1 + ((d : ℝ) + 1) * δ ^ 2)⁻¹) *
      ((X + C (2 * ((d : ℝ) + 1) * δ)) * laguerreHermite δ (d + 1) -
        C ((d : ℝ) + 1) * laguerreHermite δ d)

theorem laguerreHermite_denominator_pos (δ : ℝ) (d : ℕ) :
    0 < 1 + ((d : ℝ) + 1) * δ ^ 2 := by positivity

theorem laguerreHermite_eval_add_two (δ x : ℝ) (d : ℕ) :
    (1 + ((d : ℝ) + 1) * δ ^ 2) * (laguerreHermite δ (d + 2)).eval x =
      (x + 2 * ((d : ℝ) + 1) * δ) * (laguerreHermite δ (d + 1)).eval x -
        ((d : ℝ) + 1) * (laguerreHermite δ d).eval x := by
  have hd := laguerreHermite_denominator_pos δ d
  simp only [laguerreHermite, eval_mul, eval_C, eval_sub, eval_add, eval_X]
  field_simp

/-- Exact finite normalization, before taking any limit. -/
theorem laguerreHermite_eval_eq_laguerre {b δ : ℝ} (hb : 0 < b)
    (hδ : b * δ ^ 2 = 1) (d : ℕ) (x : ℝ) :
    δ ^ d * (laguerreHermite δ d).eval x = (laguerreJensen b d).eval (δ * x - 1) := by
  induction d using Nat.twoStepInduction with
  | zero => simp [laguerreHermite, laguerreJensen_zero]
  | one => simp [laguerreHermite, laguerreJensen_one hb]
  | more d ih₀ ih₁ =>
    have hrec := congrArg (fun P : ℝ[X] => P.eval (δ * x - 1)) (laguerreJensen_add_two hb d)
    simp only [eval_mul, eval_C, eval_sub, eval_add, eval_X] at hrec
    rw [← ih₀, ← ih₁] at hrec
    have hcoef : (b + (d : ℝ) + 1) * δ ^ 2 = 1 + ((d : ℝ) + 1) * δ ^ 2 := by
      nlinarith [hδ]
    have hlinear : (b + 2 * (d : ℝ) + 2 + b * (δ * x - 1)) * δ =
        x + 2 * ((d : ℝ) + 1) * δ := by
      linear_combination x * hδ
    apply mul_left_cancel₀ (show b + (d : ℝ) + 1 ≠ 0 by positivity)
    calc
      (b + (d : ℝ) + 1) * (δ ^ (d + 2) * (laguerreHermite δ (d + 2)).eval x) =
          δ ^ d * (((b + (d : ℝ) + 1) * δ ^ 2) * (laguerreHermite δ (d + 2)).eval x) := by
            rw [pow_add]
            ring
      _ = δ ^ d * ((x + 2 * ((d : ℝ) + 1) * δ) *
          (laguerreHermite δ (d + 1)).eval x - ((d : ℝ) + 1) * (laguerreHermite δ d).eval x) := by
            rw [hcoef, laguerreHermite_eval_add_two]
      _ = (b + 2 * (d : ℝ) + 2 + b * (δ * x - 1)) *
          (δ ^ (d + 1) * (laguerreHermite δ (d + 1)).eval x) -
            ((d : ℝ) + 1) * (δ ^ d * (laguerreHermite δ d).eval x) := by
              rw [← hlinear, pow_succ]
              ring
      _ = _ := hrec.symm

theorem laguerreHermite_width_zero (d : ℕ) : laguerreHermite 0 d = hermiteReal d := by
  induction d using Nat.twoStepInduction with
  | zero => apply Polynomial.funext; intro x; simp [laguerreHermite]
  | one => apply Polynomial.funext; intro x; simp [laguerreHermite]
  | more d ih₀ ih₁ => simp [laguerreHermite, ih₀, ih₁, hermiteReal_add_two]

theorem tendsto_laguerreHermite_eval {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝 0))
    (d : ℕ) (x : ℝ) :
    Tendsto (fun n => (laguerreHermite (δ n) d).eval x) atTop (𝓝 ((hermiteReal d).eval x)) := by
  induction d using Nat.twoStepInduction with
  | zero => simp [laguerreHermite]
  | one => simp [laguerreHermite]
  | more d ih₀ ih₁ =>
    have hden : Tendsto (fun n => (1 + ((d : ℝ) + 1) * δ n ^ 2)⁻¹) atTop (𝓝 1) := by
      have hbase : Tendsto (fun n => 1 + ((d : ℝ) + 1) * δ n ^ 2) atTop (𝓝 (1 : ℝ)) := by
        simpa using tendsto_const_nhds.add ((hδ.pow 2).const_mul ((d : ℝ) + 1))
      simpa using hbase.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    have hlin : Tendsto (fun n => x + 2 * ((d : ℝ) + 1) * δ n) atTop (𝓝 x) := by
      simpa using tendsto_const_nhds.add (hδ.const_mul (2 * ((d : ℝ) + 1)))
    have h := hden.mul ((hlin.mul ih₁).sub (ih₀.const_mul ((d : ℝ) + 1)))
    simpa only [laguerreHermite, eval_mul, eval_C, eval_sub, eval_add, eval_X, one_mul,
      eval_hermiteReal_add_two] using h

end RHTower
