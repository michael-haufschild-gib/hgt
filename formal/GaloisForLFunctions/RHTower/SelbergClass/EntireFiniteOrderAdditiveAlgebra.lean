import GaloisForLFunctions.RHTower.SelbergClass.EntireFiniteOrderAlgebra
import GaloisForLFunctions.HTGeometry.ComplexExponentialPolynomial

/-!
# Additive algebra of entire finite-order functions

Entire finite-order functions are closed under subtraction. This module also installs the identity
and polynomial-evaluation carriers needed to turn cofinite zero sampling into full zero sampling.
-/

open Metric Set

namespace RHTower

noncomputable section

/-- Differences of entire finite-order functions retain exponential-power growth outside the unit
disk. The common order is the maximum of the two input orders. -/
theorem EntireFiniteOrder.hasExponentialPowerGrowthOutside_sub
    (F G : EntireFiniteOrder) :
    HasExponentialPowerGrowthOutside (fun z : ℂ ↦ F z - G z) := by
  rcases F.growth with ⟨AF, BF, ρF, hAF, hBF, hρF, hF⟩
  rcases G.growth with ⟨AG, BG, ρG, hAG, hBG, hρG, hG⟩
  refine ⟨AF + AG, BF + BG, max ρF ρG, 1, add_pos hAF hAG, add_pos hBF hBG,
    hρF.trans (le_max_left _ _), zero_le_one, ?_⟩
  intro z hz
  have hpowF : ‖z‖ ^ ρF ≤ ‖z‖ ^ max ρF ρG :=
    Real.rpow_le_rpow_of_exponent_le hz (le_max_left _ _)
  have hpowG : ‖z‖ ^ ρG ≤ ‖z‖ ^ max ρF ρG :=
    Real.rpow_le_rpow_of_exponent_le hz (le_max_right _ _)
  have hpow0 : 0 ≤ ‖z‖ ^ max ρF ρG := Real.rpow_nonneg (norm_nonneg z) _
  have htermF : BF * ‖z‖ ^ ρF ≤ (BF + BG) * ‖z‖ ^ max ρF ρG := by
    calc
      BF * ‖z‖ ^ ρF ≤ BF * ‖z‖ ^ max ρF ρG :=
        mul_le_mul_of_nonneg_left hpowF hBF.le
      _ ≤ (BF + BG) * ‖z‖ ^ max ρF ρG := by
        nlinarith
  have htermG : BG * ‖z‖ ^ ρG ≤ (BF + BG) * ‖z‖ ^ max ρF ρG := by
    calc
      BG * ‖z‖ ^ ρG ≤ BG * ‖z‖ ^ max ρF ρG :=
        mul_le_mul_of_nonneg_left hpowG hBG.le
      _ ≤ (BF + BG) * ‖z‖ ^ max ρF ρG := by
        nlinarith
  have hexpF : Real.exp (BF * ‖z‖ ^ ρF) ≤
      Real.exp ((BF + BG) * ‖z‖ ^ max ρF ρG) := Real.exp_le_exp.mpr htermF
  have hexpG : Real.exp (BG * ‖z‖ ^ ρG) ≤
      Real.exp ((BF + BG) * ‖z‖ ^ max ρF ρG) := Real.exp_le_exp.mpr htermG
  calc
    ‖F z - G z‖ ≤ ‖F z‖ + ‖G z‖ := norm_sub_le _ _
    _ ≤ AF * Real.exp (BF * ‖z‖ ^ ρF) + AG * Real.exp (BG * ‖z‖ ^ ρG) :=
      add_le_add (hF z) (hG z)
    _ ≤ AF * Real.exp ((BF + BG) * ‖z‖ ^ max ρF ρG) +
        AG * Real.exp ((BF + BG) * ‖z‖ ^ max ρF ρG) :=
      add_le_add (mul_le_mul_of_nonneg_left hexpF hAF.le)
        (mul_le_mul_of_nonneg_left hexpG hAG.le)
    _ = (AF + AG) * Real.exp ((BF + BG) * ‖z‖ ^ max ρF ρG) :=
      (add_mul AF AG _).symm

/-- Pointwise subtraction preserves the project's entire finite-order carrier. -/
def EntireFiniteOrder.sub (F G : EntireFiniteOrder) : EntireFiniteOrder :=
  EntireFiniteOrder.ofOutside (fun z : ℂ ↦ F z - G z) (F.analytic.sub G.analytic)
    (F.hasExponentialPowerGrowthOutside_sub G)

@[simp]
theorem EntireFiniteOrder.sub_apply (F G : EntireFiniteOrder) (z : ℂ) :
    F.sub G z = F z - G z := rfl

/-- The identity entire function, packaged with order-one growth. -/
def entireFiniteOrderId : EntireFiniteOrder where
  toFun := fun z : ℂ ↦ z
  analytic := analyticOnNhd_id
  growth := by
    refine ⟨1, 1, 1, zero_lt_one, zero_lt_one, zero_le_one, ?_⟩
    intro z
    calc
      ‖z‖ ≤ ‖z‖ + 1 := by linarith
      _ ≤ Real.exp ‖z‖ := Real.add_one_le_exp ‖z‖
      _ = 1 * Real.exp (1 * ‖z‖ ^ (1 : ℝ)) := by simp

@[simp]
theorem entireFiniteOrderId_apply (z : ℂ) : entireFiniteOrderId z = z := rfl

/-- Every complex polynomial evaluation is an entire finite-order function. -/
def entireFiniteOrderPolynomial (Q : Polynomial ℂ) : EntireFiniteOrder where
  toFun := fun z : ℂ ↦ Q.eval z
  analytic := (Polynomial.differentiable Q).differentiableOn.analyticOnNhd isOpen_univ
  growth := by
    let S : ℝ := ∑ k ∈ Finset.range (Q.natDegree + 1), ‖Q.coeff k‖
    refine ⟨max 1 S, (Q.natDegree : ℝ) + 1, 1,
      lt_of_lt_of_le zero_lt_one (le_max_left _ _), by positivity, zero_le_one, ?_⟩
    intro z
    have hS : 0 ≤ S := Finset.sum_nonneg (fun k _ ↦ norm_nonneg _)
    have hEval : ‖Q.eval z‖ ≤ S * Real.exp ((Q.natDegree : ℝ) * ‖z‖) := by
      refine le_trans (GaloisForLFunctions.HTGeometry.CExpPoly.norm_eval_le Q z) ?_
      exact mul_le_mul_of_nonneg_left
        (GaloisForLFunctions.HTGeometry.CExpPoly.one_add_norm_pow_le_exp Q.natDegree z) hS
    have hExp : Real.exp ((Q.natDegree : ℝ) * ‖z‖) ≤
        Real.exp (((Q.natDegree : ℝ) + 1) * ‖z‖) := by
      apply Real.exp_le_exp.mpr
      nlinarith [norm_nonneg z]
    calc
      ‖Q.eval z‖ ≤ S * Real.exp ((Q.natDegree : ℝ) * ‖z‖) := hEval
      _ ≤ max 1 S * Real.exp (((Q.natDegree : ℝ) + 1) * ‖z‖) :=
        mul_le_mul (le_max_right _ _) hExp (Real.exp_pos _).le (by positivity)
      _ = max 1 S * Real.exp (((Q.natDegree : ℝ) + 1) * ‖z‖ ^ (1 : ℝ)) := by
        rw [Real.rpow_one]

@[simp]
theorem entireFiniteOrderPolynomial_apply (Q : Polynomial ℂ) (z : ℂ) :
    entireFiniteOrderPolynomial Q z = Q.eval z := rfl

end

end RHTower
