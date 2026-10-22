import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSecondHarmonicComplementaryHypergeometric
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Formal Gauss ODE for the BM complementary second harmonic

For a formal hypergeometric series `F` and Euler operator `θ = X d/dX`, the Gauss equation is

`θ²F + (c-1)θF - X(θ²F + (a+b)θF + abF) = 0`.

Its coefficient at degree `j+1` is exactly the Pochhammer successor recurrence. This module proves
that formal ODE over `ℂ` away from denominator-parameter collisions and specializes it to the BM
complementary `++` series, including every Xi fibre.
-/

open Complex Nat Polynomial
open scoped PowerSeries

namespace RHTower

noncomputable section

/-- Opaque coefficient wrapper for formal-power-series calculations. -/
def ordinaryHypergeometricFormalCoefficient
    (a b c : ℂ) (j : ℕ) : ℂ :=
  ordinaryHypergeometricCoefficient a b c j

/-- Formal power series with ordinary hypergeometric coefficients. -/
def ordinaryHypergeometricFormalPowerSeries
    (a b c : ℂ) : ℂ⟦X⟧ :=
  PowerSeries.mk (ordinaryHypergeometricFormalCoefficient a b c)

/-- Euler operator `θ = X d/dX` on complex formal power series. -/
def hypergeometricEulerOperator (F : ℂ⟦X⟧) : ℂ⟦X⟧ :=
  PowerSeries.X * PowerSeries.derivative ℂ F

/-- Euler operator multiplies the degree-`j` coefficient by `j`. -/
theorem coeff_hypergeometricEulerOperator
    (F : ℂ⟦X⟧) (j : ℕ) :
    PowerSeries.coeff j (hypergeometricEulerOperator F) =
      (j : ℂ) * PowerSeries.coeff j F := by
  cases j with
  | zero => simp [hypergeometricEulerOperator]
  | succ j =>
      rw [hypergeometricEulerOperator]
      have h := PowerSeries.coeff_X_pow_mul
        (PowerSeries.derivative ℂ F) 1 j
      have h' :
          PowerSeries.coeff (j + 1)
              (PowerSeries.X * PowerSeries.derivative ℂ F) =
            PowerSeries.coeff j (PowerSeries.derivative ℂ F) := by
        simpa only [pow_one, Nat.add_comm] using h
      rw [h', PowerSeries.coeff_derivative]
      push_cast
      ring

/-- Multiplication by `X` shifts coefficient `j` to coefficient `j+1`. -/
theorem coeff_X_mul_succ (F : ℂ⟦X⟧) (j : ℕ) :
    PowerSeries.coeff (j + 1) (PowerSeries.X * F) =
      PowerSeries.coeff j F := by
  simpa only [pow_one] using PowerSeries.coeff_X_pow_mul F 1 j

/-- Formal Euler-form Gauss differential residual of the ordinary hypergeometric series. -/
def ordinaryHypergeometricFormalEulerResidual
    (a b c : ℂ) : ℂ⟦X⟧ :=
  let F := ordinaryHypergeometricFormalPowerSeries a b c
  hypergeometricEulerOperator (hypergeometricEulerOperator F) +
      PowerSeries.C (c - 1) * hypergeometricEulerOperator F -
    PowerSeries.X *
      (hypergeometricEulerOperator (hypergeometricEulerOperator F) +
        PowerSeries.C (a + b) * hypergeometricEulerOperator F +
        PowerSeries.C (a * b) * F)

/-- Hypergeometric formal series solves the Euler-form Gauss equation coefficientwise. -/
theorem ordinaryHypergeometricFormalEulerResidual_eq_zero
    (a b c : ℂ) (hc : ∀ j : ℕ, (j : ℂ) ≠ -c) :
    ordinaryHypergeometricFormalEulerResidual a b c = 0 := by
  apply PowerSeries.ext
  intro j
  cases j with
  | zero =>
      rw [ordinaryHypergeometricFormalEulerResidual,
        map_sub, map_add, map_add,
        coeff_hypergeometricEulerOperator,
        PowerSeries.coeff_C_mul,
        coeff_hypergeometricEulerOperator,
        PowerSeries.coeff_zero_X_mul,
        map_zero]
      norm_num
  | succ j =>
      rw [ordinaryHypergeometricFormalEulerResidual,
        map_sub, map_add, map_add,
        coeff_hypergeometricEulerOperator,
        PowerSeries.coeff_C_mul,
        coeff_hypergeometricEulerOperator,
        coeff_X_mul_succ]
      simp only [map_add, add_mul,
        coeff_hypergeometricEulerOperator,
        PowerSeries.coeff_C_mul,
        ordinaryHypergeometricFormalPowerSeries,
        PowerSeries.coeff_mk, map_zero]
      have hpc : (ascPochhammer ℂ j).eval c ≠ 0 := by
        rw [ne_eq, ascPochhammer_eval_eq_zero_iff]
        push Not
        intro k hk hkc
        exact hc k hkc
      have hcj : c + (j : ℂ) ≠ 0 := by
        intro h
        apply hc j
        linear_combination h
      have hrec :
          ((j + 1 : ℕ) : ℂ) * (c + (j : ℂ)) *
              ordinaryHypergeometricFormalCoefficient a b c (j + 1) =
            (a + (j : ℂ)) * (b + (j : ℂ)) *
              ordinaryHypergeometricFormalCoefficient a b c j := by
        exact ordinaryHypergeometricCoefficient_succ_recurrence
          a b c j hpc hcj
      rw [Nat.cast_add, Nat.cast_one] at hrec ⊢
      linear_combination hrec

/-- BM complementary `++` formal series solves its transformed Gauss equation. -/
theorem d4BMPlusPlusComplementaryHypergeometricFormalEulerResidual_eq_zero
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    ordinaryHypergeometricFormalEulerResidual
      (d4BMPlusPlusComplementaryHypergeometricA n chi)
      (d4BMPlusPlusComplementaryHypergeometricB n chi)
      (d4BMPlusPlusComplementaryHypergeometricC n chi) = 0 := by
  apply ordinaryHypergeometricFormalEulerResidual_eq_zero
  intro j
  exact
    (d4BMPlusPlusComplementaryHypergeometricParameters_ne_negNat
      n chi hchi j).2.2

/-- Every Xi-fibre complementary `++` formal series solves its transformed Gauss equation. -/
theorem d4BMXiPlusPlusComplementaryHypergeometricFormalEulerResidual_eq_zero
    (n : ℕ) (q : XiZeroCopy) :
    ordinaryHypergeometricFormalEulerResidual
      (d4BMPlusPlusComplementaryHypergeometricA
        n (d4BMXiMixedHorizonAngularMomentum q))
      (d4BMPlusPlusComplementaryHypergeometricB
        n (d4BMXiMixedHorizonAngularMomentum q))
      (d4BMPlusPlusComplementaryHypergeometricC
        n (d4BMXiMixedHorizonAngularMomentum q)) = 0 := by
  exact d4BMPlusPlusComplementaryHypergeometricFormalEulerResidual_eq_zero n _
    (d4BMXiMixedHorizonAngularMomentum_re_ne_zero q)

end

end RHTower
