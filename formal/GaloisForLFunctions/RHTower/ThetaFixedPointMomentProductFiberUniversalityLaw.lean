import GaloisForLFunctions.RHTower.XiCTaylorThetaTailArithmeticPotentialNormalForm
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailCompletedValuationReflection

/-!
# Theta fixed-point moment/product-fibre universality

At the spectral reflection fixed point, every potential remainder in the arithmetic atom normal
form is killed by its explicit factors of `z`. The same value and derivative are the zeroth and
first density moments, so both moments acquire closed endpoint formulas and every product-fibre
current becomes an explicit finite Gibbs sum.
-/

open Complex Real
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The zeroth moment of every positive square-index density atom is its closed arithmetic
endpoint value. -/
theorem thetaCuspTailSecondDensityAtomMoment_zero_eq_endpoint (m : ℕ) :
    thetaCuspTailSecondDensityAtomMoment (m + 1) 0 =
      (8 * Real.pi * ((m + 1 : ℕ) : ℝ) ^ (2 : ℕ) - 2) *
        Real.exp (-Real.pi * ((m + 1 : ℕ) : ℝ) ^ (2 : ℕ)) := by
  have hphase :=
    thetaCuspTailSecondDensityAtomPhase_eq_arithmeticEndpoint_sub_sq_potential
      (n := m + 1) (by omega) (z := 0) (by simp)
  rw [thetaCuspTailSecondDensityAtomPhase_zero m] at hphase
  simp only [pow_two, mul_zero, zero_mul, add_zero, sub_zero] at hphase
  have hre := congrArg Complex.re hphase
  simpa only [Complex.ofReal_re, Nat.cast_add, Nat.cast_one, Nat.cast_pow, pow_two] using hre

/-- The first moment of every positive square-index density atom is four times its Gaussian
endpoint weight. -/
theorem thetaCuspTailSecondDensityAtomMoment_one_eq_endpoint (m : ℕ) :
    thetaCuspTailSecondDensityAtomMoment (m + 1) 1 =
      4 * Real.exp (-Real.pi * ((m + 1 : ℕ) : ℝ) ^ (2 : ℕ)) := by
  have hphase :=
    thetaCuspTailSecondDensityAtomPhaseDerivative_eq_arithmeticEndpoint_sub_sq_potential
      (n := m + 1) (by omega) (z := 0) (by simp)
  rw [thetaCuspTailSecondDensityAtomPhaseDerivative_zero m] at hphase
  simp only [pow_two, mul_zero, zero_mul, sub_zero] at hphase
  have hcancel :
      (thetaCuspTailSecondDensityAtomMoment (m + 1) 1 : ℂ) =
        (4 : ℂ) * (Real.exp (-Real.pi * ((m + 1 : ℕ) : ℝ) ^ (2 : ℕ)) : ℂ) := by
    apply mul_left_cancel₀ Complex.I_ne_zero
    calc
      I * (thetaCuspTailSecondDensityAtomMoment (m + 1) 1 : ℂ) = _ := hphase
      _ = I * ((4 : ℂ) *
          (Real.exp (-Real.pi * ((m + 1 : ℕ) : ℝ) ^ (2 : ℕ)) : ℂ)) := by ring
  exact_mod_cast hcancel

/-- Every product-fibre current at the reflection fixed point is an explicit finite product of
the two arithmetic endpoint weights. -/
theorem thetaProductFiberActualPhaseCurrent_zero_eq_endpointGibbsSum (k : ℕ) :
    thetaProductFiberActualPhaseCurrent k 0 =
      ∑ q ∈ thetaPositiveFactorPairs k,
        (4 * Real.exp (-Real.pi * ((q.1 + 1 : ℕ) : ℝ) ^ (2 : ℕ))) *
          ((8 * Real.pi * ((q.2 + 1 : ℕ) : ℝ) ^ (2 : ℕ) - 2) *
            Real.exp (-Real.pi * ((q.2 + 1 : ℕ) : ℝ) ^ (2 : ℕ))) := by
  rw [thetaProductFiberActualPhaseCurrent_zero]
  apply Finset.sum_congr rfl
  intro q _hq
  rw [thetaCuspTailSecondDensityAtomMoment_one_eq_endpoint q.1,
    thetaCuspTailSecondDensityAtomMoment_zero_eq_endpoint q.2]

/-- **Theta fixed-point moment/product-fibre universality law.**  The reflection-fixed spectral
evaluation simultaneously closes every atom's first two moment coordinates and all finite
product-fibre currents into explicit Gaussian endpoint data. -/
theorem thetaFixedPoint_momentProductFiberUniversality :
    (∀ m : ℕ,
      thetaCuspTailSecondDensityAtomMoment (m + 1) 0 =
        (8 * Real.pi * ((m + 1 : ℕ) : ℝ) ^ (2 : ℕ) - 2) *
          Real.exp (-Real.pi * ((m + 1 : ℕ) : ℝ) ^ (2 : ℕ))) ∧
    (∀ m : ℕ,
      thetaCuspTailSecondDensityAtomMoment (m + 1) 1 =
        4 * Real.exp (-Real.pi * ((m + 1 : ℕ) : ℝ) ^ (2 : ℕ))) ∧
    ∀ k : ℕ,
      thetaProductFiberActualPhaseCurrent k 0 =
        ∑ q ∈ thetaPositiveFactorPairs k,
          (4 * Real.exp (-Real.pi * ((q.1 + 1 : ℕ) : ℝ) ^ (2 : ℕ))) *
            ((8 * Real.pi * ((q.2 + 1 : ℕ) : ℝ) ^ (2 : ℕ) - 2) *
              Real.exp (-Real.pi * ((q.2 + 1 : ℕ) : ℝ) ^ (2 : ℕ))) := by
  exact ⟨thetaCuspTailSecondDensityAtomMoment_zero_eq_endpoint,
    thetaCuspTailSecondDensityAtomMoment_one_eq_endpoint,
    thetaProductFiberActualPhaseCurrent_zero_eq_endpointGibbsSum⟩

end

end RHTower
