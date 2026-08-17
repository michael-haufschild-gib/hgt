import GaloisForLFunctions.HTGeometry.BesselK1PoincareForm
import GaloisForLFunctions.HTGeometry.BesselK1SectorialRemainder

/-!
# The ray coefficients are the Poincaré coefficients

The ray expansion and the Gaussian-moment expansion of the order-one Schläfli integral are two
presentations of the same asymptotic, and their coefficients agree term by term.  The identification
rests on two elementary facts: the half-integer Gamma values are the Gaussian moment factors times
the square root of `π`, and the binomial coefficients of `(1+x)^{1/2}` and `(1+x)^{-1/2}` satisfy the
Pascal relation coming from `(1+x)^{1/2} = (1+x)(1+x)^{-1/2}`.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section GammaValues

theorem gaussianMomentFactor_succ (k : ℕ) :
    gaussianMomentFactor (k + 1) = gaussianMomentFactor k * ((k : ℝ) + 1 / 2) := by
  rw [gaussianMomentFactor, gaussianMomentFactor, Finset.prod_range_succ]
  congr 1
  ring

/-- **The half-integer Gamma values are the Gaussian moment factors.** -/
theorem gamma_add_half (k : ℕ) :
    Real.Gamma ((k : ℝ) + 1 / 2) = Real.sqrt Real.pi * gaussianMomentFactor k := by
  induction k with
  | zero =>
      rw [gaussianMomentFactor]
      simp only [Finset.range_zero, Finset.prod_empty, mul_one, Nat.cast_zero, zero_add]
      exact Real.Gamma_one_half_eq
  | succ k ih =>
      have hne : ((k : ℝ) + 1 / 2) ≠ 0 := by positivity
      have hstep : Real.Gamma (((k : ℕ) : ℝ) + 1 / 2 + 1) = ((k : ℝ) + 1 / 2)
          * Real.Gamma ((k : ℝ) + 1 / 2) := Real.Gamma_add_one hne
      have hcast : (((k + 1 : ℕ) : ℝ) + 1 / 2) = ((k : ℝ) + 1 / 2 + 1) := by push_cast; ring
      rw [hcast, hstep, ih, gaussianMomentFactor_succ]
      ring

end GammaValues

section PascalIdentity

theorem binomCoeff_eq_cbinomCoeff (α : ℝ) (k : ℕ) :
    binomCoeff α k = cbinomCoeff α k / 2 ^ k := by
  rw [binomCoeff, cbinomCoeff]
  have hfac : ((Nat.factorial k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have h2 : ((2 : ℝ)) ^ k ≠ 0 := by positivity
  field_simp

/-- The Pascal relation for the two half exponents. -/
theorem cbinomCoeff_half_succ (k : ℕ) :
    cbinomCoeff ((1 : ℝ) / 2) (k + 1)
      = cbinomCoeff ((-1 : ℝ) / 2) (k + 1) + cbinomCoeff ((-1 : ℝ) / 2) k := by
  have hfacS : ((Nat.factorial (k + 1) : ℕ) : ℝ) = ((k : ℝ) + 1) * (Nat.factorial k : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hfack : ((Nat.factorial k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hleft : (∏ j ∈ Finset.range (k + 1), ((1 : ℝ) / 2 - (j : ℝ)))
      = (1 / 2) * ∏ i ∈ Finset.range k, ((-1 : ℝ) / 2 - (i : ℝ)) := by
    rw [Finset.prod_range_succ']
    have : (∏ i ∈ Finset.range k, ((1 : ℝ) / 2 - ((i : ℝ) + 1)))
        = ∏ i ∈ Finset.range k, ((-1 : ℝ) / 2 - (i : ℝ)) := by
      refine Finset.prod_congr rfl fun i _ => by ring
    rw [show ((1 : ℝ) / 2 - ((0 : ℕ) : ℝ)) = 1 / 2 by norm_num]
    rw [show (∏ i ∈ Finset.range k, ((1 : ℝ) / 2 - ((i : ℕ) + 1 : ℕ)))
        = ∏ i ∈ Finset.range k, ((-1 : ℝ) / 2 - (i : ℝ)) from
      Finset.prod_congr rfl fun i _ => by push_cast; ring]
    ring
  have hright : (∏ j ∈ Finset.range (k + 1), ((-1 : ℝ) / 2 - (j : ℝ)))
      = (∏ j ∈ Finset.range k, ((-1 : ℝ) / 2 - (j : ℝ))) * ((-1 : ℝ) / 2 - (k : ℝ)) :=
    Finset.prod_range_succ _ _
  rw [cbinomCoeff, cbinomCoeff, cbinomCoeff, hleft, hright, hfacS]
  field_simp
  ring

/-- **The ray numerators are the Schläfli coefficients.** -/
theorem two_cbinom_sub_eq_schlafli (k : ℕ) :
    2 * cbinomCoeff ((1 : ℝ) / 2) k - cbinomCoeff ((-1 : ℝ) / 2) k
      = Real.sqrt 2 * 2 ^ k * schlafliCoeff k := by
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs2ne : Real.sqrt 2 ≠ 0 := ne_of_gt hs2
  cases k with
  | zero =>
      rw [schlafliCoeff]
      simp only [cbinomCoeff, binomCoeff, Finset.range_zero, Finset.prod_empty,
        Nat.factorial_zero, Nat.cast_one, pow_zero, div_one, mul_one]
      norm_num
  | succ k =>
      rw [schlafliCoeff, cbinomCoeff_half_succ k]
      have hne : ¬ (k + 1 = 0) := by omega
      rw [if_neg hne]
      have hsub : (k + 1) - 1 = k := by omega
      rw [hsub, binomCoeff_eq_cbinomCoeff, binomCoeff_eq_cbinomCoeff]
      field_simp
      ring

end PascalIdentity

section Identification

/-- **The ray coefficients are the Poincaré coefficients, rescaled.** -/
theorem rayCoeff_eq (k : ℕ) :
    rayCoeff k = Real.sqrt 2 * 2 ^ k * Real.sqrt Real.pi * besselK1Coeff k := by
  rw [rayCoeff, gamma_add_half, besselK1Coeff, two_cbinom_sub_eq_schlafli]
  ring

end Identification

end

end GaloisForLFunctions.HTGeometry
