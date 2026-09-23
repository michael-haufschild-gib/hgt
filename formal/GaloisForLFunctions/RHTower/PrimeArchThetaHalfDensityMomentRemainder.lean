import GaloisForLFunctions.RHTower.PrimeArchThetaWardLaplaceHalfDensity
import GaloisForLFunctions.RHTower.PrimeArchThetaSourceAtomDomination

/-!
# Half-density clock budget for the first theta atom through fourth order

The exact symmetric half-density observation

`2 ∫ cosh (x / 2) source₁(x) dx = (4π - 1) exp (-π)`

is a static clock-reading constraint, not an evolution law.  Keeping the first three positive
terms of the `cosh` observation bounds the first atom's zeroth, second, and fourth raw moments.
The fourth-moment remainder then supplies a source-specific sufficient condition for the relaxed
fourth-moment concentration used by the linear prime--Gamma Hankel criterion.

No numerical enclosure or zero-location assumption enters the argument.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

/-- The exact half-density observation controls the first three even raw moments of the first
theta atom. -/
theorem thetaCuspFirstAtomMomentTriple_le_halfDensityBudget :
    thetaCuspAtomRawEvenMoment 0 1 +
        thetaCuspAtomRawEvenMoment 1 1 / 8 +
          thetaCuspAtomRawEvenMoment 2 1 / 384 ≤
      (4 * Real.pi - 1) * Real.exp (-Real.pi) := by
  have h0 : IntegrableOn (fun x : ℝ => thetaCuspSourceTerm x 1) (Ioi 0) := by
    simpa using integrableOn_pow_mul_thetaCuspSourceTerm 0 1
  have h1 : IntegrableOn (fun x : ℝ =>
      x ^ (2 : ℕ) * thetaCuspSourceTerm x 1) (Ioi 0) := by
    simpa using integrableOn_pow_mul_thetaCuspSourceTerm 1 1
  have h2 : IntegrableOn (fun x : ℝ =>
      x ^ (4 : ℕ) * thetaCuspSourceTerm x 1) (Ioi 0) := by
    simpa using integrableOn_pow_mul_thetaCuspSourceTerm 2 1
  have hpoly : IntegrableOn (fun x : ℝ =>
      (1 + x ^ (2 : ℕ) / 8 + x ^ (4 : ℕ) / 384) * thetaCuspSourceTerm x 1) (Ioi 0) := by
    have h := (h0.add (h1.const_mul (1 / 8 : ℝ))).add
      (h2.const_mul (1 / 384 : ℝ))
    apply h.congr
    filter_upwards [] with x
    simp only [Pi.add_apply]
    ring
  have hcosh := integrableOn_cosh_half_mul_thetaCuspSourceTerm
    (n := 1) (by norm_num)
  have hmono : (∫ x : ℝ in Ioi 0,
      (1 + x ^ (2 : ℕ) / 8 + x ^ (4 : ℕ) / 384) * thetaCuspSourceTerm x 1) ≤
      ∫ x : ℝ in Ioi 0,
        Real.cosh (x / 2) * thetaCuspSourceTerm x 1 := by
    apply integral_mono_ae hpoly hcosh
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_le_mul_of_nonneg_right
      (HTGeometry.one_add_sq_div_eight_add_fourth_div_384_le_cosh_half x)
      (thetaCuspSourceTerm_nonneg_of_pos hx 1)
  have hpoly_eq :
      (∫ x : ℝ in Ioi 0,
          (1 + x ^ (2 : ℕ) / 8 + x ^ (4 : ℕ) / 384) * thetaCuspSourceTerm x 1) =
        (∫ x : ℝ in Ioi 0, thetaCuspSourceTerm x 1) +
          (1 / 8 : ℝ) * (∫ x : ℝ in Ioi 0,
            x ^ (2 : ℕ) * thetaCuspSourceTerm x 1) +
          (1 / 384 : ℝ) * (∫ x : ℝ in Ioi 0,
            x ^ (4 : ℕ) * thetaCuspSourceTerm x 1) := by
    calc
      _ = ∫ x : ℝ in Ioi 0,
          ((thetaCuspSourceTerm x 1 +
              (1 / 8 : ℝ) * (x ^ (2 : ℕ) * thetaCuspSourceTerm x 1)) +
            (1 / 384 : ℝ) * (x ^ (4 : ℕ) * thetaCuspSourceTerm x 1)) := by
              apply integral_congr_ae
              filter_upwards [] with x
              ring
      _ = (∫ x : ℝ in Ioi 0,
            thetaCuspSourceTerm x 1 +
              (1 / 8 : ℝ) * (x ^ (2 : ℕ) * thetaCuspSourceTerm x 1)) +
          ∫ x : ℝ in Ioi 0,
            (1 / 384 : ℝ) * (x ^ (4 : ℕ) * thetaCuspSourceTerm x 1) := by
              apply integral_add
              · exact h0.add (h1.const_mul (1 / 8 : ℝ))
              · exact h2.const_mul (1 / 384 : ℝ)
      _ = _ := by
        rw [integral_add h0 (h1.const_mul (1 / 8 : ℝ)),
          integral_const_mul, integral_const_mul]
  have hbudget : 2 * (∫ x : ℝ in Ioi 0,
      Real.cosh (x / 2) * thetaCuspSourceTerm x 1) =
      (4 * Real.pi - 1) * Real.exp (-Real.pi) := by
    simpa using two_mul_integral_cosh_half_mul_thetaCuspSourceTerm_eq_budget
      (n := 1) (by norm_num)
  rw [hpoly_eq] at hmono
  rw [thetaCuspAtomRawEvenMoment, thetaCuspAtomRawEvenMoment,
    thetaCuspAtomRawEvenMoment]
  norm_num only [Nat.mul_zero, Nat.mul_one, Nat.reduceMul, pow_zero, one_mul]
  nlinarith

/-- The fourth raw moment is bounded by the unused remainder of the exact half-density clock
budget after subtracting its zeroth- and second-moment observations. -/
theorem thetaCuspFirstAtomRawEvenMoment_two_le_halfDensityRemainder :
    thetaCuspAtomRawEvenMoment 2 1 ≤
      384 * ((4 * Real.pi - 1) * Real.exp (-Real.pi) -
        thetaCuspAtomRawEvenMoment 0 1 -
          thetaCuspAtomRawEvenMoment 1 1 / 8) := by
  have h := thetaCuspFirstAtomMomentTriple_le_halfDensityBudget
  linarith

/-- A lower-order endpoint-remainder condition discharges the full-source relaxed fourth-moment
concentration condition.  It contains only the first atom's zeroth and second raw moments plus
the exact half-density endpoint value; the unknown fourth moment has been eliminated. -/
theorem thetaCuspRelaxedFourthMomentConcentration_of_firstAtomHalfDensityRemainder
    (hrem :
      6144 * (3005 / 2997 : ℝ) ^ (2 : ℕ) * thetaCuspAtomRawEvenMoment 0 1 *
          ((4 * Real.pi - 1) * Real.exp (-Real.pi) -
            thetaCuspAtomRawEvenMoment 0 1 -
              thetaCuspAtomRawEvenMoment 1 1 / 8) ≤
        45 * thetaCuspAtomRawEvenMoment 1 1 ^ (2 : ℕ)) :
    ThetaCuspRelaxedFourthMomentConcentration := by
  have hM2 := thetaCuspFirstAtomRawEvenMoment_two_le_halfDensityRemainder
  have hfactor : 0 ≤
      16 * (3005 / 2997 : ℝ) ^ (2 : ℕ) * thetaCuspAtomRawEvenMoment 0 1 := by
    exact mul_nonneg (by positivity) (thetaCuspAtomRawEvenMoment_nonneg 0 1)
  have hscaled := mul_le_mul_of_nonneg_left hM2 hfactor
  apply thetaCuspRelaxedFourthMomentConcentration_of_first_atom
  calc
    16 * ((3005 / 2997 : ℝ) * thetaCuspAtomRawEvenMoment 0 1) *
          ((3005 / 2997 : ℝ) * thetaCuspAtomRawEvenMoment 2 1) =
        (16 * (3005 / 2997 : ℝ) ^ (2 : ℕ) *
          thetaCuspAtomRawEvenMoment 0 1) *
            thetaCuspAtomRawEvenMoment 2 1 := by ring
    _ ≤ (16 * (3005 / 2997 : ℝ) ^ (2 : ℕ) *
          thetaCuspAtomRawEvenMoment 0 1) *
        (384 * ((4 * Real.pi - 1) * Real.exp (-Real.pi) -
          thetaCuspAtomRawEvenMoment 0 1 -
            thetaCuspAtomRawEvenMoment 1 1 / 8)) := hscaled
    _ = 6144 * (3005 / 2997 : ℝ) ^ (2 : ℕ) *
          thetaCuspAtomRawEvenMoment 0 1 *
          ((4 * Real.pi - 1) * Real.exp (-Real.pi) -
            thetaCuspAtomRawEvenMoment 0 1 -
              thetaCuspAtomRawEvenMoment 1 1 / 8) := by ring
    _ ≤ 45 * thetaCuspAtomRawEvenMoment 1 1 ^ (2 : ℕ) := hrem

/-- Direct prime-source consumer: the old relaxed fourth-moment hypothesis is replaced by the
exact half-density remainder condition. -/
theorem forall_primeArchSourceTraceHankel_linear_nonneg_of_firstAtomHalfDensityRemainder
    (hupper :
      14 * ((3005 / 2997 : ℝ) * thetaCuspAtomRawEvenMoment 2 1) ^ (2 : ℕ) ≤
        9 * thetaCuspAtomRawEvenMoment 1 1 *
          thetaCuspAtomRawEvenMoment 3 1)
    (hrem :
      6144 * (3005 / 2997 : ℝ) ^ (2 : ℕ) * thetaCuspAtomRawEvenMoment 0 1 *
          ((4 * Real.pi - 1) * Real.exp (-Real.pi) -
            thetaCuspAtomRawEvenMoment 0 1 -
              thetaCuspAtomRawEvenMoment 1 1 / 8) ≤
        45 * thetaCuspAtomRawEvenMoment 1 1 ^ (2 : ℕ)) :
    ∀ a b : ℝ, 0 ≤ (primeArchSourceTraceHankel (C a + C b * X)).re :=
  forall_primeArchSourceTraceHankel_linear_nonneg_of_ratioSplit
    (thetaCuspUpperAdjacentRatioSeparation_of_first_atom hupper)
    (thetaCuspRelaxedFourthMomentConcentration_of_firstAtomHalfDensityRemainder hrem)

end

end RHTower
