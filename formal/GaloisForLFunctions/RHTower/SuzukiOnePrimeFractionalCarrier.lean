import GaloisForLFunctions.RHTower.SuzukiOnePrimeRoughPrimitiveHardyTail
import GaloisForLFunctions.RHTower.SuzukiOrbitCarrier

/-!
# The one-prime fractional polynomial carrier

The rank-one Gamma window requires the nonintegral orbit exponent `κ = 2/3`.  The earlier
polynomial shift estimate covered only natural-number exponents, so it did not construct the
carrier used by the rough-primitive Hardy argument.  This module supplies the missing operator
infrastructure: fractional weights, their exact shift cocycle, a sharp polynomial ratio bound,
rank-one square summability, and the resulting lattice-energy estimate.
-/

open Filter

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Fractional polynomial orbit weight. -/
def fractionalPolynomialOrbitWeight {d : ℕ} (κ : ℝ) (ν : Fin d → ℤ) : ℝ :=
  ((1 + (orbitLength ν : ℝ)) ^ κ)⁻¹

theorem fractionalPolynomialOrbitWeight_pos {d : ℕ} (κ : ℝ) (ν : Fin d → ℤ) :
    0 < fractionalPolynomialOrbitWeight κ ν := by
  unfold fractionalPolynomialOrbitWeight
  positivity

/-- Ratio across a valuation shift. -/
def fractionalPolynomialOrbitShiftRatio {d : ℕ}
    (κ : ℝ) (s ν : Fin d → ℤ) : ℝ :=
  fractionalPolynomialOrbitWeight κ ν /
    fractionalPolynomialOrbitWeight κ (ν + s)

/-- The fractional shift ratios form the exact multiplicative cocycle of the valuation action. -/
theorem fractionalPolynomialOrbitShiftRatio_cocycle {d : ℕ}
    (κ : ℝ) (s t ν : Fin d → ℤ) :
    fractionalPolynomialOrbitShiftRatio κ s ν *
        fractionalPolynomialOrbitShiftRatio κ t (ν + s) =
      fractionalPolynomialOrbitShiftRatio κ (s + t) ν := by
  unfold fractionalPolynomialOrbitShiftRatio
  rw [add_assoc]
  have hmid : fractionalPolynomialOrbitWeight κ (ν + s) ≠ 0 :=
    (fractionalPolynomialOrbitWeight_pos κ (ν + s)).ne'
  field_simp [hmid]

/-- Fractional weighted valuation shift on a scalar lattice field. -/
def fractionalPolynomialOrbitShift {d : ℕ}
    (κ : ℝ) (s : Fin d → ℤ) (Z : (Fin d → ℤ) → ℝ) (ν : Fin d → ℤ) : ℝ :=
  fractionalPolynomialOrbitShiftRatio κ s ν * Z (ν + s)

/-- Exact group law: polynomial norm growth comes from changing metric, not from a defect in the
valuation action. -/
theorem fractionalPolynomialOrbitShift_add {d : ℕ}
    (κ : ℝ) (s t : Fin d → ℤ) (Z : (Fin d → ℤ) → ℝ) :
    fractionalPolynomialOrbitShift κ s
        (fractionalPolynomialOrbitShift κ t Z) =
      fractionalPolynomialOrbitShift κ (s + t) Z := by
  funext ν
  unfold fractionalPolynomialOrbitShift
  rw [← mul_assoc, fractionalPolynomialOrbitShiftRatio_cocycle, add_assoc]

/-- Fractional polynomial weights have the same submultiplicative shift bound as integer ones. -/
theorem abs_fractionalPolynomialOrbitShiftRatio_le {d : ℕ} {κ : ℝ} (hκ : 0 ≤ κ)
    (s ν : Fin d → ℤ) :
    |fractionalPolynomialOrbitShiftRatio κ s ν| ≤
      (1 + (orbitLength s : ℝ)) ^ κ := by
  have hsub : orbitLength (ν + s) ≤ orbitLength ν + orbitLength s :=
    orbitLength_add_le ν s
  have hsubR : (orbitLength (ν + s) : ℝ) ≤
      (orbitLength ν : ℝ) + (orbitLength s : ℝ) := by
    exact_mod_cast hsub
  have hprod : 1 + (orbitLength (ν + s) : ℝ) ≤
      (1 + (orbitLength ν : ℝ)) * (1 + (orbitLength s : ℝ)) := by
    have hν : (0 : ℝ) ≤ orbitLength ν := by positivity
    have hs : (0 : ℝ) ≤ orbitLength s := by positivity
    nlinarith
  have hrpow : (1 + (orbitLength (ν + s) : ℝ)) ^ κ ≤
      (1 + (orbitLength ν : ℝ)) ^ κ *
        (1 + (orbitLength s : ℝ)) ^ κ := by
    calc
      (1 + (orbitLength (ν + s) : ℝ)) ^ κ ≤
          ((1 + (orbitLength ν : ℝ)) *
            (1 + (orbitLength s : ℝ))) ^ κ :=
        Real.rpow_le_rpow (by positivity) hprod hκ
      _ = (1 + (orbitLength ν : ℝ)) ^ κ *
          (1 + (orbitLength s : ℝ)) ^ κ :=
        Real.mul_rpow (by positivity) (by positivity)
  have hνpow : 0 < (1 + (orbitLength ν : ℝ)) ^ κ := by positivity
  rw [fractionalPolynomialOrbitShiftRatio,
    abs_of_pos (div_pos (fractionalPolynomialOrbitWeight_pos κ ν)
      (fractionalPolynomialOrbitWeight_pos κ (ν + s))),
    fractionalPolynomialOrbitWeight, fractionalPolynomialOrbitWeight]
  calc
    ((1 + (orbitLength ν : ℝ)) ^ κ)⁻¹ /
        ((1 + (orbitLength (ν + s) : ℝ)) ^ κ)⁻¹ =
        (1 + (orbitLength (ν + s) : ℝ)) ^ κ /
          (1 + (orbitLength ν : ℝ)) ^ κ := by field_simp
    _ ≤ ((1 + (orbitLength ν : ℝ)) ^ κ *
          (1 + (orbitLength s : ℝ)) ^ κ) /
          (1 + (orbitLength ν : ℝ)) ^ κ :=
      div_le_div_of_nonneg_right hrpow hνpow.le
    _ = (1 + (orbitLength s : ℝ)) ^ κ := by field_simp

/-- The surviving rank-one `2/3` weight is square summable. -/
theorem summable_fractionalPolynomialOrbitWeight_twoThirds_sq :
    Summable fun n : ℤ =>
      fractionalPolynomialOrbitWeight (d := 1) (2 / 3) (fun _ => n) ^ 2 := by
  have hbase :=
    GaloisForLFunctions.RHTower.summable_suzukiOnePrimePolynomialWeightSq
  refine hbase.congr fun n => ?_
  rw [fractionalPolynomialOrbitWeight]
  have hlen : orbitLength (fun _ : Fin 1 => n) = n.natAbs := by
    simp [orbitLength]
  rw [hlen]
  have hpos : (0 : ℝ) < 1 + (n.natAbs : ℝ) := by positivity
  rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
  norm_num

/-- Every one-prime valuation shift is bounded on the `2/3` weighted carrier, with norm growth
`(1+|s|)^(2/3)`. -/
theorem tsum_sq_fractionalPolynomialOrbitWeightedShift_le
    (s : Fin 1 → ℤ) {Z : (Fin 1 → ℤ) → ℝ}
    (hZ : Summable fun ν => Z ν ^ 2) :
    (∑' ν : Fin 1 → ℤ,
      (fractionalPolynomialOrbitShiftRatio (2 / 3) s ν * Z (ν + s)) ^ 2) ≤
      ((1 + (orbitLength s : ℝ)) ^ (2 / 3 : ℝ)) ^ 2 *
        ∑' ν : Fin 1 → ℤ, Z ν ^ 2 := by
  apply tsum_sq_weightedShift_le
    (fun ν => abs_fractionalPolynomialOrbitShiftRatio_le (by norm_num) s ν) s hZ

end

end RHTower
