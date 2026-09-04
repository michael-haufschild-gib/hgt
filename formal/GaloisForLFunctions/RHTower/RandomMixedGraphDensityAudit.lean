import GaloisForLFunctions.HTGeometry.RandomMixedGraphCore
import GaloisForLFunctions.RHTower.LegStripContinuum
import Mathlib.MeasureTheory.Integral.Gamma

open MeasureTheory Set Real
open scoped ENNReal NNReal

namespace GaloisForLFunctions.RHTower.RandomMixedGraph

noncomputable section

def poissonNearestNeighborDensity (s : ℝ) : ℝ := Real.exp (-s)

def semiPoissonNearestNeighborDensity (s : ℝ) : ℝ :=
  4 * (s ^ (1 : ℝ) * Real.exp (-(2 * s)))

def goeNearestNeighborDensity (s : ℝ) : ℝ :=
  (Real.pi / 2) * (s ^ (1 : ℝ) * Real.exp (-(Real.pi / 4 * s ^ (2 : ℝ))))

def gueNearestNeighborDensity (s : ℝ) : ℝ :=
  (32 / Real.pi ^ 2) * (s ^ (2 : ℝ) * Real.exp (-(4 / Real.pi * s ^ (2 : ℝ))))

theorem poissonNearestNeighborDensity_integral :
    ∫ s in Ioi (0 : ℝ), poissonNearestNeighborDensity s = 1 := by
  simpa [poissonNearestNeighborDensity] using integral_exp_neg_Ioi_zero

theorem semiPoissonNearestNeighborDensity_integral :
    ∫ s in Ioi (0 : ℝ), semiPoissonNearestNeighborDensity s = 1 := by
  rw [show (∫ s in Ioi (0 : ℝ), semiPoissonNearestNeighborDensity s) =
      4 * ∫ s in Ioi (0 : ℝ), s ^ (1 : ℝ) * Real.exp (-(2 * s)) by
        simp_rw [semiPoissonNearestNeighborDensity, MeasureTheory.integral_const_mul]]
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := 2) (r := 2) (by norm_num) (by norm_num)
  norm_num [Real.Gamma_two] at h
  convert congrArg (fun x : ℝ => 4 * x) h using 1 <;> norm_num

theorem goeNearestNeighborDensity_integral :
    ∫ s in Ioi (0 : ℝ), goeNearestNeighborDensity s = 1 := by
  rw [show (∫ s in Ioi (0 : ℝ), goeNearestNeighborDensity s) =
      (Real.pi / 2) * ∫ s in Ioi (0 : ℝ),
        s ^ (1 : ℝ) * Real.exp (-(Real.pi / 4 * s ^ (2 : ℝ))) by
          simp_rw [goeNearestNeighborDensity, MeasureTheory.integral_const_mul]]
  have h := integral_rpow_mul_exp_neg_mul_rpow
    (p := 2) (q := 1) (b := Real.pi / 4)
    (by norm_num) (by norm_num) (div_pos Real.pi_pos (by norm_num))
  have hintegral :
      (∫ s in Ioi (0 : ℝ),
        s ^ (1 : ℝ) * Real.exp (-(Real.pi / 4 * s ^ (2 : ℝ)))) = 2 / Real.pi := by
    rw [show (∫ s in Ioi (0 : ℝ),
        s ^ (1 : ℝ) * Real.exp (-(Real.pi / 4 * s ^ (2 : ℝ)))) =
        ∫ s in Ioi (0 : ℝ),
          s ^ (1 : ℝ) * Real.exp (-(Real.pi / 4) * s ^ (2 : ℝ)) by
            apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
            intro s _
            ring_nf]
    rw [h]
    norm_num [Real.Gamma_one, Real.rpow_neg_one]
    field_simp [Real.pi_ne_zero]
    ring
  rw [hintegral]
  field_simp [Real.pi_ne_zero]

theorem gamma_three_halves : Real.Gamma (3 / 2) = Real.sqrt Real.pi / 2 := by
  rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by ring,
    Real.Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0), Real.Gamma_one_half_eq]
  ring

theorem four_div_pi_rpow_neg_three_halves :
    (4 / Real.pi) ^ (-(3 / 2 : ℝ)) = Real.pi * Real.sqrt Real.pi / 8 := by
  rw [Real.rpow_neg_eq_inv_rpow]
  have hinv : (4 / Real.pi : ℝ)⁻¹ = Real.pi / 4 := by
    field_simp [Real.pi_ne_zero]
  rw [hinv, show (3 / 2 : ℝ) = 1 + 1 / 2 by ring,
    Real.rpow_add (div_pos Real.pi_pos (by norm_num)), Real.rpow_one,
    ← Real.sqrt_eq_rpow, Real.sqrt_div Real.pi_nonneg]
  have hsqrtFour : Real.sqrt 4 = 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 4), Real.sqrt_nonneg 4]
  rw [hsqrtFour]
  ring

theorem gueNearestNeighborDensity_integral :
    ∫ s in Ioi (0 : ℝ), gueNearestNeighborDensity s = 1 := by
  rw [show (∫ s in Ioi (0 : ℝ), gueNearestNeighborDensity s) =
      (32 / Real.pi ^ 2) * ∫ s in Ioi (0 : ℝ),
        s ^ (2 : ℝ) * Real.exp (-(4 / Real.pi * s ^ (2 : ℝ))) by
          simp_rw [gueNearestNeighborDensity, MeasureTheory.integral_const_mul]]
  have h := integral_rpow_mul_exp_neg_mul_rpow
    (p := 2) (q := 2) (b := 4 / Real.pi)
    (by norm_num) (by norm_num) (div_pos (by norm_num) Real.pi_pos)
  have hintegral :
      (∫ s in Ioi (0 : ℝ),
        s ^ (2 : ℝ) * Real.exp (-(4 / Real.pi * s ^ (2 : ℝ)))) =
          Real.pi ^ 2 / 32 := by
    rw [show (∫ s in Ioi (0 : ℝ),
        s ^ (2 : ℝ) * Real.exp (-(4 / Real.pi * s ^ (2 : ℝ)))) =
        ∫ s in Ioi (0 : ℝ),
          s ^ (2 : ℝ) * Real.exp (-(4 / Real.pi) * s ^ (2 : ℝ)) by
            apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
            intro s _
            ring_nf]
    rw [h]
    norm_num only
    rw [four_div_pi_rpow_neg_three_halves, gamma_three_halves]
    have hsqrtPi := Real.sq_sqrt Real.pi_nonneg
    nlinarith
  rw [hintegral]
  field_simp [Real.pi_ne_zero]

def correctedPoissonRatioDensity (r : ℝ) : ℝ := (1 + r) ^ (-2 : ℝ)

def printedPoissonRatioDensity (r : ℝ) : ℝ := 2 * correctedPoissonRatioDensity r

theorem correctedPoissonRatioDensity_integral :
    ∫ r in Ioi (0 : ℝ), correctedPoissonRatioDensity r = 1 := by
  have h := _root_.RHTower.integral_one_add_rpow (r := 2) (by norm_num)
  norm_num at h
  simpa [correctedPoissonRatioDensity] using h

theorem printedPoissonRatioDensity_integral :
    ∫ r in Ioi (0 : ℝ), printedPoissonRatioDensity r = 2 := by
  rw [show (∫ r in Ioi (0 : ℝ), printedPoissonRatioDensity r) =
      2 * ∫ r in Ioi (0 : ℝ), correctedPoissonRatioDensity r by
        simp_rw [printedPoissonRatioDensity, MeasureTheory.integral_const_mul]]
  rw [correctedPoissonRatioDensity_integral]
  norm_num

theorem printedPoissonRatioDensity_not_normalized :
    (∫ r in Ioi (0 : ℝ), printedPoissonRatioDensity r) ≠ 1 := by
  rw [printedPoissonRatioDensity_integral]
  norm_num

def correctedUnitaryComponentDensityTwo (x : ℝ) : ℝ :=
  Set.indicator (Set.Icc (0 : ℝ) 2) (fun _ => (1 / 2 : ℝ)) x

def printedUnitaryComponentDensityTwo (x : ℝ) : ℝ :=
  Set.indicator (Set.Icc (0 : ℝ) 2) (fun _ => Real.sqrt 2) x

theorem correctedUnitaryComponentDensityTwo_integral :
    ∫ x : ℝ, correctedUnitaryComponentDensityTwo x = 1 := by
  change (∫ x : ℝ, Set.indicator (Set.Icc (0 : ℝ) 2) (fun _ => (1 / 2 : ℝ)) x) = 1
  rw [MeasureTheory.integral_indicator measurableSet_Icc,
    MeasureTheory.setIntegral_const]
  norm_num [Real.volume_Icc]

theorem printedUnitaryComponentDensityTwo_integral :
    ∫ x : ℝ, printedUnitaryComponentDensityTwo x = 2 * Real.sqrt 2 := by
  change (∫ x : ℝ, Set.indicator (Set.Icc (0 : ℝ) 2) (fun _ => Real.sqrt 2) x) =
    2 * Real.sqrt 2
  rw [MeasureTheory.integral_indicator measurableSet_Icc,
    MeasureTheory.setIntegral_const]
  norm_num [Real.volume_Icc]

theorem printedUnitaryComponentDensityTwo_not_normalized :
    (∫ x : ℝ, printedUnitaryComponentDensityTwo x) ≠ 1 := by
  rw [printedUnitaryComponentDensityTwo_integral]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]

end

end GaloisForLFunctions.RHTower.RandomMixedGraph

