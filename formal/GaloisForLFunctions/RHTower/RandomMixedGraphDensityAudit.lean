import GaloisForLFunctions.HTGeometry.RandomMixedGraphCore
import GaloisForLFunctions.RHTower.LegStripContinuum
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
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

structure WignerSurmiseParameters where
  beta : ℝ
  decay : ℝ
  beta_gt_neg_one : -1 < beta
  decay_pos : 0 < decay

def wignerSurmiseNormalization (θ : WignerSurmiseParameters) : ℝ :=
  2 * θ.decay ^ ((1 + θ.beta) / 2) / Real.Gamma ((1 + θ.beta) / 2)

def wignerSurmiseDensity (θ : WignerSurmiseParameters) (s : ℝ) : ℝ :=
  wignerSurmiseNormalization θ *
    (s ^ θ.beta * Real.exp (-θ.decay * s ^ (2 : ℝ)))

theorem wignerSurmiseDensity_integral (θ : WignerSurmiseParameters) :
    ∫ s in Ioi (0 : ℝ), wignerSurmiseDensity θ s = 1 := by
  rw [show (∫ s in Ioi (0 : ℝ), wignerSurmiseDensity θ s) =
      wignerSurmiseNormalization θ *
        ∫ s in Ioi (0 : ℝ), s ^ θ.beta * Real.exp (-θ.decay * s ^ (2 : ℝ)) by
          simp_rw [wignerSurmiseDensity, MeasureTheory.integral_const_mul]]
  rw [integral_rpow_mul_exp_neg_mul_rpow
    (p := 2) (q := θ.beta) (b := θ.decay)
    (by norm_num) θ.beta_gt_neg_one θ.decay_pos]
  unfold wignerSurmiseNormalization
  have ha : 0 < (1 + θ.beta) / 2 := by linarith [θ.beta_gt_neg_one]
  have hgamma : Real.Gamma ((1 + θ.beta) / 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos ha).ne'
  have hpow : θ.decay ^ ((1 + θ.beta) / 2) ≠ 0 :=
    (Real.rpow_pos_of_pos θ.decay_pos _).ne'
  rw [show (-(θ.beta + 1) / 2) = -((1 + θ.beta) / 2) by ring,
    Real.rpow_neg θ.decay_pos.le]
  rw [show (θ.beta + 1) / 2 = (1 + θ.beta) / 2 by ring]
  field_simp [hgamma, hpow]

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

/-- Printed factor `2` is correctly normalized only on folded-ratio support `[0,1]`. -/
theorem printedPoissonRatioDensity_integral_unitInterval :
    ∫ r in Set.Icc (0 : ℝ) 1, printedPoissonRatioDensity r = 1 := by
  change ∫ r in Set.Icc (0 : ℝ) 1, 2 * (1 + r) ^ (-2 : ℝ) = 1
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_const_mul]
  have hshift : (∫ r in (0 : ℝ)..1, (1 + r) ^ (-2 : ℝ)) =
      ∫ r in (1 : ℝ)..2, r ^ (-2 : ℝ) := by
    rw [show (∫ r in (0 : ℝ)..1, (1 + r) ^ (-2 : ℝ)) =
        ∫ r in (0 : ℝ)..1, (r + 1) ^ (-2 : ℝ) by
          apply intervalIntegral.integral_congr
          intro r _
          change (1 + r) ^ (-2 : ℝ) = (r + 1) ^ (-2 : ℝ)
          rw [add_comm],
      intervalIntegral.integral_comp_add_right (fun r : ℝ => r ^ (-2 : ℝ)) 1]
    norm_num
  rw [hshift, integral_rpow (Or.inr ⟨by norm_num, by norm_num⟩)]
  norm_num [Real.rpow_neg, Real.rpow_one]

/-- Second-order semi-Poisson ratio law printed in the paper. -/
def semiPoissonSecondOrderRatioDensity (r : ℝ) : ℝ :=
  6 * (r * (1 + r) ^ (-4 : ℝ))

theorem semiPoissonSecondOrderRatioDensity_integral :
    ∫ r in Ioi (0 : ℝ), semiPoissonSecondOrderRatioDensity r = 1 := by
  have hpoint : ∀ r ∈ Ioi (0 : ℝ),
      r * (1 + r) ^ (-4 : ℝ) =
        (1 + r) ^ (-3 : ℝ) - (1 + r) ^ (-4 : ℝ) := by
    intro r hr
    have hr0 : 0 < r := hr
    have hbase : 0 < 1 + r := by linarith
    calc
      r * (1 + r) ^ (-4 : ℝ) = ((1 + r) - 1) * (1 + r) ^ (-4 : ℝ) := by ring
      _ = (1 + r) * (1 + r) ^ (-4 : ℝ) - (1 + r) ^ (-4 : ℝ) := by ring
      _ = (1 + r) ^ (1 : ℝ) * (1 + r) ^ (-4 : ℝ) -
          (1 + r) ^ (-4 : ℝ) := by rw [Real.rpow_one]
      _ = (1 + r) ^ (-3 : ℝ) - (1 + r) ^ (-4 : ℝ) := by
        rw [← Real.rpow_add hbase]
        norm_num
  rw [show (∫ r in Ioi (0 : ℝ), semiPoissonSecondOrderRatioDensity r) =
      6 * ∫ r in Ioi (0 : ℝ), r * (1 + r) ^ (-4 : ℝ) by
        simp_rw [semiPoissonSecondOrderRatioDensity, MeasureTheory.integral_const_mul]]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hpoint]
  rw [MeasureTheory.integral_sub
    (_root_.RHTower.integrableOn_one_add_rpow (r := 3) (by norm_num))
    (_root_.RHTower.integrableOn_one_add_rpow (r := 4) (by norm_num)),
    _root_.RHTower.integral_one_add_rpow (r := 3) (by norm_num),
    _root_.RHTower.integral_one_add_rpow (r := 4) (by norm_num)]
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

/-- The paper's orthogonal component law at `N = 3`, simplified away from the null endpoint. -/
def printedOrthogonalComponentDensityThree (x : ℝ) : ℝ :=
  Set.indicator (Set.Icc (0 : ℝ) 3)
    (fun x => Real.sqrt 3 / 2 * x ^ (-1 / 2 : ℝ)) x

/-- Unit-mass correction of the paper's `N = 3` orthogonal component law. -/
def correctedOrthogonalComponentDensityThree (x : ℝ) : ℝ :=
  Set.indicator (Set.Icc (0 : ℝ) 3)
    (fun x => 1 / (2 * Real.sqrt 3) * x ^ (-1 / 2 : ℝ)) x

theorem integral_Icc_zero_three_rpow_neg_half :
    ∫ x in Set.Icc (0 : ℝ) 3, x ^ (-1 / 2 : ℝ) = 2 * Real.sqrt 3 := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 3),
    integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -1 / 2))]
  norm_num [Real.rpow_one]
  rw [← Real.sqrt_eq_rpow]
  ring

theorem printedOrthogonalComponentDensityThree_integral :
    ∫ x : ℝ, printedOrthogonalComponentDensityThree x = 3 := by
  change (∫ x : ℝ, Set.indicator (Set.Icc (0 : ℝ) 3)
    (fun x => Real.sqrt 3 / 2 * x ^ (-1 / 2 : ℝ)) x) = 3
  rw [MeasureTheory.integral_indicator measurableSet_Icc,
    MeasureTheory.integral_const_mul, integral_Icc_zero_three_rpow_neg_half]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]

theorem correctedOrthogonalComponentDensityThree_integral :
    ∫ x : ℝ, correctedOrthogonalComponentDensityThree x = 1 := by
  change (∫ x : ℝ, Set.indicator (Set.Icc (0 : ℝ) 3)
    (fun x => 1 / (2 * Real.sqrt 3) * x ^ (-1 / 2 : ℝ)) x) = 1
  rw [MeasureTheory.integral_indicator measurableSet_Icc,
    MeasureTheory.integral_const_mul, integral_Icc_zero_three_rpow_neg_half]
  have hsqrt : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  field_simp [hsqrt]

theorem printedOrthogonalComponentDensityThree_not_normalized :
    (∫ x : ℝ, printedOrthogonalComponentDensityThree x) ≠ 1 := by
  rw [printedOrthogonalComponentDensityThree_integral]
  norm_num

end

end GaloisForLFunctions.RHTower.RandomMixedGraph
