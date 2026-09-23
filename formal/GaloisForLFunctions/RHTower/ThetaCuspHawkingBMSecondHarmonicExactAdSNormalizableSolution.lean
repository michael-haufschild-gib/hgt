import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSecondHarmonicExactAdSForbiddenSolution

/-!
# Exact BM second-harmonic AdS normalizable solution

The complementary Frobenius branch of the outer `w=1-z` Gauss equation has exponent `1/2` and
transformed parameters `c-b`, `c-a`, `c-a-b+1=3/2`. This module constructs that square-root branch,
proves its first two actual radial derivatives, and verifies the original BM equation on `0<z<1`.
-/

open Complex Real Set Filter Topology Nat FormalMultilinearSeries Polynomial

namespace RHTower

noncomputable section

attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

def d4BMPlusPlusAdSNormalizableHypergeometricA
    (n : ℕ) (chi : ℂ) : ℂ :=
  d4BMCausalRadialC (d4BMCausalPlusPlusFrequency n chi) -
    d4BMCausalHypergeometricB (d4BMCausalPlusPlusFrequency n chi) chi

def d4BMPlusPlusAdSNormalizableHypergeometricB
    (n : ℕ) (chi : ℂ) : ℂ :=
  d4BMCausalRadialC (d4BMCausalPlusPlusFrequency n chi) -
    d4BMCausalHypergeometricA (d4BMCausalPlusPlusFrequency n chi) chi

def d4BMPlusPlusAdSNormalizableHypergeometricC
    (n : ℕ) (chi : ℂ) : ℂ :=
  d4BMCausalRadialC (d4BMCausalPlusPlusFrequency n chi) -
    d4BMCausalHypergeometricA (d4BMCausalPlusPlusFrequency n chi) chi -
    d4BMCausalHypergeometricB (d4BMCausalPlusPlusFrequency n chi) chi + 1

theorem d4BMPlusPlusAdSNormalizableHypergeometricA_eq
    (n : ℕ) (chi : ℂ) :
    d4BMPlusPlusAdSNormalizableHypergeometricA n chi =
      d4BMCausalRadialA (d4BMCausalPlusPlusFrequency n chi) chi := by
  rw [d4BMPlusPlusAdSNormalizableHypergeometricA,
    d4BMCausalRadialC_plusPlus_eq, d4BMCausalHypergeometricB_plusPlus,
    d4BMCausalRadialA_plusPlus]
  ring

theorem d4BMPlusPlusAdSNormalizableHypergeometricB_eq
    (n : ℕ) (chi : ℂ) :
    d4BMPlusPlusAdSNormalizableHypergeometricB n chi =
      d4BMCausalRadialB (d4BMCausalPlusPlusFrequency n chi) chi := by
  rw [d4BMPlusPlusAdSNormalizableHypergeometricB,
    d4BMCausalRadialC_plusPlus_eq, d4BMCausalHypergeometricA_plusPlus,
    d4BMCausalRadialB_plusPlus]
  ring

/-- Outer normalizable factor has transformed denominator `3/2`. -/
theorem d4BMPlusPlusAdSNormalizableHypergeometricC_eq
    (n : ℕ) (chi : ℂ) :
    d4BMPlusPlusAdSNormalizableHypergeometricC n chi = 3 / 2 := by
  rw [d4BMPlusPlusAdSNormalizableHypergeometricC]
  linear_combination -(d4BMPlusPlusHypergeometric_exponentBalance n chi)

theorem d4BMPlusPlusAdSNormalizableHypergeometricParameters_ne_negNat
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) (j : ℕ) :
    (j : ℂ) ≠ -d4BMPlusPlusAdSNormalizableHypergeometricA n chi ∧
      (j : ℂ) ≠ -d4BMPlusPlusAdSNormalizableHypergeometricB n chi ∧
      (j : ℂ) ≠ -d4BMPlusPlusAdSNormalizableHypergeometricC n chi := by
  constructor
  · intro h
    have him := congrArg Complex.im h
    rw [d4BMPlusPlusAdSNormalizableHypergeometricA_eq,
      d4BMCausalRadialA_plusPlus] at him
    norm_num [Complex.mul_im] at him
    exact hchi (by linarith)
  constructor
  · intro h
    have him := congrArg Complex.im h
    rw [d4BMPlusPlusAdSNormalizableHypergeometricB_eq,
      d4BMCausalRadialB_plusPlus] at him
    norm_num [Complex.mul_im] at him
    exact hchi (by linarith)
  · rw [d4BMPlusPlusAdSNormalizableHypergeometricC_eq]
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    have hj : (0 : ℝ) ≤ (j : ℝ) := by positivity
    linarith

def d4BMPlusPlusAdSNormalizableHypergeometricSeries
    (n : ℕ) (chi : ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  ordinaryHypergeometricSeries ℂ
    (d4BMPlusPlusAdSNormalizableHypergeometricA n chi)
    (d4BMPlusPlusAdSNormalizableHypergeometricB n chi)
    (d4BMPlusPlusAdSNormalizableHypergeometricC n chi)

theorem d4BMPlusPlusAdSNormalizableHypergeometricSeries_radius_eq_one
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    (d4BMPlusPlusAdSNormalizableHypergeometricSeries n chi).radius = 1 := by
  rw [d4BMPlusPlusAdSNormalizableHypergeometricSeries]
  apply ordinaryHypergeometricSeries_radius_eq_one
  exact d4BMPlusPlusAdSNormalizableHypergeometricParameters_ne_negNat n chi hchi

def d4BMPlusPlusAdSNormalizableHypergeometricFactor
    (n : ℕ) (chi w : ℂ) : ℂ :=
  (d4BMPlusPlusAdSNormalizableHypergeometricSeries n chi).sum w

def d4BMPlusPlusAdSNormalizableHypergeometricFirstDerivative
    (n : ℕ) (chi w : ℂ) : ℂ :=
  (((d4BMPlusPlusAdSNormalizableHypergeometricSeries n chi).derivSeries.sum w) 1)

def d4BMPlusPlusAdSNormalizableHypergeometricSecondDerivative
    (n : ℕ) (chi w : ℂ) : ℂ :=
  ((((d4BMPlusPlusAdSNormalizableHypergeometricSeries n chi).derivSeries.derivSeries.sum w)
    1) 1)

@[simp]
theorem d4BMPlusPlusAdSNormalizableHypergeometricFactor_zero
    (n : ℕ) (chi : ℂ) :
    d4BMPlusPlusAdSNormalizableHypergeometricFactor n chi 0 = 1 := by
  change ordinaryHypergeometric
    (d4BMPlusPlusAdSNormalizableHypergeometricA n chi)
    (d4BMPlusPlusAdSNormalizableHypergeometricB n chi)
    (d4BMPlusPlusAdSNormalizableHypergeometricC n chi) 0 = 1
  exact ordinaryHypergeometric_zero _ _ _

theorem hasDerivAt_d4BMPlusPlusAdSNormalizableHypergeometricFactor
    (n : ℕ) (chi w : ℂ) (hchi : chi.re ≠ 0) (hw : ‖w‖ₑ < 1) :
    HasDerivAt (d4BMPlusPlusAdSNormalizableHypergeometricFactor n chi)
      (d4BMPlusPlusAdSNormalizableHypergeometricFirstDerivative n chi w) w := by
  let p := d4BMPlusPlusAdSNormalizableHypergeometricSeries n chi
  have hwp : ‖w‖ₑ < p.radius := by
    rw [d4BMPlusPlusAdSNormalizableHypergeometricSeries_radius_eq_one n chi hchi]
    exact hw
  change HasDerivAt p.sum ((p.derivSeries.sum w) 1) w
  exact (p.hasFDerivAt_sum hwp).hasDerivAt

theorem hasDerivAt_d4BMPlusPlusAdSNormalizableHypergeometricFirstDerivative
    (n : ℕ) (chi w : ℂ) (hchi : chi.re ≠ 0) (hw : ‖w‖ₑ < 1) :
    HasDerivAt (d4BMPlusPlusAdSNormalizableHypergeometricFirstDerivative n chi)
      (d4BMPlusPlusAdSNormalizableHypergeometricSecondDerivative n chi w) w := by
  let p := d4BMPlusPlusAdSNormalizableHypergeometricSeries n chi
  let q := p.derivSeries
  have hwp : ‖w‖ₑ < p.radius := by
    rw [d4BMPlusPlusAdSNormalizableHypergeometricSeries_radius_eq_one n chi hchi]
    exact hw
  have hwq : ‖w‖ₑ < q.radius := lt_of_lt_of_le hwp p.radius_le_radius_derivSeries
  have hq := q.hasFDerivAt_sum hwq
  have heval := hq.clm_apply (hasFDerivAt_const (1 : ℂ) w)
  change HasDerivAt (fun u : ℂ => (q.sum u) 1)
    (((q.derivSeries.sum w) 1) 1) w
  simpa using heval.hasDerivAt

theorem d4BMPlusPlusAdSNormalizableHypergeometric_standardGaussODE
    (n : ℕ) (chi w : ℂ) (hchi : chi.re ≠ 0) (hw : ‖w‖ₑ < 1) :
    w * (1 - w) * d4BMPlusPlusAdSNormalizableHypergeometricSecondDerivative n chi w +
        (d4BMPlusPlusAdSNormalizableHypergeometricC n chi -
          (d4BMPlusPlusAdSNormalizableHypergeometricA n chi +
            d4BMPlusPlusAdSNormalizableHypergeometricB n chi + 1) * w) *
          d4BMPlusPlusAdSNormalizableHypergeometricFirstDerivative n chi w -
      d4BMPlusPlusAdSNormalizableHypergeometricA n chi *
        d4BMPlusPlusAdSNormalizableHypergeometricB n chi *
          d4BMPlusPlusAdSNormalizableHypergeometricFactor n chi w = 0 := by
  let a := d4BMPlusPlusAdSNormalizableHypergeometricA n chi
  let b := d4BMPlusPlusAdSNormalizableHypergeometricB n chi
  let c := d4BMPlusPlusAdSNormalizableHypergeometricC n chi
  have hc : ∀ j : ℕ, (j : ℂ) ≠ -c := by
    intro j
    exact (d4BMPlusPlusAdSNormalizableHypergeometricParameters_ne_negNat
      n chi hchi j).2.2
  have hwr : ‖w‖ₑ < (ordinaryHypergeometricSeries ℂ a b c).radius := by
    change ‖w‖ₑ < (d4BMPlusPlusAdSNormalizableHypergeometricSeries n chi).radius
    rw [d4BMPlusPlusAdSNormalizableHypergeometricSeries_radius_eq_one n chi hchi]
    exact hw
  simpa [a, b, c, d4BMPlusPlusAdSNormalizableHypergeometricFactor,
    d4BMPlusPlusAdSNormalizableHypergeometricFirstDerivative,
    d4BMPlusPlusAdSNormalizableHypergeometricSecondDerivative,
    d4BMPlusPlusAdSNormalizableHypergeometricSeries,
    ordinaryHypergeometricFirstDerivativeSeriesValue,
    ordinaryHypergeometricSecondDerivativeSeriesValue] using
      ordinaryHypergeometric_standardGaussODE a b c w hc hwr

/-- Positive square-root Frobenius branch at the AdS endpoint. -/
def d4BMPlusPlusAdSLeadingNormalizableBranch (z : ℝ) : ℂ :=
  Complex.exp ((1 / 2 : ℂ) * (Real.log (1 - z) : ℂ))

def d4BMPlusPlusAdSLeadingNormalizableBranchDerivative (z : ℝ) : ℂ :=
  -(1 / 2 : ℂ) * d4BMPlusPlusAdSLeadingNormalizableBranch z / ((1 - z : ℝ) : ℂ)

def d4BMPlusPlusAdSLeadingNormalizableBranchSecondDerivative (z : ℝ) : ℂ :=
  (1 / 2 : ℂ) * ((1 / 2 : ℂ) - 1) *
    d4BMPlusPlusAdSLeadingNormalizableBranch z / ((1 - z : ℝ) : ℂ) ^ (2 : ℕ)

theorem hasDerivAt_d4BMPlusPlusAdSLeadingNormalizableBranch
    {z : ℝ} (hz1 : z < 1) :
    HasDerivAt d4BMPlusPlusAdSLeadingNormalizableBranch
      (d4BMPlusPlusAdSLeadingNormalizableBranchDerivative z) z := by
  have hw : 1 - z ≠ 0 := ne_of_gt (sub_pos.mpr hz1)
  have hinner : HasDerivAt (fun x : ℝ => 1 - x) (-1) z := by
    simpa using (hasDerivAt_id z).const_sub (1 : ℝ)
  have hlogR := (Real.hasDerivAt_log hw).comp z hinner
  have hlogC : HasDerivAt (fun x : ℝ => (Real.log (1 - x) : ℂ))
      ((-(1 - z)⁻¹ : ℝ) : ℂ) z := by
    simpa using hlogR.ofReal_comp
  have h := (hlogC.const_mul (1 / 2 : ℂ)).cexp
  rw [d4BMPlusPlusAdSLeadingNormalizableBranchDerivative]
  change HasDerivAt
    (fun x : ℝ => Complex.exp ((1 / 2 : ℂ) * (Real.log (1 - x) : ℂ)))
    (-(1 / 2 : ℂ) *
      Complex.exp ((1 / 2 : ℂ) * (Real.log (1 - z) : ℂ)) /
        ((1 - z : ℝ) : ℂ)) z
  apply h.congr_deriv
  have hwC : ((1 - z : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hw
  push_cast
  field_simp [hwC]

theorem hasDerivAt_d4BMPlusPlusAdSLeadingNormalizableBranchDerivative
    {z : ℝ} (hz1 : z < 1) :
    HasDerivAt d4BMPlusPlusAdSLeadingNormalizableBranchDerivative
      (d4BMPlusPlusAdSLeadingNormalizableBranchSecondDerivative z) z := by
  let h := d4BMPlusPlusAdSLeadingNormalizableBranch
  have hw : 1 - z ≠ 0 := ne_of_gt (sub_pos.mpr hz1)
  have hwC : ((1 - z : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hw
  have hwC' : (1 - (z : ℂ)) ≠ 0 := by exact_mod_cast hw
  have hh : HasDerivAt h
      (-(1 / 2 : ℂ) * h z / ((1 - z : ℝ) : ℂ)) z := by
    simpa [h, d4BMPlusPlusAdSLeadingNormalizableBranchDerivative] using
      hasDerivAt_d4BMPlusPlusAdSLeadingNormalizableBranch hz1
  have hdenR : HasDerivAt (fun x : ℝ => 1 - x) (-1) z := by
    simpa using (hasDerivAt_id z).const_sub (1 : ℝ)
  have hden := hdenR.ofReal_comp
  have hquot := (hh.const_mul (-(1 / 2 : ℂ))).div hden hwC
  change HasDerivAt
    (fun x : ℝ => -(1 / 2 : ℂ) * h x / ((1 - x : ℝ) : ℂ))
    ((1 / 2 : ℂ) * ((1 / 2 : ℂ) - 1) * h z /
      ((1 - z : ℝ) : ℂ) ^ (2 : ℕ)) z
  apply hquot.congr_deriv
  change
    ((-(1 / 2 : ℂ) * (-(1 / 2 : ℂ) * h z / ((1 - z : ℝ) : ℂ)) *
          ((1 - z : ℝ) : ℂ) -
        (-(1 / 2 : ℂ) * h z) * ((-1 : ℝ) : ℂ)) /
        ((1 - z : ℝ) : ℂ) ^ (2 : ℕ)) =
      (1 / 2 : ℂ) * ((1 / 2 : ℂ) - 1) * h z /
        ((1 - z : ℝ) : ℂ) ^ (2 : ℕ)
  apply (div_left_inj' (pow_ne_zero 2 hwC)).2
  norm_num
  field_simp [hwC, hwC']
  ring

/-- Exact square-root normalizable AdS solution. -/
def d4BMPlusPlusAdSNormalizableSolution
    (n : ℕ) (chi : ℂ) (z : ℝ) : ℂ :=
  d4BMPlusPlusAdSLeadingNormalizableBranch z *
    d4BMPlusPlusAdSNormalizableHypergeometricFactor n chi ((1 - z : ℝ) : ℂ)

def d4BMPlusPlusAdSNormalizableSolutionDerivative
    (n : ℕ) (chi : ℂ) (z : ℝ) : ℂ :=
  d4BMPlusPlusAdSLeadingNormalizableBranchDerivative z *
      d4BMPlusPlusAdSNormalizableHypergeometricFactor n chi ((1 - z : ℝ) : ℂ) -
    d4BMPlusPlusAdSLeadingNormalizableBranch z *
      d4BMPlusPlusAdSNormalizableHypergeometricFirstDerivative n chi ((1 - z : ℝ) : ℂ)

def d4BMPlusPlusAdSNormalizableSolutionSecondDerivative
    (n : ℕ) (chi : ℂ) (z : ℝ) : ℂ :=
  d4BMPlusPlusAdSLeadingNormalizableBranchSecondDerivative z *
      d4BMPlusPlusAdSNormalizableHypergeometricFactor n chi ((1 - z : ℝ) : ℂ) -
    2 * d4BMPlusPlusAdSLeadingNormalizableBranchDerivative z *
      d4BMPlusPlusAdSNormalizableHypergeometricFirstDerivative n chi ((1 - z : ℝ) : ℂ) +
    d4BMPlusPlusAdSLeadingNormalizableBranch z *
      d4BMPlusPlusAdSNormalizableHypergeometricSecondDerivative n chi ((1 - z : ℝ) : ℂ)

theorem hasDerivAt_d4BMPlusPlusAdSNormalizableSolution
    (n : ℕ) (chi : ℂ) {z : ℝ} (hchi : chi.re ≠ 0)
    (hz0 : 0 < z) (hz1 : z < 1) :
    HasDerivAt (d4BMPlusPlusAdSNormalizableSolution n chi)
      (d4BMPlusPlusAdSNormalizableSolutionDerivative n chi z) z := by
  have hw0 : 0 < 1 - z := sub_pos.mpr hz1
  have hw1 : 1 - z < 1 := by linarith
  have hH := hasDerivAt_d4BMPlusPlusAdSLeadingNormalizableBranch hz1
  have hF := hasDerivAt_d4BMPlusPlusAdSNormalizableHypergeometricFactor
    n chi ((1 - z : ℝ) : ℂ) hchi (enorm_ofReal_lt_one hw0 hw1)
  have hinner : HasDerivAt (fun x : ℝ => 1 - x) (-1) z := by
    simpa using (hasDerivAt_id z).const_sub (1 : ℝ)
  have hFz := hF.comp z hinner.ofReal_comp
  change HasDerivAt
    (fun x : ℝ => d4BMPlusPlusAdSLeadingNormalizableBranch x *
      d4BMPlusPlusAdSNormalizableHypergeometricFactor n chi ((1 - x : ℝ) : ℂ))
    (d4BMPlusPlusAdSLeadingNormalizableBranchDerivative z *
        d4BMPlusPlusAdSNormalizableHypergeometricFactor n chi ((1 - z : ℝ) : ℂ) -
      d4BMPlusPlusAdSLeadingNormalizableBranch z *
        d4BMPlusPlusAdSNormalizableHypergeometricFirstDerivative n chi
          ((1 - z : ℝ) : ℂ)) z
  simpa [Function.comp_def] using! hH.mul hFz

theorem hasDerivAt_d4BMPlusPlusAdSNormalizableSolutionDerivative
    (n : ℕ) (chi : ℂ) {z : ℝ} (hchi : chi.re ≠ 0)
    (hz0 : 0 < z) (hz1 : z < 1) :
    HasDerivAt (d4BMPlusPlusAdSNormalizableSolutionDerivative n chi)
      (d4BMPlusPlusAdSNormalizableSolutionSecondDerivative n chi z) z := by
  have hw0 : 0 < 1 - z := sub_pos.mpr hz1
  have hw1 : 1 - z < 1 := by linarith
  have hH := hasDerivAt_d4BMPlusPlusAdSLeadingNormalizableBranch hz1
  have hHd := hasDerivAt_d4BMPlusPlusAdSLeadingNormalizableBranchDerivative hz1
  have hF := hasDerivAt_d4BMPlusPlusAdSNormalizableHypergeometricFactor
    n chi ((1 - z : ℝ) : ℂ) hchi (enorm_ofReal_lt_one hw0 hw1)
  have hFd := hasDerivAt_d4BMPlusPlusAdSNormalizableHypergeometricFirstDerivative
    n chi ((1 - z : ℝ) : ℂ) hchi (enorm_ofReal_lt_one hw0 hw1)
  have hinner : HasDerivAt (fun x : ℝ => 1 - x) (-1) z := by
    simpa using (hasDerivAt_id z).const_sub (1 : ℝ)
  have hFz := hF.comp z hinner.ofReal_comp
  have hFdz := hFd.comp z hinner.ofReal_comp
  have h := (hHd.mul hFz).sub (hH.mul hFdz)
  have hder :
      d4BMPlusPlusAdSLeadingNormalizableBranchSecondDerivative z *
            d4BMPlusPlusAdSNormalizableHypergeometricFactor n chi ((1 - z : ℝ) : ℂ) +
          d4BMPlusPlusAdSLeadingNormalizableBranchDerivative z *
            (d4BMPlusPlusAdSNormalizableHypergeometricFirstDerivative n chi
              ((1 - z : ℝ) : ℂ) * ((-1 : ℝ) : ℂ)) -
        (d4BMPlusPlusAdSLeadingNormalizableBranchDerivative z *
            d4BMPlusPlusAdSNormalizableHypergeometricFirstDerivative n chi
              ((1 - z : ℝ) : ℂ) +
          d4BMPlusPlusAdSLeadingNormalizableBranch z *
            (d4BMPlusPlusAdSNormalizableHypergeometricSecondDerivative n chi
              ((1 - z : ℝ) : ℂ) * ((-1 : ℝ) : ℂ))) =
        d4BMPlusPlusAdSNormalizableSolutionSecondDerivative n chi z := by
    rw [d4BMPlusPlusAdSNormalizableSolutionSecondDerivative]
    norm_num
    ring
  have h' := h.congr_deriv hder
  apply h'.congr_of_eventuallyEq
  filter_upwards [] with x
  simp [d4BMPlusPlusAdSNormalizableSolutionDerivative, Function.comp_def]

/-- Exact normalizable AdS branch solves the original BM radial equation. -/
theorem d4BMPlusPlusAdSNormalizableSolution_jet_eq_zero
    (n : ℕ) (chi : ℂ) {z : ℝ} (hchi : chi.re ≠ 0)
    (hz0 : 0 < z) (hz1 : z < 1) :
    d4BMPlusPlusHypergeometricJet n chi z
      (d4BMPlusPlusAdSNormalizableSolution n chi z)
      (d4BMPlusPlusAdSNormalizableSolutionDerivative n chi z)
      (d4BMPlusPlusAdSNormalizableSolutionSecondDerivative n chi z) = 0 := by
  let a := d4BMCausalHypergeometricA (d4BMCausalPlusPlusFrequency n chi) chi
  let b := d4BMCausalHypergeometricB (d4BMCausalPlusPlusFrequency n chi) chi
  let c := d4BMCausalRadialC (d4BMCausalPlusPlusFrequency n chi)
  let c0 := d4BMPlusPlusAdSForbiddenHypergeometricC n chi
  let w : ℂ := ((1 - z : ℝ) : ℂ)
  let h := d4BMPlusPlusAdSLeadingNormalizableBranch z
  let F := d4BMPlusPlusAdSNormalizableHypergeometricFactor n chi w
  let dF := d4BMPlusPlusAdSNormalizableHypergeometricFirstDerivative n chi w
  let ddF := d4BMPlusPlusAdSNormalizableHypergeometricSecondDerivative n chi w
  have hw0 : 0 < 1 - z := sub_pos.mpr hz1
  have hw1 : 1 - z < 1 := by linarith
  have hw : w ≠ 0 := by
    dsimp [w]
    exact_mod_cast ne_of_gt hw0
  have hode := d4BMPlusPlusAdSNormalizableHypergeometric_standardGaussODE
    n chi w hchi (enorm_ofReal_lt_one hw0 hw1)
  have hfactor := complementaryGaussJet_factor a b c0 w h F dF ddF hw
  have hc0 : c0 = 1 / 2 := d4BMPlusPlusAdSForbiddenHypergeometricC_eq n chi
  have hcbal : c = a + b + 1 - c0 := by
    dsimp [a, b, c, c0]
    rw [d4BMPlusPlusAdSForbiddenHypergeometricC]
    ring
  have hA : a - c0 + 1 = d4BMPlusPlusAdSNormalizableHypergeometricA n chi := by
    dsimp [a, c0]
    rw [d4BMPlusPlusAdSForbiddenHypergeometricC]
    rw [d4BMPlusPlusAdSNormalizableHypergeometricA]
    ring
  have hB : b - c0 + 1 = d4BMPlusPlusAdSNormalizableHypergeometricB n chi := by
    dsimp [b, c0]
    rw [d4BMPlusPlusAdSForbiddenHypergeometricC]
    rw [d4BMPlusPlusAdSNormalizableHypergeometricB]
    ring
  have hC : 2 - c0 = d4BMPlusPlusAdSNormalizableHypergeometricC n chi := by
    rw [hc0, d4BMPlusPlusAdSNormalizableHypergeometricC_eq]
    ring
  rw [hA, hB] at hfactor
  have hfactor0 :
      w * (1 - w) *
          (((1 - c0) * ((1 - c0) - 1) * h / w ^ (2 : ℕ)) * F +
            2 * ((1 - c0) * h / w) * dF + h * ddF) +
        (c0 - (a + b + 1) * w) *
          (((1 - c0) * h / w) * F + h * dF) -
        a * b * (h * F) = 0 := by
    rw [hfactor, hC, hode, mul_zero]
  rw [d4BMPlusPlusHypergeometricJet,
    d4BMPlusPlusAdSNormalizableSolution,
    d4BMPlusPlusAdSNormalizableSolutionDerivative,
    d4BMPlusPlusAdSNormalizableSolutionSecondDerivative]
  change
    (((z * (1 - z) : ℝ) : ℂ)) *
          (d4BMPlusPlusAdSLeadingNormalizableBranchSecondDerivative z * F -
            2 * d4BMPlusPlusAdSLeadingNormalizableBranchDerivative z * dF + h * ddF) +
        (c - (a + b + 1) * (z : ℂ)) *
          (d4BMPlusPlusAdSLeadingNormalizableBranchDerivative z * F - h * dF) -
      a * b * (h * F) = 0
  push_cast
  rw [hcbal, hc0]
  rw [hc0] at hfactor0
  rw [d4BMPlusPlusAdSLeadingNormalizableBranchDerivative,
    d4BMPlusPlusAdSLeadingNormalizableBranchSecondDerivative]
  dsimp [w, h, F, dF, ddF] at hfactor0 ⊢
  convert hfactor0 using 1
  all_goals push_cast
  all_goals ring

/-- Every Xi fibre carries the exact square-root AdS normalizable solution jet. -/
theorem d4BMXiPlusPlusAdSNormalizableSolution_jet_eq_zero
    (n : ℕ) (q : XiZeroCopy) {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    d4BMPlusPlusHypergeometricJet n (d4BMXiMixedHorizonAngularMomentum q) z
      (d4BMPlusPlusAdSNormalizableSolution n
        (d4BMXiMixedHorizonAngularMomentum q) z)
      (d4BMPlusPlusAdSNormalizableSolutionDerivative n
        (d4BMXiMixedHorizonAngularMomentum q) z)
      (d4BMPlusPlusAdSNormalizableSolutionSecondDerivative n
        (d4BMXiMixedHorizonAngularMomentum q) z) = 0 :=
  d4BMPlusPlusAdSNormalizableSolution_jet_eq_zero n _
    (d4BMXiMixedHorizonAngularMomentum_re_ne_zero q) hz0 hz1

end

end RHTower
