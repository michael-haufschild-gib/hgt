import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodSpectralMeasure
import GaloisForLFunctions.RHTower.PrimeArchThetaGaussianApertureBalance
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailSeamJets

/-!
# Modular-seam transport of the theta likelihood measure

The positive spectral measure of the normalized higher theta tail extends from the positive
source half-line to every point where its intrinsic coordinate is positive. Modular reflection
then places both source ends on one fixed positive measure. Their channel ratio is a strictly
decreasing exponential with one crossing. Intrinsically, reflection is a reciprocal Möbius
scattering law, crossing is a log-partition secant, and infinitesimal balance fixes the exact first
spectral moment at the seam.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial
open scoped BigOperators ENNReal

namespace RHTower

noncomputable section

/-- Positivity of the first theta atom on the full positive-likelihood-coordinate domain. -/
theorem thetaCuspSourceTerm_one_pos_of_likelihoodCoordinate_pos {x : ℝ}
    (hB : 0 < thetaCuspLikelihoodCoordinate x) :
    0 < thetaCuspSourceTerm x 1 := by
  rw [thetaCuspSourceTerm_eq_scaleForm]
  norm_num
  have hweight : 0 < 2 * (Real.pi * Real.exp x ^ 2) - 3 := by
    unfold thetaCuspLikelihoodCoordinate at hB
    linarith
  positivity

/-- The fixed spectral response represents the actual higher-to-first ratio throughout its
positive intrinsic-coordinate domain. -/
theorem thetaCuspHigherLikelihoodSpectralResponse_coordinate_of_coordinate_pos
    {x : ℝ} (hB : 0 < thetaCuspLikelihoodCoordinate x) :
    thetaCuspHigherLikelihoodSpectralResponse (thetaCuspLikelihoodCoordinate x) =
      thetaCuspHigherToFirstAtomLikelihoodRatio x := by
  rw [thetaCuspHigherToFirstAtomLikelihoodRatio_eq_tsum]
  unfold thetaCuspHigherLikelihoodSpectralResponse
  refine tsum_congr fun k => ?_
  exact (thetaCuspAtomLikelihoodRatio_eq_spectralTerm_of_coordinate_pos hB).symm

/-- The full theta source is the first atom times the fixed positive Laplace carrier wherever the
intrinsic likelihood coordinate is positive. -/
theorem thetaCuspFullSource_eq_first_mul_one_add_spectralIntegral_of_coordinate_pos
    {x : ℝ} (hB : 0 < thetaCuspLikelihoodCoordinate x) :
    thetaCuspFullSource x = thetaCuspSourceTerm x 1 *
      (1 + ∫ t : ℝ, Real.exp (-thetaCuspLikelihoodCoordinate x * t)
        ∂thetaCuspHigherLikelihoodSpectralMeasure) := by
  have hfirst := thetaCuspSourceTerm_one_pos_of_likelihoodCoordinate_pos hB
  rw [integral_exp_neg_mul_thetaCuspHigherLikelihoodSpectralMeasure hB,
    thetaCuspHigherLikelihoodSpectralResponse_coordinate_of_coordinate_pos hB]
  unfold thetaCuspHigherToFirstAtomLikelihoodRatio
  field_simp [hfirst.ne']
  ring

/-- Exact balance of the two reflected likelihood carriers across the modular seam. -/
theorem thetaCuspLikelihood_reflected_spectral_balance {x : ℝ}
    (hBx : 0 < thetaCuspLikelihoodCoordinate x)
    (hBnx : 0 < thetaCuspLikelihoodCoordinate (-x)) :
    thetaCuspSourceTerm x 1 *
        (1 + ∫ t : ℝ, Real.exp (-thetaCuspLikelihoodCoordinate x * t)
          ∂thetaCuspHigherLikelihoodSpectralMeasure) =
      thetaCuspSourceTerm (-x) 1 *
        (1 + ∫ t : ℝ, Real.exp (-thetaCuspLikelihoodCoordinate (-x) * t)
          ∂thetaCuspHigherLikelihoodSpectralMeasure) := by
  rw [← thetaCuspFullSource_eq_first_mul_one_add_spectralIntegral_of_coordinate_pos hBx,
    ← thetaCuspFullSource_eq_first_mul_one_add_spectralIntegral_of_coordinate_pos hBnx]
  exact (thetaCuspFullSource_neg x).symm

/-- Every higher-atom spectral response is strictly positive at positive temperature. -/
theorem thetaCuspAtomLikelihoodSpectralTerm_pos
    {n : ℕ} (hn : 2 ≤ n) {B : ℝ} (hB : 0 < B) :
    0 < thetaCuspAtomLikelihoodSpectralTerm n B := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by omega) hn)
  have hd := thetaCuspLikelihoodGap_pos hn
  unfold thetaCuspAtomLikelihoodSpectralTerm
  positivity

/-- Every higher-atom spectral response is strictly decreasing in temperature. -/
theorem thetaCuspAtomLikelihoodSpectralTerm_strictAnti
    {n : ℕ} (hn : 2 ≤ n) {B C : ℝ} (hB : 0 < B) (hBC : B < C) :
    thetaCuspAtomLikelihoodSpectralTerm n C <
      thetaCuspAtomLikelihoodSpectralTerm n B := by
  have hC : 0 < C := hB.trans hBC
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by omega) hn)
  have hd := thetaCuspLikelihoodGap_pos hn
  have hExp : Real.exp (-C * thetaCuspLikelihoodGap n) <
      Real.exp (-B * thetaCuspLikelihoodGap n) := by
    apply Real.exp_lt_exp.mpr
    nlinarith
  have hDiv : Real.exp (-C * thetaCuspLikelihoodGap n) / C <
      Real.exp (-B * thetaCuspLikelihoodGap n) / B := by
    rw [div_lt_div_iff₀ hC hB]
    exact (mul_lt_mul_of_pos_right hExp hB).trans
      (mul_lt_mul_of_pos_left hBC (Real.exp_pos _))
  have hfirst :
      (n : ℝ) ^ 4 * Real.exp (-C * thetaCuspLikelihoodGap n) <
        (n : ℝ) ^ 4 * Real.exp (-B * thetaCuspLikelihoodGap n) :=
    mul_lt_mul_of_pos_left hExp (pow_pos hnR 4)
  have hweight :
      0 < (3 / 2 : ℝ) * (n : ℝ) ^ 2 * thetaCuspLikelihoodGap n := by
    positivity
  have hsecond :
      (3 / 2 : ℝ) * (n : ℝ) ^ 2 * thetaCuspLikelihoodGap n *
          (Real.exp (-C * thetaCuspLikelihoodGap n) / C) <
        (3 / 2 : ℝ) * (n : ℝ) ^ 2 * thetaCuspLikelihoodGap n *
          (Real.exp (-B * thetaCuspLikelihoodGap n) / B) :=
    mul_lt_mul_of_pos_left hDiv hweight
  unfold thetaCuspAtomLikelihoodSpectralTerm
  apply mul_lt_mul_of_pos_left _ (Real.exp_pos _)
  have hsecond' :
      (3 / 2 : ℝ) * (n : ℝ) ^ 2 * thetaCuspLikelihoodGap n *
          Real.exp (-C * thetaCuspLikelihoodGap n) / C <
        (3 / 2 : ℝ) * (n : ℝ) ^ 2 * thetaCuspLikelihoodGap n *
          Real.exp (-B * thetaCuspLikelihoodGap n) / B := by
    calc
      _ = (3 / 2 : ℝ) * (n : ℝ) ^ 2 * thetaCuspLikelihoodGap n *
          (Real.exp (-C * thetaCuspLikelihoodGap n) / C) := by ring
      _ < _ := hsecond
      _ = _ := by ring
  exact add_lt_add hfirst hsecond'

/-- The complete higher-tail spectral response is strictly decreasing on the positive half-line. -/
theorem thetaCuspHigherLikelihoodSpectralResponse_strictAnti
    {B C : ℝ} (hB : 0 < B) (hBC : B < C) :
    thetaCuspHigherLikelihoodSpectralResponse C <
      thetaCuspHigherLikelihoodSpectralResponse B := by
  have hC : 0 < C := hB.trans hBC
  unfold thetaCuspHigherLikelihoodSpectralResponse
  exact Summable.tsum_lt_tsum_of_nonneg
    (fun k => (thetaCuspAtomLikelihoodSpectralTerm_pos (n := k + 2) (by omega) hC).le)
    (fun k => (thetaCuspAtomLikelihoodSpectralTerm_strictAnti (n := k + 2) (by omega) hB hBC).le)
    (thetaCuspAtomLikelihoodSpectralTerm_strictAnti (n := 2) (by norm_num) hB hBC)
    (summable_thetaCuspAtomLikelihoodSpectralTerm hB)

/-- The intrinsic coordinate is strictly larger at the positive reflected source point. -/
theorem thetaCuspLikelihoodCoordinate_neg_lt {x : ℝ} (hx : 0 < x) :
    thetaCuspLikelihoodCoordinate (-x) < thetaCuspLikelihoodCoordinate x := by
  have he : Real.exp (-x) < Real.exp x :=
    Real.exp_lt_exp.mpr (by linarith)
  have heNeg := Real.exp_pos (-x)
  have hePos := Real.exp_pos x
  unfold thetaCuspLikelihoodCoordinate
  have hsq : Real.exp (-x) ^ 2 < Real.exp x ^ 2 := by nlinarith
  nlinarith [Real.pi_pos]

/-! ### Exact modular scattering in the likelihood coordinate -/

/-- Modular reflection written intrinsically in the affine likelihood coordinate. -/
def thetaCuspLikelihoodModularInvolution (B : ℝ) : ℝ :=
  Real.pi ^ 2 / (B + 3 / 2) - 3 / 2

/-- Source reflection is the fractional-linear modular involution in likelihood temperature. -/
theorem thetaCuspLikelihoodCoordinate_neg_eq_modularInvolution (x : ℝ) :
    thetaCuspLikelihoodCoordinate (-x) =
      thetaCuspLikelihoodModularInvolution (thetaCuspLikelihoodCoordinate x) := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hexp : Real.exp x ≠ 0 := Real.exp_ne_zero x
  unfold thetaCuspLikelihoodCoordinate thetaCuspLikelihoodModularInvolution
  rw [Real.exp_neg]
  field_simp [hpi, hexp]
  ring

/-- The intrinsic modular temperature map is an involution on its natural domain. -/
theorem thetaCuspLikelihoodModularInvolution_involution
    {B : ℝ} (hB : -3 / 2 < B) :
    thetaCuspLikelihoodModularInvolution
        (thetaCuspLikelihoodModularInvolution B) = B := by
  have hden : B + 3 / 2 ≠ 0 := by linarith
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold thetaCuspLikelihoodModularInvolution
  have hcollapse :
      Real.pi ^ 2 / (Real.pi ^ 2 / (B + 3 / 2)) = B + 3 / 2 := by
    rw [div_eq_mul_inv, inv_div]
    field_simp [hden, hpi]
  rw [show Real.pi ^ 2 / (B + 3 / 2) - 3 / 2 + 3 / 2 =
      Real.pi ^ 2 / (B + 3 / 2) by ring, hcollapse]
  ring

/-- Positive Laplace partition carried by the first atom and the complete higher likelihood tail. -/
def thetaCuspLikelihoodPartition (B : ℝ) : ℝ :=
  1 + thetaCuspHigherLikelihoodSpectralResponse B

/-- The likelihood partition is strictly positive at positive temperature. -/
theorem thetaCuspLikelihoodPartition_pos {B : ℝ} (hB : 0 < B) :
    0 < thetaCuspLikelihoodPartition B := by
  rw [thetaCuspLikelihoodPartition,
    ← integral_exp_neg_mul_thetaCuspHigherLikelihoodSpectralMeasure hB]
  have hnonneg : 0 ≤
      ∫ t : ℝ, Real.exp (-B * t)
        ∂thetaCuspHigherLikelihoodSpectralMeasure :=
    integral_nonneg fun t => (Real.exp_pos _).le
  linarith

/-- Positive modular scattering multiplier between the two first-atom boundary channels. -/
def thetaCuspLikelihoodSeamScattering (x : ℝ) : ℝ :=
  thetaCuspSourceTerm (-x) 1 / thetaCuspSourceTerm x 1

/-- Exact multiplicative scattering law for the latent likelihood partition. -/
theorem thetaCuspLikelihoodPartition_modular_scattering
    {x : ℝ}
    (hBx : 0 < thetaCuspLikelihoodCoordinate x)
    (hBnx : 0 < thetaCuspLikelihoodCoordinate (-x)) :
    thetaCuspLikelihoodPartition (thetaCuspLikelihoodCoordinate x) =
      thetaCuspLikelihoodSeamScattering x *
        thetaCuspLikelihoodPartition (thetaCuspLikelihoodCoordinate (-x)) := by
  have hbal := thetaCuspLikelihood_reflected_spectral_balance hBx hBnx
  rw [integral_exp_neg_mul_thetaCuspHigherLikelihoodSpectralMeasure hBx,
    integral_exp_neg_mul_thetaCuspHigherLikelihoodSpectralMeasure hBnx] at hbal
  have hsource := thetaCuspSourceTerm_one_pos_of_likelihoodCoordinate_pos hBx
  unfold thetaCuspLikelihoodPartition thetaCuspLikelihoodSeamScattering
  field_simp [hsource.ne']
  nlinarith

/-- Modular scattering is reciprocal under reflection. -/
theorem thetaCuspLikelihoodSeamScattering_mul_reflection
    {x : ℝ}
    (hBx : 0 < thetaCuspLikelihoodCoordinate x)
    (hBnx : 0 < thetaCuspLikelihoodCoordinate (-x)) :
    thetaCuspLikelihoodSeamScattering x *
        thetaCuspLikelihoodSeamScattering (-x) = 1 := by
  have hx := thetaCuspSourceTerm_one_pos_of_likelihoodCoordinate_pos hBx
  have hnx := thetaCuspSourceTerm_one_pos_of_likelihoodCoordinate_pos hBnx
  unfold thetaCuspLikelihoodSeamScattering
  rw [neg_neg]
  field_simp [hx.ne', hnx.ne']

/-- Inside the modular-seam window, the positive-side first atom strictly dominates its reflected
negative-side value. The higher-tail carrier supplies the exact opposite balance. -/
theorem thetaCuspFirstAtom_reflected_lt_of_likelihoodCoordinate_neg_pos
    {x : ℝ} (hx : 0 < x)
    (hBnx : 0 < thetaCuspLikelihoodCoordinate (-x)) :
    thetaCuspSourceTerm (-x) 1 < thetaCuspSourceTerm x 1 := by
  have hcoord := thetaCuspLikelihoodCoordinate_neg_lt hx
  have hBx : 0 < thetaCuspLikelihoodCoordinate x := hBnx.trans hcoord
  have hresponse := thetaCuspHigherLikelihoodSpectralResponse_strictAnti hBnx hcoord
  have hbal := thetaCuspLikelihood_reflected_spectral_balance hBx hBnx
  rw [integral_exp_neg_mul_thetaCuspHigherLikelihoodSpectralMeasure hBx,
    integral_exp_neg_mul_thetaCuspHigherLikelihoodSpectralMeasure hBnx] at hbal
  have hposx := thetaCuspSourceTerm_one_pos_of_likelihoodCoordinate_pos hBx
  have hposnx := thetaCuspSourceTerm_one_pos_of_likelihoodCoordinate_pos hBnx
  have hnonneg (q : ℝ) (hq : 0 < q) :
      0 ≤ thetaCuspHigherLikelihoodSpectralResponse q := by
    rw [← integral_exp_neg_mul_thetaCuspHigherLikelihoodSpectralMeasure hq]
    exact integral_nonneg fun t => (Real.exp_pos _).le
  by_contra h
  have hle : thetaCuspSourceTerm x 1 ≤ thetaCuspSourceTerm (-x) 1 := le_of_not_gt h
  have hprod :
      thetaCuspSourceTerm x 1 *
          (1 + thetaCuspHigherLikelihoodSpectralResponse
            (thetaCuspLikelihoodCoordinate x)) <
        thetaCuspSourceTerm (-x) 1 *
          (1 + thetaCuspHigherLikelihoodSpectralResponse
            (thetaCuspLikelihoodCoordinate (-x))) := by
    have hfacNonneg :
        0 ≤ 1 + thetaCuspHigherLikelihoodSpectralResponse
          (thetaCuspLikelihoodCoordinate x) := by
      linarith [hnonneg _ hBx]
    have hfacLt :
        1 + thetaCuspHigherLikelihoodSpectralResponse
            (thetaCuspLikelihoodCoordinate x) <
          1 + thetaCuspHigherLikelihoodSpectralResponse
            (thetaCuspLikelihoodCoordinate (-x)) := by
      linarith
    exact (mul_le_mul_of_nonneg_right hle hfacNonneg).trans_lt
      (mul_lt_mul_of_pos_left hfacLt hposnx)
  exact (ne_of_lt hprod) hbal

/-- On the positive modular-seam side, the scattering multiplier is a strict contraction. -/
theorem thetaCuspLikelihoodSeamScattering_mem_Ioo
    {x : ℝ} (hx : 0 < x)
    (hBnx : 0 < thetaCuspLikelihoodCoordinate (-x)) :
    thetaCuspLikelihoodSeamScattering x ∈ Set.Ioo 0 1 := by
  have hcoord := thetaCuspLikelihoodCoordinate_neg_lt hx
  have hBx : 0 < thetaCuspLikelihoodCoordinate x := hBnx.trans hcoord
  have hsource :=
    thetaCuspFirstAtom_reflected_lt_of_likelihoodCoordinate_neg_pos hx hBnx
  have hsourceX := thetaCuspSourceTerm_one_pos_of_likelihoodCoordinate_pos hBx
  have hsourceNeg := thetaCuspSourceTerm_one_pos_of_likelihoodCoordinate_pos hBnx
  constructor
  · exact div_pos hsourceNeg hsourceX
  · exact (div_lt_one hsourceX).mpr hsource

/-- The fixed positive measure containing the first atom at spectral coordinate zero and the
complete higher-tail likelihood measure. -/
def thetaCuspLikelihoodSeamMeasure : Measure ℝ :=
  Measure.dirac 0 + thetaCuspHigherLikelihoodSpectralMeasure

/-- One latent likelihood channel of the first theta atom. -/
def thetaCuspLikelihoodSeamChannel (x t : ℝ) : ℝ :=
  thetaCuspSourceTerm x 1 *
    Real.exp (-thetaCuspLikelihoodCoordinate x * t)

/-- Every channel is integrable against the fixed seam measure on the positive-coordinate domain. -/
theorem integrable_thetaCuspLikelihoodSeamChannel
    {x : ℝ} (hBx : 0 < thetaCuspLikelihoodCoordinate x) :
    Integrable (thetaCuspLikelihoodSeamChannel x)
      thetaCuspLikelihoodSeamMeasure := by
  rw [thetaCuspLikelihoodSeamMeasure]
  apply Integrable.add_measure
  · exact integrable_dirac (by simp [thetaCuspLikelihoodSeamChannel])
  · exact (integrable_exp_neg_mul_thetaCuspHigherLikelihoodSpectralMeasure hBx).const_mul _

/-- Integrating one source point over the fixed seam measure reconstructs the completed source. -/
theorem integral_thetaCuspLikelihoodSeamChannel
    {x : ℝ} (hBx : 0 < thetaCuspLikelihoodCoordinate x) :
    (∫ t : ℝ, thetaCuspLikelihoodSeamChannel x t
        ∂thetaCuspLikelihoodSeamMeasure) = thetaCuspFullSource x := by
  have hdirac : Integrable (thetaCuspLikelihoodSeamChannel x) (Measure.dirac 0) :=
    integrable_dirac (by simp [thetaCuspLikelihoodSeamChannel])
  have hhigher : Integrable (thetaCuspLikelihoodSeamChannel x)
      thetaCuspHigherLikelihoodSpectralMeasure :=
    (integrable_exp_neg_mul_thetaCuspHigherLikelihoodSpectralMeasure hBx).const_mul _
  rw [thetaCuspLikelihoodSeamMeasure, integral_add_measure hdirac hhigher,
    integral_dirac]
  simp only [thetaCuspLikelihoodSeamChannel]
  rw [integral_const_mul]
  rw [thetaCuspFullSource_eq_first_mul_one_add_spectralIntegral_of_coordinate_pos hBx]
  simp only [mul_zero, Real.exp_zero, mul_one]
  ring

/-- The reflected channels have equal total mass on the fixed seam measure. -/
theorem integral_thetaCuspLikelihoodSeamChannel_reflection
    {x : ℝ}
    (hBx : 0 < thetaCuspLikelihoodCoordinate x)
    (hBnx : 0 < thetaCuspLikelihoodCoordinate (-x)) :
    (∫ t : ℝ, thetaCuspLikelihoodSeamChannel x t
        ∂thetaCuspLikelihoodSeamMeasure) =
      ∫ t : ℝ, thetaCuspLikelihoodSeamChannel (-x) t
        ∂thetaCuspLikelihoodSeamMeasure := by
  rw [integral_thetaCuspLikelihoodSeamChannel hBx,
    integral_thetaCuspLikelihoodSeamChannel hBnx]
  exact (thetaCuspFullSource_neg x).symm

/-- Every odd jet of the integrated fixed-measure channel vanishes at the modular seam. This is
the all-order cancellation hierarchy before expanding each channel jet into spectral moments. -/
theorem iteratedDeriv_integral_thetaCuspLikelihoodSeamChannel_zero_of_odd
    {m : ℕ} (hm : Odd m) :
    iteratedDeriv m
      (fun x : ℝ => ∫ t : ℝ, thetaCuspLikelihoodSeamChannel x t
        ∂thetaCuspLikelihoodSeamMeasure) 0 = 0 := by
  have hB0 : 0 < thetaCuspLikelihoodCoordinate 0 := by
    unfold thetaCuspLikelihoodCoordinate
    norm_num
    nlinarith [Real.pi_gt_three]
  have hcont : ContinuousAt thetaCuspLikelihoodCoordinate 0 := by
    unfold thetaCuspLikelihoodCoordinate
    fun_prop
  have hevent : ∀ᶠ x in nhds 0, 0 < thetaCuspLikelihoodCoordinate x :=
    hcont.tendsto (Ioi_mem_nhds hB0)
  have heq :
      (fun x : ℝ => ∫ t : ℝ, thetaCuspLikelihoodSeamChannel x t
        ∂thetaCuspLikelihoodSeamMeasure) =ᶠ[nhds 0]
      thetaCuspFullSource := by
    filter_upwards [hevent] with x hx
    exact integral_thetaCuspLikelihoodSeamChannel hx
  rw [heq.iteratedDeriv_eq m]
  exact iteratedDeriv_thetaCuspFullSource_zero_of_odd hm

/-- Unique crossing location of the two reflected likelihood channels. -/
def thetaCuspLikelihoodSeamCrossing (x : ℝ) : ℝ :=
  Real.log (thetaCuspSourceTerm x 1 / thetaCuspSourceTerm (-x) 1) /
    (thetaCuspLikelihoodCoordinate x - thetaCuspLikelihoodCoordinate (-x))

/-- The reflected channels cross at a positive latent spectral coordinate. -/
theorem thetaCuspLikelihoodSeamCrossing_pos
    {x : ℝ} (hx : 0 < x)
    (hBnx : 0 < thetaCuspLikelihoodCoordinate (-x)) :
    0 < thetaCuspLikelihoodSeamCrossing x := by
  have hcoord := thetaCuspLikelihoodCoordinate_neg_lt hx
  have hBx : 0 < thetaCuspLikelihoodCoordinate x := hBnx.trans hcoord
  have hsource := thetaCuspFirstAtom_reflected_lt_of_likelihoodCoordinate_neg_pos hx hBnx
  have hsourceNeg := thetaCuspSourceTerm_one_pos_of_likelihoodCoordinate_pos hBnx
  have hratio : 1 < thetaCuspSourceTerm x 1 / thetaCuspSourceTerm (-x) 1 :=
    (one_lt_div hsourceNeg).mpr hsource
  unfold thetaCuspLikelihoodSeamCrossing
  exact div_pos (Real.log_pos hratio) (sub_pos.mpr hcoord)

/-- The channel crossing is the negative divided slope of the log likelihood partition along one
modular orbit. This is the exact thermodynamic scattering phase, with no endpoint expansion. -/
theorem thetaCuspLikelihoodSeamCrossing_eq_logPartition_secant
    {x : ℝ} (hx : 0 < x)
    (hBnx : 0 < thetaCuspLikelihoodCoordinate (-x)) :
    thetaCuspLikelihoodSeamCrossing x =
      (Real.log (thetaCuspLikelihoodPartition
          (thetaCuspLikelihoodCoordinate (-x))) -
        Real.log (thetaCuspLikelihoodPartition
          (thetaCuspLikelihoodCoordinate x))) /
        (thetaCuspLikelihoodCoordinate x -
          thetaCuspLikelihoodCoordinate (-x)) := by
  have hcoord := thetaCuspLikelihoodCoordinate_neg_lt hx
  have hBx : 0 < thetaCuspLikelihoodCoordinate x := hBnx.trans hcoord
  have hsourceNeg := thetaCuspSourceTerm_one_pos_of_likelihoodCoordinate_pos hBnx
  have hpartX := thetaCuspLikelihoodPartition_pos hBx
  have hpartNeg := thetaCuspLikelihoodPartition_pos hBnx
  have hbal := thetaCuspLikelihood_reflected_spectral_balance hBx hBnx
  rw [integral_exp_neg_mul_thetaCuspHigherLikelihoodSpectralMeasure hBx,
    integral_exp_neg_mul_thetaCuspHigherLikelihoodSpectralMeasure hBnx] at hbal
  have hratio :
      thetaCuspSourceTerm x 1 / thetaCuspSourceTerm (-x) 1 =
        thetaCuspLikelihoodPartition (thetaCuspLikelihoodCoordinate (-x)) /
          thetaCuspLikelihoodPartition (thetaCuspLikelihoodCoordinate x) := by
    apply (div_eq_div_iff hsourceNeg.ne' hpartX.ne').2
    simpa [thetaCuspLikelihoodPartition, mul_comm] using hbal
  unfold thetaCuspLikelihoodSeamCrossing
  rw [hratio, Real.log_div hpartNeg.ne' hpartX.ne']

/-- Exact exponential likelihood ratio between the two reflected channels. -/
theorem thetaCuspLikelihoodSeamChannel_reflection_eq
    {x : ℝ} (hx : 0 < x)
    (hBnx : 0 < thetaCuspLikelihoodCoordinate (-x)) (t : ℝ) :
    thetaCuspLikelihoodSeamChannel x t =
      thetaCuspLikelihoodSeamChannel (-x) t *
        Real.exp ((thetaCuspLikelihoodCoordinate x -
          thetaCuspLikelihoodCoordinate (-x)) *
            (thetaCuspLikelihoodSeamCrossing x - t)) := by
  have hcoord := thetaCuspLikelihoodCoordinate_neg_lt hx
  have hBx : 0 < thetaCuspLikelihoodCoordinate x := hBnx.trans hcoord
  have hsourceX := thetaCuspSourceTerm_one_pos_of_likelihoodCoordinate_pos hBx
  have hsourceNeg := thetaCuspSourceTerm_one_pos_of_likelihoodCoordinate_pos hBnx
  have hdelta : thetaCuspLikelihoodCoordinate x -
      thetaCuspLikelihoodCoordinate (-x) ≠ 0 := (sub_pos.mpr hcoord).ne'
  unfold thetaCuspLikelihoodSeamChannel thetaCuspLikelihoodSeamCrossing
  calc
    thetaCuspSourceTerm x 1 *
          Real.exp (-thetaCuspLikelihoodCoordinate x * t) =
        Real.exp (Real.log (thetaCuspSourceTerm x 1) +
          (-thetaCuspLikelihoodCoordinate x * t)) := by
      rw [Real.exp_add, Real.exp_log hsourceX]
    _ = Real.exp (Real.log (thetaCuspSourceTerm (-x) 1) +
          (-thetaCuspLikelihoodCoordinate (-x) * t) +
          (thetaCuspLikelihoodCoordinate x -
            thetaCuspLikelihoodCoordinate (-x)) *
            (Real.log
                (thetaCuspSourceTerm x 1 / thetaCuspSourceTerm (-x) 1) /
              (thetaCuspLikelihoodCoordinate x -
                thetaCuspLikelihoodCoordinate (-x)) - t)) := by
      apply congrArg Real.exp
      rw [Real.log_div hsourceX.ne' hsourceNeg.ne']
      field_simp [hdelta]
      ring
    _ = thetaCuspSourceTerm (-x) 1 *
          Real.exp (-thetaCuspLikelihoodCoordinate (-x) * t) *
          Real.exp ((thetaCuspLikelihoodCoordinate x -
            thetaCuspLikelihoodCoordinate (-x)) *
            (Real.log
                (thetaCuspSourceTerm x 1 / thetaCuspSourceTerm (-x) 1) /
              (thetaCuspLikelihoodCoordinate x -
                thetaCuspLikelihoodCoordinate (-x)) - t)) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_log hsourceNeg]

/-- Single-crossing law: the positive-side channel dominates exactly below the crossing. -/
theorem thetaCuspLikelihoodSeamChannel_reflection_lt_iff
    {x : ℝ} (hx : 0 < x)
    (hBnx : 0 < thetaCuspLikelihoodCoordinate (-x)) (t : ℝ) :
    thetaCuspLikelihoodSeamChannel (-x) t <
        thetaCuspLikelihoodSeamChannel x t ↔
      t < thetaCuspLikelihoodSeamCrossing x := by
  rw [thetaCuspLikelihoodSeamChannel_reflection_eq hx hBnx]
  have hchannel : 0 < thetaCuspLikelihoodSeamChannel (-x) t := by
    unfold thetaCuspLikelihoodSeamChannel
    exact mul_pos (thetaCuspSourceTerm_one_pos_of_likelihoodCoordinate_pos hBnx) (Real.exp_pos _)
  have hdelta := sub_pos.mpr (thetaCuspLikelihoodCoordinate_neg_lt hx)
  constructor
  · intro h
    have hfactor : 1 < Real.exp
        ((thetaCuspLikelihoodCoordinate x -
          thetaCuspLikelihoodCoordinate (-x)) *
            (thetaCuspLikelihoodSeamCrossing x - t)) := by
      by_contra hnot
      have hle : Real.exp
          ((thetaCuspLikelihoodCoordinate x -
            thetaCuspLikelihoodCoordinate (-x)) *
              (thetaCuspLikelihoodSeamCrossing x - t)) ≤ 1 :=
        le_of_not_gt hnot
      have hmul := mul_le_mul_of_nonneg_left hle hchannel.le
      nlinarith
    rw [← Real.exp_zero, Real.exp_lt_exp] at hfactor
    nlinarith
  · intro h
    have hexponent : 0 <
        (thetaCuspLikelihoodCoordinate x -
          thetaCuspLikelihoodCoordinate (-x)) *
            (thetaCuspLikelihoodSeamCrossing x - t) :=
      mul_pos hdelta (sub_pos.mpr h)
    have hfactor : 1 < Real.exp
        ((thetaCuspLikelihoodCoordinate x -
          thetaCuspLikelihoodCoordinate (-x)) *
            (thetaCuspLikelihoodSeamCrossing x - t)) := by
      rw [← Real.exp_zero, Real.exp_lt_exp]
      exact hexponent
    simpa only [mul_one] using mul_lt_mul_of_pos_left hfactor hchannel

/-- Differentiating the fixed Laplace response produces the negative first tilted moment. -/
theorem hasDerivAt_thetaCuspHigherLikelihoodSpectralResponse
    {B : ℝ} (hB : 0 < B) :
    HasDerivAt thetaCuspHigherLikelihoodSpectralResponse
      (-thetaCuspHigherLikelihoodSpectralMoment B 1) B := by
  let s : Set ℝ := Metric.ball B (B / 2)
  let bound : ℝ → ℝ := fun t => t * Real.exp (-(B / 2) * t)
  have hs : s ∈ nhds B := Metric.ball_mem_nhds B (half_pos hB)
  have hpositive : ∀ z ∈ s, B / 2 < z := by
    intro z hz
    have habs : |z - B| < B / 2 := by
      simpa [s, Real.dist_eq] using hz
    have hneg : -(B / 2) < z - B := (neg_lt_of_abs_lt habs)
    linarith
  have hFmeas : ∀ᶠ z in nhds B,
      AEStronglyMeasurable (fun t : ℝ => Real.exp (-z * t))
        thetaCuspHigherLikelihoodSpectralMeasure := by
    filter_upwards with z
    exact (by fun_prop : Continuous (fun t : ℝ => Real.exp (-z * t))).aestronglyMeasurable
  have hF'meas :
      AEStronglyMeasurable (fun t : ℝ => -t * Real.exp (-B * t))
        thetaCuspHigherLikelihoodSpectralMeasure :=
    (by fun_prop : Continuous
      (fun t : ℝ => -t * Real.exp (-B * t))).aestronglyMeasurable
  have hboundInt : Integrable bound thetaCuspHigherLikelihoodSpectralMeasure := by
    simpa [bound] using
      integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 1
        (half_pos hB)
  have hdom : ∀ᵐ t ∂thetaCuspHigherLikelihoodSpectralMeasure,
      ∀ z ∈ s, ‖-t * Real.exp (-z * t)‖ ≤ bound t := by
    filter_upwards [ae_nonneg_thetaCuspHigherLikelihoodSpectralMeasure] with t ht
    intro z hz
    have hzLower := hpositive z hz
    have hexp : Real.exp (-z * t) ≤ Real.exp (-(B / 2) * t) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    rw [norm_mul, Real.norm_eq_abs, abs_neg, abs_of_nonneg ht,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    dsimp [bound]
    exact mul_le_mul_of_nonneg_left hexp ht
  have hdiff : ∀ᵐ t ∂thetaCuspHigherLikelihoodSpectralMeasure,
      ∀ z ∈ s, HasDerivAt (fun q : ℝ => Real.exp (-q * t))
        (-t * Real.exp (-z * t)) z := by
    filter_upwards with t z hz
    have hinner : HasDerivAt (fun q : ℝ => -q * t) (-t) z := by
      simpa using (hasDerivAt_id z).neg.mul_const t
    simpa [Function.comp_def, mul_comm] using
      (Real.hasDerivAt_exp (-z * t)).comp z hinner
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := thetaCuspHigherLikelihoodSpectralMeasure)
    (F := fun z t : ℝ => Real.exp (-z * t))
    (F' := fun z t : ℝ => -t * Real.exp (-z * t))
    (bound := bound) hs hFmeas
    (integrable_exp_neg_mul_thetaCuspHigherLikelihoodSpectralMeasure hB)
    hF'meas hdom hboundInt hdiff
  have hderiv : HasDerivAt
      (fun q : ℝ => ∫ t : ℝ, Real.exp (-q * t)
        ∂thetaCuspHigherLikelihoodSpectralMeasure)
      (-thetaCuspHigherLikelihoodSpectralMoment B 1) B := by
    convert hmain.2 using 1
    rw [thetaCuspHigherLikelihoodSpectralMoment_eq_integral]
    simp only [pow_one]
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards with t
    ring
  have heq :
      (fun q : ℝ => ∫ t : ℝ, Real.exp (-q * t)
        ∂thetaCuspHigherLikelihoodSpectralMeasure) =ᶠ[nhds B]
      thetaCuspHigherLikelihoodSpectralResponse := by
    filter_upwards [Ioi_mem_nhds hB] with q hq
    exact integral_exp_neg_mul_thetaCuspHigherLikelihoodSpectralMeasure hq
  exact hderiv.congr_of_eventuallyEq heq.symm

/-- Mean latent spectral coordinate in the normalized seam likelihood state. -/
def thetaCuspLikelihoodSeamMean (B : ℝ) : ℝ :=
  thetaCuspHigherLikelihoodSpectralMoment B 1 /
    thetaCuspLikelihoodPartition B

/-- The latent mean is the negative logarithmic derivative of the modular likelihood partition. -/
theorem hasDerivAt_log_thetaCuspLikelihoodPartition
    {B : ℝ} (hB : 0 < B) :
    HasDerivAt (fun q : ℝ => Real.log (thetaCuspLikelihoodPartition q))
      (-thetaCuspLikelihoodSeamMean B) B := by
  have hpart : HasDerivAt thetaCuspLikelihoodPartition
      (-thetaCuspHigherLikelihoodSpectralMoment B 1) B := by
    unfold thetaCuspLikelihoodPartition
    exact (hasDerivAt_thetaCuspHigherLikelihoodSpectralResponse hB).const_add 1
  have hpos := thetaCuspLikelihoodPartition_pos hB
  have hlog := hpart.log hpos.ne'
  convert hlog using 1
  unfold thetaCuspLikelihoodSeamMean
  ring

/-- Exact modular-seam barycenter law for the positive higher-tail spectral measure. -/
theorem thetaCuspHigherLikelihoodSpectralMoment_seam_barycenter :
    2 * Real.pi * thetaCuspHigherLikelihoodSpectralMoment
        (thetaCuspLikelihoodCoordinate 0) 1 =
      thetaCuspFirstAtomBoundaryLogSlope *
        (1 + thetaCuspHigherLikelihoodSpectralMoment
          (thetaCuspLikelihoodCoordinate 0) 0) := by
  have hB0 : 0 < thetaCuspLikelihoodCoordinate 0 := by
    unfold thetaCuspLikelihoodCoordinate
    norm_num
    nlinarith [Real.pi_gt_three]
  have hcoord : HasDerivAt thetaCuspLikelihoodCoordinate (2 * Real.pi) 0 := by
    unfold thetaCuspLikelihoodCoordinate
    convert (((Real.hasDerivAt_exp 0).pow 2).const_mul Real.pi).sub_const (3 / 2) using 1
    all_goals norm_num
    all_goals ring
  have hresponse :=
    (hasDerivAt_thetaCuspHigherLikelihoodSpectralResponse hB0).comp 0 hcoord
  have hresponse' : HasDerivAt
      (fun x : ℝ => 1 + thetaCuspHigherLikelihoodSpectralResponse
        (thetaCuspLikelihoodCoordinate x))
      (-(2 * Real.pi * thetaCuspHigherLikelihoodSpectralMoment
        (thetaCuspLikelihoodCoordinate 0) 1)) 0 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hresponse.const_add 1
  have hproduct := hasDerivAt_thetaCuspSourceTerm_one_zero.mul hresponse'
  have hM0 :
      thetaCuspHigherLikelihoodSpectralResponse
          (thetaCuspLikelihoodCoordinate 0) =
        thetaCuspHigherLikelihoodSpectralMoment
          (thetaCuspLikelihoodCoordinate 0) 0 := by
    rw [← integral_exp_neg_mul_thetaCuspHigherLikelihoodSpectralMeasure hB0,
      thetaCuspHigherLikelihoodSpectralMoment_eq_integral]
    simp only [pow_zero, one_mul]
  have hfullZero : HasDerivAt thetaCuspFullSource 0 0 := by
    have hdiff := hasDerivAt_thetaCuspFullDerivative 0 0
    rw [← iteratedDeriv_thetaCuspFullSource 0,
      ← iteratedDeriv_thetaCuspFullSource 1] at hdiff
    have hodd := iteratedDeriv_thetaCuspFullSource_zero_of_odd
      (show Odd 1 by exact ⟨0, by omega⟩)
    rw [hodd] at hdiff
    simpa using hdiff
  have heq : thetaCuspFullSource =ᶠ[nhds 0]
      (fun x : ℝ => thetaCuspSourceTerm x 1 *
        (1 + thetaCuspHigherLikelihoodSpectralResponse
          (thetaCuspLikelihoodCoordinate x))) := by
    have hcont : ContinuousAt thetaCuspLikelihoodCoordinate 0 := by
      unfold thetaCuspLikelihoodCoordinate
      fun_prop
    have hevent : ∀ᶠ x in nhds 0, 0 < thetaCuspLikelihoodCoordinate x :=
      hcont.tendsto (Ioi_mem_nhds hB0)
    filter_upwards [hevent] with x hx
    rw [thetaCuspFullSource_eq_first_mul_one_add_spectralIntegral_of_coordinate_pos hx,
      integral_exp_neg_mul_thetaCuspHigherLikelihoodSpectralMeasure hx]
  have hproductFull := hproduct.congr_of_eventuallyEq heq
  have hderivEq := hproductFull.unique hfullZero
  rw [hM0] at hderivEq
  have hsource0 := thetaCuspSourceTerm_one_zero_pos
  nlinarith

end

end RHTower
