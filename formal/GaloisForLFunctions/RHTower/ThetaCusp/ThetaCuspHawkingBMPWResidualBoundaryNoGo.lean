import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPWResidualRadialRigidity
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPWResidualCuspAsymptotic
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMLiteralCyclicPeierlsPrincipalGrowthDetector
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMLiteralCyclicPeierlsPrincipalWeylSpectrum

/-!
PW-B literal residual boundary no-go.  For any left-half Xi copy, its actual
square-plus-cap cusp boundary has a nonzero dominant normalized limit on some
original radial clock.  Hence the unrenormalized residual cannot vanish at the
cusp on all physical fibres.  This does not settle the ordered CTP/contact
incidence or RH.
-/

open Complex Set Filter Topology
open RHTower RHTower.D4BMModularCore RHTower.D4BMGlobalAngularResponse
open RHTower.D4BMJointSource RHTower.D4BMCapAngularFluxCusp
open RHTower.D4BMPWResidualRadialRigidity
open RHTower.D4BMPWResidualCuspAsymptotic
open RHTower.D4BMLiteralCyclicPeierlsSquareReaderCusp
open RHTower.D4BMMixedParticularCuspFlux
open RHTower.D4BMLiteralCyclicPeierlsCapRadialDefect
open RHTower.D4BMLiteralCyclicPeierlsCapResidualCusp

namespace RHTower.D4BMPWResidualBoundaryLeading
noncomputable section
set_option autoImplicit false

private theorem reader_plus_zero (q : XiZeroCopy) :
    d4BMCompletedEisensteinCuspConstantCoefficient (physicalAngularParameter q) true = 0 := by
  have h := physicalScalar_principal q (![0,1] : D4BMHorizon.Point)
  simp only [D4BMGlobalAngularResponse.principal,d4BMCompletedEisensteinCuspConstantPart,
    d4BMCompletedEisensteinCuspConstantTerm,d4BMCompletedEisensteinCuspConstantMaassFactor,
    mul_one,Matrix.cons_val_one,Matrix.cons_val_zero,Complex.ofReal_one,Complex.one_cpow] at h
  have hm : d4BMCompletedEisensteinCuspConstantCoefficient (physicalAngularParameter q) false =
      reflectedCompletedLambda ((q.1:ℂ)-1) := by
    rw [physicalAngularParameter_eq]
    simp only [d4BMCompletedEisensteinCuspConstantCoefficient,Bool.false_eq_true,ite_false]
    congr 1
    ring
  rw [hm] at h
  exact add_left_cancel (h.trans (add_zero _).symm)

private theorem cap_flux_bool_sum (q : XiZeroCopy) (y : Ioi (0:ℝ)) :
    constantVerticalFlux (center q) (physicalAngularParameter q) y.val =
      ∑ e1 : Bool, ∑ e2 : Bool,
        constantCoefficient (center q) (physicalAngularParameter q) e1 e2 false *
          (y.val : ℂ) ^ (-1 +
            d4BMCompletedEisensteinCuspWeylExponent (center q) e1 +
            d4BMCompletedEisensteinCuspWeylExponent (center q) e2 +
            d4BMCompletedEisensteinCuspWeylExponent (physicalAngularParameter q) false) := by
  rw [constantVerticalFlux_eq_family]
  unfold constantFamily
  rw [d4BM_evaluateDiagonalCuspBoundaryFamily_eq_boolSum]
  simp only [Fintype.sum_bool]
  have hz (e1 e2 : Bool) :
      constantCoefficient (center q) (physicalAngularParameter q) e1 e2 true = 0 := by
    simp [constantCoefficient,reader_plus_zero]
  simp only [hz, zero_mul, zero_add]

private theorem cap_flux_three (q : XiZeroCopy) (y : Ioi (0:ℝ)) :
    constantVerticalFlux (center q) (physicalAngularParameter q) y.val =
      constantCoefficient (center q) (physicalAngularParameter q) true true false *
        (y.val : ℂ) ^ ((3/2 : ℂ) * (q.1 : ℂ)) +
      (constantCoefficient (center q) (physicalAngularParameter q) true false false +
        constantCoefficient (center q) (physicalAngularParameter q) false true false) *
        (y.val : ℂ) ^ (1 - (q.1 : ℂ)/2) +
      constantCoefficient (center q) (physicalAngularParameter q) false false false *
        (y.val : ℂ) ^ (2 - (5/2 : ℂ)*(q.1 : ℂ)) := by
  rw [cap_flux_bool_sum]
  simp only [Fintype.sum_bool]
  have hexp (e1 e2 : Bool) :
      -1 + d4BMCompletedEisensteinCuspWeylExponent (center q) e1 +
        d4BMCompletedEisensteinCuspWeylExponent (center q) e2 +
        d4BMCompletedEisensteinCuspWeylExponent (physicalAngularParameter q) false =
      RHTower.D4BMLiteralCyclicPeierlsPrincipalWeylSpectrum.capWeylExponent q.1 e1 e2 := by
    rw [physicalAngularParameter_eq]
    rfl
  rw [hexp true true, hexp true false, hexp false true, hexp false false]
  rw [RHTower.D4BMLiteralCyclicPeierlsPrincipalWeylSpectrum.capWeylExponent_true_true,
    RHTower.D4BMLiteralCyclicPeierlsPrincipalWeylSpectrum.capWeylExponent_true_false,
    RHTower.D4BMLiteralCyclicPeierlsPrincipalWeylSpectrum.capWeylExponent_false_true,
    RHTower.D4BMLiteralCyclicPeierlsPrincipalWeylSpectrum.capWeylExponent_false_false]
  ring

private theorem tendsto_cpow_zero {w : ℂ} (hw : w.re < 0) :
    Tendsto (fun y : ℝ => (y : ℂ) ^ w) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hpos : 0 < -w.re := neg_pos.mpr hw
  have h : Tendsto (fun y : ℝ => (y ^ (-w.re))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_rpow_atTop hpos)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hy]
  rw [← Real.rpow_neg hy.le]
  congr 1
  ring

private theorem three_weyl_normalized_tendsto (c0 c1 c2 a b d : ℂ)
    (ha : (a-d).re < 0) (hb : (b-d).re < 0) :
    Tendsto (fun y : ℝ => (y : ℂ)^(-d) *
      (c2*(y : ℂ)^a + c1*(y : ℂ)^b + c0*(y : ℂ)^d)) atTop (𝓝 c0) := by
  have h2 := (tendsto_cpow_zero ha).const_mul c2
  have h1 := (tendsto_cpow_zero hb).const_mul c1
  have h : Tendsto (fun y : ℝ =>
      c2*(y : ℂ)^(a-d) + c1*(y : ℂ)^(b-d) + c0) atTop (𝓝 c0) := by
    simpa only [mul_zero, zero_add] using
      (h2.add h1).add (tendsto_const_nhds (x := c0))
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
  have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hp (e : ℂ) : (y : ℂ)^(-d) * (y : ℂ)^e = (y : ℂ)^(e-d) := by
    rw [← Complex.cpow_add _ _ hy0]
    congr 1
    ring
  calc
    c2*(y : ℂ)^(a-d) + c1*(y : ℂ)^(b-d) + c0 =
        c2*((y : ℂ)^(-d)*(y : ℂ)^a) +
          c1*((y : ℂ)^(-d)*(y : ℂ)^b) +
          c0*((y : ℂ)^(-d)*(y : ℂ)^d) := by rw [hp a, hp b, hp d]; simp
    _ = _ := by ring

private theorem cap_normalized_tendsto (q : XiZeroCopy)
    (hleft : (q.1 : ℂ).re < 1/2) :
    Tendsto (fun y : ℝ => (y : ℂ)^(-(2-(5/2 : ℂ)*(q.1 : ℂ))) *
      constantVerticalFlux (center q) (physicalAngularParameter q) y)
      atTop (𝓝 (constantCoefficient (center q) (physicalAngularParameter q)
        false false false)) := by
  have ha : (((3/2 : ℂ)*(q.1 : ℂ)) - (2-(5/2 : ℂ)*(q.1 : ℂ))).re < 0 := by
    norm_num [Complex.sub_re, Complex.mul_re]
    linarith
  have hb : ((1 - (q.1 : ℂ)/2) - (2-(5/2 : ℂ)*(q.1 : ℂ))).re < 0 := by
    norm_num [Complex.sub_re, Complex.mul_re, Complex.div_re]
    linarith
  have h := three_weyl_normalized_tendsto
    (constantCoefficient (center q) (physicalAngularParameter q) false false false)
    (constantCoefficient (center q) (physicalAngularParameter q) true false false +
      constantCoefficient (center q) (physicalAngularParameter q) false true false)
    (constantCoefficient (center q) (physicalAngularParameter q) true true false)
    ((3/2 : ℂ)*(q.1 : ℂ)) (1-(q.1 : ℂ)/2) (2-(5/2 : ℂ)*(q.1 : ℂ)) ha hb
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
  rw [cap_flux_three q ⟨y,hy⟩]

private theorem square_normalized_tendsto (q : XiZeroCopy)
    (hleft : (q.1 : ℂ).re < 1/2) :
    Tendsto (fun y : ℝ => (y : ℂ)^(-(2-(5/2 : ℂ)*(q.1 : ℂ))) *
      squareReaderPrincipalCuspFlux q q y)
      atTop (𝓝 (dominantSquareCoefficient q)) := by
  have hsource :=
    RHTower.D4BMLiteralCyclicPeierlsPrincipalGrowthDetector.principalSquare_left_normalized_tendsto
      q hleft
  have hcoef :
      (reflectedCompletedLambda (2*(q.1 : ℂ)-1)^(2 : ℕ)/2) *
        (readerCoefficient q * readerPower q) = dominantSquareCoefficient q := by
    have hs : d4BMCompletedEisensteinCuspConstantCoefficient
        (D4BMGlobalAngularResponse.center q) false =
        reflectedCompletedLambda (2*(q.1 : ℂ)-1) := by
      simp only [d4BMCompletedEisensteinCuspConstantCoefficient,
        Bool.false_eq_true, ite_false, D4BMGlobalAngularResponse.center]
      congr 1
      ring
    have hr : d4BMCompletedEisensteinCuspConstantCoefficient
        (physicalAngularParameter q) false =
        reflectedCompletedLambda ((q.1 : ℂ)-1) := by
      rw [physicalAngularParameter_eq]
      simp only [d4BMCompletedEisensteinCuspConstantCoefficient,
        Bool.false_eq_true, ite_false]
      congr 1
      ring
    have hp : d4BMCompletedEisensteinCuspWeylExponent
        (physicalAngularParameter q) false = readerPower q := by
      rw [physicalAngularParameter_eq]
      simp only [d4BMCompletedEisensteinCuspWeylExponent,d4BMCuspSign,
        readerPower,Bool.false_eq_true,↓reduceIte]
      ring
    unfold dominantSquareCoefficient readerCoefficient
    rw [hs,hr,hp]
    ring
  have h := hsource.mul_const (readerCoefficient q * readerPower q)
  rw [hcoef] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
  have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hpow : (y : ℂ)^(-(2-(5/2 : ℂ)*(q.1 : ℂ))) *
      (y : ℂ)^(readerPower q-1) = (y : ℂ)^(-(2-2*(q.1 : ℂ))) := by
    rw [← Complex.cpow_add _ _ hy0]
    congr 1
    unfold readerPower
    ring
  change (y : ℂ)^(-(2-2*(q.1 : ℂ))) *
      RHTower.D4BMJointSource.principalSquare q ![0,y] *
      (readerCoefficient q * readerPower q) =
    (y : ℂ)^(-(2-(5/2 : ℂ)*(q.1 : ℂ))) *
      (RHTower.D4BMJointSource.principalSquare q ![0,y] *
        readerCoefficient q * readerPower q *
          (y : ℂ)^(readerPower q-1))
  rw [← hpow]
  ring

def dominantResidualValue (q : XiZeroCopy) (branch side outer : Bool)
    (t : Iio (0 : ℝ)) (base : {z : D4BMHorizon.Point // 0 < z 1}) : ℂ :=
  dominantSquareCoefficient q *
    (cyclicPeierlsSquareCoefficient q q branch side outer 1 t base +
      dominantCapRatio q * cyclicPeierlsCapFluxCoefficient q q branch side outer 1 t base)

private theorem residualPrincipal_normalized_tendsto (q : XiZeroCopy)
    (hleft : (q.1 : ℂ).re < 1/2) (branch side outer : Bool)
    (t : Iio (0 : ℝ)) (base : {z : D4BMHorizon.Point // 0 < z 1}) :
    Tendsto (fun y : ℝ => (y : ℂ)^(-(2-(5/2 : ℂ)*(q.1 : ℂ))) *
      residualPrincipal q q branch side outer 1 t base y) atTop
      (𝓝 (dominantResidualValue q branch side outer t base)) := by
  let A := cyclicPeierlsSquareCoefficient q q branch side outer 1 t base
  let B := cyclicPeierlsCapFluxCoefficient q q branch side outer 1 t base
  have hs := (square_normalized_tendsto q hleft).const_mul A
  have hc := (cap_normalized_tendsto q hleft).const_mul B
  have h := hs.add hc
  have hL : A * dominantSquareCoefficient q +
      B * constantCoefficient (center q) (physicalAngularParameter q) false false false =
      dominantResidualValue q branch side outer t base := by
    rw [cap_dominant_coefficient_eq]
    unfold dominantResidualValue
    dsimp only [A,B]
    ring
  rw [hL] at h
  apply h.congr'
  filter_upwards with y
  dsimp only [residualPrincipal,A,B]
  ring

theorem residualBoundary_normalized_tendsto (q : XiZeroCopy)
    (hleft : (q.1 : ℂ).re < 1/2) (branch side outer : Bool)
    (t : Iio (0 : ℝ)) (base : {z : D4BMHorizon.Point // 0 < z 1}) :
    Tendsto (fun y : ℝ => (y : ℂ)^(-(2-(5/2 : ℂ)*(q.1 : ℂ))) *
      cyclicPeierlsResidualCuspBoundary q q branch side outer 1 t base y)
      atTop (𝓝 (dominantResidualValue q branch side outer t base)) := by
  let w : ℂ := -(2-(5/2 : ℂ)*(q.1 : ℂ))
  have htail := residualCuspBoundary_weighted_sub_principal_tendsto_zero
    q q branch side outer 1 w t base
  have hprincipal := residualPrincipal_normalized_tendsto q hleft branch side outer t base
  have h := htail.add hprincipal
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards with y
  dsimp only [w]
  ring

theorem exists_nonzero_residualBoundary_normalized_limit (q : XiZeroCopy)
    (hleft : (q.1 : ℂ).re < 1/2) (branch side outer : Bool)
    (base : {z : D4BMHorizon.Point // 0 < z 1}) :
    ∃ t : Iio (0 : ℝ), dominantResidualValue q branch side outer t base ≠ 0 ∧
      Tendsto (fun y : ℝ => (y : ℂ)^(-(2-(5/2 : ℂ)*(q.1 : ℂ))) *
        cyclicPeierlsResidualCuspBoundary q q branch side outer 1 t base y)
        atTop (𝓝 (dominantResidualValue q branch side outer t base)) := by
  obtain ⟨t,ht⟩ := exists_dominant_residual_coefficient_ne_zero
    q hleft branch side outer base
  exact ⟨t,ht,residualBoundary_normalized_tendsto q hleft branch side outer t base⟩

/-- The literal square-plus-cap residual cannot be discarded as a zero cusp
boundary on all physical radial clocks when an off-line left Xi copy exists. -/
theorem exists_residualBoundary_not_tendsto_zero (q : XiZeroCopy)
    (hleft : (q.1 : ℂ).re < 1/2) (branch side outer : Bool)
    (base : {z : D4BMHorizon.Point // 0 < z 1}) :
    ∃ t : Iio (0 : ℝ),
      ¬ Tendsto (fun y : ℝ =>
        cyclicPeierlsResidualCuspBoundary q q branch side outer 1 t base y)
        atTop (𝓝 0) := by
  obtain ⟨t,hne,hlim⟩ := exists_nonzero_residualBoundary_normalized_limit
    q hleft branch side outer base
  refine ⟨t,?_⟩
  intro hzero
  have hw : (-(2-(5/2 : ℂ)*(q.1 : ℂ))).re < 0 := by
    norm_num [Complex.neg_re,Complex.sub_re,Complex.mul_re]
    linarith
  have hprod := (tendsto_cpow_zero hw).mul hzero
  exact hne (tendsto_nhds_unique hlim (by simpa only [mul_zero] using hprod))

end
end RHTower.D4BMPWResidualBoundaryLeading
