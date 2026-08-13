import GaloisForLFunctions.RHTower.XiHorizontalCollisionWardGreenExteriorSourceCarrier

/-!
# Cayley--Abel source landing of the transverse exterior Green factor

The inverse transverse coordinate in the Ward--Green exterior carrier is the Abel boundary value
of finite polynomials in the source-horizontal Cayley phase.  This removes the apparent
post-divisor insertion of `1 / Im z`: away from the critical line it is the elementary Cayley
identity

`1 / Im z = 2 i (1-u) / (1+u)`,

where `u=realCayley(2 Re rho-1)`.  On the critical line the adjacent exterior determinant already
vanishes, so the boundary pole is removable after exteriorization.  Both adjacent orientations
therefore arise as iterated limits of finite Cayley source-orbit polynomials.

This closes normalization provenance.  It does not supply the remaining prime--Gamma bound on the
dephased exterior trace.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Finite source-Cayley polynomial approximating the transverse Green multiplier. -/
def sourceCayleyAbelGreenPolynomial (R : ℝ) (K : ℕ) (x : ℝ) : ℂ :=
  2 * I * (1 - GaloisForLFunctions.HTGeometry.realCayley x) *
    ∑ k ∈ Finset.range K,
      (-((R : ℂ) * GaloisForLFunctions.HTGeometry.realCayley x)) ^ k

/-- Abel-resolvent form of the same source-Cayley orbit. -/
def sourceCayleyAbelGreenMultiplier (R x : ℝ) : ℂ :=
  2 * I * (1 - GaloisForLFunctions.HTGeometry.realCayley x) /
    (1 + (R : ℂ) * GaloisForLFunctions.HTGeometry.realCayley x)

/-- At every strict Abel radius, finite Cayley polynomials converge to the resolvent multiplier. -/
theorem tendsto_sourceCayleyAbelGreenPolynomial
    {R : ℝ} (hR : |R| < 1) (x : ℝ) :
    Tendsto (fun K : ℕ => sourceCayleyAbelGreenPolynomial R K x)
      atTop (nhds (sourceCayleyAbelGreenMultiplier R x)) := by
  let u : ℂ := GaloisForLFunctions.HTGeometry.realCayley x
  have hu : ‖u‖ = 1 := GaloisForLFunctions.HTGeometry.norm_realCayley x
  have hratio : ‖-((R : ℂ) * u)‖ < 1 := by
    rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, hu, mul_one]
    exact hR
  have hgeom := (hasSum_geometric_of_norm_lt_one hratio).tendsto_sum_nat
  have hmul := tendsto_const_nhds.mul hgeom
  convert hmul using 1
  · funext K
    simp only [sourceCayleyAbelGreenPolynomial, u]
  · rw [sourceCayleyAbelGreenMultiplier]
    change 2 * I * (1 - u) * (1 - -((R : ℂ) * u))⁻¹ =
      2 * I * (1 - u) / (1 + (R : ℂ) * u)
    rw [div_eq_mul_inv]
    congr 2
    ring

/-- The Cayley denominator at the Abel boundary is nonzero away from the reflection fixed point. -/
theorem one_add_realCayley_ne_zero {x : ℝ} (hx : x ≠ 0) :
    1 + GaloisForLFunctions.HTGeometry.realCayley x ≠ 0 := by
  have hxI : (x : ℂ) + I ≠ 0 :=
    GaloisForLFunctions.HTGeometry.real_add_I_ne_zero x
  have heq :
      1 + GaloisForLFunctions.HTGeometry.realCayley x =
        (2 * (x : ℂ)) / ((x : ℂ) + I) := by
    unfold GaloisForLFunctions.HTGeometry.realCayley
    field_simp [hxI]
    ring
  rw [heq]
  exact div_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr hx)) hxI

/-- Boundary Cayley identity: the Abel multiplier is exactly the inverse transverse coordinate. -/
theorem sourceCayleyAbelGreenMultiplier_one_eq
    {x : ℝ} (hx : x ≠ 0) :
    sourceCayleyAbelGreenMultiplier 1 x = ((-2 / x : ℝ) : ℂ) := by
  have hxI : (x : ℂ) + I ≠ 0 :=
    GaloisForLFunctions.HTGeometry.real_add_I_ne_zero x
  have hsum := one_add_realCayley_ne_zero hx
  rw [sourceCayleyAbelGreenMultiplier]
  norm_num only [ofReal_one, one_mul]
  unfold GaloisForLFunctions.HTGeometry.realCayley
  push_cast
  field_simp [hxI, hsum, ofReal_ne_zero.mpr hx]
  ring_nf
  norm_num [Complex.I_sq]

/-- An adjacent exterior determinant vanishes at the critical-line kernel before normalization. -/
theorem adjacentCriticalFeatureEvaluationDet_eq_zero_of_im_eq_zero
    (t : ℝ) (z : ℂ) (hz : |z.im| < 1 / 2) (hy : z.im = 0) :
    adjacentCriticalFeatureEvaluationDet t z hz = 0 := by
  rw [adjacentCriticalFeatureEvaluationDet_eq, hy]
  norm_num

/-- Abel multiplier specialized to the source-horizontal rate of one Xi divisor class. -/
def xiExteriorCayleyAbelGreenMultiplier (R : ℝ) (rho : XiDivisorSupport) : ℂ :=
  sourceCayleyAbelGreenMultiplier R (2 * (rho : ℂ).re - 1)

/-- Finite polynomial version of the same divisor-class multiplier. -/
def xiExteriorCayleyAbelGreenPolynomial
    (R : ℝ) (K : ℕ) (rho : XiDivisorSupport) : ℂ :=
  sourceCayleyAbelGreenPolynomial R K (2 * (rho : ℂ).re - 1)

/-- The boundary multiplier is the existing totalized inverse transverse coordinate off line. -/
theorem xiExteriorCayleyAbelGreenMultiplier_one_eq_inv_im
    (rho : XiDivisorSupport) (hoff : (rho : ℂ).re ≠ 1 / 2) :
    xiExteriorCayleyAbelGreenMultiplier 1 rho =
      ((((xiSpectralPointSupport rho).im)⁻¹ : ℝ) : ℂ) := by
  have hx : 2 * (rho : ℂ).re - 1 ≠ 0 := by
    intro h
    apply hoff
    linarith
  rw [xiExteriorCayleyAbelGreenMultiplier,
    sourceCayleyAbelGreenMultiplier_one_eq hx,
    xiSpectralPointSupport_im]
  push_cast
  field_simp [hx]
  ring

/-- Abel-normalized forward adjacent exterior coefficient. -/
def xiExteriorCayleyAbelPlusCoefficient
    (R : ℝ) (rho : XiDivisorSupport) : ℂ :=
  let z := xiSpectralPointSupport rho
  let hz : |z.im| < 1 / 2 :=
    abs_xiSpectralPointSupport_im_lt_half_exteriorCarrier rho
  xiExteriorCayleyAbelGreenMultiplier R rho *
    adjacentCriticalFeatureEvaluationDet (xiExteriorReporterCenter rho) z hz

/-- Abel-normalized backward adjacent exterior coefficient. -/
def xiExteriorCayleyAbelMinusCoefficient
    (R : ℝ) (rho : XiDivisorSupport) : ℂ :=
  let z := xiSpectralPointSupport rho
  let hz : |z.im| < 1 / 2 :=
    abs_xiSpectralPointSupport_im_lt_half_exteriorCarrier rho
  xiExteriorCayleyAbelGreenMultiplier R rho *
    adjacentCriticalFeatureEvaluationDet (xiExteriorReporterCenter rho - 1) z hz

/-- On an off-line class, the forward Abel boundary value is the existing Ward--Green exterior
coefficient exactly. -/
theorem xiExteriorCayleyAbelPlusCoefficient_one_eq_of_offLine
    (rho : XiDivisorSupport) (hoff : (rho : ℂ).re ≠ 1 / 2) :
    xiExteriorCayleyAbelPlusCoefficient 1 rho =
      xiWardGreenExteriorPlusCoefficient rho := by
  rw [xiExteriorCayleyAbelPlusCoefficient,
    xiWardGreenExteriorPlusCoefficient,
    xiExteriorCayleyAbelGreenMultiplier_one_eq_inv_im rho hoff]

/-- The same exact boundary identification holds for the backward adjacent orientation. -/
theorem xiExteriorCayleyAbelMinusCoefficient_one_eq_of_offLine
    (rho : XiDivisorSupport) (hoff : (rho : ℂ).re ≠ 1 / 2) :
    xiExteriorCayleyAbelMinusCoefficient 1 rho =
      xiWardGreenExteriorMinusCoefficient rho := by
  rw [xiExteriorCayleyAbelMinusCoefficient,
    xiWardGreenExteriorMinusCoefficient,
    xiExteriorCayleyAbelGreenMultiplier_one_eq_inv_im rho hoff]

/-- Exteriorization removes the critical-line Abel pole in the forward channel. -/
theorem xiExteriorCayleyAbelPlusCoefficient_eq_zero_of_onLine
    (R : ℝ) (rho : XiDivisorSupport) (hline : (rho : ℂ).re = 1 / 2) :
    xiExteriorCayleyAbelPlusCoefficient R rho = 0 := by
  have hy : (xiSpectralPointSupport rho).im = 0 :=
    (xiSpectralPointSupport_im_eq_zero_iff rho).2 hline
  rw [xiExteriorCayleyAbelPlusCoefficient,
    adjacentCriticalFeatureEvaluationDet_eq_zero_of_im_eq_zero _ _
      (abs_xiSpectralPointSupport_im_lt_half_exteriorCarrier rho) hy,
    mul_zero]

/-- Exteriorization removes the critical-line Abel pole in the backward channel as well. -/
theorem xiExteriorCayleyAbelMinusCoefficient_eq_zero_of_onLine
    (R : ℝ) (rho : XiDivisorSupport) (hline : (rho : ℂ).re = 1 / 2) :
    xiExteriorCayleyAbelMinusCoefficient R rho = 0 := by
  have hy : (xiSpectralPointSupport rho).im = 0 :=
    (xiSpectralPointSupport_im_eq_zero_iff rho).2 hline
  rw [xiExteriorCayleyAbelMinusCoefficient,
    adjacentCriticalFeatureEvaluationDet_eq_zero_of_im_eq_zero _ _
      (abs_xiSpectralPointSupport_im_lt_half_exteriorCarrier rho) hy,
    mul_zero]

/-- Totalized forward boundary value agrees with the Ward--Green carrier on every divisor class. -/
theorem xiExteriorCayleyAbelPlusCoefficient_one_eq
    (rho : XiDivisorSupport) :
    xiExteriorCayleyAbelPlusCoefficient 1 rho =
      xiWardGreenExteriorPlusCoefficient rho := by
  by_cases hline : (rho : ℂ).re = 1 / 2
  · rw [xiExteriorCayleyAbelPlusCoefficient_eq_zero_of_onLine 1 rho hline]
    have hy : (xiSpectralPointSupport rho).im = 0 :=
      (xiSpectralPointSupport_im_eq_zero_iff rho).2 hline
    rw [xiWardGreenExteriorPlusCoefficient, hy]
    norm_num
  · exact xiExteriorCayleyAbelPlusCoefficient_one_eq_of_offLine rho hline

/-- Totalized backward boundary value agrees with the second Ward--Green carrier everywhere. -/
theorem xiExteriorCayleyAbelMinusCoefficient_one_eq
    (rho : XiDivisorSupport) :
    xiExteriorCayleyAbelMinusCoefficient 1 rho =
      xiWardGreenExteriorMinusCoefficient rho := by
  by_cases hline : (rho : ℂ).re = 1 / 2
  · rw [xiExteriorCayleyAbelMinusCoefficient_eq_zero_of_onLine 1 rho hline]
    have hy : (xiSpectralPointSupport rho).im = 0 :=
      (xiSpectralPointSupport_im_eq_zero_iff rho).2 hline
    rw [xiWardGreenExteriorMinusCoefficient, hy]
    norm_num
  · exact xiExteriorCayleyAbelMinusCoefficient_one_eq_of_offLine rho hline

/-- Finite Cayley polynomials converge to the forward Abel exterior coefficient at fixed radius. -/
theorem tendsto_xiExteriorCayleyAbelPolynomial_mul_plus
    {R : ℝ} (hR : |R| < 1) (rho : XiDivisorSupport) :
    Tendsto
      (fun K : ℕ =>
        xiExteriorCayleyAbelGreenPolynomial R K rho *
          adjacentCriticalFeatureEvaluationDet (xiExteriorReporterCenter rho)
            (xiSpectralPointSupport rho)
            (abs_xiSpectralPointSupport_im_lt_half_exteriorCarrier rho))
      atTop (nhds (xiExteriorCayleyAbelPlusCoefficient R rho)) := by
  simpa only [xiExteriorCayleyAbelGreenPolynomial,
    xiExteriorCayleyAbelPlusCoefficient,
    xiExteriorCayleyAbelGreenMultiplier] using
    (tendsto_sourceCayleyAbelGreenPolynomial hR
      (2 * (rho : ℂ).re - 1)).mul_const
        (adjacentCriticalFeatureEvaluationDet (xiExteriorReporterCenter rho)
          (xiSpectralPointSupport rho)
          (abs_xiSpectralPointSupport_im_lt_half_exteriorCarrier rho))

/-- Finite Cayley polynomials converge to the backward Abel exterior coefficient at fixed radius. -/
theorem tendsto_xiExteriorCayleyAbelPolynomial_mul_minus
    {R : ℝ} (hR : |R| < 1) (rho : XiDivisorSupport) :
    Tendsto
      (fun K : ℕ =>
        xiExteriorCayleyAbelGreenPolynomial R K rho *
          adjacentCriticalFeatureEvaluationDet (xiExteriorReporterCenter rho - 1)
            (xiSpectralPointSupport rho)
            (abs_xiSpectralPointSupport_im_lt_half_exteriorCarrier rho))
      atTop (nhds (xiExteriorCayleyAbelMinusCoefficient R rho)) := by
  simpa only [xiExteriorCayleyAbelGreenPolynomial,
    xiExteriorCayleyAbelMinusCoefficient,
    xiExteriorCayleyAbelGreenMultiplier] using
    (tendsto_sourceCayleyAbelGreenPolynomial hR
      (2 * (rho : ℂ).re - 1)).mul_const
        (adjacentCriticalFeatureEvaluationDet (xiExteriorReporterCenter rho - 1)
          (xiSpectralPointSupport rho)
          (abs_xiSpectralPointSupport_im_lt_half_exteriorCarrier rho))

/-- The forward Abel family has the exact Ward--Green coefficient as its removable boundary
value. -/
theorem tendsto_xiExteriorCayleyAbelPlusCoefficient_one
    (rho : XiDivisorSupport) :
    Tendsto (fun R : ℝ => xiExteriorCayleyAbelPlusCoefficient R rho)
      (nhdsWithin 1 (Set.Iio 1))
      (nhds (xiWardGreenExteriorPlusCoefficient rho)) := by
  by_cases hline : (rho : ℂ).re = 1 / 2
  · have hzero : (fun R : ℝ => xiExteriorCayleyAbelPlusCoefficient R rho) =
        fun _ => 0 := by
      funext R
      exact xiExteriorCayleyAbelPlusCoefficient_eq_zero_of_onLine R rho hline
    rw [hzero]
    have htarget := xiExteriorCayleyAbelPlusCoefficient_one_eq rho
    rw [xiExteriorCayleyAbelPlusCoefficient_eq_zero_of_onLine 1 rho hline] at htarget
    rw [← htarget]
    exact tendsto_const_nhds
  · have hden :
        1 + ((1 : ℝ) : ℂ) *
          GaloisForLFunctions.HTGeometry.realCayley (2 * (rho : ℂ).re - 1) ≠ 0 := by
      norm_num only [ofReal_one, one_mul]
      apply one_add_realCayley_ne_zero
      intro hx
      apply hline
      linarith
    have hcont : ContinuousAt
        (fun R : ℝ => xiExteriorCayleyAbelPlusCoefficient R rho) 1 := by
      rw [xiExteriorCayleyAbelPlusCoefficient,
        xiExteriorCayleyAbelGreenMultiplier,
        xiExteriorCayleyAbelGreenMultiplier]
      fun_prop
    rw [← xiExteriorCayleyAbelPlusCoefficient_one_eq rho]
    exact hcont.tendsto.mono_left inf_le_left

/-- The backward Abel family has the second Ward--Green coefficient as its removable boundary
value. -/
theorem tendsto_xiExteriorCayleyAbelMinusCoefficient_one
    (rho : XiDivisorSupport) :
    Tendsto (fun R : ℝ => xiExteriorCayleyAbelMinusCoefficient R rho)
      (nhdsWithin 1 (Set.Iio 1))
      (nhds (xiWardGreenExteriorMinusCoefficient rho)) := by
  by_cases hline : (rho : ℂ).re = 1 / 2
  · have hzero : (fun R : ℝ => xiExteriorCayleyAbelMinusCoefficient R rho) =
        fun _ => 0 := by
      funext R
      exact xiExteriorCayleyAbelMinusCoefficient_eq_zero_of_onLine R rho hline
    rw [hzero]
    have htarget := xiExteriorCayleyAbelMinusCoefficient_one_eq rho
    rw [xiExteriorCayleyAbelMinusCoefficient_eq_zero_of_onLine 1 rho hline] at htarget
    rw [← htarget]
    exact tendsto_const_nhds
  · have hden :
        1 + ((1 : ℝ) : ℂ) *
          GaloisForLFunctions.HTGeometry.realCayley (2 * (rho : ℂ).re - 1) ≠ 0 := by
      norm_num only [ofReal_one, one_mul]
      apply one_add_realCayley_ne_zero
      intro hx
      apply hline
      linarith
    have hcont : ContinuousAt
        (fun R : ℝ => xiExteriorCayleyAbelMinusCoefficient R rho) 1 := by
      rw [xiExteriorCayleyAbelMinusCoefficient,
        xiExteriorCayleyAbelGreenMultiplier,
        xiExteriorCayleyAbelGreenMultiplier]
      fun_prop
    rw [← xiExteriorCayleyAbelMinusCoefficient_one_eq rho]
    exact hcont.tendsto.mono_left inf_le_left

end

end RHTower
