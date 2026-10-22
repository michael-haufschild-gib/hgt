import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspOddFourGaussianFlow
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaSourceUnconditional

/-!
# Gaussian scale flow and the physical center-weight Green remainder

The exact Gaussian factor of the first theta atom satisfies a scale differential
equation. Its positive Sturm energy does not remain pointwise positive after
inserting the required physical center weight: the full-source Green remainder
is strictly negative at the center. The exact flux identity retains that term.
No sign of the integrated current or of the all-rank signed cone is asserted.
-/

namespace RHTower
noncomputable section

open ThetaCuspOddFour

theorem thetaCuspGaussian_hasDerivAt_scale (q t : ℝ) :
    HasDerivAt (fun s => gaussian s t)
      (-2*(Real.cosh (2*t)-1)*gaussian q t) q := by
  have h := (((hasDerivAt_id q).const_mul (-2)).mul_const
    (Real.cosh (2*t)-1)).exp
  exact h.congr_deriv (by dsimp [gaussian]; ring)

private theorem gaussian_scale_second (q t : ℝ) :
    deriv (deriv (fun s => gaussian s t)) q =
      4*(Real.cosh (2*t)-1)^2*gaussian q t := by
  have h : deriv (fun s => gaussian s t) =
      fun s => -2*(Real.cosh (2*t)-1)*gaussian s t :=
    funext fun s => (thetaCuspGaussian_hasDerivAt_scale s t).deriv
  rw [h]
  rw [((thetaCuspGaussian_hasDerivAt_scale q t).const_mul
    (-2*(Real.cosh (2*t)-1))).deriv]
  ring

/-- Exact scale generator, before taking any reflection-jet order or limit. -/
theorem thetaCuspGaussian_reflection_second_eq_scale (q t : ℝ) :
    -deriv (deriv (gaussian q)) t =
      8*q*gaussian q t + (16*q^2-4*q)*deriv (fun s => gaussian s t) q -
        4*q^2*deriv (deriv (fun s => gaussian s t)) q := by
  have h : deriv (gaussian q) =
      fun y => -4*q*Real.sinh (2*y)*gaussian q y :=
    funext fun y => (gaussian_hasDerivAt q y).deriv
  have hs := (Real.hasDerivAt_sinh (2*t)).comp t ((hasDerivAt_id t).const_mul 2)
  have hd := (hs.const_mul (-4*q)).mul (gaussian_hasDerivAt q t)
  dsimp only [Function.comp_apply, Pi.mul_apply] at hd
  change HasDerivAt (fun y => -4*q*Real.sinh (2*y)*gaussian q y) _ t at hd
  rw [h, hd.deriv, (thetaCuspGaussian_hasDerivAt_scale q t).deriv,
    gaussian_scale_second]
  have hc := Real.cosh_sq_sub_sinh_sq (2*t)
  linear_combination 16*q^2*gaussian q t*hc

/-- The literal first-atom pair uses the same scale flow, with its affine term retained. -/
theorem thetaCuspFirstAtomPair_eq_gaussian_scale_deriv (x t : ℝ) :
    let q := thetaCuspSingleAtomReflectionScale 1 x
    thetaCuspSourceTerm (x+t) 1*thetaCuspSourceTerm (x-t) 1 =
      4*q^2*Real.exp (x-2*q)*
        ((2*q-3)^2*gaussian q t+6*q*deriv (fun s => gaussian s t) q) := by
  dsimp only
  rw [firstAtomPair_eq_affine,
    (thetaCuspGaussian_hasDerivAt_scale _ t).deriv]
  dsimp only [affine, factor]
  ring

/-- A common physical scale for both members of an ordered Gaussian pair. -/
def thetaCuspScalePairKernel (p s r t : ℝ) : ℝ :=
  Real.exp (-Real.exp r*(p*Real.exp (2*t)+s*Real.exp (-2*t)))

private theorem pairKernel_scale_deriv (p s r t : ℝ) :
    HasDerivAt (fun u => thetaCuspScalePairKernel p s u t)
      (-Real.exp r*(p*Real.exp (2*t)+s*Real.exp (-2*t))*
        thetaCuspScalePairKernel p s r t) r := by
  have h := (((Real.hasDerivAt_exp r).neg).mul_const
    (p*Real.exp (2*t)+s*Real.exp (-2*t))).exp
  exact h.congr_deriv (by dsimp [thetaCuspScalePairKernel]; ring)

private theorem pairKernel_scale_second (p s r t : ℝ) :
    deriv (deriv (fun u => thetaCuspScalePairKernel p s u t)) r =
      ((Real.exp r*(p*Real.exp (2*t)+s*Real.exp (-2*t)))^2 -
        Real.exp r*(p*Real.exp (2*t)+s*Real.exp (-2*t)))*
          thetaCuspScalePairKernel p s r t := by
  have he : deriv (fun u => thetaCuspScalePairKernel p s u t) =
      fun u => -Real.exp u*(p*Real.exp (2*t)+s*Real.exp (-2*t))*
        thetaCuspScalePairKernel p s u t :=
    funext fun u => (pairKernel_scale_deriv p s u t).deriv
  rw [he]
  have hd := ((((Real.hasDerivAt_exp r).neg).mul_const
    (p*Real.exp (2*t)+s*Real.exp (-2*t))).mul (pairKernel_scale_deriv p s r t))
  change HasDerivAt (fun u => -Real.exp u*(p*Real.exp (2*t)+s*Real.exp (-2*t))*
    thetaCuspScalePairKernel p s u t) _ r at hd
  rw [hd.deriv]
  dsimp only [Pi.neg_apply]
  ring

/-- The positive-potential scale operator holds for every ordered pair, retaining its product. -/
theorem thetaCuspScalePairKernel_reflection_eq_scale (p s r t : ℝ) :
    -deriv (deriv (thetaCuspScalePairKernel p s r)) t =
      -4*deriv (deriv (fun u => thetaCuspScalePairKernel p s u t)) r +
        16*p*s*Real.exp (2*r)*thetaCuspScalePairKernel p s r t := by
  have he : thetaCuspScalePairKernel p s r =
      thetaPairRadialProfile (p*Real.exp r) (s*Real.exp r) 1 := by
    funext y
    change Real.exp (-Real.exp r*(p*Real.exp (2*y)+s*Real.exp (-2*y))) =
      Real.exp (-(p*Real.exp r*Real.exp (2*y)+s*Real.exp r*Real.exp (-2*y)))*
        Polynomial.eval _ (1 : Polynomial ℝ)
    simp only [Polynomial.eval_one, mul_one]
    congr 1
    ring
  rw [he, thetaPairRadialProfile_second, pairKernel_scale_second]
  rw [← he]
  simp only [thetaPairRadialProfile, thetaPairRadialEvenStep, Polynomial.derivative_one,
    Polynomial.derivative_zero, Polynomial.eval_neg, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_zero, Polynomial.eval_one]
  have hp : Real.exp (2*r) = Real.exp r^2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  change -(- (Real.exp (-(p*Real.exp r*Real.exp (2*t)+s*Real.exp r*Real.exp (-2*t)))*
      (-(4*(((p*Real.exp r*Real.exp (2*t)+s*Real.exp r*Real.exp (-2*t))^2-
        4*(p*Real.exp r*(s*Real.exp r)))*(0-2*0+1)+
        (p*Real.exp r*Real.exp (2*t)+s*Real.exp r*Real.exp (-2*t))*(0-1)))))) = _
  have hk : Real.exp (-(p*Real.exp r*Real.exp (2*t)+s*Real.exp r*Real.exp (-2*t))) =
      thetaCuspScalePairKernel p s r t := by
    unfold thetaCuspScalePairKernel
    congr 1
    ring
  rw [hk, hp]
  ring

/-- Exact ordered integer-source pairing, including its scale derivative and both indices. -/
theorem thetaCuspAtomPair_eq_scaleKernel (n m : ℕ) (x t : ℝ) :
    let p := thetaCuspSingleAtomReflectionScale n x
    let s := thetaCuspSingleAtomReflectionScale m x
    thetaCuspSourceTerm (x+t) n*thetaCuspSourceTerm (x-t) m =
      4*(p*s)*Real.exp x*((4*(p*s)+9)*thetaCuspScalePairKernel p s 0 t +
        6*deriv (fun r => thetaCuspScalePairKernel p s r t) 0) := by
  dsimp only
  rw [congrFun (thetaCuspAtomPair_eq_radialProfile n m x) t,
    (pairKernel_scale_deriv _ _ 0 t).deriv]
  set p := thetaCuspSingleAtomReflectionScale n x
  set s := thetaCuspSingleAtomReflectionScale m x
  change 4*(p*s)*Real.exp x*
      (Real.exp (-(p*Real.exp (2*t)+s*Real.exp (-2*t)))*
        Polynomial.eval (p*Real.exp (2*t)+s*Real.exp (-2*t))
          (thetaPairRadialEvenPolynomial (p*s) 0)) = _
  simp only [thetaPairRadialEvenPolynomial, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    thetaCuspScalePairKernel, Real.exp_zero, neg_mul, one_mul]
  ring

/-- Physical-radius potential of the conjugated Gaussian scale operator. -/
def thetaCuspScaleGreenPotential (r : ℝ) : ℝ :=
  16*Real.pi^2*Real.exp (2*r)

/-- Complete-source test of the first-pair Green operator. Its operator image is not
identified with a native reflection jet; the ordered-pair potentials above differ. -/
def thetaCuspScaleGreenSource (r : ℝ) : ℝ := thetaCuspFullSource (r/2)

def thetaCuspScaleGreenWeight (a r : ℝ) : ℝ := r*Real.sinh (a*r)

def thetaCuspScaleGreenOperator (f : ℝ → ℝ) (r : ℝ) : ℝ :=
  -4*deriv (deriv f) r+thetaCuspScaleGreenPotential r*f r

def thetaCuspScaleGreenFlux (a r : ℝ) : ℝ :=
  4*thetaCuspScaleGreenWeight a r*thetaCuspScaleGreenSource r*
    deriv thetaCuspScaleGreenSource r -
  2*deriv (thetaCuspScaleGreenWeight a) r*thetaCuspScaleGreenSource r^2

def thetaCuspScaleGreenRemainder (a r : ℝ) : ℝ :=
  4*thetaCuspScaleGreenWeight a r*(deriv thetaCuspScaleGreenSource r)^2 +
    (thetaCuspScaleGreenPotential r*thetaCuspScaleGreenWeight a r -
      2*deriv (deriv (thetaCuspScaleGreenWeight a)) r)*thetaCuspScaleGreenSource r^2

private theorem greenSource_smooth : ContDiff ℝ 2 thetaCuspScaleGreenSource := by
  have hf : ContDiff ℝ 2 thetaCuspFullSource :=
    contDiff_thetaCuspFullSource.of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  exact hf.comp (contDiff_id.div_const 2)

/-- Positive unweighted energy, with the boundary flux displayed explicitly. -/
theorem thetaCuspScaleGreen_unweighted_identity (r : ℝ) :
    thetaCuspScaleGreenSource r*thetaCuspScaleGreenOperator thetaCuspScaleGreenSource r +
      deriv (fun y => 4*thetaCuspScaleGreenSource y*deriv thetaCuspScaleGreenSource y) r =
    4*(deriv thetaCuspScaleGreenSource r)^2 +
      thetaCuspScaleGreenPotential r*thetaCuspScaleGreenSource r^2 := by
  have hu := ((greenSource_smooth.differentiable (by norm_num)) r).hasDerivAt
  have hdu := (greenSource_smooth.differentiable_deriv_two r).hasDerivAt
  have hF := (hu.const_mul 4).mul hdu
  change HasDerivAt (fun y => 4*thetaCuspScaleGreenSource y*
    deriv thetaCuspScaleGreenSource y) _ r at hF
  rw [hF.deriv]
  dsimp only [thetaCuspScaleGreenOperator]
  ring

theorem thetaCuspScaleGreen_unweighted_pos (r : ℝ) :
    0 < 4*(deriv thetaCuspScaleGreenSource r)^2 +
      thetaCuspScaleGreenPotential r*thetaCuspScaleGreenSource r^2 := by
  have hsrc : 0 < thetaCuspScaleGreenSource r := thetaCuspFullSource_pos (r/2)
  unfold thetaCuspScaleGreenPotential
  positivity

private theorem greenWeight_deriv (a r : ℝ) :
    HasDerivAt (thetaCuspScaleGreenWeight a)
      (Real.sinh (a*r)+a*r*Real.cosh (a*r)) r := by
  have hs := (Real.hasDerivAt_sinh (a*r)).comp r ((hasDerivAt_id r).const_mul a)
  exact ((hasDerivAt_id r).mul hs).congr_deriv (by dsimp; ring)

private theorem greenWeight_second (a r : ℝ) :
    HasDerivAt (deriv (thetaCuspScaleGreenWeight a))
      (2*a*Real.cosh (a*r)+a^2*r*Real.sinh (a*r)) r := by
  have he : deriv (thetaCuspScaleGreenWeight a) =
      fun y => Real.sinh (a*y)+a*y*Real.cosh (a*y) :=
    funext fun y => (greenWeight_deriv a y).deriv
  rw [he]
  have hs := (Real.hasDerivAt_sinh (a*r)).comp r ((hasDerivAt_id r).const_mul a)
  have hc := (Real.hasDerivAt_cosh (a*r)).comp r ((hasDerivAt_id r).const_mul a)
  exact (hs.add (((hasDerivAt_id r).const_mul a).mul hc)).congr_deriv (by dsimp; ring)

/-- Exact Green identity with the actual complete theta source and physical weight. -/
theorem thetaCuspScaleGreen_identity (a r : ℝ) :
    thetaCuspScaleGreenWeight a r*thetaCuspScaleGreenSource r*
        thetaCuspScaleGreenOperator thetaCuspScaleGreenSource r +
      deriv (thetaCuspScaleGreenFlux a) r = thetaCuspScaleGreenRemainder a r := by
  have hu := ((greenSource_smooth.differentiable (by norm_num)) r).hasDerivAt
  have hdu := (greenSource_smooth.differentiable_deriv_two r).hasDerivAt
  have hw := (greenWeight_deriv a r).differentiableAt.hasDerivAt
  have hdw := (greenWeight_second a r).differentiableAt.hasDerivAt
  have hF := (((hw.const_mul 4).mul hu).mul hdu).sub
    ((hdw.const_mul 2).mul (hu.pow 2))
  change HasDerivAt (thetaCuspScaleGreenFlux a) _ r at hF
  rw [hF.deriv]
  dsimp only [thetaCuspScaleGreenOperator, thetaCuspScaleGreenRemainder,
    Pi.mul_apply, Pi.pow_apply]
  ring

/-- The physical flux has its required zero center endpoint. -/
theorem thetaCuspScaleGreenFlux_zero (a : ℝ) : thetaCuspScaleGreenFlux a 0 = 0 := by
  simp [thetaCuspScaleGreenFlux, thetaCuspScaleGreenWeight, (greenWeight_deriv a 0).deriv]

/-- The exact potential remainder is negative at the center for every positive aperture. -/
theorem thetaCuspScaleGreenRemainder_zero (a : ℝ) :
    thetaCuspScaleGreenRemainder a 0 = -4*a*thetaCuspFullSource 0^2 := by
  rw [thetaCuspScaleGreenRemainder, (greenWeight_second a 0).deriv]
  simp only [thetaCuspScaleGreenWeight, thetaCuspScaleGreenSource,
    mul_zero, Real.sinh_zero, Real.cosh_zero, zero_mul, zero_div, mul_one, add_zero]
  ring

theorem thetaCuspScaleGreenRemainder_zero_neg {a : ℝ} (ha : 0 < a) :
    thetaCuspScaleGreenRemainder a 0 < 0 := by
  rw [thetaCuspScaleGreenRemainder_zero]
  have hpos := sq_pos_of_pos (thetaCuspFullSource_pos 0)
  nlinarith

/-- The sign defect occupies a positive-radius interval, not merely its endpoint. -/
theorem thetaCuspScaleGreenRemainder_neg_near_center {a : ℝ} (ha : 0 < a) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 < r → r < δ →
      thetaCuspScaleGreenRemainder a r < 0 := by
  have hu := greenSource_smooth.continuous
  have hdu := greenSource_smooth.continuous_deriv (by norm_num)
  have he : (fun r => deriv (deriv (thetaCuspScaleGreenWeight a)) r) =
      fun r => 2*a*Real.cosh (a*r)+a^2*r*Real.sinh (a*r) :=
    funext fun r => (greenWeight_second a r).deriv
  have hc : Continuous (thetaCuspScaleGreenRemainder a) := by
    unfold thetaCuspScaleGreenRemainder
    simp_rw [he]
    unfold thetaCuspScaleGreenPotential thetaCuspScaleGreenWeight
    fun_prop
  have hev := hc.continuousAt.tendsto.eventually_lt_const
    (thetaCuspScaleGreenRemainder_zero_neg ha)
  obtain ⟨δ, hδ, hneg⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨δ, hδ, fun r hr hrδ => hneg ?_⟩
  simpa only [Real.dist_eq, sub_zero, abs_of_pos hr] using hrδ

end
end RHTower
