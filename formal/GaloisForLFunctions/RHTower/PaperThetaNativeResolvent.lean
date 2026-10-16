import GaloisForLFunctions.RHTower.PaperThetaNativeUniqueness

/-! # Whole-domain native theta resolvents

An arbitrary continuous BV forcing has one native solution at each regular
parameter. Every nonzero imaginary parameter is regular unconditionally,
by the positive real theta integral. Endpoint traces and BV admission are
part of the constructed solution, not premises on its spectral coordinates.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex

namespace RHTower.PaperThetaEndpoint
open HedenmalmThetaSource HedenmalmQuantile

theorem flatConnection_imaginary_ne_zero (r : ℝ) :
    flatConnection (I*(r : ℂ)) ≠ 0 := by
  let F : ℝ → ℝ := fun x => thetaSource.normalized x*Real.exp (-r*x)
  have hi : Integrable F := by
    simpa only [norm_flatCharDensity, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, add_zero]
      using (integrable_flatCharDensity_all (I*(r : ℂ))).norm
  have hc : Continuous F := by
    dsimp [F]
    exact continuous_normalized_theta.mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_id))
  have hp : ∀ x, 0 < F x := fun x =>
    mul_pos (thetaSource.normalized_pos x) (Real.exp_pos _)
  have hpos : 0 < ∫ x, F x :=
    integral_pos_of_integrable_nonneg_nonzero hc hi (fun x => (hp x).le) (hp 0).ne'
  have he : flatConnection (I*(r : ℂ)) = (∫ x, F x : ℝ) := by
    rw [flatConnection]
    simp_rw [flatCharDensity, sourceChar_imaginary, ← Complex.ofReal_mul]
    exact integral_ofReal
  rw [he]
  exact Complex.ofReal_ne_zero.mpr hpos.ne'

theorem XiC_imaginary_ne_zero (r : ℝ) : XiC (I*(r : ℂ)) ≠ 0 := by
  intro h
  apply flatConnection_imaginary_ne_zero r
  rw [flatConnection_eq_all, h, zero_div]

abbrev ThetaRegularParameter := {z : ℂ // z ≠ 0 ∧ XiC z ≠ 0}

def thetaImaginaryRegularParameter (r : ℝˣ) : ThetaRegularParameter :=
  ⟨I*((r : ℝ) : ℂ), mul_ne_zero I_ne_zero (Complex.ofReal_ne_zero.mpr r.ne_zero),
    XiC_imaginary_ne_zero r⟩

def nativeResolventTrace (z : ThetaRegularParameter) (g : ThetaContinuousBV) : ℂ :=
  -forcedMoment z g / (z.val*flatConnection z)

theorem regular_connection_ne_zero (z : ThetaRegularParameter) : flatConnection z ≠ 0 := by
  rw [flatConnection_eq_all]
  exact div_ne_zero z.property.2 (Complex.ofReal_ne_zero.mpr thetaSource.mass_ne_zero)

def nativeThetaResolvent (z : ThetaRegularParameter) (g : ThetaContinuousBV) : ThetaNativeDomain :=
  nativeZeroMomentSolution z (g.affine (z.val*nativeResolventTrace z g) 1)
    (nativeResolventTrace z g) (by
      rw [forcedMoment_affine]
      simp only [one_mul]
      dsimp [nativeResolventTrace]
      field_simp [z.property.1, regular_connection_ne_zero z]
      ring)

theorem nativeThetaResolvent_trace (z : ThetaRegularParameter) (g : ThetaContinuousBV) :
    thetaTailTrace (nativeThetaResolvent z g) = nativeResolventTrace z g :=
  nativeZeroMomentSolution_trace _ _ _ _

/-- A pointwise inhomogeneous equation on the entire native BV source domain. -/
theorem nativeThetaResolvent_equation (z : ThetaRegularParameter) (g : ThetaContinuousBV)
    (x : ℝ) : thetaSpatialAction (nativeThetaResolvent z g) x-
      z.val*nativeThetaResolvent z g x = g x := by
  rw [nativeThetaResolvent, nativeZeroMomentSolution_equation]
  change (z.val*nativeResolventTrace z g+1*g x)-z.val*nativeResolventTrace z g = g x
  ring

theorem nativeThetaResolvent_existsUnique (z : ThetaRegularParameter) (g : ThetaContinuousBV) :
    ∃! f : ThetaNativeDomain, ∀ x,
      thetaSpatialAction f x-z.val*f x = g x := by
  refine ⟨nativeThetaResolvent z g, nativeThetaResolvent_equation z g, fun f hf => ?_⟩
  exact nativeSolution_unique z.property.1 z.property.2 f (nativeThetaResolvent z g)
    (fun x => (hf x).trans (nativeThetaResolvent_equation z g x).symm)

/-- Unconditional, without finite-mode membership or an unproved zero-free premise. -/
theorem nativeThetaImaginaryEquation_existsUnique (r : ℝˣ) (g : ThetaContinuousBV) :
    ∃! f : ThetaNativeDomain, ∀ x,
      thetaSpatialAction f x-(I*((r : ℝ) : ℂ))*f x = g x :=
  nativeThetaResolvent_existsUnique (thetaImaginaryRegularParameter r) g

end RHTower.PaperThetaEndpoint
