import GaloisForLFunctions.RHTower.PaperThetaForcedTail

/-! # Exact connection cancellation for whole native forcing profiles

The full theta moment is cancelled before division by the source. This joins
two individually admitted BV tails and gives a literal two-ended domain.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex

namespace RHTower.PaperThetaEndpoint
open HedenmalmThetaSource HedenmalmQuantile

theorem forcedMoment_affine (z : ℂ) (g : ThetaContinuousBV) (a b : ℂ) :
    forcedMoment z (g.affine a b) = a*flatConnection z+b*forcedMoment z g := by
  have he : (fun x => flatCharDensity z x*(g.affine a b) x) =
      fun x => a*flatCharDensity z x+b*(flatCharDensity z x*g x) := by
    funext x
    change _*(a+b*g x) = _
    ring
  rw [forcedMoment, he, integral_add ((integrable_flatCharDensity_all z).const_mul a)
    ((integrable_forcedDensity z g).const_mul b), integral_const_mul, integral_const_mul]
  rfl

/-- The exact connection coefficient is the sole discrepancy between the two tails. -/
theorem forcedRightTail_reflection {z : ℂ} {g : ThetaContinuousBV}
    (hzero : forcedMoment z g = 0) (x : ℝ) :
    forcedRightTail z g x = -forcedRightTail (-z) g.reflect (-x) := by
  have hI : (∫ y in Iic x, flatCharDensity z y*g y) =
      ∫ y in Ioi (-x), flatCharDensity (-z) y*g.reflect y := by
    rw [← integral_comp_neg_Iic x (fun y => flatCharDensity (-z) y*g.reflect y)]
    apply integral_congr_ae
    filter_upwards [] with y
    rw [flatCharDensity_reflection]
    change _ = _*g (-(-y))
    rw [neg_neg]
  have he : Complex.exp (-(I*(-z))*((-x : ℝ) : ℂ)) =
      Complex.exp (-(I*z)*(x : ℂ)) := by congr 1; push_cast; ring
  rw [forcedRightTail, forcedTail_integral_split, hzero, zero_sub, hI,
    forcedRightTail, he, normalized_reflection]
  ring

theorem boundedVariationOn_forcedRightTail {z : ℂ} {g : ThetaContinuousBV}
    (hzero : forcedMoment z g = 0) :
    BoundedVariationOn (forcedRightTail z g) univ := by
  have hl : BoundedVariationOn (forcedRightTail z g) (Iic (0 : ℝ)) := by
    have hb := boundedVariationOn_forcedRightTail_ray (-z) g.reflect 0
    have hr : BoundedVariationOn (fun x => forcedRightTail (-z) g.reflect (-x)) (Iic (0 : ℝ)) :=
      ne_top_of_le_ne_top hb (eVariationOn.comp_le_of_antitoneOn _
        (s := Ici (0 : ℝ)) (t := Iic (0 : ℝ)) (fun x : ℝ => -x)
        (fun _ _ _ _ h => neg_le_neg h) (fun x hx => neg_nonneg.mpr hx))
    have hn := boundedVariation_affine hr 0 (-1)
    have he : forcedRightTail z g = fun x => 0+(-1)*forcedRightTail (-z) g.reflect (-x) := by
      funext x
      simpa using forcedRightTail_reflection hzero x
    rwa [he]
  have hr := boundedVariationOn_forcedRightTail_ray z g 0
  have hs : IsGreatest (Iic (0 : ℝ)) 0 := ⟨le_rfl, fun _ h => h⟩
  have ht : IsLeast (Ici (0 : ℝ)) 0 := ⟨le_rfl, fun _ h => h⟩
  change eVariationOn (forcedRightTail z g) univ ≠ ⊤
  rw [← Iic_union_Ici (0 : ℝ), eVariationOn.union _ hs ht]
  exact ENNReal.add_ne_top.mpr ⟨hl, hr⟩

theorem tendsto_forcedRightTail_atBot {z : ℂ} {g : ThetaContinuousBV}
    (hzero : forcedMoment z g = 0) :
    Tendsto (forcedRightTail z g) atBot (𝓝 0) := by
  have h := ((tendsto_forcedRightTail_atTop (-z) g.reflect).comp tendsto_neg_atBot_atTop).neg
  simpa only [neg_zero, ← forcedRightTail_reflection hzero] using h

/-- The literal differential domain, with its actual common endpoint trace. -/
structure ThetaNativeDomain extends ThetaContinuousBV where
  differentiable : Differentiable ℝ toFun
  leftTrace : Tendsto toFun atBot (𝓝 (thetaTailTrace toFun))

instance : CoeFun ThetaNativeDomain (fun _ => ℝ → ℂ) :=
  ⟨fun f => f.toThetaContinuousBV.toFun⟩

theorem ThetaNativeDomain.rightTrace (f : ThetaNativeDomain) :
    Tendsto f atTop (𝓝 (thetaTailTrace f)) := f.bv.tendsto_atTop_limUnder

@[ext] theorem ThetaContinuousBV.ext {f g : ThetaContinuousBV}
    (h : ∀ x, f x = g x) : f = g := by
  have he : f.toFun = g.toFun := funext h
  cases f
  cases g
  cases he
  rfl

@[ext] theorem ThetaNativeDomain.ext {f g : ThetaNativeDomain}
    (h : ∀ x, f x = g x) : f = g := by
  have he : f.toThetaContinuousBV = g.toThetaContinuousBV := ThetaContinuousBV.ext h
  cases f
  cases g
  cases he
  rfl

def nativeZeroMomentSolution (z : ℂ) (g : ThetaContinuousBV) (c : ℂ)
    (hzero : forcedMoment z g = 0) : ThetaNativeDomain where
  toFun x := c+I*forcedRightTail z g x
  continuous := continuous_const.add (continuous_const.mul (continuous_forcedRightTail z g))
  bv := boundedVariation_affine (boundedVariationOn_forcedRightTail hzero) c I
  differentiable x := ((hasDerivAt_forcedRightTail z g x).const_mul I).const_add c |>.differentiableAt
  leftTrace := by
    have ht := ((tendsto_forcedRightTail_atTop z g).const_mul I).const_add c
    have hb := ((tendsto_forcedRightTail_atBot hzero).const_mul I).const_add c
    simp only [mul_zero, add_zero] at ht hb
    change Tendsto _ atBot (𝓝 (limUnder atTop _))
    rw [ht.limUnder_eq]
    exact hb

theorem nativeZeroMomentSolution_trace (z : ℂ) (g : ThetaContinuousBV) (c : ℂ)
    (hzero : forcedMoment z g = 0) :
    thetaTailTrace (nativeZeroMomentSolution z g c hzero) = c := by
  have ht := ((tendsto_forcedRightTail_atTop z g).const_mul I).const_add c
  simpa only [mul_zero, add_zero] using ht.limUnder_eq

theorem nativeZeroMomentSolution_equation (z : ℂ) (g : ThetaContinuousBV) (c : ℂ)
    (hzero : forcedMoment z g = 0) (x : ℝ) :
    thetaSpatialAction (nativeZeroMomentSolution z g c hzero) x-
      z*nativeZeroMomentSolution z g c hzero x = g x-z*c := by
  have hd := (((hasDerivAt_forcedRightTail z g x).const_mul I).const_add c).deriv
  change deriv (nativeZeroMomentSolution z g c hzero) x = _ at hd
  rw [thetaSpatialAction, hd, nativeZeroMomentSolution_trace]
  change I*(_+sourceLogDerivative x*((c+I*forcedRightTail z g x)-c))-
    z*(c+I*forcedRightTail z g x) = _
  ring_nf
  simp [Complex.I_sq]

/-- A complete native parametrix, paid on every original continuous BV forcing. -/
def nativeThetaParametrix (z : ℂ) (g : ThetaContinuousBV) : ThetaNativeDomain :=
  nativeZeroMomentSolution z
    (g.affine (-z*forcedMoment z g) (z*flatConnection z)) (-forcedMoment z g) (by
      rw [forcedMoment_affine]
      ring)

/-- No spectral premise: the scalar obstruction is the literal full theta connection. -/
theorem nativeThetaParametrix_equation (z : ℂ) (g : ThetaContinuousBV) (x : ℝ) :
    thetaSpatialAction (nativeThetaParametrix z g) x-z*nativeThetaParametrix z g x =
      (z*flatConnection z)*g x := by
  rw [nativeThetaParametrix, nativeZeroMomentSolution_equation]
  change (-z*forcedMoment z g+(z*flatConnection z)*g x)-z*(-forcedMoment z g) = _
  ring

end RHTower.PaperThetaEndpoint
