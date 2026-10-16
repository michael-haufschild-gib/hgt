import GaloisForLFunctions.RHTower.PaperThetaNativeGrushinArithmetic
import GaloisForLFunctions.RHTower.PaperThetaNativeScalarReduction
import GaloisForLFunctions.RHTower.PaperThetaCutMeyerCurrent
import GaloisForLFunctions.RHTower.PaperThetaMeyerFredholmMultiplicity

/-! # Entire continuous native modes with the full original Meyer source

A compact smooth source carries the Xi defect while every mode remains in
the actual continuous native differential domain. The whole-plane family
is entire in uniform norm and recovers the literal original modes on Xi.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex
open scoped BoundedContinuousFunction

namespace RHTower.PaperThetaEndpoint
open HedenmalmThetaSource CHMDDoobGraph

def nativeZeroForcing : ThetaContinuousBV where
  toFun _ := 0
  continuous := continuous_const
  bv := by simpa only [zero_mul, add_zero] using
    boundedVariation_affine (nativeCounterSource_boundedVariation 0) 0 0

@[simp] theorem nativeBVUniform_zeroForcing : nativeBVUniform nativeZeroForcing = 0 := by
  ext x
  rfl

def nativeEntireMode (z : ℂ) : NativeContinuousSpace := nativeGrushinProfile z (0,1)

def nativeEntireModeDomain (z : ℂ) : ThetaNativeDomain := nativeGrushinBV z nativeZeroForcing 1

theorem nativeEntireMode_coe (z : ℂ) :
    (nativeEntireMode z : ℝ → ℂ) = nativeEntireModeDomain z := by
  funext x
  change nativeGrushinProfile z (0,1) x = nativeGrushinBV z nativeZeroForcing 1 x
  rw [nativeGrushinProfile_eq_solution, nativeGrushinBV_apply, nativeBVUniform_zeroForcing]

theorem differentiable_nativeEntireMode : Differentiable ℂ nativeEntireMode :=
  differentiable_nativeGrushinProfile.clm_apply (differentiable_const (0,1))

theorem nativeEntireMode_trace (z : ℂ) : thetaTailTrace (nativeEntireMode z) = 1 :=
  nativeGrushinProfile_trace z 0 1

/-- A classical native equation on the whole plane, with a genuine compact source. -/
theorem nativeEntireMode_equation (z : ℂ) (x : ℝ) :
    thetaSpatialAction (nativeEntireMode z) x-z*nativeEntireMode z x =
      -nativeEffectiveScalar z*nativeCounterSource z x := by
  have he := nativeGrushinProfile_equation z 0 1 x
  simp only [nativeBoundaryCorrection, map_zero, zero_add, mul_one] at he
  change thetaSpatialAction (nativeEntireMode z) x-z*nativeEntireMode z x+
    nativeEffectiveScalar z*nativeCounterSource z x = 0 at he
  linear_combination he

/-- The source continuation agrees with the literal native mode at every Xi point. -/
theorem nativeEntireMode_at_Xi (rho : XiDivisorSupport) (x : ℝ) :
    nativeEntireMode (xiSpectralPointSupport rho) x = -flatQuotient (xiSpectralPointSupport rho) x := by
  let z := xiSpectralPointSupport rho
  have hXi : XiC z = 0 := XiC_xiSpectralPoint_eq_zero
    (⟨rho, ⟨0,xiSupportMultiplicity_pos rho⟩⟩ : XiZeroCopy)
  have he0 : nativeEffectiveScalar z = 0 := (nativeEffectiveScalar_zero_iff z).mpr (Or.inr hXi)
  have he (y : ℝ) : deriv (nativeEntireMode z) y+
      sourceLogDerivative y*(nativeEntireMode z y-1)+I*z*nativeEntireMode z y = 0 := by
    have h := nativeEntireMode_equation z y
    rw [he0, neg_zero, zero_mul, thetaSpatialAction, nativeEntireMode_trace] at h
    linear_combination (norm := ring_nf) -I*h
    simp only [Complex.I_sq]
    ring
  have h := nativeHomogeneous_eq z (nativeEntireMode z) 1
    (nativeGrushinProfile_differentiable z 0 1) (nativeGrushinProfile_atTop z 0 1) he x
  simpa only [neg_mul, one_mul] using h

theorem nativeEffectiveScalar_meyer_factorization (rho : XiDivisorSupport)
    (k : Fin (xiSupportMultiplicity rho+1)) (z : ℂ) :
    nativeEffectiveScalar z =
      (z/((thetaSource.mass : ℂ)*(nativeCounterMass : ℂ)))*
        (z-xiSpectralPointSupport rho)^k.val*
          deningerMeyerCenteredMellin (deningerMeyerHedenmalmSource rho k) z := by
  rw [nativeEffectiveScalar_eq, deningerMeyerHedenmalmSource_transform,
    xiThetaDividedChain_partial_factorization rho (Nat.le_of_lt_succ k.isLt) z]
  ring

/-- The continuous source defect has exactly the original HF full-Jordan rank. -/
theorem nativeEffectiveScalar_meyer_rank (rho : XiDivisorSupport) :
    analyticOrderAt nativeEffectiveScalar (xiSpectralPointSupport rho) =
      (deningerMeyerHasseSpectralRank rho : ℕ∞) := by
  rw [nativeEffectiveScalar_order, deningerMeyerHasseSpectralRank_eq]

/-- Every original full-multiplicity source factors the literal continuous equation. -/
theorem nativeEntireMode_meyer_source (rho : XiDivisorSupport)
    (k : Fin (xiSupportMultiplicity rho+1)) (z : ℂ) (x : ℝ) :
    thetaSpatialAction (nativeEntireMode z) x-z*nativeEntireMode z x =
      -(z/((thetaSource.mass : ℂ)*(nativeCounterMass : ℂ)))*
        (z-xiSpectralPointSupport rho)^k.val*
          deningerMeyerCenteredMellin (deningerMeyerHedenmalmSource rho k) z*nativeCounterSource z x := by
  rw [nativeEntireMode_equation, nativeEffectiveScalar_meyer_factorization rho k]
  ring

/-- The entire family lives in the original continuous native domain and retains
the complete arithmetic expression through the singular compact coordinate. -/
theorem nativeEntireMode_full_source :
    Differentiable ℂ nativeEntireMode ∧
      ∀ z : ℂ,
        (nativeEntireMode z : ℝ → ℂ) = nativeEntireModeDomain z ∧
        thetaTailTrace (nativeEntireModeDomain z) = 1 ∧
        AbsolutelyContinuousOnInterval (nativeClosedQuantile (nativeEntireModeDomain z)) 0 1 ∧
        (∀ x, thetaSpatialAction (nativeEntireMode z) x-z*nativeEntireMode z x =
          -nativeEffectiveScalar z*nativeCounterSource z x) ∧
        ∀ L : ℂ →L[ℝ] ℝ,
          sourceWeilEnergy (nativeWeilGraph (nativeEntireModeDomain z) L) =
            ThetaQuantileArithmetic.weilEnergy (fun t => L (nativeClosedQuantile (nativeEntireModeDomain z) t)) :=
  ⟨differentiable_nativeEntireMode, fun z => ⟨nativeEntireMode_coe z,
    nativeGrushinBV_trace z nativeZeroForcing 1, absolutelyContinuousOnInterval_nativeClosedQuantile _,
    nativeEntireMode_equation z, fun L => nativeWeilGraph_quantile _ L⟩⟩

end RHTower.PaperThetaEndpoint
