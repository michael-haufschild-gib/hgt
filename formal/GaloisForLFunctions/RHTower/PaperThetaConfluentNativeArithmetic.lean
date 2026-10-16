import GaloisForLFunctions.RHTower.PaperThetaConfluentNativeRegularity

/-!
# Repeated native resonance in the full arithmetic domain

For every original continuous BV forcing and every positive resonant order,
the explicit Green-lifted solver satisfies the literal repeated spatial
equation with its precise finite Meyer correction. Its actual compact AC
representative retains all prime, Gamma, mass, and polar terms of the Weil form.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex Zeta23
open scoped BoundedContinuousFunction

namespace RHTower.PaperThetaEndpoint
open CHMDDoobGraph

/-- Literal solution of a repeated resonant equation, retaining the exact
finite source correction. The positive order is `n+1`. -/
def nativeConfluentBVProfile (rho : XiDivisorSupport) (n : ℕ) (g : ThetaContinuousBV) :
    ThetaNativeDomain :=
  nativeThetaResolvent nativeCompactParameter (nativeBVOfUniform
    ((nativeCompactResolvent^n) (nativeConfluentPowerSolver rho (n+1) (nativeBVUniform g)))
    (nativeCompactResolvent_pow_bv n (nativeConfluentPowerSolver_bv rho (n+1) g.bv)))

theorem nativeConfluentBVProfile_eq (rho : XiDivisorSupport) (n : ℕ) (g : ThetaContinuousBV) :
    (nativeConfluentBVProfile rho n g : ℝ → ℂ) =
      (nativeCompactResolvent^(n+1)) (nativeConfluentPowerSolver rho (n+1) (nativeBVUniform g)) := by
  have h := nativeThetaResolvent_uniform nativeCompactParameter (nativeBVOfUniform
    ((nativeCompactResolvent^n) (nativeConfluentPowerSolver rho (n+1) (nativeBVUniform g)))
    (nativeCompactResolvent_pow_bv n (nativeConfluentPowerSolver_bv rho (n+1) g.bv)))
  rw [nativeBVUniform_ofUniform] at h
  funext x
  have hx := congrArg (fun f : NativeContinuousSpace => f x) h
  change nativeConfluentBVProfile rho n g x =
    nativeCompactResolvent ((nativeCompactResolvent^n)
      (nativeConfluentPowerSolver rho (n+1) (nativeBVUniform g))) x at hx
  simpa only [pow_succ',mul_apply_eq_comp] using hx

/-- The entire repeated spatial equation is solved on original BV forcing.
The only residual is the explicitly constructed original Meyer packet. -/
theorem nativeConfluentBVProfile_equation (rho : XiDivisorSupport) (n : ℕ)
    (g : ThetaContinuousBV) :
    (nativeShiftAction (xiSpectralPointSupport rho))^[n+1] (nativeConfluentBVProfile rho n g) =
      nativeBVUniform g-nativeConfluentPowerDefect rho (n+1) (nativeBVUniform g) := by
  rw [nativeConfluentBVProfile_eq,nativeShiftAction_iterate_compact,
    nativeConfluentPowerSolver_equation]
  rfl

/-- No packet, simplicity, spectral separation, domain-admission, or positivity
premise: the constructed repeated-resonance solution has a compact AC
representative and the complete signed arithmetic value. -/
theorem nativeConfluentBVProfile_full_arithmetic (rho : XiDivisorSupport) (n : ℕ)
    (g : ThetaContinuousBV) :
    AbsolutelyContinuousOnInterval (nativeClosedQuantile (nativeConfluentBVProfile rho n g)) 0 1 ∧
    ∀ L : ℂ →L[ℝ] ℝ,
      sourceWeilEnergy (nativeWeilGraph (nativeConfluentBVProfile rho n g) L) =
        phiDoobArchJumpEnergy (fun x => L (nativeConfluentBVProfile rho n g x))+
        (∑' k, ∫ x, phiDoobPrimeJump (fun y => L (nativeConfluentBVProfile rho n g y)) k x)-
        phiDoobCoshMass (fun x => L (nativeConfluentBVProfile rho n g x)^2)+
        2*phiDoobCoshMass (fun x => L (nativeConfluentBVProfile rho n g x))^2-
        2*phiDoobSinhMass (fun x => L (nativeConfluentBVProfile rho n g x))^2 ∧
      sourceWeilEnergy (nativeWeilGraph (nativeConfluentBVProfile rho n g) L) =
        ThetaQuantileArithmetic.weilEnergy
          (fun t => L (nativeClosedQuantile (nativeConfluentBVProfile rho n g) t)) :=
  ⟨absolutelyContinuousOnInterval_nativeClosedQuantile _,
    fun L => ⟨nativeWeilGraph_energy _ L,nativeWeilGraph_quantile _ L⟩⟩

end RHTower.PaperThetaEndpoint
