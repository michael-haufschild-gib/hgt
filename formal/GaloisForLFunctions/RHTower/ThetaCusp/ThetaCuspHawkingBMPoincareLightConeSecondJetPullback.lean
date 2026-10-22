import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPlebanskiCoordinateJacobiVertex

/-!
# Full Poincare light-cone Hessian pullback to the BM rapidity chart

The coordinate Plebanski operator needs `partial_u^(2 : ℕ)`, `partial_u partial_w`, and
`partial_w^(2 : ℕ)`, not merely the first light-cone derivatives.  A variable-coefficient inverse
Jacobian has a forced first-jet connection term:

`V(W f) = V^i W^j f_ij + V^i (partial_i W^j) f_j`.

This module implements that formula on complete symmetric BM two-jets in
`(tau,x,sigma,xi)`.  The formal inverse-scale jets are the algebraic derivatives of

`timeScaleInv = (sigma*tanh xi)^-1`,
`radialScaleInv = (sigma*sech xi)^-1`.

They give total polynomial expressions in the two inverse-scale variables, so no chart-edge
premise is introduced.  The resulting `u,w,uu,uw,ww` jet feeds the literal coordinate-space
Plebanski Eq. (63) operator.  A physical radial-coordinate witness proves that deleting the
connection term changes `partial_Z^(2 : ℕ)` even on a sigma-affine BM jet.

`[NEW CONSEQUENCE] [PAPER-PROVED] [LEAN-PROVED] [HC94] [FULL LIGHT-CONE HESSIAN]`
-/

open Complex Real

namespace RHTower

noncomputable section

/-- Complete symmetric second jet of a scalar in BM rapidity coordinates
`(tau,x,sigma,xi)`. -/
structure D4BMFullSecondJet where
  first : D4BMFullFirstJet
  tauTau : ℂ
  tauHorizonX : ℂ
  tauSigma : ℂ
  tauXi : ℂ
  horizonXHorizonX : ℂ
  horizonXSigma : ℂ
  horizonXXi : ℂ
  sigmaSigma : ℂ
  sigmaXi : ℂ
  xiXi : ℂ

/-- First jet of every coefficient of a BM vector field. -/
structure D4BMVectorFieldFirstJet where
  tau : D4BMFullFirstJet
  horizonX : D4BMFullFirstJet
  sigma : D4BMFullFirstJet
  xi : D4BMFullFirstJet

/-- Linear combination of scalar BM first jets. -/
def d4BMFullFirstJetLinearCombination
    (a b : ℂ) (P Q : D4BMFullFirstJet) : D4BMFullFirstJet where
  value := a * P.value + b * Q.value
  tau := a * P.tau + b * Q.tau
  horizonX := a * P.horizonX + b * Q.horizonX
  sigma := a * P.sigma + b * Q.sigma
  xi := a * P.xi + b * Q.xi

/-- Linear combination of variable-coefficient BM vector fields, including coefficient jets. -/
def d4BMVectorFieldFirstJetLinearCombination
    (a b : ℂ) (V W : D4BMVectorFieldFirstJet) : D4BMVectorFieldFirstJet where
  tau := d4BMFullFirstJetLinearCombination a b V.tau W.tau
  horizonX := d4BMFullFirstJetLinearCombination a b V.horizonX W.horizonX
  sigma := d4BMFullFirstJetLinearCombination a b V.sigma W.sigma
  xi := d4BMFullFirstJetLinearCombination a b V.xi W.xi

/-- First directional derivative on a BM first jet. -/
def d4BMDirectionalDerivativeOnFullFirstJet
    (V : D4BMVectorFieldFirstJet) (J : D4BMFullFirstJet) : ℂ :=
  V.tau.value * J.tau + V.horizonX.value * J.horizonX +
    V.sigma.value * J.sigma + V.xi.value * J.xi

/-- Hessian-principal part `V^i W^j f_ij` of an ordered second derivative. -/
def d4BMPrincipalSecondDirectionalDerivative
    (V W : D4BMVectorFieldFirstJet) (J : D4BMFullSecondJet) : ℂ :=
  V.tau.value *
      (W.tau.value * J.tauTau + W.horizonX.value * J.tauHorizonX +
        W.sigma.value * J.tauSigma + W.xi.value * J.tauXi) +
    V.horizonX.value *
      (W.tau.value * J.tauHorizonX +
        W.horizonX.value * J.horizonXHorizonX +
        W.sigma.value * J.horizonXSigma + W.xi.value * J.horizonXXi) +
    V.sigma.value *
      (W.tau.value * J.tauSigma + W.horizonX.value * J.horizonXSigma +
        W.sigma.value * J.sigmaSigma + W.xi.value * J.sigmaXi) +
    V.xi.value *
      (W.tau.value * J.tauXi + W.horizonX.value * J.horizonXXi +
        W.sigma.value * J.sigmaXi + W.xi.value * J.xiXi)

/-- First-jet connection part `V^i (partial_i W^j) f_j`. -/
def d4BMConnectionSecondDirectionalDerivative
    (V W : D4BMVectorFieldFirstJet) (J : D4BMFullSecondJet) : ℂ :=
  V.tau.value *
      (W.tau.tau * J.first.tau + W.horizonX.tau * J.first.horizonX +
        W.sigma.tau * J.first.sigma + W.xi.tau * J.first.xi) +
    V.horizonX.value *
      (W.tau.horizonX * J.first.tau +
        W.horizonX.horizonX * J.first.horizonX +
        W.sigma.horizonX * J.first.sigma + W.xi.horizonX * J.first.xi) +
    V.sigma.value *
      (W.tau.sigma * J.first.tau + W.horizonX.sigma * J.first.horizonX +
        W.sigma.sigma * J.first.sigma + W.xi.sigma * J.first.xi) +
    V.xi.value *
      (W.tau.xi * J.first.tau + W.horizonX.xi * J.first.horizonX +
        W.sigma.xi * J.first.sigma + W.xi.xi * J.first.xi)

/-- Ordered second directional derivative `V(W f)` on a complete BM two-jet. -/
def d4BMOrderedSecondDirectionalDerivative
    (V W : D4BMVectorFieldFirstJet) (J : D4BMFullSecondJet) : ℂ :=
  V.tau.value *
      (W.tau.tau * J.first.tau + W.horizonX.tau * J.first.horizonX +
        W.sigma.tau * J.first.sigma + W.xi.tau * J.first.xi +
        W.tau.value * J.tauTau + W.horizonX.value * J.tauHorizonX +
        W.sigma.value * J.tauSigma + W.xi.value * J.tauXi) +
    V.horizonX.value *
      (W.tau.horizonX * J.first.tau +
        W.horizonX.horizonX * J.first.horizonX +
        W.sigma.horizonX * J.first.sigma + W.xi.horizonX * J.first.xi +
        W.tau.value * J.tauHorizonX +
        W.horizonX.value * J.horizonXHorizonX +
        W.sigma.value * J.horizonXSigma + W.xi.value * J.horizonXXi) +
    V.sigma.value *
      (W.tau.sigma * J.first.tau + W.horizonX.sigma * J.first.horizonX +
        W.sigma.sigma * J.first.sigma + W.xi.sigma * J.first.xi +
        W.tau.value * J.tauSigma + W.horizonX.value * J.horizonXSigma +
        W.sigma.value * J.sigmaSigma + W.xi.value * J.sigmaXi) +
    V.xi.value *
      (W.tau.xi * J.first.tau + W.horizonX.xi * J.first.horizonX +
        W.sigma.xi * J.first.sigma + W.xi.xi * J.first.xi +
        W.tau.value * J.tauXi + W.horizonX.value * J.horizonXXi +
        W.sigma.value * J.sigmaXi + W.xi.value * J.xiXi)

/-- Exact variable-coefficient second-chain-rule decomposition. -/
theorem d4BMOrderedSecondDirectionalDerivative_eq_principal_add_connection
    (V W : D4BMVectorFieldFirstJet) (J : D4BMFullSecondJet) :
    d4BMOrderedSecondDirectionalDerivative V W J =
      d4BMPrincipalSecondDirectionalDerivative V W J +
        d4BMConnectionSecondDirectionalDerivative V W J := by
  simp [d4BMOrderedSecondDirectionalDerivative,
    d4BMPrincipalSecondDirectionalDerivative,
    d4BMConnectionSecondDirectionalDerivative]
  ring

/-- Formal first jet of the Poincare `partial_T` vector field in BM coordinates.  Derivatives of
`timeScaleInv` use the exact inverse rule for `(sigma*tanh xi)^-1`. -/
def d4PoincareTimeVectorFieldFirstJetOnBMFormalInv
    (timeScaleInv : ℂ) (tau xi sigma : ℝ) : D4BMVectorFieldFirstJet :=
  let a : ℂ := Real.tanh xi
  let b : ℂ := d4BMRindlerRapiditySech xi
  let c : ℂ := Real.cosh tau
  let s : ℂ := Real.sinh tau
  let S : ℂ := sigma
  { tau :=
      { value := timeScaleInv * c
        tau := timeScaleInv * s
        horizonX := 0
        sigma := -a * timeScaleInv ^ (2 : ℕ) * c
        xi := -S * b ^ (2 : ℕ) * timeScaleInv ^ (2 : ℕ) * c }
    horizonX := { value := 0, tau := 0, horizonX := 0, sigma := 0, xi := 0 }
    sigma :=
      { value := -timeScaleInv * S * a ^ (2 : ℕ) * s
        tau := -timeScaleInv * S * a ^ (2 : ℕ) * c
        horizonX := 0
        sigma := (a * timeScaleInv ^ (2 : ℕ) * S - timeScaleInv) * a ^ (2 : ℕ) * s
        xi :=
          (S ^ (2 : ℕ) * b ^ (2 : ℕ) * timeScaleInv ^ (2 : ℕ) * a ^ (2 : ℕ) -
            2 * timeScaleInv * S * a * b ^ (2 : ℕ)) * s }
    xi :=
      { value := -timeScaleInv * a * s
        tau := -timeScaleInv * a * c
        horizonX := 0
        sigma := a ^ (2 : ℕ) * timeScaleInv ^ (2 : ℕ) * s
        xi := (S * b ^ (2 : ℕ) * timeScaleInv ^ (2 : ℕ) * a - timeScaleInv * b ^ (2 : ℕ)) * s } }

/-- Formal first jet of the Poincare `partial_Y` vector field in BM coordinates. -/
def d4PoincareHorizonYVectorFieldFirstJetOnBMFormalInv
    (timeScaleInv : ℂ) (tau xi sigma : ℝ) : D4BMVectorFieldFirstJet :=
  let a : ℂ := Real.tanh xi
  let b : ℂ := d4BMRindlerRapiditySech xi
  let c : ℂ := Real.cosh tau
  let s : ℂ := Real.sinh tau
  let S : ℂ := sigma
  { tau :=
      { value := -timeScaleInv * s
        tau := -timeScaleInv * c
        horizonX := 0
        sigma := a * timeScaleInv ^ (2 : ℕ) * s
        xi := S * b ^ (2 : ℕ) * timeScaleInv ^ (2 : ℕ) * s }
    horizonX := { value := 0, tau := 0, horizonX := 0, sigma := 0, xi := 0 }
    sigma :=
      { value := timeScaleInv * S * a ^ (2 : ℕ) * c
        tau := timeScaleInv * S * a ^ (2 : ℕ) * s
        horizonX := 0
        sigma := (-a * timeScaleInv ^ (2 : ℕ) * S + timeScaleInv) * a ^ (2 : ℕ) * c
        xi :=
          (-S ^ (2 : ℕ) * b ^ (2 : ℕ) * timeScaleInv ^ (2 : ℕ) * a ^ (2 : ℕ) +
            2 * timeScaleInv * S * a * b ^ (2 : ℕ)) * c }
    xi :=
      { value := timeScaleInv * a * c
        tau := timeScaleInv * a * s
        horizonX := 0
        sigma := -a ^ (2 : ℕ) * timeScaleInv ^ (2 : ℕ) * c
        xi := (-S * b ^ (2 : ℕ) * timeScaleInv ^ (2 : ℕ) * a + timeScaleInv * b ^ (2 : ℕ)) * c } }

/-- Formal first jet of the Poincare `partial_Z` vector field in BM coordinates. -/
def d4PoincareRadialVectorFieldFirstJetOnBMFormalInv
    (radialScaleInv : ℂ) (xi sigma : ℝ) : D4BMVectorFieldFirstJet :=
  let a : ℂ := Real.tanh xi
  let b : ℂ := d4BMRindlerRapiditySech xi
  let S : ℂ := sigma
  { tau := { value := 0, tau := 0, horizonX := 0, sigma := 0, xi := 0 }
    horizonX := { value := 0, tau := 0, horizonX := 0, sigma := 0, xi := 0 }
    sigma :=
      { value := radialScaleInv * S * b ^ (2 : ℕ)
        tau := 0
        horizonX := 0
        sigma := (-b * radialScaleInv ^ (2 : ℕ) * S + radialScaleInv) * b ^ (2 : ℕ)
        xi :=
          S ^ (2 : ℕ) * a * b ^ (3 : ℕ) * radialScaleInv ^ (2 : ℕ) -
            2 * radialScaleInv * S * a * b ^ (2 : ℕ) }
    xi :=
      { value := -radialScaleInv * a
        tau := 0
        horizonX := 0
        sigma := b * radialScaleInv ^ (2 : ℕ) * a
        xi := -S * a ^ (2 : ℕ) * b * radialScaleInv ^ (2 : ℕ) - radialScaleInv * b ^ (2 : ℕ) } }

/-- Constant Poincare `partial_X` vector field. -/
def d4PoincareHorizonXVectorFieldFirstJetOnBM : D4BMVectorFieldFirstJet :=
  { tau := { value := 0, tau := 0, horizonX := 0, sigma := 0, xi := 0 }
    horizonX := { value := 1, tau := 0, horizonX := 0, sigma := 0, xi := 0 }
    sigma := { value := 0, tau := 0, horizonX := 0, sigma := 0, xi := 0 }
    xi := { value := 0, tau := 0, horizonX := 0, sigma := 0, xi := 0 } }

/-- Poincare light-cone `partial_u=(partial_T+partial_Z)/2` as a BM coefficient first jet. -/
def d4PoincareLightConeUVectorFieldFirstJetOnBMFormalInv
    (timeScaleInv radialScaleInv : ℂ) (tau xi sigma : ℝ) :
    D4BMVectorFieldFirstJet :=
  d4BMVectorFieldFirstJetLinearCombination (1 / 2) (1 / 2)
    (d4PoincareTimeVectorFieldFirstJetOnBMFormalInv timeScaleInv tau xi sigma)
    (d4PoincareRadialVectorFieldFirstJetOnBMFormalInv radialScaleInv xi sigma)

/-- Poincare `partial_w=(partial_X-i partial_Y)/2` as a BM coefficient first jet. -/
def d4PoincareLightConeWVectorFieldFirstJetOnBMFormalInv
    (timeScaleInv : ℂ) (tau xi sigma : ℝ) : D4BMVectorFieldFirstJet :=
  d4BMVectorFieldFirstJetLinearCombination (1 / 2) (-Complex.I / 2)
    d4PoincareHorizonXVectorFieldFirstJetOnBM
    (d4PoincareHorizonYVectorFieldFirstJetOnBMFormalInv timeScaleInv tau xi sigma)

/-- Full coordinate-space Plebanski light-cone two-jet pulled through the BM rapidity chart.
The mixed derivative is symmetrized, making Hessian symmetry explicit in the total algebraic
extension at chart edges. -/
def d4PlebanskiLightConeTwoJetOfBMFormalInv
    (timeScaleInv radialScaleInv : ℂ) (tau xi sigma : ℝ)
    (J : D4BMFullSecondJet) : D4PlebanskiLightConeTwoJet :=
  let U := d4PoincareLightConeUVectorFieldFirstJetOnBMFormalInv
    timeScaleInv radialScaleInv tau xi sigma
  let W := d4PoincareLightConeWVectorFieldFirstJetOnBMFormalInv
    timeScaleInv tau xi sigma
  { value := J.first.value
    u := d4BMDirectionalDerivativeOnFullFirstJet U J.first
    w := d4BMDirectionalDerivativeOnFullFirstJet W J.first
    uu := d4BMOrderedSecondDirectionalDerivative U U J
    uw := (1 / 2 : ℂ) *
      (d4BMOrderedSecondDirectionalDerivative U W J +
        d4BMOrderedSecondDirectionalDerivative W U J)
    ww := d4BMOrderedSecondDirectionalDerivative W W J }

/-- First-order compatibility with the already-audited full inverse-Jacobian map. -/
theorem d4PlebanskiLightConeTwoJetOfBMFormalInv_first_eq
    (timeScaleInv radialScaleInv : ℂ) (tau xi sigma : ℝ)
    (J : D4BMFullSecondJet) :
    (d4PlebanskiLightConeTwoJetOfBMFormalInv
        timeScaleInv radialScaleInv tau xi sigma J).u =
        d4PoincareLightConeUDerivative
          (d4PoincareFullFirstJetOfBMInv
            timeScaleInv radialScaleInv tau xi sigma J.first) ∧
      (d4PlebanskiLightConeTwoJetOfBMFormalInv
        timeScaleInv radialScaleInv tau xi sigma J).w =
        d4PoincareLightConeWDerivative
          (d4PoincareFullFirstJetOfBMInv
            timeScaleInv radialScaleInv tau xi sigma J.first) := by
  constructor <;>
    simp [d4PlebanskiLightConeTwoJetOfBMFormalInv,
      d4PoincareLightConeUVectorFieldFirstJetOnBMFormalInv,
      d4PoincareLightConeWVectorFieldFirstJetOnBMFormalInv,
      d4BMVectorFieldFirstJetLinearCombination,
      d4BMFullFirstJetLinearCombination,
      d4BMDirectionalDerivativeOnFullFirstJet,
      d4PoincareTimeVectorFieldFirstJetOnBMFormalInv,
      d4PoincareHorizonYVectorFieldFirstJetOnBMFormalInv,
      d4PoincareRadialVectorFieldFirstJetOnBMFormalInv,
      d4PoincareHorizonXVectorFieldFirstJetOnBM,
      d4PoincareLightConeUDerivative,
      d4PoincareLightConeWDerivative,
      d4PoincareFullFirstJetOfBMInv,
      d4ScaledPoincareTimeDerivativeOnBMFirstJet,
      d4ScaledPoincareHorizonYDerivativeOnBMFirstJet,
      d4ScaledPoincareRadialDerivativeOnBMFullFirstJet] <;>
    ring

/-- Eq. (63) evaluated on two arbitrary complete BM two-jets after the exact full Hessian
pullback. -/
def ads4PlebanskiJacobiDoubleBracketOnBMFullSecondJets
    (inverseUV timeScaleInv radialScaleInv : ℂ) (tau xi sigma : ℝ)
    (P Q : D4BMFullSecondJet) : ℂ :=
  ads4PlebanskiJacobiDoubleBracketOnTwoJets inverseUV
    (d4PlebanskiLightConeTwoJetOfBMFormalInv
      timeScaleInv radialScaleInv tau xi sigma P)
    (d4PlebanskiLightConeTwoJetOfBMFormalInv
      timeScaleInv radialScaleInv tau xi sigma Q)

/-- Exchange symmetry survives the complete BM Hessian pullback. -/
theorem ads4PlebanskiJacobiDoubleBracketOnBMFullSecondJets_exchange
    (inverseUV timeScaleInv radialScaleInv : ℂ) (tau xi sigma : ℝ)
    (P Q : D4BMFullSecondJet) :
    ads4PlebanskiJacobiDoubleBracketOnBMFullSecondJets
        inverseUV timeScaleInv radialScaleInv tau xi sigma Q P =
      ads4PlebanskiJacobiDoubleBracketOnBMFullSecondJets
        inverseUV timeScaleInv radialScaleInv tau xi sigma P Q := by
  exact ads4PlebanskiJacobiDoubleBracketOnTwoJets_exchange _ _ _

/-- Sigma-affine BM witness: value `sigma`, constant first sigma derivative, zero Hessian. -/
def d4BMSigmaAffineFullSecondJet (sigma : ℝ) : D4BMFullSecondJet :=
  { first := { value := sigma, tau := 0, horizonX := 0, sigma := 1, xi := 0 }
    tauTau := 0
    tauHorizonX := 0
    tauSigma := 0
    tauXi := 0
    horizonXHorizonX := 0
    horizonXSigma := 0
    horizonXXi := 0
    sigmaSigma := 0
    sigmaXi := 0
    xiXi := 0 }

/-- On the physical inverse radial scale at `sigma=1`, the full `partial_Z^(2 : ℕ)` connection acting
on the sigma-affine witness is exactly `tanh(xi)^(2 : ℕ)`; its Hessian-principal part is zero. -/
theorem d4PoincareRadialSecondDerivative_sigmaAffine_connection
    (xi : ℝ) :
    let Z := d4PoincareRadialVectorFieldFirstJetOnBMFormalInv
      ((d4BMRindlerRapiditySech xi : ℂ)⁻¹) xi 1
    d4BMOrderedSecondDirectionalDerivative Z Z (d4BMSigmaAffineFullSecondJet 1) =
        (Real.tanh xi : ℂ) ^ (2 : ℕ) ∧
      d4BMPrincipalSecondDirectionalDerivative Z Z (d4BMSigmaAffineFullSecondJet 1) = 0 := by
  have hbR : d4BMRindlerRapiditySech xi ≠ 0 := by
    exact inv_ne_zero (ne_of_gt (Real.cosh_pos xi))
  have hb : (d4BMRindlerRapiditySech xi : ℂ) ≠ 0 := by
    exact_mod_cast hbR
  dsimp
  constructor
  · simp [d4BMOrderedSecondDirectionalDerivative,
      d4PoincareRadialVectorFieldFirstJetOnBMFormalInv,
      d4BMSigmaAffineFullSecondJet]
    field_simp [hb]
    ring
  · simp [d4BMPrincipalSecondDirectionalDerivative,
      d4PoincareRadialVectorFieldFirstJetOnBMFormalInv,
      d4BMSigmaAffineFullSecondJet]

/-- Physical route-killer for the connection-free Hessian shortcut. -/
theorem d4PoincareRadialSecondDerivative_sigmaAffine_ne_principal :
    let xi : ℝ := 1
    let Z := d4PoincareRadialVectorFieldFirstJetOnBMFormalInv
      ((d4BMRindlerRapiditySech xi : ℂ)⁻¹) xi 1
    d4BMOrderedSecondDirectionalDerivative Z Z (d4BMSigmaAffineFullSecondJet 1) ≠
      d4BMPrincipalSecondDirectionalDerivative Z Z (d4BMSigmaAffineFullSecondJet 1) := by
  dsimp
  rw [(d4PoincareRadialSecondDerivative_sigmaAffine_connection 1).1,
    (d4PoincareRadialSecondDerivative_sigmaAffine_connection 1).2]
  have htanh : Real.tanh (1 : ℝ) ≠ 0 := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_ne_zero (Real.sinh_ne_zero.mpr one_ne_zero)
      (ne_of_gt (Real.cosh_pos 1))
  exact pow_ne_zero 2 (ofReal_ne_zero.mpr htanh)

end

end RHTower
