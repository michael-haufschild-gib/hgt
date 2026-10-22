# Deninger even-Real conjugate-time flow universality law

Status: **Stage 3 — formalized in Lean 4**

## Discovery

Whole-corpus theorem-posting closure joined:

- `deningerEntireFlowSource_add` and `deningerArithmeticFlow_add`, which construct an honest complex
  one-parameter Frobenius group from the source multiplier
  `exp(t(1/2 + Iz))`; and
- `deningerEntireFunctionalEquationSigma_thetaCoordinate`,
  `deningerEntireFunctionalEquationSigma_mul`, and
  `deningerArithmeticH1EvenKReal_sigma_class`, which define the multiplicative even-Real
  involution on the same source and its middle-cohomology quotient.

No corpus theorem identifies how the full complex flow transforms under that Real structure.

## Universal law

For every complex time `t` and middle-cohomology class `x`,

`σ(φ_t x) = φ_conj(t)(σx)`.

Consequently:

1. the Real structure commutes with the complete flow at every real time;
2. it exchanges the `t` and `conj(t)` complex-time actions off the real axis; and
3. this conjugate-time action is compatible with the additive flow law.

This is the global-time counterpart of the reflected characteristic-spectrum law: the same
source Real structure controls both generator eigenvectors and its exponentiated flow.

## Dependency-closed paper proof

1. Source flow is multiplication by `E_t(z) = exp(t(1/2 + Iz))`.
2. Functional-equation reflection sends an entire source `F` to
   `conj(F(-conj z))`.
3. Direct substitution gives
   `σ(E_t)(z) = conj(exp(t(1/2 + I(-conj z))))
              = exp(conj(t)(1/2 + Iz))
              = E_conj(t)(z)`.
4. Reflection is multiplicative, so
   `σ(E_t F) = σ(E_t) σ(F) = E_conj(t) σ(F)`.
5. Pass to the stable Xi quotient using the existing class formula. This yields
   `σ(φ_t x) = φ_conj(t)(σx)` for arbitrary `x`.
6. If `t` is real, `conj(t)=t`, giving honest commutation. The existing source addition theorem
   supplies compatibility with `φ_(t+u)=φ_t φ_u`.

No spectral sum, unbounded functional calculus, RH premise, or numerical evidence enters.

## Formal targets

- `deningerEntireFunctionalEquationSigma_flowSource`
- `deningerArithmeticH1EvenKReal_sigma_flow`
- `deningerArithmeticH1EvenKReal_sigma_flow_ofReal`
- `deninger_evenReal_conjugateTimeFlowUniversality`

## Novelty audit

Post-proof searches found Deninger's foliated-flow analogy, dynamical Lichtenbaum theory, and
regularized determinant formulas for flow generators. They did not reveal the exact conjugate-time
equivariance of this source-quotient Frobenius flow under a constructed functional-equation
even-Real involution.

The exact global flow law remains **[NOVELTY UNVERIFIED]**:

- https://arxiv.org/abs/math/0605724
- https://arxiv.org/abs/2410.20758
- https://arxiv.org/abs/1602.01980

## Lean formalization

Formalized in:

`formal/GaloisForLFunctions/RHTower/Deninger/DeningerEvenRealConjugateTimeFlowUniversalityLaw.lean`

with declarations:

- `deningerEntireFunctionalEquationSigma_flowSource`
- `deningerArithmeticH1EvenKReal_sigma_flow`
- `deningerArithmeticH1EvenKReal_sigma_flow_ofReal`
- `deninger_evenReal_conjugateTimeFlowUniversality`

Exact-file verification passed:

`lake env lean GaloisForLFunctions/RHTower/Deninger/DeningerEvenRealConjugateTimeFlowUniversalityLaw.lean`

Wired into `GaloisForLFunctions/RHTower.lean` with the other Deninger characteristic, flow, and
Real-source laws.
