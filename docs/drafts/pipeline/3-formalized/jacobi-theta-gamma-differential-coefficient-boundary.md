# Jacobi theta–Gamma differential coefficient boundary

- **Stage:** 3-formalized
- **Type:** Theorem
- **Parent:** [three approaches, B](../1-in-progress/argon-three-orthogonal-rh-approaches.md).

Let `a=θ₂(τ)`, `b=θ₃(τ)`, `c=θ₄(τ)`, and `e=E₂(τ)`, realized as their actual
analytic germs at the complex upper end. Put `K=ℂ(τ)(a,b,c,e)` and
`G=ℂ(τ)⟨Γ⟩` inside the same meromorphic field.

The ordinary field `K` is already closed under differentiation, so
`K=ℂ(τ)⟨a,b,c,e⟩`, and every element of `K` is differentially algebraic over
`ℂ(τ)`. Adjoining these concrete functions to `G` preserves and reflects
joint differential independence of every indexed family of upper-end
meromorphic functions. In particular, `ζ` and every Dirichlet `L`-function
remain hypertranscendental over `G⟨a,b,c,e⟩`.

Thus no finite algebraic differential equation for zeta or these `L`-functions
can be obtained by allowing the actual variable-modulus theta constants,
`E₂`, Gamma, and arbitrary rational expressions in all their derivatives as
coefficients. The positive survivor is the exact preservation of joint
independence, together with the concrete finite differential-field model for
the theta coefficients.

## Proof

With `k=πi/12`, the actual functions satisfy

```
a′ = k a (e+a⁴+2c⁴)
b′ = k b (e+a⁴−c⁴)
c′ = k c (e−2a⁴−c⁴)
e′ = k (2e²−a⁸−b⁸−c⁸).
```

The theta-three logarithmic derivative fixes the second equation. The
unconditional theta Wronskian fixes the difference of the first two
logarithmic derivatives, and the product/discriminant identity fixes their
sum with the third. Nonvanishing of the three theta constants clears the
denominators. Ramanujan's `E₂′` identity and
`E₄=(θ₂⁸+θ₃⁸+θ₄⁸)/2` give the fourth equation.

All four functions are holomorphic on the upper half-plane. Their equations
therefore descend to the actual upper-end analytic germs and then their
fraction field, whose derivation is ordinary complex differentiation.
Every generator derivative lies in `K`; field operations and the quotient
rule give differential closure. Finite generation bounds the ordinary
transcendence degree, so no element can have algebraically independent jets
of every order. Hence every element of `K` is differentially algebraic.

Differential algebraicity persists when the base is extended to `G`.
The corpus's exact DA base-change theorem preserves and reflects joint
differential independence after adjoining any such coefficient family.
Applying the established Gamma-field hypertranscendence of zeta and
Dirichlet `L`-functions gives the asserted concrete obstruction.

## Lean certificate

Module: `ArithmeticHarmonicAnalysis/JacobiThetaGammaCoefficientBoundary.lean`.
Namespace:
`GaloisForLFunctions.ArithmeticHarmonicAnalysis.ModularThetaCoefficients`.

- `source_deriv`, `sourceMero_deriv`: actual polynomial differential system.
- `differentialAdjoin_source_eq`: ordinary and differential theta fields coincide.
- `modularField_differentialAlgebraic`: DA of every rational observable in that field.
- `thetaGamma_differentialIndependent_iff`: exact joint independence preservation.
- `thetaGamma_hypertranscendental_iff`: exact HT preservation for every observable.
- `zeta_hypertranscendentalOver_thetaGamma`.
- `lfunction_hypertranscendentalOver_thetaGamma`.

Direct source check and all six transitive axiom audits passed. Dependencies
are exactly `propext`, `Classical.choice`, and `Quot.sound`.

## Scope

The theta constants vary with their modulus `τ`. This differs from the
existing elliptic-variable theta logarithmic-derivative theorem with fixed
modulus. The analytic realization and polynomial closure are proved here;
the abstract base-change law and Gamma-field hypertranscendence are reused.
No literature-novelty claim is made.

The result concerns finite algebraic differential equations over the stated
function field. It does not exclude isolated special-value period relations,
Mahler/q-difference equations, or a new mixed arithmetic realization outside
that coefficient field.
