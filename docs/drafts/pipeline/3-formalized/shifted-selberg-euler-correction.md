# Shifted polynomial forms and frozen gcd jet limits

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** A111, `levinson-gate-from-below-square-root-twists.md`.

## Statement

Let `P,Q` be real polynomials vanishing at zero. Put `RP(x)=(1−x)P(x)`
and, with every profile evaluated at `1−t`, define

`I(P,Q,v,k)=∫₀¹ t^k (P′−vP)(Q′−vQ) dt`.

The literal shifted finite Möbius–gcd form is

`F(P,N,c,v)=log N Σ_{h,k≤N} μ(h)μ(k)(hk)^(v/log N)`
`  ·gcd(h,k)^(1+c/log N)/(hk) ·P(1−log h/log N)P(1−log k/log N)`.

On `c=−2v`, its limit is `I(P,P,v,0)`. Its actual first directional
jet in direction `(κ,ν)` has limiting operation

`J₁(P,Q,v,κ,ν,k)=κI(P,Q,v,k+1)+νI(RP,Q,v,k)+νI(P,RQ,v,k)`.

The second limiting jet is

`J₂(P,Q,v,κ,ν,k)=κJ₁(P,Q,v,κ,ν,k+1)`
`  +νJ₁(RP,Q,v,κ,ν,k)+νJ₁(P,RQ,v,κ,ν,k)`.

All three limits hold along any filter with cutoff `N→∞` and normalized
shift `v→v₀`. No dependence of `v` solely on the integer cutoff is required.

For original twisted-moment coefficients frozen at normalized displacement
`u`, the direct gcd sum moves along `(c,v)=(−2u−2z,u+2z)` and the reflected
sum along `(2u+2z,−u)`, with physical displacement `(u+z)/log N`.
After multiplication by `log N`, their values and first two actual
`z`-derivatives have the corresponding limits above.

## Proof

Exact Euler factorization reduces the form to harmonic Möbius-profile
rows. Compact uniform profile convergence, vanishing harmonic endpoint
mass, and a summable correction-pair majorant give the value limit.

Differentiation inserts `κt`, replaces either profile by `νRP`, or
differentiates the correction. Cauchy bounds dominate every correction
jet; positive-order correction jets vanish after summation. Applying the
same recurrence twice gives the two literal derivative limits.

Uniform row and correction bounds give a common Lipschitz constant in
`v` on compact intervals. Comparing a moving shift with its fixed limit
then permits arbitrary real-height cutoffs. Exact coefficient identities
transfer the result to the original frozen gcd sums.

## Lean

Namespace `GaloisForLFunctions.MultiscaleMollifiedZetaField`:

- `TheCorrectedPolynomialJetsConverge`
- `TheShiftedSelbergFormKeepsItsFirstTwoDerivatives`
- `TheCorrectedJetsAreUniformlyLipschitz`
- `TheCorrectedJetLimitsAllowArbitraryHeights`
- `TheFrozenGcdJetsHaveTheirProfileLimits.tendsto_frozenDirectGcd_first_three`
- `TheFrozenGcdJetsHaveTheirProfileLimits.tendsto_frozenReflectedGcd_first_three`

Direct Lean checks passed; umbrella imports added. Factorization inputs
are recorded in `shifted-selberg-euler-factorization.md`.
