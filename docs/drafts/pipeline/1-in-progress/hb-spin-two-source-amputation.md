# HB canonical source-level spin-two amputation

- **ID:** HB-SPIN-TWO-SOURCE-AMPUTATION
- **Stage:** 1-in-progress
- **Type:** CANDIDATE / source construction
- **Objective:** unconditional RH proof/falsification through HB; this card constructs the
  angular source before divisor selection and does not claim the missing extinction law.

## Full chain

Literal theta-cusp source → Xi occurrence → retained completed spin-two source → physical
radial/left-QNM causal landing → extinction on the fixed Hawking clock → RH.
The old BM testing leg erases critical-copy source coefficients. The present construction
retains the nonzero angular coefficient through analytic external-leg cancellation instead.

## Corpus evidence

`ThetaCuspHawkingBMCompletedBalancedSpinTwoAmputationOrderNoGo` already proves
`V(u,v)=thetaXi(v)^2 * side(u,v)` and entire analyticity of `side`.
`ThetaCuspHawkingBMCompletedBalancedSpinTwoFirstLiveJet` proves nonvanishing of this side
factor at supplied Xi copies for `u=3/2`, and the exact multiplicity-matched first-live jet.
The source theorem is extended to a whole domain, with no zero copy or multiplicity in
its definition. The exact delta is global analytic uniqueness, strip-wide invertibility,
agreement with all normalized first-live jets, and the source-defined simple boundary poles.
The arguments use existing factorization, analytic uniqueness, zero-free half-planes, and
product differentiation. No claim of external mathematical novelty is made.

Whole-corpus searches include `spin two radial`, `third order source actual`, `theta source
ward`, `coefficient phase centralizer`, `spin two quotient`, `amputated source normalized`,
`projecting side factor`, `analytic quotient nonzero source`, and `XiC analytic dense nonzero`.

## Exact proposed source

For the actual repeated Eisenstein parameter `s=2`, define for every complex `z`

`U(z)=((4z²+1)(4z²+25)/32) * XiC(z-3i) * XiC(-z-3i)`.

The proposed theorem package is:

1. `U` is the unique entire function satisfying
   `V(3/2,iz)=XiC(z)^2 U(z)` everywhere.
2. In `-5/2 < Im z < 5/2`, its only zeros are `z=±i/2`. Thus `U` and its inverse are
   analytic and nonzero throughout the physical Xi strip `|Im z|<1/2`.
3. On the real axis `U(x)=P(x)*normSq(XiC(x-3i))>0`.
4. At each Xi copy, division of the first-live vertex jet by the first-live external-square
   jet equals this same predeclared `U`. No choice depending on a target response is used.
5. The unamputated vertex has exactly the original Xi zero locus in the physical strip.
6. Both fixed geometric zeros are simple. The inverse source normalization has exact
   meromorphic order `-1` there, with derivative
   `U'(z)=6z XiC(z-3i)XiC(-z-3i)` when `4z²+1=0`.

## Dependency-closed paper proof

[PROVED HERE] The existing diagonal four-Xi factorization gives the displayed product
identity, and each factor of `U` is entire. Since `XiC(0)≠0`, any other entire factor agrees
with `U` on a neighborhood of zero by scalar cancellation, hence everywhere by the identity
theorem. Off the Xi zero set it equals the ordinary quotient.

For `-5/2<Im z<5/2`, both `z-3i` and `-z-3i` have imaginary part below `-1/2`, so the
unconditional zero-free half-plane theorem makes both shifted factors nonzero. The polynomial
factor has precisely the roots `±i/2, ±5i/2`; the latter pair lies outside that open strip.
Thus `U` has no zeros in the physical strip and its reciprocal is analytic there.

For real `x`, evenness and Schwarz reality of `XiC` make the shifted factors conjugates.
Their product is a strictly positive squared norm, and the real polynomial factor is positive.
The existing product-jet formula gives `firstLiveVertexJet=firstLiveExternalSquareJet*U`;
the external-square jet is nonzero for every multiplicity, so division gives the same `U`.

Inside the physical strip, multiplication by `U` contributes zero analytic order. The vertex
therefore has exactly twice the Xi order at every point, including nonzeros. No zero-location
information disappears from the full factorization.

At a polynomial root `4z²+1=0`, the derivative of the polynomial factor is `6z`. All derivative
terms on the two shifted factors vanish because they retain the zero polynomial. Such a root
is nonzero and lies in the larger strip, so `U'` is nonzero there. The zero order is one, and
inversion gives exact pole order minus one. These poles depend only on fixed geometric boundary
points, not on any Xi zero or fitted radial target.

## Scope audit

- Ordinary pointwise division returns zero at an external zero; the desired object is its
  analytic extension. Prove extension and uniqueness explicitly.
- Keep the removed external factor in the identity. A nonvanishing quotient does not prove
  the original function nonvanishing or select its zero locations.
- No physical radial equation, causal support, left-QNM pairing, extinction, or RH is inferred
  from existence of this analytic source normalization.
- Analytic invertibility in the open strip is not bounded invertibility up to its boundary:
  the inverse has the exact geometric poles above. Their existence alone is not an RH selector.

## Tracking

- [x] Audit source factorization and prior amputation theorems.
- [ ] Complete paper proof and scratch Lean proof.
- [ ] Direct leaf check, umbrella wiring, final leaf build, all-theorem axiom audit.
- [ ] Update current route state and compact route-independent knowledge where new.
