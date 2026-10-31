# Arithmetic affine Eisenstein unfolding

- **ID:** `finite-field-eisenstein-unfolding`
- **Stage:** 1-in-progress
- **Type:** CLASSICAL BRIDGE / FORMALIZATION TARGET
- **Status:** Arithmetic product formula, analytic Euler product, additive and actual unipotent quotient probabilities, and loop Iwasawa characters formalized; arithmetic unfolding remains.
- **Completed work:** [Finite-field Weyl-sum noncancellation and arithmetic foundations](../3-formalized/finite-field-weyl-noncancellation-and-arithmetic-foundations.md).
- **Arithmetic source:** [Finite-field zeta pole transfer](../3-formalized/finite-field-zeta-pole-transfer.md).

## Exact remaining target

For the actual genus-one function field of `y²=x³−x` over `F₃`, independently
construct the arithmetic affine `SL₂` Eisenstein coset sum and prove its
constant-term identity

`∫_(U_A/(U_A∩Γ)) E_λ(h η u) du = Σ_w (hη)^(-wλ-ρ) ∏_(β∈I(w)) ζ_K(λ(β∨))/ζ_K(λ(β∨)+1)`.

Use the `KHU` convention, right arithmetic cosets `Γ/(Γ∩B)`, and
`χ=-λ-ρ`. The arithmetic group `Γ` must be the intersection of the diagonal
completed rational loop group with the restricted adelic group; the whole
rational completed loop group need not embed in that restricted product.

The left side must be defined independently of the right side. No structure
field, hypothesis, imported assumption or definition may substitute for the
missing arithmetic identification. The genus-one measure factor must follow
from a proved quotient normalization.

## Unproved dependencies

- Arithmetic coset parametrization. The independently defined actual arithmetic coset series and its right arithmetic invariance are audited. [Coset descent](../3-formalized/elliptic-eisenstein-summands-descend-to-actual-arithmetic-cosets.md). Finite root-cell parametrization and convergence remain.
- Finite root-coordinate refinement of Bruhat cells, with compatible left/right conventions.
- Local Iwasawa-character identification with the radial Haar kernel. [Finite simple loop values](../3-formalized/finite-simple-loop-iwasawa-values-are-column-norms.md) are audited: central valuation one and finite valuation equal to the first-column norm. Normalized character identification and the affine simple root remain.
- Arithmetic coset-sum convergence and justified sum/integral exchanges giving unfolding.

The simple-pole additive domain, quotient topology and covolume are formalized
and audited. The product formula now uses exactly the normalized actual
adelic completions, also with direct Lean and axiom audits.
The unordered analytic Euler product over actual closed places equals the
nonzero curve zeta function throughout `|u|<1/3`, with the same audits.
Actual idele magnitudes and their continuous complex spectral characters are
formalized and trivial on diagonal field units. Actual loop-factorization
independence and arithmetic-Borel triviality are also audited.
[Every actual idele rotates the restricted loop group](../3-formalized/actual-elliptic-ideles-rotate-restricted-loops.md), preserving Borel and both spectral coordinates, with the same audits.
[Actual degree ideles](../3-formalized/elliptic-degree-parameters-are-actual-ideles.md)
realize magnitude `3^d` and logarithmic parameter `d log 3`, with the same audits. Bruhat-coordinate
identification and unfolding remain unproved targets.

The full coefficient-integral local loop group satisfies `K∩B=B(O)`.
Actual `KHU` decomposition, both torus valuation invariances and the exact
unipotent coefficient-integrality criterion are audited in
`IntegralLoopBorelIntersection`.

## Actual unipotent quotient

Order free coefficients as `b₀,c₁,a₁,b₁,c₂,a₂,…`. Multiplication defects
use only earlier coordinates. Recursive right rational correction places
every coordinate uniquely in the additive domain and preserves one common
finite exceptional-place set. The uniform coefficient group is isomorphic
to the actual restricted unipotent carrier, and its rational subgroup is
exactly the actual arithmetic intersection.

The literal quotient, with its coefficient quotient topology, is
homeomorphic to the countable product of additive domains. Triangular
normalization preserves product Haar probability; its transfer is invariant
under actual quotient left multiplication. All statements passed direct
Lean and axiom audits. [Proof and declarations](../3-formalized/actual-elliptic-unipotent-quotient-has-invariant-probability.md).

This provides the quotient measure. [Scalar additive periodization](../3-formalized/elliptic-additive-haar-periodizes-over-the-actual-function-field.md)
over the actual function field is also audited, including nonnegative Tonelli
unfolding. [Actual local Haar moduli](../3-formalized/elliptic-local-haar-moduli-equal-normalized-magnitudes.md)
equal the normalized finite-place and infinity magnitudes. The
[actual local radial spectral integrals](../3-formalized/actual-elliptic-local-spectral-characters-have-exact-integrals.md)
have their exact residue factors for `Re(s)>0`. Both passed direct Lean
and axiom audits. Relative finite-cell periodization and the identification of local-integral products with the actual adelic integral
remain necessary for unfolding.

## Convergence mechanism to test

Unfold the nonnegative real-parameter series with Tonelli before claiming
convergence. If the arithmetic cells give the proved convergent Weyl sum,
its finite integral forces almost-everywhere summability on the unipotent
quotient. Absolute values at complex parameters are bounded by the
corresponding real-parameter series, giving the required integral exchange.
The arithmetic cell decomposition and local-character identity remain
necessary; this does not prove pointwise convergence everywhere.

## Established boundary

The complete infinite Weyl sum already has exact eventual noncancellation,
simultaneously for both Frobenius indices at sufficiently large parameters
`R=d log 3`. This does not identify it with an Eisenstein constant term.
Ambient adelic Haar measure, finite strong approximation, actual local integrals,
and principal ideal norms also do not by themselves prove unfolding.
A continued constant term would not by itself construct meromorphic continuation
of the full Eisenstein family.

## Literature audit

Primary source: Lee–Lombardo,
[Eisenstein series on affine Kac–Moody groups over function fields](https://arxiv.org/pdf/1208.4006),
§§2–7 and Appendix A. Verdict: **BRIDGE**; no novelty claim.
