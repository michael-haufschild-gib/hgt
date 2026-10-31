# Arithmetic affine Eisenstein unfolding

- **ID:** `finite-field-eisenstein-unfolding`
- **Stage:** 1-in-progress
- **Type:** CLASSICAL BRIDGE / FORMALIZATION TARGET
- **Status:** Arithmetic product formula, analytic Euler product and normalized additive quotient formalized; actual idele characters formalized; loop-character and unfolding bridges remain.
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

- Unipotent quotient measure. The additive quotient has Haar probability and covolume one. Its continuous additive retraction and rational correction preserving every integral finite place are audited. The three-free-entry equivalence is audited over arbitrary commutative rings, including the adele ring; completed arithmetic reduction and invariant quotient probability remain.
- Arithmetic cosets, Iwasawa spectral characters and their torus normalization. The actual restricted adelic loop group, faithful restricted arithmetic embedding and integral–Borel factorization are audited.
- Finite root-coordinate refinement of Bruhat cells, with compatible left/right conventions.
- Local Iwasawa-character identification with the already proved radial Haar kernel.
- Arithmetic coset-sum convergence and justified sum/integral exchanges giving unfolding.

The simple-pole additive domain, quotient topology and covolume are formalized
and audited. The product formula now uses exactly the normalized actual
adelic completions, also with direct Lean and axiom audits.
The unordered analytic Euler product over actual closed places equals the
nonzero curve zeta function throughout `|u|<1/3`, with the same audits.
Actual idele magnitudes and their continuous complex spectral characters are
formalized and trivial on diagonal field units. Loop-factorization independence,
Bruhat-coordinate identification and unfolding remain unproved targets.

For local Iwasawa uniqueness, the integral-vertex target is
`P₀(O)∩B=P₁(O)∩B=B(O)`, with integral finite/affine rank-one
factorizations inside each vertex. The existing
`subgroup_join_base_or_alternating` and
`alternating_simpleMatrixWord_not_mem_iwahori` would then give
`⟨P₀(O),P₁(O)⟩∩B=B(O)`. Both torus coordinates of `B(O)` must be
proved to have valuation one, including the central coordinate.
Both integral vertex identities passed direct Lean and transitive axiom audits in
`IntegralAdjacentVertex`. The generated-group intersection, actual `KHU` decomposition, both torus
valuation invariances and the exact unipotent coefficient-integrality criterion
are audited in `IntegralLoopBorelIntersection`.

## Unipotent reduction mechanism

Order free matrix coefficients as `b₀,c₁,a₁,b₁,c₂,a₂,…`.
The three multiplication defects are
`(a−1)B+b(D−1)`, `c(A−1)+(d−1)C`, `(a−1)(A−1)+bC`.
Their zero constant terms make each defect depend only on earlier free
coefficients. The fourth entry through degree `n` uses `a,c` through `n`
and `b` below `n`.

Recursive right multiplication by rational coefficients should place every
coordinate in the compact additive domain. The audited additive correction
preserves a common finite exceptional-place set. Uniqueness follows from the
trivial intersection of the diagonal field with the additive domain.
Finite triangular translations then supply the proposed invariant quotient
probability. The free coefficient stream, finite coefficient dependence and countable
triangular probability theorem are audited. The full stream multiplication law,
recursion and quotient identification still require Lean proofs.

## Convergence mechanism to test

Unfold the nonnegative real-parameter series with Tonelli before claiming
convergence. If the arithmetic cells give the proved finite Weyl sum,
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
