# Arithmetic affine Eisenstein unfolding

- **ID:** `finite-field-eisenstein-unfolding`
- **Stage:** 0-backlog
- **Type:** CLASSICAL BRIDGE / FORMALIZATION TARGET
- **Status:** Unproved target; no active implementation. Existing drafts were closed at the user's request.
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

- Actual additive quotient fundamental domain and covolume; unipotent quotient measure.
- Finite-place product formula and full curve/closed-point Euler product.
- Actual adelic loop group, arithmetic cosets, Iwasawa characters and torus normalization.
- Finite root-coordinate refinement of Bruhat cells, with compatible left/right conventions.
- Local Iwasawa-character identification with the already proved radial Haar kernel.
- Arithmetic coset-sum convergence and justified sum/integral exchanges giving unfolding.

These are targets, not paper proofs. The former fundamental-domain, Bruhat-coordinate
and global-product-formula sketches have been withdrawn as proof claims. They are
not counted as completed results or left as unformalized proofs.

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
§§2–7 and Appendix A. Verdict: **BRIDGE**; no novelty claim. This backlog target
is not scheduled or active, and no further proof branch was started during closure.
