# Arithmetic affine Eisenstein unfolding and surviving zeta poles

- **ID:** `finite-field-eisenstein-unfolding`
- **Stage:** 1-in-progress
- **Type:** FORMALIZATION PROGRAMME / CLASSICAL BRIDGE
- **Source:** [finite-field-zeta-pole-transfer](../3-formalized/finite-field-zeta-pole-transfer.md).
- **Target:** Construct the arithmetic affine `SL₂` Eisenstein series over the actual genus-one
  function field of `y²=x³−x` over `F₃`, prove its constant-term unfolding, and prove that
  the arithmetic zeta poles survive the infinite Weyl sum at actual degree rotations.

## Exact scope

Use the existing actual function field, not a complex function field. Keep the infinite
untwisted affine `A₁` Weyl group and the centrally extended loop group. The arithmetic
series must be a sum over arithmetic Borel cosets, defined independently of its proposed
constant term. No interface may assume Iwasawa decomposition, local intertwining integrals,
Euler products, convergence, unfolding, or noncancellation.

With `λ=−(χ+ρ)`, the Godement chamber is `Re λ₀, Re λ₁>1`. The expected identity is

`∫_(U(A)/U(F)) E_λ(h η u) du = Σ_w hη^(−wλ−ρ) ∏_(β∈I(w)) ζ_F(λ(β∨))/ζ_F(λ(β∨)+1)`.

The genus factor is one because the source curve has independently proved genus one.
The measure must be the actual invariant probability measure; the right side is not a
definition of the left side.

Noncancellation is a generic or existence claim, not a claim at every torus point. Fix
an actual arithmetic pole `s₀` of `c(s)=ζ_F(s)/ζ_F(s+1)`, its order `−m`, and the
spectral slice `λ(s)=(4−s,s)`. All other positive-root arguments have real part greater
than one near `s₀`, since `Re s₀=−1/2`. At trivial finite/central torus coordinates,
translation index `n` has degree factor `exp(−R(4n²+ns))`. Only identity and finite
simple reflection have index zero. After multiplication by `(s−s₀)^m`, the identity
term vanishes at `s₀`, the simple reflection contributes a nonzero leading coefficient,
and the other terms tend to zero as `R→∞`. Prove uniform analytic convergence of the
regularized sum and this limit; conclude exact order `−m` for all sufficiently strong
actual degree rotations. Exchange the simple roots for the second direction.

A pole of the continued constant term is not by itself a construction of meromorphic
continuation of the full Eisenstein family. Track this distinction explicitly.

## Internal frontier

- The source function field, genus, all extension point counts, zeta series and rational
  continuation are formalized. Exact pole multiplicities and simple affine coefficient
  formulas are formalized and audited.
- The rational-field affine Weyl sum has absolute convergence via quadratic degree decay;
  this supplies reusable combinatorics, not the finite-field arithmetic unfolding.
- Existing loop-group sources construct the actual Laurent central extension, root
  splittings, degree rotation, simple coroots, positive-loop splitting, and field maps.
- The arithmetic series, finite-field adelic quotient measure, Iwasawa/Bruhat integration,
  and full-sum noncancellation are not supplied by the preceding card.

## External audit and research gates

Primary source: Lee–Lombardo, *Eisenstein series on affine Kac–Moody groups over
function fields*, <https://arxiv.org/pdf/1208.4006>, especially §§2–7 and Appendix A.
Unfolding and meromorphic continuation of the constant term are classical. Verdict:
**BRIDGE**. This task requests proof and formalization of that theorem; a novelty claim
would be false. Audit descendants for precise continuation and pole-survival scope.

Competing assertions to attack: (1) every coefficient pole survives at every torus point;
(2) only generic survival holds; (3) degree rotation isolates a nonzero leading residue.
The third is the selected exact target. Do not infer noncancellation from termwise poles.

## Gates

- [x] Exact arithmetic source and intended group fixed.
- [ ] Complete internal and external dependency audit.
- [ ] Dependency-closed paper proof of analytic noncancellation.
- [ ] Lean proof of the exact full-sum pole theorem.
- [ ] Actual finite-field arithmetic series and convergence.
- [ ] Actual unipotent quotient measure and local/global intertwining integrals.
- [ ] Dependency-closed paper proof of arithmetic unfolding.
- [ ] Lean unfolding, final source checks, and transitive axiom audit.

## Open core

Construct and discharge the arithmetic definitions and integration theorems. For analytic
noncancellation, prove coefficient bounds uniform near `s₀`, locally uniform convergence
after removal of the one singular factor, and a nonzero limiting Laurent coefficient.
No completed sublemma closes this programme; both requested theorems remain required.
