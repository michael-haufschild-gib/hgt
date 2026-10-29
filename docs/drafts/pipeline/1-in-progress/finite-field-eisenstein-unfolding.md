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

`∫_(U_A/(U_A∩Γ_F)) E_λ(h η u) du = Σ_w hη^(−wλ−ρ) ∏_(β∈I(w)) ζ_F(λ(β∨))/ζ_F(λ(β∨)+1)`.

The genus factor is one because the source curve has independently proved genus one.
The measure must be the actual invariant probability measure; the right side is not a
definition of the left side.

Here `Γ_F` is the intersection of the diagonal image of the completed rational loop
group with the restricted adelic group. Lee–Lombardo §3.5 explicitly shows that the
whole rational loop group need not embed in the restricted product. The intersection
cannot be replaced by the full rational group without proof.

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

## Dependency-closed analytic Weyl-sum proof `[PROVED HERE]`

This section proves the analytic noncancellation statement for the actual affine
zeta-product expansion. It does not supply the separate arithmetic unfolding.

Put `t(s)=3^(−s)`,
`N(s)=(1−t(s)/3)P(t(s))`, and
`Q(s)=(1−3t(s))P(t(s)/3)`.
The reduced factor `N/Q` agrees with `c(s)` wherever `t(s)≠1`; at the exceptional
points it represents the same meromorphic germ. Both `N` and `Q` are entire.
For an arithmetic pole `s₀`, the prior root-order theorem gives `ord Q=m>0`, and
`N(s₀)≠0`: `P(t(s₀))≠0` by the two disjoint root circles, while `t(s₀)/3≠1`.

Use the connected strip `S={s:−1<Re s<2}` and `λ(s)=(4−s,s)`.
A positive root other than `α` has argument `4n+s` with `n≥1`, or `4n−s`
with `n≥1`; both have real part greater than two throughout `S`.
On `Re z≥2`, `|t(z)|≤1/9`. The reduced rational zeta quotient is analytic on
a neighborhood of that closed disk: its possible poles have moduli `1/3` and
`√3`. Compactness gives a constant `M≥1` bounding all these other root factors.
On `S`, `|t(s)|≤3`; compactness of the radius-three disk bounds `|N(s)|` and
`|Q(s)|` by one fixed `K≥1`.

Define a regular coefficient `A_w(s)` as follows. If `α∈I(w)`, replace its factor
`c(s)` by `N(s)` and retain all other factors. If `α∉I(w)`, multiply the coefficient
by `Q(s)`. These are holomorphic on `S` and satisfy
`|A_w(s)|≤K M^(#I(w))`. Their two index-zero values are `Q(s)` for the identity
and `N(s)` for the finite simple reflection. Whenever `Q(s)≠0` and `t(s)≠1`,
`A_w(s)=Q(s)c_w(λ(s))` term by term.

For both dihedral families indexed by `n∈Z`, the degree exponent at trivial finite
and central torus coordinates is `−R(4n²+ns)`. Since `|Re s|≤2` on `S` and
`|n|≤n²` for integral `n`, its real decay is at least `2Rn²`.
Also `#I(w)≤2|n|+1`. Thus, for every fixed `R>0`,

`|A_w(s) exp(−R(4n²+ns))| ≤ K M^(2|n|+1) exp(−2Rn²)`.

This bound is summable in `n`: writing `M^x=exp(x log M)`, complete the square
and dominate by a constant times `exp(−|n|)`. The Weierstrass theorem makes the
regularized sum `H_R(s)=Σ_w A_w(s)exp(−R(4n²+ns))` holomorphic on `S`.
Consequently `H_R/Q` is meromorphic there. On `1<Re s<2` every original term is
in the Godement chamber, and absolute convergence allows the factor `Q` to pass
through the sum. Hence this quotient is the meromorphic continuation of that full
Weyl expansion on the slice, rather than a newly chosen unrelated function.

For `R≥1`, the same majorant with `R=1` is independent of `R`. Every term with
`n≠0` tends to zero as `R→∞`; the two index-zero terms remain `Q(s)+N(s)`.
Dominated convergence for the counting measure therefore gives
`lim_(R→∞) H_R(s₀)=N(s₀)≠0`. Continuity of the norm gives an `R₀` such that
`H_R(s₀)≠0` for every `R≥R₀`. The local quotient order is then exactly `−m`.
In particular this holds along `R=d log 3` for all sufficiently large integers `d`.
The projective rational point at infinity supplies the degree-one place required to
realize those rotations; constructing that place in the adelic model remains part of
the separate arithmetic construction, not an input assumed by the analytic theorem.

This proves survival for every actual arithmetic root copy, with multiplicity. It
makes no claim that no exceptional smaller rotations or torus values can cancel a
leading coefficient. All analytical inputs above are the already proved polynomial
root circle, finite inversion sets, elementary compactness, holomorphic uniform-limit
theory, and dominated convergence. No arithmetic unfolding theorem is used.
