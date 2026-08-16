# Semilocal prolate control deformation

- **ID:** semilocal-prolate-control-deformation
- **Stage:** 3-formalized
- **Type:** EXACT REDUCTION / BRIDGE (paper)
- **Scientific status:** NOT NEW SCIENTIFIC KNOWLEDGE
- **Source:** Connes--Consani--Moscovici, *Zeta zeros and prolate wave operators*,
  arXiv:2310.18423v2, Sections 4.3--4.4

## Statement

For a one-prime enlargement, let

`W_(lambda,p)^cyc=-D_p^2+lambda^2N_p`

be the source formal cyclic-pair prolate candidate. Let `theta_p` be the exact Sonin isomorphism and
define the transported control

`W_(lambda,p)^theta=theta_pW_(lambda,infinity)theta_p^(-1)`.

Since `theta_p` intertwines the scaling generator, define the pure grading deformation

`K_p=N_p-theta_pN_infinitytheta_p^(-1)`.                   (1)

Then as an identity of formal grading expressions,

`W_(lambda,p)^cyc=W_(lambda,p)^theta+lambda^2K_p`.          (2)

There is no natural common algebraic core on which (2) is presently an operator identity. The cyclic
core and transported core intersect only at zero by `semilocal-prolate-core-disjointness.md`.

Suppose a new source-selected common graph/boundary realization is constructed which makes (2) a
valid closed perturbation identity at a nonreal common resolvent parameter `z`. Write its resolvent as
`R_cyc(z)` and the transported-control resolvent as `R_theta(z)`. The second resolvent identity gives

`R_cyc(z)-R_theta(z)
 =-lambda^2R_cyc(z)K_pR_theta(z)`.                          (3)

Consequently the exact cyclic relative-resolvent Sonin corner splits as

`C_cyc(z)=C_theta(z)
 -lambda^2(1-Q_p)R_cyc(z)K_pR_theta(z)eta_pQ_infinity`,     (4)

where `C_theta(z)` is the nonzero trace-class corner constructed in
`transported-prolate-relative-resolvent-corner.md`.

Thus, conditional on first solving the common-domain problem, every unresolved analytic and arithmetic
issue in the genuine semilocal candidate is carried by the single deformation `K_p` and the correction
term in (4).

## Proof

The source maps `eta_p` and `theta_p` both intertwine the scaling action at the formal level. Hence

`theta_pD_infinitytheta_p^(-1)=D_p`.

Conjugating the archimedean formal prolate expression gives

`W_(lambda,p)^theta=-D_p^2+lambda^2theta_pN_infinitytheta_p^(-1)`.

Subtracting the formal expressions proves (2). This subtraction is not yet an operator-domain
statement. Under the explicit common-realization hypothesis, equation (3) is the standard second
resolvent identity applied to (2). Finally

`R_cyc eta_p-eta_pR_infinity
 =(R_theta eta_p-eta_pR_infinity)+(R_cyc-R_theta)eta_p`.

Compressing by the two Sonin projections and inserting (3) proves (4).

## Route consequence

- `[PROVED]` The transported control and the arithmetic semilocal candidate differ formally only in
  their grading, not in the scaling-square term.
- `[PROVED OBSTRUCTION]` Their natural cores are disjoint, so this formal difference is not a
  densely-defined perturbation until a new common graph domain is constructed.
- `[PROVED]` The cofinally nonzero trace-class control corner is a fixed baseline. Any failure of the
  genuine candidate is caused by lack of a closed realization for `K_p`, failure of Schatten control
  for the correction, or exact cancellation in (4).
- `[OPEN CORE]` Construct a new common graph/boundary relation; only then prove that
  `K_pR_theta(z)` is relatively controlled or belongs to a stated operator ideal and determine the
  compressed correction.
- `[OPEN CORE]` Exclude exact cancellation of `C_theta(z)` by a source sign, spectral separation, or
  a nonzero two-place boundary. Without this, nonvanishing of the control model does not transfer.
- `[LIMIT]` Equation (2) is formal until the domain of the cyclic prolate operator is constructed.
  The reduction does not assume that missing conclusion.

## Lean formalization

`formal/GaloisForLFunctions/RHTower/SemilocalProlateControlDeformation.lean`

The card's proved content is exactly ring algebra in an associative `ℂ`-algebra: the analytic
content is the *hypothesis* that a common closed realization exists, and the Lean statements carry
it as the explicit two-sided resolvent hypotheses `R (W - z) = 1`, `(W - z) R = 1`.

| Card claim | Lean declaration |
|---|---|
| `θ_p D_∞ θ_p^{-1} = D_p` ⟹ `W^θ_{λ,p} = -D_p² + λ² θ N_∞ θ^{-1}` | `conj_prolate` (with `conj_mul`, `conj_smul`) |
| `K_p = N_p - θ N_∞ θ^{-1}` | `gradingDeformation` |
| **(2)** `W^cyc = W^θ + λ² K_p` | `cyclic_eq_transported_add_deformation` |
| **(3)** `R_cyc - R_θ = -λ² R_cyc K_p R_θ` | `second_resolvent_identity` |
| the corner `C(z) = (1-Q_p)(R η_p - η_p R_∞) Q_∞` | `relativeCorner` |
| **(4)** `C_cyc = C_θ - λ² (1-Q_p) R_cyc K_p R_θ η_p Q_∞` | `relativeCorner_split` |

The `[OPEN CORE]` items (constructing a common graph/boundary relation, Schatten control of the
correction, and exclusion of exact cancellation) are explicitly open research and are not part of
the proved theorem; `[LIMIT]` is respected because identity (4) is stated only under the resolvent
hypotheses.

All declarations audited with `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`.

## Novelty audit

This is the second resolvent identity applied after a source change of coordinates. It is the exact
remaining Route B equation, but it is a reduction rather than new scientific knowledge.
