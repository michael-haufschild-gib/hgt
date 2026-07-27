# High-shell completion-stable polarization creator

- **ID:** `high-shell-completion-stable-polarization-creator`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / RH source-creator search
- **Source:** publication-ready positive shell frame, universal orientation law, and fixed-width
  Weil source spectrum
- **Statement:** Find a source-defined, shell-label-preserving polarized completion whose
  reflection defect is forced to vanish at every Xi divisor point without assuming Weil
  positivity, reflection unitarity, or any equivalent form of RH.

## Goal

The positive shell paper supplies pairwise-disjoint positive Dirichlet sources

```text
S_m(s)=Xi(s) H_m(s) / c_infinity(s),
H_m(s)=1/zeta((m+1)s)-1/zeta(ms),
```

with the full strict-right Xi divisor and maximal relative differential rank.  The universal
orientation paper says an RH-capable carrier must retain four coupled layers:

1. ordered hypertranscendental tail constraints;
2. positive source pointing;
3. a radial self-adjoint Hankel polarization;
4. a reflection-odd defect.

The first three layers can be placed on the shell family.  The open core is a **creator theorem**:
derive the vanishing or nonexpansivity of the fourth layer from the completed Euler--Gamma source
itself.  Merely defining a defect that vanishes exactly on the critical line is not progress.

## Gates

- [x] 0 → 1 in-progress: source-pure family, exact candidate invariant, and hostile circularity
  tests identified
- [ ] 1 → 2 fully-proven: dependency-closed creator/saturation theorem with no RH-equivalent
  premise
- [ ] 2 → 3 formalized: exact creator theorem in Lean, direct check, final module build and axiom
  audit
- [ ] 3 → 4 publication-ready: independent novelty review and standalone proof

## Exact unconditional shell coordinates

For `m >= 2` and `Re(s)>1/2`, absolute convergence gives

```text
H_m(s)
 = -sum_(n>=2) mu(n)(1-n^(-s))n^(-m s).                         (1)
```

At a Xi zero `rho` of order `d`,

```text
(Xi H_m)^(d)(rho)/Xi^(d)(rho)=H_m(rho).                         (2)
```

The already formalized prime-two domination implies

```text
lim_(m→infinity) |H_(m+1)(rho)/H_m(rho)|=2^(-Re(rho)).           (3)
```

Thus the divisor-normal shell profile unconditionally reconstructs each zero's horizontal
coordinate.  This is divisor-sensitive and stronger than a yes/no restatement, but it does not
constrain that coordinate.

## Squarefree Möbius--Szegő lift

Put

```text
v_m(s;n)=mu(n)(1-n^(-s))n^(-m s),  n>=2,
Q(u)=sum_(n>=1)mu(n)^2 n^(-u)=zeta(u)/zeta(2u).
```

For `m,k>=1`, `Re(s),Re(t)>1/2`, the Gram is the positive four-term mixed difference

```text
<v_m(s),v_k(t)>
 = Q(ms+k conjugate(t))
 - Q((m+1)s+k conjugate(t))
 - Q(ms+(k+1)conjugate(t))
 + Q((m+1)s+(k+1)conjugate(t)).                          (4)
```

Shell-tail fusion telescopes coordinatewise:

```text
sum_(m>=M) (1-n^(-s))n^(-m s)=n^(-M s),
||sum_(m>=M) v_m(s)||^2=Q(2M Re(s))-1.                          (5)
```

The diagonal in `(5)` is strictly decreasing in `Re(s)`.  Hence

```text
||tail_M(rho)||=||tail_M(1-conjugate(rho))||
  iff Re(rho)=1/2.                                               (6)
```

### Hostile verdict

Equations `(4)`--`(6)` are dependency-closed, but formalizing them now would be theatre.  The
corpus already has a stronger all-prime Hilbert seam whose prime-two coordinate detects the same
horizontal displacement.  The squarefree lift becomes significant only if a new theorem forces
the reflected equality from source completion.

## Fixed-width tomography amplification attack

Every high completion `X_m=Xi H_m` has the same Xi zero divisor.  It is tempting to apply the
fixed-width Weil detector to all disjoint shell sources and amplify one common off-line negative
mode against orthogonal source budgets.

This shortcut fails at its first exact interface:

```text
-X_m'/X_m = -Xi'/Xi - H_m'/H_m.                                (7)
```

The zero-side detector is common, but the prime side of the explicit formula uses logarithmic
derivatives.  The terms `H_m'/H_m` are neither coefficient-disjoint nor orthogonal shell sources.
Moreover `X_m` is not functional-equation invariant.  Treating the common zero contribution as
many independent negative modes while dropping `(7)` double-counts one divisor and is invalid.

**Positive survivor:** any valid amplification must be performed before the fixed-current
quotient by an operator that retains the shell label through both the Euler pole cancellation
and the regular multiplier current.  A scalar codiagonal is already known to be nonclosable.

## Occupation determinant and low-jet no-go

The publication-ready multiple-elliptic-Gamma paper supplies canonical determinants for every
occupation sector retaining the one-particle states.  That construction does not recover the
missing creator.

For a finite prime set `P`, the bosonic occupation moments are

```text
M_k(P,s)=product_(p in P)(1-p^(-ks))^(-1)=zeta_P(ks).
```

After all-prime completion, let `T_s=diag(n^(-s))`.  Whenever `q Re(s)>1`, the intrinsic
regularized determinant has germ

```text
log det_q(I-xT_s)=-sum_(k>=q) zeta(ks)x^k/k.                    (7a)
```

Hence every derivative of order below `q` vanishes identically.  In the strict right critical
half-strip the minimal admissible genus is `q=2`, so

```text
partial_x det_2(I-xT_s)|_(x=0)=0
```

for every `s`, while the first surviving coefficient at a zeta zero `rho` is
`-zeta(2rho)/2`, which is nonzero because `Re(2rho)>1`.

Recovering the ordinary determinant germ requires the explicit counterterm

```text
exp(-sum_(k<q) zeta(ks)x^k/k).                               (7b)
```

For `q=2`, `(7b)` reinstates `exp(-zeta(s)x)`, so the first derivative vanishes at a zeta zero
only because the deleted source moment was inserted by hand.  Genus one is trace class only for
`Re(s)>1`, where zeta has no zeros.  The exact scheme-change law therefore gives:

```text
scheme-independent x-divisor = {n^s : n>=1}, zeta-zero blind;
zeta-zero-sensitive low jets = scheme-dependent counterterms. (7c)
```

The occupation-sector universality theorem makes this obstruction statistics-independent:
retaining the one-particle sector never improves the minimal genus.  Unpointed Morse germs do not
help, since the holomorphic Morse lemma makes all nondegenerate one-variable germs locally
equivalent.

**Positive survivor.**  Zeta-zero information is localized exactly in the low spectral moments
deleted by the admissible determinant regularization.  Any completion-stable invariant must retain
those moments as a polarized relative class rather than restore them by a scalar counterterm.
This information-localization law is exact but standard/bridge-level; formalizing it alone would
be theatre.

## Canonical-product phase audit

The tempting integer-temperature conjecture was already proved by Bank in 1980: the canonical
product with zeros `n^p` is DA for even `p` and HT for odd `p`.  It is therefore
`[REDISCOVERED]`, not frontier mathematics.

The stronger rational completion law does survive:

```text
product_(j=0)^(q-1) W_(p/q)(omega_q^j z)
  =W_p((-1)^(q+1)z^q).
```

It proves HT of `W_(p/q)` for every reduced rational with odd numerator and makes the cyclic norm
DA exactly for even numerator.  Complete proof and literature boundary:

`../2-fully-proven/new_scientific_knowledge/rational-power-canonical-product-cyclic-norm-law.md`.

This advances general HT theory but is not yet the creator in this card.  The live mathematical
boundary has now narrowed further.  Barnes' zeta-valued asymptotic tail, combined with the
Sibuya--Ramis exact Gevrey-slope theorem, proves:

```text
s positive irrational  ->  W_s is HT over C(z).
```

Complete proof and literature boundary:

`../2-fully-proven/new_scientific_knowledge/irrational-power-canonical-products-hypertranscendental-by-gevrey-slope-rigidity.md`.

The only unresolved positive real factors are reduced rationals `p/q` with even numerator and
`q>1`.  Nonreal exponents remain a separate open core; their logarithmic-spiral divisor has an
infinite monodromy orbit.

## Candidate creator interface

Let `F_m` denote a completed source realization of the positive coefficient shell and let
`U_FE` be the actual Poisson/Mellin functional-equation transform on a rigged source space.  Seek
a closed operator-valued graph satisfying all of:

```text
1. shell labels remain orthogonal on the source side;
2. codiagonal(F_m) is the full theta/zeta source;
3. U_FE acts before codiagonalization and preserves the graph norm;
4. the divisor-normal readout is the tail vector in (5);
5. graph symmetry forces its reflection-odd norm defect to vanish at Xi zeros.       (8)
```

Conditions 3 and 5 are the unknown theorem.  Declaring `U_FE` unitary on the divisor-normal
readout, assuming a source-to-Xi Pick contraction, or assuming Weil positivity would insert RH
at the seam.

## Novelty and significance status

- `(1)`--`(6)`: exact synthesis not found verbatim in preliminary searches, but elementary and
  dominated by existing corpus seam laws; **not significant frontier movement alone**.
- `(7)`: closes the naive fixed-width amplification.
- `(8)`: genuinely RH-capable open core.  No creator theorem is currently proved.

## Log

- 2026-07-27 — Audited all sixteen publication-ready papers.  Combined the high-shell divisor
  frame with the four-layer orientation requirement and fixed-width global tomography.
- 2026-07-27 — Derived the squarefree Möbius--Szegő Gram and exact tail norm, then rejected it as
  standalone progress because the corpus already contains a stronger prime-two-faithful seam.
- 2026-07-27 — Rejected naive repeated-Weil amplification: logarithmic differentiation destroys
  shell orthogonality through `H_m'/H_m`, and the shell completions are not FE invariant.
- 2026-07-27 — Proved the determinant low-jet no-go: admissible regularization deletes exactly
  the zeta-zero-sensitive moments, while restoring them uses explicit scheme counterterms.
- 2026-07-27 — Bank's integer theorem killed the integer-temperature novelty claim.  The exact
  rational cyclic norm and odd-numerator HT extension survived and were paper-proved separately.
- 2026-07-27 — Closed the irrational real family: the zeta tail has exact irrational Gevrey
  order, impossible for a divergent formal solution of an analytic ADE by Sibuya--Ramis.
