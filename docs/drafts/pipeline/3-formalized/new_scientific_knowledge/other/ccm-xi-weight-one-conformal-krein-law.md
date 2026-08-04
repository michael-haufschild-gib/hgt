# CCM--Xi weight-one conformal Krein law

- **ID:** `ccm-xi-weight-one-conformal-krein-law`
- **Stage:** 3-formalized
- **Type:** universal law / sharp positivity classification
- **Parents:**
  - `../../not_new_scientific_knowledge/ccm-clifford-weil-matrix-bridge.md`;
  - `../../not_new_scientific_knowledge/ccm-closed-xi-haar-mellin-realization.md`.
- **Scientific status:** `[LEAN-FORMALIZED] [NOVELTY PROVISIONAL] [NOT AN RH PROOF]`

## Universal theorem

Let `J rho = 1-conj(rho)` be critical-line reflection, let

```text
m_c(rho)=exp(-rho log|c|)
```

be the Haar--Mellin character of a class-space section, and let

```text
Q(x,y)=sum_rho E(x)_rho conjugate(E(y)_(J rho))
```

be the multiplicity-exact closed-CCM Weil pairing. Then

```text
m_c(rho) conjugate(m_c(J rho)) = exp(-log|c|)=|c|^(-1),       (1)
Q(L_c x,L_c y)=|c|^(-1) Q(x,y).                               (2)
```

The factor is positive and independent of `rho`, its height, multiplicity, and horizontal
displacement. Hence every simultaneous Lefschetz orbit has constant Krein sign. Clifford phases
cancel in the bivariant product, but no scalar phase or same-section Mellin translation can turn a
negative Weil direction into a positive one.

More generally, for a divisor stable under `rho |-> w-conj(rho)`, Mellin character
`exp(-rho t)`, and the corresponding reflected pairing, simultaneous translation has conformal
weight `exp(-w t)`. The Xi/CCM law is the weight-one case `w=1`.

## Proof

Put `t=log|c|`. Critical-line reflection gives `J rho=1-conj(rho)`, so

```text
m_c(rho) conjugate(m_c(J rho))
 = exp(-rho t) exp(-conj(J rho)t)
 = exp(-rho t) exp(-(1-rho)t)
 = exp(-t).
```

Haar--Mellin covariance on the literal closed quotient gives
`E(L_c x)_rho=m_c(rho)E(x)_rho`. Substitute this in every summand of `Q`, apply `(1)`, and pull the
constant through the absolutely convergent sum. Since `t` is real,
`exp(-t)=Real.exp(-t)>0`; taking real parts proves exact sign invariance.

## Non-circular positivity and sharpness

On the multiplicity Hilbert carrier let `J` also denote the linear isometric involution induced by
critical-line reflection. For every vector `v`, define

```text
v_plus  = v + Jv,
v_minus = v - Jv.
```

Then, without any zero-location hypothesis,

```text
Q(v_plus,v_plus)   = ||v_plus||^2 >= 0,                       (3)
Q(v_minus,v_minus) = -||v_minus||^2 <= 0,                     (4)
Q(v,v) = (||v_plus||^2-||v_minus||^2)/4.                      (5)
```

Thus the reflection-even channel supplies a genuine non-circular positive Weil sector, while the
reflection-odd channel is exactly negative. Full scalar positivity is equivalent to domination of
odd energy by even energy on the realized test space. Equations `(2)`--`(5)` prove that the
class-space flow and Clifford phase correction preserve this ratio; they cannot prove that
domination. Any full RH route must add a source-derived non-diagonal mechanism that kills or shorts
the odd channel before scalarization.

This sector is realized by an explicit operation on tests, not merely by abstract carrier vectors.
For every square-summable test `F`, put

```text
F_plus(z) = F(z) + F(conjugate(z)).
```

Then `F_plus` is square-summable and its multiplicity-exact Weil square satisfies

```text
xiWeilPolarization(F_plus,F_plus)
  = ||E(F) + J E(F)||^2 >= 0.                                 (6)
```

Equation `(6)` is a direct unconditional Weil-form positivity theorem on a canonical, explicitly
described test sector. It uses neither RH nor positivity of the unrestricted Weil form.

The exact remaining bridge can now be stated without the word "positivity."  If `E(F)` is the
multiplicity-exact evaluation packet, then

```text
RH
  iff ||E(F)-J E(F)||^2 <= ||E(F)+J E(F)||^2
      for every square-summable F.                            (7)
```

Thus a future source-geometric construction has one auditable obligation: prove even-channel
energy dominance on the realized image. Gram positivity, Clifford phase cancellation, and
class-space translation cannot substitute for `(7)`.

## Hostile audit

- `(1)`--`(6)` contain no RH, zero-reality, Weil-sign, density, or source-effectivity premise.
- `(7)` is an equivalence classifier, not a claimed proof of its right-hand side.
- Matrix Gram positivity is not used to infer positivity of its Clifford supertrace.
- The positive theorem is exactly scoped to the reflection-even sector; no claim is made that all
  CCM evaluation packets lie there.
- The law is a no-theatre classifier: scalar phases and Mellin flow are now proved incapable of
  supplying missing full-domain sign.
- External novelty remains to be checked; abstract Krein even/odd decomposition is classical, but
  exact weight-one conformal covariance on the literal closed CCM--Xi pairing may be new.

## Gates

- [x] dependency-closed paper proof
- [x] exact literal recipient
- [x] non-circular positivity theorem
- [x] sharp negative-channel theorem
- [x] RH circularity audit
- [x] unconditional Lean verification
- [ ] independent novelty audit
