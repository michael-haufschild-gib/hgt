# Polygamma--Hurwitz value bridge

- **ID:** `polygamma-hurwitz-value-bridge`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scientific status:** `[SEARCH] [BRIDGE] [FORMALIZATION] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** Every positive-order polygamma value on the open right half-plane is exactly an
  integer-exponent value of the project's complex-shift Hurwitz zeta.

## Exact relation

For every `m >= 0` and `Re z > 0`,

```text
psi^(m+1)(z) = (-1)^(m+2) (m+1)! hzeta(m+2,z).             (1)
```

In particular,

```text
psi'(z) = hzeta(2,z).                                      (2)

hzeta(2,1) = pi^2/6,     hzeta(2,1/2) = pi^2/2.           (3)
```

The base and shift relations are now explicit as well:

```text
hzeta(s,a+1) = hzeta(s,a) - a^(-s),                        (4)
hzeta(s,0) = hzeta(s,1) = riemannZeta(s)   (Re s > 1),     (5)
hzeta(s,-n) = riemannZeta(s) + exp(-pi i s) H_n^(s).       (6)
```

Consequently every positive-order unit polygamma value is an actual Riemann-zeta value:

```text
psi^(m+1)(1) = (-1)^(m+2) (m+1)! riemannZeta(m+2).         (7)

psi^(m+1)(1/2)
  = (2^(m+2)-1)(-1)^(m+2)(m+1)! riemannZeta(m+2),          (8)

hzeta(s,1/2) = (2^s-1) riemannZeta(s)       (Re s > 1),    (9)

hzeta(m+2,1/2) = (2^(m+2)-1) riemannZeta(m+2).            (10)

sum_(0<=k<n) hzeta(s,(a+k)/n) = n^s hzeta(s,a)             (11)
    (Re s > 1, n > 0).
```

Here `hzeta` is `HurwitzZetaShift.hzeta`, the convergent complex-shift series constructed inside
the project, not an unrelated library wrapper.

## Proof

For `q=m+1`, the already formalized translated recurrence is

```text
psi^q(z+N) = psi^q(z) + (-1)^q q! sum_{n<N} (z+n)^(-(q+1)).
```

The existing all-order far-field theorem sends `psi^q(z+N)` to zero.  Independently,
`summable_hurwitzSeries` sends the same partial sums to `hzeta(q+1,z)`; the bridge from complex
`cpow` to inverse natural powers is `cpow_neg` followed by `cpow_natCast`.  Uniqueness of limits
therefore gives

```text
(-1)^q q! hzeta(q+1,z) = -psi^q(z),
```

which is `(1)` after the parity sign is normalized.

Separating the first Hurwitz-series term proves `(4)`.  At `a=0` that term vanishes in the
convergence half-plane, while the remaining series is exactly mathlib's Dirichlet-series
representation of `riemannZeta`; this proves `(5)`.  Rewriting the banked negative-integer tail law
with `(5)` gives `(6)`, and specializing `(1)` at `z=1` gives `(7)`.  Combining `(7)` with the
complete half-argument multiplication law gives `(8)`.  Splitting the absolutely convergent
Dirichlet series into its even- and odd-denominator parts proves `(9)` for every exponent in the
convergence half-plane; `(10)` is its positive-integer specialization.
Finally, Euclidean division writes every natural index uniquely as (mn+k), with (0\leq k<n).
Absolute summability permits this reindexing, and positive-real scaling of principal complex powers
then proves the complete rational-fiber distribution relation `(11)`.

## Parent classification

`[SEARCH]` This is the classical polygamma/Hurwitz-zeta identity recorded in NIST DLMF 5.15.2:

- https://dlmf.nist.gov/5.15.E2
- the Hurwitz recurrence is DLMF 25.11.3: https://dlmf.nist.gov/25.11.E3
- the half-shift value is DLMF 25.11.11: https://dlmf.nist.gov/25.11.E11
- the distribution relation is DLMF 25.11.15: https://dlmf.nist.gov/25.11.E15
- the Riemann-zeta Dirichlet series is DLMF 25.2.1: https://dlmf.nist.gov/25.2.E1

Both sides and all analytic ingredients were already formalized locally, but the exact equality
between them was absent from the local tree and the pinned mathlib checkout.  The bridge is useful
new formal infrastructure, not new scientific knowledge.

## Lean certificate

File: `formal/GaloisForLFunctions/Hurwitz/PolygammaHurwitzValue.lean`.

- `polygamma_eq_hzeta`: the all-order identity `(1)`;
- `hzeta_add_one`: the shift recurrence `(4)`;
- `hzeta_zero_eq_riemannZeta`, `hzeta_one_eq_riemannZeta`: the RH-object identification `(5)`;
- `hzeta_neg_nat_eq_riemannZeta_add`: the strengthened tail value `(6)`;
- `polygamma_one_eq_riemannZeta`: the all-order unit-value law `(7)`;
- `polygamma_one_half_eq_riemannZeta`: the all-order half-value law `(8)`;
- `hzeta_one_half_eq_mul_riemannZeta`: the full convergence-half-plane law `(9)`;
- `hzeta_nat_one_half_eq_mul_riemannZeta`: the integer-exponent specialization `(10)`;
- `hzeta_distribution`: the complete rational-fiber relation `(11)`;
- `trigamma_eq_hzeta_two`: the trigamma specialization `(2)`;
- `hzeta_two_one`, `hzeta_two_one_half`: exact custom-Hurwitz values `(3)`.

The module is imported by `GaloisForLFunctions`.

## RHTower and parent integration audit

1. `GammaProjectiveBoundary.lean` supplies the recurrence and far-field limits but previously left
   the limiting series unnamed.  Relation `(1)` closes that value-identification gap exactly.
2. `Hurwitz/HurwitzZeta.lean` supplies the series as a shift-variable object but previously had no
   Gamma/digamma interpretation and did not identify its base constant with the RH tree's
   `riemannZeta`.  Relations `(1)` and `(5)` close both value-identification gaps.
3. `ReflectionCocycleArchimedean.lean` may now rewrite every trigamma value on its positive-real
   locus as `hzeta(2,.)`.  Its strict-curvature proof still needs termwise order information, so its
   existing partial-sum comparison remains the stronger proof and is not replaced.
4. The generic Hurwitz independence theorems assume a nonrational exponent `s`.  Relation `(1)`
   lies exactly on the complementary positive-integer exponent locus, where the monodromy scalar is
   torsion.  It therefore identifies the boundary between the existing nonrational ladder theorem
   and the polygamma tower without falsely discharging the nonrationality hypothesis.
5. Current RHTower winding and envelope consumers use one-sided norm or real-part estimates.  The
   exact bridge changes the name of their value but supplies no stronger inequality, so those native
   bounds are retained.
6. `HurwitzZeta.hzeta_neg_nat` and all of its tail-independence consumers formerly carried
   `hzeta(s,0)` as an internal constant.  The strengthened endpoint `(6)` replaces it by the actual
   `riemannZeta(s)`.  Existing independence proofs need only cancellation of the constant, so their
   argument remains unchanged.  The value-sensitive parent module now exports
   `HurwitzN2Tail.tailFactored_zero_eq_riemannZeta_add`, which identifies the analytic factored
   tail's endpoint directly with the RH tree's zeta value and finite harmonic correction.
7. The isolated `hzeta_two_one_half` endpoint is now a specialization of `(9)`, which holds for
   every complex exponent with real part greater than one.  This gives noninteger Hurwitz consumers
   the same exact half-shift endpoint without changing their genuinely different monodromy
   hypotheses.
8. Combining `hzeta_distribution` with `polygamma_eq_hzeta` recovers the positive-order
   polygamma multiplication law on the right half-plane.  The existing differentiated-Gamma proof
   remains useful because it is formulated directly in the polygamma API; the new theorem supplies
   the more general complex-exponent Hurwitz value relation and avoids duplicating rational-fiber
   reindexing in future parent consumers.

The positive integration result is a genuine identification of previously separate value APIs.
No current hypothesis is removed: the consumers that remain use order, norm, or nonrational
monodromy information not contained in the equality alone.

## Gates

- [x] exact parent identity identified in the literature
- [x] local and mathlib declaration search confirms the bridge was absent
- [x] all positive derivative orders formalized
- [x] trigamma specialization formalized
- [x] exact unit and half-shift `hzeta(2,.)` values formalized
- [x] Hurwitz shift recurrence and `hzeta(s,0/1)=riemannZeta(s)` formalized
- [x] negative-integer tail law strengthened with the actual Riemann zeta
- [x] all-order unit polygamma/Riemann-zeta value law formalized
- [x] all-order half polygamma and full convergence-half-plane Hurwitz half-value laws formalized
- [x] full positive-modulus Hurwitz rational-fiber distribution relation formalized
- [x] RHTower and parent consumer audit completed
- [x] targeted source verification passes
- [x] targeted build, axiom audit, generated indexes, and formal lint pass

Every audited public bridge theorem uses only `propext`, `Classical.choice`, and `Quot.sound`.
