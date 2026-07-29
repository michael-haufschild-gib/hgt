# Unit-exponential Wold--Calderón suspension

- **ID:** `unit-exponential-wold-calderon-suspension`
- **Stage:** 1-in-progress
- **Type:** SOURCE THEOREM / EXACT CONTINUOUS--DISCRETE COMPARISON /
  BOUNDED-COMPLETION NO-GO
- **Scientific status:** `[PAPER-PROVED CORE] [SOURCE-PURE] [NOT RH]`
  `[NEW TO CORPUS] [EXTERNAL NOVELTY UNVERIFIED]`
- **Parents:**
  - `prime-stokes-ccm-unit-resolvent-weld.md`;
  - `source-curved-prime-torus-conormal-temperedness.md`;
  - `deninger-mertens-adiabatic-exponential-corner.md`;
  - `../3-formalized/not_new_scientific_knowledge/ccm-unit-riesz-mobius-renewal-law.md`;
  - `../2-fully-proven/not_new_scientific_knowledge/burnol-prime-dilation-copoisson-quotient-law.md`.

## Result

The unit exponential aperture law is not merely the unique scalar law
matching the CCM resolvent.  It is also the continuous suspension of
every rational-dilation Wold renewal.  If

```text
dmu(c)=exp(-c) dc,                 c>=0,                 (1)
L_q=log q,                         q>1,
```

then its `k`-th `q`-cell has mass

```text
mu([kL_q,(k+1)L_q))
  =(1-q^(-1))q^(-k).                                      (2)
```

These are exactly the Haar/Wold weights in the source-conormal renewal

```text
J(S_q^k c_(j+2k))
  =(1-q^(-1))q^(-k)J(p_j).                               (3)
```

The comparison is compatible with multiplication of rational
dilations.  Its Laplace first-cell symbol is

```text
b_q(w)
 =integral_[0,L_q] exp(-(1+w)c) dc
 =(1-q^(-(1+w)))/(1+w).                                  (4)
```

Thus one cell is exactly one reciprocal Euler local factor divided by
the universal unit Calderón factor.  The full unit resolvent is the
Wold renewal of this cell:

```text
R(w)=1/(1+w)
    =sum_(k>=0) q^(-k(1+w)) b_q(w),   Re(w)>-1.           (5)
```

At the operator level, for any strongly continuous contraction
semigroup `T_c`, define

```text
R = integral_[0,infinity] exp(-c) T_c dc,
B_q = integral_[0,L_q] exp(-c) T_c dc.                   (6)
```

Then

```text
R=sum_(k>=0)q^(-k)T_(kL_q)B_q,
B_q=(I-q^(-1)T_(L_q))R.                                  (7)
```

Because the normalized CCM aperture multiplier is `-R` on every
right-half-plane Laplace mode, `(7)` is the explicit finite-dilation
Wold--Calderón comparison that was previously left unnamed:

```text
B_q=-(I-q^(-1)T_(L_q)) C_CCM.                            (8)
```

This closes the coefficient-level type mismatch.  It does not prove
that the comparison is conservative on the complete Xi conormal.

## 1. Exact cell law

For `L>0`,

```text
integral_[kL,(k+1)L] exp(-c) dc
 =exp(-kL)(1-exp(-L)).                                   (9)
```

Putting `L=log q` gives `(2)`.  Summing `(9)` over `k>=0`
gives one.  Hence the continuous aperture coordinate and the discrete
valuation depth are the same renewal clock after taking integer cells.

The unit rate is forced.  For the rate-`a` law

```text
dmu_a(c)=a exp(-ac)dc,
```

the cell weights are

```text
(1-q^(-a))q^(-ak).                                      (10)
```

They equal the arithmetic Wold weights `(2)` for one `q>1` and every
`k` only when `a=1`.  Thus the same unit rate is selected
independently by:

1. the prime-Stokes/CCM resolvent weld; and
2. the rational-dilation Wold/Haar renewal.

## 2. Multiplicative coherence

Put

```text
e(t)=1-exp(-t).
```

Then

```text
e(t+u)=e(t)+exp(-t)e(u).                                 (11)
```

At `t=log q`, `u=log r`, this is

```text
1-(qr)^(-1)
 =(1-q^(-1))+q^(-1)(1-r^(-1)).                          (12)
```

Equation `(12)` is the scalar shadow of the Wold-defect decomposition
for composed shifts:

```text
E_(qr)=E_q+S_q E_r S_q^*.                               (13)
```

The first-cell operators satisfy the stronger semigroup cocycle

```text
B_(qr)=B_q+q^(-1)T_(L_q)B_r.                            (14)
```

On a Laplace mode `T_c -> exp(-wc)`, `(14)` is

```text
b_(qr)(w)=b_q(w)+q^(-(1+w))b_r(w).                       (15)
```

Therefore the comparison respects rational multiplication; it is not
a separate fitted map for each prime.

## 3. Euler-factor transgression

Equation `(4)` can be rearranged as

```text
(1-q^(-(1+w)))R(w)=b_q(w).                              (16)
```

The left factor is the reciprocal Euler factor at `s=1+w`.
Consequently the Wold range defect, unit Calderón resolvent, and Euler
local factor are three readings of one first-cell transgression.

This sharpens the existing regular/singular dictionary:

```text
Wold defect E_q
  -> cell mass 1-q^(-1)              (BV first trace),
  -> cell operator B_q,
  -> symbol (1-q^(-s))/s             (Euler/Calderón),
  -> geometric renewal               (principal conormal),
  -> determinant telescoping         (Gamma anomaly).
```

The first, fourth, and fifth readings were already typed in
`source-curved-prime-torus-conormal-temperedness.md`.  The second and
third provide the missing continuous aperture comparison.

## 4. Bounded-completion no-go

The unit-averaged Stokes metric has Fourier multiplier

```text
m_1(xi)=2+2/(1+xi^2),
2<=m_1(xi)<=4.                                           (17)
```

Therefore its Hilbert norm is equivalent to the ambient `L2` norm.
Its completion is the same Hausdorff Hilbert space, with the same
continuous spectrum and the same discontinuous point-evaluation
functionals.  Unit averaging removes fixed-aperture blind frequencies
but cannot restore a Xi divisor fibre lost in scalar `L2`.

This falsifies the bounded version of the former
`UNIT-RESOLVENT GAMMA/CALDERON INTERTWINER` conjecture.  Any bounded
map obtained only from `(17)` is topologically incapable of producing
the missing conormal fibres.  An unbounded map would require a
source-fixed domain, and asserting that its Xi fibres survive would
again be the prime-Schwartz temperedness/RH core.

The positive survivor is `(7)`--`(16)`: unit averaging is useful as a
**relative first-cell transgression**, not as a new Hilbert
completion.

## 5. What remains genuinely open

The exact finite-dilation comparison does not solve the all-prime
problem.  Three gaps remain:

1. **Prime-rank conservativity.**  The scalar log-time semigroup reads
   rational dilation through `log q`.  The six-channel HT minimality
   theorem requires the full finite-prime product bornology and
   integral incidence data.  One must lift `(14)` from the scalar
   suspension to the source-relative Wold--Toeplitz extension without
   collapsing independent prime directions.
2. **Renormalized all-prime product.**  Multiplying the reciprocal
   factors in `(16)` reaches `1/zeta(1+w)` only in its ordinary
   convergence half-plane.  The Gamma/BV relative class must provide
   the continuation before divisor specialization.
3. **Conormal conservativity.**  The resulting source comparison must
   remain nonzero on every Xi multiplicity jet.  Assuming this in the
   natural quotient topology is RH-equivalent.

The next RH-bearing theorem is therefore narrower than the former
unspecified intertwiner:

> **[CONJECTURE -- SOURCE-EFFECTIVE WOLD--CALDERON PRODUCT
> CONSERVATIVITY.]**  The coherent first-cell cocycle `(14)`, lifted
> through the actual Euler--Gamma/BV relative Wold extension and
> completed in the six-channel finite-prime Ind-bornology, has a
> renormalized product whose moderate boundary is the source-defined
> co-Poisson/Xi principal conormal map and is nonzero on every top
> multiplicity jet.

This is a truth-hunch; no proof is known.  Its conclusion must be
derived from the named source extension, not inserted as continuity of
the target Xi quotient.

## 6. Hostile audit

1. **Classical ingredients.**  Laplace resolvents, geometric renewal,
   Haar valuation shells, Wold decomposition, and Euler factors are
   standard separately.  No novelty is claimed for them.
2. **No topology miracle.**  Equation `(17)` proves the unit metric is
   topologically trivial relative to `L2`.
3. **No scalar-to-complete positivity leap.**  The unit resolvent is a
   rational Herglotz/Schur object.  It is not the shifted-Xi Pick
   kernel, and scalar equality of multipliers does not control complete
   negative index.
4. **No analytic continuation by product notation.**  The all-prime
   product of `(16)` is not used on `Re(w)=0` without a separate
   source-relative continuation theorem.
5. **No target-defined domain.**  Choosing the domain of an unbounded
   map so that Xi evaluations are continuous is the missing theorem,
   not its proof.
6. **Off-line systems.**  Any proposed extension must be tested
   against the corpus's explicit positive generalized-prime off-line
   systems.  The ordinary-prime integral incidence and Gamma/BV
   transgression must be the point where those systems fail.

## 7. Literature boundary

The Laplace representation of a semigroup resolvent and its
decomposition into step cells are standard semigroup theory.
Geometric valuation-shell masses are standard local Haar measure.
Wold decompositions and semigroup boundary quotients are parent
operator algebra.  Targeted searches found no source combining the
unit CCM aperture resolvent, rational Wold renewal, reciprocal Euler
local factor, and Gamma/BV principal-conormal transgression in
`(2)`--`(16)`.  This is a provisional noncollision statement, not a
priority claim.

Closest parent sources:

- Hille--Yosida/Laplace semigroup resolvent theory;
- Kakariadis--Katsoulis--Laca--Li, *Boundary quotient C*-algebras of
  semigroups*, `arXiv:2105.00422`;
- Li--Yang, *Wold Decomposition and C*-envelopes of Self-Similar
  Semigroup Actions on Graphs*, `arXiv:2307.10108`;
- Connes--Consani--Moscovici, *Zeta zeros and prolate wave operators*,
  `arXiv:2310.18423`;
- Burnol's co-Poisson/Sonine work.

## Gates

- [x] exact exponential-cell/Wold-Haar identity
- [x] rate-one uniqueness from arithmetic renewal
- [x] rational-dilation cocycle
- [x] first-cell Euler-factor symbol
- [x] operator renewal and Calderón comparison
- [x] bounded unit-metric completion no-go
- [x] previous bounded-intertwiner conjecture retired
- [ ] independent specialist novelty audit
- [x] formalize dependency-closed scalar cocycle
- [ ] lift cocycle to source-relative Wold--Toeplitz extension
- [ ] construct six-channel finite-prime Ind-product
- [ ] prove moderate boundary equals source co-Poisson/Xi conormal
- [ ] prove multiplicity-jet conservativity
- [ ] RH

## Log

- 2026-07-28 — Derived unit exponential cell law, rational-dilation
  cocycle, first-cell Euler factor, and semigroup renewal.  Identified
  exact continuous suspension of the corpus Wold/BV weights.  Proved
  unit metric is norm-equivalent to ambient `L2`, retiring the bounded
  Gamma/Calderón-intertwiner route while retaining its first-cell
  transgression as the positive survivor.
- 2026-07-28 — Formalized the scalar suspension in
  `PrimeStokesWoldCalderonSuspension.lean`: Wold boundary cocycle,
  exact rational cell masses, rate-one uniqueness, complex first-cell
  cocycle, finite renewal, and CCM defect identity.  Direct Lean,
  final module build, and axiom audits pass; declarations use only
  `propext`, `Classical.choice`, and `Quot.sound`.
