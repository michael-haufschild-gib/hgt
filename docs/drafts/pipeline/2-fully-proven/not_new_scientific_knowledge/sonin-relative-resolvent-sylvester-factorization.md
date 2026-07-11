# Sonin relative-resolvent Sylvester factorization

- **ID:** sonin-relative-resolvent-sylvester-factorization
- **Stage:** 2-fully-proven
- **Type:** THEOREM / ANALYTIC REDUCTION (paper)
- **Scientific status:** BRIDGE / NOT NEW SCIENTIFIC KNOWLEDGE
- **Source inputs:** Connes--Consani--Moscovici, *Zeta zeros and prolate wave operators*,
  arXiv:2310.18423v2, Propositions 4.6--4.8; `sonin-euler-inverse-polar-corner-noncompact.md`

## Setup

Let `H_infinity,H_P` be the archimedean and finite semilocal Hilbert spaces. Let

`theta_P:H_infinity->H_P`

be the boundedly invertible source map carrying every archimedean Sonin space `K_lambda` onto the
semilocal Sonin space `K_(lambda,P)`. Let `eta_P` be the cyclic place transition. On the archimedean
Hardy--Titchmarsh model the source formulas give

`eta_P=theta_P G_P`,                                         (1)

where `G_P` is multiplication by the positive finite Euler cyclic density

`G_P(s)=prod_(p in P)|L_p(1/2-is)|^2`.

Let `Q` and `Q_P` be the orthogonal Sonin projections. Suppose closed operators `W_infinity,W_P`
have resolvents `R_infinity(z),R_P(z)` at a common nonreal `z`, and suppose their Sonin spaces are
reducing. Define

`Rhat_P(z)=theta_P^(-1)R_P(z)theta_P`.

Then `K_lambda` is invariant under `Rhat_P(z)`.

## Factorization theorem

Put

`H_P=(1-Q)G_PQ`,                                            (2)

`A_P(z)=(1-Q)Rhat_P(z)(1-Q)`,

`B_infinity(z)=QR_infinity(z)Q`.

Up to the bounded invertible quotient identification induced by `theta_P`, the exact relative-resolvent
Sonin corner is

`A_P(z)H_P-H_PB_infinity(z)`.                               (3)

More precisely, the compression

`L_P=(1-Q_P)theta_P|_(K_lambda^perp):K_lambda^perp->K_(lambda,P)^perp`

is boundedly invertible and

`(1-Q_P)(R_P(z)eta_P-eta_PR_infinity(z))Q
 =L_P(A_P(z)H_P-H_PB_infinity(z))`.                         (4)

Consequently:

1. the source relative-resolvent corner is compact or belongs to a Schatten ideal exactly when the
   Sylvester transform in (3) does;
2. if both restricted resolvents `A_P(z)` and `B_infinity(z)` are trace class, then the corner is
   trace class despite noncompactness of `H_P`;
3. the corner vanishes exactly when `H_P` intertwines the two restricted resolvents at `z`;
4. if it vanishes for every common resolvent parameter, then `H_P` intertwines the restricted
   resolvent representations, hence their spectral calculi;
5. if the two restricted self-adjoint spectra are disjoint, the corner cannot vanish because `H_P`
   is nonzero.

## Proof

Using (1), pull the relative resolvent back through `theta_P`:

`theta_P^(-1)(R_Peta_P-eta_PR_infinity)
 =Rhat_PG_P-G_PR_infinity`.                                 (5)

Since `Rhat_P` leaves `range Q` invariant,

`(1-Q)Rhat_PQ=0`.

Since the archimedean Sonin space reduces `R_infinity`,

`R_infinity Q=QR_infinity Q`.

Decomposing `G_PQ=QG_PQ+(1-Q)G_PQ` in (5) therefore gives

`(1-Q)(Rhat_PG_P-G_PR_infinity)Q
 =(1-Q)Rhat_P(1-Q)H_P-H_PQR_infinity Q`,

which is (3).

Because `theta_P` maps `K_lambda` bijectively onto `K_(lambda,P)`, it induces a bounded isomorphism of
the quotient Hilbert spaces. Written on the orthogonal complements this induced map is `L_P`, proving
that it is boundedly invertible. Multiplying (3) by `L_P` gives (4). Two-sided multiplication by
bounded invertible operators preserves compactness and every Schatten class, proving item 1. Item 2
follows from the operator-ideal property.

Item 3 is the definition of the Sylvester kernel. If the equality holds throughout a common resolvent
set, the resolvent identity and analytic continuation show that `H_P` intertwines all resolvents and
therefore the bounded Borel spectral calculi, proving item 4. For self-adjoint restrictions with
disjoint spectra, choose a bounded Borel function equal to one on the first spectrum and zero on the
second. Intertwining that function forces `H_P=0`. The actual Euler corner is nonzero--indeed
noncompact--so item 5 follows.

## Route consequence

- `[PROVED]` Relative-resolvent smoothing is not a vague fallback: its exact Sonin corner is a
  Sylvester transform of the already-identified Euler metric crossing.
- `[PROVED]` Noncompactness of the unsmoothed Euler corner does not preclude trace class after
  resolvent smoothing. Trace-class restricted resolvents are sufficient.
- `[PROVED]` Vanishing is no longer an unspecified compression accident. It is equivalent to an exact
  restricted spectral intertwiner.
- `[OPEN CORE]` Construct source-selected closed semilocal prolate realizations; prove the Sonin spaces
  reduce them; prove trace-class restricted resolvents; and separate, or explicitly compare, the
  semilocal complementary spectrum with the archimedean Sonin spectrum.
- `[OPEN CORE]` A nonzero trace-class two-space corner still needs a canonical determinant-line or
  quadratic pairing. The ordinary determinant of the raw strictly-lowering defect remains trivial.

## Novelty audit

The Sylvester identity, quotient transport, ideal property, and disjoint-spectrum intertwiner theorem
are standard operator theory. Their source-specific assembly precisely identifies the remaining Route B
analytic gates, but it is a reduction rather than new scientific knowledge.
