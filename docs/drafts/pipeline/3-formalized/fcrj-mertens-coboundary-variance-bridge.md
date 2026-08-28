# FCRJ Mertens-coboundary variance bridge

- **ID:** `fcrj-mertens-coboundary-variance-bridge`
- **Stage:** 3 — formalized in Lean 4
- **Route:** `CCM-FU / FCRJ`
- **Type:** `THEOREM (paper) [LEAN-PROVED] [POSITIVE SURVIVOR] [EXACT BURDEN EQUIVALENCE]`
- **Date:** 2026-08-27
- **Source:** conjecture loops 58--67 in
  `docs/drafts/pipeline/1-in-progress/critical-multiplicative-compensated-cancellation-rh.md`

## Question

After adaptive-width regularization is retired, what exact classical arithmetic object carries
the fixed-ratio FCRJ energy burden? Can the positive prime-pair tent be recentered without losing
physical coefficients, clipping, or source orientation?

## Answer

For finite physical packet `P`, define cumulative prime-log mass and unit-density discrepancy

```text
C_P(t) = sum_(p in P, log p <= t) log(p)/p,
D_P(t) = C_P(t)-t.
```

The raw moving flux has exact coboundary decomposition

```text
Flux_P(m,k;u)
 = C_P(k-u)-C_P(m-u)
 = (k-m)+D_P(k-u)-D_P(m-u).                            (MC1)
```

Let `L_P` be physical weighted clipped-length mass. Exact aperture centering gives

```text
CenteredFlux_P(A,m,k;u)
 = [D_P(k-u)-D_P(m-u)]-[L_P/A-(k-m)].                  (MC2)
```

The scalar centered flux is almost everywhere the concrete complex Hilbert carrier already used
by FCRJ. Therefore

```text
Energy_P(A,m,k)
 = integral_0^A |CenteredFlux_P(A,m,k;u)|^2 du
 = integral_0^A
     |D_P(k-u)-D_P(m-u)-[L_P/A-(k-m)]|^2 du.           (MC3)
```

At fixed physical scale `X` and ratio width `c`, put `m=log X`, `k=log X+c`. Then

```text
Energy_P(A,log X,log X+c) <= B

iff

integral_0^A
  |D_P(log X+c-u)-D_P(log X-u)-[L_P/A-c]|^2 du <= B.   (MC4)
```

## Verdict

`[PROVED — FIXED-RATIO PHYSICAL FCRJ ENERGY IS EXACTLY A CENTERED TWO-ENDPOINT MERTENS-DISCREPANCY
VARIANCE; NO PRIME-PAIR OR HILBERT LOSS REMAINS]`.

This removes ambiguity about fixed-width provider. Continuum log density is annihilated exactly,
not asymptotically. Remaining `M^-1 polylog(M)` target is a coefficient-faithful Selberg-type mean
square for one Mertens discrepancy increment. Any proposed analytic input can now be checked by
literal substitution into `(MC4)`; bounds for uncentered pair mass or pointwise PNT error are not
the required theorem.

## Novelty audit

Cumulative-sum differences and variance identities are classical. Selberg integrals and
prime-short-interval variance are established literature; adjacent primary sources include
[Coppola](https://arxiv.org/abs/1006.1229),
[Coppola--Laporta](https://arxiv.org/abs/1312.5701),
[Montgomery--Soundararajan](https://arxiv.org/abs/math/0409258), and
[Bui--Keating--Smith](https://arxiv.org/abs/1506.03741).

Mandatory corpus searches and targeted current-literature searches found no theorem identifying
the exact clipped FCRJ Hilbert carrier with `(MC1)--(MC4)`, including endpoint weight `log p/p`,
finite-packet cumulative discrepancy, physical clipping mean `L_P/A`, and fixed-ratio budget
equivalence. Candidate-new content is restricted to this coefficient-exact bridge. No broad
priority claim is made without expert review.

## Lean

Module:

```text
GaloisForLFunctions.RHTower.XiPhysicalPrimeApertureMertensCoboundary
```

Capstones:

- `xiPhysicalPrimeLogCumulativeMass_sub_eq_windowFlux`
- `xiPhysicalPrimeLogWindowFlux_eq_width_add_mertensCoboundary`
- `xiPhysicalPrimeLogCenteredWindowFlux_eq_centered_mertensCoboundary`
- `xiPhysicalPrimeLogComplexAggregateApertureCarrier_coeFn_eq`
- `intervalIntegral_sq_xiPhysicalPrimeLogCenteredWindowFlux_eq_energy`
- `xiPhysicalPrimeLogApertureFusionEnergy_eq_mertensCoboundaryVariance`
- `xiPhysicalPrimeLogApertureFusionEnergy_logScale_eq_mertensCoboundaryVariance`
- `xiPhysicalPrimeLogApertureFusionEnergy_logScale_le_iff`

Audit:

- direct `lake env lean` check: pass;
- targeted `lake build GaloisForLFunctions.RHTower.XiPhysicalPrimeApertureMertensCoboundary`: pass;
- capstone `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`;
- theorem-area umbrella: wired;
- global lint: both new modules are reachable and clean; repository gate remains blocked by
  unrelated concurrently owned unwired `RHTower.Sieve`, theta-cusp, and `HTGeometry` modules.

## Remaining burden

Instantiate `P` as exact cofinal physical prime packet and prove right side of `(MC4)` is
`O_(A,c)(log(X)^B/X)`. This is now sole fixed-ratio FCRJ carrier estimate. Next attack should
compare exact `log p/p` discrepancy increment to a weighted Selberg integral for `theta` or `psi`,
with prime-power and partial-summation corrections kept at target scale.
