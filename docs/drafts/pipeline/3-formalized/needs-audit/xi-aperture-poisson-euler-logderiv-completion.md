# Xi aperture--Poisson Euler log-derivative completion

- **ID:** `xi-aperture-poisson-euler-logderiv-completion`
- **Stage:** 3-formalized / needs-audit
- **Type:** THEOREM (Lean) / completed prime-assembly bridge
- **Source:** `XiAperturePoissonValuationClockShuttle.lean`,
  `PolarPrimeMellinDefect.lean`, `XiShiftPrimeHypertranscendence.lean`, and *Finite Fusion Forces
  Infinite Hypertranscendence*
- **Scientific status:** `[PROVED HERE] [CANDIDATE NEW RH-PROOF-SHAPE KNOWLEDGE]`
  `[LEAN-PROVED] [EXTERNAL NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Statement:** For every real aperture `a>1`, multiplying the fully valuation-fused Poisson
  current by its forced prime clock and summing over primes reconstructs exactly the Euler-region
  logarithmic derivative: `sum_p log(p) F_a(p)=-a zeta'(a)/zeta(a)`.  Adding the canonical
  Gamma/boundary current gives exactly `-a xi'(a)/xi(a)`.

## Goal

Complete the coefficient-level Xi/Poisson shuttle through the prime assembly.  The preceding fusion
theorem gives a convergent current at each prime but leaves open whether those local currents join
to an actual completed Xi source.  The theorem below identifies the joined object exactly.

## Paper proof `[PROVED HERE]`

For `a>0`, complete valuation fusion at prime `p` gives

```text
F_a(p)=sum_(e>=0) a exp(-a(e+1)log p)
      =a/(p^a-1).                                      (EL1)
```

The actual Xi source supplies the forced clock `log p`.  Therefore, for `a>1`, absolute
convergence permits prime/valuation reindexing:

```text
sum_p log(p) F_a(p)
 =a sum_p sum_(e>=0) log(p) p^(-a(e+1))
 =a sum_n Lambda(n) n^(-a).                            (EL2)
```

The last series is the Euler-region negative logarithmic derivative of zeta, so

```text
sum_p log(p) F_a(p)=-a zeta'(a)/zeta(a).               (EL3)
```

Let `A(s)` be the fixed archimedean factor in `xi(s)=A(s)zeta(s)`, and complete the clocked
response by the same aperture factor:

```text
C^hat_a = sum_p log(p) F_a(p) - a A'(a)/A(a).
```

The already proved prime--archimedean seam identity and `(EL3)` give

```text
C^hat_a = a[-zeta'(a)/zeta(a)-A'(a)/A(a)]
        = a seamFluxCochain(a)
        = -a xi'(a)/xi(a).                              (EL4)
```

The reindexing in `(EL2)` is canonical: `Nat.Primes.prodNatEquiv` identifies `(p,e)` with the
prime power `p^(e+1)`, and the von Mangoldt coefficient vanishes away from prime powers.

## What this changes

The local Poisson current does not merely resemble an Euler kernel.  After the source-forced clock
weight, complete valuation fusion reconstructs the actual zeta logarithmic derivative exactly;
after the canonical Gamma/boundary correction it reconstructs the actual Xi logarithmic derivative
with no residual term.  Thus both prime assembly and scalar completion are closed on the
absolute-convergence ray.  The remaining analytic core is operator-level continuation of the
aperture response into the Xi region, together with the indefinite orbit-selection estimate.

## Hostile audit

1. The Euler product/log-derivative identity is classical.  Candidate novelty is restricted to its
   derivation from the actual aperture--Poisson valuation fusion and its role in the RH proof shape.
2. `(EL3)` is initially valid only for `a>1`; analytic continuation across the pole and into the
   critical strip is not supplied by termwise summation.
3. The identity is linear and does not provide the quadratic response inequality or select an
   off-line zero orbit.
4. The corpus already formalizes the von Mangoldt channel as `-zeta'/zeta`, but a targeted search
   found no existing bridge from the fused Poisson current `(EL1)` to that channel.
5. The corpus also already formalizes the prime--archimedean seam as `-xi'/xi`; `(EL4)` is the new
   splice from the response-derived current, not a new proof of Gamma completion.
6. Scalar continuation of `-xi'/xi` does not itself continue the aperture Hilbert/response
   operator or prove the required sign estimate.
7. External specialist novelty review remains open.

## No-go closure

- **Exact killing theorem/mechanism:** the unweighted prime sum of fused response coefficients is
  not the actual Euler source and has no canonical completed-Xi interpretation.
- **Strongest positive survivor:** restoring the forced prime clock `log p` yields the exact
  absolutely convergent reconstruction `(EL2)`--`(EL3)`.
- **New insight:** valuation fusion and prime completion are not separate guessed operations; in
  the Euler region they compose to the actual zeta logarithmic derivative, and the fixed
  archimedean correction then lands exactly on the completed Xi seam with no response defect.
- **Status:** dependency-closed paper and Lean proof in
  `XiAperturePoissonEulerLogDerivCompletion.lean`; external novelty unverified.

## Lean status

`RHTower/XiAperturePoissonEulerLogDerivCompletion.lean` formalizes:

1. the exact prime-power equality between a von Mangoldt L-series term and the clocked Poisson
   valuation density;
2. support of that L-series on positive prime powers;
3. the canonical prime/valuation reindexing `(EL2)`; and
4. both the von Mangoldt-channel and explicit `-a zeta'/zeta` forms `(EL3)`; and
5. the completed-current identities `a * seamFluxCochain(a)=-a xi'(a)/xi(a)` in `(EL4)`.

The exact leaf compilation passes.  `#print axioms` for the completed von Mangoldt channel and
explicit zeta logarithmic-derivative theorems reports only `propext`, `Classical.choice`, and
`Quot.sound`.  No umbrella or full project build was used.

## Gates

- [x] 0 -> 1: exact source clock, convergence region, and canonical prime-power reindexing identified
- [x] 1 -> 2: dependency-closed paper proof without RH or numerical input
- [ ] hostile external novelty audit
- [x] 2 -> 3: Lean prime-power reindexing, zeta log-derivative splice, leaf check, axiom audit
- [x] scalar Gamma/Xi attachment on the Euler ray
- [ ] operator-level continuation into the Xi response region

## Log

- 2026-07-19 — derived immediately after infinite valuation fusion exposed the Bose current
  `a/(p^a-1)`; the forced `log p` clock turns its prime sum into the von Mangoldt L-series.
- 2026-07-19 — formalized by the canonical prime-power support reindexing and spliced to the
  existing Euler-region zeta logarithmic-derivative theorem; targeted leaf and axiom checks pass.
- 2026-07-19 — attached the response-derived current to the existing prime--archimedean seam;
  scalar completion now lands exactly on `-a xi'(a)/xi(a)`, leaving operator continuation open.
