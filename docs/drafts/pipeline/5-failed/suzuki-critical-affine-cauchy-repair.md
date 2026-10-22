# Suzuki critical affine-Cauchy repair

- **ID:** `suzuki-critical-affine-cauchy-repair`
- **Stage:** 5 — failed/retired
- **Type:** FALSIFIED SOURCE REPAIR
- **Status:** `[FALSIFIED] [PAPER-PROVED] [LEAN-PROVED] [NO RH PREMISE]`

## Retired claim

Use canonical affine two-boundary Cauchy residual at endpoints `+/-1/2` to cancel critical rooted
Gamma--Bianchi divergence before Hilbert completion.

## Exact killing theorem/mechanism

At prime `p`, `L=log p`, residual is exactly

```text
C(p)=-1/[4L(L+1/2)(L-1/2)].
```

After weighting by critical source mass `Lambda(p)/sqrt(p)`, Lean proves

```text
1/(6400000*p) <= Lambda(p)/sqrt(p) * C(p)^2.
```

Euler prime-harmonic divergence therefore proves repaired mass is not summable.  Exact theorem:
`not_summable_suzukiCriticalAffineCauchyResidualMass` in
`formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCriticalAffineCauchyResidualDivergence.lean`.

## Strongest positive survivor

Midpoint-Lorentz numerator really is same polynomial as affine Cauchy residual numerator; collision
identifies why candidate is canonical.  Failure proves power-scale source operation is needed.
Corpus finite aperture current supplies it: transverse disk factor `q/(1+q)=1/(p+1)` pairs
distributional critical Gamma boundary with true-aperture innovation.  Exact valuation atoms form
contractive quarter-shift geometric sequence and have resolvent sum, formalized in
`SuzukiCriticalApertureQuarterShiftCurrent.lean`.

## New insight

Do not add more prime-log factors to standalone rooted vector.  Change representation order:

```text
critical boundary x aperture innovation -> current -> compound completion,
```

before any square or cofinal Hilbert limit.  First surviving power gain is source transverse
`1/(p+1)`, not fitted counterterm.

## Status

- Killing theorem: dependency-closed paper proof and Lean proof.
- Positive survivor: exact depth law/resolvent Lean-proved; absolute prime completion paper-proved,
  Lean gate open.
- Novelty: Suzuki-specific connection unverified; generic geometric series is parent analysis.

## Log

- 2026-07-22 — candidate falsified; positive quarter-shift aperture-current survivor extracted and
  formalized at depth-resolvent level.
