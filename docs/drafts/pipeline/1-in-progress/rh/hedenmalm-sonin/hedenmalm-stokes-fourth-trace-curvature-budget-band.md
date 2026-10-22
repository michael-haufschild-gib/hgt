# Hedenmalm Stokes fourth-trace curvature-budget band

- **ID:** `hedenmalm-stokes-fourth-trace-curvature-budget-band`
- **Label:** `P-G146`
- **Stage:** `1-in-progress`
- **Type:** UNCONDITIONAL SOURCE PROPAGATION / FOURTH-TRACE BAND AMPLIFICATION
- **Parent:** `hedenmalm-stokes-curvature-budget-central-band.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [CORPUS-NEW SYNTHESIS] [NOT RH]`

## Result

P-G145 used endpoint-quartet curvature directly and closed Route P budget on

```text
|Im(s)| <= 218/25.
```

Corpus contains stronger source exclusion in a disconnected theorem graph. Exact fourth
reciprocal-trace budget proves every off-line Xi copy satisfies

```text
Im(rho)^2 >= 2365/16.                                  (1)
```

No external zero calculation enters `(1)`. It follows from source upper bound on normalized first
prime--archimedean moment and quartet lower bound on one fourth-trace atom.

Since

```text
(243/20)^2 < 2365/16,
```

`RHVerifiedThrough (243/20)` follows unconditionally. Verified-height relative-resolvent transfer
then gives raw completed passivity and P-G144 curvature budget throughout

```text
Re(s)>1/2,
|Im(s)| <= 233/20.                                     (2)
```

The half-unit difference between `243/20` and `233/20` is exact critical-strip transverse width,
not proof slack.

Define `TailBudget(R)` as in P-G145. Lean proves

```text
TailBudget(233/20) <-> RightBudget <-> RH.              (3)
```

Thus source-only fourth-trace geometry moves Route P wall from `8.72` to `11.65` in height.

## Proof

For a Xi zero `rho` of positive ordinate at most `243/20`, construct its multiplicity copy `q`.
The rational height bound gives `Im(q)^2<2365/16`; `(1)` forces `Re(q)=1/2`. This is a closed Lean
certificate of `RHVerifiedThrough (243/20)`.

For `s` in `(2)`, put

```text
a=Re(s)-1/2,
b=Im(s),
z=b-a*i,
z+=b+a*i.
```

Verified-height transfer makes `XiC(z+)` nonzero and proves

```text
Im Tr_rel(z+) <= 0.
```

Schwarz reflection gives `Im Tr_rel(z)>=0`; exact completed-flux identification gives

```text
Tr_rel(z)=-i F(s),
```

so `Re F(s)<=0`. Central-slope calibration then yields P-G144 budget. Splitting frequency into
central band and exterior tail proves `(3)`.

## Higher principle

Endpoint curvature is not maximal low-frequency producer. Higher reciprocal traces can certify a
wider critical-line prefix; any such prefix automatically propagates completed passivity inward by
half-strip separation. This creates a reusable ladder:

```text
higher source trace exclusion at height H
  -> RHVerifiedThrough H
  -> completed passivity on |frequency|<=H-1/2
  -> curvature-budget tail starts at H-1/2.
```

Reasons prior work appeared stuck were shadows of missing theorem-graph composition: P-G144 asked
for transverse propagation while fourth-trace route had already paid for larger source band but
had not been transported through polar-residue cancellation and curvature normalization.

## Anti-theatre audit

- `RHVerifiedThrough (243/20)` is proved from symbolic source inequalities, not assumed.
- No numerical zero verification, floating-point evaluation, or RH premise is used.
- `(3)` does not prove tail budget; it strictly reduces its domain.
- Higher moment positivity alone is not claimed to extrapolate indefinitely. Each future extension
  needs a closed exclusion theorem with a concrete larger height.
- Scientific content is cross-route propagation and reusable trace-to-tail ladder; fourth-trace
  exclusion itself predates this card.

## Formal artifact

```text
formal/GaloisForLFunctions/RHTower/HedenmalmStokesFourthTraceCurvatureBudgetBand.lean
```

Principal declarations:

```text
rhVerifiedThrough_twoHundredFortyThree_twentieths
seamFluxCochain_re_nonpos_of_verifiedHeightBand
hedenmalmCurvatureNormalizedSeamFlux_budget_of_verifiedHeightBand
hedenmalmCurvatureNormalizedSeamFlux_budget_twoHundredThirtyThree_twentieths
hedenmalmCurvatureNormalizedRightTailBudget_iff_rightBudget_of_verifiedHeightBand
hedenmalmCurvatureNormalizedRightTailBudget_twoHundredThirtyThree_twentieths_iff_rh
```

## Remaining target

Search all higher reciprocal-trace source exclusions for larger verified heights and compose each
through generic ladder. When finite trace ladder saturates, remaining producer must control
positive high-frequency modular seam directly; fixed-order moments cannot rule out arbitrarily
high off-line charge.

## Gates

- [x] paper proof dependency closed
- [x] direct foreground Lean check
- [x] exact module build (`[12819/12819]`)
- [x] axiom audit (`propext`, `Classical.choice`, `Quot.sound` only)
- [ ] umbrella build
- [ ] high-frequency tail budget / RH

## Log

- 2026-08-13 — Discovered fourth-trace band during P-G145 tail audit; converted source exclusion
  into verified-height certificate, curvature slab, and exact `233/20` tail/RH criterion.
