# Physical-cutoff Jordan mass as the FCRJ obstruction

- **ID:** `physical-cutoff-jordan-mass-fcrj-obstruction`
- **Stage:** 5-failed
- **Type:** `[FALSIFIED] [BRIDGE] [POSITIVE SALVAGE]`
- **Source:** `critical-multiplicative-compensated-cancellation-rh.md`, `(PF12)`--`(PF13)`,
  `(AC15)`, `(AC17)`--`(AC25)`
- **Statement:** The negative mass or total variation of a separately truncated physical-cutoff
  alias measure is the invariant analytic obstruction remaining in `FCRJ`.

## Verdict

`[FALSIFIED]` The low and high divisor cutoffs multiply the same anchored primitive response.
Their coefficients add coordinatewise to the complete positive future-alias weight.  The forced
zero-mode switch then rejoins the remaining physical-cutoff term, so `H_h` disappears from the
final nonzero-frequency scalar.

## Exact obstruction to the claim

With `theta_h(n)=nu_h(n)/n`, complementary packet `N`, anchor `c`, and `r|N`, put

```text
lambda^<=_r=theta_h(r)
  sum_(d|N/r,c r d<=H)mu(d)theta_h(d),

lambda^>_r=theta_h(r)
  sum_(d|N/r,H<c r d)mu(d)theta_h(d).
```

Then

```text
lambda^<=_r+lambda^>_r
 =theta_h(r)product_(ell|N/r)(1-theta_h(ell))
 =w_(N,h)(r).
```

Consequently the low and high response actions join to the complete probability average.  Any
negative part of either half is decomposition-dependent.  At the full physical formula,
`beta_h=delta_h+J_h omega_h` gives

```text
delta_h(P_(H_h)F_p)+beta_h(Q_(H_h)F_p)
 =delta_h(F_p)+J_h omega_h(Q_(H_h)F_p),
```

and the first-crossing telescoping gives

```text
FCRJ_h=J_h S_z(h)-sum_p delta_h(F_p).
```

Thus a theorem controlling the separate Jordan mass would estimate a splice gauge, not the
invariant `FCRJ` response.

## Hostile strengthening

For arbitrary finitely supported Hermitian frequency profiles, the anchored primitive responses
can realize arbitrary real vectors sector by sector.  Hence the separate cutoff total variation
is actually the exact sectorwise operator norm.  CRT conjugation, character orthogonality, and
retaining the causal color cannot lower it without using the common physical source profile and
the global `h,p,a,r` joining.

This strengthening is finite interpolation plus `l-infinity/l-one` duality.  It is a route-closing
`[BRIDGE]`, not new scientific knowledge.

## Positive salvage

`[LEAN-PROVED]` Low/high cutoff joining is a nontrivial positive theorem: separate signed pieces
can fail positivity while their common-response sum is exactly a positive probability operator of
sharp norm one.  It is formalized by
`physicalCutoffAliasResponse_join` and
`quadraticCongruencePhysicalCutoffAliasResponse_join_norm_le` in
`GaloisForLFunctions/RHTower/PhysicalCutoffAliasResponseJoining.lean`; the Stage 3 card is
`3-formalized/needs-audit/physical-cutoff-alias-response-joining.md`.

After the global low/high source join, `(HGS29)` exposes a second exact survivor.  If `D_M` is the
`AC25` density, `R_M` its complete joined response, `E_M` the progression-plus-quadrature error,
and `P_M` the ordinary-prime endpoint carrier, then

```text
D_M-R_M+E_M=||P_M||^2>=0.
```

Thus `R_M<=D_M+E_M`, with equality exactly when `P_M=0`.  Once `|E_M|` is placed inside the
existing error budget, the negative half of the absolute `AC25` target is unconditional; only the
reverse response inequality remains.  The dependency-closed paper proof and sharp quantitative
reduction are recorded in
`2-fully-proven/not_new_scientific_knowledge/fcrj-corrected-response-saturation-law.md`.
This is a corpus-new frontier correction but an immediate Hilbert-square consequence, so it is
honestly classified as a bridge rather than new scientific knowledge.

## Representation lesson

Do not Jordan-decompose before the forced low/high response pieces and zero mode have joined.
After joining, do not ask for an unoriented “correlation cancellation”: corrected response
domination is automatic.  The genuine open target is the one-sided saturation inequality
`R_M>=D_M-O(polylog(M)/M)`, equivalently the small upper bound for the ordinary-prime aperture
energy.
