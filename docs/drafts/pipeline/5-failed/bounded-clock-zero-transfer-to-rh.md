# Bounded-clock zero transfer to RH (retired)

- **ID:** `bounded-clock-zero-transfer-to-rh`
- **Stage:** 5-failed
- **Type:** THEOREM (Lean) / TOP-DOWN RH TRANSFER
- **Scientific status:** `[TRANSFER PROVED] [ROUTE RETIRED: CIRCULAR CERTIFICATE] [BRIDGE]`
- **Statement:** Locally uniform approximants whose off-real zero fibres ride positive vertical
  arithmetic progressions with a uniform upper bound on their periods force the limit divisor to
  have the same periodicity.  Applied vertically in the centered `XiC` coordinate, the positive
  limiting period is ruled out by the elementary zero-free half-plane for `xi`, and the shrinking
  period is ruled out by analyticity.  Therefore the approximation law forces RH.

## The missed compactness alternative

Let `F_n -> F` locally uniformly on a vertically shift-closed domain, let `z_n -> z`, and suppose

```text
F_n(z_n+k T_n i)=0        for every k in Z,
0<T_n<=B.
```

Compactness of `[0,B]` gives a subsequence `T_n -> T`.

1. If `T>0`, locally uniform convergence gives

   ```text
   F(z+k T i)=0           for every k in Z.
   ```

2. If `T=0`, for each real `t` choose `k_n=floor(t/T_n)`.  Then

   ```text
   k_n T_n -> t,
   F_n(z_n+k_n T_n i)=0,
   F(z+t i)=0.
   ```

   Thus `F` vanishes on the whole vertical line through `z`.  If `F` is analytic and nonzero,
   this branch is impossible.

The existing `ClockEscape.lean` theorem only handles a fixed finite inventory of periods.  The new
argument handles continuously varying clocks and periods tending to zero.  Shrinking a clock does
not evade zero-locus closure: it produces a dense vertical mesh and collapses the analytic limit.

Coordinate warning: a vertical clock in the centered variable `z` is a horizontal clock in the
original variable `s`, because `s=1/2+iz`.  Ordinary Euler-column clocks are vertical in `s` and
therefore real in `z`; they do not instantiate this theorem.

## Top-down RH chain

For `XiC(z)=xi(1/2+iz)`, assume `F_n -> XiC` locally uniformly, the `F_n` are eventually entire,
and for one finite `B` the following finite-stage source predicate holds eventually:

```text
BoundedVerticalClockDichotomy B F_n:
  F_n(w)=0
  -> Im(w)=0 or
     exists T, 0<T<=B and F_n(w+kTi)=0 for every k in Z.
```

Hurwitz selection of zeros converging to each `XiC` zero is proved internally.  Then

```text
bounded-clock approximant zero fibres
  -> positive limiting clock or vertical zero continuum
  -> off-real XiC zero lies on a vertical arithmetic progression
  -> horizontal xi-zero progression entering Re(s)>=1, impossible
  -> every XiC zero is real
  -> RH.
```

This is not a restatement of RH through positivity, a Hermitian determinant, or a zero-side norm.
For a fixed, independently defined prime/theta approximant family, its antecedent is an
approximation-stable source constraint on the divisor-generating clocks.  Without that provenance
restriction, however, the existential approximation certificate is equivalent to RH: under RH the
constant family `F_n=XiC` satisfies the real-zero branch.  Thus the abstract certificate alone is a
criterion, not an independent route.

The theorem `xiC_no_vertical_zero_progression` discharges the positive limiting-period branch
unconditionally: a negative integer step eventually maps to `Re(s)>=1`, where `xi` is nonzero.
The theorem `riemannHypothesis_of_bounded_vertical_clock_dichotomy_approximants` carries the global
source-level composition.  The sharper
`riemannHypothesis_of_locally_bounded_vertical_clock_dichotomy_approximants` needs the dichotomy
only on each fixed compact ball, with a bound allowed to depend on the ball; spurious zeros escaping
to infinity are irrelevant.  Neither theorem has a no-arithmetic-progression or
limiting-zero-sequence premise.  The older `riemannHypothesis_of_bounded_clock_zero_approximants`
remains as the lower-level sequence interface.

The unconditional theorem `xiC_transverse_clock_tendsto_atTop` gives the converse source pressure:
whenever exact transverse-clock zero fibres of any locally uniform approximants have centres
converging in `C`, their periods tend to `+infinity`.  Mere unboundedness is not the conclusion;
every bounded subsequence is excluded.  This is the divisor-level form of clock
decompactification.

## Lean status

`formal/GaloisForLFunctions/RHTower/BoundedClockZeroTransfer.lean` proves:

- `tendsto_intFloor_mul_of_pos_of_tendsto_zero`;
- `periodic_zero_limit_of_period_tendsto`;
- `shrinking_periodic_zero_limit_vertical`;
- `bounded_periodic_zero_limit`;
- `xiC_no_vertical_zero_progression`;
- `riemannHypothesis_of_bounded_clock_zero_approximants`;
- `exists_XiC_zero_approximating_subsequence`;
- `BoundedVerticalClockDichotomy`;
- `riemannHypothesis_of_bounded_vertical_clock_dichotomy_approximants`;
- `xiC_transverse_clock_escape`;
- `xiC_transverse_clock_tendsto_atTop`;
- `BoundedVerticalClockApproximationCertificate`;
- `boundedVerticalClockApproximationCertificate_iff_riemannHypothesis`;
- `LocalBoundedVerticalClockDichotomy`;
- `riemannHypothesis_of_locally_bounded_vertical_clock_dichotomy_approximants`;
- `LocalBoundedVerticalClockApproximationCertificate`;
- `localBoundedVerticalClockApproximationCertificate_iff_riemannHypothesis`.

The file compiles with the project toolchain and is imported by the RHTower umbrella.

## Route verdict

The bounded-clock hypothesis is not a non-circular RH mechanism.  Lean proves both abstract
existential forms equivalent to RH:

```text
BoundedVerticalClockApproximationCertificate <-> RH,
LocalBoundedVerticalClockApproximationCertificate <-> RH.
```

The compact-local weakening does not change the verdict.  Under RH the constant family `F_n=XiC`
satisfies every clock dichotomy through its real-zero branch.  Conversely, the Hurwitz transfer
proves RH.  Adding an informal provenance adjective does not alter the mathematical hypothesis,
and no natural prime or theta construction supplies the transverse clock orientation anyway.

The positive theorem survives independently:

```text
exact transverse clocks in any genuine locally uniform approximation of XiC
  -> their periods tend to +infinity.
```

Thus every genuine transverse clock decompactifies cofinally.  The reusable part of the route is
the Hurwitz/compactness machinery, not the bounded-clock antecedent.  Source-side successors must
replace exact bounded periodicity by an independently controlled defect, such as the already
formalized compact-local reflected prime energy, or quantify a decompactifying source law without
repackaging real-zero localization.

The strongest direct pivot is the source-closure problem in
`xi-approximant-prime-energy-source-close.md`; a second is all-depth horizontal carrier coercivity,
whose depth-one and depth-two cases are already formalized.  The full pipeline and Lean audit is
`docs/reports/bounded_clock_route_full_audit_0711.md`.
