# CCM unit-Riesz Hankel boundary pulse and covariance obstruction

- **ID:** `ccm-unit-riesz-hankel-boundary-pulse`
- **Stage:** `3-formalized/new_scientific_knowledge`
- **Type:** EXACT HANKEL TRACE LAW / OPERATOR-COVARIANCE NO-GO / ROUTE TRIAGE
- **Status:** `[PAPER-PROVED] [LEAN-PROVED, UNCONDITIONAL] [NOVELTY UNVERIFIED] [NO RH CLAIM]`
- **Routes:** `CCM-HG`, `CCM-EP`, `CCM-UR`, `CCM-FU`, `G`, `O`, `CCM-GS`
- **Parent:** `ccm-four-unit-cesaro-curvature-wall`

## Public claim

The limiting FU--UR curvature reporter selects a unique fast/slow pair of positive exponential
Hankel leak profiles.  Their signed boundary relative trace is strictly positive at every positive
aperture, has exact maximum `3/128` at aperture `2 log 2`, and after four-unit normalization lies
strictly below the incoming pole trace by one exact square.

This scalar positivity does not lift to positive operator covariance.  Every positive aperture and
every nonzero two-sample separation produces a strictly negative `2 x 2` determinant.  Therefore
this canonical pair remains a legitimate signed/Krein scalar-trace carrier for CCM-HG or
G-exterior, but it cannot be the missing positive background in CCM-EP and cannot feed Route O,
G-floor, or CCM-GS through a positive Gram identification.

The profiles are selected by the reporter kernel, not by the literal completed-Xi source.  No
arithmetic estimate or RH conclusion is asserted.

## 1. Canonical leak pair

The limiting FU--UR curvature kernel is

```text
K_infinity(u) = (3/32) exp(-u) - (3/128) exp(-u/2).
```

Its canonical positive channels are

```text
ell_fast(t) = sqrt(3/32) exp(-t/2),
ell_slow(t) = sqrt(3/128) exp(-t/4),
K_infinity = |ell_fast|^2 - |ell_slow|^2.                 (1)
```

Both satisfy the corpus `LeakProfile` integrability law.  Their masses and first moments are

```text
integral |ell_fast|^2 = 3/32,
integral |ell_slow|^2 = 3/64,
integral t |ell_fast|^2 = integral t |ell_slow|^2 = 3/32. (2)
```

Thus the signed pair has mass `3/64` but zero barycentric defect.  The FU--UR boundary atom cancels
the mass while affine blindness is already encoded by equal barycentres.

## 2. Exact Hankel gap and positive boundary pulse

For any exponential leak density `c exp(-a t)`, direct integration gives

```text
Gap(u) = (c/a^2) exp(-a u), u >= 0.                       (3)
```

Hence

```text
Gap_fast(u) = (3/32) exp(-u),
Gap_slow(u) = (3/32) exp(-u/2).                            (4)
```

The signed fast-minus-slow boundary relative trace is

```text
P(u) = (3/32)(exp(-u/2) - exp(-u)), u > 0.                 (5)
```

Therefore `P(u)>0` for every `u>0`.  Completing the square in
`x=exp(-u/2)` gives

```text
P(u) <= 3/128,
P(2 log 2) = 3/128.                                       (6)
```

Four-unit normalization gives

```text
P_4(u) = (256/3) P(u) = 8(exp(-u/2)-exp(-u)).              (7)
```

The incoming pole packet has boundary trace `4(1-exp(-u))`, and subtraction factors exactly:

```text
BRT_pole(u) - P_4(u) = 4(1-exp(-u/2))^2 > 0, u>0.          (8)
```

Thus the curvature pair produces a genuine positive scalar boundary pulse but can never saturate
the sharp four-unit HG budget at any positive aperture.

## 3. Positive-operator covariance obstruction

The output-cutoff fast and slow coefficients are

```text
A_u = (3/32)(1-exp(-u)),
B_u = (3/64)(1-exp(-u/2)).                                 (9)
```

For `u>0`, both are strictly positive.  The corresponding signed rank-two covariance core is

```text
C_u(y,z) = A_u exp(-(y+z)/2) - B_u exp(-(y+z)/4).           (10)
```

Compress to samples `{0,L}`.  Exact expansion gives

```text
det [C_u(y_i,y_j)]
  = -A_u B_u (exp(-L/2)-exp(-L/4))^2 < 0, u,L>0.            (11)
```

Consequently the matrix is never positive semidefinite at positive aperture and separation.
Scalar positivity of `(5)` is only positivity of one traced observable; it does not imply
operator-valued positivity.

## 4. Route consequences

- **CCM-HG:** positive scalar boundary pulse survives.  Pair is reporter-selected, not
  arithmetic-source-selected, and undershoots pole trace by `(8)`.  Literal completed-Xi leak
  landing and density `<=4` remain open.
- **CCM-EP:** this particular background is dead.  Equation `(11)` rules out positive operator
  covariance before any cofinal limit or divisor argument.  A surviving EP construction must add
  operator-valued completed-source structure, not repackage this two-rate difference.
- **Route O / G-floor / CCM-GS:** no positive Gram or ground-state merger can use this covariance.
  Any bridge must retain signed boundary orientation or provide an additional positive source
  channel that changes `(11)`.
- **G-exterior:** signed two-channel orientation remains admissible; `(11)` is not an obstruction
  to a Krein/exterior return law.  Literal source realization and return orientation remain open.
- **CCM-FU / CCM-UR:** `(5)` is receiver geometry derived from their exact curvature transport.  It
  supplies no new bound on the actual arithmetic Cesàro primitive.

## 5. Theatre and novelty audit

Known ingredients are elementary exponential Hankel integrals, rank-one kernel algebra, and corpus
boundary-relative-trace identity.  Candidate new residue is their forced composition: positive
pulse `(5)`, four-unit square slack `(8)`, and universal negative covariance minor `(11)` for the
FU--UR-selected pair.

Targeted searches of Connes--Consani archimedean trace/Hankel work, Connes--Consani--Moscovici
prolate work, and general commuting-Hankel literature found no occurrence of this exact pair or
determinant obstruction.  This is not proof of novelty; no priority claim is made.

Falsifiers:

1. Treating `(1)` as source-selected would be false: it comes from limiting reporter kernel.
2. Treating scalar pulse positivity as PSD covariance is refuted by `(11)`.
3. Treating `(8)` as HG closure would be false: it is strict undersaturation.
4. No estimate for literal completed prime-minus-polar source occurs in `(1)--(11)`.

Verdict: `SURVIVES INTERNAL HOSTILE AUDIT` as sharp route classification, not RH step.

## 6. Lean status

`CCMUnitRieszHankelBoundaryPulse.lean` proves unconditionally:

- exact fast/slow densities and `LeakProfile` laws;
- generic exponential Hankel gap `(3)` and specializations `(4)`;
- pulse formula, strict positivity, global bound, and equality at `2 log 2`;
- four-unit normalization and exact square slack `(8)`;
- coefficient positivity, determinant identity `(11)`, strict negativity, and failure of
  `Matrix.PosSemidef` for literal `Fin 2` compression.

## 7. Index of the formalization

Modules: `RHTower/CCMUnitRieszHankelBoundaryPulse.lean`,
`RHTower/CCMUnitRieszCesaroCurvature.lean`.  All declarations are unconditional; `#print axioms`
returns only `propext, Classical.choice, Quot.sound`.

| Card item | Lean declaration |
|---|---|
| `(1)` canonical leak pair | `unitRieszFastLeakProfile`, `unitRieszSlowLeakProfile`, `leakDensity_unitRieszFastLeakProfile`, `leakDensity_unitRieszSlowLeakProfile`, `leakProfile_unitRieszFast`, `leakProfile_unitRieszSlow`, `unitRieszCesaroCurvatureKernel_eq_fast_sub_slow` |
| `(2)` masses and first moments | `integral_unitRieszCesaroFastLeakDensity`, `integral_unitRieszCesaroSlowLeakDensity`, `integral_mul_unitRieszCesaroFastLeakDensity`, `integral_mul_unitRieszCesaroSlowLeakDensity`, `unitRieszCesaro_twoChannel_mass_barycenter` |
| `(3)` generic exponential Hankel gap | `hankelGapProfile_of_leakDensity_exp` |
| `(4)` specializations | `hankelGapProfile_unitRieszFast`, `hankelGapProfile_unitRieszSlow` |
| `(5)` pulse and strict positivity | `unitRieszBoundaryPulse_eq`, `unitRieszBoundaryPulse_pos` |
| `(6)` global bound and equality at `2 log 2` | `unitRieszBoundaryPulse_le`, `unitRieszBoundaryPulse_at_two_log_two` |
| `(7)` four-unit normalization | `unitRieszFourUnitBoundaryPulse_eq` |
| `(8)` exact square slack | `poleBoundaryTrace_sub_unitRieszFourUnitBoundaryPulse`, `unitRieszFourUnitBoundaryPulse_lt_pole` |
| `(9)` output-cutoff coefficients | `unitRieszFastBoundaryCoefficient_pos`, `unitRieszSlowBoundaryCoefficient_pos` |
| `(10)`, `(11)` covariance obstruction | `unitRieszBoundaryCovarianceCore_twoPoint_det`, `unitRieszBoundaryCovarianceCore_twoPoint_det_neg`, `unitRieszBoundaryCovarianceMatrix_det`, `unitRieszBoundaryCovarianceMatrix_not_posSemidef` |
