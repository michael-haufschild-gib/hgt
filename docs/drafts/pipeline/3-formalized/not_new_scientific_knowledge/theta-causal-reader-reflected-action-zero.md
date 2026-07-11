# The causal square-rate reader annihilates the reflected theta half

- **ID:** theta-causal-reader-reflected-action-zero
- **Stage:** 3-formalized
- **Type:** THEOREM / ROUTE NO-GO, `[BRIDGE]`
- **Date:** 2026-07-11
- **Lean:** `formal/GaloisForLFunctions/RHTower/XiThetaSquareRateReflectedAction.lean`
- **Statement:** In the global shifted heat coordinate, every causal `L2` reader has exactly zero
  action on the reflected completed-theta half; reorienting that half instead reproduces the
  positive source and creates no independent charge.

## Constraint

Let

```text
h_+(u) = 1_(0,infinity)(u) h(u),
h_-(u) = h_+(-u),
y = exp(u) - 1.
```

The reflected action must be computed using the same coordinate as the positive square-rate reader.
Choosing a new coordinate for the reflected term is allowed only if the resulting datum is audited
for independence.

## Theorem A `[PROVED IN LEAN]`: reflected shifted-heat support

Define the reflected shifted-heat profile on its natural coordinate domain `y > -1` by

```text
H_-(y) = T(h_-)(y),
T(f)(y) = (1/2) exp(-log(1+y)/4) f(log(1+y)).
```

Then

```text
H_-(y) = 0  for y >= 0,
H_-(y) = 0  for y <= -1.
```

Indeed, `u < 0` maps exactly to `-1 < y < 0`.  The proof does not impose the upper support by
definition: on `y >= 0`, `log(1+y) >= 0`, and the reflected theta source itself vanishes there.

Lean theorems:

- `xiThetaReflectedShiftedHeatProfile_eq_zero_of_nonneg`;
- `xiThetaReflectedShiftedHeatProfile_eq_zero_of_le_neg_one`.

## Theorem B `[PROVED IN LEAN]`: every causal reflected action is zero

For any `r in L2(R)` with lower support at zero, define

```text
A_ref(r) = integral_R conjugate(r(y)) H_-(y) dy.
```

Then

```text
A_ref(r) = 0.
```

For almost every `y < 0`, causality gives `r(y)=0`; for `y >= 0`, Theorem A gives `H_-(y)=0`.
Thus the integrand vanishes almost everywhere.  Applying the theorem to the canonical reader gives

```text
A_ref(thetaHeatRateSourceReaderL2(n)) = 0
```

for every physical index `n >= 1`.

Lean theorems:

- `causalReaderReflectedThetaAction_eq_zero`;
- `thetaHeatRateSourceReaderL2_reflectedThetaAction_eq_zero`.

## Theorem C `[PROVED IN LEAN]`: reorientation duplicates the positive datum

If the reflected half is reoriented before the heat change of variables, then

```text
h_-(-u) = h_+(u).
```

This is `xiThetaReflectedSource_reoriented`.  Consequently the alternative positive heat
coordinate for the reflected term feeds the reader the same positive source again.  It is not a
second sign or charge variable.

## Balanced-Perron composition and route verdict

The direct reader calculation has only the trivial sign law `A_ref = 0`.  The remaining admissible
Perron source is `h_+`; `xiThetaPositiveSourcePerronCharge_tendsto_zero` already proves that its
negative-line source charge tends to zero beyond unit radius.  The coefficient recovered by the
canonical seam therefore lives in the cross-line residue, not in a reflected source contribution.

The last possible reader-dependent term was the moving logarithmic boundary.  It is already proved
to be the exact conjugation coboundary

```text
T_a P_+ T_(-a) - P_+
```

with zero translation curvature in `XiThetaBoundaryCoboundary.lean`.

`[FALSIFIED AS AN RH ROUTE]` The causal square-rate reader produces no nontrivial reflected
completed-theta sign, parity, or charge:

1. in one global coordinate its reflected action is exactly zero;
2. after reorientation it duplicates the positive half;
3. the positive-half Perron source charge tends to zero;
4. the moving-boundary remainder is an exact flat flow coboundary.

The valid reader remains coefficient-extraction infrastructure.  It cannot be the missing
source-side RH rigidity mechanism.

## Scientific-status audit

The support-orthogonality proof is a direct consequence of the exact coordinate change and causal
support.  The reorientation identity is definitional.  The result is decisive for project route
selection but does not pass the scientific-novelty gate; it is classified as `[BRIDGE]`.

## Certificate

- Targeted source check: passed.
- Targeted module build: passed, 8610 jobs.
- Axiom audit: `[propext, Classical.choice, Quot.sound]` only.
- Active `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`: none in the new module.

## Gates

- [x] 0 → 1: exact support calculation isolated; no divisor or RH-equivalent hypothesis enters.
- [x] 1 → 2: paper proof and route verdict complete.
- [x] 2 → 3: formalized in `XiThetaSquareRateReflectedAction.lean`; targeted build and axiom audit
  passed.
- [ ] 3 → 4: not promoted; this is a routine bridge and route obstruction, not new scientific
  knowledge.
