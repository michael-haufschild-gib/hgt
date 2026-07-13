# One-aperture Hedenmalm upper-singularity ceiling forces RH

- **ID:** `hedenmalm-orientation-upper-singularity-ceiling-rh`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / TERMINAL BRIDGE
- **Scientific status:** `[PROVED] [LEAN] [BRIDGE] [NOT AN RH PROOF]`
  `[NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent:** `hedenmalm-canonical-orientation-singularity-carrier.md`
- **Statement:** At any positive aperture `a`, analyticity of the canonical Hedenmalm orientation
  multiplier throughout the upper half-plane `Im b > a` forces RH.

## Theorem

Write

```text
Q_a(b)
  = (xi'/xi)(1/2+a+i b) + (xi'/xi)(1/2+a-i b).
```

For one fixed real `a > 0`, assume the one-sided singularity ceiling

```text
not AnalyticAt Q_a b  ->  Im b <= a.
```

Equivalently, `Q_a` is analytic at every point of the open half-plane `Im b > a`.  Then the
Riemann hypothesis holds.

## Proved top-down chain

```text
Sing(Q_a) subset {b : Im b <= a}
  -> every Xi left-shift-boundary zero for h=2a has Re rho>=1/2
  -> every Xi zero reaches such a boundary after finitely many h-predecessors
  -> every Xi zero is boundary + n h
  -> every Xi zero has Re rho>=1/2
  -> functional-equation reflection gives Re rho<=1/2
  -> every Xi zero has Re rho=1/2
  -> RH.
```

The first implication uses the forced-singularity map

```text
b = -i (rho - (1/2+a)),
Im b = 1/2+a-Re rho.
```

Thus `Im b <= a` gives `Re rho >= 1/2`.  Every successor is translated right by the positive
amount `2a`, so the same inequality holds at every Xi zero.  No lower singularity bound, aperture
threshold, exact two-line placement, positivity, or zero enumeration is needed.

## Positive general theorem extracted

The previously private predecessor argument is now exported:

```text
If S is contained in {Re z > 0} and h>0, then every z in S has a finite
left h-predecessor chain ending in leftShiftBoundary S h.
```

The Xi specialization is also exported as a reusable terminal criterion: if all left-boundary
zeros for one positive translation have real part at least `1/2`, then RH follows by exhaustion
and reflection.

## Formal theorem surface

The general predecessor theorems are in
`formal/GaloisForLFunctions/TranslatedStripBoundary.lean`:

```text
exists_nat_le_sub_mem_leftShiftBoundary_of_re_lt
exists_nat_sub_mem_leftShiftBoundary.
```

The capstone module is
`formal/GaloisForLFunctions/RHTower/HedenmalmOrientationUpperSingularityCeilingRH.lean`:

```text
XiCanonicalOrientationUpperSingularityCeiling
xiLeftShiftBoundary_re_ge_half_of_orientationUpperSingularityCeiling
xiZeroSet_re_ge_half_of_leftShiftBoundary_re_ge_half
xiZeroSet_re_eq_half_of_leftShiftBoundary_re_ge_half
riemannHypothesis_of_xiLeftShiftBoundary_re_ge_half
riemannHypothesis_of_orientationUpperSingularityCeiling
riemannHypothesis_of_canonicalOrientation_analyticOnNhd_upperHalfPlane.
```

Targeted builds, the formal lint, index refresh, and the axiom audit are green.  The exported
capstones depend only on `propext`, `Classical.choice`, and `Quot.sound`.

## Non-circularity boundary

The ceiling hypothesis is a domain-of-analyticity statement about one canonical multiplier, not a
pointwise assertion about every Xi zero.  It is nevertheless Xi-dependent and terminal: this card
does not prove the ceiling from prime--Gamma or theta data.  It is therefore a bridge, not an
unconditional RH proof.

The open source problem is to prove upper-half-plane analyticity of `Q_a` from its prime--Gamma
representation, or to find a weaker source-pure condition implying the boundary inequality.

## Gates

- [x] 0 -> 1 in-progress: exact hypothesis, predecessor mechanism, and circularity boundary stated
- [x] 1 -> 2 fully-proven: complete proof with no hidden divisor assumptions
- [x] 2 -> 3 formalized: Lean theorems, targeted builds, axiom audit, lint, and index green
- [ ] 3 -> 4 publication-ready: not claimed; bridge-level result only

## Log

- 2026-07-13 — prior-corpus search found the bounded predecessor argument only as a private local
  claim in `TranslatedStripBoundary.lean`.
- 2026-07-13 — exact two-line placement weakened to the one-sided upper singularity ceiling.
- 2026-07-13 — the provisional `a >= 1/4` threshold was removed: positive successor translation
  preserves the boundary inequality, and reflection supplies the opposite inequality.
- 2026-07-13 — formalized and promoted to stage 3 after targeted verification.
