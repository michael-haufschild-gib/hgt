# Hedenmalm orientation vertical-mesh lower bound forces RH

- **ID:** `hedenmalm-orientation-vertical-mesh-lower-bound-rh`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / VALUE-RELATION BRIDGE
- **Scientific status:** `[PROVED] [LEAN] [BRIDGE] [NOT AN RH PROOF]`
  `[NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent:** `hedenmalm-orientation-upper-singularity-ceiling-rh.md`
- **Statement:** At one positive aperture, eventual lower boundedness of the real canonical
  orientation multiplier on every reciprocal vertical mesh above the singularity ceiling forces
  RH.

## Theorem

Let

```text
epsilon_n = 1/(n+1),
Q_a(b) = (xi'/xi)(1/2+a+i b) + (xi'/xi)(1/2+a-i b).
```

For one `a>0`, assume that for every center `b` with `Im b>a` there is a finite real `L_b` such
that eventually

```text
L_b <= Re Q_a(b+i epsilon_n).
```

Then RH holds.

## Proved top-down chain

```text
eventual lower bound on every upper reciprocal vertical mesh
  -> no forced left-boundary singularity can lie above Im b=a
  -> every Xi left 2a-translation-boundary zero has Re rho>=1/2
  -> positive translation-boundary exhaustion
  -> every Xi zero has Re rho>=1/2
  -> functional-equation reflection
  -> every Xi zero has Re rho=1/2
  -> RH.
```

At a forced boundary singularity `b_rho`, the exact multiplicity residue germ gives

```text
epsilon_n Re Q_a(b_rho+i epsilon_n) -> -m_rho,
```

where `m_rho>=1`.  Since `epsilon_n>0` tends to zero, any eventual finite lower bound for
`Re Q_a` contradicts this negative scaled limit.

## Formal theorem surface

The implementation is in
`formal/GaloisForLFunctions/RHTower/HedenmalmOrientationVerticalMeshRH.lean`:

```text
orientationVerticalMeshEpsilon
orientationVerticalMeshEpsilon_tendsto_zero
tendsto_orientationVerticalMeshEpsilon_mul_re_canonicalOrientation_of_leftBoundary
XiCanonicalOrientationUpperVerticalMeshLocallyBoundedBelow
xiLeftShiftBoundary_re_ge_half_of_orientationUpperVerticalMeshLocallyBoundedBelow
riemannHypothesis_of_orientationUpperVerticalMeshLocallyBoundedBelow.
```

Targeted builds, the formal lint, index refresh, and the axiom audit are green.  The residue limit
and RH capstone depend only on `propext`, `Classical.choice`, and `Quot.sound`.

## Value-relation significance

This removes analytic continuation from the sufficient hypothesis.  The source task is only a
countable one-sided value bound along a fixed canonical mesh at each upper-half-plane center.  It
is still Xi-dependent and terminal; no unconditional source bound or converse is claimed.  Its
possible advantage is that prime--Gamma or theta formulas may control sampled values without first
constructing a holomorphic continuation of the entire multiplier.

## Gates

- [x] 0 -> 1 in-progress: exact value condition and residue mechanism stated
- [x] 1 -> 2 fully-proven: scaled residue limit and contradiction proved
- [x] 2 -> 3 formalized: Lean theorem, targeted build, axiom audit, lint, and index green
- [ ] 3 -> 4 publication-ready: not claimed; bridge-level result only

## Log

- 2026-07-13 — created after weakening the upper singularity ceiling to a vertical sampled-value
  condition using the exact residue germ.
- 2026-07-13 — formalized and promoted to stage 3 after targeted verification.
