# Tate-clock unilateral boundary defect

- **ID:** tate-clock-unilateral-boundary-defect
- **Stage:** 3-formalized
- **Type:** PROVED IN LEAN / GENERAL HYPERTRANSCENDENCE BRIDGE / OBSERVABLE VALUE DECOMPOSITION
- **Source:** unilateral quantum phase operators and index-one boundary anomalies
- **Statement:** The algebraic Tate clock has canonical forward/backward partial inverses whose failure to be two-sided is exactly the coordinate-zero boundary projector; every Ind/Pro observable pairing is the boundary reading plus the pairing of the two shifted tails.

## Goal

Strengthen the general hypertranscendental clock boundary from separate injectivity, surjectivity,
kernel, cokernel, and adjointness statements to one exact unilateral-shift calculus.  The output must
evaluate observable values, not merely rename the existing exact sequences.

## Gates

- [x] 0 → 1 in-progress: matched the Ind-forward/Pro-backward Tate clock with the index-one unilateral-shift pattern
- [x] 1 → 2 fully-proven: constructed both partial inverses, both boundary projectors, both defect identities, and the boundary-plus-shift pairing law
- [x] 2 → 3 formalized: scratch certification, one exact-target cache build, direct source check, and axiom audit pass
- [ ] 3 → 4 publication-ready: use the boundary-plus-tail recurrence on a source-selected enlarged conormal or corona functional

## Physics source

K. Fujikawa, *Phase Operator for the Photon Field and an Index Theorem*,
arXiv:hep-th/9411066, relates the Susskind--Glogower phase operator's failure of unitarity to its
unit index and rank-one anomalous boundary.  The same one-sided shift geometry underlies covariant
phase/time observables.

The Lean theorem transfers only the exact algebraic shift-defect pattern.  It does not identify the
Tate clock with a photon phase operator and makes no novelty claim about quantum phase theory.

## Exact relation

Let `F` be the forward shift on finitely supported Ind covectors, `B` its backward shift, and `P0`
the coordinate-zero boundary projector.  Lean proves

```text
B F = 1,                 F B = 1 - P0.                   (1)
```

The linearly compact Pro clock has the dual zero-extending forward map `Fpro`, its existing
backward observation `Bpro`, and the existing boundary line `b0`; Lean proves

```text
Bpro Fpro = 1,           Fpro Bpro p = p - b0(p(0)).     (2)
```

Combining `(1)` with the existing Ind/Pro adjointness theorem evaluates every pairing:

```text
<a,p> = a(0)p(0) + <B a, Bpro p>.                        (3)
```

Equation `(3)` is the new value relation.  It localizes all irreversible information loss to one
observable boundary reading and recursively exposes the remaining clock tail.

## Formalization

`formal/GaloisForLFunctions/HTGeometry/TateClockUnilateralShiftDefect.lean` proves:

- `tateClockIndBackward_forward`;
- `tateClockIndForward_backward_eq_sub_boundary`;
- `tateClockInd_boundary_add_forward_backward`;
- `tateClockProBackward_forward`;
- `tateClockProForward_backward_eq_sub_boundary`;
- `tateClockPro_boundary_add_forward_backward`;
- `tateClockPairing_boundary_add_shift`.

## Corpus value

This result applies to the general `HypertranscendentalClockBoundary` construction, independently
of Gamma or zeta.  It sharpens “there is no backward algebraic clock” into a precise observable
statement: on the enlarged self-dual Tate clock, backward observation exists as a partial inverse,
and its complete defect is the rank-one boundary value.  Nothing is attributed to temporal
propagation.

The recurrence `(3)` can simplify any later conormal or corona calculation by peeling one boundary
coordinate at a time.  In particular, a nonzero enlarged conormal cannot hide the boundary defect
behind bulk shift notation: its value is forced to appear either at coordinate zero or in a shifted
tail.  This is the concrete next interface to the existing finite-observable conormal no-go.

## Status

[PROVED IN LEAN] The exact target and direct source check pass.  The audited theorems use only
Lean's standard `propext`, `Classical.choice`, and `Quot.sound` axioms (the Pro defect does not use
`Classical.choice`).  No numerical computation, full project build, or concurrent Lean process was
run.
