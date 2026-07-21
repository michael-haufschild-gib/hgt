# Xi completed-density projective heteroclinic barrier

- **ID:** `xi-completed-density-projective-heteroclinic-barrier`
- **Stage:** 5-failed
- **Type:** `[SUPERSEDED OPEN CORE] [POSITIVE SURVIVOR FORMALIZED] [NO RH CLAIM]`
- **Replacement:**
  `../1-in-progress/xi-completed-density-affine-pencil-top-edge-barrier.md`

## Retired conjecture

The former card asked for classification of every negative-real trajectory of `R=E#/E`, including
Wronskian regularity and separation of projective zero/pole endpoints, to exclude an unanchored
trajectory crossing `R=-1`.

## Exact killing mechanism

New transverse Pick geometry proves

```text
E(z)!=0 for every Im z>0.
```

Thus `R` has no poles in the upper half-plane and the proposed zero/pole endpoint problem does not
exist.  More importantly, zero trajectories of the affine pencil

```text
H_tau=((1+tau)/2)E+((1-tau)/2)E#
```

are governed globally by the argument principle.  Interior critical collisions can merge or split
branches but cannot change total zero multiplicity.  Requiring Wronskian regularity everywhere on
the negative ray was therefore unnecessary and stronger than the transport problem.

## Strongest positive survivor

The source-selected transverse cone

```text
Im(z)|F(z)|<=Im(zF(z))
```

and upper zero-freeness of `E` are formalized in
`XiCTaylorThetaTailCompletedDensityTransversePick.lean`.  They reduce all noncompact transport
possibilities to boundary entry and horizontal escape.  Bottom and imaginary boundaries are
already oriented, while theta-Schwartz decay controls horizontal infinity.  The surviving RH-grade
problem is top-edge exclusion for `H_tau`, sharpened to the acute-angle conjecture in the
replacement card.

## New insight

Actual frontier is codimension-one boundary geometry, not two-dimensional projective trajectory
classification.  The growing reflected half-density channel on `Im z=1/2` is the sole source piece
not controlled by the one-sided Pick cone.

## No-go closure

`NO POSITIVE SALVAGE FOUND` does not apply.  Positive survivor is dependency-closed on paper and in
Lean.  Novelty remains unverified externally.

## Log

- 2026-07-21 — superseded after transverse Pick cone eliminated upper poles and affine-pencil
  homotopy removed interior collision regularity from extinction analysis.

