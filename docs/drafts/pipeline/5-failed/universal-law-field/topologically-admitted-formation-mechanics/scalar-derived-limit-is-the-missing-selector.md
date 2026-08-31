# Scalar derived limit is the missing selector

- **ID:** ULF-TAFM-F1
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** local exactness/global selection audit; Route-R Roos and completion-phantom corpus
- **Statement:** The common higher field is a scalar modular inverse tower whose nonzero `lim^1`
  class detects off-wall displacement and whose vanishing supplies selection.
- **Status:** `[FALSIFIED] [LEAN KILLING THEOREMS ALREADY PRESENT] [POSITIVE SURVIVOR EXTRACTED]`

## Goal

Test whether ordinary derived inverse limits turn finite exactness, completion phantoms,
reflection, and global selection into one new source law.

## Exact killing theorem/mechanism

For a one-dimensional vector-space tower with nonzero scalar bond maps, every bond is surjective.
The tower therefore has stable images and its Roos `lim^1` vanishes. If the bonds are all zero, the
Roos difference is also surjective and `lim^1` again vanishes.

The existing Lean corpus proves both implications:

- `derivedLimitOne_subsingleton_of_surjective`;
- `derivedLimitOne_subsingleton_of_hasStableImages`;
- `derivedLimitOne_subsingleton_of_zero_bond` and its stable-image variant.

More generally, at a fixed finite-dimensional stage the descending images of all later stages must
stabilize after finitely many strict dimension drops. Thus a countable tower of finite-dimensional
linear stages is Mittag--Leffler and cannot carry the desired nonzero derived class.

The actual Route-R transgression avoids this theorem only because it uses an infinite-dimensional
summable-sequence ideal with a non-surjective tail bond. The corpus already proves an injective
coefficient-faithful derived class there, nonzero exactly off the wall. Its global vanishing is an
RH-equivalent receiver condition, not an independent source law.

## Strongest positive survivor

Any completion selector carried by `lim^1` must use a genuinely infinite-dimensional,
non-Mittag--Leffler admission tower. Scalar modular factors, finite prime blocks, finite jet spaces,
and finite-dimensional coface packets can only be shadows. The missing source theorem must control
why the relevant infinite effect or admission family is compact/proper; `lim^1` merely records its
failure.

This survivor leads to ULF-TAFM: replace the derived class as primitive by the production law that
forces noncompact effect history whenever nonneutral tensor formation persists.

## New insight

Derived completion correctly locates a global obstruction invisible at finite stages, but cannot
explain why the obstruction must vanish. The higher mechanism must precede the tower and constrain
admitted formation morphisms. This separates **reporter** (`lim^1`) from **producer** (formation
properness).

## Status

Dependency-closed. Killing and positive-survivor infrastructure already exists in Lean; no new Lean
declaration is needed for this retirement.

## Log

- 2026-08-31 -- rejected after full corpus search found the Route-R tail-Roos transgression,
  completion-phantom classifier, stable-image vanishing theorems, and exact RH-equivalent global
  no-phantom condition.
