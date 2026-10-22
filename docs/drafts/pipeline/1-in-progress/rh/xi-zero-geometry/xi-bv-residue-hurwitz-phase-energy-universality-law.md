# Xi BV-Residue / Hurwitz Phase-Energy Universality Law

- **ID:** LAW443
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Lean-corpus synthesis of
  `XiCCMBVWindowDilationOrientationUniversalityLaw.lean`,
  `BVPrimeWindowDilationOrientation.lean`, and `XiHurwitzPhaseEnergyGrowth.lean`
- **Statement:** For every noncensored compact-BV prime window, every real dilation `r>1`, and
  every right Xi divisor copy, the Hurwitz principal phase is exactly the logarithmic ratio of
  forward/inverse continued-source residue norms.  The recovered source coordinate gives the
  exact Hurwitz orientation defect, a strictly positive atom below total orientation energy, and
  the explicit eventual negative continued-Cauchy floor.

## Goal

Identify an exact transfer—not a conjunction—between a prime-window source observable and the
Hurwitz zero-phase/energy mechanism.  This turns BV residue orientation into a faithful numerical
reader of the transverse Xi coordinate.

## Gates

- [x] 0 → 1 in-progress: opposite Mellin characters and phase-energy theorem found in corpus
- [x] 1 → 2 fully-proven: dependency-closed proof below
- [x] 2 → 3 formalized:
  `xiBVResidue_hurwitzPhaseEnergyUniversality`;
  `lake env lean GaloisForLFunctions/RHTower/XiBVResidueHurwitzPhaseEnergyUniversalityLaw.lean`
  clean; imported by `GaloisForLFunctions/RHTower.lean`
- [ ] 3 → 4 publication-ready: pending standalone exposition and external novelty review

## Statement

Let `R_+(q)` and `R_-(q)` be the actual continued-source residues produced by forward and inverse
argument dilation of a compact BV prime window `W`, and assume its base residue at the right Xi
copy `q` is nonzero.  Define

`Φ_W,r(q) = log (‖R_+(q)‖ / ‖R_-(q)‖) / (2 log r)`.

Then

1. `Φ_W,r(q) = xiHurwitzRightPrincipalPhase(q)`;
2. the Hurwitz orientation defect is `sin(2π Φ_W,r(q))²`;
3. its weighted atom is strictly positive and bounded above by total Hurwitz orientation energy;
4. a continued-Cauchy algebraic reconstruction sequence is eventually below minus one half of
   that same source-recovered weighted atom.

## Paper proof

The corpus proves the exact residue characters

`R_+ = r^(rho-1/2) R` and `R_- = r^(1/2-rho) R`.

For `r>1`, the complex-cpower norm law gives

`‖R_+‖ / ‖R_-‖ = r^(2(Re rho-1/2))`;

the noncensorship hypothesis cancels `‖R‖`.  Taking real logarithms and dividing by `2 log r`
recovers `Re rho-1/2`, which is exactly the corpus definition/theorem for the right Hurwitz
principal phase.  Substitution into the existing exact sine-square defect identity proves (2).
The open critical strip gives `0<Φ<1/2`, hence its sine is positive; the existing summand-to-total
energy theorem gives (3).  Finally substitute the reconstruction identity into the existing
continued-Cauchy phase-to-source negative-value theorem to obtain (4).  All cancellations use
strictly nonzero quantities supplied by `r>1` and source noncensorship. `[PROVED HERE]`

## Novelty boundary

Claim only this corpus-specific exact BV-residue reconstruction and its forced Hurwitz-energy
consequences.  Mellin scaling, generic logarithmic recovery of an exponent, and the separate
phase-energy bounds are prior ingredients.

## Log

- 2026-07-23 — Discovered bottom-up from opposite BV residue characters sharing the exact
  transverse coordinate with the Hurwitz principal phase.
- 2026-07-23 — Dependency-closed paper proof and local Lean lemma-name probe completed before
  external literature search.
- 2026-07-23 — Formalized as a source-coordinate definition, universal certificate, and theorem;
  exact module check passed without warnings.
- 2026-07-23 — Post-proof literature search found generic Mellin/reflection approaches, inverse
  phase work, and zero-related Mellin transforms, but no compact-BV prime-window
  forward/inverse-residue norm reconstruction of the Hurwitz phase or its orientation-energy
  transfer.  No scoped collision found.
