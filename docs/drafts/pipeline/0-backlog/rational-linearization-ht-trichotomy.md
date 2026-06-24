# Rational linearization HT trichotomy is already source-settled

- **ID:** rational-linearization-ht-trichotomy
- **Stage:** 0-backlog
- **Type:** SOURCE ANCHOR / GATEKEEPER
- **Source:** Becker--Bergweiler via Fernandes survey; Ritt; Di Vizio--Fernandes
- **Priority:** HIGH for avoiding false Feigenbaum and parabolic detours

## Statement

For rational maps of degree at least two, the local linearization functions attached to fixed points are already
classified with respect to differential algebraicity:

1. **Schroeder / Koenigs / Poincare case** (`0 < |mu| != 1`, or repelling inverse form):
   DA occurs only in Ritt's explicit exceptional list. Non-exceptional polynomial/rational Poincare functions
   are HT.
2. **Boettcher / superattracting case**:
   DA occurs only in the Becker--Bergweiler exceptional monomial/Chebyshev forms; otherwise the Boettcher
   function is HT.
3. **Abel / parabolic Fatou-coordinate case**:
   Abel functions for rational maps of degree at least two are always HT.

Thus the rational-map linearization trichotomy is not an open HT frontier. The open Feigenbaum lane lies outside
this theorem because the Feigenbaum map is polynomial-like/scaling-compatible rather than a rational map on the
sphere.

## Source evidence

Fernandes's survey reproduces Becker--Bergweiler's theorem:

- Abel functions are defined for rationally indifferent fixed points after passing to an iterate with multiplier
  `1`.
- Theorem 3.1 says: if a Schroeder, Boettcher, or Abel function is differentially algebraic, then the Schroeder
  function is in the repelling exceptional list, the Boettcher function is in the listed monomial/Chebyshev
  forms, and **the function is not an Abel function**.
- The survey states the immediate corollary: Abel functions are always hypertranscendental.

The same survey explains the proof structure: assuming DA, Becker--Bergweiler use coherent families to pass from
non-repelling cases to repelling periodic points and Ritt's classification, then conclude that a DA linearizer
cannot be Abel and that the Boettcher cases are exactly the listed exceptional ones.

Di Vizio--Fernandes later give a Galoisian proof of the Ritt/Poincare part for rational base maps and a partial
extension to algebraic base functions.

## Promptability audit

This is a source correction, not a new result. The question "are parabolic Fatou coordinates known HT for
rational maps?" is directly answerable by checking Becker--Bergweiler/Fernandes. The work here is to prevent a
false open-problem branch.

## Consequence for current research

The proposed rational linearization trichotomy should be treated as a known source anchor:

- Superattracting rational: source-settled.
- Geometrically attracting/repelling rational: source-settled up to the explicit exceptional list.
- Parabolic rational: source-settled, Abel functions are HT.

The live new territory is not "parabolic rational HT" and not "Koenigs HT for rational maps." It is one of:

1. polynomial-like transfer of the rational theorems, especially for Feigenbaum's `f_lambda(z)=f(lambda z)`;
2. scaling-compatible straightening into a finite algebraic base;
3. genuinely non-rational analytic dynamics where the rational finite-base machinery no longer applies.

The card `ritt-algebraicity-load-bearing.md` shows why the last category cannot be attacked by merely assuming
the local base germ is DA: DA local dynamics can have DA Koenigs coordinates.

## Gates

- [x] 0 -> 1 in-progress: source theorem identified and implication for parabolic route stated.
- [ ] 1 -> 2 fully-proven: team verifies source reading and cross-links Feigenbaum cards.
- [ ] 2 -> 3 formalized: not a Lean target; it is a literature anchor.
- [ ] 3 -> 4 publication-ready: cite only as prior-art boundary in a Feigenbaum note.

## Log

- 2026-06-24 - Created by Haiku after Turing id=1776 proposed the parabolic/Fatou case as possibly open.
  Source check against Fernandes Theorem 3.1 showed the rational Abel case is already covered by
  Becker--Bergweiler.
