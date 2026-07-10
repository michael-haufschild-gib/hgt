# Finite divisor-prefix orbit nonselection (no jets)

- **ID:** finite-divisor-prefix-orbit-nonselection
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** verified-height amplification; divisor-orbit reformulation
- **Statement:** `[PROVED IN LEAN]` Any finite positive critical-line divisor with arbitrary multiplicities, together with any finite exact Euler head, admits both an FE/Schwarz extension by a fresh simple fixed orbit and an FE/Schwarz extension by a simple free orbit at any prescribed generic off-line point of the open strip, while preserving every old multiplicity exactly.

## Goal

Test the verified-zero input as a divisor rather than as a height interval or a finite jet.  The
result determines whether the complete finite divisor output of a Platt--Trudgian-style certificate,
combined with flat reflection symmetry and any finite Euler head, can select the orbit type of an
extension.

## Gates

- [x] 0 → 1 in-progress: exact orbit-extension question and collision conditions stated.
- [x] 1 → 2 fully-proven: explicit product proof with no open dependency.
- [x] 2 → 3 formalized: Lean theorem `RHTower.finiteDivisorPrefix_orbitNonselection`; direct module and axiom checks pass.
- [ ] 3 → 4 publication-ready: not applicable; the result is classified `[BRIDGE]`, not new knowledge.

## Proof

For a finite set `S` of positive ordinates and multiplicity function `m`, form the product of the
critical-line pairs `linePair τ ^ m τ`.  Positivity makes distinct representatives collision-free,
so additivity of analytic order gives exact order `m τ` at every prescribed point.

Multiplication by a fresh `linePair η` adds a simple fixed reflection orbit and is nonvanishing at
all old representatives.  Multiplication by `orbitQuartic ρ` adds a simple free `V4` orbit at any
off-line, off-real strip point and is nonvanishing on the critical line.  The finite Euler bundle is
zero-free in the open strip, so it changes none of these orders.  Both products retain the same
functional equation and Schwarz symmetry.

No derivative, Taylor coefficient, local expansion, or jet occurs in the statement or proof.

## Research classification

`[BRIDGE]` The theorem is rigorous and strengthens the repository interface from an empty verified
region to an arbitrary exact verified divisor prefix.  It does not clear the novelty × significance
gate: the mathematical mechanism is finite polynomial packing, and the carriers are not the
completed zeta function.  In particular, it does not increase the numerical lower bound for a
possible RH counterexample.

`[OPEN CORE]` A positive amplifier must impose a genuinely infinite source constraint that is not
preserved by multiplication with a free-orbit quartic.  The missing object is therefore not more
finite divisor data and not a jet, but a global source-to-divisor selection law.

## Log

- 2026-07-10 — Paper proof and Lean formalization completed; direct and umbrella builds, axiom audit, and formal lint pass. Classified as formalized/not-new after the anti-theatre and dual-gate checks.
