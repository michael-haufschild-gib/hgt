# HB moving-horizon/AIME temporal optical triangle

- **ID:** HC65
- **Stage:** 3-formalized
- **Type:** THEOREM / CUBIC OPTICAL IDENTITY / LEAN-PROVED HARD FRONTIER
- **Routes:** HB
- **Source:** HC64 moving-event-horizon third mass defect and AIME chiral anti-alignment;
  flux-normalized AIME horizon-history reciprocity defect
- **Statement:** At every Xi fibre and every QNM level, the moving-event-horizon third mass defect
  equals a canonical strictly positive susceptibility times the causal AIME horizon-gain defect.
  Therefore radial third-mass response and temporal Duhamel-history imbalance reinforce one another
  off line, while their common orientation is opposite the chiral AIME kernel. These three concrete
  channels form an exact coefficient-level optical triangle, with unique cancellation ratios.

## Corpus-led conjecture

Let `G_n(q)` be positive/negative AIME horizon-gain difference at `xiSpectralPoint(q)`. Define

`lambda_n(q) = eventThirdMassSusceptibility(q) * (normSq D+ * normSq D-)
               / (8 * conformalDecay(n))`.

Prove:

1. `lambda_n(q) > 0`;
2. `eventThirdMassDefect(q) = lambda_n(q) * G_n(q)`;
3. off line, event-third-mass and temporal-gain defects have strictly positive product;
4. off line, `c * G_n(q) + AIMEKernelDefect(q) = 0` has one exact positive coefficient, obtained
   by dividing HC64's chiral susceptibility by `lambda_n(q)`;
5. the three-channel compensated optical defect vanishes identically;
6. `G_n(q)=0` iff critical-line incidence, and universal extinction at any fixed level is RH.

## Why this is frontier-level

Corpus separately derives a moving-horizon third mass shape derivative and a Duhamel horizon-gain
imbalance, but never identifies their exact relative normalization. The relation is a source-level
radial-to-temporal optical law between concrete cubic channels, narrowing the full `++-` projection
problem from unknown signs to a unique scalar mismatch. It also determines which pair of physical
channels can and cannot cancel before any continuum/direct-vertex contribution is invoked.

## Hostile checks

- Use exact gain denominators and moving-event-horizon susceptibility; no asymptotics or bounds.
- Prove all norm-square denominators strictly positive on Xi fibres.
- Retain signed gain difference before positivity consequences.
- Derive unique coefficient against HC64's chiral AIME defect.
- Do not assert full gauge-fixed `++-` projection equals this three-channel truncation.
- Keep frontier map read-only.

## Novelty boundary as of 2026-08-28

Bounded primary-source audit found AIME as a third-order absorbed-mass effect
(Sberna--Bosch--East--Green--Lehner, 2022), later numerical third-order mass/spin ringdown drift,
and recent causal Green-function models of dynamical QNM excitation. No audited source derives a
completed-zeta Xi-fibre exact susceptibility between a moving-horizon third mass parity jet and a
flux-normalized two-branch AIME Duhamel gain defect, nor its exact optical triangle with the chiral
kernel. This is a bounded, not exhaustive, priority claim.

## Gates

- [x] 0 -> 1 in-progress: corpus gap, exact conjecture, hostile proof route, bounded literature audit
- [x] 1 -> 2 fully-proven: dependency-closed paper proof
- [x] 2 -> 3 formalized: closed Lean theorem, target build, axiom/lint audit, umbrella wire
- [ ] 3 -> 4 publication-ready: independent priority audit and standalone exposition

## Log

- 2026-08-28 — Opened after HC64 showed sign-based AIME exclusion fails and corpus search found an
  independently derived temporal horizon-gain defect carrying the same horizontal coordinate.
- 2026-08-28 — Proved exact radial-to-temporal susceptibility, strict off-line reinforcement,
  three-channel optical triangle, unique chiral closing coefficient, and fixed-level universal
  extinction iff RH in
  `ThetaCuspHawkingMovingHorizonAIMETemporalOpticalTriangle.lean`. Direct Lean passed; target-only
  build passed (`11893/11893`); all nine theorem axiom audits contain only `propext`,
  `Classical.choice`, and `Quot.sound`; umbrella import present. Formal lint has no HC65 finding and
  reports only unrelated pre-existing unreachable modules.
