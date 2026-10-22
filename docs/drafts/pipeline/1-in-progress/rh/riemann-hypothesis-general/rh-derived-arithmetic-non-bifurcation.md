# Derived Arithmetic Non-Bifurcation

- **ID:** DANB
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `rh-current-frontier-map.md` · DANB active route
- **Statement:** `[CONJECTURE]` For every internal Xi jet order `m`, literal coefficient-faithful Möbius–theta/Euler–Gamma completion has zero reflection-odd relative cotangent complex over `J_m = C[epsilon]/(epsilon^(m+1))`.

## Public sentence

Arithmetic completion may preserve an individual zero's internal multiplicity defect, but cannot
turn one prime-labelled infinitesimal source event into two different reflected transverse events.

## Goal

Construct the completion and its relative cotangent object before divisor selection, prove the
stated vanishing from source structure, identify functional-equation and Schwarz presentations as
two lifts of one reduced source map, and use the existing transverse-dual-number classifier to force
`Re(rho)=1/2` for every Xi divisor.

Non-circularity requirement: do not assume formal unramifiedness of `XiTransverseArcAlgebra`, framed
reflection descent, absence of completion phantoms, closed graph admission, source-linear sewing, or
any other corpus theorem already equivalent to RH.

## Exact objects to audit and freeze

- `J_m`: `TruncatedArcAlgebra C m`; internal multiplicity lives in base and is never reduced.
- finite source stage `A_(P,d,m) = product_(nu : P → Fin(d+1)) J_m`.
- source pro/ind-system: transition maps induced by enlarging finite prime support and valuation
  depth, with the direction fixed by actual coefficient restriction/extension maps.
- completed source algebra: completion selected by literal target-free Möbius–theta rungs and
  Euler–Gamma/prime-normal source topology, not by a divisor or horizontal grade.
- reflection `tau`: source-defined FE/Schwarz involution on completed object.
- claimed object: reflection-odd summand `e_- L_(Ahat_m/J_m)`, with
  `e_- = (1-tau)/2` over `C`.

The statement is not considered well-typed enough for proof work until corpus audit identifies the
actual transition system, completed algebra, and reflection action without inventing replacements.

## Current labels

- `[LEAN-PROVED]` Finite-stage bridge:
  `internalJetPrimeCylinderAlgebra_formallyEtale` and
  `no_arithmeticCylinderTransverseBifurcation` in
  `formal/GaloisForLFunctions/RHTower/PrimeCylinderRelativeEtale.lean`.
- `[CORPUS]` Off-line Xi placement gives a faithful transverse dual-number arc and a formally
  ramified transverse image; critical placement collapses that transverse algebra while retaining
  internal nilpotents (`XiTransverseDualNumberArc.lean`).
- `[CORPUS]` Finite exactness does not prevent a completed phantom; global phantom-freeness is
  RH-equivalent (`RouteRCompletionPhantomNoether.lean`).
- `[OPEN CORE]` Prove source-specific derived completion preserves reflection-normal lift uniqueness
  without assuming any RH-equivalent completion admission.
- `[NOVELTY UNVERIFIED]` No completed external priority audit yet for the exact frozen statement.

## Gates

- [x] 0 → 1 in-progress: source-pure target identified; finite bridge and falsifiers exist
- [ ] 1 → 2 fully-proven: exact completion frozen; external audit complete; dependency-closed proof
- [ ] 2 → 3 formalized: exact unconditional Lean theorem; target build, lint, and axiom gate pass
- [ ] 3 → 4 publication-ready: standalone theorem, proof, Lean certificate, and novelty audit

## Approach

1. Recover actual finite observer/source system already formalized around Route-R completion phantom,
   prime-Walsh cylinders, complete occupations, and Möbius–theta prime-normal landing.
2. Determine whether system is ind-étale, pro-étale, adic, bornological, or none of these; do not
   force it into derived-adic language if transition maps/topology disagree.
3. Identify exact derived obstruction carried by known completion phantom/TailRoos/Noether shadows.
4. Search for a source theorem—pro-Tor-unitality, weak proregularity, Mittag-Leffler exactness,
   nuclear exactness, or a new coefficient-faithful replacement—that kills only reflection-odd
   obstruction while preserving internal jet.
5. Hostile-test on explicit completion counterexamples and on corpus's strict-right Xi certificate.

## Falsifiers

- Literal source completion carries a nonzero reflection-odd relative cotangent class before divisor
  selection.
- FE and Schwarz maps are not lifts over one internal base, but merely different target gauges.
- Finite source stages do not form the transition system used by actual Möbius–theta completion.
- Required continuity principle is equivalent to no-completion-phantom/RH rather than derived from
  independent source hypotheses.
- Higher prime compounds or valuation depths are lost by cotangent/cyclic completion.

## Risky consequence

If true, every source-compatible reflection-odd infinitesimal observable—not only Xi-zero
displacement—must vanish after literal completion. This predicts a pre-divisor annihilation theorem
for the completed source normal class, stronger than pointwise critical-line classification and
testable without enumerating zeros.

## No-go closure

- **Exact killing theorem/mechanism:** Open.
- **Strongest positive survivor:** Open.
- **New insight:** Open.
- **Status:** Active Stage 1.

## Log

- 2026-08-24 — Card created after CP/Stinespring CADR was falsified by phase/orientation erasure.
- 2026-08-24 — Finite internal-jet prime-cylinder non-bifurcation Lean-proved; global completion
  passage explicitly left open.
- 2026-08-24 — `[FALSIFIED AS STATED]` Actual Route-R finite observers are source-marked finite
  truncation states in a provenance topology, not the finite product-algebra pro-system posited
  above. Formal etaleness of `A_(P,d,m)` therefore does not address the physical completion
  phantom. Positive survivor: lift uniqueness must be formulated as left-exact end hyperdescent on
  the actual arithmetic refinement category. Successor card:
  `rh-arithmetic-constraint-hyperdescent.md`.
