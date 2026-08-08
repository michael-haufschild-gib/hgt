# NAD Stage-2 unconditional Lean sweep

- **ID:** `nad-stage2-unconditional-lean-sweep`
- **Stage:** 1-in-progress
- **Type:** FORMALIZATION PROGRAM
- **Scientific status:** `[IN PROGRESS] [NO AXIOMS] [NO HYPOTHESIS WRAPPERS]`
- **Scope:** Every one of the 58 cards currently under
  `docs/drafts/pipeline/2-fully-proven/nad`, including every dependency-closed theorem proved on
  paper in those cards.

## Completion rule

A source card is complete for this sweep only when its proved mathematical result—not merely an
algebraic shadow or conditional interface—is represented by an unconditional, closed Lean theorem;
all new modules are imported by the appropriate umbrella; targeted source checks and final module
builds pass; capstone axiom output contains only standard Lean foundations; generated indexes and
formal lint pass; and the card is moved to `3-formalized/needs-audit` with accurate residual
publication/novelty gates.

Future conjectures, RH consequences, experimental realizations, novelty reviews, and publication
work are not formalization debt unless the card labels them proved.

## Current dependency strategy

1. Audit all 58 cards against existing declarations before adding code.
2. Reuse shared missing foundations across cards: complex analysis, Nevanlinna/moment theory,
   differential algebra, rational dynamics, operator/QFT interfaces, and special functions.
3. Close leaf theorems before capstones; never encode a missing theorem as a premise, structure
   field, axiom, or opaque declaration.
4. Verify each leaf with `lake env lean <file>` and one foreground Lean process. Build only the
   affected module for final audit, then check umbrella import directly.

## Completed during this sweep

- `geometric-cdd-tail-flat-jt-projective-limit`: strict no-wrapper audit passed for the universal
  positive-shell and concrete geometric capstones; targeted source checks, axiom prints, and final
  module build passed. Card promoted to `3-formalized/needs-audit`.
- `fermionic-zero-braid-anchor-commutation-gate`: exact finite-dimensional local-product
  diagonalization theorem implemented in
  `HTGeometry/FermionicZeroBraidLocalProductDiagonalization.lean`, supported by the arbitrary
  star-commuting simultaneous spectral theorem in
  `HTGeometry/CommutingNormalMatrixEigenbasis.lean`. Source checks, final targeted build, and axiom
  audit passed; card promoted to `3-formalized/needs-audit`.
- `prime-replication-profile-grassmann-completion-law`: all eight exact prime-clock
  correspondence clauses plus the closed analytic Euler completion barrier re-audited. Four
  targeted module builds passed; nine representative capstones depend only on `propext`,
  `Classical.choice`, and `Quot.sound`; all modules were already umbrella-wired. Card promoted to
  `3-formalized/needs-audit`.
- `global-confocal-support-transform-bifurcation-law`: all five all-radius transform clauses
  passed strict signature audit, direct capstone source check, seven-theorem axiom audit, umbrella
  check, and final targeted build. Card promoted to `3-formalized/needs-audit`.
- `projective-wigner-smith-nonabelian-ht-separation`: missing minimal-tomography lower bound added
  in Lean. Exact source check, two downstream targeted builds, seven-capstone axiom audit, and
  umbrella audit passed. Card promoted to `3-formalized/needs-audit`.
- `theta-likelihood-modular-seam-transport`: exact all-order score polynomials, degree and leading
  coefficient, odd normalized score expectation, strict thermodynamic bracket, genuine
  Radon--Nikodym/log-likelihood and directed KL identities, strict positivity, and Jeffreys flux
  implemented in two wired modules. Direct source checks, targeted builds, and eleven-capstone
  standard-foundation-only axiom audit passed. Card promoted to `3-formalized/needs-audit`.
- `arxiv-2026-electrical-optical-frontier-harvest`: formalization scope audited as exactly empty.
  Card reports external literature, rejected interfaces, and open producer obligations but proves
  no new local theorem. Promoted to Stage 3/N-A without manufacturing a Lean wrapper.
- `semilocal-one-prime-harmonic-moment-defect`: literal normalized Gamma/Poisson defect quotient,
  strict positivity, explicit uniform `42/p^2` remainder, harmonic prime divergence, Hilbert-space
  trace-norm obstruction and its nonsummable family form, and exact finite-prime mixed-packet
  survivor implemented in one wired module. Direct source check, targeted build, and eight-capstone
  standard-foundation-only axiom audit passed. Card promoted to `3-formalized/needs-audit`.

## Open core

- Exhaustive per-card theorem/declaration inventory.
- Shared-dependency graph and formalization order.
- Exact closures and audits for every card not already unconditionally formalized.

## Log

- 2026-08-08 — Scope clarified from one candidate to all 58 Stage-2 NAD cards. Coordination card
  opened. First exact capstone and semantic ON-basis bridge completed without new axioms.
- 2026-08-08 — Prime-clock master correspondence and closed Euler completion consequence passed
  strict no-wrapper, targeted-build, umbrella, and axiom audits; third source card promoted.
- 2026-08-08 — Global confocal/support transform, radical bifurcation, transform faithfulness, and
  maximal-hull equality passed exact Stage-3 audit; fourth source card promoted.
- 2026-08-08 — Theta likelihood modular-seam card’s three paper-only gaps closed algebraically and
  information-theoretically; sixth source card promoted with exact all-order and KL capstones.
- 2026-08-08 — Electrical/optical frontier harvest promoted as N/A after confirming it introduces
  no local theorem and all cited results remain external literature rather than project axioms.
- 2026-08-08 — Projective Wigner–Smith card’s hidden minimality omission closed by a trace-kernel
  dimension theorem and universal reporter lower bound; fifth source card promoted.
- 2026-08-08 — Semilocal one-prime harmonic defect card closed without surrogate inputs: exact
  series quotient, explicit asymptotic error, Euler divergence, trace-class nonsummability, and
  positive global mixed-packet survivor all passed Lean and final targeted audit.
