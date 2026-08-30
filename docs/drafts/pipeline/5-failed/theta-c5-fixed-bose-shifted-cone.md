# Theta C5 fixed Bose-shifted cone no-go

- **ID:** CLG-TTF-C5-fixed-bose-shifted-cone
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** `../1-in-progress/theta-c5-likelihood-homotopy-curvature.md` · Conjecture K
- **Statement:** Literal affine theta packet does not satisfy all four nonpositive fixed
  lowest-mode Bose faces throughout structural tail.

## Goal

Conjecture K was intended to close

```text
fixed shifted four-face cone -> M''' > 0 -> convex likelihood lift -> direct-J ->
rank-four/Ptolemy -> CLG/TTF or Weil positivity -> RH.
```

## Gates

- [x] 0 → 1 in-progress: exact source claim and RH chain frozen
- [x] 1 → 2 fully-proven: dependency-closed paper proof and positive survivor
- [x] 2 → 3 formalized: unconditional Lean capstone, targeted build, axiom audit
- [ ] 3 → 4 publication-ready: standalone exposition not prepared

## No-go closure

- **Exact killing theorem/mechanism:** At first-atom endpoint `l=0`, let `P_u(t)` be first fixed
  Bose-shifted face. For every positive seam centre with structural scale at least six,
  `P_u^(k)(0)=0` for `k<7`, while

  ```text
  P_u^(7)(0) = 3360 * thetaCuspC5FirstFaceSeamObstruction(u) > 0.
  ```

  Taylor--Lagrange therefore gives `P_u(t)>0` for all sufficiently small positive `t`. Continuity
  of structural scale keeps those `t` admissible. This contradicts Conjecture K's required
  `P_u(t)<=0`. Lean theorem:
  `RHTower.thetaCuspC5LikelihoodHomotopy_conjectureK_false`.
- **Strongest positive survivor:** Exact seventh-order seam classification above, plus literal
  local theorem
  `RHTower.eventually_thetaCuspC5LikelihoodHomotopy_boseShiftedTransportOne_zero_pos`.
- **New insight:** Fixed physical Bose shift has forced positive first-face orientation at modular
  seam. Any surviving C5 assembly must exploit cancellation in full weighted three-term balance
  or use a different sign architecture; no proof requiring four individually nonpositive fixed
  faces can work.
- **Status:** Paper proof dependency-closed and formalized in
  `ThetaCuspLikelihoodHomotopyBoseFirstFaceSeamNoGo`. Targeted build passes. Axiom audit reports
  only `propext`, `Classical.choice`, and `Quot.sound`. Corpus search found no earlier theorem.
  Primary-literature audit found only Chouikha's complete monotonicity laws
  ([arXiv:1409.1498](https://arxiv.org/abs/1409.1498)) and Planat--Solé's second-level theta-kernel
  concavity ([arXiv:2608.19160](https://arxiv.org/abs/2608.19160)); neither treats affine
  likelihood packet, fixed Bose four-face cone, or this seventh-order seam obstruction.

## Proof architecture

1. Split actual log theta locally into smooth first-atom and likelihood potentials.
2. Classify generated first-face germ through order seven by exact jet convolution.
3. Identify seventh coefficient with source obstruction built from first-atom jets and likelihood
   cumulants.
4. Prove obstruction positive using projective first-atom energy and strict likelihood cooling at
   scale six.
5. Identify smooth germ with literal first face on a punctured right neighbourhood and apply
   Taylor--Lagrange.
6. Instantiate admissible structural centre to negate Conjecture K without hypotheses.

## Log

- 2026-08-30 — Route killed and positive survivor formalized; targeted Lean build and axiom audit
  pass. Broader C5 likelihood-homotopy route remains open only through non-facewise assembly.
