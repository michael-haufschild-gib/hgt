# Theta Schur quartic asymptotic zero transfer

- **ID:** GTA-PQ4-LSC
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Source:** `rh-current-frontier-map.md` · route GTA (`COF + ORIENT`)
- **Statement:** Uniform decay to zero of positive quartic charge over every Schur packet of the actual finite signed theta-source stages implies the Riemann hypothesis.

## Goal
Replace exact charge zero at every finite theta stage by an asymptotic scalar condition.  The
condition is source-pure after Schur transport: it concerns actual finite corrected theta matrices,
not Xi zeros.  Compact-open determinant completion is already unconditional in the corpus.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem `riemannHypothesis_of_thetaSourceSchurPositiveQuarticCharge_tendsto_zero`, exact module build green, lint and axiom audit pass
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach
For a finite matrix `M` with Schur packet `S`, a zero `z != 0` of `det(1-zM)` forces one
diagonal entry of `S.T` to equal `z^-1`.  Nonnegativity of every packet summand therefore gives the
quantitative lower bound

`sourcePairPositiveQuarticCharge (z^-1).re (z^-1).im <= charge(S)`.

If normalized finite theta determinants converge locally uniformly to normalized `XiC`, any XiC
zero persists in a fixed small closed ball.  At an off-real zero `z`, the reciprocal local charge is
strictly positive and continuous on a sufficiently small ball avoiding zero.  Thus every late-stage
Schur packet has charge bounded below by one fixed positive constant, contradicting uniform charge
decay.  Hence every XiC zero is real and RH follows.

## Conjecturing loop
- `[GTA-PQ4-LSC.1]` Exact zero at every stage. Already Lean-proved but source burden too rigid.
- `[GTA-PQ4-LSC.2]` Decay of one arbitrarily selected Schur packet. Plausible, but introduces a
  noncanonical choice and requires packet-invariance infrastructure.
- `[GTA-PQ4-LSC.3]` Uniform decay over all Schur packets. Current target; choice-free and directly
  contradicted by the reciprocal-zero lower bound.

## Novelty audit
- Internal corpus search on 2026-08-27 found qualitative positive charge from a nonreal divisor and
  finite-prime energy zero transfer, but no reciprocal-zero quantitative quartic lower bound or
  asymptotic theta-stage quartic criterion.
- External literature audit pending. Do not label new science before exact-source comparison.

## Log
- 2026-08-27 — created directly in 1-in-progress after corpus-led conjecture freeze.
