# <Title>

- **ID:** <short-id>
- **Stage:** 0-backlog
- **Type:** CONJECTURE | CANDIDATE | THEOREM (paper) | THEOREM (Lean) | FALSIFIED
- **Source:** ../../door/<bucket>.md · 00-status row #N
- **Statement:** <one line>

## Goal
<what proving it gives; the non-circularity / Door note>

## Gates
- [ ] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem `<name>`, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach
<the line of attack>

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** <what fails and why>
- **Strongest positive survivor:** <non-trivial positive theorem, classification, invariant, or `NO POSITIVE SALVAGE FOUND` after a serious second pass>
- **New insight:** <what the survivor changes in the representation or open core>
- **Status:** <internal/external audit; paper-proof dependencies; exact Lean theorem/module if dependency-closed>

Do not count a restated negation, vacuous corollary, or renamed known fact as positive salvage. If
the survivor is dependency-closed on paper, formalize the exact theorem in Lean before closing the
no-go.

## Log
- YYYY-MM-DD — created in 0-backlog
