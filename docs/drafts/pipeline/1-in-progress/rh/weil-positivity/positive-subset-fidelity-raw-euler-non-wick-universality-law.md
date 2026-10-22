# Positive subset fidelity / raw-Euler non-Wick universality law

- **ID:** positive-subset-fidelity-raw-euler-non-wick-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** Lean-corpus closure of CCM subset fidelity rigidity and squarefree Euler Wick defect
- **Statement:** Every nonnegative four-coordinate subset mixture with exact full-product fidelity
  collapses to the top subset atom; every nonzero realization of that atom has exact nonvanishing
  shared-Rademacher fourth cumulant `-2 a₀a₁a₂a₃`.

## Goal

Test whether positive subset-channel redistribution can preserve exact Euler multiplicativity and
simultaneously repair the raw source's pairwise Wick defect.  Retain both exact weight
classification and exact cumulant value.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem and exact `lake env lean` green; final axiom audit pending
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Corpus inputs

- `positiveSquarefreeSubsetMixture_eq_fullAtom_of_topMonomialFidelity`
- `eulerSquarefreeWickFourDefect_eq`
- `eulerSquarefreeWickFourDefect_eq_sharedRademacherCumulant`
- `not_eulerSquarefreeWickFourLaw_of_nonzero`

## Proof

`[PROVED HERE]` Exact full-product fidelity on every Boolean face and nonnegative weights invoke
positive subset Möbius rigidity: all proper-subset weights vanish and the full-subset weight is
one.  Thus no positive diagonal or rotated subset redistribution remains; the selected polynomial
channel is the raw top squarefree Euler atom.

For arbitrary nonzero complex local coefficients `a₀,…,a₃`, the raw four-point Euler/Wick defect
is exactly `-2 a₀a₁a₂a₃`.  The corpus identifies the same scalar as the fourth joint cumulant of
the shared-Rademacher packet reproducing all even squarefree moments.  Nonzero local factors make
the defect nonzero, so exact multiplicative fidelity and Wick pair matching cannot coexist in this
positive subset model.

No numerical computation is used.

## Novelty protocol

No literature search before exact Lean proof.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.PositiveSubsetFidelityRawEulerNonWickUniversalityLaw`
- Main theorem:
  `RHTower.positiveFullProductFidelity_forces_rawEulerNonWick`
- Exact source check:
  `lake env lean GaloisForLFunctions/RHTower/PositiveSubsetFidelityRawEulerNonWickUniversalityLaw.lean`
  passed on 2026-07-23.
- Imported by `GaloisForLFunctions/RHTower.lean`.
- Axiom audit and module build deferred to required final audit; no intermediate `lake build`.

## Post-proof literature audit

Performed only after the exact Lean source check passed.

- Döbler–Krokowski, *On the fourth moment condition for Rademacher chaos*
  ([arXiv:1706.00751](https://arxiv.org/abs/1706.00751)), proves that Gaussian-style fourth-moment
  equivalence fails for Rademacher chaos of order at least two.  It does not classify positive
  Boolean subset mixtures by full-product fidelity or derive this exact four-coordinate defect.
- Nourdin–Peccati, *The optimal fourth moment theorem*
  ([arXiv:1305.1527](https://arxiv.org/abs/1305.1527)), gives the Gaussian Wiener-chaos
  fourth-cumulant framework.  It does not contain the Boolean Möbius rigidity step or the
  shared-Rademacher Euler atom appearing here.
- Blass–Sagan, *Möbius functions of lattices*
  ([arXiv:math/9801009](https://arxiv.org/abs/math/9801009)), supplies broad lattice Möbius
  background, not the analytic/probabilistic synthesis proved here.

No exact statement was found combining: nonnegative full-product Boolean fidelity, collapse to the
top subset atom, the exact defect `-2 a₀a₁a₂a₃`, its shared-Rademacher cumulant identification, and
the resulting Wick-law obstruction.  Door 2 therefore remains open rather than claimed closed.

## Log

- 2026-07-23 — same-folder terminal-symbol scan exposed the shared squarefree monomial; theorem
  statements verified before synthesis.
- 2026-07-23 — exact Lean source check passed; post-proof literature audit found adjacent Boolean
  Möbius and fourth-cumulant results but no exact combined law.
