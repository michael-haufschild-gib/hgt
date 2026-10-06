# Complete-source projective seam compatibility

- **ID:** TT-C114-SEAM-TUBE
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Route TT; ThetaCuspModularRatioMonotonicity, ThetaCuspModularRatioSlopeBarrier.
- **Statement:** For every actual center x>0, with U=u², K=k and Z=J/u,
  `0 < (9-U)*(9K²-6K-4-9KZ) < 6KU`.

## Goal

Constrain the still-open compact upper-center determinant by a source-derived
relation whose width vanishes at the seam. This is an order-U compatibility
law, not an optimization of an existing numerical constant. It forces
`Z=K-2/3-4/(9K)` at the limiting seam. Its sufficiency for the determinant sign
is a new conjecture, not a proved consequence. No RH conclusion follows yet.

## Complete paper proof [PROVED HERE]

Use the existing unconditional actual-source equations
`u'=kt`, `k'=2(k+1/3)J`, `w'=4+6k-2uJ/3`, `t=9-u²>0`,
and the proved bounds `k>5/4`, `0≤J≤u/3`, `u>0` for x>0.
Set `R=w-2u/3-4u/(9k)` and `q=8(k+1/3)/(9k²)`.
At zero, R=0. Direct differentiation gives

`R'=u²(2k/3+4/9)-2uJ/3+uJq`.

Since k>1 and k²≥k, `0≤q<4/3`. The exact decompositions

`R'=u²(2k/3+2/9)+(2u/3)(u/3-J)+uJq`,

`2ku²-R'=u²(4k/3-2/3)+(2u/3)(u/3-J)+uJ(4/3-q)`

have positive first terms and nonnegative remaining terms. Hence
`0<R'<2ku²` on the whole positive ray and R>0 by its zero initial value.
Define `E=(2/3)u³-tR`. Then E(0)=0 and

`E'=t(2ku²-R')+2uktR>0`.

Thus `0<tR<(2/3)u³`. Finally J=uk-w gives

`(9-U)(9K²-6K-4-9KZ)=(9k/u)tR`.

Multiply the strict bounds by the positive factor 9k/u. This proves the
stated polynomial tube using only already-proved source facts.

## Novelty and Lean status

Two corpus searches completed: `/tmp/tt_c114_compact_determinant_search.json`
and `/tmp/tt_c114_seam_cone_search.json`. Both reported partial=false, but
compiler enrichment remains largely pending/source-only; broad suggested
ingredients were inapplicable. Direct source reads verified all ODE and
projective-ceiling dependencies. Exhaustive targeted text search found no
existing seam-defect or same polynomial tube theorem.

Production `ThetaCuspRatioProjectiveSeamTube.lean` passed its direct leaf audit.
All 12 public declarations passed imported axiom checks; each uses only a
subset of `{propext, Classical.choice, Quot.sound}`. The module is wired
into `RHTower.lean`; no umbrella build was run. Main theorem:
`RHTower.ThetaCuspModularRatio.actual_projective_seam_tube`. Final audit:
`lake --old env lean /tmp/TTC114SeamTubeProductionAudit.lean`.
This does not establish compact determinant positivity.

## Next conjecture

The complete upper determinant is positive on the actual kinetic cone
intersected with this vanishing-width seam tube. Prove or refute this full
polynomial sign, retaining every source moment and load term. If the tube
is insufficient, extract the missing source correlation from the failure.

## Log

- 2026-10-06 — C114: derived complete paper proof from current corpus ODE;
  scratch formalization prepared. Control 7 concurrently completed its
  existing serial certificate: 13/19 controls closed in scratch, production
  audit still pending. One owned Lean process only.

- 2026-10-06 — C114: scratch and production direct/axiom audits passed.
