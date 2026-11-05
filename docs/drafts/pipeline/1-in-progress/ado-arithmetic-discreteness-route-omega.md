# Route Ω — arithmetic discreteness (obstacles-summary review-0511 §2.4)

- **ID:** ADO
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (programme)
- **Source:** docs/reports/review-0511/obstacles-summary.md §2.4, §2.7.4 (Field IV), B54
- **Statement:** purity by (i) a pure member, (ii) continuity of the zeros along a deformation,
  (iii) a discrete (integral) structure on near-coincidences forcing collide-or-repel.

## Goal
Decide what discreteness can and cannot produce, calibrate it exactly over `𝔽_q`, and locate the
exact statement it would need for `ζ`.

## Lean
Folder `formal/GaloisForLFunctions/ArithmeticDiscreteness/`, umbrella
`ArithmeticDiscreteness.lean`, wired into `MainTheorems.lean`.

## Conjectures (status)

| # | Statement | Status |
|---|---|---|
| Ω1 | Distinct complex roots of every monic `f ∈ ℤ[X]` with roots in `|z| ≤ R` repel: `1 ≤ |α−β|(2R)^{(n−1)²+n−2}` (no separability) | open |
| Ω2 | Impurity is quantized: a root of an integral trace polynomial is pure, or `|Im τ| ≥ ε₀/2`, or `|τ| − 2√q ≥ ε₁` | open |
| Ω3 | Discreteness is not a producer: impure integral trace polynomials exist in every degree | open |
| Ω4 | Finite certificate: power sums bounded at `2g` consecutive orders past an explicit `M₀` certify purity of an integral configuration; false for real configurations at every finite set of orders | open |
| Ω5 | Paths: continuous integral families are constant; uniform repulsion along a continuous real family carries reality from one member to all (integrality not needed) | open |

## Log
- 2026-11-05 — created; route analysis below.

## Route analysis
- On a connected parameter set an integral structure of bounded degree cannot move (Ω5), so step
  (iii) of the sketch cannot act along a continuous path; uniform repulsion along a path is the same
  as "no collision forms" and needs no integrality (Ω5). The `𝔽_q` mechanism is not a path.
- What integrality does over `𝔽_q`: it quantizes impurity (Ω2) and so turns approximate purity, or a
  size bound at finitely many orders, into exact purity (Ω4). It never produces purity: fake
  integral configurations exist (Ω3).
- For `ζ` the analogue of Ω2 is a depth gap: every off-line zero at height `T` has depth `0` or
  `≥ δ(T)` (B54 restricted to FE pairs). An amplifier also needs approximate purity at scale `δ(T)`;
  the only corpus producer of it is window positivity (F6), i.e. Σ.
