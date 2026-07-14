# Operator-tail differential matroid for prime Dirichlet carriers

- **ID:** operator-tail-differential-matroid
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** referee repair of `prime-dirichlet-tail-differential-matroid`
- **Statement:** For coefficient families on the primes, every finite shift--jet relation is exactly a finite-support relation among the coefficient columns after multiplication by the corresponding exponential-polynomial clock functions; finite-range coefficient families therefore have full shift--jet rank exactly when their recurring joint values span.

## Goal

Replace the signed-Boolean tail theorem by the intrinsic operator-tail law.  The quotient by finitely
supported coefficient functions is acted on by the logarithmic clock and by finite shift factors.
The resulting module, rather than the raw sign cube, is the exact linear object seen by all finite
Dirichlet shift--jet rectangles.  The finite-range projective-tail theorem is to be a sharp,
checkable corollary, and the analytic hypertranscendence claim is to begin only after a separately
stated classical Dirichlet-series Jacobian theorem.

## Gates

- [x] 0 → 1  in-progress: source-pure coefficient law stated; direct finite-support attack; analytic dependency isolated
- [ ] 1 → 2  fully-proven: complete operator-tail equivalence, finite-range corollary, weighted uniqueness, and analytic transfer written without gaps
- [ ] 2 → 3  formalized: Lean theorems for every original algebraic/topological deduction; classical literature theorem exposed as an explicit interface; source builds and axiom audit pass
- [ ] 3 → 4  publication-ready: standalone paper with honest comparison to Pong and Di Vizio--Pellarin, no universality inflation, and no unsupported RH consequence

## Approach

1. Define the finite-support quotient implicitly through `TailCoefficientIndependent`.
2. Prove the taut but structurally exact operator-tail identity: a finite shift--jet rectangle is
   independent precisely when no nonzero coefficient array produces finite support after applying
   its shift factors and clock powers.
3. For a finite joint coefficient range, pass to infinitely recurring fibres.  On each fibre,
   shift--clock rigidity kills the exponential-polynomial row; recurring-value spanning then kills
   every source column.
4. Prove the converse by using a scalar tail relation as a zeroth-order, unshifted row relation.
5. Supply polynomial-weighted Dirichlet uniqueness so clearing denominators cannot annihilate a
   genuine formal relation.
6. State the classical Shapiro--Sparer/Pong Jacobian transfer at its exact boundary and derive the
   analytic differential-independence theorem only from that input.

## Novelty and significance gate

- **Novelty risk:** the analytic transfer belongs to established Dirichlet-series
  hypertranscendence theory.  Any new claim must therefore be the exact multi-source operator-tail
  classifier or a strict consequence not already present in Pong's coefficient criteria.
- **Significance target:** an intrinsic law that identifies the complete finite shift--jet matroid
  and makes scalar projective-tail classification a finite-range corollary.
- **Retirement condition:** if the operator-tail theorem is only a renaming of an existing theorem
  in Pong or Shapiro--Sparer, retain the formal algebra as infrastructure but do not publish it as
  new scientific knowledge.

## Log

- 2026-07-14 — created after referee report exposed that the signed prime cube was decorative and
  that scalar tail independence is not the intrinsic invariant outside finite joint range.
