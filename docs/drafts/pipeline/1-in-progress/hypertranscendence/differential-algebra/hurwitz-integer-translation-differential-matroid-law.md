# Hurwitz integer-translation differential-matroid law

- **ID:** `hurwitz-integer-translation-differential-matroid-law`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Scientific status:** `[CONJECTURE] [MAIN-LAW CANDIDATE]`
- **Statement:** Under augmented rational independence of one representative from each
  integer-translation class, the differential matroid of the corresponding analytically continued
  Hurwitz functions is exactly the partition matroid of those classes.

## Goal

Let `I` be finite, let `s : I → ℂ`, and put `i ~ j` when `s i - s j ∈ ℤ`.  Choose one exponent
`t c` from every equivalence class and assume that `1,(t c)_c` is linearly independent over `ℚ`.
For the concrete upper-half-plane analytic continuations

\[
  H_i(a)=\zeta(s_i,a),
\]

prove the exact independent-set law

\[
  (H_j)_{j\in J}\text{ is differentially algebraically independent over }\mathbb C(a)
  \quad\Longleftrightarrow\quad
  J\text{ contains at most one index from every }\mathbb Z\text{-translation class}.
\]

Consequently the differential rank of the full family is the number of integer-translation
classes.  This is the intended single main law; analytic continuation, the differential ladder,
and arithmetic--monodromy equivalence are supporting lemmas, not parallel headline results.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, attack idea explicit
- [ ] 1 → 2 fully-proven: complete proof with unrestricted exponent theorem and both implications
- [ ] 2 → 3 formalized: one unconditional Lean theorem, exact build green, `#print axioms` clean
- [ ] 3 → 4 publication-ready: paper centered on this law, independent novelty audit at target 90/100

## Approach

1. Construct the concrete Taylor-regularized upper-half-plane Hurwitz carrier and its upper-end
   meromorphic-field element.
2. Prove unrestricted joint differential independence for augmented rationally independent
   exponent families.
3. Prove that adding integer offsets preserves augmented rational independence.
4. For a subset meeting every integer class at most once, apply unrestricted joint independence
   after changing representatives by integers.
5. If two selected exponents differ by an integer, orient the pair by the nonnegative difference
   and use the all-order Hurwitz differential ladder to exhibit a nonzero differential relation.
6. Package both directions as the exact independent-set theorem and derive the rank statement only
   as a corollary.

## Open core

The derivative-tail transfer from the proved convergence-chamber theorem to the concrete
continued upper-end elements is not yet formalized.  It must be proved axiom-free or replaced by a
direct continuation-compatible monodromy argument.  A proposition-valued bridge hypothesis is not
an acceptable endpoint.

## Lean evidence already established

- `HurwitzZetaContinuation.continuedHzeta_hasDerivAt`
- `HurwitzZetaContinuation.continuedHzeta_iteratedDeriv`
- `HurwitzJointLadder.continuedHzetaUpperEndMero`
- `HurwitzJointLadder.differentialJet_continuedHzetaUpperEndMero_eq`
- `HurwitzJointOrbit.linearIndependent_iff_monomialValue_monoScalar_injective`

These declarations are infrastructure only.  The main law remains conjectural until the open core
and exact two-sided matroid classification compile in Lean.

## Honest significance baseline

The earlier one-direction convergence-chamber theorem was graded 46/100.  Removing the half-plane
restriction alone is not enough to revise that score to 90.  The candidate earns reconsideration
only if the exact independent-set classification is proved as one law and survives a direct
parent-literature comparison.

## Log

- 2026-07-12 — created in stage 1 after replacing the collection-of-theorems framing by one exact
  differential-matroid law.
