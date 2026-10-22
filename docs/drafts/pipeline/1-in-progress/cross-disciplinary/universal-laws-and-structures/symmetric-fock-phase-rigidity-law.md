# Symmetric-Fock phase-rigidity law

- **ID:** symmetric-fock-phase-rigidity-law
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper proved, hostile-audited, Lean-direct-checked; no priority claim)
- **Source:** Bottom-up closure of the sharp transverse Fano square law and the independently
  proved lowering-shadow equality classification
- **Statement:** Equality in the rank-sensitive graded Fock Fano bound holds exactly when every
  positive adjacent level is closed under both lowering and creation and every transverse channel
  is at its unique balancing phase. Strict gap is exactly one failed level closure or one
  off-balance channel.

## Gates

- [x] 0 → 1 in-progress: theorem-first closure and exact hypotheses
- [x] Complete paper proof with no open dependency
- [x] Lean source passes `lake env lean <file>`
- [x] Direct tree-file Lean check
- [x] Hostile literature noncollision audit
- [ ] Final module build, lint, and axiom audit

## Lean inputs

1. `transverseChannelFanoMargin_square_card` writes the transverse margin as its sharp baseline
   plus a finite sum of phase squares.
2. `gradedFockLoweringCharge_lower_bound` gives the independent nonnegative lowering-charge gap.
3. `gradedFockLoweringCharge_eq_iff_levelwise_creator_closed` classifies equality in that gap by
   two-sided lowering/creation closure at every positive level.
4. `gradedFockLoweringCharge_lt_iff_exists_level_defect` classifies its strict complement by a
   concrete level defect.

## Paper proof

Expand the right side of the rank-sensitive Fano bound by the exact channel-square identity. The
difference from the left side is the sum of two nonnegative quantities: the global graded
lowering-charge gap and `(card I + 1)` times the sum of channel phase squares. Equality holds iff
both vanish. The first vanishes exactly under levelwise lowering/creation closure; the second
vanishes exactly when `(M-1)p_i=(M-2)/2` for every channel. Since the same decomposition is a sum
of nonnegative terms, strictness holds exactly when the charge gap is strict or some phase square
is nonzero. The existing strict charge classification turns the first alternative into one
incomplete lowering shadow or one creation escape. `[PROVED HERE]`

## Formalization target

- Module: `formal/GaloisForLFunctions/HilbertMetric/SymmetricFockPhaseRigidity.lean`
- Equality capstone: `gradedFockTransverse_rank_bound_eq_iff_phase_rigidity`
- Strict capstone: `gradedFockTransverse_rank_bound_lt_iff_phase_defect`

## Hostile literature audit

Searches covered exact and neighboring formulations: `"graded Fock" "Fano" inequality equality`,
`"symmetric Fock lowering" shadow`, `"rank-sensitive Fano bound"`, symmetric-tensor contraction
dimension inequalities, annihilation-invariant graded subspaces, and Fano-factor rank inequalities.
The closest primary mathematical source found, Arias--Popescu's
[Factorization and Reflexivity on Fock spaces](https://arxiv.org/abs/math/9404209), classifies
left-creation-invariant subspaces of full noncommutative Fock space but contains neither this
finite symmetric-Fock charge inequality nor the channel-square Fano equality law. A terminology
collision, Aharony et al.'s
[Breakdown of `phase rigidity' and variations of the Fano effect](https://arxiv.org/abs/cond-mat/0512384),
concerns Aharonov--Bohm conductance and is mathematically unrelated. No source found the combined
equality/strict classification or its exact decomposition. This is evidence of noncollision, not
a priority claim.

## Log

- 2026-07-21 — Found during complete HilbertMetric non-PSD endpoint rescan. The phase module used
  the sharp charge inequality, while the separate rigidity module classified its equality case;
  no common consumer or prior card was present.
- 2026-07-22 — Formalized equality and strict-complement classifications. Exact direct check
  `lake env lean GaloisForLFunctions/HilbertMetric/SymmetricFockPhaseRigidity.lean` passed.
- 2026-07-22 — Hostile literature audit passed: exact searches were empty; nearest creation-
  invariant-subspace and Fano/phase-rigidity literature proved unrelated statements.
