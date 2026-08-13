# Bottleneck 1 half-plane flip — COMPLETE AND GREEN (2026-08-13)

The node-side half-plane flip (evaluation nodes lower, Weyl poles upper) is fully executed,
compiled, and axiom-clean.  Full detail in the ledger sections "Bottleneck 1 sign repair —
decision taken and execution plan" and "— EXECUTED AND GREEN" in
`docs/drafts/pipeline/2-fully-proven/nad/_FORMALIZATION-LEDGER.md`.

## Verified end state
- `MaximalTranslationInputs.upperMap : ∀ z, z.im < 0 → 0 < (F.quotient z).im` (flipped field).
- **`HTGeometry.analyticNevCarrierFamily_lowerMap`** (new module
  `NevanlinnaEntryConjugation.lean`, wired at umbrella EOF) inhabits it unconditionally for the
  constructed family.  Proof: `nevBinf_conj`/`nevDinf_conj` (entries commute with conjugation —
  `Complex.conj_tsum` + `monicOrthoC_conj`/new `secondKindC_conj`) + `nevInf_quotient_im_neg`.
- `boundaryCarrierFace_maximalTranslationPhase_dense_residual` and
  `barycenter_mem_closure_maximalTranslationFullRankWitness_inter_face` compile axiom-clean under
  the flip; both HTGeometry + both RHTower SingularContinuous laws, Cofinal laws,
  PatternRelationWitnesses, FullRankWitnessInhabitation all green.
- Structure fields `finite_cauchy`/`infinity_cauchy` generalized to `z.im ≠ 0`;
  `integrable_cauchyKernel_(pow_)of_im_ne_zero` renamed accordingly (no external users of the old
  names).  Atlas renamed `noncriticalProjectiveLowerGood…` with `(z + shift i).im < 0` clauses;
  lower detectors `exists_placed_lower_packet_all_rows_nondegenerate` etc. in
  `PacketPlacementAvoidance.lean`.
- Parallel Herglotz/canonical/evenCanonical chains need NO flip (no Möbius pole there).
- `cayleyMoment_prefix_…_at_I` left at node `I` (no consumers today); needs the `−I` treatment via
  real-measure jet conjugation when a consumer materializes.

## What Bottleneck 1 still needs (per-family term of MaximalTranslationInputs)
1. `minimalExponentialType : HasMinimalExponentialType F.c` — reduced to
   `KernelMinimalExponentialType s` (M. Riesz).  Volterra/Gronwall CANNOT work (order two);
   route: zeros of B real with ∑1/|x_k| < ∞ + genus-zero Hadamard product.  Mathlib has NO
   Weierstrass/Hadamard factorization — must be built.
2. `phase_isGδ : IsGδ {ν | MaximalTranslationDifferentialFree ν}` — task #4.
3. leaf/label covariance upgrade for `carrierProjector_eq_of_leaf_label_covariance`.
Then the ten per-card assemblies (cards 5, 11, 17, 19, 21, 25, 34, 35, 36, 41 of the nad ledger).

## Build hygiene that worked
Detached builds survive Claude process restarts:
`nohup zsh -c 'lake build +T1 +T2 … > /tmp/log 2>&1; echo EXIT_$? >> /tmp/log' &`, then poll the
log with an until-loop.  Background Bash tasks die with the harness process — do not rely on them
for long builds.  Other agents build concurrently in this repo; never kill their lake/lean
processes; one own build at a time.
