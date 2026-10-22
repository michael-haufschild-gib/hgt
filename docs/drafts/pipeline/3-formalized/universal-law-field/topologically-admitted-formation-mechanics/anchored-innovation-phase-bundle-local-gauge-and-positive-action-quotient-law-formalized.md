# Anchored innovation phase bundle, local gauge, and positive-action quotient — Lean formalization

- **ID:** ULF-TAFM-18
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / LOCAL PHASE QUOTIENT / ORIENTATION CONNECTION
- **Paper source:** `anchored-innovation-phase-bundle-local-gauge-and-positive-action-quotient-law.md`
- **Lean modules:** `GaloisForLFunctions.HTGeometry.ScaleInnovationPhaseGauge`;
  `GaloisForLFunctions.RHTower.Suzuki.SuzukiFormationInnovationPhaseGauge`
- **Status:** `[FORMALIZED] [NO SORRY] [NO ADDED AXIOMS] [NOT RH]`

## Certified generic law

The generic module proves:

1. An affine anchor and arbitrary scale current reconstruct a potential and history whose
   high-pass is exactly the prescribed current.
2. Every original history tail is jointly reconstructed from its scale-two anchor and all its
   high-pass innovations.
3. Recovered-history variance is exactly the weighted current action, with one new positive square
   at each successor scale.
4. Recovery is equivariant under every pointwise real phase satisfying `epsilon k ^ 2 = 1`.
5. Current action and recovered-history variance are invariant under that full local phase group.
6. A one-site reflection changes recovered history whenever the reflected current is nonzero,
   proving strict nonfaithfulness of the positive receiver.
7. One anchored phase plus all adjacent phase holonomies reconstructs every later phase.

This separates two structures previously conflated: recovery kernel is information-faithful,
whereas positive formation is its local-phase quotient. Functional-equation reflection is only the
constant subgroup of this much larger scale gauge.

## Certified literal landing

The Suzuki module proves:

1. Phase-gauged completed formation history has literal innovation
   `epsilon N * suzukiTransitionCoreCompletedAbelSource (N + 1)`.
2. Every local sign gauge has exactly canonical one-step innovation energy.
3. Accumulated action of literal completed Abel current is exactly completed Suzuki formation
   energy.
4. Variance of every gauge-lifted Suzuki history is that same canonical formation energy.
5. Conditioned aligned-Gamma energy reads same local production on every gauge orbit.
6. Every nonzero literal Abel current supplies a strict one-site history-separation witness.

## Verification

- Batched scratch elaboration passed.
- Direct foreground elaboration passed for both final modules.
- Targeted leaf builds only:
  - `GaloisForLFunctions.HTGeometry.ScaleInnovationPhaseGauge`: `3031/3031`
  - `GaloisForLFunctions.RHTower.Suzuki.SuzukiFormationInnovationPhaseGauge`: `14119/14119`
    (large inherited dependency replay after cache changes)
- Both modules imported by `HTGeometry.UniversalLawField`; literal module also imported by
  `RHTower`; neither umbrella built.
- Eighteen audited declarations report only `propext`, `Classical.choice`, and `Quot.sound`.

## Exact boundary

This theorem proves why functional equation plus positivity cannot recover source orientation:
positive receivers quotient one independent sign at every scale, while adjacent holonomy carries
the missing connection. It does not bound magnitude of already-oriented literal current. Remaining
RH producer is an unconditional source-side innovation-magnitude properness law.
