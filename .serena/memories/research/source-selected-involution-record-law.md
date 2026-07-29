# Source-selected involution record / actuality conservation law

Date: 2026-07-29

## Hostile research chain

1. Candidate: use Albert cubic Hessian at primitive idempotent as rank-six 10→10 event.
2. Killed: on Peirce-zero `H_2(O)` corner, `1/2 D²N_p` is determinant spin-factor form of signature `(1,9)`, nondegenerate rank 10. It metricizes an outgoing corner but cannot generate 4/6/4 fracture.
3. Positive survivor: compatible pure pair gives commuting orthogonal complex structures; product involution `A` has `6+4` eigenspaces (Krasnov arXiv:2209.05088). Its spectral projectors canonically select both continuation and record:
   `C_A=(1+A)/2`, `R_A=(1-A)/2`.
4. Hostile priority collision: Kauffman arXiv:2108.13905 already proposes episodic actualization creates spacetime and spacetime records actualization history. Headline-level actualization-created spacetime is rediscovered.
5. Stronger surviving physical hunch: **ACTUALITY CONSERVATION LAW** — total physical distinguishability before an event equals continuable quantum distinguishability plus created causal distinguishability. Complete event lossless; local quantum continuation noninvertible; every elementary causal distinction arises from complementary transfer.

Public headline: **Nothing quantum disappears. What reality rules out becomes spacetime.**
Alternative: **The universe saves every quantum possibility it rejects as spacetime.**

## Exact Lean theorem

Module: `formal/GaloisForLFunctions/HTGeometry/EventInvolutionComplement.lean`

Proves unconditionally:
- `C+R=1`
- `CR=RC=0`
- continuation idempotent
- `ker C = range R`
- `ker R = range C`
- combined `(C,R)` map injective with record corestricted to range
- `coker C ≃ range R` canonically
- on `C^10`, `A²=1`, `trace A=2`: record rank 4, continuation rank 6, exact 4/6/4 kernel/range/coker.

Declarations:
- `involutionContinuationProjection`
- `involutionContinuation_add_record`
- `involutionContinuation_mul_record`
- `involutionRecord_mul_continuation`
- `involutionContinuation_isIdempotent`
- `involutionContinuation_ker_eq_record_range`
- `involutionRecord_ker_eq_continuation_range`
- `involutionRecordToRange`
- `involutionRecordToRange_surjective`
- `involutionContinuation_prod_record_injective`
- `involutionRecordToRange_ker_eq_continuation_range`
- `involutionContinuationCokernelEquivRecordRange`
- `traceTwoInvolution_record_four_continuation_six`
- `traceTwoInvolution_continuation_four_six_four`

Verification: direct lean clean; targeted final build `lake build GaloisForLFunctions.HTGeometry.EventInvolutionComplement` passed 2947/2947; formal lint passed; axiom audit only propext/Classical.choice/Quot.sound; no stale Lean/Lake.

Cards:
- failed route: `docs/drafts/pipeline/5-failed/albert-hessian-as-rank-six-event.md`
- paper proof: `docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/involution-selects-minimal-event-record.md`
- Stage3: `docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/involution-selects-minimal-event-record.md`
- active law appended at `docs/drafts/pipeline/1-in-progress/actuality-creates-future-law.md`, Tenth hostile descent / F9 / F10.

## Physical boundary

Spectral projectors route a fixed carrier and are reversible jointly; not objective actualization. Need:
1. compatible pure pair selected by event;
2. CP probability-preserving quantum instrument and Born probabilities;
3. record transported to distinct causal role, not relabelled;
4. Albert Hessian supplies 1+3 Lorentz metric/time orientation on outgoing record;
5. locally finite causal composition and continuum;
6. one connection yields gravity + exact GSM + mixed Higgs;
7. finite prediction.

Derived critical locus/self-dual obstruction representation is occupied mathematics (PTVV 1111.3209, Vezzosi 1109.5213, Behrend-Fantechi math/0512556). It is only a bridge: can represent quantum deformations vs causal obstructions, but exceptional source must derive physical complex.

Open core: `[OPEN CORE: EXCEPTIONAL SELF-DUAL EVENT COMPLEX]` — construct source event complex with local F9, outgoing four-record as causal obstruction, Albert Lorentz structure, event-relative gluing evading Higgs–tangent topology no-go, one curvature, quantum probabilities, and finite observable.