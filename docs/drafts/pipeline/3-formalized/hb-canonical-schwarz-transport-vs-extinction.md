# HB canonical Schwarz transport versus source extinction

## Status

Paper proof and Lean formalization complete, 2026-08-28. Promoted to stage 3. Frontier map is read-only and remains untouched.

## Route

HB open core: source-forced FE--Schwarz branch covariance/unit left-response Ward.

## Corpus basis

- `HBXiPeierlsCarrier` is a direct sum of two finite-support packet axes.
- `hbXiPeierlsPlusSource` occupies only first axis; `hbXiPeierlsMinusSource` occupies only second.
- `hbXiPeierlsPlusLeftSource_eq` and `_MinusLeftSource_eq` reduce canonical left-coordinate packets exactly to those axes.
- Existing `HBXiPeierlsCanonicalLeftBranchCovariance` asks for literal equality of reflected plus-axis and minus-axis packets and is RH-equivalent.
- `deningerDivisorReflectGauge` supplies corpus-native anti-linear coefficient conjugation and divisor reindexing.
- Mandatory corpus search found no anti-linear channel-exchange operator on `HBXiPeierlsCarrier`, no proof that existing equality covariance is exactly simultaneous source extinction, and no comparison between genuine Schwarz transport and equality covariance.

## HC49 conjecture

The existing endpoint conflates two different notions:

1. Genuine Schwarz channel transport is anti-linear exchange `(f,g) ↦ (conj g, conj f)`. It should be involutive, preserve the symmetric carrier pairing up to conjugation, and map every canonical plus packet to its minus packet unconditionally.
2. Literal equality of a plus-axis packet with a minus-axis packet can occur only when both packets vanish. For nonzero seed, reflected canonical equality is therefore source extinction, exactly the critical-line receiver already encoded by helicity mixing.

If proved, ordinary Schwarz channel covariance is an unconditional symmetry and cannot select RH. HB's remaining producer must instead derive an additional FE reindexing/cocycle compatibility or a nonzero source/response Ward law; direct-sum equality is not a nontrivial branch exchange.

## Positive survivor

Expected exact classification of transport versus extinction, including the unique corpus-native anti-linear channel exchange and its pairing law. This refines HB open burden from vague “branch covariance” to a transport-compatible FE cocycle/source law that cannot be discharged by ordinary Schwarz symmetry alone.

## Bounded novelty audit

Search date: 2026-08-28. Primary-source search covered Peierls brackets and gauge-field covariance (`arXiv:hep-th/0301113`, `hep-th/0209147`), conserved QNM bilinear forms and reflection isometries (`arXiv:2210.15935`), AIME (`arXiv:2112.11168`), and recent covariant phase-space work (`arXiv:2510.19939`). Bounded search found no exact finite-support Xi-carrier anti-linear channel transport, source-extinction classification, or HB/RH endpoint distinction above. This is a bounded no-match result, not an exhaustive literature-wide novelty claim.

## Conjecture loop

- HC49-A: canonical anti-linear channel exchange exists and is involutive — proved in Lean.
- HC49-B: it maps canonical plus/regular-left packets to minus/complementary-left packets unconditionally — proved in Lean.
- HC49-C: it preserves carrier pairing up to complex conjugation — proved in Lean.
- HC49-D: literal cross-axis equality is equivalent to simultaneous extinction — proved in Lean.
- HC49-E: existing universal branch equality is global source extinction and remains exactly RH, while genuine transport covariance holds without RH — proved in Lean.
- HC49-F: off wall, genuine Schwarz transport exchanges two nonzero packets while literal equality fails — discovered during proof and proved in Lean.

## Proven survivor and route consequence

Ordinary Schwarz symmetry is now dependency-closed: coefficient conjugation plus regular/complementary channel exchange is an anti-linear involution, conjugates the carrier pairing, and transports every literal/canonical left packet exactly on every Xi fibre. It has no RH-selective content.

Existing “FE--Schwarz branch covariance” instead compares vectors on disjoint direct-sum axes without applying channel transport. Such equality is exactly simultaneous extinction. For nonzero seed its local zero locus is the critical line; global extinction is exactly RH. Thus HB cannot close by deriving ordinary Schwarz covariance. Remaining hard producer is a nontrivial FE reindexing/cocycle compatibility or nonzero source/response Ward law.

## Lean artifact

`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCanonicalSchwarzTransportExtinctionClassification`

All declarations are closed Lean proofs. No new axioms, `sorry`, `admit`, `opaque`, or `unsafe` declarations are introduced.

## Verification audit

- `lake env lean GaloisForLFunctions/RHTower/ThetaCuspHawkingBMCanonicalSchwarzTransportExtinctionClassification.lean`: passed.
- `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCanonicalSchwarzTransportExtinctionClassification`: passed, 11,917 jobs.
- `#print axioms` for all nineteen public theorems: only `propext`, `Classical.choice`, and `Quot.sound`.
- Module wired into `GaloisForLFunctions.RHTower` umbrella; no umbrella build was run.
- Formal lint contains no HC49 error. Global lint remains red only on unrelated unreachable owned modules.
