# Universal hybrid-blind / Xi-zero-Hurwitz-faithful observable nonuniformity law

- **ID:** universal-hybrid-blind-xi-zero-hurwitz-faithful-observable-nonuniformity
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** Cross-corpus closure of universal chamber blindness and Xi-zero Hurwitz observable
  factorization
- **Statement:** One finite differential observable-field functor is exactly blind on universal
  orientation/prime chambers but order-reflecting, equality-reflecting, and tensor-factorizing on
  injective Xi-zero Hurwitz jet nets.

## Goal

Classify two opposite source-dependent behaviors of the same observable construction.  Retain the
hybrid chamber defect, not only field equality, and retain the full Xi-zero order/factorization
certificate, not only injectivity.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, exact `lake env lean` green, `check_axioms.sh` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Corpus inputs

- `universalHybridChamber_sameObservableField_Herglotz_iff_defect_zero`
- `xiZeroHurwitz_factorizingFaithfulObservableNet`

Both act on `differentialFamilyObservableField (RatFunc ℂ)` inside the same
`upperEndMeroField`.

## Proof

`[PROVED HERE]` For arbitrary orientation index `k`, prime chamber `J`, and finite resolution,
the hybrid chamber theorem identifies the oriented and prime-residue observable fields.  Its
nonnegative defect is exactly `k` plus prime-chamber Hamming distance, and vanishes exactly when
both associated Herglotz channels are positive.

For any finite injective Xi-divisor labeling, the Hurwitz net theorem says field inclusion is
equivalent to coordinatewise resolution inclusion and field equality is equivalent to equality
of the entire resolution vector.  Disjoint supports additionally give linear disjointness,
coefficient-field intersection, and a domain tensor product.  Combining the two conclusions under
the shared instances proves source-class nonuniformity of the observable functor.

No numerical computation is used.

## Novelty protocol

No literature search before exact Lean proof.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.UniversalHybridBlindXiZeroHurwitzFaithfulObservableNonuniformityLaw`
- Main theorem:
  `RHTower.universalHybridBlind_xiZeroHurwitzFaithfulObservableNonuniformity`
- Exact source check:
  `lake env lean GaloisForLFunctions/RHTower/UniversalHybridBlindXiZeroHurwitzFaithfulObservableNonuniformityLaw.lean`
  (exit 0, no output).
- Imported by `GaloisForLFunctions/RHTower.lean`.
- Axiom audit and module build deferred to required final audit; no intermediate `lake build`.

## Post-proof literature audit

- **Status:** `[LEAN PROVED — LITERATURE AUDITED]`
- Montanari--Lamoline--Bereza--Gonçalves show that identifiability depends on sensors,
  experimental conditions, and model structure, and formulate algebraic observability tests for
  differential-algebraic systems
  ([arXiv:2405.13818](https://arxiv.org/abs/2405.13818)).
- [DLMF §25.11](https://dlmf.nist.gov/25.11) records the classical Hurwitz-zeta function,
  continuation, and derivative formulas.
- General differential-field literature treats linear disjointness separately; see
  [*Deciding Linear Disjointness of Finitely Generated Differential Fields*](https://doi.org/10.1515/GMJ.2005.443).
- No audited source states this exact same-functor contrast: finite differential observable fields
  are simultaneously defect-certified blind on universal orientation/prime chambers and
  order/equality-reflecting with tensor-domain factorization on Xi-zero-labelled Hurwitz jet nets.
  This no-match conclusion is an inference from targeted searches, not an exhaustive enumeration
  of all publications.

## Log

- 2026-07-23 — fresh cross-folder terminal-symbol pass exposed shared observable-field functor;
  source types and instances verified before synthesis.
- 2026-07-23 — exact Lean source check passed; post-proof literature audit found no exact prior law.
