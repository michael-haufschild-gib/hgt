# HB vacuum real-differentiable nonlinear detector scalarization no-go

- **ID:** HB-HC95-REAL-LINEAR-SCALARIZATION
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / route-class no-go
- **Statement:** Faithful real-linear—including conjugate-linear—vacuum response can scalarize the actual horizon/boundary radiative FE cocycle at `q` iff `Re(q)=1/2`; copywise global existence is iff RH.

## Killed RH chain

`nonlinear detector → faithful real/conjugate-linear vacuum response → one scalar FE gain → universal Ward cancellation → RH`.

Exact chain proved:
`real-linear intertwiner` → each physical gain is `c` or `conj(c)` → equal gain norms → equal reflected BM transfer norms → `Re(q)=1/2` → fixed-pairing endpoint; universally, RH. RH supplies identity detector.

## Corpus and novelty audit

- HC92: actual boundary/horizon quotient is `T(Rq)/conj(T(q))`; equal gains iff criticality.
- BM transfer corpus: exact Gamma transfer has strictly increasing horizontal squared modulus at all unverified heights; low heights are already zero-verified.
- HC93/HC94 cover complex-linear compression and complex-linear vacuum first variation only.
- Corpus searches found no real-linear intertwiner classification or reflected BM transfer-modulus collision theorem.
- Birmingham--Mokhtari exact hypergeometric/QNM literature contains transfer data, not Xi-cocycle real-linear scalarization or this RH rigidity law.

## Paper proof `[PROVED HERE]`

For injective real-linear `L` with `L Cq=M_c L`, multiplication `M_c` obeys
`M_c²-2 Re(c)M_c+|c|²I=0`. Real-linearity and injectivity pull this quadratic back to `Cq`; hence each diagonal gain is a root of `(X-c)(X-conj(c))` and their squared norms agree.

HC92 and nonvanishing reduce equal gain norms to `|T(Rq)|²=|T(q)|²`. At high ordinates existing strict horizontal BM-transfer monotonicity forces `Re(q)=1/2`; low ordinates are already verified. Converse uses equal gains and identity response. Exact nonlinear scalarization passes to vacuum limit, so the result applies to arbitrary nonlinear detectors with real-linear first variation.

## No-go closure

- **Killing mechanism:** real characteristic quadratic plus exact BM transfer-modulus rigidity.
- **Strongest positive survivor:** `|T(Rq)|²=|T(q)|² ↔ Re(q)=1/2`; off line every exact scalarizing real-linear first variation is non-injective.
- **Remaining architecture:** vacuum-singular response or first-order loss of physical readout information.

## Lean certificate

- Module: `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMRadiativeSourceFEVacuumRealDifferentiableNonlinearDetectorNoGo.lean`
- Final theorem: `RHTower.d4HBVacuumRealDifferentiableNonlinearDetectorScalarizationRouteKilled`
- Transfer survivor: `RHTower.d4BMXiSecondHarmonicBoundaryTransfer_normSq_reflect_eq_iff_re_eq_half`
- Global classification: `RHTower.hbXiRadiativeGlobalVacuumRealDifferentiableFaithfulDetectorScalarization_iff_rh`
- Direct `lake env lean` PASS; targeted build `13100/13100` PASS.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- Wired into `GaloisForLFunctions/RHTower.lean`; no umbrella build run.
- Formal lint finds no forbidden declaration in new module; unrelated shared-worktree unreachable-module errors remain.

## Gates

- [x] 0 → 1 exact corpus-derived conjecture and RH chain
- [x] 1 → 2 dependency-closed paper proof, literature check, hostile audit
- [x] 2 → 3 direct Lean, targeted build, axiom audit, umbrella wire
- [ ] 3 → 4 publication-ready: not claimed
