# Finite-clock unitary reference-frame master-observability universality law

- **ID:** finite-clock-unitary-reference-frame-master-observability-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** theorem-generated closure of finite-clock Kadison-defect covariance and multi-clock
  master-observability
- **Statement:** Simultaneous unitary conjugation of every finite clock, the observable, and the
  state preserves total erased observability energy exactly, and its zero set is the transformed
  finite master-constraint kernel.

## Goal

Upgrade operator-level covariance of each finite-clock defect to a scalar, multi-clock,
master-constraint law under one unitary reference-frame switch.

## Gates

- [x] 0 → 1 in-progress: source-pure theorem-generated connector
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact-file Lean check passed warning-free
- [x] 3 → 4 novelty audit: completed; negative priority result

## Corpus inputs

- `finiteCyclicObservableTwirlKadisonDefect_twoSidedConjugation`
- `finiteClockFamilyObservabilityEnergy_eq_zero_iff_masterPhysical`
- `physicalState_finiteQuantumMasterConstraint_iff`
- `ContinuousLinearMap.inner_map_map_iff_adjoint_comp_self`

## Proof

**[PROVED HERE]** Let `V` be a bounded unitary frame map, with
`V†V = 1 = VV†`. Put

`Uᵢ' = V Uᵢ V†`, `X' = V X V†`, and `ψ' = Vψ`.

For each clock, covariance of the complete finite-clock Kadison defect gives

`D(Uᵢ',X') = V D(Uᵢ,X) V†`.

Since `V†V = 1`, applying this operator to `ψ'` gives
`D(Uᵢ',X')ψ' = V(D(Uᵢ,X)ψ)`. Unitarity preserves the inner product, so

`Re⟨ψ',D(Uᵢ',X')ψ'⟩ = Re⟨ψ,D(Uᵢ,X)ψ⟩`.

Summing over the finite clock family proves exact invariance of total erased energy.

For the master kernel, write `Cᵢ = Uᵢ-1`. The identity `VV†=1` gives
`Uᵢ'-1 = VCᵢV†`, while `X'ψ' = V(Xψ)`. Thus

`(Uᵢ'-1)(X'ψ') = V(Cᵢ(Xψ))`.

The left inverse `V†` makes `V` injective, so this vector vanishes exactly when
`Cᵢ(Xψ)=0`. The finite master-constraint theorem identifies each family of individual kernels
with its master kernel. The existing multi-clock observability theorem identifies original zero
energy with the original master kernel; energy invariance and kernel covariance therefore identify
transformed zero energy with the transformed master kernel. No computation is used. ∎

## Strict gain over corpus endpoints

The reference-frame theorem stops at conjugation of one operator-valued defect. The multi-clock
theorem identifies zero scalar energy with one fixed master constraint but says nothing about frame
changes. Their closure proves exact scalar-energy invariance and covariance of the complete
multi-clock physicality detector.

## Lean certificate

- Module:
  `GaloisForLFunctions.HTGeometry.FiniteClockUnitaryReferenceFrameMasterObservabilityUniversalityLaw`
- Main theorem:
  `finiteClockFamily_unitaryReferenceFrameMasterObservabilityUniversality`
- Exact-file command:
  `lake env lean GaloisForLFunctions/HTGeometry/FiniteClockUnitaryReferenceFrameMasterObservabilityUniversalityLaw.lean`
- Result: passed warning-free.
- Umbrella:
  `formal/GaloisForLFunctions/HTGeometry.lean`.

## Novelty audit

Performed only after the dependency-closed Lean proof passed.

Closest background located:

- Krumm, Höhn, and Müller, *Quantum reference frame transformations as symmetries and the
  paradox of the third particle*, arXiv:2011.01951, develops finite-Abelian quantum
  reference-frame transformations, constraints, and relational observables.
- de la Hamette and Galley, *Quantum reference frames for general symmetry groups*,
  arXiv:2004.14292, studies unitary changes of quantum reference frame for general symmetry
  groups.
- Thiemann, *(Quantum) reference frames, relational observables, gauge reduction and physical
  interpretation*, arXiv:2603.04072, treats quantum reference frames and physical constraint
  reduction at broad structural level.

No source located states the exact corpus closure: simultaneous unitary conjugation invariance of
the finite-family Kadison-defect scalar loss together with equality of its zero set and the
transformed finite quantum master-constraint kernel. This is a negative search result, not a
priority claim.

## Log

- 2026-07-23 — terminal-pair scan exposed the shared finite cyclic Kadison defect.
- 2026-07-23 — corpus research found separate operator covariance and master zero-set theorems,
  but no frame-invariant scalar or transformed-master closure.
- 2026-07-23 — dependency-closed proof completed before Lean source or literature search.
- 2026-07-23 — Lean source passed the required exact-file check warning-free and was wired into
  `GaloisForLFunctions/HTGeometry.lean`.
- 2026-07-23 — post-proof literature audit found general quantum-reference-frame covariance and
  constraint reduction, but not the exact finite-family Kadison-loss/master-kernel conjunction.
