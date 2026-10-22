# N=2 supersymmetric projection-phase energy

- **ID:** `n2-supersymmetric-projection-phase-energy`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper + source-level Lean formalization)
- **Source:** [BRIDGE] supersymmetric quantum mechanics / projection geometry
- **Statement:** An off-diagonal corner `Q=(1-P)DP` of an idempotent is nilpotent.  For
  self-adjoint projection data, the phase rotation is the second Hermitian supercharge
  `i(Q-Q†)`; when `D` is tangent, `D=Q+Q†`, so the two concrete tangents anticommute and have the
  same square.

## Goal

Turn the existing semilocal phase-polarization construction into an exact energy identity and
remove the nilpotence premise when the reusable BRST/Hodge API is applied to projection normal
corners.  The relation is valuable only through these corpus effects; novelty is not claimed.

## Gates

- [x] 0 → 1 in-progress: exact source relation, paper proof, and direct consumers identified
- [ ] 1 → 2 fully-proven: independent paper/source review
- [ ] 2 → 3 formalized: targeted Lean check and axiom audit, only when explicitly permitted
- [ ] 3 → 4 publication-ready: standalone statement and verified Lean certificate

## Physics relation

The two equivalent presentations of bounded `N=2` supersymmetric quantum mechanics are a complex
nilpotent charge and two Hermitian charges:

```text
Q² = 0,
H = Q†Q + QQ†,
D = Q + Q†,
J = i(Q - Q†),
D² = J² = H,
DJ + JD = 0.
```

Fendley, Schoutens, and de Boer use nilpotent supersymmetry generators with
`H={Q⁺,Q⁻}` in lattice quantum systems:
<https://arxiv.org/abs/hep-th/0210161>.

Andrianov and Sokolov study the real and complex supercharge presentations of `N=2`
supersymmetric quantum mechanics:
<https://arxiv.org/abs/hep-th/0301062>.

An explicit current physics review gives both `{Q_i,Q_j}=2Hδ_ij` and the equivalent complex
relations `H={Q_c,Q_c†}`, `Q_c²=0`:
<https://link.springer.com/article/10.1007/s00601-025-01994-w>.

## Paper proof

`[PROVED HERE]` Let `P²=P` and `Q=(1-P)DP`.  Since `P(1-P)=0`,

```text
Q² = (1-P)DP(1-P)DP = 0.
```

If `P†=P` and `D†=D`, then `Q†=PD(1-P)`, so the existing projection phase rotation is exactly

```text
projectionPhaseRotation(P,D) = i(Q-Q†) = J.
```

Nilpotence passes to `Q†`.  Direct expansion gives

```text
(Q+Q†)² = Q†Q+QQ†,
[i(Q-Q†)]² = Q†Q+QQ†,
(Q+Q†)i(Q-Q†) + i(Q-Q†)(Q+Q†) = 0.
```

If additionally `DP+PD=D`, then `PDP=0`.  Expanding the two off-diagonal corners gives

```text
Q+Q† = (1-P)DP + PD(1-P) = DP+PD = D.
```

Therefore `projectionPhaseRotation(P,D)²=D²`, and the tangent anticommutes with its phase
rotation.

## Corpus application

### General HTGeometry

`HTGeometry/BRSTHodgeConstraint.lean` now contains:

- `offDiagonalProjectionCorner_sq_eq_zero`;
- `brstHodgeCoDiracOperator`;
- `brstHodgeCoDiracOperator_isSelfAdjoint`;
- `brstHodgeCoDiracOperator_sq_eq_hamiltonian`;
- `norm_brstHodgeCoDiracOperator_apply_sq_eq_norm_diracOperator_apply_sq`;
- `brstHodgeDiracOperator_anticommutes_coDiracOperator`.

The first theorem applies to arbitrary bounded operators over any `RCLike` scalar field and any
idempotent.  It makes projection corners automatic inputs to the existing BRST/Hodge Hamiltonian,
commutation, Green-operator, Ward-value, and constraint-ideal surfaces.  This is general
hypertranscendental infrastructure, not zeta-specific code.

### RHTower

`RHTower/SemilocalProjectionPhasePolarization.lean` now contains:

- `projectionNormalCorner_sq_eq_zero`;
- `projectionPhaseRotation_eq_brstHodgeCoDiracOperator`;
- `projectionPhaseRotation_sq_eq_brstHodgeHamiltonian`;
- `brstHodgeDiracOperator_projectionNormalCorner_eq_tangent`;
- `projectionPhaseRotation_sq_eq_tangent_sq`;
- `norm_projectionPhaseRotation_apply_sq_eq_norm_tangent_apply_sq`;
- `projectionTangent_anticommutes_phaseRotation`.

This directly strengthens the existing phase-polarized mixed-curvature route: the orientation
quarter-turn preserves the exact quadratic operator energy of every self-adjoint projection
tangent, both as an operator-square identity and as the statewise value relation
`||J psi||²=||D psi||²`.  The normal corner's nilpotence is discharged by idempotence instead of
being left as a new source hypothesis.

## Limits

The relation does not construct the source-specific semilocal projection family, prove compactness
of the base-compressed mixed derivative, or establish an RH-equivalent implication.  It strengthens
the algebra available once such a tangent exists and prevents future BRST consumers from asking for
a redundant nilpotence premise.

## Verification boundary

All Lean declarations are source-reviewed only.  By explicit instruction, no Lean process, build,
lint, axiom audit, numerical script, experiment, or other computation was run.

## Log

- 2026-07-15 — exact physics relation identified, paper proof written, generic HTGeometry and
  concrete RHTower theorem surfaces added source-only; no build or computation run.
