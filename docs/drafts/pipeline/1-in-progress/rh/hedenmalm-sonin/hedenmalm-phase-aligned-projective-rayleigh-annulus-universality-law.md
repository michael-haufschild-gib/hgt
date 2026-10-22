# Hedenmalm phase-aligned projective Rayleigh-annulus universality law

- **ID:** hedenmalm-phase-aligned-projective-rayleigh-annulus-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** theorem-generated closure of concrete Hedenmalm source–tangent independence,
  projective phase alignment, and Rayleigh-gap coercivity
- **Statement:** Under the Hedenmalm Rayleigh hypotheses, a unit phase aligns tangent and source
  at strictly positive squared distance bounded above by twice the Rayleigh excess divided by the
  gap.

## Goal

Turn the existing projective-energy estimate into an actual phase-aligned metric statement for the
concrete theta-cusp source and aperture tangent, retaining strict separation.

## Gates

- [x] 0 → 1 in-progress: source-pure theorem-generated connector
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact-file Lean check passed warning-free
- [x] 3 → 4 novelty audit: no exact statement found in searched literature

## Corpus inputs

- `thetaCuspRightLine_projectiveRayleighGap_strict`
- `thetaCuspRightLine_unit_source_tangent_linearIndependent`
- `exists_unitScalar_norm_sub_sq_le_two_projectiveQuantumTangentEnergy`

## Proof

**[PROVED HERE]** Let `v` and `g` be the unit-normalized Hedenmalm source and aperture tangent.
The concrete source theorem gives linear independence of `(v,g)`. The Rayleigh-gap theorem gives

`0 < D(v,g) ≤ (R_T(g)-ε)/gap`

for projective Gram energy `D`, and consequently `ε < R_T(g)`.

Generic phase alignment supplies `c : ℂ` with `|c|=1` and

`‖g-cv‖² ≤ 2D(v,g)`.

Multiplying the energy bound by two yields

`‖g-cv‖² ≤ 2(R_T(g)-ε)/gap`.

If `‖g-cv‖²=0`, then `g=cv`, contradicting linear independence of `(v,g)`. Therefore the selected
distance is strictly positive. The phase-aligned tangent lies in the punctured metric annulus

`0 < ‖g-cv‖² ≤ 2(R_T(g)-ε)/gap`,

while its Rayleigh quotient remains strictly above `ε`. No computation is used. ∎

## Strict gain over corpus endpoints

The generic alignment theorem has no Hedenmalm specialization or strict lower bound. The concrete
Hedenmalm Rayleigh law bounds only projective energy and Rayleigh quotient, not an actual
phase-aligned vector distance. Their closure yields a new metric spectral statement.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmPhaseAlignedProjectiveRayleighAnnulusUniversalityLaw`
- Main theorem:
  `thetaCuspRightLine_phaseAlignedProjectiveRayleighAnnulusUniversality`
- Exact-file command:
  `lake env lean GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmPhaseAlignedProjectiveRayleighAnnulusUniversalityLaw.lean`
- Result: passed warning-free on 2026-07-23.
- Umbrella:
  `formal/GaloisForLFunctions/RHTower.lean`.

## Novelty audit

Performed only after exact Lean proof passed. Searches combining Hedenmalm theta-cusp sources,
aperture tangents, unit-phase alignment, projective Hilbert distance, and Rayleigh-gap bounds found
general Rayleigh-quotient perturbation and subspace-angle literature, but no theorem for this
concrete source–tangent pair or its punctured phase-aligned annulus.

Closest background:

- Zhu–Argentati–Knyazev, *Bounds for the Rayleigh quotient and the spectrum of self-adjoint
  operators*, arXiv:1207.3240.
- Knyazev–Jujunashvili–Argentati, *Angles Between Infinite Dimensional Subspaces with
  Applications to the Rayleigh–Ritz and Alternating Projectors Methods*, arXiv:0705.1023.

Those works concern general Rayleigh perturbation or subspace angles, not Hedenmalm’s theta-cusp
aperture tangent, the proved projective-energy connector, or strict positive distance modulo phase.
This is a negative search result, not a priority claim.

## Log

- 2026-07-23 — terminal cross-surface scan exposed shared projective Gram energy.
- 2026-07-23 — exact corpus search found generic phase alignment and concrete Hedenmalm
  Rayleigh-energy control, but no concrete strict metric closure.
- 2026-07-23 — dependency-closed proof completed before Lean source or literature search.
- 2026-07-23 — exact-file Lean check passed warning-free; module wired into RHTower umbrella.
- 2026-07-23 — post-proof novelty search found no exact literature collision.
