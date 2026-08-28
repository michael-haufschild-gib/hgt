# HB universal skew-propagator classification

- **ID:** HB-USPC
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` · HB `LAND ORIENT DYN`
- **Statement:** Every complex-linear propagator skew for universal coordinate pairing is uniquely a target-scaled symplectic rotation; existence of any fixed skew propagator realizing all unit-seed BM incidences is equivalent to RH.

## Goal

Remove concern that scalar propagator family used by universal-incidence no-go omitted other two-dimensional skew Peierls propagators. Upgrade fixed-propagator RH receiver to arbitrary fixed skew endomorphisms.

## Gates

- [x] 0 → 1 in-progress: corpus search found scalar family but no arbitrary skew classification; coordinate proof identified
- [x] 1 → 2 fully-proven: dependency-closed coordinate classification and global reduction below
- [x] 2 → 3 formalized: two Lean modules wired into umbrella; direct checks, targeted builds, and axiom audit pass
- [ ] 3 → 4 publication-ready: standalone exposition

## Theorems

1. If `Delta : ℂ² →ₗ[ℂ] ℂ²` is skew for the universal coordinate source pairing, then uniquely
   `Delta = [[0,-T],[T,0]]`, with `T = (Delta (1,0)).2`.
2. For every overtone `n`, existence of any fixed skew `Delta` realizing every unit-seed BM
   incidence is equivalent to RH.
3. No nonzero fixed skew `Delta` realizes every such incidence.

## Proof `[PROVED HERE]`

Evaluate skewness on coordinate basis pairs. Diagonal evaluations kill two diagonal matrix coefficients; mixed evaluation identifies off-diagonal coefficients with opposite signs. Linearity reconstructs entire endomorphism as unique scalar symplectic rotation. Reduce global incidence to HC9 scalar theorem.

Explicitly, writing columns of `Delta` as `(a,c)` and `(b,d)`, skewness at `(e₁,e₁)` and
`(e₂,e₂)` gives `2a=0` and `2d=0`; skewness at `(e₁,e₂)` gives `b=-c`. Hence
`Delta(x,y)=(-cy,cx)`. Evaluation at `e₁` proves parameter uniqueness. Replacing an arbitrary
fixed skew propagator by this uniquely classified scalar rotation reduces all-copy incidence to
`exists_hbUniversalPeierls_fixedPropagator_unit_BM_incidence_iff_rh`. Its unconditional Hardy
anchor also forces `c=0`, excluding nonzero fixed skew propagators.

## Lean certificate

- Modules:
  - `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMUniversalSkewPropagatorClassification`
  - `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMUniversalSkewPropagatorGlobalRigidity`
- Theorems:
  - `hbUniversalPeierls_skewPropagator_eq_targetScaledRotation`
  - `hbUniversalPeierls_skewPropagator_existsUnique_targetScaledRotation`
  - `exists_hbUniversalPeierls_fixedSkewPropagator_unit_BM_incidence_iff_rh`
  - `not_exists_hbUniversalPeierls_nonzero_fixedSkewPropagator_unit_BM_incidence`
- Axioms: only Mathlib foundations `propext`, `Classical.choice`, `Quot.sound`.
- No `sorry`, `admit`, added `axiom`, `opaque`, or `unsafe` declaration.
- Both target-specific `lake build` audits passed. Repository-wide formal lint reports only
  pre-existing unreachable modules; neither new module is among them.

## Novelty audit (2026-08-28)

Mandatory corpus search found universal scalar realization and target constancy, but no
classification of arbitrary skew endomorphisms or arbitrary-skew RH receiver. Literature search
found general canonical classification of systems of forms and general covariant Peierls theory,
but no exact universal-carrier classification combined with BM incidence and RH equivalence.
Relevant sources: Sergeichuk, [Canonical matrices for linear matrix problems](https://arxiv.org/abs/0801.0823); Khavkine, [Characteristics, conal geometry and causality in locally covariant field theory](https://arxiv.org/abs/1211.1914).

## Log

- 2026-08-28 — created after mandatory corpus search found no arbitrary-propagator classification.
- 2026-08-28 — coordinate paper proof and Lean classification closed.
- 2026-08-28 — arbitrary-skew global incidence reduced to scalar HC9; RH equivalence and nonzero no-go formalized.
- 2026-08-28 — dependency-isolated modules passed direct checks, targeted builds, umbrella wiring, and axiom audit.
