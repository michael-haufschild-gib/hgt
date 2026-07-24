# Squarefree--Möbius double-normal-cone duality universality law

- **ID:** squarefree-mobius-double-normal-cone-duality-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** theorem-generated closure of
  `tendsto_squarefreeMacroscopicHeightOverlap`,
  `mobiusCompletedNormalConeTransfer_one`, and
  `tendsto_mobiusCompletedNormalConeTransfer_one`
- **Statement:** At every fixed nonzero height on the Euler boundary, the squarefree
  macroscopic boundary section and the Möbius exceptional normal-cone section are mutual
  inverses up to the universal scalar `ζ(2)`. Their product is exactly `ζ(2)`, independently
  of aperture and height.

## Goal

Join two independently constructed Euler-pole blow-ups through their shared squarefree partition
section and expose the invariant pairing hidden by the separate normalizations.

## Gates

- [x] 0 → 1 in-progress: source-pure theorem-generated connector
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact-file Lean check passed; final global axiom audit pending
- [x] 3 → 4 publication-ready: post-proof collision audit found no exact literature match

## Corpus inputs

- `squarefreePartition`
- `tendsto_squarefreeMacroscopicHeightOverlap`
- `mobiusCompletedNormalConeTransfer_one`
- `tendsto_mobiusCompletedNormalConeTransfer_one`
- `riemannZeta_ne_zero_of_one_le_re`
- `riemannZeta_ne_zero_of_one_lt_re`

## Proof

**[PROVED HERE]** Fix real aperture `δ ≥ 0` and nonzero physical height `γ`, and set
`t = 1 + iγ`. The squarefree macroscopic-height theorem gives

`squarefreeMacroscopicHeightOverlap(σ, δ, γ) → ζ(2) squarefreePartition(t)`

as `σ → 1+`.

Because `Re(t) = 1` and `t ≠ 1`, the zero-free closed Euler half-plane gives `ζ(t) ≠ 0`.
Also `Re(2t) = 2 > 1`, so `ζ(2t) ≠ 0`. Hence
`squarefreePartition(t) = ζ(t) / ζ(2t)` is nonzero. The Möbius normal-cone theorem therefore
gives

`mobiusCompletedNormalConeTransfer(squarefreePartition, b, t)
  → squarefreePartition(t)⁻¹`

as `b → 1`, and its exceptional-value theorem identifies the value at `b = 1` with this same
inverse section. Multiplication cancels the shared nonzero squarefree section:

`(ζ(2) squarefreePartition(t)) ·
  mobiusCompletedNormalConeTransfer(squarefreePartition, 1, t) = ζ(2)`.

The right side contains neither `δ` nor `γ`. No computation is used. ∎

## Strict gain over corpus endpoints

The squarefree height blow-up produced a covariant fixed-height boundary section but did not
compare it with a Möbius deformation. The Möbius normal cone produced a reciprocal exceptional
section for arbitrary source functions but did not identify a boundary observable pairing it
with the squarefree blow-up. Their theorem-generated closure exposes an exact, parameter-free
double-normal-cone pairing invariant.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.SquarefreeMobiusDoubleNormalConeDualityUniversalityLaw`
- Main theorem:
  `squarefreeMobius_completeDoubleNormalConeDualityUniversality`
- Supporting theorem:
  `squarefreePartition_one_add_mul_I_ne_zero`
- Exact-file command:
  `lake env lean GaloisForLFunctions/RHTower/SquarefreeMobiusDoubleNormalConeDualityUniversalityLaw.lean`
  passed warning-free on 2026-07-23.
- Umbrella:
  imported by `formal/GaloisForLFunctions/RHTower.lean`.

## Novelty audit

No literature search occurred before dependency-closed paper and Lean proofs. Post-proof searches
for squarefree zeta quotients, Möbius reciprocal Dirichlet series, Euler-pole normal cones, and
fixed-height boundary pairings found no exact collision. Closest primary sources:

- M. Kobayashi, *Möbius functions of higher rank and Dirichlet series*,
  <https://arxiv.org/abs/2108.01822>, studies higher-rank Möbius functions and zeta-controlled
  Dirichlet series for `r`-free integers, not paired Euler-pole blow-ups.
- S. Yakubovich, *New summation and transformation formulas of the Poisson, Müntz, Möbius and
  Voronoi type*, <https://arxiv.org/abs/1410.7934>, derives Mellin and Möbius transformation
  formulas involving zeta-product ratios, not the squarefree macroscopic/Möbius exceptional
  normal-cone pairing.
- D. Ni, *On the deformation to the normal cone in Arakelov geometry*,
  <https://arxiv.org/abs/2206.07954>, develops arithmetic deformation-to-normal-cone invariants
  in Arakelov geometry, not an Euler-pole source blow-up or the constant `ζ(2)` pairing.

## Log

- 2026-07-23 — fresh terminal-cluster scan exposed shared squarefree boundary section.
- 2026-07-23 — dependency-closed paper proof completed before literature search or Lean source.
- 2026-07-23 — exact Lean proof passed warning-free and module wired into RHTower umbrella.
- 2026-07-23 — post-proof collision audit found no exact literature match.
