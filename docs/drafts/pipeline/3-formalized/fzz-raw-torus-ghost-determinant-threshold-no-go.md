# Raw torus ghost determinant threshold no-go

- **ID:** FZZ-RAW-DET-NOGO
- **Stage:** 3-formalized
- **Type:** FALSIFIED + THEOREM (Lean)
- **Source:** FZZ-P frontier: fixed theta source → torus replica area → divisor passivity → RH
- **Statement:** Raw twisted genus-one theta-determinant norm, even after any continuous injective scalar postprocessing, cannot have a fixed sublevel set equal to the full zero-radial-holonomy wall.

## Goal

Kill direct determinant/ghost-norm completion of `FZZLinearReplicaAreaDivisorPassive` without assuming divisor data or RH.

## Gates

- [x] 0 → 1: source-pure; raw twisted determinant is canonical surviving non-character torus datum
- [x] 1 → 2: dependency-closed proof; `[PROVED HERE]`
- [x] 2 → 3: Lean module and targeted build PASS; standard axioms only
- [ ] 3 → 4: publication-ready

## Proof

Let `F(s₁,s₂)` be a continuous response with `F(s₁,s₂) ≤ c ↔ s₁=0`. Approaching `(0,s₂)` through nonzero `s₁` forces `c ≤ F(0,s₂)`, while selection gives the reverse inequality; hence `F(0,s₂)=c` for every `s₂`.

For the twisted determinant section
`D_q(λ)=‖θ_q(exp(2πiλ))‖`, `D_q(0)=0`, while `D_q(1/2)≠0`: the latter is `θ_q(-1)≠0`, proved from the exact q-Pochhammer shift and open-disc nonvanishing. Thus `φ∘D_q` is nonconstant on the wall for every continuous injective `φ`, contradicting wall saturation.

## No-go closure

- **Exact killing theorem:** `not_exists_fzzRawTorusGhostDeterminantNorm_postprocess_threshold_selector`.
- **Strongest positive survivor:** `continuous_exactWallSublevel_saturates`; any exact continuous passivity response must be tangentially constant on the critical wall.
- **New insight:** Pointwise determinant rescaling cannot close FZZ-P. Survivor must first erase compact-holonomy variation non-pointwise: logarithmic circle average, Quillen ratio/covariant derivative, or marked branch localization before Jacobian integration.
- **Status:** Paper proof closed. Lean direct check PASS; targeted build PASS. `#print axioms`: `propext`, `Classical.choice`, `Quot.sound` only. Global lint still reports unrelated pre-existing unreachable modules; new module is wired and absent from lint errors.

## Literature audit (through 2026-08)

- Hikida–Schomerus (arXiv:0805.3931) supplies twisted higher-genus first-order systems and Jacobian integration.
- Russo–Sciuto (arXiv:hep-th/0306129) supplies twisted determinant/theta products.
- Halder–Jafferis (arXiv:2402.00932v3, (3.29), (3.33)) defines the fractional-winding area operator and states its torus one-point function is expected; it does not evaluate it.
- No source found states this wall-saturation obstruction or its FZZ-P consequence. Novelty is the source-specific no-go and survivor classification; ingredients are classical.

## Lean certificate

- Module: `GaloisForLFunctions.RHTower.FZZCigarParityRawTorusGhostDeterminantNoGo`
- Umbrella: `GaloisForLFunctions.RHTower`
- Targeted build: PASS

## Log

- 2026-09-01 — paper proof, novelty audit, Lean formalization, and targeted audit complete
