# Suzuki causal-depth Gamma-Schur trace-class completion

- **ID:** SUZUKI-GAMMA-SCHUR-TRACE-CLASS
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `RiemannHypothesisSOTA2026.lean`, open core `SUZUKI-FE-REFLECTED-WALL-WARD-ASSEMBLY`
- **Statement:** Cubic-aperture weighting makes the complete prime-depth mean-and-conductor-projected Gamma Schur kernel a positive trace-class Gram operator with aperture-uniform trace ceiling.

## Goal

Proof chain: full Gamma-Schur trace-class/bounded holonomy debt → one premise of rectangular Suzuki Ward lower bound → shared receiver extinction → RH.

## Gates

- [x] 0 → 1: corpus-defined kernel, exact source weights, Mercer factorization
- [x] 1 → 2: dependency-closed proof; `[PROVED HERE]`
- [x] 2 → 3: Lean module, direct check, axiom audit, targeted build, umbrella wire
- [ ] 3 → 4: publication audit

## Proof `[PROVED HERE]`

For source index `i=(p,e)`, put `νᵢ=log(p^(e+1))/2` and let `wᵢ` be actual cubic-aperture boundary amplitude. Corpus identities give `νᵢ>0`, `wᵢ²=normSq(boundaryAtomᵢ)`, and `∑ᵢwᵢ²<∞` with aperture-independent ceiling. Projected Gamma residual has Mercer expansion `R(t,u)=f₁(t)f₁(u)+∑ₖfₖ₊₃(t)fₖ₊₃(u)` and diagonal `0<R(t,t)≤1`. Thus `A(k,i)=wᵢf_{d(k)}(νᵢ)`, `d(0)=1`, `d(k+1)=k+3`, satisfies `‖A‖²_HS=∑ᵢwᵢ²R(νᵢ,νᵢ)≤∑ᵢwᵢ²`. Hence `A†A` is positive trace class, its source block is exactly `wᵢR(νᵢ,νⱼ)wⱼ`, and its trace has same uniform ceiling.

## Lean certificate

- Module: `GaloisForLFunctions.RHTower.Suzuki.SuzukiCausalDepthGammaSchurTraceClassCompletion`
- Premise-free main theorems: `suzukiCanonicalCausalDepthGammaEnergyOperator_isTraceClass`, `suzukiCanonicalCausalDepthGammaEnergyOperator_sourceBlock`, `suzukiCanonicalCausalDepthGammaEnergyOperator_re_opTrace_le`
- `lake build GaloisForLFunctions.RHTower.Suzuki.SuzukiCausalDepthGammaSchurTraceClassCompletion`: PASS
- Axioms: `propext`, `Classical.choice`, `Quot.sound`
- Umbrella: `GaloisForLFunctions.RHTower`

## Novelty audit

Corpus proved finite-packet strict definiteness and scalar Schur-tax summability but explicitly left complete operator placement open. Suzuki screw-function papers, Connes–Consani archimedean trace work, and 2026 M-function literature contain no prime-depth cubic-aperture trace-class completion found.
