# Analytically tempered signed FZZ reflection collapses by moment determinacy

- **ID:** FZZ-P-SIGNED-NONLOCAL-DETERMINACY
- **Stage:** 3-formalized
- **Type:** THEOREM / ROUTE KILL
- **Source:** `ThetaCuspHawkingFZZParityPositiveNonlocalFEReflectionCollapse` · `HTGeometry.LocalExponentialTestClosure`
- **Lean:** `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingFZZParitySignedNonlocalMomentDeterminacyNoGo`
- **Statement:** Every signed Fermi-weighted nonlocal kernel with a common bilateral exponential window and all reflected integer Mellin rows equals the reciprocal-delay target atom after cancellation; its undressed total variation is therefore at least the forced exponentially singular local weight.

## Goal and discharged burden

This kills the analytically tempered signed finite-measure survivor in the FZZ-P chain

`literal FZZ parity-delay source → signed nonlocal FE reflection → universal reflected-information stationarity → FZZ Mellin completeness → RH`.

It is a pre-divisor obstruction. A polynomially tempered signed finite-measure nonlocal completion with one analytic moment window cannot supply the reflection arrow. The surviving completion must instead be genuinely distributional, moment-indeterminate (no local exponential window), or retain the forced essential singularity.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3  formalized: Lean theorem, targeted `lake build` green, axiom audit clean, umbrella wired
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Proof `[PROVED HERE]`

For each positive `t`, write the signed Fermi-weighted output as `ν₊-ν₋`, with finite positive measures on `ℝ`. Put `a=t⁻¹` and `c=aF(t)>0`. All-grade reflected Mellin covariance states

`∫x^n dν₊ = ∫x^n dν₋ + c a^n` for every `n≥0`.

Therefore `ν₊` and `ν₋ + cδ_a` have identical moments. Their common bilateral exponential window permits application of the corpus moment-determinacy theorem, yielding the exact Jordan identity

`ν₊ = ν₋ + cδ_a`.

Integrability of reciprocal Fermi density against both parts allows undressing. The signed undressed mass is exactly

`c/F(a) = aF(t)/F(a) = a(exp(a)+1)/(exp(t)+1)`.

Total variation dominates this positive mass. Along reciprocal ultraviolet depth, the existing local essential-singularity theorem proves that this lower bound exceeds every polynomial envelope. Hence no data satisfying the packed signed nonlocal reflection and analytic-window conditions can be polynomially tempered.

## Formal certificate

- Main theorem: `no_polynomiallyTempered_FZZCigarParitySignedNonlocalFEReflectionData`
- Exact classification: `fermiWeightedMeasure_eq`
- Undressed identity: `undressedNetMass_eq`
- Sharp lower bound: `forcedWeight_le_undressedVariation`
- Direct check: `lake env lean GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingFZZParitySignedNonlocalMomentDeterminacyNoGo.lean`
- Targeted audit: `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingFZZParitySignedNonlocalMomentDeterminacyNoGo`
- Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`
- Umbrella: wired into `formal/GaloisForLFunctions/RHTower.lean`

## No-go closure

- **Exact killing theorem/mechanism:** `no_polynomiallyTempered_FZZCigarParitySignedNonlocalFEReflectionData`; all moment rows plus one common bilateral exponential window force the signed kernel's net contribution to be the reciprocal-delay atom, whose undressed variation has essential ultraviolet growth.
- **Strongest positive survivor:** Exact Jordan identity `ν₊ = ν₋ + cδ_a` and exact forced undressed mass. Only distributional or moment-indeterminate transport can evade the classification without accepting essential singularity.
- **New insight:** Signed cancellation creates apparent freedom at finitely many Mellin grades, but analytic all-grade covariance eliminates it completely before divisor information enters.
- **Status:** Paper proof and Lean formalization complete. Full FZZ-P route remains open only through the stated non-finite-measure/non-determinate survivors.

## Log

- 2026-08-30 — created after positive-kernel collapse exposed signed/distributional nonlocal completion as sharp FZZ-P survivor.
- 2026-08-30 — proved exact signed measure classification, undressed variation lower bound, and unconditional polynomial-tempering no-go; formalized, built, axiom-audited, and wired.
