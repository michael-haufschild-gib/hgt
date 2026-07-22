# Suzuki coherent causal-depth fusion — formalization certificate

- **Stage:** 3 — formalized in Lean 4
- **Paper theorem:**
  `../../2-fully-proven/new_scientific_knowledge/suzuki-coherent-causal-depth-fusion.md`
- **Lean module:**
  `formal/GaloisForLFunctions/RHTower/SuzukiCoherentCausalDepthFusion.lean`
- **Umbrella import:**
  `formal/GaloisForLFunctions/RHTower/RiemannHypothesisSOTA2026.lean`
- **RH used:** no
- **Computation used:** no

## Formal theorem surface

Lean proves unconditionally:

- `suzukiCriticalEntryWallEndpointAmplitude_zero_eq_coherentWeight`: exact extra
  inverse-prime endpoint damping;
- `summable_suzukiCriticalEntryWallCoherentMajorant`: logarithmic `p^(-5/4)` majorant is summable;
- `summable_norm_suzukiCriticalApertureDepthFusedAtom_allPrime`: valuation-fused prime rays are
  `ell^1` over all primes;
- `suzukiCriticalApertureCoherentlyFusedAtom_neg_eq_star`: coherent FE reflection;
- `normSq_suzukiCriticalApertureCoherentFiniteSum_eq_crossPrimeGram`: exact finite double-prime
  Gram expansion;
- `normSq_suzukiCriticalApertureCoherentlyFusedAtom_eq_crossPrimeGram`: absolutely convergent
  cofinal double-prime Gram;
- `norm_suzukiCriticalApertureCoherentlyFusedAtom_le_cap`: global coherent cap;
- `suzukiCriticalApertureCoherentSeparation_nonneg`: nonnegative global height deficit;
- `suzukiCriticalApertureCoherentSeparation_eq_zero_iff`: deficit vanishes exactly at equal
  heights.

## Boundary

Module constructs the concrete coherent cross-prime carrier but does not assert its equality with
the rectangular Robin--Gamma--holonomy trace, Ward semiboundedness, or RH.

## Verification

- `lake env lean GaloisForLFunctions/RHTower/SuzukiCoherentCausalDepthFusion.lean`: passes.
- `lake build GaloisForLFunctions.RHTower.SuzukiCoherentCausalDepthFusion`: passes, 9337/9337 jobs.
- `#print axioms` for all-prime summability, cofinal Gram expansion, and faithful separation reports
  only `propext`, `Classical.choice`, and `Quot.sound`.
- Forbidden-declaration scan of this module is empty; `git diff --check` passes.
- Repository-wide formal lint is presently red only because unrelated concurrent new modules are
  not yet imported by their theorem-area umbrellas; it reports no defect in this module.
