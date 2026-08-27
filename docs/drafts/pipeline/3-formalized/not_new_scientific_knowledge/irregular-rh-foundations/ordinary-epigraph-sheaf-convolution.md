# Ordinary epigraph sheaf convolution

- **ID:** ordinary-epigraph-sheaf-convolution
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** irregular microlocal Riemann--Hilbert foundations
- **Statement:** Integer-module sheaves on two closed exponential epigraphs admit an underived convolution bifunctor formed by pullback to the fiber product, sheafified tensor, and direct image along certified proper fiberwise addition.

## Goal
Construct the honest ordinary-sheaf precursor of enhanced convolution. Keep exact boundary: no derived functor, enhanced quotient, ind-sheaf, D-module, or RH implication.

## Gates
- [x] 0 → 1  in-progress: exact coefficient category, fiber-product maps, tensor construction, and proper pushforward identified
- [x] 1 → 2  fully-proven: complete construction audit below, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: exact construction, direct module check, targeted module build, umbrella wiring, and authoritative repository lint pass
- [ ] 3 → 4  publication-ready: standalone paper (construction + Lean certificate + Door-2)

## Approach
Use `ModuleCat ℤ`, whose monoidal product is tensor over integers rather than cartesian product. Pull each sheaf back from its exponential epigraph to the paired epigraph, apply pointwise presheaf tensor, sheafify, then direct-image along the already proved proper addition map.

## Construction audit

`[PROVED HERE]` For phases `φ,ψ`, both projections from the paired epigraph to its two epigraph factors are continuous. Sheaf pullback therefore gives two functors into integer-module sheaves on the paired epigraph. The pointwise tensor bifunctor on presheaves uses the monoidal structure of `ModuleCat ℤ`; sheafification produces the standard tensor product sheaf without assuming pointwise tensor preserves the sheaf condition. Composing the product of both pullback functors with this sheafified tensor gives an external-tensor bifunctor on the paired support.

For continuous phases, restricted fiberwise addition is already proved proper. Ordinary direct image along this map therefore supplies the underived proper-map pushforward needed in this closed-support case. Composing it with external tensor gives the claimed convolution bifunctor, with target type the exponential epigraph of `φ+ψ`. Applying the bifunctor to constant integral sheaves gives the rank-one integral specialization.

The construction deliberately does not define `f_!` for a nonproper map, derive tensor or direct image, impose convolution coherence isomorphisms, or form the enhanced quotient.

## Lean certificate

- Module: `GaloisForLFunctions.HTGeometry.StokesOrdinaryEpigraphConvolution`
- Main declarations:
  - `sheafTensorFunctor`
  - `epigraphExternalTensorFunctor`
  - `epigraphFiberwiseAdditionHom_isProperMap`
  - `ordinaryEpigraphConvolutionFunctor`
  - `integralOrdinaryEpigraphConvolution`
- Direct module check: PASS.
- Targeted module build: PASS.
- New-declaration axiom audit: only `propext`, `Classical.choice`, `Quot.sound` (`IntModuleCat` abbreviation uses only `propext`).

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** Not applicable.
- **Strongest positive survivor:** Not applicable.
- **New insight:** Correct coefficient tensor requires `ModuleCat ℤ`; cartesian monoidal `AddCommGrpCat` would encode direct product, not tensor over integers.
- **Status:** Dependency-closed ordinary construction and Lean formalization complete; convolution coherence, derived enhancement, and irregular RH remain open.

## Log
- 2026-08-24 — created after corpus search found no existing external tensor or proper-support convolution declaration; local mathlib API prototype typechecked.
- 2026-08-24 — bifunctor construction checked; targeted build and new-declaration axiom audit passed; moved to 2-fully-proven.
- 2026-08-26 — exact card-to-Lean audit, direct module check, targeted module build, umbrella-wiring lint, and authoritative repository lint passed; promoted to 3-formalized.
