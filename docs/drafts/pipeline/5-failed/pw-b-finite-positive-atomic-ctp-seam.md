# PW-B positive atomic CTP seams

- **ID:** pw-b-finite-positive-atomic-ctp-seam
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** `docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md` · PW-B
- **Statement:** No finite or summable-countably atomic positive seam confined to a finite physical-energy interval can realize the two Mellin grades of PW-B functional-equation reflection, even with an independent nonzero seam contact.

## Goal

Kill every finite or summable countable positive CTP completion of the Hawking reverse, while leaving the route’s required literal nonlocal/singular seam obligation explicit and non-circular.

## Gates

- [x] 0 → 1 in-progress: source-pure finite-energy finite/countable atomic seam and two-grade reflection formalized.
- [x] 1 → 2 fully-proven: strict endpoint-gap moment contradiction, dependency-closed.
- [x] 2 → 3 formalized: `RHTower.no_PWFiniteEnergyPositiveAtomicFEReflectionData` and `RHTower.no_PWFiniteEnergyPositiveCountableFEReflectionData`; both leaf `lake build` audits green; standard Lean axioms only.
- [ ] 3 → 4 publication-ready: not applicable to retired subroute.

## Approach

For the interior energy `x = X / (X² + 1)`, grade one fixes positive total seam mass to `x⁻¹`; grade two fixes its first target-energy moment to `x⁻²`. For a countable seam, summability gives the endpoint-gap series `Σ wₙ(X−Eₙ)`. Every term is nonnegative and one is positive, so its sum is positive. But the two grades rewrite it as `x⁻¹X − x⁻² < 0`, because `x⁻¹ > X`, contradiction. The finite-channel proof is the finite-sum specialization.

## No-go closure

- **Exact killing theorem/mechanism:** `no_PWFiniteEnergyPositiveAtomicFEReflectionData` rules out arbitrary finite nonlocal channel mixing. `no_PWFiniteEnergyPositiveCountableFEReflectionData` rules out countably many positive channels when total mass and first moment are summable. Both structures include separate `contact : ℂ` with `contact ≠ 0`; retaining a finite-energy seam contact cannot evade the endpoint-gap obstruction.
- **Strongest positive survivor:** The global reciprocal completion exists and realizes both grades: `nonempty_PWGlobalReciprocalFEReflectionData`. Thus positive atomic reflection requires unbounded reciprocal support; alternatively any finite-energy candidate must abandon the positive atomic moment model through signed/complex or singular/spectral transport.
- **New insight:** Finite-channel and summable countable KMS/Wightman-style positivity are incompatible with PW-B reflection before Xi specialization. The open seam is sharply narrowed to an infinite reciprocal tail or a genuinely signed/complex/singular CTP mechanism, with contact transport still to be derived from the literal Hawking source.
- **Status:** Paper proof is the displayed strict endpoint-gap moment argument. Lean modules `formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingParikhWilczekFinitePositiveAtomicSeamNoGo.lean` and `formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingParikhWilczekCountablePositiveAtomicSeamNoGo.lean`; direct `lake env lean`, leaf builds, and axiom audits passed. Both audits report only `propext`, `Classical.choice`, `Quot.sound`.

## Log

- 2026-09-21 — finite and summable-countable positive atomic PW-B CTP-seam subroutes retired.
