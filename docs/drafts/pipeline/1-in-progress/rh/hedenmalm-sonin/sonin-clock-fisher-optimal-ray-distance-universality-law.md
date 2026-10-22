# Sonin clock Fisher optimal-ray-distance universality law

- **ID:** `sonin-clock-fisher-optimal-ray-distance-universality-law`
- **Law:** LAW517
- **Stage:** 1-in-progress
- **Type:** THEOREM (dependency-closed paper proof)
- **Register:** `[UNIVERSAL-LAW] [CORPUS-SYNTHESIS]`
- **Target:** `formal/GaloisForLFunctions/RHTower/SoninClockFisherOptimalRayDistanceUniversalityLaw.lean`

## Theorem

For every bounded observation `X` of every normalized physical Sonin state `ψ`, the
invariant-sector weight times erased logarithmic-clock quantum Fisher information is exactly

```text
d² · (||Xψ||² - d²/4),
```

where `d²` is the squared distance from the observed state `Xψ` to its closer real Sonin
scattering ray.  One sign `c ∈ {+1,-1}` attains this distance:

```text
||S(Xψ) - c Xψ||² = d².
```

Thus the hidden Fisher quantity has an attained projective-ray certificate, not merely a sector
decomposition.

## Theorem-generated derivation

Whole-corpus declaration comparison exposed:

- `soninLogClock_homogeneousFidelityDeficit_eq_invariantWeight_mul_erasedQFI`;
- `soninLogFourierScattering_projectiveAsymmetry_eq_rayDistanceSq_mul_massComplement`;
- `exists_sign_soninLogFourierScatteringRayDistanceSq`;
- `soninLogFourierScattering_norm`.

LAW512 identifies homogeneous scattering infidelity with invariant weight times erased QFI.
The ray-distance law identifies the same projective Gram energy with the exact closer-ray
distance polynomial, and separately proves attainment by one real phase.  Corpus does not join
these two descriptions.

## Dependency-closed paper proof

Let `v=Xψ` and let `S` be logarithmic Sonin scattering.  Unitarity gives `||Sv||=||v||`, hence

```text
||v||⁴-|<v,Sv>|² = projectiveGramTangentEnergy(v,Sv).
```

LAW512 makes the left side invariant-sector weight times erased QFI.  The exact ray/asymmetry law
makes the right side `d²(||v||²-d²/4)`.  Transitivity proves the scalar identity.  Apply the
existing ray-selection theorem to `v` to obtain `c=±1`, `|c|=1`, and attained squared distance.
No numerical computation is used.

## Strict corpus delta

Existing files separately give Fisher/sector factorization and closest-ray/asymmetry conversion.
New law identifies the Fisher product with the attained closest-ray polynomial for arbitrary
bounded observations of physical states.

## Gates

- [x] Whole-corpus theorem-leaf discovery
- [x] Prior corpus and failed-route audit
- [x] Dependency-closed paper proof
- [x] Lean formalization; direct `lake env lean`
- [x] Post-proof literature audit
- [ ] Axiom and umbrella audit

## Lean result

`formal/GaloisForLFunctions/RHTower/SoninClockFisherOptimalRayDistanceUniversalityLaw.lean`
proves:

- `soninLogClock_invariantWeight_mul_erasedQFI_eq_rayDistanceSq_mul_massComplement`;
- `exists_sign_soninLogClock_invariantWeight_mul_erasedQFI_eq_rayDistance`.

Direct exact check passed without warnings:

`lake env lean GaloisForLFunctions/RHTower/SoninClockFisherOptimalRayDistanceUniversalityLaw.lean`

The module is imported by `GaloisForLFunctions/RHTower.lean`.

## Post-proof novelty audit

Performed only after dependency-closed Lean proof passed.  Searches found general pure-state QFI
formulas, direct QFI measurement via fluctuations, Fisher-symmetric measurements, and
Fisher/coherence relations.  No source linked logarithmic Sonin scattering, erased clock QFI,
and an attained closest `±1` scattering-ray distance through this exact homogeneous
mass-complement polynomial.

Verdict: `[NOVELTY PLAUSIBLE — SEARCH NOT EXHAUSTIVE]`.  Novelty is claimed for the exact Sonin
clock/scattering identity and its attained phase certificate, not for generic QFI--fidelity or
two-sector algebra.

## Log

- 2026-07-26 — LAW517 generated from Sonin fidelity--Fisher and exact ray-distance closure.
- 2026-07-26 — direct Lean check passed; wired into RHTower umbrella; post-proof audit plausible.
