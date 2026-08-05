# Adelic phase-defect character-blindness law

- **ID:** `adelic-phase-defect-character-blindness-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — universal law + no-go
- **Source:** literature sweep (arXiv 2604.25288 *Reciprocity and the Maslov Phase*) tested against
  Route R's `route-r-kummer-cyclic-one-cocycle-detector` and `cofinal-bockstein-polarized-adelic-stokes`
- **Statement:** the coboundary defect of a local phase is exactly the phase modulo the character
  group; hence no invariant of reciprocity data can detect a character twist, and in particular no
  defect-level criterion on the rational adelic scaling group is equivalent to `Re ρ = 1/2`.

## Goal

Route R's cofinal-Bockstein card records a *first hostile discriminator*: the two endpoint residues

```text
α_ρ(n) = n^(1/2 - Re ρ),   β_ρ(n) = n^(Re ρ - 1/2)
```

satisfy `α_ρ · β_ρ = 1` for every spectral parameter by the adelic product formula, whereas RH
requires `α_ρ = β_ρ`. The card marks as `[FALSIFIED]` any proposal that derives only reciprocity or
full-product gain one. That verdict was a case-by-case judgement. This card converts it into a
theorem: reciprocity data is a *quotient* of phase data by the character group, and the endpoint
residues are exactly characters, so the quotient is blind to them by construction.

## Gates

- [x] 0 → 1 in-progress: abstract model frozen (commutative scaling group, commutative value group)
- [x] 1 → 2 fully-proven: complete algebraic proof, no analytic input
- [x] 2 → 3 formalized: Lean modules below, axiom audit `[propext, Classical.choice, Quot.sound]`
- [ ] 3 → 4 publication-ready: not intended as standalone publication

## The law

Let `G` be a commutative group of scalings and `N` a commutative group of values. For a local phase
`γ : G → N` define the **coboundary defect**

```text
μ_γ(a,b) = γ a · γ b · (γ 1 · γ (a·b))⁻¹.
```

1. **Cocycle structure.** `μ_γ` is symmetric, unital in each argument, and satisfies the two-cocycle
   identity `μ(a,b)·μ(ab,c) = μ(b,c)·μ(a,bc)`. It vanishes exactly when the unit-normalised phase
   `a ↦ γ a · (γ 1)⁻¹` is a homomorphism.
2. **Classification (the universal law).** For phases normalised at the unit,
   `μ_γ = μ_δ ⟺ ∃ χ : G →* N, δ = χ · γ`.
   The defect layer *is* the phase layer modulo the character group — no more, no less.
3. **Abstract reciprocity.** For a finite family of places `γ : V → G → N`, the total defect is the
   coboundary defect of the global normalised phase:
   `∏_v μ_{γ_v}(a,b) = Γ(a)·Γ(b)·Γ(ab)⁻¹` with `Γ(a) = ∏_v γ_v a · (γ_v 1)⁻¹`.
   So `∏_v μ_v ≡ 1` is *equivalent* to multiplicativity of `Γ`, and carries no further content.
4. **No-go.** If a predicate `P` on defect data satisfies
   `P(μ_{χ·γ}) ↔ χ = 1` for all characters `χ`, then every character is trivial. Contrapositively,
   as soon as one nontrivial character exists, no such `P` exists.

## Shadow table

| Known item | Its shadow under the law |
|---|---|
| Hilbert reciprocity via the Kashiwara–Maslov phase (arXiv 2604.25288): `(a,b)_v = γ_v(a)γ_v(b)/(γ_v(1)γ_v(ab))`, `∏_v (a,b)_v = 1` | item 3 with `γ_v` the local Weil index |
| Route R adelic product formula `α_ρ · β_ρ = 1` | item 3 for a two-place normalised phase |
| `[FALSIFIED]` verdict on reciprocity-only proposals in `cofinal-bockstein-polarized-adelic-stokes` | item 4 |
| "finite and archimedean Haar characters cancel on the full rational adelic source" | item 2: cancellation is a character twist, invisible to the defect |

## Route R consequence

On the actual Route R object — the scaling group `CCMRationalAdelicScaling` of the exact rational
adelic crossed product — the logarithmic Kummer weight `ℓ(q) = log |q|` is additive, hence a
character; scaling it by `s ∈ ℂ` gives a faithful one-parameter family, faithful because the
ordinary prime scalings carry weight `log p ≠ 0`. Specialising `s = 1/2 - Re ρ` gives the
source-inverse endpoint residue, whose triviality is exactly `Re ρ = 1/2`.

Therefore: **no criterion formulated at the level of reciprocity data on the rational adelic source
can force the critical line.** The open producer of `route-r-kummer-cyclic-one-cocycle-detector` —
"construct the all-degree source-to-Xi comparison and prove it preserves `φ_ℓ`" — is now known to be
*necessarily* phase-level: the comparison must transport the cyclic cocycle `φ_ℓ` itself, and any
weakening to its coboundary defect is provably dead.

## Lean

- `formal/GaloisForLFunctions/RHTower/AdelicPhaseDefectCharacterBlindnessLaw.lean`
  - `phaseDefect_cocycle`, `phaseDefect_comm`, `phaseDefect_eq_one_iff`
  - `phaseDefect_character_smul`, `phaseDefect_eq_iff_exists_character`
  - `prod_phaseDefect`, `prod_phaseDefect_eq_one_iff`, `prod_phaseDefect_character_smul`
  - `eq_one_of_phaseDefect_criterion`, `not_exists_phaseDefect_criterion`
  - `xiSourceInverseCharacter_eq_one_iff`, `xiSourceInverse_mul_xiAnalyticAdjoint`,
    `no_phaseDefect_criterion_detects_criticalLine`
- `formal/GaloisForLFunctions/RHTower/RouteRAdelicDefectCharacterBlindness.lean`
  - `adelicLogPowerCharacter`, `adelicLogPowerCharacter_eq_one_iff`
  - `adelicXiSourceInverseCharacter_eq_one_iff`,
    `adelicXiSourceInverse_mul_adelicXiAnalyticAdjoint`
  - `not_exists_phaseDefect_criterion_adelicScaling`,
    `no_phaseDefect_criterion_detects_criticalLine_adelicScaling`

All statements are unconditional; the axiom audit shows only `propext`, `Classical.choice`,
`Quot.sound`.

## Falsifier

Exhibit a group `G` with a nontrivial character `χ : G →* N` and a predicate on defect data that is
equivalent to `χ = 1`. Item 4 shows this is impossible, so the law is falsified only by an error in
the classification, i.e. by two unit-normalised phases with equal defect that do not differ by a
character.

## Log

- 2026-08-05 — created directly at stage 3; law proved and formalized, Route R instantiation closed
