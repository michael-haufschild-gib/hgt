# Route R: reciprocity data is provably blind to the critical line

Formalized 2026-08-05. Triggered by arXiv 2604.25288 *Reciprocity and the Maslov Phase*
(Hilbert symbol = coboundary defect of the local Weil index; reciprocity = total defect one).

## The law

For a local phase `γ : G → N` (both commutative groups) define the coboundary defect
`μ_γ(a,b) = γa · γb · (γ1 · γ(ab))⁻¹`.

- **Classification**: for phases normalised at the unit, `μ_γ = μ_δ ⟺ ∃ χ : G →* N, δ = χ·γ`.
  The defect layer IS the phase layer modulo the character group.
- **Reciprocity**: over a finite place set, `∏_v μ_{γ_v}(a,b)` equals the coboundary defect of the
  global normalised phase. So `∏_v μ_v ≡ 1 ⟺ the global phase is multiplicative`, nothing more.
- **No-go**: if a predicate `P` on defect data satisfies `P(μ_{χγ}) ↔ χ = 1` for all characters `χ`,
  then every character is trivial. One nontrivial character kills every such `P`.

## Why it matters for Route R

On `CCMRationalAdelicScaling` the Kummer log weight `ℓ(q)=log|q|` is a character; scaled by `s ∈ ℂ`
it gives a FAITHFUL one-parameter family (faithful because `log p ≠ 0` on ordinary primes).
`s = 1/2 − Re ρ` is the source-inverse endpoint residue `α_ρ`, and `α_ρ = 1 ⟺ Re ρ = 1/2`.

Therefore no criterion on reciprocity/defect data over the rational adelic source can force the
critical line. `α_ρ·β_ρ = 1` is defect-level, hence separates nothing — the cofinal-Bockstein
card's `[FALSIFIED]` verdict on reciprocity-only proposals is now a theorem, not a judgement.

**Producer consequence**: the open Route R obligation ("all-degree source-to-Xi comparison
preserving `φ_ℓ`") cannot be weakened to preserving the *defect* of `φ_ℓ`. The comparison must
transport the cyclic cocycle itself. Stokes-boundary-defect matching, product-formula gains, and
Haar-character cancellation are all in the blind quotient.

## Lean

- `GaloisForLFunctions/RHTower/AdelicPhaseDefectCharacterBlindnessLaw.lean` — abstract law
  (`phaseDefect_eq_iff_exists_character`, `prod_phaseDefect_eq_one_iff`,
  `not_exists_phaseDefect_criterion`, `no_phaseDefect_criterion_detects_criticalLine`)
- `GaloisForLFunctions/RHTower/RouteRAdelicDefectCharacterBlindness.lean` — instantiation on the
  actual scaling group (`adelicLogPowerCharacter_eq_one_iff`,
  `no_phaseDefect_criterion_detects_criticalLine_adelicScaling`)

Unconditional: `[propext, Classical.choice, Quot.sound]`.

Card: `docs/drafts/pipeline/3-formalized/adelic-phase-defect-character-blindness-law.md`.

## Lean gotchas hit

- `group` tactic does NOT use commutativity; for `CommGroup` identities use
  `simp [mul_comm, mul_left_comm, mul_assoc, mul_inv_rev]`, and when simp stalls on cross
  cancellation rewrite with `← div_eq_mul_inv` and use `div_eq_div_iff_mul_eq_mul` / `div_mul_div_comm`.
- `to_additive` cannot be used when only ONE of two group parameters should be additivised.
- `Multiplicative.ofAdd_add` / `Multiplicative.toAdd_mul` do not exist; use root `ofAdd_add` and
  `rfl`. `x = x + x → x = 0` is `left_eq_add.mp`.
