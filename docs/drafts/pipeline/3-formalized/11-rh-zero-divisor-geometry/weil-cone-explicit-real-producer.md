# An explicit Weil-positive system for ζ's archimedean datum: Lebesgue measure minus one atom

- **ID:** weil-explicit-real-producer
- **Stage:** 3-formalized (paper proof and Lean, 2026-10-05)
- **Type:** THEOREM (paper) + THEOREM (Lean, full Weil-positivity statement)
- **Source:** `1-in-progress/hf-positive-hodge-attack/krein-producer-loops.md`, L131
- **Statement:** `lam₀ = 1_{(1,∞)}dx − e^{1/20000}δ_{e^{1/10000}}` is Weil-positive for ζ's archimedean datum (pole weight 1). Its Weil measure is absolutely continuous with density `2[θ'(t) + Re(1/(½+it)) + cos(t/10⁴)] ≥ 1/100`, so the form is coercive.

## Goal
- **Existence over ℝ.** The Weil cone of ζ's archimedean datum, relaxed to signed measures on `(1,∞)`, has nonempty interior. Positivity is produced by the pole density (Lebesgue) plus one negative correction near `x = 1`, which pays for the low-frequency deficit `½ψ(5/4) − ½log π = −0.686` of Γ_ℝ.
- **Localization of RH.** For integer-supported systems, existence (W ≠ ∅, PBAP) is open and RH-strength. The present theorem shows that the whole difficulty is integrality of the support (plus sign), not the archimedean datum.

## Proof (paper)
1. In log coordinates, `T_{lam₀} = arch + e^{−|u|/2} + δ_{u₀} + δ_{−u₀}` with `u₀ = 10^{−4}`. The Lebesgue part cancels `e^{|u|/2}` from the pole term exactly, and the atom enters with weight `e^{u₀/2}e^{−u₀/2} = 1`.
2. `FT(T) = 2θ' + 1/(¼+t²) + 2cos(u₀t) = 2[½Re ψ(5/4+it/2) − ½log π + cos(u₀t)]`, using `½ψ(s/2) + 1/s = ½ψ(s/2+1)`.
3. The bracket is `≥ 1/200` for all `t` (Lean).
4. `T` is tempered with `FT(T) ≥ 0`, so it is positive definite (Bochner–Schwartz). ∎

## Gates
- [x] 0 → 1, 1 → 2: paper proof above.
- [x] Core inequality in Lean: `RHTower.lebesgueAtomWeilDensity_ge`, `RHTower.thetaDeriv_add_pole_add_atom_ge`, `RHTower.half_digamma_add_inv_criticalLine` (module `RHTower/LebesgueAtomArchimedeanWeilDensity`).
- [x] 2 → 3: full Weil-positivity statement in Lean (module `RHTower/LebesgueAtomWeilPositivity`,
  axioms `propext`, `Classical.choice`, `Quot.sound`):
  - `RHTower.LebesgueAtomWeil.weilMeasureFunctional νp νm` — the Weil functional of ζ's archimedean
    datum (pole weight one) for a signed weight system `ν₊ − ν₋` of measures on `(1,∞)`;
    `weilMeasureFunctional_natWeights` shows it equals the corpus `weilFullFunctional lam` for counting
    weights `Σ lam(n)δ_n`, so it is the same Weil cone extended to measures.
  - `pole_sub_lebesgue_eq`: the Lebesgue part cancels `e^{|u|/2}` exactly (change of variables `x = e^u`);
    `integral_atomPart`: the atom enters with weight one.
  - `integral_expNegHalfAbs_mul_eq`: `∫e^{−|u|/2}k = (1/2π)∫ĥ(r)/(¼+r²)dr` (Fourier inversion + Fubini).
  - `lebesgueAtomWeilFunctional_weilTest_eq`: `W_{λ₀}(f⋆g̃) = (1/2π)∫ f̂ conj ĝ ρ dr` — the Weil measure
    is absolutely continuous with density `ρ = γ + 1/(¼+r²) + 2cos(r/10⁴)`;
    `lebesgueAtomDensity_eq`: `ρ = 2[θ' + Re 1/(½+ir) + cos(r/10⁴)]`;
    `one_hundredth_le_lebesgueAtomDensity`: `ρ ≥ 1/100`.
  - `lebesgueAtomWeilFunctional_coercive`: `Re W_{λ₀}(f⋆f̃) ≥ (1/100)∫|f|²`;
    `weilMeasurePositive_lebesgueAtom`: `λ₀` is Weil-positive.

## Log
- 2026-09-29 — created from L131. Paper proof complete; density inequality in Lean.
- 2026-10-05 — full Weil-positivity and coercivity formal (`RHTower/LebesgueAtomWeilPositivity`); moved to stage 3.
