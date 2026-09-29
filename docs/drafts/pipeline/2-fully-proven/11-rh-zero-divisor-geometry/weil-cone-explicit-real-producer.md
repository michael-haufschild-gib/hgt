# An explicit Weil-positive system for ζ's archimedean datum: Lebesgue measure minus one atom

- **ID:** weil-explicit-real-producer
- **Stage:** 2-fully-proven (paper), core inequality formalized (Lean)
- **Type:** THEOREM (paper) + THEOREM (Lean, density form)
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
- [ ] Full Weil-positivity statement in Lean: needs the x-space explicit-formula distribution and Plancherel (the corpus's CCM/archimedean Weil kernel layer is the natural host).

## Log
- 2026-09-29 — created from L131. Paper proof complete; density inequality in Lean.
