# Twisted Hamburger theorem: a constant root-number twist on a half-line still forces ζ

- **ID:** hamburger-twisted-critical-line
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** krein-producer-loops L235, L236 · STATUS MUST-612
- **Statement.** Setting of Hamburger's theorem on the critical line (as in MUST-603):
  - `f = Σ a_n n^{−s}`, with `Σ|a_n|n^{−σ} < ∞` for `σ > 1`;
  - `E = Γ_ℝ f − βΓ_ℝ(s−1)` continuous on `½ ≤ Re s ≤ 3/2`, holomorphic inside, `O(1/(1+t²))`;
  - boundary values `Γ_ℝ(s)Φ(Im s/2) = E(s) + βΓ_ℝ(s−1)` on the line, with `Φ` polynomially bounded;
  - reflection defect `Γ_ℝ(s)g(Im s/2) = Λ(s) − Λ(1−s)` on the line, with `g` polynomially bounded.

  If, for some `Y ≥ 0` and `κ ≠ 0`, `g = (1−κ^{−1})Φ + r'` on `t < −Y` with `r'` Abel-sublinear (e.g. zero), and `g` is otherwise only polynomially bounded, then `a_n = 2κβ` for every `n`.
  - **One half-line suffices.** Nothing is assumed of the defect on `t ≥ −Y`.
  - With `r' = 0` the hypothesis reads `Λ(1−s) = κ^{−1}Λ(s)` on the lower part of the line. For real coefficients the two halves are conjugate, so this means the phase of `Λ(½+iy)` is eventually constant mod π. The conclusion is that `f` is a multiple of ζ, and then the phase is 0.

## Goal
Hamburger's theorem assumes the exact functional equation (root number 1 on the whole line). This card shows that a constant non-real root number on each half-line changes nothing. This is the engine for producers with finitely many non-integer spectral masses (card `weil-cone-fractional-mass-rigidity`).

## Gates
- [x] 0 → 1
- [x] 1 → 2: L235 paper proof.
- [x] 2 → 3: `RHTower.HamburgerTwisted.coeff_eq_of_critical_line_twisted_defect` (module `RHTower/HamburgerTwistedCriticalLine.lean`, 564 lines).
  - Supporting results: `coeffTheta_eq_defectKernel` (`θ(x) − βx^{−½} = K_Φ(x)`), `norm_pairKernel_le_of_nonneg` (one-sided damping), `tendsto_mul_defectLaplace_upper_radial`, `defectLaplace_split`.
  - `lake env lean` is clean; `#print axioms` gives propext, Classical.choice, Quot.sound; the module is wired into the RHTower umbrella.
- [ ] 3 → 4

## Proof
1. *Untwisted identity.* Mellin inversion of `x^{−½}(e^{−πx} − 1)` on `Re = ¼` (its transform is `Γ_ℝ(s−1)`), added to the critical-line inverse Mellin integral of `θ`, gives `θ(x) − βx^{−½} = K_Φ(x)`. The Laplace step with `ε = 0` gives `L(τ) = β + J_Φ(τ)`.
2. *Defect identity.* `L = S − β/(πτ) + β + J_g`, where `S = Σ a_n e^{−2πnτ}` is `i`-periodic.
3. *Split* `J` along `t > Y`, `t < −Y`, `|t| ≤ Y`, and eliminate the lower piece of `J_Φ` with step 1:
   `L = κS − (κβ/π)/τ + β + K₀`, where `K₀` contains only upper pieces (of `g` and `Φ`), bounded pieces and the lower remainder.
4. *One-sided damping.* For `v ≥ 0`, `Re τ > 0` and `Im τ ≥ 0`, `arg(πτ²) ≥ 0` gives `‖k(v,τ)‖ ≤ 3‖τ‖^{−½}e^{−πv/2}`. Upper pieces therefore vanish radially at every `im`, whatever the growth of `Φ`. Bounded pieces and the remainders are Abel-sublinear.
5. Hamburger's periodicity/residue comparison with `c = −κβ/π` gives `a_n = 2κβ`.

## Why it works
Near the positive imaginary axis the only undamped piece is the lower half-line, so the upper half-line is invisible to the residues at `in`. On the lower half the defect is a constant multiple of the boundary values. That multiple rescales every residue `a_n/(2π)` of `L` by the same factor, and periodicity compares residues only with one another.

## No-go closure
- **Killing mechanism:** constant twists factor out of Hamburger's residue comparison.
- **Strongest positive survivor:** the theorem itself (formal, unconditional).
- **New insight:** Hamburger rigidity is a statement about the *variation* of the critical-line phase, not about its value. Only phase that keeps moving at large heights can escape it.
- **Status:** Lean complete.

## Log
- 2026-10-01 — created at stage 3
