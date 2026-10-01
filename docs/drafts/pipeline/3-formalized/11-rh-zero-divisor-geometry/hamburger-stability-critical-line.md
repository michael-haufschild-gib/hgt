# Hamburger stability: a sublinear defect on the critical line forces ζ

- **ID:** hamburger-stability-critical-line
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** krein-producer-loops L227 (Step B), L228, L229 · STATUS MUST-603
- **Statement.** Let `Σ|a_n| n^{−σ} < ∞` for `σ > 1`. Let `E` be continuous on `½ ≤ Re s ≤ 3/2`, holomorphic inside, and `O(1/(1+t²))`, with:
  - `Γ_ℝ(s) Σ a_n n^{−s} = E(s) + β Γ_ℝ(s−1)` on `Re s = 3/2`;
  - `E(s) − E(1−s) = −β(Γ_ℝ(s−1) − Γ_ℝ(−s)) + Γ_ℝ(s) g(Im s/2)` on `Re s = ½`.

  If `g` is measurable, polynomially bounded, and Abel-sublinear (`δ ∫‖g(t)‖e^{−δ|t|}dt → 0` as `δ → 0⁺`, e.g. `∫_{−T}^{T}‖g‖ = o(T)`), then `a_n = 2β` for every `n`, i.e. `f = 2βζ`.

## Goal
Hamburger's theorem assumes the exact functional equation. This card proves that a functional-equation defect whose `L¹` mass (weighted by the Gamma factor) grows sublinearly changes nothing. It is Step B of the L227 uniqueness programme.

## Gates
- [x] 0 → 1
- [x] 1 → 2: L228 paper proof.
- [x] 2 → 3: `RHTower.HamburgerStability.coeff_eq_of_critical_line_even_sublinear_defect` (module `RHTower/HamburgerStabilityCriticalLine.lean`, 819 lines). The even theta relation with a defect is `GaloisForLFunctions.HTGeometry.critical_line_even_theta_relation_defect` (module `HTGeometry/HamburgerCriticalLineEvenDefect.lean`).
  - `lake env lean` is clean.
  - `#print axioms` gives propext, Classical.choice, Quot.sound.
  - Both modules are wired into their umbrellas.
- [ ] 3 → 4

## Proof
1. **Theta relation.** Both `θ(x)` and `x^{−½}θ(1/x)` are inverse Mellin integrals over the critical line. Subtracting gives `θ(x) − x^{−½}θ(1/x) = β(x^{−½} − 1) + K(x)`, with `K(x) = (1/2π)∫x^{−(¼+it)}Γ_ℝ(½+2it)g(t)dt`.
2. **Laplace kernel.** The Laplace transform of `K` is `J(τ) = (1/2π)∫g(t)k(2t, τ)dt`. Here `k(v, τ) = π^{−ρ/2}Γ(ρ/2)Γ(1−ρ/2)·τ(πτ²)^{−(1−ρ/2)}` with `ρ = ½+iv`. It is computed by Fubini, using `Γ_ℝ`'s exponential decay on `Re s = ½`.
3. **Damping.** The reflection formula and `|arg(πτ²)| ≤ π − 2Re τ/‖τ‖` give `‖k(v, τ)‖ ≤ 3‖τ‖^{−½}e^{−|v|Re τ/‖τ‖}`, and the τ-derivative obeys the same bound with a factor `1+|v|`. Dominated differentiation then makes `J` holomorphic on `Re τ > 0`.
4. **Radial vanishing.** On `τ = ε + im` the damping rate is at least `ε/(m+1)`, so `ε J(ε+im) → 0` under the Abel condition. At `m = 0`, `εJ(ε) = O(ε^{½})`.
5. **Residues.** The corpus Laplace step (`hamburgerSeries_eq_of_coeffTheta_relation_defect`) and residue comparison (`tendsto_sub_mul_defect_of_radial`, `coeff_eq_of_hamburgerSeries_periodic_re_pos_of_defect`) give `a(n+1) = −2π(−β/π) = 2β`.

## Producer reading
On the line `E(1−s) = conj E(s)` for real coefficients, so the defect is `2i Im(Γ_ℝ F)`, i.e. `|g| = 2|F||sin φ|` with `φ = arg Γ_ℝ F`.
- For a producer `lam`, `φ = πN_ν + c`. So `∫_0^T|F(½+it)||sin πN_ν(t)|dt = o(T)` forces `lam = Λ`, provided `E` has continuous boundary values.
- With L224 Lemma C this gives: a mean-square excess `ℰ(T) = o(T)` forces `lam = Λ`.

## No-go closure
- **Killing mechanism:** Hamburger's residue comparison survives any Abel-sublinear defect.
- **Strongest positive survivor:** the theorem itself (unconditional, formal).
- **New insight:** uniqueness of producers is a lower-bound problem for the phase defect `|F||sin πN_ν|`. Non-Λ producers must be far from their own functional equation in `L¹`.
- **Status:** Lean complete. The producer corollary needs boundary continuity of `E`. That holds for atomic producers, but has not been formalized from `WeilPositiveFull`.

## Log
- 2026-10-01 — created at stage 3
- 2026-10-01 — the producer corollary is now formal in Herglotz form: `RHTower.PhaseLockRigidity.phase_lock_rigidity_of_defect` (MUST-617, with `κ = 1`). Any Herglotz producer whose exponential is continuous up to the line, and whose reflection defect divided by `s(s−1)Γ_ℝ(s)` is Abel-sublinear, is `Λ`, and RH follows.
