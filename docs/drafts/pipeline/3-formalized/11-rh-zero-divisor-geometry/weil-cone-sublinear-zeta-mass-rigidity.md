# Sublinear ζ-mass rigidity: `Σ_{t_j ≤ T}|c_j||ζ(½+it_j)| = o(T)` forces `lam = Λ` and RH

- **ID:** weil-sublinear-zeta-mass-rigidity
- **Stage:** 3-formalized (2026-09-29)
- **Type:** THEOREM (paper + Lean)
- **Source:** `1-in-progress/hf-positive-hodge-attack/krein-producer-loops.md`, L152.
  - Sharpens L151 (`weil-cone-zeta-mass-rigidity.md`) from finite to sublinear ζ-mass.
- **Statement.**
  - **Hypotheses.**
    - `lam : ℕ → ℝ` with `Σ|lam(n)|n^{−σ} < ∞` for `σ > 1`.
    - `t_j ≥ 1` and `Σ|c_j|/t_j² < ∞`.
    - (H) `Γ̃(s) + 1/(s−1) − Σ lam(n)n^{−s} = (2(s−½)/π)Σ_j c_j/((s−½)²+t_j²)` on `Re s > 1`.
    - (Z_o) `Σ_{t_j ≤ T}|c_j||ζ(½+it_j)| = o(T)`.
  - **Conclusion.** `lam(n) = Λ(n)` for `n ≥ 2`, and RH.
  - **Equivalent Abel form.** `δ·Σ_j|c_j||ζ(½+it_j)|e^{−δt_j} → 0` as `δ → 0⁺` replaces (Z_o).
  - No positivity is used, and the ordinates are arbitrary.
- **Reading.**
  - A Weil-positive system's spectral measure has mass `~ (T/2π)log T` on `[0,T]`. So (Z_o) says: on average, the ζ-weight of the spectral mass is `o(1/log T)`.
  - Every spectrum that is ζ-light in this sense is exactly the zero spectrum.
  - Any second producer must carry ζ-mass at least linear in `T` along a sequence.
- **Sharpness (signed case).**
  - `lam ≡ 1` satisfies (H) with a signed absolutely continuous `μ`, since `ζ(s) − 1/(s−1)` continues. Its ζ-mass is of order `T(log T)^{5/4}`, which is superlinear.
  - It is open whether some signed pair with `lam ≠ Λ` reaches linear ζ-mass.

## Proof
1. **Damped kernel.**
   - For `Re τ > 0`, `|arg τ| ≤ π/2 − Re τ/|τ|`, because `cos θ = sin(π/2−θ) ≤ π/2−θ`.
   - The phase of `(πτ²)^{iu/2}` therefore costs at most `e^{|u|(π/2 − Re τ/|τ|)}`. Against the `1/sin` decay `e^{−π|u|/2}`, the atom Laplace kernel is `≤ 3|ζ(½+iu)||τ|^{−½}e^{−|u|Re τ/|τ|}`.
2. **`J` without a ζ-mass hypothesis.**
   - `J` is holomorphic on `Re τ > 0`, since on compact sets the damping is uniform and `Σ|c_j||ζ(½+it_j)|e^{−δt_j} < ∞` for `δ > 0` (`|ζ(½+it)| ≪ t` and `Σ|c_j|/t_j² < ∞`).
   - The defect Laplace identity of L151 holds as before.
3. **Radial limits.**
   - At `τ = ε + im` (with `m ≥ 1`, `ε ≤ 1`) the damping rate is `≥ ε/(m+1)` and `|τ|^{−½} ≤ 1`. So `ε|J(ε+im)| ≤ (3/π)(m+1)·δM(δ)` with `δ = ε/(m+1)`, which tends to 0 under the Abel form.
   - At `m = 0`, `ε|J(ε)| ≤ (3/π)M(1)ε^{½}`.
4. **Radial limits suffice.** In `L(t+i) − L(t) = c/(t+i) − c/t + K(t)`, every other term has a limit at `in₀` from `Re t > 0`, so `(t−in₀)K(t)` has one. The ray `t = ε+in₀` identifies it as 0. Hamburger's residue comparison then gives `1⋆(lam−Λ) ≡ −2β`, and the L151 conclusion follows.
5. **Abelian step.**
   - Layer cake: `e^{−δx} ≤ Σ_{k: x ≤ k+1} r^k(1−r)` with `r = e^{−δ}`.
   - Hence `M(δ) ≤ Σ_k r^k(1−r)S(k+1) ≤ η/(1−e^{−δ}) + C` when `S(T) ≤ ηT + C`, where `S(T) = Σ_{t_j≤T}|c_j||ζ(½+it_j)|`.
   - With `δ/(1−e^{−δ}) ≤ 2` on `(0,1]`, this gives `δM(δ) ≤ 2η + Cδ`. ∎

## Lean
- **Module** `formal/GaloisForLFunctions/RHTower/ZetaMassSublinearRigidity.lean`, wired after `ZetaMassRigidity`.
- **Main theorems:**
  - `RHTower.zeta_mass_sublinear_rigidity_of_truncated` (counting form);
  - `RHTower.zeta_mass_sublinear_rigidity` (Abel form).
- **Axioms:** `propext, Classical.choice, Quot.sound`.
- **Pieces:**
  - `abs_arg_le_of_re_pos`;
  - `norm_completedRiemannZeta_mul_Gamma_laplace_le_decay`;
  - `differentiableOn_spectralDefectLaplace_of_summable`;
  - `tendsto_mul_spectralDefectLaplace_radial`;
  - `tendsto_sub_mul_defect_of_radial` (radial Hamburger residue comparison);
  - `exp_neg_mul_le_tsum_indicator`, `dampedZetaMass_le_of_truncated`, `tendsto_mul_dampedZetaMass_of_sublinear`.
- **Refactor.** `ZetaMassRigidity` now exposes `vonMangoldt_and_RH_of_crystallineCoeff_eq`: constant coefficients of `1⋆(lam−Λ)` imply `lam = Λ` and RH.

## Log
- 2026-09-29 — L152 paper and Lean closed on the same day.
- 2026-09-29 — Measure form: `RHTower.zeta_mass_sublinear_rigidity_measure_of_truncated` (general signed spectral measures, `∫_{t≤T}|c||ζ(½+it)|dν = o(T)`). Module `RHTower/SpectralMeasureZetaMassRigidity`.
