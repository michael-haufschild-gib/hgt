# ζ-mass rigidity: a Weil function whose spectral measure integrates |ζ(½+it)| is von Mangoldt's, and forces RH

- **ID:** weil-zeta-mass-rigidity
- **Stage:** 3-formalized (atomic and measure forms, 2026-09-29)
- **Type:** THEOREM (paper + Lean, general signed spectral measures)
- **Source:** `1-in-progress/hf-positive-hodge-attack/krein-producer-loops.md`, L151.
  - Generalizes L150 (`3-formalized/11-rh-zero-divisor-geometry/weil-cone-crystalline-producer-rigidity.md`) from atoms on the zeta spectrum to arbitrary spectral measures of finite ζ-mass.
  - Makes the L144 defect law unconditional and decisive.
- **Statement.**
  - **Data.** A positive Borel measure `ν` on ℝ and a measurable `w : ℝ → ℝ` with `∫|w|/(1+u²) dν < ∞`.
  - **Spectral function.** `Φ(s) := (1/π) ∫ w(u) Q_u(s) dν(u)`, where `Q_u(s) = 1/(s−½−iu) + 1/(s−½+iu) = 2(s−½)/((s−½)²+u²)`.
  - **Hypotheses.** Let `lam : ℕ → ℝ` with `Σ|lam(n)|n^{−σ} < ∞` for `σ > 1`, and suppose
    - (H) `Γ̃(s) + 1/(s−1) − Σ lam(n) n^{−s} = Φ(s)` on `Re s > 1`, where `Γ̃ = Γ_ℝ'/Γ_ℝ + 1/s`;
    - (Z) `∫ |w(u)| |ζ(½+iu)| dν(u) < ∞`.
  - **Conclusion.** `lam(n) = Λ(n)` for every `n ≥ 2`, and the Riemann hypothesis holds.
  - No positivity is used. No hypothesis is placed on the location of the support of `ν`, and none on the zeros of ζ.

## Meaning for the producer question
- **Every Weil-positive system other than Λ has infinite ζ-mass.**
  - A producer `lam ≠ Λ` must have spectral measure with `∫|ζ(½+it)| dμ_lam = ∞`: it places a ζ-weighted infinite amount of spectral mass away from the zeros.
  - Excluded, unconditionally:
    - crystalline systems on the zeros (L150);
    - all systems with finitely many or summable fake atoms;
    - atoms displaced from the zeros by a summable amount;
    - narrowly smeared zeros (the convergent regime of L132);
    - absolutely continuous slack with `∫|ζ||g| < ∞`.
- **RH criterion.** RH holds if and only if some pair `(lam, w dν)` satisfies (H) and (Z).
  - Forward: `Λ` with `ν = π Σ_γ m_γ δ_γ`, which has ζ-mass 0.
  - Backward: the theorem.

## Proof
1. **The Dirichlet series `F`.** Let `a = 1 ⋆ (lam − Λ)` and `F(s) = Σ a(n)n^{−s} = ζ(s)(L_lam(s) + ζ'/ζ(s))` for `Re s > 1`.
   - Then `Γ_ℝF = G₁ − ΛΦ` there, with `G₁ = Λ₀' + Λ₀(1/s + 1/(s−1)) = Λ ξ'/ξ` (odd, poles at 0 and 1 only). This is `Gammaℝ_mul_riemannZeta_mul_eq` (L150).
2. **The remainder `E`.** Put `Ψ(s) := G₁(s) − Λ(s)Φ(s)` off the critical line and off `{0,1}`. `Ψ` is odd, because `G₁` is odd, `Λ` is even and `Φ` is odd.
   - Let `β = (Λ₀(1) − Φ(1))/2` and `E := Ψ − βΓ_ℝ(s−1)`. The singularity at 1 is removable, so `E` is holomorphic on `Re s > ½`.
   - `E = O(1/(1+t²))` on `¾ ≤ Re s ≤ 3/2`, since `Λ` decays exponentially and `Φ` grows at most like `(1+|t|)²` there.
3. **Theta series.** Let `θ(x) = Σ a(n) e^{−πn²x}`. Its Mellin transform at `s/2` is `Γ_ℝF = E + βΓ_ℝ(s−1)` on `Re s = 3/2`.
4. **Shift to `Re s = ¾` and reflect.**
   - Inverse Mellin shifted to `Re s = ¾`: `θ(x) − βx^{−½}e^{−πx} = (1/2π)∫ x^{−(3/8+it)} E(¾+2it) dt`.
   - Dual side, by `t ↦ −t`, using `E(1−s) = −Ψ(s) + βΓ_ℝ(−s)` for `Re s = ¼`: `x^{−½}θ(1/x) − βe^{−π/x} = −(1/2π)∫ x^{−(1/8+it)} [Ψ(¼+2it) + βΓ_ℝ(−¼−2it)] dt`.
5. **Polar terms.** `Γ_ℝ(s−1)` on `Re s = ¾` and `Γ_ℝ(−s)` on `Re s = ¼` are the Mellin transforms of `x^{−½}(e^{−πx}−1)` and `e^{−π/x}−1`. So the β-terms sum to `β(1 + x^{−½})`, as in the corpus odd Hamburger.
6. **Thin-strip defect.**
   - `(1/2π)[∫ x^{−(3/8+it)}Ψ(¾+2it)dt − ∫ x^{−(1/8+it)}Ψ(¼+2it)dt] = K(x)`.
   - The `G₁`-part cancels: it is holomorphic and decaying on `¼ ≤ Re ≤ ¾`, so the contour shifts.
   - For the `ΛΦ`-part, use Fubini over `ν`; for each `u` write `ρ = ½+iu`.
     - Decompose `Λ Q_u = B_u + (Λ(ρ)/2)Γ((s−ρ)/2) + (Λ(ρ̄)/2)Γ((s−ρ̄)/2)`.
     - `B_u` is holomorphic on the strip. It equals `dslope Λ ρ + dslope Λ ρ̄ − Λ(ρ)·dslope g 0 (s−ρ) − Λ(ρ̄)·dslope g 0 (s−ρ̄)` with `g(z) = Γ(z/2+1)`, since `1/z − ½Γ(z/2) = −(g(z)−g(0))/z`.
     - `Γ(z)` is the Mellin transform of `e^{−x}` on `Re z > 0` and of `e^{−x}−1` on `−1 < Re z < 0`.
     - So the per-`u` strip difference is `½Λ(ρ)(x^{−ρ/2} + x^{−ρ̄/2}) = Λ(½+iu) x^{−¼} cos((u/2) log x)`.
     - Integrability for Fubini: `∫|Λ Q_u| dt ≪ 1/(1+u²)` on both lines.
   - Result: **`K(x) = −(1/π) ∫ w(u) Λ(½+iu) x^{−¼} cos((u/2)log x) dν(u)`**.
   - Atoms on the zeta spectrum contribute nothing, because `Λ(½+iγ) = 0`.
7. **Defect theta relation.** `θ(x) + x^{−½}θ(1/x) = β(1 + x^{−½}) + K(x)` for all `x > 0`.
8. **Laplace step.** Multiply by `τ e^{−πτ²x}` and integrate (real `τ > 0`). This gives `L_a(τ) + E_a(τ) = β/(πτ) + β + J(τ)`, where:
   - `L_a(τ) = Σ a(n)τ/(π(n²+τ²))`;
   - `E_a(τ) = Σ a(n)e^{−2πnτ}`;
   - `J(τ) = −(1/2π) ∫ w(u) [ζ(½−iu)τ^{−½−iu}/sin(π(¼−iu/2)) + ζ(½+iu)τ^{−½+iu}/sin(π(¼+iu/2))] dν(u)`.
   - The closed form uses `Λ(½+iu)Γ(¾∓iu/2) = π^{−¼∓iu/2}·π·ζ(½±iu)/sin(π(¼±iu/2))`, from `Γ(z)Γ(1−z) = π/sin πz`.
   - `J` is analytic on `Re τ > 0`, so the identity holds on `Re τ > 0` by the identity theorem.
9. **The 1/sin kernel is bounded.**
   - On `Re τ > 0`: `|τ^{±iu}| = e^{∓u arg τ} ≤ e^{π|u|/2}` and `|1/sin(π(¼±iu/2))| ≤ 2e^{−π|u|/2}` (because `|sin(π/4+iy)|² = ½cosh 2y`).
   - Hence **`|J(τ)| ≤ (2/π)|τ|^{−½} ∫|w||ζ(½+iu)|dν`**.
   - By (Z), `J` is bounded near every `in₀` with `n₀ ≥ 1`, and `τJ(τ) → 0` as `τ → 0`.
10. **Residue comparison.** `E_a` is `i`-periodic, so `L_a(τ+i) − L_a(τ) = β/(π(τ+i)) − β/(πτ) + [J(τ+i) − J(τ)]`, and `(τ − in₀)[J(τ+i) − J(τ)] → 0` at every `in₀`. Hamburger's residue comparison (corpus `coeff_eq_of_hamburgerSeries_periodic_re_pos`, with a vanishing perturbation) gives `a(n) = −2β` for all `n ≥ 1`.
11. **Conclusion.**
    - `1⋆(lam − Λ) = −2β·1` gives `lam − Λ = −2βδ₁`, so `lam(n) = Λ(n)` for `n ≥ 2`.
    - Then `ξ'/ξ + 2β = Φ` on `Re s > 1`, so `Λ' = Λ·(Φ − 2β − 1/s − 1/(s−1))` on `Re s > ½`, `s ≠ 1`, by the identity theorem. The coefficient is holomorphic there.
    - A zero of `Λ` with `Re > ½` would be non-isolated (`eventually_eq_zero_of_deriv_eq_mul`). So there is none, and RH holds. ∎

## Sanity checks
- **`ν` atomic on the zeros:** `K ≡ 0` and `J ≡ 0`. This is L150.
- **`ν` = α·Lebesgue:**
  - `K = −2α(ϑ − 1 − x^{−½})` and `a ≡ −2α` (`lam = Λ − 2αδ₁`): the theorem's conclusion `lam(n) = Λ(n)` (n ≥ 2) is consistent.
  - (Z) fails here, since `∫|ζ(½+iu)|du = ∞`. `J` then has poles at `±in`, matching L144's Abel law.

## Gates
- [x] 0 → 1, 1 → 2: proof above.
- [x] 2 → 3: Lean, atomic form and measure form (see Lean section).
  - Plan: the atomic version first (tsum, reusing L150's `atomicPairSeries`); the measure version next.
  - New pieces:
    - the inverse Mellin on `Re s = ¾`;
    - the Γ-absorbed thin-strip identity;
    - the defect Laplace step;
    - the 1/sin bound;
    - a perturbed residue comparison.

## Log
- 2026-09-29 — created from L151 (paper complete).

## Lean
- **Modules** (wired into `GaloisForLFunctions/RHTower.lean` after `CrystallineProducerRigidity`):
  - `formal/GaloisForLFunctions/HTGeometry/HamburgerThetaDefect.lean`: the inverse Mellin shift to `Re s = ¾`, the Γ thin-strip identity `gamma_thin_strip_inverse_mellin`, the defect Laplace step `hamburgerSeries_eq_of_coeffTheta_relation_defect`, and the perturbed residue comparison `coeff_eq_of_hamburgerSeries_periodic_re_pos_of_defect`.
  - `formal/GaloisForLFunctions/RHTower/SpectralAtomThinStrip.lean`: steps 1–7. Main result `coeffTheta_spectral_defect_relation`.
  - `formal/GaloisForLFunctions/RHTower/ZetaMassRigidity.lean`: steps 8–11. Main result `zeta_mass_rigidity`.
- **Statement formalized** (`RHTower.zeta_mass_rigidity`). The spectral measure is `ν = Σ_j c_j (δ_{t_j} + δ_{−t_j})/2`, with:
  - `t_j ≥ 1` and `Σ|c_j|/t_j² < ∞`;
  - (Z) `Σ|c_j| |ζ(½+it_j)| < ∞`;
  - (H) `Γ̃ + 1/(s−1) − L_lam = atomicPairSeries c t` on `Re s > 1`.
  - Conclusion: `(∀ n ≥ 2, lam n = Λ n) ∧ RiemannHypothesis`.
  - The ordinates are otherwise arbitrary; nothing is assumed about zeros of ζ.
- **Axioms:** `propext, Classical.choice, Quot.sound` only, checked in a scratch file.
- **Lint:** the gate is clean for all three modules.
- **Lean-side constants:**
  - The atom Laplace kernel bound is `3|ζ(½+iu)||τ|^{−½}` (`norm_completedRiemannZeta_mul_Gamma_laplace_le`), rather than the paper's `2/π` normalisation.
  - The RH step uses the quarter plane `{Re > ½, Im > 0}` and conjugation.
- **Measure form (added 2026-09-29):** `RHTower.zeta_mass_rigidity_measure` and `RHTower.zeta_mass_sublinear_rigidity_measure_of_truncated` (module `RHTower/SpectralMeasureZetaMassRigidity`, on top of the abstract engine `RHTower/OddWeilFunctionRigidity`).
  - Spectral data are `(X, ν, c, t)` with `c, t` measurable, `t ≥ 1` and `∫|c|/t² dν < ∞`, and `[SFinite ν]`.
  - A signed measure `μ` on `[1,∞)` is `ν = |μ|`, `c = dμ/d|μ|`.
- 2026-09-29 — Lean closed for the atomic form (three modules, all wired). Moved to 3-formalized.
- 2026-09-29 — Measure form formalized: the abstract odd-Weil-function engine plus the spectral-measure instance (L154).
