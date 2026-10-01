# Singular deficit law for Weil-positive completions of ζ's archimedean datum

- **ID:** weil-singular-deficit-law
- **Stage:** 3-formalized (paper 2026-09-29; Lean 2026-10-01, `RHTower/WeilConeSingularDeficitCounting`)
- **Type:** THEOREM (paper)
- **Source:** `1-in-progress/hf-positive-hodge-attack/krein-producer-loops.md`, L126; companion to `weil-cone-finite-type-uniqueness.md`
- **Statement:** Let `lam` be Weil-positive for ζ's archimedean datum, with `w := lam − Λ`. Let `R⁺(T) := Σ_{0<γ≤T, β=½} (m_ρ − c_ρ)⁺`, where `c_ρ` is the atom of `lam`'s Weil measure at ρ, and let `N_off⁺(T)` count zeros with `β > ½`. Then `liminf_T [2N_off⁺(T) + R⁺(T)]/T ≥ sup_{σ>1} M₁(w,σ)/2π ≥ sup_{n≥2} |w(n)|/(4πn)`, where `M₁(w,σ)` is the Bohr mean of `|Re D_w(σ+it)|`.

## Goal
- **Quantitative uniqueness.** A Weil-positive system that differs from Λ must pay in singular modifications, at linear density in `T`, in proportion to its distance from Λ.
- **Complement to finite-type uniqueness.**
  - The finite-type theorem excludes perturbations that modify *every* atom but are algebraically structured (finite Dirichlet polynomials).
  - This law excludes perturbations of *any* structure that modify only `o(T)` atoms.
  - Together they leave only infinite-type completions that modify `≫ T` atoms.
- **Non-circularity.** RH is not assumed. The off-line zeros enter only through their Poisson mass.

## Setting and normalization
- `lam: ℕ_{≥2} → ℝ` with `Σ|lam(n)|n^{−σ} < ∞` for `σ > 1`, and `lam(1) = 0`.
- `W_lam(g) = arch(g) + ĝ(0) + ĝ(1) − Σ_n lam(n)[g(n) + n^{−1}g(1/n)]`.
- `Φ_lam(s) = G_∞(s) + 1/s + 1/(s−1) − D_lam(s)`, with `G_∞ = ½ψ(s/2) − ½log π`. So `Φ_Λ = ξ'/ξ`.
- Weil-positive: `W_lam(h⋆h̃*) ≥ 0` for all `h ∈ C_c^∞(ℝ_{>0}^×)`.

## Proof
1. **Exact Herglotz dictionary.**
   - In the variable `x = log`, `W_lam` is a positive-definite distribution `T_lam`. By Bochner–Schwartz, `T_lam = FT(μ)` with `μ ≥ 0` tempered.
   - Weil's explicit-formula normalization gives `μ = 2 Re Φ_lam(½+i·)` as a boundary value. The one-sided Laplace transform of `T_lam` is `Φ_lam`, and the archimedean regularization at `x = 0` is exactly `G_∞`.
   - The local singularity of `T_lam` at 0 is that of `arch`, so `μ([−U,U]) = O(U log U)` and `∫dμ/(1+u²) < ∞`.
   - Let `H` be the Herglotz function with `Re H = Poisson(μ/2)`. Then `Φ_lam − H` is holomorphic on `Re s > ½` with zero boundary real part. By Schwarz reflection it is entire, and it has polynomial growth, hence equals `a(s−½) + ib` with `a` real.
   - Along the real axis `Φ_lam(σ) ∼ ½log σ` and `H(σ) = O(log σ)`, so `a = 0`. **Hence `Re Φ_lam = Poisson(μ/2) ≥ 0` on `Re s > ½`.** (Holomorphy of `Φ_lam` there is Input (B) of the companion card.)
2. **Subtracting the singular part.**
   - Write `μ/2 = π Σ_{crit ρ} c_ρ δ_γ + ν`, with `ν ≥ 0` carrying everything else (a.c. part, and atoms at non-zeros of ζ).
   - Hadamard gives `Re ξ'/ξ(s) = Σ_ρ Re 1/(s−ρ)`, absolutely convergent.
   - Put `S(s) := Σ_{β>½} m_ρ[1/(s−ρ) + 1/(s−ρ*)] + Σ_{crit} r_ρ/(s−ρ)`, with `ρ* = 1−ρ̄` and `r_ρ = m_ρ − c_ρ`. Its real part converges absolutely; imaginary constants are irrelevant.
   - Then `Ψ := −D_w + S = Φ_lam − ξ'/ξ + S` satisfies `Re Ψ = Poisson(ν) ≥ 0` on `Re s > ½`. Each zero of ξ is accounted for exactly once: off-line zeros through the pairs, critical zeros through `c_ρ + r_ρ = m_ρ`.
3. **Lower envelope.** Fix `σ > 1` and put `f(t) := Re(−D_w(σ+it)) = −Σ_n w(n)n^{−σ}cos(t log n)`.
   - `f` is Bohr almost periodic with mean `−w(1) = 0`.
   - By step 2, `f ≥ −Re S(σ+i·) ≥ −ε(t)`, where `ε(t) := Σ_{β>½} m_ρ Re[1/(s−ρ) + 1/(s−ρ*)] + Σ_{crit} r_ρ⁺ Re 1/(s−ρ) ≥ 0`. Terms with `r_ρ < 0` only help.
4. **Counting.**
   - Each pair's Poisson term has total `t`-mass `2π`, and each critical term has mass `π r_ρ⁺`. The tails outside `[0,T]` contribute `O(σ log T)`. So `∫_0^T ε = π(2N_off⁺(T) + R⁺(T)) + O(log T)`.
   - Since `f⁻ ≤ ε` and `∫_0^T f = o(T)`, we get `∫_0^T |f| = ∫_0^T f + 2∫_0^T f⁻ ≤ 2π(2N_off⁺(T) + R⁺(T)) + o(T)`.
   - Dividing by `T` gives the first inequality.
5. **Coefficient bound.** The Bohr coefficient of `f` at frequency `log n` is `−½w(n)n^{−σ}`, so `M₁(w,σ) ≥ |mean(f(t)cos(t log n))| = ½|w(n)|n^{−σ}`. Let `σ ↓ 1`. ∎

## Corollaries
- **(A) Sparse repair is impossible.** If `lam` is Weil-positive and `2N_off⁺(T) + R⁺(T) = o(T)`, then `lam = Λ`, and hence RH holds with `R⁺ ≡ 0`.
  - This contains L106: pole-free `v` has `N_off⁺ = 0` (its `Φ` is holomorphic) and `R⁺ = 0`.
  - It also contains every finite-singularity variant.
- **(B) Under RH.** Every Weil-positive `lam ≠ Λ` weakens at least `(sup_n|w(n)|/4πn − o(1))·T` critical atoms of Λ, counted with deficit weights.
- **(C) If RH fails with `N_off⁺(T) = o(T)`,** then no Weil-positive system keeps all but `o(T)` of Λ's critical atoms.

## Scope and limits
- The bound is linear in `T`, while `N(T) ∼ (T/2π)log T`. It forces modifications at relative density only `≫ 1/log T`. Reaching `T log T` would need the weighted means `mean(f·P)` with `P ≥ 0` a trigonometric polynomial in `log ℚ_{>0}`. Those bring Landau–Gonek sums `Σ_γ x^{iγ}`, which is the discrete-moment regime of the companion card.
- The law uses no arithmetic of `lam` beyond integer support (almost periodicity), and nothing about ζ beyond Hadamard and Weil's explicit formula.

## Gates
- [x] 0 → 1 in-progress: well-posed, proof idea (Herglotz lower envelope + Bohr mean)
- [x] 1 → 2 fully-proven: proof above; cited inputs are Bochner–Schwartz, Hadamard product, Bohr almost-periodicity, Weil explicit formula normalization
- [x] 2 → 3 formalized (2026-10-01, MUST-643 + counting module below). Earlier note: the Bohr-mean step and the Poisson counting are elementary. The Herglotz dictionary needs Bochner–Schwartz, which is not in mathlib. A Lean version can take `Re Φ_lam ≥ 0` on `Re s > ½` as the definition of the cone, which is equivalent by step 1.
- [ ] 3 → 4 publication-ready

## Log
- 2026-09-29 — created directly at stage 2 from L126 (paper proof complete).

## Extension analysis: from linear density to a positive proportion (2026-09-29, L127)
- **Mass lemma (proved).** For every Weil-positive `lam`, `(μ/2)([0,T]) = πN(T) + O(log T)`.
  - At `σ = 2`, `∫_0^T Re D(2+it)dt = Σ lam(n)n^{−2}sin(T log n)/log n = O(1)` for both `lam` and Λ. So `∫_0^T Re Φ_lam(2+it) − ∫_0^T Re ξ'/ξ(2+it) = O(1)`.
  - Both sides are Poisson integrals at width 3/2 of measures with `O(log T)` local mass. So the endpoint leakage is `O(log T)`.
  - Consequently `(μ/2)([T,T+1]) = O(log T)`: the atoms `c_ρ` are `O(log T)`.
- **Near-line envelope (proved).** At `σ_T = ½ + a/log T`, `−D_w = Φ_lam − ξ'/ξ` holds exactly, and:
  - `∫_0^T Re(−D_w)(σ_T+it)dt = 2πN(σ_T,T) + O(log T)`. Zeros right of `σ_T` flip the sign of their Poisson mass.
  - The lower envelope gives `∫_0^T |Re D_w(σ_T+i·)| ≤ 2π(3N_off⁺ + R⁺) + O(log T)`.
- **What a positive-proportion law needs.** A lower bound `∫_0^T |Re D_w(σ_T+i·)| ≫ T log T` whenever `w` has prime mass `Σ_{n≤T^η} w(n)²/n ≫ log²T`.
  - The coefficient-pairing side works. Residues at off-line zeros are controlled by the large sieve over `O(log T)` well-spaced subfamilies, with error `≪ T log^{3/2}T`.
  - The obstruction is converting the L² lower bound into L¹. That needs a pointwise or high-moment upper bound on `Re Φ_lam(σ_T+it)`.
  - For Λ this is Selberg–Tsang moment control of local zero counts. For a general `lam` it requires a domination hypothesis `μ_lam/2 ≤ C(πΣm_ρδ_γ + log(2+|t|)dt)`.
- **Conditional statement [P-sketch].** Under that domination hypothesis, `3N_off⁺(T) + R⁺(T) ≥ c(C,δ,η)·T log T`. Unconditionally, only the linear law above is proved.
- **Verdict:** the unconditional positive-proportion law is blocked exactly by the missing upper control of the Weil measure of `lam` at scale `1/log T`. Positivity gives lower control only.

## Lean (2026-09-29)
- The averaging step (proof steps 3–5) is formalized as an abstract theorem: `RHTower.abs_le_four_mul_of_logCosSeries_envelope`, in module `RHTower/CosineSeriesBohrEnvelope`, wired into `RHTower.lean`.
  - Hypotheses: a cosine series `Σ a_n cos(t log n)` with `Σ|a_n| < ∞` and `a_0 = a_1 = 0`, bounded below on `[8,∞)` by `−ε` with `ε ≥ 0` of Cesàro mean `E`.
  - Conclusion: `|a_m| ≤ 4E` for every `m ≥ 2`.
  - Supporting lemma: `tendsto_mean_logCosSeries_mul_cos` (Bohr coefficients via dominated convergence and Tannery). Axioms `[propext, Classical.choice, Quot.sound]`.
- With `a_n = −w(n)n^{−σ}` and `E = π(2N_off⁺ + R⁺)`-density this is exactly `(2N_off⁺ + R⁺)/T ≥ |w(n)|n^{−σ}/(4π)`. The Herglotz dictionary (step 1) and the Poisson counting (step 4) remain paper-only; they need Bochner–Schwartz and the Hadamard product.

## Lean (2026-10-01, MC loop cycle 202): envelope law formal (MUST-643)
- Module `formal/GaloisForLFunctions/RHTower/WeilConeSingularDeficitEnvelope.lean` (namespace `RHTower.WeilSpectral`). It is built on the Herglotz bridge (MUST-639/640: the boundary measure `μ_lam` exists for every full-cone producer).
- `abs_sub_vonMangoldt_le_of_envelope`: proof steps 1–3 and 5, with the deficit weights read off from the atoms of `μ_lam`.
- `eq_vonMangoldt_of_envelope_mean_tendsto_zero`: Corollary (A) in envelope form.
- **(Closed the same day, see the next section.)** Step 4, the Poisson counting `mean_T ε_σ ≤ π(R⁺(T) + 2N_off⁺(T))/T + o(1)`. It needs the corpus local zero density (`exists_card_near_xi_zeros_le`) for the tails.

## Lean (2026-10-01, MC loop cycle 203): counting form formal; the card is at stage 3 (MUST-645)
- Module: `formal/GaloisForLFunctions/RHTower/WeilConeSingularDeficitCounting.lean`. It is wired into `RHTower.lean`, with axioms `[propext, Classical.choice, Quot.sound]`.
- **Deficit count.** `deficitCount hW T = Σ_{0<γ_q≤T} d_q` sums over the divisor copies of ξ.
  - Off-line copies have weight 1; ρ and 1−ρ̄ are both counted, giving `2N_off⁺(T)`.
  - Critical copies have weight `(1 − μ_lam({γ})/m_ρ)⁺`, giving `R⁺(T)`.
- **Main theorem** `abs_sub_vonMangoldt_le_of_deficitCount`: if `D(T)/T ≤ E + η` frequently, for every `η > 0`, then `|lam(m) − Λ(m)| ≤ 4π m E`. This is exactly the card's statement `liminf (2N_off⁺ + R⁺)/T ≥ sup_n |w(n)|/(4πn)`.
- **Corollaries.**
  - `eq_vonMangoldt_of_deficitCount`: lower density zero forces `lam = Λ`.
  - `riemannHypothesis_of_deficitCount`: lower density zero forces RH, via `riemannHypothesis_of_weilPositiveFull_of_ge`.
- **The counting step**, `integral_deficitEnvelope_le`: for `T ≥ 64` and `σ ≤ √T`,
  `∫_8^T ε_σ ≤ πD(T) + (2+4σ)√T(½log T + C_σ)`.
  - Each Poisson term has `t`-mass `≤ π` (arctan antiderivative).
  - With `H = √T`, the far copies are dominated by `(2σ/(H−1))·Re ξ'/ξ(H+it)`.
  - The near-but-outside copies only matter for `t` within `H` of the ends.
  - `Re ξ'/ξ(σ'+it) ≤ ½log T + C_σ` comes from the corpus Stirling bound `re_digamma_vertical_bound_uncond`.
  - No zero-counting lemma is needed: the Hadamard sum at abscissa `H` does the counting.
- The paper's σ ↓ 1 step is done by continuity of `m^{−σ}`.

## Lean (2026-10-01, cycle 208): unit-scale upper control of `μ_lam` (MUST-648)
- `WeilFullConeLocalMassBound.exists_boundaryMeasure_Icc_le_log` gives `μ_lam([t−1,t+1]) ≤ C log(|t|+3)` for every full-cone producer. This formalizes the unit-scale half of the L127 mass lemma. The positive-proportion extension still needs the same bound at scale `1/log T`, which positivity does not give.

## Lean (2026-10-01, cycle 222): exact Poisson counting identity (MUST-656)
- `WeilFullConePoissonCountingIdentity.poissonCount_sub_eq`: the Poisson-smoothed (width 3/2) spectral count of `μ_lam` minus the Poisson-smoothed zero count of ξ (abscissa 2) equals `Σ(Λ−lam)(n)n^{−2}sin(T log n)/log n` exactly.
- This sharpens L127's mass lemma (`πN(T) + O(log T)`) to an exact identity with an `O(1)` almost-periodic error.
- Consequence for the deficit law: zero-atom removal (`R⁺`) is compensated, within `O(1)` in Poisson-smoothed counts, by mass created elsewhere. This is L269's mean balance in exact form.
