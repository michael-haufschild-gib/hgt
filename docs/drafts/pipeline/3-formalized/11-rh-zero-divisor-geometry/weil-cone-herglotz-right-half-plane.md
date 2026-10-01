# Full-cone Weil positivity is Herglotz positivity on `Re s > 1`

- **ID:** MC-199
- **Stage:** 3-formalized (MUST-639)
- **Type:** THEOREM [L]
- **Source:** MC loop cycle 199. Stage 1 of the bridge `WeilPositiveFull ⇒ HerglotzWeilPositive`; `HerglotzWeilPositive` is a hypothesis structure in `WeilPositiveShortIntervalSupport`, used by three modules.

## Statement
For `lam : ℕ → ℝ` put `Φ_lam(s) = ½ψ(s/2) − ½ log π + 1/s + 1/(s−1) − Σ_{n≥2} lam(n) n^{−s}` (`weilFunction`). If `lam` is full-cone Weil-positive, then `Re Φ_lam(s) ≥ 0` for all `s` with `Re s > 1` (`re_weilFunction_nonneg`).

## Proof
Write `s = ½ + w`, `w = b + it`, `b > ½`.
1. **Tests.** `h_j = ρ_j ⋆ (e^{−wu}1_{[0,j+1]})`, with `ρ_j` the normalised `ContDiffBump` of radius `1/(j+1)`. These are `C^∞` with compact support, so `Re W_lam(h_j ⋆ h̃_j) ≥ 0`.
2. **Transforms.** `ĥ_j = ρ̂_j · ĝ_j`, where `ĝ_j(z) = (1 − e^{−(w−iz)(j+1)})/(w − iz)` and `ρ̂_j → 1` pointwise. For real `r`: `|ρ̂_j(r)| ≤ 1` and `|ĝ_j(r)| ≤ 2/|w − ir|`.
3. **Pole part.** By `paperFT_weilTest` at `±i/2`, it tends to `A·conj B + B·conj A`, with `A = 1/s` and `B = 1/(s−1)`. This needs `Re(w − ½) > 0`, i.e. `b > ½`. Since `A + conj B = 2b·A·conj B`, its real part is `Re(A + B)/b`.
4. **Prime part.**
   - Majorant: `|h_j(u)| ≤ e^{b}e^{−bu}1_{u≥−1}`. Hence `|K_j(x)| ≤ C e^{−b|x|}`, and the prime sum is dominated by `Σ|lam(n)|n^{−Re s}`, which converges on the Weil cone (`summable_abs_div_rpow_of_weilPositiveFull`).
   - Pointwise: `h_j → e^{−wu}1_{u>0}` off `0`.
   - Closed form of the limit autocorrelation: `K(x) = e^{w̄x}e^{−2b max(0,x)}/(2b)`.
   - Hence `λ(n)n^{−½}(K(log n) + K(−log n)) = Re(λ(n)n^{−s})/b`.
5. **Archimedean part.**
   - Dominated by `4|γ(r)|/|w − ir|² = (4π/b) P_b(r−t)|γ(r)|`.
   - The limit is `(1/2b)∫P_b(r − t)γ(r) dr`.
   - **Shifted reproduction identity** (new module): `∫P_a(x − t) Re ψ(c + ix/2) dx = Re ψ(c + a/2 + it/2)`. Proof: integrate the Gauss series termwise; the Poisson semigroup `P_a ∗ P_B = P_{a+B}` evaluates each summand, and the summands' Poisson masses are `O(n⁻²)`.
   - With `c = ¼` this gives `(Re ψ(s/2) − log π)/(2b)`.
6. **Conclusion.** The limit of the nonnegative real parts is `Re Φ_lam(s)/b`.

## Scope and novelty
- **Not new mathematics.** For `Λ` it is `Re ξ'/ξ > 0` on `Re s > 1`. For a general producer it is the easy half of the Bochner–Schwartz/Herglotz dictionary (HF L224 Lemma B uses its `Re s > ½` version).
- **What is new in the corpus.**
  - The statement is now formal and hypothesis-free for the whole Weil cone.
  - The shifted digamma–Poisson identity: the corpus had only the centre `t = 0`.
  - The pole-point budget (L221) is the `s → 1⁺`, `t = 0` edge.
- **Next (stage 2).** Use Bochner (`HTGeometry.exists_charFun_eq_of_positiveDefinite`) on the mollified Weil distributions `y ↦ W_lam(τ_y(χ⋆χ̃))`. Glue the measures `ν_χ = |χ̂|²μ` into the boundary measure `μ_lam`. Then the Herglotz integral of `μ_lam` continues `Φ_lam` to `Re s > ½`, which gives `HerglotzWeilPositive` on `W`.

## Lean
- `formal/GaloisForLFunctions/RHTower/WeilFullConeHerglotzRightHalfPlane.lean` (namespace `RHTower.WeilHerglotz`).
- `formal/GaloisForLFunctions/RHTower/PoissonDigammaShiftedReproduction.lean`.
- Axioms `[propext, Classical.choice, Quot.sound]`. Both modules are wired into `RHTower.lean`.

## Stages 2–3: the full bridge (MUST-640, Lean)
- **Theorem.** `WeilPositiveFull lam ⇒ HerglotzWeilPositive (lam·1_{n≥2}) zetaArchimedeanDatum` (`herglotzWeilPositive_of_weilPositiveFull`).
- **Stage 2: boundary measure.**
  - `F_f(y) = W_lam(τ_y(f⋆f̃))` is continuous and positive definite. The proof uses the Gram identity for translates, linearity on admissible tests, and Hermitian symmetry `W(k̃) = conj W(k)`. Corpus Bochner then gives a finite `ν_f`.
  - Consistency `|ĝ|²ν_f = |f̂|²ν_g`: both sides have the characteristic function `W_lam(∫(g⋆g̃)(u)(f⋆f̃)(·−y−u)du)`, which is symmetric in `f, g`. This rests on `W` commuting with averages: piece by piece, Fubini for the pole and archimedean parts, a finite sum for the prime part.
  - `μ_lam := Σ_j |ρ̂_j|⁻²ν_{ρ_j}|_{S_j}` over the shells `S_j = {j/4 ≤ |r| < (j+1)/4}`, where `|ρ̂_j| ≥ ½`. Then `ν_f = |f̂|²μ_lam` for every test.
- **Stage 3: Herglotz function.**
  - Poisson representation on `Re s > 1` via the stage-1 tests: Fatou, then dominated convergence with majorant `4|w − ir|⁻²`.
  - `H(z) = ∫(1/(z−ir) − ir/(1+r²))dμ_lam` is holomorphic on `Re z > 0`, with a kernel bound `O((1+r²)⁻¹)` locally uniform in `z`, and `Re H ≥ 0`.
  - `Φ_lam − H(·−½)` has zero real part on the convex set `Re s > 1`, hence is constant. The continuation is `H(s−½) + const`.
- **Corollary.** `exists_prime_mem_Ioo_of_weilPositiveFull`: a prime-supported `lam ∈ W` forces primes in `(x, x+x^{½+ε})`.
- **Scope.** Classical (Bochner–Schwartz + Herglotz) for distributions in general. New here as a formal, hypothesis-free statement on the integer Weil cone. It discharges the hypothesis of every `HerglotzWeilPositive`-conditional corpus theorem.
- **Further corollaries** (module `WeilFullConeShortIntervalConsequences`):
  - `exists_weight_ne_zero_mem_Ioo_of_weilPositiveFull`: the support of every full-cone producer meets every interval `(x, x + x^{½+ε})`.
  - `volume_primeGapStarts_le_of_weilPositiveFull`: a prime-supported producer has primes in almost all windows of length `X^ε`, with exceptional measure `O(X^{−ε/2})`.
