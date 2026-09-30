# Weil-cone rigidity under one-sided convergence at `s = 1`

- **ID:** weil-cone-one-sided-convergence
- **Stage:** 3-formalized (MUST-586)
- **Source:** MC conjecture loop, cycle 172. It strengthens MUST-584 (`weil-cone-absolute-convergence-rigidity.md`) and the one-sided `1/√n` results (summable excess/deficit, MUST-532 lineage).
- **Theorem.** Let `lam` be full-cone Weil-positive.
  - If `Σ_n max(lam(n) − Λ(n), 0)/n < ∞`, then `lam(n) = Λ(n)` for all `n ≥ 2`.
  - If `Σ_n max(Λ(n) − lam(n), 0)/n < ∞`, then `lam(n) = Λ(n)` for all `n ≥ 2`.
- **Positive law exposed** (`exists_profile_summable_windows`). There is a single profile `φ ≥ 0`, bounded, supported in `[−½, ½]` and `≥ c₀ > 0` near `0`, with a step `δ > 0`, such that for every cone member the harmonic unit-scale windows `W_k = Σ_n d(n) φ(log n − kδ)/n` of `d = lam − Λ` satisfy `Σ_k |W_k| < ∞`.

## Phase 1–4
- **Starting point.** MUST-584 closed the absolute side at `s = 1`. The corpus already had one-sided rigidity at weight `1/√n`, and the minorant, majorant and eventual-sign cases.
- **Question.** Can one sign of the deviation be summable at `1/n` while the other is not?
- **Mechanism.**
  - Window pinning (MUST-534) puts every cone member's log-windows within `O(1)` of `2P₊P₋ cosh(L/2)`.
  - The de la Vallée Poussin error term puts `Λ`'s windows within `O(e^{L/2}e^{−c√L})` of the same value.
  - So the harmonic windows of `d` are `O(e^{−L/2} + e^{−c√L})`, which is summable along any arithmetic progression of `L`.
  - A nonnegative covering profile then converts `Σd⁺/n < ∞` into `Σd⁻/n < ∞`.
- **Kill attempts.**
  1. *False?* No. The argument uses only pinning and an unconditional PNT error term that is integrable in `L`; any saving `(log x)^{−1−ε}` would do.
  2. *Circular?* No. `Λ ∈ C` is never used; the PNT enters only through `Λ`'s own windows.
  3. *Implied by the corpus?* It strictly contains:
     - MUST-584, since `|d| = d⁺ + d⁻`;
     - the summable excess and deficit results at `1/√n`, since `1/n ≤ 1/√n`;
     - the minorant, majorant and eventual-sign rigidities, since a finitely supported `d⁻` is summable.
     No stronger statement was found in a search of the corpus.
  4. *Insignificant?* It is a unification plus a strengthening. It does not touch the Ω core.
- **Verdict.** SURVIVES as a sharpening. The honest scope: the (P2) class is now "`d⁺/n` and `d⁻/n` are both non-summable, while the unit-window masses `W_k` are absolutely summable".

## Phase 5 — paper proof
1. **Smoothed PNT** (`exists_abs_windowSum_vonMangoldt_sub_le`). For `L ≥ 1` the window is `w(n) = G(log n)` with `G(u) = e^{−u/2}ρ(u − L)`.
   - *Primes.* Put `E(N) = Σ_{n≤N}Λ(n) − N`. Summation by parts gives `Σ_{n<M}(Λ(n+1) − 1)w(n+1) = −Σ_{n<M}E(n)(w(n+1) − w(n))`, because `w(M) = 0` and `E(0) = 0`.
     - A difference is nonzero only for `n ≥ 1` with `log n ≥ L − 3/2`.
     - There `|w(n+1) − w(n)| ≤ e^{−log n/2}(K+H)/n` (Lipschitz bound of `G` on `[log n, ∞)`), and `|E(n)| ≤ B n e^{−√(log n)/960000}` for `n ≥ N₀`.
     - With `M ≤ 2e^{L+1}` terms, the total is `≤ 2e^{7/4}B(K+H) e^{L/2} e^{−√L/1920000}` for `L ≥ 3`.
   - *Integers.* `|w(n+1) − ∫_{n+1}^{n+2}G(log x)dx| ≤ (K+H)e^{−3(L−3/2)/2}`, and this vanishes unless `log(n+1) ≥ L − 3/2`. Summed, the error is `≤ 2e^{13/4}(K+H)`.
     - The substitution `x = e^u` gives `∫_1^{M+1} G(log x)dx = ∫ e^{u/2}ρ(u−L)du = e^{L/2}∫ρ(v)e^{v/2}dv`.
     - Finally `∫ρ(v)e^{v/2}dv = P₊P₋`, the Fourier factorization `\widehat{g⋆g̃}(−i/2) = ĝ(−i/2)·conj(ĝ(i/2))`.
   - *Cosh.* `2P₊P₋cosh(L/2) − e^{L/2}P₊P₋ = P₊P₋e^{−L/2}`.
2. **Windows of `d`.** With `φ(x) = ρ(x)e^{x/2}` and `L ≥ 1`, `e^{−L/2}w_L(n) = φ(log n − L)/n`. So `W(L) = e^{−L/2}(S_L(lam) − S_L(Λ))`. By pinning and step 1, `|W(L)| ≤ C(e^{−L/2} + e^{−√L/1920000})`. Along `L = kδ` this is `≤ C e^{−kδ/2} + C e^{−(√δ/1920000)√k}`, which is summable.
3. **Transfer** (`summable_abs_div_of_windows`).
   - Take `g ≥ 0` (the narrow bump), so `φ ≥ 0` and `φ(0) = ρ(0) > 0`. Continuity gives `φ ≥ c₀` on `[−δ/2, δ/2]`.
   - For `1 ≤ n < N`, the index `k₀ = ⌊log n/δ + ½⌋ < K` has `|log n − k₀δ| ≤ δ/2`. Hence `d⁻(n)/n ≤ c₀^{−1} Σ_{k<K} d⁻(n)φ(log n − kδ)/n`.
   - Swap the sums and enlarge `n < N` to `n < N*`, with `N*` covering every window. Then use `d⁻ = d⁺ − d` in each window and the covering count `Σ_k φ(u − kδ) ≤ H(⌊1/δ⌋ + 1)`:
     `Σ_{n<N} d⁻(n)/n ≤ c₀^{−1}(H(⌊1/δ⌋+1)Σ d⁺/n + Σ_k |W_k|)`.
   - So `Σ d⁻/n < ∞` and `Σ|d|/n < ∞`.
4. **Conclusion.** MUST-584 gives `lam = Λ` on `n ≥ 2`. The deficit case applies step 3 to `−d`. ∎

## Lean (formalized 2026-09-30)
Audit: both modules compile clean under `lake env lean`, the build used `lake build --old`, `#print axioms` reports the standard three, both are wired into `RHTower.lean` after `WeilAbsoluteConvergenceRigidity`, and the name-collision sweep is clean. Three names that clashed with `WeilShiftPairLandau` and `MertensSecondTheorem` were renamed.
- `LogWindowPrimeNumberTheorem`:
  - `windowSum_eq_sum`, `windowSum_sub`;
  - `abs_autoCorr_sub_le`, `continuous_autoCorr`, `exists_autoCorr_constants`, `integral_autoCorr_mul_exp_half`;
  - `logWindow`, `windowValue_eq_logWindow`, `abs_expWindow_sub_le`;
  - `sum_range_sub_mul_eq`, `psiRemainderNat`, `exists_abs_psiRemainderNat_le`;
  - `abs_sum_vonMangoldt_sub_one_mul_logWindow_le`, `integral_logWindow_log_eq`, `abs_sum_logWindow_sub_integral_le`;
  - `exists_abs_windowSum_vonMangoldt_sub_le`.
- `WeilOneSidedConvergenceRigidity`:
  - `sum_range_profile_eq`, `sum_range_profile_le`, `summable_abs_div_of_windows`;
  - `harmonicProfile`, `sum_harmonicProfile_eq_windowSum`, `exists_abs_windowSum_sub_vonMangoldt_le`, `exists_profile_summable_windows`;
  - `summable_abs_sub_div_of_one_sided`;
  - `eq_vonMangoldt_of_weilPositiveFull_of_summable_excess_div`, `eq_vonMangoldt_of_weilPositiveFull_of_summable_deficit_div`.

## Significance
- **(P2) at `s = 1` is now closed on each side separately.** A second cone point must have both its excess and its deficit over `Λ` non-summable against `1/n`. This single statement subsumes the absolute, `1/√n`-one-sided, minorant, majorant and eventual-sign rigidities.
- **The remaining class is sharply described.** `d` has absolutely summable harmonic unit-window masses, yet `Σ d⁺/n = Σ d⁻/n = ∞`. So `d` must change sign inside unit log-windows, cancelling at scale `O(1)` in `log n` while the absolute `1/n`-mass diverges. HF's Ω deviations are of exactly this sign-oscillating type.
- **Next target.** Show that sign oscillation below unit log-scale is incompatible with positive definiteness of `−ψ_v`. The notch moments `M(log n)` oscillate at log-scale `1/L`, so the needed input is a fine-scale (width `1/L`) window bound for cone members, strictly stronger than pinning at unit scale.

## Addenda (after formalization)
- **RH criteria [L].**
  - `riemannHypothesis_iff_exists_weilPositiveFull_summable_excess_div`: RH ⟺ some full-cone Weil-positive `lam` has `Σ max(lam − Λ, 0)/n < ∞`.
  - `riemannHypothesis_iff_exists_weilPositiveFull_summable_deficit_div`: the same with `Σ max(Λ − lam, 0)/n < ∞`.
  - Both strengthen the `1/√n` criterion `riemannHypothesis_iff_exists_weilPositiveFull_summable_deficit`.
- **Honest novelty note: a shorter route via Landau.** If one grants the Herglotz continuation of `A_lam` for cone members (paper-level in HF L80, not in Lean), MUST-586 also follows from MUST-584 by Landau's theorem:
  - `D = A_lam − A_Λ` is analytic at `s = 1`, because the poles cancel.
  - Hence `D⁺ = D + D⁻` has abscissa `≤ 1`.
  - By monotone convergence, `Σd⁺/n = D(1) + D⁻(1) < ∞`.

  The Lean proof above avoids the Herglotz continuation entirely, using only pinning and the dlVP error term. So MUST-586 is a Tauberian corollary of MUST-584, not an independent structural law.
- **What the cycle learned about the core.** The notch main term `Y = Σ v·mainWeight` is an Euler-fibre functional: `mainWeight` carries the indicator "P-part of `n` equals `1` or `n₀`" times `n^{−1/2}`, so it is multiplicative-residue data, not log-smooth. Window laws of every scale control only log-smooth functionals of `d/n`.
  - Consequence: no window law closes (P2). The residual class is exactly where the Euler-fibre (non-archimedean) and log-window (archimedean) descriptions of `d/n` disagree.
  - The spectral twin, "sublinear zero removal `Σ_{γ≤T} r_γ = o(T)` forces `lam = Λ`", is already HF L-(5) (Bohr mean argument), so it is REDISCOVERED and was not re-formalized.
- **Sign-set density [L].** Combine MUST-586 with the box `|lam(n) − Λ(n)| ≤ √n(2 log n + C)`:
  - `eq_vonMangoldt_of_weilPositiveFull_of_summable_excess_support`: if `Σ_{n : lam(n) > Λ(n)} (1 + log n)/√n < ∞`, then `lam = Λ`;
  - `eq_vonMangoldt_of_weilPositiveFull_of_summable_deficit_support`: the same for the set `lam(n) < Λ(n)`.
  - So both sign sets of a second cone point have divergent `√`-log mass. Any support that is sparse in this sense is excluded. This includes:
    - every `P`-smooth support for finite `P`;
    - every finite union of geometric progressions;
    - every thin set of primes with `Σ log p/√p < ∞`.
  - This unifies the finite-support (MUST-570), powers-of-two (L159) and common-ratio results as special cases, on each sign separately.
