# Weil-cone rigidity for prime-supported `o(Λ)` deviations (evaporation exclusion)

- **ID:** weil-cone-prime-small-deviation
- **Stage:** 1-in-progress (MC loop cycle 177)
- **Conjecture 177.** Let `lam` be full-cone Weil-positive with:
  - `lam(n) = Λ(n)` for every non-prime `n ≥ 2`;
  - `|lam(p) − log p| = o(log p)` as `p → ∞`.

  Then `lam = Λ`.
  - In particular, bounded prime deviations `|lam(p) − log p| ≤ C` are excluded. This is HF's uniform-evaporation class (`w ≈ Λ/log n`, `|a(p)| ≍ 1`, krein-producer-loops L155/L163), which the corpus left open.

## Phase 1–2 (corpus audit)
- **Excluded so far:**
  - `Σ|d|/n < ∞` (MUST-584);
  - one-sided summability (MUST-586);
  - a thin prime deficit set (MUST-588);
  - pointwise `n^{−½}` polylog size (HF L162);
  - polylog square mass (HF L163);
  - lacunary and dyadic supports (L158/159).
- **Not excluded:** bounded prime deviations with random-like signs. For those, `Σ_{p≤x}|d(p)|/p ≍ log log x` diverges, the square mass is `≍ x/log x`, and every sign set is dense.
- HF (L163) records "evaporation needs `≍ N/log N`", i.e. that this class is open, and that "only local (non-`B²`) structure of `D_w` near the zeros can exclude them". The notch pairing is exactly such a local test.

## Phase 3–4 (why the notch should work here, and the kill attempt)
- **What blocked MUST-584 beyond `Σ|d|/n < ∞`.** The error weight `(1 + log n) n^{−½}` comes from the diagonal law, which uses the crude bound `‖𝒟_L(N) − (∫ω log t − ω̂(0) log N)‖ ≤ 2L(C + log N)`.
- **Refinement.**
  - In the regime `N ≤ X` the direct and dual diagonal sums are `½ log(X/N) + O(1)`. For `N > X` they are `O(X/N)`.
  - Hence `𝒟_L(N) = ∫ ω(t)[½ log⁺(L/N) + ½ log⁺(t²/(LN))] dt + O(L)`, uniformly in `N`.
  - The `−ω̂(0) log N` is therefore a main term with a Riesz structure, not an error.
- **With the refined diagonal:**
  - the per-`n` remainder is `O(L n^{−½} + √L log L · 1_{n ≤ cL} + tiny)`, with no `log n`;
  - the per-scale main term is `e_P ω̂(0) Σ_n v(n) mW(n) K_L(log n)`, with a ramp kernel `K_L(x) ≈ (log L − x + c)⁺`.
- **Prime-supported `d` with `d(p) = o(log p)`:**
  - *Errors.* `L Σ_{p≤L²}|d(p)|/p = o(L log L)`, by Mertens. Also `√L log L Σ_{p≤cL}|d(p)|p^{−½} = o(L log L)`, by Chebyshev.
  - *Main term.* `Σ_p (d(p)/p)(log L − log p)⁺ = Y log L + o(log L)`, provided the sharp partial sums `S(x) = Σ_{p≤x} d(p)/p` converge.
  - *Convergence of `S(x)`.* It follows from MUST-586's window law, since `∫|W| < ∞` gives convergence of the smoothed sums, together with local smallness: `Σ_{p∈[x,ex]} |d(p)|/p = o(1)`, by Mertens. Then `S'(x) = Σ_{p≤x} d(p) log p/p = o(log x)`.
  - *Fibre main term.* `Y_{P,ε,n₀} = (1+ε²) Σ_{p∉P} d(p)/p + ε d(n₀)/√n₀`.
  - *Conclusion.* The pairing gives `Y ≤ 0`. Letting `P ↑` makes the tail vanish, so `±ε d(n₀) ≤ 0` and `d(n₀) = 0`.
- **Kill attempt.**
  1. The α ≥ 1 wall enters only through `Σ_{n∈[L, L²]}|d|/n`. That is `o(log L)` here, because `d` is `o(Λ)`. For `Λ`-size `d` it is `≍ log L`, so the conjecture stops exactly at Ω. It is not implausibly strong.
  2. *Circular?* No.
  3. *Implied by the corpus?* No; the list above shows it is outside every excluded class.
  4. *Insignificant?* No. It removes HF's uniform-evaporation core.
- **Verdict.** SURVIVES; proof in progress.

## Phase 5 (paper proof, dependency list)
1. **Refined diagonal law.** For `N ≥ 1`, `‖𝒟_L(N) − T_L(N)‖ ≤ 2L C`, where `T_L(N) = ω̂(0) ½ log⁺(L/N) + ∫ ω ½ log⁺(t²/(LN))`. For `N ≤ L/4`, `T_L(N) = ∫ω log t − ω̂(0) log N`; for `N ≥ 25L/4`, `T_L(N) = 0`.
2. **Refined twist envelope.** `‖M_L(log h − log k) − (hk)^{−½} T_L(hk)‖ ≤ (hk)^{−½} 2LC + C'(near + far + small + tail)`.
3. **Mode sum.** `‖M_L^q(log n) − 1_{n ≤ L/c₂} mW(n) e_P (∫ω log t − ω̂(0) log n)‖ ≤ D (L n^{−½} + √L log L · 1_{n ≤ cL} + T_L + Z_L)`.
4. **Pairing and tail.** Use the shifted-pole pairing (MUST-584) with `Σ|v|n^{−¾} < ∞`, the tail `(1+L)/n`, and the defect `C/(2+L)`.
5. **Mixture.** The Gaussian mixture concentrates at `u ≈ L`. The per-scale error is `o(u log u)`, and the main term is `Y_{N} e_P 2e^{−1} log(L−1) + o(log L)`.
6. **Arithmetic inputs.**
   - Window `L¹` law, from pinning + PNT, for all real `L`.
   - Local smallness and harmonic `o(log x)`, from Mertens `Σ_{n≤x} Λ(n)/n ≤ log x + C`.
   - Chebyshev `Σ_{n≤x} Λ(n) n^{−½} ≤ C√x`.
7. **Fibre limit** for prime support, as above.

## Lean plan
- **R1** `ZetaNotchTruncatedDiagonal`: step 1.
- **R2** `ZetaNotchRefinedEnvelope`: steps 2–3.
- **R3** `WeilPrimeSmallDeviationRigidity`: steps 4–7.
