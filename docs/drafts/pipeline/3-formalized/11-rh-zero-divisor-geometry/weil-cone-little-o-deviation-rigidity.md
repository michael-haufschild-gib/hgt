# Weil-cone rigidity for prime-supported `o(Λ)` deviations (evaporation exclusion)

- **ID:** weil-cone-prime-small-deviation
- **Stage:** 3-formalized (MC loop cycle 177; MUST-599; proved for all `o(Λ)` deviations)
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

## Result (stage 3, MUST-599)
- **Proved and formalized, in general form.** A full-cone Weil-positive `lam` with `lam − Λ = o(Λ)` equals `Λ`. The prime-supported conjecture is a special case.
- The fibre argument needs no prime support. Every non-fibre term with `n > y` is composite and is bounded by `Σ_{n>y, n composite} Λ(n)/n → 0`.
- Corollaries:
  - `…_of_bounded_prime_deviation`: `lam = Λ` off the primes and `|lam(p) − log p| ≤ C` imply `lam = Λ`.
  - `riemannHypothesis_iff_exists_weilPositiveFull_isLittleO`.
- **Paper proof as formalized:**
  1. *Truncated diagonal (R1).* `‖𝒟_L(N) − T_L(N)‖ ≤ 2LC`, with `T_L(N) = ω̂(0)½log⁺(L/N) + ∫ω½log⁺(t²/(LN))`. For `N ≤ L/4`, `T_L(N) = ∫ω log t − ω̂(0) log N`, and `|T_L(N)| ≤ 4L·½log⁺(25L/(4N))` for all `N`.
  2. *Refined envelope (R2).* `‖M_L(log n) − 1_{K₀n≤L/4} mW(n) e_P (∫ω log t − ω̂(0) log n)‖ ≤ D (L n^{−½} + √L log L 1_{n≤2K₀³L} + L^{5/2}((L/8)^{−K} + e^{−L²/128}) + L²e^{−L²/32})`.
  3. *Scale identities.* `ŵ_u(0) = u β₀` and `∫ω_u log t = u(β₀ log u + β₁)`, so the main term is `u(β₀(log u − log n) + β₁)`.
  4. *Ramp.* If `|S(k)| ≤ B` and `S(k) ≥ c ≥ 0` for `k ≥ T`, then `Σ_{n≤min(N, u/4K₀)} a(n)(β₀ log(u/n) + β₁) ≥ β₀ c log u − C`, uniformly in `N ≥ T` and `u ≥ 1`. This is Abel summation, `Σ_{n≤M} a(n) log(M/n) = Σ_{k<M} S(k) log((k+1)/k)`.
  5. *Convergence.* `Σ_{n<N} d(n)/n` converges. Write `I Σ_{N≤n<N'} d/n = ∫_{log N}^{log N'} W + Σ (d/n)(e(log n − X) − e(log n − X'))`. Here the windows `|W(L)| ≤ C/L²` (window pinning + smoothed PNT), and the edges cost `I η (2log4 + 16) e^{1/2}` by the square-root Chebyshev bound.
  6. *Scale inequality.* The shifted-pole pairing (`Σ|d| n^{−5/4} < ∞`), the tail `Csh(1+L) Σ_{n>N}|d|n^{−3/2} ≤ Csh η C_T`, the defect `Cdf/(2+L) Σ_{n≤N}|d|/√n ≤ Cdf(A + 2ηC)` and the Gaussian scale mixture give `κ log(L − 1) ≤ C_η + η K log(L − 1)`. Taking `η = κ/(2(K+1))` contradicts `Y > 0`.
  7. *Fibre.* For `y ≥ max(n₀, P₀(1), Cauchy index, τ-index)` and `M ≥ y`, `|S(M) − εv(n₀) − 2Σ_{y<n≤M} v(n)/√n| ≤ (2 + √n₀) τ(y)`. So `εv(n₀) ≤ (4 + √n₀) δ` for both signs.
- **Lean modules** (all under `formal/GaloisForLFunctions/RHTower/`; wired into `RHTower.lean`; standard axioms only):
  - `ZetaNotchTruncatedDiagonal` (R1);
  - `ZetaNotchRefinedEnvelope` (R2);
  - `PrimeSmallDeviationArithmetic`: Mertens, square-root Chebyshev and dyadic `n^{−3/2}` tail sizes of `o(Λ)` deviations;
  - `WeilLittleODeviationHarmonicConvergence` (step 5);
  - `ZetaNotchRampMainTerm` (steps 3–4, the ramp mixture, the refined error integral);
  - `WeilLittleOVonMangoldtRigidity` (steps 6–7 and the corollaries).
- **Novelty/significance audit.**
  - The literature has no Weil-cone uniqueness results; the corpus results are MUST-534/571/576/584/586/588/591 and HF L155–L163.
  - The theorem removes every prime-power-supported deviation of relative size `o(1)`, including bounded prime deviations `|a(p)| ≍ 1` with arbitrary signs. These are L155's uniform-evaporation model `w ≈ Λ/log n`; the corpus had recorded that model as open (L163: "evaporation needs `≍ N/log N`"), and only its one-signed case was killed (MUST-586).
  - **Correction to the Phase 1–4 framing.** HF's pinned continuous-producer profile (L201: deficit `1/(4π)` per prime, mass restored by a Cramér density `(1/4π)/log n` on all `n`) and HF's survivor 3 in the form `D = r·ν_Λ − μ₀` (L206) carry a composite part that is not `o(Λ)`. They are **not** covered; the Cramér-density part is the next obstruction.
  - It is the first exclusion that does not rely on any summability of `|d|` against `1/n`, the first that uses a conditionally convergent series, and the first where `log n` sits in the main term.
- **Boundary.** The method stops at `d ≍ Λ`: `Σ_{n≤L²} |d(n)|/n ≍ log L` then competes with the main term. This is the α = 1 wall in Weil-cone form. The next target is the `η K log L` coefficient for `d = O(Λ)` with oscillating sign: a signed version of Step 6 in which `Σ d(n)/n` convergence controls the error sum, not `Σ|d|/n`.
