# Producer short-interval law: every Weil-positive system carries RH-quality prime-number theory for its own weights

- **ID:** weil-producer-short-interval-law
- **Stage:** 3-formalized (Lean closed 2026-09-29)
- **Type:** THEOREM (paper + Lean, standard axioms)
- **Source:** `1-in-progress/hf-positive-hodge-attack/krein-producer-loops.md`, L148
- **Statement:** Let `lam: ℕ_{≥2} → ℝ` with `Σ|lam(n)|n^{−σ} < ∞` for `σ > 1`. Suppose `lam` is Weil-positive for an archimedean datum `A` of logarithmic growth, for example ζ's `Γ̃(s) = ½ψ(s/2+1) − ½log π`. Then:
  - (S) for every `ε > 0` and `x ≥ x₀(ε)`, every interval `(x, x + x^{½+ε})` meets `supp lam`;
  - (AA) for every `ε > 0`, all but `O(X^{1−ε/3}log²X)` of the `y ∈ [X, 2X]` have `supp lam ∩ (y, y + 2X^ε) ≠ ∅`;
  - (Q) `Σ_{n≤X} lam(n)²/n ≪ log³X·(log log X)²`;
  - (D) `#(supp lam ∩ (x, 2x)) ≫ x/(log³x (log log x)²)`.
  - Consequently, a Weil-positive system supported on the primes (or on the prime powers) forces a prime in every interval `(x, x + x^{½+ε})`, and in almost every interval `(y, y + y^ε)`.

## Goal
- **Existence side of the Weil cone (PBAP).** A positivity producer other than Λ is a free-weight system in W. This card gives rigorous, unconditional necessary conditions on the *arithmetic* of any such producer.
- They replace the heuristic statement of L119/L127 ("prime-supported producers are tied to short-interval prime distribution") with theorems.
- **Non-circularity.** Nothing about the zeros of ζ is used. The only input is the Herglotz form of Weil positivity for `lam` itself.

## Setting
- `D(s) = Σ lam(n)n^{−s}` on `σ > 1`.
- `A` is holomorphic on `H = {Re s > ½}` with `|A(s)| ≤ K log(|Im s| + 3)` on `½ < Re s ≤ 2`. ζ's datum qualifies: `s/2 + 1` has real part in `(5/4, 2]`, where `ψ(z) = log z + O(1)`.
- **Weil positivity (Herglotz form).** There is `Φ` holomorphic on `H`, with `Re Φ ≥ 0` on `H`, and `Φ = A + 1/(s−1) − D` on `σ > 1`. (For `A = Γ̃` this is `Φ_lam`; for `lam = Λ` it is `ξ'/ξ`.)
- `E := A − Φ` is holomorphic on `H`, and `E = D − 1/(s−1)` on `σ > 1`. So `D` continues to `H ∖ {1}` with a simple pole of residue 1 at `s = 1`.
- `L₂ := Σ|lam(n)|n^{−2}`.

## Proof

### Lemma H (Harnack strip bound).
For `½ < σ ≤ 2`: `|E(σ+it)| ≤ C log(|t|+3)/(σ − ½)`, with `C = 6(2K + 1 + L₂)`.
- *Proof.*
  1. Apply Borel–Carathéodory (corpus `RHTower.borel_caratheodory`) to `g = −Φ`, bound `ε > 0`, on `B(2+it, 3/2) ⊂ H`, and let `ε → 0`: `|Φ(z) − Φ(c)| ≤ 2|z−c|/(3/2 − |z−c|)·Re Φ(c)`.
  2. With `c = 2+it` and `z = σ+it` (`|z−c| = 2−σ`) this gives `|Φ(σ+it)| ≤ (1 + 3/(σ−½))|Φ(2+it)|`.
  3. Bound the right side: `|Φ(2+it)| ≤ K log(|t|+3) + 1 + L₂`. Combine with `|A(σ+it)| ≤ K log(|t|+3)` and `1 ≤ (3/2)/(σ−½)`. ∎

### Lemma P (smoothed sums).
Let `φ ∈ C_c^∞((a,b))` with `0 < a`, and let `φ̃(s) = ∫_0^∞φ(u)u^{s−1}du`. For `x ≥ 1/a` and `0 < η ≤ 3/2`:
`Σ_n lam(n)φ(n/x) = x∫φ + (1/2π)∫_ℝ E(½+η+it) φ̃(½+η+it) x^{½+η+it} dt`.
- *Proof.*
  1. Mellin inversion on `Re s = 2` and Fubini (`Σ|lam(n)|n^{−2}∫|φ̃(2+it)|dt < ∞`) give `Σ lam(n)φ(n/x) = (1/2πi)∫_{(2)}D(s)φ̃(s)x^s ds`.
  2. Split `D = E + 1/(s−1)`. The pole part: `φ̃(s)/(s−1)` is the Mellin transform of `g(u) = u^{−1}∫_u^∞φ` (for `Re s > 1`). Mellin inversion at `u = 1/x` gives `g(1/x) = x∫_{1/x}^∞φ = x∫φ`.
  3. The `E` part: `E` is holomorphic on the strip `½+η ≤ σ ≤ 2`, with `|E| ≤ C log(|t|+3)/η` there by Lemma H. `φ̃` decays faster than any power uniformly in the strip. So the horizontal edges vanish and the contour moves to `Re s = ½+η`. ∎

### Lemma M (short bumps).
Let `ψ ∈ C_c^∞((0,1))`, `ψ ≥ 0`, `∫ψ = 1`, and put `φ_δ(u) = ψ((u−1)/δ)` for `0 < δ ≤ 1`, supported in `(1, 1+δ)`.
- For `½ ≤ σ ≤ 2`: `|φ̃_δ(σ+it)| ≤ 2δ`.
- Integrating by parts twice: `φ̃_δ(s) = (s(s+1)δ)^{−1}∫_0^1ψ''(v)(1+δv)^{s+1}dv`, so `|φ̃_δ(σ+it)| ≤ 8‖ψ''‖₁/(δt²)`.
- Hence `∫_ℝ|φ̃_δ(½+η+it)| log(|t|+3) dt ≤ C_ψ log(3/δ)`.

### Theorem S (all short intervals).
Take `δ = x^{−½+ε}` and `η = ε/2`. Then `Σ_n lam(n)ψ((n−x)/x^{½+ε}) = x^{½+ε} + O_ψ(C·x^{½+ε/2} log x/ε)`. For large `x` the sum is positive, so some `n ∈ (x, x+x^{½+ε})` has `lam(n) ≠ 0`. ∎

### Theorem AA (almost all short intervals).
- Put `S(y) := Σ lam(n)φ_δ(n/y) − δy`. By Lemma P, `S(y)y^{−½−η} = (1/2π)∫G(t)y^{it}dt` with `G = E·φ̃_δ` on `Re s = ½+η`.
- Plancherel in `log y`: `∫_X^{2X}|S(y)|²dy ≤ (2X)^{2+2η}(1/2π)∫|G|² ≪ X^{2+2η}·δ log²X·C²/η²`.
- Take `δ = h/X` with `h = X^{3η}`. If `supp lam` misses `(y, y+δy)`, then `S(y) = −δy`, so `|S(y)|² ≥ h²`. The exceptional set therefore has measure `≪ X^{1−η}log²X/η² = o(X)`. With `ε = 3η`, all but `O(X^{1−ε/3}log²X)` of the `y ∈ [X,2X]` have a support point in `(y, y + δy)`, and `δy ≤ 2X^ε`. ∎

### Theorem Q (square-mass law, via Montgomery–Vaughan).
1. *Approximation.* Let `v ∈ C^∞` with `v = 1` on `[0,1]` and `v = 0` on `[2,∞)`. Then `v̂(z) = ∫v(u)u^{z−1}du` has a single simple pole at `z = 0`, with residue 1.
   - For `s = ½+η+it` and `0 < a < η`: `D(s) = Σ lam(n)v(n/X)n^{−s} − ∫_1^∞v(y/X)y^{−s}dy − R(s)`.
   - Here `R(s) = (1/2πi)∫_{(−a)}E(s+z)v̂(z)X^z dz`. This uses the same pole-splitting as Lemma P and one residue at `z = 0`.
   - The integral term is `O(X^{½}/|t|)`.
2. *Mean square of `E`.* This is a sharper, mean-square form of Lemma H.
   - The Herglotz representation `Re Φ = P_η ⋆ ν` has no linear term, since `Φ(σ) = O(log σ)`.
   - The local mass bound `ν([t−1,t+1]) ≤ 7 Re Φ(2+it) ≪ log|t|` holds.
   - `L²`-boundedness of the conjugate function gives `(1/T)∫_T^{2T}|E(½+η+it)|²dt ≪ log²T/η`, via `‖P_η⋆ν_loc‖₂² ≤ ν_loc(ℝ)·sup P_{2η}⋆ν`.
3. *Montgomery–Vaughan.* With `T = 12πX` and `a = η/2`: `½Σ_{n≤X}lam(n)²n^{−1−2η} ≤ (1/T)∫_T^{2T}|Σ lam(n)v(n/X)n^{−½−η−it}|²dt ≪ log²X/η + X^{−η}log²(1/η)log²X/η`.
4. Take `η = 1/log X`. ∎
- With only the pointwise Lemma H (no Herglotz representation), the same argument gives `log⁴X(log log X)²`.

### Theorem D (dyadic density).
- By Lemma P with `φ ∈ C_c^∞((1,2))` and `η = ¼`: `Σ lam(n)φ(n/x) = x∫φ + O(x^{3/4})`.
- Cauchy–Schwarz gives `x² ≪ #(supp ∩ (x,2x))·Σ_{(x,2x)}lam²`, and `Σ_{(x,2x)}lam² ≤ 2xΣ_{n≤2x}lam²/n`. ∎

### Corollary (prime-power support forces primes in short intervals).
- If `supp lam ⊆ {p^k}`, the powers `p^k` with `k ≥ 2` in `I = (x, x+x^{½+ε})` number `≤ x^ε`.
- By Cauchy–Schwarz and Q they contribute `≪ x^{ε/2}(x log³x)^{½}(log log x) = o(x^{½+ε})`.
- So the primes in `I` carry `≫ x^{½+ε}` of the weight, and there are `≫ x^{2ε}/(log³x(log log x)²)` of them (Cauchy–Schwarz again).
- The same argument in AA gives primes in almost all intervals `(y, y+y^ε)`. ∎

## Meaning (why this matters for the producer search)
- **Hardness transfer.** An unconditional construction of a prime-supported producer would prove two open problems:
  - primes in every interval `(x, x+x^{½+ε})`, where the best unconditional exponent is `0.525` (Baker–Harman–Pintz);
  - primes in almost every interval `(y, y+y^ε)`, for every `ε`, where the known exponents are fixed positive constants (Huxley-type density arguments).
  - So prime-supported producers are at least as hard as these short-interval problems. This makes L119/L127 rigorous in the direction producer ⇒ primes.
- **Where an unconditional producer must live.**
  - By (S), (AA) and (D), the support must be `x^{½+ε}`-dense, almost-everywhere `x^ε`-dense, and of density `≫ x/log^{3+o(1)}x`.
  - A support containing all integers meets these trivially, and then only the resonance obstruction (L107/L133) remains.
  - So an unconditional producer needs **dense composite support with anti-resonant (non-multiplicative) weights of polylogarithmic square mass (Q)**.
- **Improvement over L75.** L75 excluded supports with `#(P ∩ [2,N]) ≤ CN^θ`, `θ < ½`. (D) excludes every support of dyadic density `≤ x/log^{3+δ}x`, including squares and all polynomial images.
- **Consistency.** Λ satisfies everything, with room: its square mass is `½log²X`, its dyadic density is `x/log x`, and RH already implies primes in `x^{½+ε}` intervals (von Koch–Cramér).

## Cited inputs
- Borel–Carathéodory (in the corpus).
- Mellin inversion and contour shift (mathlib and corpus).
- Plancherel (for AA).
- Montgomery–Vaughan mean value theorem, and `L²`-boundedness of the Hilbert transform (for Q).

## Gates
- [x] 0 → 1, 1 → 2: proof above (all steps dependency-closed).
- [ ] 2 → 3: Lean. Target: Theorem S and the prime corollary, from Lemma H (Borel–Carathéodory), Lemma P (Mellin inversion plus contour shift) and Lemma M.

## Log
- 2026-09-29 — created from L148.

## Lean (2026-09-29)
- **Theorem S and the prime corollary are formal.** Standard axioms `[propext, Classical.choice, Quot.sound]`. Both modules are built and wired, and lint-clean.
- `HTGeometry/ShortBumpMellinSmoothedSums` (wired after `PoissonMeasureUniqueness`):
  - `norm_sub_le_of_re_nonneg_on_ball`: Harnack bound via Schwarz lemma on a Cayley transform;
  - `shortBump` together with `norm_mellin_shortBump_le_lorentz`: two integrations by parts give `‖𝓜φ_δ(σ+it)‖ ≤ (4+16M)δ/(1+δ²t²)`;
  - `tsum_mul_shortBump_eq_integral`: Mellin inversion, and `Σ ∫ = ∫ Σ`;
  - `integral_shortBump_eq_pole_integral`: the pole term is exactly `x∫φ_δ`, by Fubini against `∫_{u>1}u^{−s} = 1/(s−1)`;
  - `integral_lorentz_rpow_le`.
- `RHTower/WeilPositiveShortIntervalSupport` (wired after `WeilPositivitySparseWeightsObstruction`):
  - `HerglotzWeilPositive lam A`: the Herglotz form of the Weil cone;
  - `norm_regularPart_le`: `‖E(σ+it)‖ ≤ 6(K+1+Σ|lam|/n²) log(|t|+3)/(σ−½)`;
  - `exists_const_abs_smoothedSum_sub_le`: `|Σ lam(n)φ_δ(n/x) − x∫φ_δ| ≤ C x^{½+η}δ^{−κ}/(ηκ)`;
  - `exists_weight_ne_zero_mem_Ioo_of_herglotzWeilPositive`: Theorem S;
  - `exists_prime_mem_Ioo_of_herglotzWeilPositive`: prime corollary, for any log-growth datum;
  - `zetaArchimedeanDatum = ½ψ(s/2) − ½log π + 1/s` and `exists_log_bound_zetaArchimedeanDatum`;
  - **`exists_prime_mem_Ioo_of_zetaWeilPositive`**: a Weil-positive system for ζ's datum supported on the primes forces a prime in every `(x, x+x^{½+ε})`.
- Still paper-only: (AA) (Plancherel in `log y`), (Q) (Montgomery–Vaughan and the Herglotz mean square), and (D).
- **2026-09-29 (L149): Theorem AA is formal.** Module `RHTower/WeilPositiveAlmostAllShortIntervals` (wired after `WeilPositiveShortIntervalSupport`); standard axioms.
  - `volume_gapStarts_le_of_herglotzWeilPositive`: for `0 < ε ≤ 1` and `X ≥ 1`, the `u ∈ [log X, log 2X]` whose window `(e^u, e^u + e^u X^{ε−1})` misses `supp lam` have measure `≤ C X^{−ε/2}`.
  - `volume_primeGapStarts_le_of_zetaWeilPositive`: a prime-supported producer for ζ's datum forces primes in all but `O(X^{−ε/2})` (logarithmic measure) of the windows of length `X^ε`, for every `ε > 0`. The unconditional record for almost-all windows is a fixed exponent (about 1/20, Jia/Harman).
  - Proof chain: `smoothedSum_sub_eq_shifted_integral` (factored out of `exists_const_abs_smoothedSum_sub_le`), the corpus Plancherel inequality `lintegral_norm_sq_angularFourier_le`, `integral_sq_lorentz_rpow_le`, and Markov.
  - Still paper-only: (Q) and (D).
