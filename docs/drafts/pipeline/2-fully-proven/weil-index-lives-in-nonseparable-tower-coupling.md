# Weil's negative index lives in inter-tower coupling, never in separable prime-tower assemblies

- **ID:** TOWER-COUPLING-SIGNATURE
- **Stage:** 2-fully-proven
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/review-3110/obstacles-summary.md §2.5.2 (Route SC)
- **Statement:** No sequence of separable prime-tower assemblies `K_S = Σ_{p∈S} k_p^{(S)}(v_p(·))` built from the `S`-truncated explicit formula (primes in `S`, Gamma, pole, running counterterm) captures `κ(K_ζ) + 1` through `κ(archGlue(K_S, c)) = Σ_{p∈S} κ₀(k_p^{(S)}) + 1 + ε_S`: whenever finite, every local polar index `κ₀(k_p^{(S)}) ∈ {0, 1}` counts only local pole shares and is blind to primes and Gamma; arbitrary separable assemblies never converge pointwise to `ratCorr`; whereas the coupled `S`-valuation assembly `coupledAssembly S ratCorr` has exact glued index `κ(K_ζ) + 1` for every `|S| ≥ 2` and `c > 0`, and window-coupled `S`-truncated explicit-formula Gram matrices exhaust `κ(K_ζ) + 1` unconditionally with zero counterterm.

## Goal
Give a complete unconditional answer and full no-go closure to the open signature-calculus question of `obstacles-summary.md` §2.5.2: determine whether separable prime-tower assemblies built from the `S`-truncated complete explicit formula converge in glued negative index to `κ(K_ζ) + 1`, identify the exact analytic and algebraic obstructions, and establish the unconditional local/`S`-truncated formulas that genuinely compute `κ(K_ζ) + 1`.

## Gates
- [x] 0 → 1  in-progress: exact question, polar trichotomy, inter-tower coupling split, and coupled survivors formulated
- [x] 1 → 2  fully-proven: complete dependency-closed paper proofs (`[PROVED HERE]`), no open dependency
- [ ] 2 → 3  formalized: Lean subfolder `AdelicKreinGeometry/TowerCoupling/`, checked with `lake --old env lean`, `#print axioms` clean, wired into `AdelicKreinGeometry.lean`

## Proof `[PROVED HERE]`

### 1. Polar second-difference reduction and polar trichotomy on `ℤ`
For `k : Multiplicative ℤ → ℂ`, define the centered second difference
`Δ²k(m) = 2 k(m) − k(m + 1) − k(m − 1)`.
On any contiguous grid `y_a = L + a` (`0 ≤ a ≤ M`), the linear difference map
`diffMap M : (Fin M → ℂ) →ₗ[ℂ] (Fin (M + 1) → ℂ)`, `d ↦ Σ_{i < M} d_i (e_i − e_{i+1})`,
has left inverse `prefixSum M c i = Σ_{a ≤ i} c_a`, maps into `ker(totalMass)`, and hence is a linear isomorphism `Fin M → ℂ ≃ₗ[ℂ] ker(totalMass(Fin (M + 1)))` by rank-nullity. Bilinear expansion gives
`hermQuad (gram k y) (diffMap M d) = hermQuad (gram (Δ²k) y|_{Fin M}) d`.
Embedding arbitrary finite families on `ℤ` into contiguous grids via `pushVec` yields the exact identity in `ℕ∞`:
`polarIndex k = negIndex (Δ²k)`.

If `k` is Hermitian and `Δ²k(n) → 0` as `n → +∞`, then `Δ²k` is Hermitian and `MixingKillsNegativeSquares.negIndex_eq_zero_or_top_of_tendsto_int` gives `polarIndex k ∈ {0, ⊤}`.

For a local pole pair `pairKernel (valChar r) ω` (`r > 1`) plus a Hermitian kernel `g` with `Δ²g(n) → 0` as `n → +∞`, `Δ²(pairKernel (valChar r) ω) = pairKernel (valChar r) ((2 − r − r⁻¹) ω)` with `2 − r − r⁻¹ = −(r − 1)²/r ≠ 0`. Hence `polarIndex (pairKernel (valChar r) ω + g) = negIndex (Δ²g + pairKernel (valChar r) ω')` satisfies the **polar trichotomy**:
1. If `¬ IsPosDefKernel (Δ²g)`, then `negIndex (Δ²g) = ⊤`; since `pairKernel` vanishes on `ker(charEval (valChar r))`, `hermNegIndex_le_add_one_of_eq_on_ker` forces `polarIndex = ⊤`.
2. If `IsPosDefKernel (Δ²g)` and `ω = 0`, then `polarIndex = 0`.
3. If `IsPosDefKernel (Δ²g)` and `ω ≠ 0`, then `ω' ≠ 0`, `‖valChar r (ofAdd 1)‖ = r > 1`, and `r ≠ r⁻¹`; `negIndex_add_sum_pairKernel_le` and `le_negIndex_of_separated_out` give `polarIndex = 1`.

### 2. Negative resolution for separable `S`-truncated explicit-formula assemblies
For any finite prime set `S` and bounded arithmetic weight `lam` (`|lam n| ≤ B`), restricting `lam` to prime powers `{p^k : p ∈ S, k ≥ 1}` produces an `ℓ¹` Dirichlet weight at `s = 1/2`:
`Σ_{n ≥ 2} |truncWeight S lam n| / √n = Σ_{p ∈ S} Σ_{k ≥ 1} |lam(p^k)| / (√p)^k < ∞`
since `1 / √p < 1`. For continuous compactly supported `g : ℝ → ℂ` and `ℓ > 0`, dominated convergence gives `towerPrime (truncWeight S lam) g ℓ (ofAdd n) → 0` as `n → +∞`, while `tendsto_archPart_transl` and Hermitianness (`towerArch g ℓ (-n) = conj (towerArch g ℓ n)`) give `towerArch g ℓ (ofAdd n) → 0`. Every local counterterm `C + D·δ_0 − A|m|` satisfies `Δ²(·)(n) = 0` for `n ≥ 2`.

Consequently, for every separable assembly `K_S = towerAssembly S k^{(S)}` whose local constituents combine `S`-truncated primes, Gamma, pole share `β_{p,S} · towerPole g (log p)`, and running counterterms `(C_{p,S}, D_{p,S}, A_{p,S})`, with `c > 0`:
- **Zero-blindness of finite local polar indices:** Either some `p ∈ S` has `¬ IsPosDefKernel (Δ²g_p^{(S)})` and `κ(archGlue(K_S, c)) = ⊤`, or every `Δ²g_p^{(S)}` is positive definite, `Σ_{p∈S} κ₀(k_p^{(S)}) = r_S := #{p ∈ S : β_{p,S} · poleWeight g ≠ 0}`, and `κ(archGlue(K_S, c)) ∈ {r_S + 1, r_S + 2}` (`towerSignature_lower`, `towerSignature_upper`). Whenever finite, `κ₀(k_p^{(S)})` receives zero contribution from the `S`-primes and Gamma.
- **Pole-retaining unconditional divergence:** For `g = cx cubicSpline`, `paperFT_cubicSpline_ne_zero` at `±I/2` gives `poleWeight (cx cubicSpline) ≠ 0`. If `β_{p,S} ≠ 0` for all `p ∈ S`, then `|S| + 1 ≤ κ(archGlue(K_S, c))` for all counterterms, diverging to `⊤` as `|S| → ∞`.
- **Pole-free spectral gap and twin-flip blindness:** If `β_{p,S} = 0` for all `p ∈ S`, then `κ(archGlue(K_S, c)) ∈ {1, 2, ⊤}` for every `S`. Since `negIndex zetaKernel = 2 · #(sectorZeros)` (`negIndex_zetaKernel_le_one_iff`), `κ(K_ζ) ≠ 1` and `κ(weilArchState c) ≠ 2` unconditionally, so every finite non-RH value `κ(K_ζ) + 1 ≥ 3` lies outside `{1, 2, ⊤}` (where finite singletons are open in `ℕ∞`). Moreover, by `gammaBracket_lower` (`0 ≤ gammaBracket t + 10`) and finite `ℓ¹(ℤ)` norms of `EF.weilTest (cx f) (cx f) (-mℓ)` and `towerPrime (truncWeight S lam)`, sufficiently large diagonal counterterms `D_{p,S}` make `g_p^{(S)}` positive definite (`κ₀ = 0`, `κ = 0`), giving `κ(archGlue(K_S, c)) = 1` for both `Λ` and `primeFlipWeight q`, whereas for any prime `q` with `8 ≤ log q` (`Nat.exists_infinite_primes`), `negIndex_zetaKernel_eq_top_or_flip` forces `negIndex zetaKernel = ⊤ ∨ negIndex (weightKernel (primeFlipWeight q) cubicSpline) = ⊤`.

### 3. Obstructions to arbitrary / untruncated separable assemblies
- **Pointwise closure impossibility:** Every `towerAssembly S k` satisfies `coprimeCrossDiff K u v := K(uv) − K(u) − K(v) + K(1) = 0` whenever `u, v` have disjoint prime supports. Taking `u ∈ ⟨2, 3⟩` and `v ∈ ⟨5, 7⟩` and using independent log-density (`denseShifts_twoPrimeLattice`), any pointwise limit `K(u) = Φ(log u)` with `Continuous Φ` satisfies `Φ(x + y) − Φ(x) − Φ(y) + Φ(0) = 0` on `ℝ`, hence `Φ(x) = Φ(0) + x(Φ(1) − Φ(0))`, whose Gram forms vanish on `ker(totalMass) ∩ ker(logMass)` (`negIndex K ≤ 2 ∧ posIndex K ≤ 2`). Since `ratCorr` is continuous in `log` (`continuous_realOrbitKernel`) and satisfies `negIndex ratCorr = ⊤ ∨ posIndex ratCorr = ⊤` (`posIndex_zetaKernel_eq_top_of_finite`), no nontrivial filter of `towerAssembly` kernels converges pointwise to `ratCorr`.
- **Axial replication blow-up:** On `S.Nonempty`, the unique `towerAssembly S k` matching `K` on all prime axes `⟨p⟩` (`p ∈ S`) is `axialAssembly S K`. If `0 < negIndex zetaKernel < ⊤`, then `2 ≤ negIndex zetaKernel` and `negIndex_zetaKernel_prime_eq` gives `polarIndex (ratCorr|_{⟨p⟩}) ≥ negIndex zetaKernel − 1 ≥ 1` for all `p ∉ zetaBlindPrimes` (finite by `zetaBlindPrimes_finite_card_le`), so `κ(archGlue(axialAssembly S ratCorr, c)) ≥ |S \ blind| · (κ(K_ζ) − 1) + 1 → ⊤`.

### 4. Positive survivors and global vs. window-coupled `S`-truncation
1. **Coupled `S`-tower signature formula:** Let `sectionS S : ℤ^S →* posUnits` be `e ↦ ∏_{p∈S} p^{e_p}`, `projS S = sectionS S ∘ valS S`, and `coupledAssembly S K = K ∘ projS S`. A prime `q ∉ S` fixes `projS S`, so `negIndex_archGlue_eq_of_periodic` gives `κ(archGlue(coupledAssembly S K, c)) = κ(coupledAssembly S K) + 1`. Whenever `2 ≤ |S|`, picking distinct `p₁, p₂ ∈ S` embeds `twoPrimeLattice p₁ p₂` into `range(projS S)`, so `negIndex_orbitKernel_twoPrime` yields `κ(coupledAssembly S (orbitCorr Z f)) = #(seenRightZeros Z f)` for every tempered `Z` and `f ∈ realTests`. In particular, for `|S| ≥ 2` and `c > 0`, `κ(archGlue(coupledAssembly S ratCorr, c)) = κ(K_ζ) + 1` unconditionally, and `coupledAssembly S ratCorr → ratCorr` pointwise along `atTop`.
2. **Global vs. window-coupled `S`-truncated explicit formula:** Let `sTruncatedCorr S` be the non-separable `S`-truncated explicit-formula correlation on `posUnits` (primes in `S`, Gamma, pole, zero counterterm). At fixed `S`, `polePart` is a real multiple of `polePair` (`boostPolarIndex_add_polePair` absorbs it on `ker(boostMassU)`), while `−primePart_S + archPart` vanishes along `twoPos^N` (`MixingKillsNegativeSquares` + `boostPolarIndex_eq_negIndex_of_subBoost`), forcing `κ(archGlue(sTruncatedCorr S, c)) ∈ {1, ⊤}`. Conversely, on any affine family `g` with `|log |slope(g_i)|| ≤ L`, once `S` contains all primes `≤ ⌊e^{2L + 8}⌋₊`, `splineCorr_prime_term_eq_zero` makes every prime power outside `S` vanish at `log(|a_j|/|a_i|)`, so `gram (archGlue (sTruncatedCorr S) c) g = gram (weilArchState c) g` entrywise and the supremum over `(L, S_L)` equals `κ(K_ζ) + 1` unconditionally.

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** Centered second-difference identity `polarIndex k = negIndex (Δ²k)` combined with `ℓ¹` summability `Σ_{p∈S, k≥1} |λ(p^k)| p^{−k/2} < ∞`, Riemann–Lebesgue decay of `archPart`, and the indefinite Howe–Moore mixing law forces `κ₀(k_p^{(S)}) ∈ {0, 1, ⊤}` (prime- and Gamma-blind whenever finite); independent `{2, 3}` vs `{5, 7}` log-density blocks pointwise approximation of `ratCorr` by any separable `towerAssembly`.
- **Strongest positive survivor:** (1) Unconditional coupled `S`-valuation signature identity `negIndex (archGlue (coupledAssembly S ratCorr) c) = negIndex zetaKernel + 1` for every `S` with `2 ≤ S.card` and `c > 0` (and for `orbitCorr Z f` of every tempered `Z`); (2) exact zero-counterterm window-coupled exhaustion `gram (archGlue (sTruncatedCorr S) c) g = gram (weilArchState c) g` for `S ⊇ primesUpTo ⌊e^{2L+8}⌋₊` on `|log |slope|| ≤ L`, whose supremum over `L` equals `negIndex zetaKernel + 1` unconditionally.
- **New insight:** Two distinct obstructions were conflated in Route SC: (a) additive separability across prime towers (`Σ_{p∈S} k_p(v_p)` vs `K(∏_{p∈S} p^{v_p})`), which destroys inter-prime cross-differences where off-line zero cancellation lives; and (b) non-commutativity of `sup_g` (unbounded slope height) with `S → ∞` in the explicit formula, governed by the transition from `Σ_{n} Λ_S(n)/√n < ∞` (mixing) to `Σ_{n} Λ(n)/√n = ∞`. Keeping inter-prime coupling on `ℤ^S` (`|S| ≥ 2`) or coupling `S` to the slope-height window `e^{2L+8}` eliminates both obstructions without running counterterms.
- **Status:** Dependency-closed paper proof above; Lean formalization in `formal/GaloisForLFunctions/AdelicKreinGeometry/TowerCoupling/`.

## Log
- 2026-10-31 — created and proved in `2-fully-proven`
