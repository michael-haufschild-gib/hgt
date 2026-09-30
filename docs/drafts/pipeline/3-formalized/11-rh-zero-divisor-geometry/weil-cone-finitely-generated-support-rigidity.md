# Weil-cone rigidity on finitely generated multiplicative supports (|ζ|²-notch Bohr lift)

- **ID:** weil-cone-fg-support-rigidity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** MC conjecture loop, cycle 167 (`1-in-progress/mc-conjecture-loop-2026-09-28.md`); HF L164 Müntz–Blaschke conjecture and L165 resolution analysis (`1-in-progress/hf-positive-hodge-attack/krein-producer-loops.md`); Q_ann (HF L164, MUST-564).
- **Statement:** Let `P` be a finite set of primes and `S_P` the set of integers `n ≥ 2` all of whose prime factors lie in `P`. If `v` is supported on `S_P`, `|v(n)| ≤ A(1 + log n)^D`, and the null potential `ψ_v(y) = Σ_n v(n)(K(y + log n) + K(y − log n))` (`K = Φ⋆Φ̃`, `𝓕K ∝ Ξ²`) is positive definite or negative definite, then `v = 0`. Consequently a full-cone Weil-positive `lam` with `lam = Λ` off `S_P` equals `Λ`.

## Goal

The Weil cone is `C = {lam : WeilPositiveFull lam}`, and `RH ⟺ Λ ∈ C`. Uniqueness (P2) says `C ⊆ {Λ}`. Known rigidity classes:
- order-comparable deviations;
- lacunary supports (ratio 3, then 4/3 in HF L165);
- powers of 2;
- geometric supports (HF L164 periodization, paper);
- `ℓ²` deviations on Baker-separated supports;
- square-root scale;
- polylog square mass;
- regular deviations (MUST-556) and regular Q_ann witnesses (MUST-564).

None of these covers a finitely generated semigroup such as `{2^a 3^b}` with deviations of box size. HF L165 concluded that polylog-sparse, large-deviation rigidity "is not reachable by radical tests of this design, under RH or not": notches at the zeros need zero sums `Σ_γ x^{iγ}` at `x ≍ T^C`, beyond Landau–Gonek.

This card uses a different notch: the weight `|ζ(½+it)|²` itself, which vanishes exactly at the critical zeros.
- Its crosstalk at the samples `log n` is a twisted second moment of `ζ`, not a zero sum. It is controlled by the product approximate functional equation for every twist up to `L^{1+ε}`.
- On the Bohr torus of `P`, the `|ζ|²`-weighted Kronecker flow equidistributes to the positive density `Ψ_P = Π_{p∈P}(1 − 1/p)/|1 − p^{−1/2}e^{iθ_p}|²`.
- For infinitely many primes this product is Kakutani's product of Poisson kernels. It is absolutely continuous iff `Σ 1/p < ∞`.

This identifies the barrier for full integer support. For `P` = all primes, `Σ 1/p = ∞` (Mertens), and the `|ζ|²`-lift is singular with respect to Haar measure, so the method cannot conclude. That is the multiplicative form of the `α ≥ 1` wall and of HF's heuristic Müntz threshold `Σ_{n∈S} 1/n < ∞`.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea
- [x] 1 → 2  fully-proven: complete paper proof below
- [x] 2 → 3  formalized: `RHTower.WeilFiniteSupport.eq_zero_of_positiveDefinite_neg_nullPotential`, `RHTower.WeilFiniteSupport.eq_zero_of_positiveDefinite_nullPotential`, `RHTower.WeilFiniteSupport.eq_vonMangoldt_of_weilPositiveFull`
- [ ] 3 → 4  publication-ready

## Notation and normalizations

- `Ξ(t) = ξ(½ + it)` is real and even on `ℝ`, with `ξ(s) = ½ s(s−1) π^{−s/2} Γ(s/2) ζ(s)`.
- `h(t) := ½(¼ + t²) π^{−1/4} |Γ(¼ + it/2)|`. This is smooth, even and positive, and `Ξ(t)² = h(t)² |ζ(½ + it)|²`.
- `K = riemannAutocorr` has Fourier transform `𝓕K(ξ) = Ξ(2πξ)²` (corpus `riemannAutocorr_eq_integral`).
- For `g` continuous, integrable, with integrable transform, the spectral pairing of a positive-definite `−ψ = charFun σ` reads (corpus `WeilDeviationSpectralPairing`, re-proved for `S_P`-supported `v`):
  `Σ_n v(n) (𝓕(Ξ²g)(log n) + 𝓕(Ξ²g)(−log n)) = −∫ g(t/2π) dσ(t)`.
  In particular the left side is `≤ 0` for every `g ≥ 0`.
- `𝓕(Ξ²g)(y) = (1/2π) ∫ Ξ(t)² g(t/2π) e^{−ity} dt`.

## Theorem A

Let `P = {p_1, …, p_r}`, `S = S_P`, and let `v : ℕ → ℝ` vanish off `S` with `|v(n)| ≤ A(1 + log n)^D`. If `−ψ_v` is positive definite on `ℝ`, then `v = 0`. The same holds if `ψ_v` is positive definite (replace `v` by `−v`).

**Corollary B.** Let `lam` be `WeilPositiveFull` with `lam(n) = Λ(n)` for every `n ≥ 2` outside `S_P`. Then `lam = Λ`.

*Proof of B.* Put `v(n) = (lam(n) − Λ(n))/√n`.
- The universal box gives `|lam(n)| ≤ √n(log n + C₀)`, so `|v(n)| ≤ 2 log n + C₀`.
- The deviation potential is negative definite (corpus `positiveDefiniteOnReal_neg_deviationPotential`).
- Theorem A applies. ∎

## Proof of Theorem A

### Step 0: summability

Write `S ∋ n = Π p_i^{a_i}` with `a ∈ ℕ^r∖{0}`. Then `#{n ∈ S : log n ≤ Λ₀} ≤ (1 + Λ₀/log 2)^r`. Hence `Σ_{n∈S} |v(n)| (1 + log n)^{−K} < ∞` for `K > r + D + 1`, and `Σ_{n∈S} |v(n)| n^{−δ} < ∞` for every `δ > 0`.

### Step 1: the pairing inequality with a `|ζ|²` notch

Fix `L ≥ L₀` and the block window `ω = ω_L`. It is smooth, `0 ≤ ω ≤ 1`, supported in `[L/2, 5L/2]`, equal to `1` on `[L, 2L]`, with `|ω^{(j)}| ≤ C_j L^{−j}`. Fix a real trigonometric polynomial
`Q(t) = Σ_{b∈B} c_b e^{itλ_b}`, `λ_b = Σ b_i log p_i`, `B ⊂ ℤ^r` finite, with `Q ≥ 0`.

Take `g(ξ) := ω(2πξ) Q(2πξ) / h(2πξ)²`. It is continuous, compactly supported and nonnegative, and its transform is integrable because `g` is `C²` with compact support. Then `Ξ(t)² g(t/2π) = ω(t) Q(t) |ζ(½+it)|²`.

The interchange of `Σ_n` and `∫` is justified as follows.
- `Ξ² g` is smooth and compactly supported, so `|𝓕(Ξ²g)(y)| ≤ C_K (1 + |y|)^{−K}`.
- Step 0 then applies.

The spectral pairing gives
`(1.1)   Σ_{n∈S} v(n) Re ∫ ω(t) Q(t) |ζ(½+it)|² n^{it} dt ≤ 0`.

### Step 2: the Euler-factor choice of `Q`

Fix `n₀ ∈ S` and `ε ∈ {±1}`, and let
`Q_ε(t) := |1 + ε n₀^{it}|² Π_{i=1}^r |1 − p_i^{−1/2 + it}|²`.
Then `Q_ε ≥ 0`, and `Q_ε(t) |ζ(½+it)|² = |1 + ε n₀^{it}|² |ζ_P(½+it)|²` with `ζ_P(s) := ζ(s) Π_{p∈P}(1 − p^{−s})`. Expand
`Π_i |1 − p_i^{−1/2+it}|² = Σ_{c∈{−1,0,1}^r} e_c q_c^{it}`, `q_c = Π p_i^{c_i}`, `e_c = Π_i e_{c_i}(p_i)`,
with `e_0(p) = 1 + 1/p` and `e_{±1}(p) = −p^{−1/2}`.

Define `m(y) := ∫ ω(t) |ζ(½+it)|² e^{ity} dt` and `𝓜(y) := Σ_c e_c m(y + log q_c)`. With `|1 + εn₀^{it}|² = 2 + ε(n₀^{it} + n₀^{−it})`, (1.1) becomes
`(2.1)   Σ_{n∈S} v(n) Re[2𝓜(log n) + ε𝓜(log(n n₀)) + ε𝓜(log(n/n₀))] ≤ 0`.

The term `n = n₀` of the third family is `ε v(n₀) 𝓜(0)`, and `𝓜(0)` is real. All other arguments are `log q` with `q ∈ Γ_P∖{1}`, where `Γ_P = ⟨p_1, …, p_r⟩ ⊂ ℚ_{>0}`. Their reduced denominators divide `n₀ Π p_i`. Hence
`(2.2)   ε v(n₀) 𝓜(0) ≤ Σ_{n∈S} |v(n)| (2|𝓜(log n)| + |𝓜(log nn₀)| + 1_{n≠n₀} |𝓜(log(n/n₀))|)`.

### Step 3: the twisted second moment (core lemma)

**Core Lemma.** Fix `k₀ ≥ 1` and `ε ∈ (0, 1/10)`. There are constants `C`, `B`-dependent constants `C_B`, and `L₀` such that the following holds for all `L ≥ L₀`, all coprime `h, k ≥ 1` with `k ≤ k₀`, and `N := hk`:
`m(log(h/k)) = N^{−1/2} [ Ω_L·D_L(N) + ∫ ω(t) D*_{t,L}(N) dt ] + E_L(h,k)`.
Here:
- `Ω_L = ∫ω`;
- `D_L(N) = Σ_{j≥1} j^{−1} V(N j²/L)`, where `V` is the Gaussian AFE cutoff `smoothAFECutoff`;
- `D*_{t,L}(N) = Σ_{j≥1} j^{−1} W_t(N j² L)`, where `W_t` is the exact product-AFE dual weight at `(s₁, s₂) = (½+it, ½−it)`;
- the error satisfies
  - `|E_L(h,k)| ≤ C L^{1/2+2ε}` for `h ≤ 2k₀ L^{1+2ε}`;
  - `|E_L(h,k)| ≤ C_B (h/L^{1+2ε})^{−B}` for `h > 2k₀ L^{1+2ε}`.

Moreover, uniformly in `N ≥ 1` and `t ∈ [L/2, 5L/2]`:
`(3.1)   |D_L(N) − ½ log⁺(L/N)| ≤ C,    |D*_{t,L}(N) − ½ log⁺(t²/(NL))| ≤ C`,
and for `N ≥ L^{1+2ε}`: `|D_L(N)| + |D*_{t,L}(N)| ≤ C_B (N/L)^{−B}`.

*Proof.*

**AFE.** For `t ≠ 0` the exact product approximate functional equation with `x = L` (corpus `riemannZeta_mul_eq_productAFE`; on the critical line `χ(s₁)χ(s₂) = 1`) gives
`|ζ(½+it)|² = Σ_{m,n} (mn)^{−1/2} (n/m)^{it} V(mn/L) + Σ_{m,n} (mn)^{−1/2} (m/n)^{it} W_t(mnL) − R_L(t)`.
The residue term obeys `|R_L(t)| ≤ C√L e^{−t²/2}` on `t ≥ 1`, together with all its `t`-derivatives up to `e^{−t²/4}` factors. Integrate against `ω(t) (h/k)^{it}`.

**Direct part.** The amplitude is `t`-independent, so the term `(m,n)` equals `(mn)^{−1/2} V(mn/L) ω̂(log(nh/(mk)))`, with `ω̂(Λ) = ∫ ω e^{itΛ}` and `|ω̂(Λ)| ≤ C_K L (1 + L|Λ|)^{−K}`.
- The diagonal `nh = mk`, i.e. `(m,n) = (hj, kj)`, gives `N^{−1/2} Ω_L D_L(N)`.
- Off-diagonal, case (i): pairs with `nh/(mk) ∉ [½, 2]` have `|Λ| ≥ log 2` and contribute `≤ C_K L^{1−K} Σ (mn)^{−1/2} V(mn/L) ≤ C L^{3/2−K} log L`.
- Off-diagonal, case (ii): put `r = nh − mk ≠ 0`, so `|Λ| ≥ |r|/(4mk)`, `(mn)^{−1/2} ≤ √(2h/k)/m` and `mn ≥ m²k/(2h)`. For fixed `m`, the admissible `r` lie in one residue class mod `h`. Let `r_min(m) ≥ 1` be the least nonzero `|r|` in that class. Then
  `Σ_r min(1, (4mk/(L|r|))^K) ≤ 2 min(1, (4mk/(L r_min(m)))^K) + C_K · 4mk/(Lh)`.
  - The second summand contributes `≤ C√(k/h) Σ_m min(1, C_B(2hL/(m²k))^B) ≤ C√L`.
  - If `N ≤ L^{1−3ε}/32`, the first summand is `≤ L^{−εK/2}` on the effective range `m ≤ √(2hL/k) L^ε`. Choosing `K ≥ 4/ε` makes it negligible.
  - Otherwise, use `min(1, x^K) ≤ min(1, x)`. Since `gcd(h,k) = 1`, `m ↦ mk mod h` is injective on blocks of `h` consecutive `m`, so `Σ_{m in a block} 1/r_min(m) ≤ 2(1 + log h)`. The first summand then contributes `≤ C (1 + log h)(√L L^ε + √(hk))`.
  - For `h ≤ 2k₀ L^{1+2ε}` this is `≤ C L^{1/2+2ε}`.
  - For larger `h`, every pair with ratio in `[½, 2]` has `mn ≥ h/(2k)`, so `V(mn/L) ≤ C_B (h/(2kL))^{−B}` and the contribution decays as stated.

**Dual part.** The term `(m,n)` equals `(mn)^{−1/2} I(mnL, log(mh/(nk)))` with `I(Y, Λ) = ∫ ω(t) W_t(Y) e^{itΛ} dt`.
- **Mellin form.** `W_t(Y) = (1/2π) ∫ G_t(1+iv) e^{(1+iv)²} Y^{−(1+iv)}/(1+iv) dv`, with `G_t(u) = χ(½+it−u) χ(½−it−u)`.
- **Height jets.** `G_t` has the height-jet law `|∂_t^n G_t(u)| ≤ n! |G_t(u)| (33(1+|v|)/t)^n` for `t ≥ 4`, `2|v| ≤ t`. This is the corpus `norm_iteratedDeriv_chiCarrier_le` at displacement `d = 0`, where the modulus weight `χ(s₁)χ(s₂)` is identically `1`.
- **Size.** `|G_t(u)| ≤ C(1+|v|)^C (t/2π)^{2 Re u}` on vertical lines, by the corpus `χ` line bounds. Shifting the `u`-contour to `Re u = B` gives `|∂_t^n W_t(Y)| ≤ C_{n,B} t^{−n} min(1, (Y/t²)^{−B})`.
- **Integration by parts.** `K`-fold IBP gives `|I(Y,Λ)| ≤ C_K L min(1, (Y/L²)^{−B}) (1 + L|Λ|)^{−K}`.
- The diagonal `mh = nk`, i.e. `(m,n) = (kj, hj)`, gives `N^{−1/2} ∫ ω D*_{t,L}(N)`.
- The off-diagonal count is the direct count with `(m,n,h,k)` replaced by `(n,m,k,h)` and effective length `mn ≤ L^{1+ε}`. It gives the same bounds.

**Diagonal sums (3.1).**
- Head: `|1 − V(y)| ≤ C y^δ` gives `Σ_{j ≤ √(L/N)} j^{−1}(1 − V(Nj²/L)) ≤ C`.
- Tail: `V(y) ≤ C_B y^{−B}` gives `Σ_{j > √(L/N)} j^{−1} V ≤ C`.
- For `W_t`, the contour shifts to `Re u = −δ` and `Re u = B` give `|1 − W_t(Y)| ≤ C (Y/t²)^δ` and `|W_t(Y)| ≤ C_B (Y/t²)^{−B}`. The residue at `u = 0` is `G_t(0) = 1`. The same head/tail split applies. ∎

### Step 4: the Bohr combination

Every `q ∈ Γ_P` has a unique coordinate vector `c(q) ∈ ℤ^r`. Its reduced height is `N(q) = hk = Π p_i^{|c_i(q)|}`, so `N(q)^{−1/2} = Ψ̂(c(q))` with `Ψ̂(c) := Π p_i^{−|c_i|/2}`. The per-prime identity

`(1+1/p) p^{−|m|/2} − p^{−1/2}(p^{−|m+1|/2} + p^{−|m−1|/2}) = (1 − 1/p) δ_{m,0}`

gives `Σ_c e_c Ψ̂(c + c(q)) = Π_i (1 − 1/p_i) δ_{q,1}`. This is `|1 − p^{−1/2}e^{iθ}|² · Poisson_{p^{−1/2}}(θ) = 1 − 1/p`, i.e. the Euler factor cancels the Bohr lift of `|ζ|²`.

Write `F_L := ∫ ω(t) log t dt ≍ Ω_L log L`. For `N(q q_c) ≤ L^{1/2}`, (3.1) gives the diagonal
`N^{−1/2}[F_L − Ω_L log N + O(L)]`, using `½ log(L/N) + ½ log(t²/(NL)) = log(t/N)`. Hence:
- **`q = 1`.** `𝓜(0) = Π(1 − 1/p_i) F_L + O(L) ≥ c_P L log L` for `L ≥ L₀`.
- **`q ≠ 1`.** The `F_L` terms cancel exactly. If every `N(q q_c) ≤ L^{1/2}`,
  `|𝓜(log q)| ≤ C L Σ_c |e_c| (1 + log N(q q_c)) N(q q_c)^{−1/2} + (errors)`.
  If some `N(q q_c) > L^{1/2}`, then `N(q) ≥ L^{1/2}/C`. Each term is bounded by `C N^{−1/2} L log L ≤ C' L (1 + log N(q)) N(q)^{−1/2}`, because `log L ≤ 2 log N(q) + C`.

### Step 5: conclusion

Insert Step 4 into (2.2). The arguments `q ∈ {n, nn₀, n/n₀}` have reduced denominators at most `k₀ := n₀ Π p_i`.
- **Diagonal remainders.** `Σ_{n∈S} |v(n)| L (1 + log n)^{D+1} n^{−1/2} · C = O(L)`, by Step 0 with `δ = ½`.
- **Core errors, `h ≤ 2k₀ L^{1+2ε}`.** At most `C(log L)^r` values of `n`, each `≤ C L^{1/2+2ε} (log L)^D`, so the total is `o(L)`.
- **Core errors, larger `h`.** `Σ_n |v(n)| C_B (n/L^{1+2ε})^{−B}` over `n > L^{1+2ε}` is `o(1)`.

Hence `ε v(n₀) · c_P L log L ≤ C L`, so `ε v(n₀) ≤ C/(c_P log L)`. Letting `L → ∞` gives `ε v(n₀) ≤ 0` for both signs, so `v(n₀) = 0`. ∎

## Remarks

- **What is new.** The notch is the zeta function itself.
  - HF L165 needed notches narrower than the zero spacing, and their crosstalk is a zero sum at `x ≍ T^C` (beyond Landau–Gonek).
  - The `|ζ|²` notch has crosstalk equal to the twisted second moment. Its off-diagonal vanishes identically below twist `L^{1−3ε}` and is `O(L^{1/2+2ε})` up to `L^{1+2ε}`.
  - The Bohr lift turns the zero-killing weight into the Poisson density `Ψ_P`, which is positive exactly because the Euler factors at `P` are finite.
- **Kakutani barrier.** For a set of primes `P` with `Σ_{p∈P} 1/p = ∞`, the product `Π_p Poisson_{p^{−1/2}}` is singular with respect to Haar measure (Kakutani's dichotomy: `Σ (p^{−1/2})² = ∞`). The final step `T̃Ψ ≤ 0 ⇒ T̃ ≤ 0` then fails. For `S = ℕ` this is exactly the Mertens divergence `Σ 1/p = ∞`. It is the multiplicative form of the `α ≥ 1` wall and of HF's Müntz threshold `Σ_{n∈S} 1/n < ∞`, since `Σ_{n ∈ ⟨P⟩} 1/n < ∞ ⟺ Σ_{p∈P} 1/p < ∞`.
- **Conjecture (Kakutani–Weil).** The theorem extends to `S = ⟨P⟩` for every set of primes with `Σ_{p∈P} p^{−σ} < ∞` for all `σ > 0`. Here the counting `#S ∩ [1, X] = X^{o(1)}` replaces polylog counting in Step 5. `Σ_{p∈P} 1/p < ∞` with `X^{1−o(1)}` counting is the sharp open case.
- **Relation to Q_ann.** Theorem A answers Q_ann negatively for all witnesses supported on finitely generated semigroups, with polynomially bounded size, not only bounded size. Together with MUST-564, a Q_ann witness must be singular on the critical line and must use infinitely many primes with `Σ 1/p = ∞`.

## Novelty audit

- **Corpus.** Grepped for `finitely generated`, `Kakutani`, `Bohr`, `Müntz`, `L164`, `L165`, `symbol`, `partial sum`, `Q_ann`, `WeilFullCone*Rigidity`.
  - The closest results are ZeroFreeWindow (`ℓ²` plus Baker separation), L164 periodization (single progression) and L165 (ratio 4/3 lacunary).
  - None covers `⟨2,3⟩` with box-size deviations. L165 explicitly concluded that the case was unreachable by its test design.
  - Kakutani appears in the corpus only in unrelated JAS / prime-valuation lanes.
- **Literature.** The Weil cone is corpus-internal. Twisted second moments are classical (Balasubramanian–Conrey–Heath-Brown and the product AFE). The use of the `|ζ|²` weight as a positivity-preserving notch together with a Bohr lift is not a literature construction known to me, and it has no internal precedent.

## Log
- 2026-09-30 — created (MC cycle 167) with a complete paper proof. Lean formalization planned in modules: product-AFE critical specialization, direct/dual twisted parts, counting lemma, diagonal sums, Bohr combination, spectral pairing for `S_P`-supported deviations.
- 2026-09-30 — Lean progress (namespace `RHTower.ZetaNotch`):
  - Compiled clean:
    - `ZetaNotchDualCarrier`: critical carrier `G_t(w)`, `∂_t G = G·D`, `‖D‖ ≤ 20‖w‖/t`, size on both lines.
    - `ZetaNotchDualContour`: residue shift `W_t = 1 + W_t^{(−δ)}`.
    - `ZetaNotchDualOscillation`: notch window, one IBP, abstract windowed-carrier bound.
    - `ZetaNotchDualOscillationBound`:
      - dual line: `‖J‖ ≤ (C/Y)(L²/|ξ| + L³e^{−L²/128})`;
      - right line: `‖J − ω̂‖ ≤ C Y^{1/4}(L^{−1/2}/|ξ| + L e^{−L²/128})`.
  - Plan for the remaining modules:
    - K-fold dual-line oscillation. The jets of `critCarrier` at `σ₀ = ½` come via `norm_iteratedDeriv_chiIncrementDifference_le`. This gives summable decay for twists `q ≥ L^{A₀}`.
    - Pointwise `W_t` bounds.
    - Diagonal sums up to `O(1)`.
    - Critical AFE plus interchange.
    - Off-diagonal counting.
    - Core assembly with the Bohr combination.
    - Spectral pairing for `S_P`.
    - Final theorem.
- 2026-09-30 — **Formalized.** Theorem A for deviations with `|v(n)| ≤ 2 log n + A`, both signs, and Corollary B, in `RHTower.WeilFiniteSupport` (`WeilFiniteSupportRigidity.lean`). Axioms: `propext`, `Classical.choice`, `Quot.sound`.
  - Modules, in dependency order:
    - `ZetaNotchDualCarrier`, `ZetaNotchDualContour`, `ZetaNotchDualOscillation`, `ZetaNotchDualOscillationBound`, `ZetaNotchDualJets`: dual weight and height oscillation.
    - `ZetaNotchDiagonalSum`, `ZetaNotchDualWeightBounds`, `ZetaNotchCriticalAFE`: harmonic diagonals and the critical product AFE.
    - `ZetaNotchResonanceCount`: near-resonant mass `≤ min(24δk√L, 16δkL√(2k/h))`.
    - `ZetaNotchTwistedDiagonal`: diagonal split and the law `𝒟_L(N) = ∫ω log t − ω̂(0) log N + O(L(1 + log N))`.
    - `ZetaNotchTwistedOffDiagonal`: twisted moment equals its diagonal up to `C(L𝒩 + L²/(Lδ)^K + L²e^{−L²/32})`.
    - `ZetaNotchCrudeTail`: Cauchy jets of `|ζ(½+it)|²` and the tail `C_K L³/|ξ|^K`.
    - `SmoothNumberLogSeries`: `Σ_{P-smooth} (1 + log n)^{−2#P} < ∞`.
    - `WeilNullPotentialSpectralPairing`: Bochner pairing for log-bounded coefficients, using kernel smoothing of polynomial decay.
    - `ZetaNotchSmoothTest`: `Ξ(t)² = ((¼+t²)/2)² Γℝ(½+it)Γℝ(½−it)|ζ(½+it)|²` and the notch test.
    - `ZetaNotchPairingInequality`: `Σ v(n) Re M_q(log n) ≤ 0`.
    - `ZetaNotchBohrLift`: exponent vectors, per-prime Poisson cancellation, the weight as a trigonometric polynomial.
    - `ZetaNotchTwistMainTerm`: main terms of smooth twists.
    - `WeilFiniteSupportRigidity`: Rankin sums, scales `L = M^{8J}`, `δ = M^{−6J}`, key inequality, theorem.
  - Scope versus the paper statement: Lean uses the bound `2 log n + A` (the Weil box), not `A(1 + log n)^D`. The general `D` needs only a larger exponent `J` in the Rankin sums and a continuity lemma for `ψ_v` with polylog coefficients.
