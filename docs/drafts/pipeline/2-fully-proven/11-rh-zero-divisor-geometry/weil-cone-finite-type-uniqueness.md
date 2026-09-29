# Finite-type uniqueness of Weil-positive completions of ζ's archimedean datum

- **ID:** weil-finite-type-uniqueness
- **Stage:** 2-fully-proven (paper, dependency-closed 2026-09-29)
- **Type:** THEOREM (paper), dependency-closed; cited inputs: Gonek 1984 Lemmas 1–3, Jutila 1983, Ingham 1940, Bochner–Schwartz, Paley–Wiener–Schwartz
- **Source:** `hf-positive-hodge-attack/krein-producer-loops.md`, entries L101–L111 (L103, L104, L106, L107)
- **Statement:** If `lam = Λ⋆a + f⋆μ + v` is Weil-positive for ζ's archimedean datum (pole weight `β = 1`), with `a`, `f` finitely supported real (`f(1) = 0`) and `v` regular (`v(1) = 0`, `D_v` holomorphic on `Re s > ½ − η₀` including `s = 1`, of polynomial growth on vertical strips), then `a = δ₁`, `f = 0`, `v = 0`. In particular, within this class, `W ≠ ∅ ⟺ Λ ∈ W ⟺ RH`.

## Goal
- **Uniqueness half of the Minkowski split.** Every finite-type second completion is excluded, unconditionally. What remains is infinite-type singular parts (conjecture L106′).
- **Producer identification (L105).** Within finite type, the Γℝ functional equation acting through Λ is the only producer of Weil positivity. Its efficacy is exactly RH.
- **Non-circularity.** RH is not assumed anywhere. The proof uses only positivity-derived constraints together with unconditional analytic inputs.

## Gates
- [x] 0 → 1 in-progress: well-posed, attack found (discrete ζ′-moments), worked example checked (single dilation, `B = −(b/2)(1 + b/2 + b²/2)`)
- [x] 1 → 2 fully-proven: inputs (A), (B), (C′) written out (see "Gate 1 → 2 closure")
- [ ] 2 → 3 formalized: see Lean plan
- [ ] 3 → 4 publication-ready

## Proof architecture
1. **Constraints from positivity.** All three are independent of `v`.
   - (i) Realness at critical zeros: `J(ρ) = ζ'(ρ)[A(ρ) − A(1−ρ)] − F(ρ) − χ(ρ)F(1−ρ) = 0`, obtained from the tangent criterion (L80 mechanism).
   - (ii) `F(ρ) = 0` at multiple critical zeros: a Herglotz function has no boundary poles of order at least 2.
   - (iii) Interpolation `F(ρ) = A(ρ)ζ'(ρ)` at simple interior zeros: no interior poles (Herglotz).
2. **Step 1 (dilation part).** Take `Σ_ρ J(ρ)V(ρ)` with `V = A(s)A(1−s)W₀(s)`.
   - The critical terms vanish.
   - The off-line terms are bounded by `C·(γ/2π)^{(1+η)|β−½|}`, because the factor `A` in `V` turns `ζ'(ρ)A(ρ)` into `F(ρ)`.
   - Rule A gives the unconditional main term `(T/4π)log²T·[top coefficient of (A − Ã)AÃW₀]`.
   - The density input (C) bounds the off-line sum by `O(T log T)`.
   - Conclusion: `A` is constant.
3. **Step 2 (L103).** With `A = c`, consider `Σ_ρ ζ'(ρ)G_F(ρ)W(ρ)`.
   - Critical terms vanish, and off-line terms are bounded via `|ζ'(ρ)| ≤ M_F/|c|`.
   - The main term is `(T/4π)log²T·B(F,W)`, with `B(F,·) ≢ 0` for `f ≠ 0` by Möbius inversion.
   - Conclusion: `f = 0`.
4. **Step 3 (L106).** Now `lam = cΛ + v`, and `v` is pole-free.
   - Positivity forbids interior poles, so RH holds.
   - Then `−D_v` is a Herglotz function with zero vertical means, so `D_v = 0`.
   - Finally `c = 1` by L52 or L77.

## Named inputs to complete (gate 1 → 2)
- **(A) Rules A/B.** For `X(s) = Σ_r x_r r^{−s}` with finitely many rational frequencies:
  - `Σ_{0<γ≤T} ζ'(ρ)X(ρ) = (T/4π)log²(T/2π)·Σ_q x_{1/q} + O_X(T log T)`;
  - `Σ ζ'(1−ρ)X(ρ) = (T/4π)log²(T/2π)·Σ_n x_n/n + O_X(T log T)`.

  Proof route: rectangle contour for `(ζ'/ζ)ζ'X` and Gonek's stationary-phase lemma `(1/2πi)∫χ(s)y^s ds ≈ y e^{2πiy}`. For non-integer phases use PNT in progressions. Rule B follows by the zero symmetry `ρ ↦ 1 − ρ̄`.
  - Checks: `X ≡ 1` gives Fujii's asymptotic (Shanks), and the result agrees with the AFE heuristic.
  - To do: verify against arXiv:2601.18025 (generalized Landau–Gonek for `Σχ(ρ)X^ρ`) and Arias de Reyna's Theorem 3.1 (arXiv:1403.7126).
- **(B) Herglotz interior analyticity.** Weil positivity of `lam` implies that `Φ_lam = G_∞ + β(1/s + 1/(s−1)) − D_lam` is analytic with `Re ≥ 0` on `Re s > ½` (L83 sketch). Equivalently, Weil's off-line detection argument applied to `D_lam`.
- **(C) Zero density.** `N(σ,T) ≪ T^{1−A(σ−½)}log T` for some `A > 1`, uniformly for `½ ≤ σ ≤ 1`.
  - Conrey 1989 announced `A = 8/7 − ε`.
  - The same follows by Selberg's method from any mollified mean square of length `T^θ` with `θ > ½`, e.g. Bettin–Chandee–Radziwiłł (`θ = ½ + 1/66`).
  - Needed only when `f ≢ 0`; the pure dilation case needs no density input.

## Lean plan (when Lean is available)
- **Algebraic core, no analysis.**
  - Nondegeneracy of the rational-frequency functional (lowest-frequency argument in `ℂ[ℚ_{>0}]`).
  - Möbius inversion for `B(F,·)`.
  - The identities `ζ'(ρ)G_F(ρ) = ζ'(ρ)F(1−ρ) − ζ'(1−ρ)F(ρ)` and `J·V` at zeros from the derivative FE `ζ'(1−ρ) = −χ(1−ρ)ζ'(ρ)`.
- **Analytic core.** Rules A/B and density (C) are deep. Formalizing them is a project of the size of the corpus's Zeta23 / Alpöge–Furman work. Per the unconditional-Lean rule they cannot enter as hypotheses in a final theorem; they must be built.

## Log
- 2026-09-29 — created in 1-in-progress from L103–L106. The worked example (single dilation) checks. Inputs (A)–(C) are named.

## Input (A): proof of Rules A/B (2026-09-29)
**Rule A.** For `X(s) = Σ_{r∈R} x_r r^{−s}`, with `R ⊂ ℚ_{>0}` finite,
`S(T) := Σ_{2<γ≤T} ζ'(ρ)X(ρ) = (T/4π)log²(T/2π)·Σ_{q∈ℕ} x_{1/q} + O_X(T log T)`.
The sum runs over zeros with multiplicity. At a multiple zero `ζ'(ρ) = 0`, and the residue of `(ζ'/ζ)ζ'X` there is 0, so the bookkeeping is consistent.

*Proof.* Let `c = 1 + 1/log T`. Choose `T` at distance `≫ 1/log T` from all ordinates; changing `T` by `O(1)` moves `O(log T)` terms of size `≪ T^{½+ε}`. Integrate `(ζ'/ζ)ζ'X` over the rectangle with vertices `c+2i, c+iT, 1−c+iT, 1−c+2i`. There are no poles besides the zeros: `s = 1` and the real poles of `χ'/χ` lie outside.
1. *Right edge.* `(ζ'/ζ)ζ' = Σ_m a(m)m^{−s}`, with `a = Λ⋆log ≥ 0` and `a(m) ≤ log²m`.
   - The diagonal `m r = 1` gives `O_X(T)`.
   - Off-diagonal terms are `≪ a(m)(mr)^{−c}/|log(mr)|`. For `mr ∉ (½, 2)` the logarithm is `≥ log 2`, and only finitely many `m` lie in the window. So the total is `O_X(log³T)`.
2. *Horizontal edges.* `ζ'/ζ ≪ log²T` there (Titchmarsh 9.6), `ζ' ≪ T^{½}log²T` for `σ ≥ −1/log T`, and `X ≪_X 1`. So these contribute `O(T^{½}log⁴T)`.
3. *Left edge.* Use `ζ'/ζ(s) = χ'/χ(s) − ζ'/ζ(1−s)`.
   - *(3a)* `−(1/2πi)∫(χ'/χ)ζ'X`. The integrand is analytic in the strip for `Im s ≥ 2`, so move it to `σ = c`, at cost `O(T^{½}log³T)`. There `χ'/χ = −log(t/2π) + O(1/t)`. The diagonal `kr = 1` gives `−(T/2π)log(T/2πe)·Σ_q x_{1/q}log q`, which is `O_X(T log T)`. Off-diagonal terms, after integrating the smooth weight by parts, are `O(log³T)`.
   - *(3b)* `(1/2πi)∫(ζ'/ζ)(1−s)ζ'(s)X(s)ds` on `σ = 1−c`. Here `(ζ'/ζ)(1−s) = −ΣΛ(j)j^{s−1}` and, by the FE, `ζ'(s) = χ(s)Σ_m[(χ'/χ)(s) + log m]m^{s−1}`. So
     `(3b) = −Σ_{j,m,r} Λ(j)x_r(jm)^{−1}·𝒥(jm/r; m)`, where `𝒥(y; m) := (1/2πi)∫_{1−c+2i}^{1−c+iT} χ(s)[(χ'/χ)(s) + log m]y^s ds`.
   - **Lemma G** (stationary phase, Gonek 1984 Lemma 5 in its real-`y` form). For `1/π ≤ y ≤ T/2π`, `(1/2πi)∫χ(s)y^s ds = y·e(y) + O(y^{½}log T)`, and `0 + O(y^{½}log T)` outside that range. With the weight, `𝒥(y;m) = y·e(y)·(log m − log y) + O(y^{½}log²T)`, since `χ'/χ = −log y` at the stationary point `t₀ = 2πy`.
     - *Sign normalization:* `X ≡ 1` must return Fujii's `+(T/4π)log²T`.
   - Summing the errors gives `≪ Σ_{jm≤T} Λ(j)(jm)^{−½}log²T ≪ T^{½}log³T`. The main part is `Σ_{j,m,r} Λ(j)x_r r^{−1}e(jm/r)log(j/r)`, over `jm ≤ rT/2π`.
     - *Case `r = 1/q`.* All phases are 1, and the sum is `x_{1/q}(T/2π)Σ_{j≤T/2πq} Λ(j)log(qj)/j + O(T) = (T/4π)log²(T/2π)·x_{1/q} + O(T log T)`, by Mertens: `ΣΛ(j)log j/j = ½log²Y + O(log Y)` and `ΣΛ(j)/j = log Y + O(1)`.
     - *Case `r = a/b` with `a ≥ 2` in lowest terms.* The phase `e(jmb/a)` is periodic in `m` with mean `[a|j]`.
       - For `a ∤ j` the partial sums in `m` are `O(a)`, giving `≪ Σ_{j≤T}Λ(j)log T = O(T log T)`.
       - For `a | j`, `j = p^l` and `a = p^k`, giving `(T/2π)x_r Σ_{l≥k} log p·log(p^l a/b)/p^l = O(T)`. ∎
**Rule B.** `Σ ζ'(1−ρ)X(ρ) = (T/4π)log²(T/2π)·Σ_n x_n/n + O(T log T)`.
- Map the zeros by `ρ ↦ 1−ρ̄`; the ordinate is preserved and so is the multiset.
- With real coefficients, the sum equals `conj Σ_ρ ζ'(ρ)X̃(ρ)`, where `X̃(s) = X(1−s)` has frequency `1/r` with coefficient `x_r/r`.
- Apply Rule A. ∎

## Input (B): status
In the finite-type setting `Φ_lam = G_∞ + β(1/s + 1/(s−1)) + Aζ'/ζ − F/ζ + D_v` is explicitly meromorphic. Three facts are then standard:
- Interior poles are excluded by Weil's classical off-line detection tests (the positivity ⇒ no-interior-singularity direction of Weil's criterion, applied to `D_lam`).
- Non-real boundary residues are excluded by the tangent criterion (L80 mechanism, in Lean for dilations).
- Boundary poles of order ≥ 2 are excluded because they make the Weil distribution non-positive.

So (B) needs no general Herglotz theorem in the finite-type case.

## Gate status
- (A): proven above, modulo the citation of Lemma G in its real-`y` form (Gonek 1984; Conrey–Ghosh–Gonek).
- (B): standard in the finite-type case.
- (C): literature (Conrey 1989: `8/7 − ε`; or BCR 2017 via Selberg). Needed only for `f ≢ 0`.
- **Remaining for gate 1 → 2:** verify the exact statement of Lemma G for real `y` in Gonek's paper, and fix the density citation. Pure dilations (`f ≡ 0`) are then dependency-closed on paper *without* (C).
- 2026-09-29 — (A) written out; card at "paper proof modulo two citations".
- 2026-09-29 — **Lemma G citation fixed.** For real `r > 0`, `(1/2πi)∫_{c+i}^{c+iT} χ(1−w) r^{−w} dw = 1_{[0,T/2π]}(r)·e(−r) + (error)`. This is Gonek, Invent. Math. 75 (1984) 123–142, Lemmas 1–3 (stationary phase with Stirling), in the form quoted in arXiv:2601.18025.
  - Our `𝒥(y;m)` is this with `s = 1−w`, `r = 1/y` scaling, and the `χ'/χ` weight (integration by parts).
  - Input (A) is therefore dependency-closed on paper.
  - **The pure-dilation case of the theorem (`f ≡ 0`) is now dependency-closed on paper.** The general case additionally needs only the density citation (C).
- 2026-09-29 — **Can the density input (C) be weakened?** Tested whether a χ-power weight could lower the needed exponent from `A > 1` to `A > ½`, where Jutila's `A = 1 − ε` would suffice.
  - The off-line weight `(γ/2π)^{|β−½|}` sits on the right zero, through `χ(1−ρ)` in `G_F`, and on the left partner, through `ζ'(ρ')`.
  - A factor `χ(1−s)^{κ}` in `W₀` moves it between them. At `κ = ½` both carry only `(γ/2π)^{δ/2}`.
  - **But** a `χ^{½}` twist destroys the `T log²T` main term. By Arias de Reyna's Theorem 3.1 at `κ = ½`, the stationary points sit at `n ≤ √(T/2π)` with alternating phases, giving `O(T^{3/4})`.
  - **NEGATIVE:** the full `(γ/2π)^δ` weight is intrinsic to any non-oscillating main term, so `A > 1` is necessary for this method.
  - Status of (C): Conrey 1989 (`8/7 − ε`, stated as announced in the literature, e.g. Simonič arXiv:1910.08274); BCR 2017 mean square at `θ = ½ + 0.01515` via Selberg's method. Dickinson (Mathematika 2024, arXiv:2211.06264) gives density bounds very close to the line for Dirichlet L-function families. The card keeps (C) as a cited input.
- 2026-09-29 — **Scope extended (L114).** The theorem holds for singular data `A`, `F` in any Beurling algebra `𝒲_η`, not only for finite type. Proof changes:
  - Rules A/B are extended by truncation.
  - Nondegeneracy uses Möbius inversion over `ℚ_{>0}` together with the identity theorem.
  - The off-line bounds are unchanged up to `(γ/2π)^{η'|β−½|}`.
  - Consider retitling to "Beurling-class uniqueness" at gate 2.

## Gate 1 → 2 closure (2026-09-29): inputs (B) and (C′) proved, s = 1 normalization, Step 3 direct

### Precise class
- `a`, `f` real, finitely supported, `f(1) = 0`.
- `v` real with `Σ|v(n)|n^{−σ} < ∞` for `σ > 1`, `v(1) = 0`, and `D_v` extending holomorphically to `Re s > ½ − η₀` (some `η₀ > 0`, **including `s = 1`**), with polynomial growth in `|t|` on vertical strips `½ ≤ σ ≤ σ₁`.
- Datum: `W_lam(g) = arch(g) + β[ĝ(0) + ĝ(1)] − Σ_n lam(n)[g(n) + n^{−1}g(1/n)]`, with ζ's pole weight `β = 1`. Weil-positive means `W_lam(h⋆h̃*) ≥ 0` for all `h ∈ C_c^∞(ℝ_{>0}^×)`.

### Input (B), proved: the positivity ⇒ analyticity dictionary
Pass to `x = log` with the half-density normalization. Then `W_lam` is a distribution `T` on `ℝ`: real, even, and **positive definite**:
`T = β(e^{x/2} + e^{−x/2}) + arch(x) − Σ_n lam(n)n^{−½}(δ_{log n} + δ_{−log n})`.
1. **Temperedness (Bochner–Schwartz).** `T` is the Fourier transform of a positive tempered Radon measure `μ` (Schwartz, *Théorie des distributions* VII.9; Reed–Simon II, Thm IX.10).
2. **Laplace side.**
   - Take `χ ∈ C^∞`, `χ = 0` on `x ≤ ½`, `χ = 1` on `x ≥ 1`. Then `χT ∈ 𝒮'` is supported in `[½, ∞)`.
   - Its Laplace transform `L(s) := ⟨χT, e^{−(s−½)x}⟩` is holomorphic on `Re s > ½`, and its `𝒮'` boundary value is `FT(χT)` (Paley–Wiener–Schwartz; Hörmander ALPDO I, Thm 7.4.2).
   - For `Re s > 1`, a direct computation gives `L = Φ_lam + E`, with `E` entire and `Φ_lam := G_∞ + β(1/s + 1/(s−1)) − D_lam`. The cutoff differs from `1_{x>0}` on a compact set, and it modifies only the finitely many `n` with `log n < 1`.
   - **Hence `Φ_lam` continues holomorphically to all of `Re s > ½`.**
3. **Boundary dictionary.**
   - `T` is even and real, so `μ = 2 Re FT(χT) + FT((1−χ−χ̌)T)`, and the last term is real-analytic.
   - Let `z₀ = ½ + it₀`, and suppose `Φ_lam = Σ_{k≤K} c_k(s−z₀)^{−k} + hol` near `z₀`. Each term has boundary value `c_k i^{−k}(x − i0)^{−k}`, where `x = t − t₀`, and `(x−i0)^{−k} = Pf x^{−k} + iπ(−1)^{k−1}δ^{(k−1)}/(k−1)!`.
   - *Order `K ≥ 2` is impossible.*
     - Pair `μ ≥ 0` with dilates `φ(x/λ)` of a bump `φ ≥ 0` supported in `(0,1)` or in `(−1,0)`. This gives `Re(c_K i^{−K})·(±1)^K·λ^{1−K} ≥ 0` as `λ → 0`.
     - For odd `K` this forces `Re(c_K i^{−K}) = 0`. For even `K`, dyadic summation gives `μ((0,1)) = ∞` unless `Re(c_K i^{−K}) = 0`, and `μ` is Radon.
     - Then pair with `φ(x/λ)`, where `φ ≥ 0` and `φ^{(K−1)}(0) ≠ 0`. The left side stays bounded by `‖φ‖_∞ μ([−λ,λ])`, while the `δ^{(K−1)}` term grows like `λ^{1−K}`, and the lower-order `Pf` terms are `O(λ^{2−K}|log λ|)`. So `Im(c_K i^{−K}) = 0`, i.e. `c_K = 0`.
   - *Order 1.* The boundary value of `c₁/(s−z₀)` is `2 Im(c₁)·PV(1/x) + 2π Re(c₁)·δ`.
     - Dyadic summation on the side where `Im(c₁)/x < 0` contradicts `μ ≥ 0`, so `Im c₁ = 0`.
     - The atom gives `Re c₁ ≥ 0`.
   - **Conclusion: every boundary pole of `Φ_lam` is simple, with real residue `≥ 0`.**
4. **Consequences in the finite-type class.** Here `D_lam = −Aζ'/ζ + F/ζ + D_v`.
   - (iii) There are no poles in `Re s > ½`. So `F(ρ) = A(ρ)ζ'(ρ)` at simple zeros with `β > ½`, and at multiple ones `ζ'(ρ) = 0`, so their terms vanish.
   - (ii) At a critical zero of multiplicity `m ≥ 2`, the pole order of `F/ζ` must be `≤ 1`, so `F(ρ) = 0`.
   - (i) At a simple critical zero the residue `A(ρ) − F(ρ)/ζ'(ρ)` is real. By `ζ'(1−ρ) = −χ(1−ρ)ζ'(ρ)` this is `J(ρ) = 0`.
   - **(new) `s = 1`.** Near `s = 1`, `Φ_lam = (β − A(1))/(s−1) + hol`, because `−ζ'/ζ ∼ 1/(s−1)`, `F/ζ(1) = 0`, and `D_v` is holomorphic at 1. So **`A(1) = β = 1`.**
   - Consequence 1: the branch `A ≡ 0` of Step 1 (previously "routine, to be written out") is empty.
   - Consequence 2: Step 1's `A = c` gives `c = 1` directly, with no appeal to L52/L77/L81.

### Input (C′), proved from classical density theorems: the off-line weight
**Lemma C′.** `S(T) := Σ_{0<γ≤T, β>½} T^{β−½} = O_ε(T(log T)^{1+12ε} log log T)` for every `ε > 0`. In particular `S(T) = o(T log²T)`.
- *Proof.* Put `L = log T` and `N(σ) = N(σ,T)`. Since `T^{β−½} − 1 = ∫_0^{β−½} L T^u du`, we get `S(T) = N(½⁺) + L∫_0^{½} T^u N(½+u) du`, with `N(½⁺) ≤ N(T) ≪ TL`. Split the integral at `u₂ = 12 log L / L`.
  - *Near range `u ≤ u₂`, Jutila 1983* (Studies in Pure Math., Birkhäuser, 385–394, the improvement of Selberg's constant `¼` to `1−ε`; restated in Simonič arXiv:1910.08274 §1): `N(½+u) ≪_ε T^{1−(1−ε)u}L`. So this part is `≪ TL²·u₂·T^{εu₂} = 12 TL log L·L^{12ε}`.
  - *Far range `u ≥ u₂`, Ingham 1940*: `N(σ) ≪ T^{3(1−σ)/(2−σ)}L⁵`, and `3(½−u)/(3/2−u) ≤ 1 − 4u/3`. So this part is `≪ L·∫_{u₂}^{½} T^{1−u/3}L⁵ du ≤ 3TL⁵·T^{−u₂/3} = 3TL`. ∎
- **Correction to L103/L104, MUST-514 and MUST-518.** The uniform exponent `A > 1` (Conrey's announced `8/7`, or BCR via Selberg) is **not needed**, and neither is the earlier remark that "`A > 1` is necessary for this method".
  - The method needs only `S(T) = o(T log²T)`: the main term is `≍ T log²T`, and each off-line term is `≤ C·(γ/2π)^{|β−½|}`, with `C` absorbing `N_e^{|β−½|} ≤ N_e^{½}`.
  - Jutila's `1 − ε` near the line together with Ingham's `4/3` away from it suffice. The χ^{½}-twist negative result stands; it concerns a different weight.
  - Beurling-class version (L114): weights `(γ/2π)^{(1+η)|β−½|}` are handled the same way for `η < 1/12`. Take `u₂ = M log L/L` with `9/(1−3η) < M < 1/(η+ε)`.

### Step 3 without L52/L77/L78: direct proof
With `c = 1` and `f = 0`, `lam = Λ + v`.
1. `Φ_lam = ξ'/ξ − D_v`, where `G_∞ = ½ψ(s/2) − ½log π`. Holomorphy on `Re s > ½` together with `D_v` holomorphic there means ζ has no zero with `β > ½`: **RH**.
2. **The Weil measure of `Λ + v`.**
   - `T_Λ` is positive definite under RH, so `T_v = T_Λ − T_lam` is tempered and supported in `|x| ≥ log 2`.
   - Its Laplace transform is exactly `D_v`, which is holomorphic across the line. So `FT(T_v) = 2Re D_v(½+it)`, a continuous function.
   - Also `Re ξ'/ξ(½+it) = 0` off zeros, since `ξ(½+it)` is real.
   - Hence `μ_lam = (atoms at critical ordinates) − 2Re D_v(½+it)dt`, and `μ_lam ≥ 0` forces `Re D_v(½+it) ≤ 0` for all `t`.
3. **Phragmén–Lindelöf.** `u := −Re D_v` is harmonic on `½ < σ < σ₁`, `≥ 0` on `σ = ½`, `≥ −ε(σ₁)` on `σ = σ₁` with `ε(σ₁) → 0` (because `v(1) = 0`), and of polynomial growth. So `u ≥ −ε(σ₁)`; letting `σ₁ → ∞` gives `u ≥ 0` on `Re s > ½`.
4. **Almost periodicity.** For `σ > 1`, `t ↦ u(σ+it)` is a nonnegative Bohr almost-periodic function with mean `−v(1) = 0`, hence `≡ 0`. So `Re D_v ≡ 0` on `σ > 1`, `D_v` is constant, and `D_v → 0` gives `v = 0`. ∎

### Status after closure
- (A) proved (Gonek 1984 Lemmas 1–3 cited). (B) proved above (Bochner–Schwartz and Paley–Wiener–Schwartz cited). (C′) proved from Jutila 1983 and Ingham 1940.
- Step 1 main-term auxiliaries:
  - Landau–Gonek for `Σ_ρ r^{−ρ}` with `r ∈ ℚ_{>0}` fixed: `O(T log T)` in total;
  - the χ-twisted sum `Σ_ρ χ(ρ)F̃V(ρ)`: `O(T)`, by Gonek's Lemma G, as in Input (A) edge 3b.
- **The theorem is dependency-closed on paper, unconditionally, for the class above.** Gate 1 → 2 passed.

## Lean (2026-09-29): algebraic core
- Module `RHTower/FiniteTypeDiscreteMomentAlgebra`, wired into `RHTower.lean`; axioms `[propext, Classical.choice, Quot.sound]`.
  - `deriv_riemannZeta_one_sub_eq_of_zero`: `ζ'(1−ρ) = −A(ρ)ζ'(ρ)` at zeros with `Re ρ > 0`, where `A(s) = 2(2π)^{−s}Γ(s)cos(πs/2)` (so `A(ρ) = χ(1−ρ)`).
  - `deriv_mul_reflectionCombination_eq`: `ζ'(ρ)G_E(ρ) = ζ'(ρ)E(1−ρ) − ζ'(1−ρ)E(ρ)` (the L103 identity).
  - `eq_zero_of_sum_multiples_div_eq_zero` and `eq_zero_of_sum_multiples_div_eq_const`: nondegeneracy of `B(E,·)`, i.e. Step 2's coefficient recovery, by the maximal-support argument, which replaces Möbius inversion.
- Remaining for gate 2 → 3: the analytic inputs (Rules A/B via Gonek's lemma, Jutila + Ingham, the Bochner–Schwartz dictionary). These are the size of the corpus's Zeta23 work.
