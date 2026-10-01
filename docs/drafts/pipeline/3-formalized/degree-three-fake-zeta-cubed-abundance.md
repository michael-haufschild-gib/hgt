# ζ³ is not determined by its functional equation: infinitely many Dirichlet series with Γ_ℝ(s)³ symmetry

- **ID:** degree-three-fake-zeta-cubed-abundance
- **Stage:** 3-formalized
- **Type:** THEOREM; Lean: `RHTower.DegreeThreeHankel.gammaRCube_functional_equation_abundance` (standard axioms)
- **Source:** `1-in-progress/degree-three-abundance-supercritical-pairs.md` §6–§8; producer ledger L250–L251. Imported: Kulikov–Nazarov–Sodin, arXiv:2306.14013 (Lemmas 1–2 and the Theorem 2A argument); Gauss multiplication (corpus `gauss_multiplication_complex`); Hecke's theta argument.
- **Statement.** The real vector space
  `W = {E(s) = Σ_{n≥1} e_n n^{−s} : e_n = O(n^K) for some K, Λ_E(s) := Γ_ℝ(s)³E(s) is entire of finite order in vertical strips, Λ_E(s) = Λ_E(1−s)}`
  is infinite-dimensional. Consequently `V₃ = ℂζ³ ⊕ W ⊋ ℂζ³`: there are infinitely many linearly independent Dirichlet series sharing the functional equation of `ζ(s)³`.

## Context
- Degree 1 (Hamburger) and degree 2 at conductor 1 (Maass converse; Kaczorowski–Perelli, arXiv:2009.12329) are rigid. This theorem shows rigidity fails first in degree 3, at conductor 1.
- Literature audit:
  - No prior statement found.
  - Bochner (Ann. Math. 67, 1958) proves the equivalence of the functional equation with modular relations, not a dimension result.
  - Knopp's abundance principle (Invent. Math. 1994) concerns degree 1 with weakened singularity conditions.

## Proof

### 0. Voronoi form
- Let `G(s) = Γ_ℝ(s)³/Γ_ℝ(1−s)³`, so that `G(s)G(1−s) = 1` and `|G| = 1` on `Re s = ½`.
- Define `H` on `L²(0,∞)` by `M[Hf](s) = G(s)Mf(1−s)`, with `M` the Mellin transform on `Re s = ½`. Then `H` is a unitary involution with kernel `J(xy)`, where `M[J] = G`.
- Let `K₃ = M^{−1}[Γ_ℝ³]`. Then `HK₃(·y) = y^{−1}K₃(·/y)`.
  - **Claim 0.** Suppose `e_n = O(n^K)` and `Σ e_n K₃(ny) = y^{−1}Σ e_nK₃(n/y)` for all `y > 0`. Then the Dirichlet series lies in `W`.
  - *Proof (Hecke).* For `Re s` large, `Λ_E(s) = ∫_0^∞ θ(y)y^s dy/y` with `θ(y) = Σe_nK₃(ny)`. The terms decay like `exp(−c(ny)^{2/3})`. Split at `y = 1` and use the relation to get `Λ_E(s) = ∫_1^∞ θ(y)(y^s + y^{1−s})dy/y`, which is entire, of finite order in strips, and symmetric.

### 1. Cube-root chart and the exact factorization
- Put `x = X³/(3√3)` and `(Uf)(X) = (dx/dX)^{½}f(x)`; `U` is unitary `L²(dx) → L²(dX)`.
- `H̃ = UHU^{−1}` has kernel `k(XY)` with `k(z) = (z/√3)J(z³/27)` and Mellin multiplier `3^{w−½}G((w+1)/3)`.
- The sine transform `S` (kernel `2sin 2πXY`) has multiplier `Γ_ℝ(w+1)/Γ_ℝ(2−w)`.
- By Gauss triplication (**formal: `triplication_twist`**), `H̃ = S∘V`, where `V` is the Mellin multiplier `v(w) = R((2−w)/3)/R((1+w)/3)` with `R(z) = Γ(z/2)²/(Γ(z/2+⅓)Γ(z/2+⅔))`.
- Properties of `v`:
  - Its poles are at `w ∈ {2, 8, …} ∪ {−3, −5, …}`, and its zeros at `w ∈ {−1, −7, …} ∪ {4, 6, …}`. So `v` is holomorphic and zero-free on `−1 < Re w < 2`.
  - `|v| = 1` on `Re w = ½`.
  - `v(w) → −1` as `|Im w| → ∞`, uniformly on closed substrips (Stirling, `R(z) ∼ 2/z`).
  - Hence `κ := sup_t |v(3/2+it)| < ∞`.

### 2. The space `𝓗`
- `𝓗 := {F ∈ L²(0,∞) : XF ∈ L², and G := H̃F satisfies YG ∈ L²}`, with norm `‖F‖² + ‖XF‖² + ‖YG‖²`.
- `H̃` maps `𝓗` to itself as an involution.
- For `F ∈ 𝓗`:
  - `F = S(VG)`. The functions `G, YG ∈ L²` give `M[G]` holomorphic on `½ < Re w < 3/2` with `L²` boundary values (Mellin Paley–Wiener).
  - Hence `M[Y·VG](w) = v(w+1)M[YG](w)`, so `‖Y·VG‖ ≤ κ‖YG‖`.
  - Since `(Sφ)' = 2π·C(Yφ)` with `C` the unitary cosine transform, `F' ∈ L²` and `‖F'‖ ≤ 2πκ‖YG‖`. Likewise `‖G'‖ ≤ 2πκ‖XF‖`.
  - In particular `F` is continuous with `F(0) = 0`, as a sine transform. Its odd extension lies in `H¹(ℝ)`, and point evaluations are bounded on `𝓗`.

### 3. Lemma B (frame inequality)
Let `Λ⁺ = −Λ⁺ ∋ 0` be discrete, uniformly supercritical (`max(|λ_j|,|λ_{j+1}|)(λ_{j+1} − λ_j) ≤ a/2` for all `j`) with `a²κ² < 1`, and separated (`λ_{j+1} − λ_j ≥ c/(1+|λ_j|)`). Then, for `F ∈ 𝓗` (odd extensions),
`A₀(‖XF‖² + ‖YG‖²) ≤ Σ_{λ∈Λ⁺}(1+|λ|)(|F(λ)|² + |G(λ)|²) ≤ B₀‖F‖²_𝓗`.

*Proof.*
1. KNS Lemma 1 on the gaps (KNS (4.2.2)) gives `‖XF‖² ≤ a²(1+ε)(2π)^{−2}‖F'‖² + C_εΣ(1+|λ|)|F(λ)|²`.
2. Combined with `‖F'‖ ≤ 2πκ‖YG‖`, this gives `‖XF‖² ≤ a²(1+ε)κ²‖YG‖² + C S_F`.
3. Symmetrically, `‖YG‖² ≤ a²(1+ε)κ²‖XF‖² + C S_G`.
4. Add the two and take `ε` small. The full `𝓗`-norm is controlled through Heisenberg's inequality and the derivative bounds of §2.
5. The upper bound is KNS Lemma 2 with separation, applied to `F` and `G`. ∎

### 4. Admissible node set
- In the chart, the integers become `X_n = √3n^{1/3}`, with `X_{n+1} − X_n ≤ √3X_n^{−2}`.
- Fix `a < 1/(2κ)` and `δ = a/2·(1−η)`. For `X ≥ L₀`, select greedily from `{X_n}` the next node at distance `≥ δ/λ`. The selected set has `λΔλ ∈ [δ, δ + √3/λ] ⊂ (0, a/2)` and separation `≥ δ/λ`.
- On `[0, L₀]`, add a finite set `P` of points (not necessarily integer nodes) to make the whole symmetric set uniformly supercritical and separated. Call the result `Λ⁺`.
- Removing from `Λ⁺` any lacunary set of selected integer nodes, together with their negatives, keeps uniform supercriticality with parameter `≤ 2a` (`(2a)²κ² < 1`) and keeps separation.

### 5. Self-dual relations
- `E₋ := {F ∈ 𝓗 : H̃F = −F}` is closed, and `(I − H̃)𝓗 ⊆ E₋`.
- For `F ∈ E₋` we have `G = −F`, so by Lemma B the map `F ↦ F|_{Λ''}` (`Λ''` = `Λ⁺` with a lacunary set `{±x_i}` of integer nodes removed) is injective with closed range into `ℓ²_{1+|λ|}`.
- By the closed range theorem, each bounded functional `F ↦ F(x_i)` factors: `F(x_i) = Σ_{λ∈Λ''} α^{(i)}_λ F(λ)` on `E₋`, with `Σ|α^{(i)}_λ|²/(1+|λ|) < ∞`. In particular `|α_λ| = O((1+|λ|)^{½})`.
- Put `ν_i = δ_{x_i} − Σ α^{(i)}_λ δ_λ`, restricted to `λ > 0` via oddness. The atom at `0` is invisible.
- Then `⟨ν_i, F⟩ = 0` on `E₋ ⊇ (I − H̃)𝓗`, so **`⟨ν_i, F⟩ = ⟨ν_i, H̃F⟩` for all `F ∈ 𝓗`**.
- The `ν_i` are linearly independent: `ν_i` has coefficient 1 at `x_i` and 0 at `x_j`, `j ≠ i`.
- The finitely many coordinates at the extra points `P` impose finitely many linear conditions. So an infinite-dimensional space of relations supported on integer nodes remains.

### 6. Back to Dirichlet series
- Write a relation as `Σ_n c_n F(X_n) = Σ_n c_n (H̃F)(X_n)`. With `F = Uf` this reads `Σ_n e_n f(n) = Σ_n e_n (Hf)(n)`, where `e_n = c_n (dx/dX)^{½}(X_n) = O(n^{K})`.
- Apply this to `f = K₃(·y)`. Here `Uf ∈ 𝓗`: at `0` it behaves like `≍ X log²X`, it decays like `e^{−cX²}` in the chart, and `HK₃(·y) = y^{−1}K₃(·/y)` is of the same type.
- This yields the theta relation of Claim 0, so the Dirichlet series lies in `W`.
- Linear independence is preserved, since distinct relations have distinct coefficient sequences.
- So `dim W = ∞`. ∎

## Remarks
- **The same proof in degree 2.** Here `X ∝ x^{½}N^{−¼}` and `a = 2/√N`. It needs `N > 4κ₂²`. For the Hecke model (`V = ±I`) this is `N > 4`, i.e. Hecke's `λ > 2`. At conductor 1 it fails (`a = 2`), consistent with rigidity.
- **Degree `d ≥ 3`.** The analogous chart `X ∝ x^{1/d}` gives `a → 0`. The argument extends whenever the `d`-fold multiplication formula gives a bounded twist `v` on `Re w = 3/2`.
- Gaussian-type decay of `K₃` in the chart, and its `log²` behaviour at `0`, are standard Meijer-G asymptotics.
- **Consequences** (in-progress card §9–§20, ledger L252–L262):
  - These are datum twins of ζ with off-line zeros (120° splitting).
  - They share ζ's prime-blind zero functional (conservation law).
  - They give the datum-twin barrier (L257).

## Gates
- [x] 0 → 1 in-progress
- [x] 1 → 2 fully proven on paper (this card). Imported results: KNS Lemmas 1–2; Mellin Paley–Wiener; Hecke's theta argument; Meijer-G asymptotics of `K₃`.
- [x] 2 → 3 Lean (2026-10-01). Capstone `gammaRCube_functional_equation_abundance` in `RHTower/GammaRCubeFunctionalEquationAbundance`; axioms `propext, Classical.choice, Quot.sound`. Earlier bricks:
  - `triplication_twist`;
  - module `RHTower/DegreeThreeHankelTwistSymbol`: `twistSymbol` holomorphic on `−3 < Re w < 2`, zero-free on `−1 < Re w < 2`, unimodular on `Re w = ½`, and the symbol factorization `voronoi_multiplier_eq_sine_mul_twist`.

    - module `RHTower/DegreeThreeHankelTwistSymbolBound`: `exists_bound_twistSymbol_three_halves`, so `κ < ∞` (explicitly `|v(3/2+it)| ≤ 2e²` for `|t| ≥ 24`).

  - `HTGeometry/DirichletWirtinger` (sharp `∫|f|² ≤ (L/π)²∫|f'|²` for `f(a) = f(b) = 0`, by odd reflection and the periodic Wirtinger inequality) and `HTGeometry/StableWirtinger` (KNS Lemma 1 form: `(1+ε)²(L/π)²∫|f'|² + (1+ε⁻¹)(2 + 2(1+ε)/π²)L(|f(a)|² + |f(b)|²)`).

  - `HTGeometry/PartitionWeightedWirtinger`: Lemma B's sampling inequality on any finite supercritical partition, `∫x²|F|² ≤ (1+ε)²(a/2π)²∫|F'|² + K_ε(a/2)Σ_j max(|p_j|,|p_{j+1}|)(|F(p_j)|²+|F(p_{j+1})|²)`.
  - `RHTower/ThetaSymmetryMellinConverse`: Claim 0 (Hecke) for an arbitrary kernel (`hecke_theta_converse`). If `θ = Σe_nK(n·)` has polynomial coefficients, rapid decay at ∞ and `θ(1/y) = yθ(y)`, then `mellin θ` is entire, symmetric, and equals `(Σe_n n^{−s})·mellin K` on `Re s > A+1`.

  - `RHTower/GammaRealPowerKernel`: the kernels `K_d` (iterated multiplicative convolutions of `2e^{−πx²}`), with Mellin transform `Γ_ℝ(s)^{d+1}`, continuity, and power bounds `|K_d(x)| ≤ C_c x^{−c}` for all `c > 0`. `gammaRPow_theta_converse` is Claim 0 for `Γ_ℝ³` (`d = 2`): a theta relation with polynomial coefficients gives an entire symmetric completion `Γ_ℝ(s)³E(s)`.

  - `HTGeometry/SamplingFrameRepresentation`: the closed-range step in abstract form (`exists_weighted_sampling_representation`). Weighted frame bounds for point evaluations give every bounded functional as `Σ β_i √w_i ev_i` with `β ∈ ℓ²` (Lax–Milgram + Riesz). This is §5's relation mechanism.

  Still to do: the concrete Hilbert space `𝓗`/`E₋` with bounded point evaluations; the infinite-node Lemma B on `E₋` (finite-partition form done; needs the `F'`–`YG` Mellin-shift bound and Heisenberg control); and passing the relations to `K₃`'s theta relation.
- [ ] 3 → 4

## Formal statement (stage 3)
- `gammaRCube_theta_relations_infinite`: there are `ℂ`-linearly independent `e_r : ℕ → ℂ`, `r ∈ ℕ`, with `|e_r(n)| ≤ C_r(n+1)²` and `Σ_n e_r(n)K₂((n+1)/y) = yΣ_n e_r(n)K₂((n+1)y)` for all `y > 0`. Here `K₂ = Mellin⁻¹Γ_ℝ³`.
- `gammaRCube_functional_equation_abundance`: for each `r`, `Λ_r = mellin θ_r` is entire, satisfies `Λ_r(1−s) = Λ_r(s)`, and equals `Γ_ℝ(s)³Σ e_r(n)(n+1)^{−s}` on `Re s > 3`.
- Not formalized: "finite order in vertical strips" from the paper statement. It is standard from the integral representation, but the Lean capstone states only entire + symmetric + Dirichlet expansion.
- The formal route differs from §2–§5 of the paper proof:
  - It uses no Hilbert space `𝓗`. The class is the rapidly decaying antisymmetric chart functions `F = Mellin⁻¹_{1/2}Φ`, with `Φ` regular on `−1 < Re w < 2` and `Φ(w) = −m̃(w)Φ(1−w)` (`antiChartSpace`).
  - Relations come from `exists_coeff_of_dominated`: a linear form dominated by an `ℓ²` sampling norm is an `ℓ²` combination (Hahn–Banach + Riesz in `ℓ²`). This removes the need for upper frame bounds, closure, or separation.
  - The nodes are `nodeSeq`: equally spaced points up to `X_{N₀}`, then every other integer node. The skipped odd integer nodes are the deleted points, so no lacunary removal is needed.
  - Elimination of the non-integer points uses blocks of `m+1` skipped nodes.
- Module chain:
  - `HTGeometry`: `MellinRegularStrip`, `MellinRegularStripLinear`, `HalfLineSamplingLowerBound`, `SamplingDominatedFunctional`, `HalfLineSamplingRelations`.
  - `RHTower`: `GammaRCubeChartDerivativeBound`, `GammaRCubeAntiChartSpace`, `GammaRCubeChartNodes`, `GammaRCubeFunctionalEquationAbundance`.

- **Strengthening (Lean).** `gammaRCube_functional_equation_abundance_vanishing_below N`: for every `N`, infinitely many independent twins vanish below `N`. So ζ³ is not determined by its functional equation together with any finite set of its coefficients.
- **Divisibility rigidity (paper, ledger L273.1).** No nonzero `E ∈ W` vanishes at every zero of `ξ`. Proof: Maass's converse theorem at level 1 plus the spectral gap `λ₁(SL₂(ℤ)) > ¼`.

## Log
- 2026-10-01 — stage 3: full Lean formalization, standard axioms. Lint clean.
- 2026-10-01 — promoted from the in-progress card §6–§8 with full proof; Bochner 1958 checked (equivalence only).

## Formal plan (stage 2 → 3), 2026-10-01
Done (standard axioms):
- `triplication_twist`, `twistSymbol` (holomorphy, zero-freeness, unimodularity) and `κ < ∞`.
- `dirichlet_wirtinger_intervalIntegral`, `stable_wirtinger_intervalIntegral`, `partition_weighted_wirtinger`.
- `exists_weighted_sampling_representation` (F5).
- `gammaRPow_theta_converse` with the kernels `K_d` (F6's analytic half).

Remaining:
- **F1 — DONE** (`RHTower/GammaRCubeVoronoiL2`: `voronoiL2` for any continuous unimodular symbol, involutive when `m(ξ)m(−ξ) = 1`; `gammaRCubeVoronoi` unitary involution). Original plan text: `L²` Voronoi transform for a unimodular Mellin multiplier `G` on `Re s = ½`: `U f(u) = e^{u/2}f(e^u)` (unitary `L²(0,∞) → L²(ℝ)`), then `H_G = U⁻¹ ∘ 𝓕⁻¹ ∘ M_G ∘ reflection ∘ 𝓕 ∘ U` (mathlib `fourierTransformₗᵢ`). It is an involution when `G(s)G(1−s) = 1`.
- **F2 — DONE** (`RHTower/GammaRCubeThetaPairsL2`: `gammaRCubeVoronoi_cubeKernel`; `K₂(y·) ∈ L²`; `L²` Mellin = pointwise Mellin bridge). Original: `H_G(K₃(y·)) = y⁻¹K₃(·/y)` for `G = Γ_ℝ³(s)/Γ_ℝ³(1−s)` (Mellin of a dilate).
- **F3a — DONE** (`RHTower/GammaRCubeRegularClass`, `HTGeometry/DecayingStripVerticalShift`). The Mellin-side regular class `StripRegular`: holomorphic on `0 < Re s < 1`, rapid vertical decay. Results: abscissa independence of `mellinInv`; uniform `Γ`/`Γ_ℝ` strip decay; the theta test symbols `Γ_ℝ³(y^{−s} − y^{s−1})` are regular, antisymmetric, and invert to `K₂(yx) − y⁻¹K₂(x/y)`. Route change: the relations will be built on the antisymmetric regular class (Mellin side), so F1/F2's `L²` operator is not needed in the final chain.
- **F3 (remaining).** Cube-root chart, the space `𝓗 = {F : F, XF, Y·H̃F ∈ L²}`, `E₋ = {H̃F = −F}`. Point evaluations are bounded (`H¹(ℝ) ⊂ C₀` via odd extension).
- **F4.** Lemma B on `E₋` for infinite supercritical node sets: gaps (F4a, done in finite form), `‖F'‖ ≤ 2πκ‖Y·H̃F‖` (Mellin shift with the twist `v`), Heisenberg control, upper (Bessel) bound with separation.
- **F7.** Independence of the relations: `dim W = ∞`.
- **F3b — DONE** (`HTGeometry/MellinLinePlancherel`): `∫₀^∞|Mellin⁻¹_σΨ|²x^{2σ−1} = (1/2π)∫|Ψ(σ+it)|²`. With abscissa independence this gives the chart norms `‖F‖, ‖XF‖, ‖F'‖` as line integrals at `Re w = ½, 3/2, −½`.
- **Refined remaining chain (2026-10-01):**
  - (c) chart symbol `Φ(w) = c(w)Ψ((w+1)/3)` and the derivative identity `F' = Mellin⁻¹(−(w−1)Φ(w−1))`;
  - (d) `|u·m̃(u)| ≤ 2πκ` on `Re u = −½`, from `voronoi_multiplier_eq_sine_mul_twist`, `|u·Γ_ℝ(u+1)/Γ_ℝ(2−u)| = 2π`, and `κ`;
  - (e) chart antisymmetry;
  - (f) Wirtinger on the infinite node partition: graded points `√(ja/2)` near 0, then a greedy sparse subset of integer chart nodes;
  - (g) Lemma B lower bound;
  - (h) Bessel upper bound and pointwise bounds;
  - (i) Hilbert closure, relations, elimination of the extra points (`|P|+1` deleted nodes per relation), coefficient bounds, theta relation, `gammaRPow_theta_converse`, independence.
- **(d), (e) — DONE** (`RHTower/DegreeThreeHankelChartMultiplier`): `|u·m̃(u)| ≤ 2πκ` on `Re u = −½`; chart symbol `Φ(w) = 3^{w/2−3/4}Ψ((w+1)/3)` with `Φ(w) = −m̃(w)Φ(1−w)`.
- **(c) — DONE.**
  - `HTGeometry/MellinRegularStrip`: general strip class; abscissa independence; `w·Φ` regular; `d/dx Mellin⁻¹Φ = x⁻¹Mellin⁻¹(−wΦ)`.
  - `RHTower/GammaRCubeChartDerivativeBound`: `∫|F'|² ≤ K²∫X²|F|²` for antisymmetric chart-regular `Φ`, with `K = 2πκ`.
  - Remaining: (c') chart symbol of `Ψ` regular and the chart function `= 3^{−¼}X f(X³/(3√3))`; (f) infinite-partition Wirtinger; (g) lower bound; (h) Bessel and pointwise bounds; (i) assembly.
