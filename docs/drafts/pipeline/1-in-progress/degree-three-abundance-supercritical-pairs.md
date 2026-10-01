# Degree-three functional equations are supercritical: abundance of Dirichlet series and the fake-ζ³ door

- **ID:** degree-three-abundance-supercritical-pairs
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper, via an imported theorem) + CONJECTURE (the `Γ_ℝ(s)³` case, i.e. ¬C1)
- **Source:** producer ledger `hf-positive-hodge-attack/krein-producer-loops.md` L222–L226, L231, L245, L249, L250; Kulikov–Nazarov–Sodin, *Fourier uniqueness and non-uniqueness pairs* (arXiv:2306.14013; J. Math. Phys. Anal. Geom. 21 (2025) 84–130)
- **Statement:** A Hecke-type functional equation of degree `d ≥ 3` (single Gamma factor `Γ_ℝ(dw)`), at any conductor, has an infinite-dimensional space of Dirichlet-series solutions. Conjecturally the same holds for `Γ_ℝ(s)³` at conductor 1, which would make ζ³ non-unique (C1 false).

## Goal
A fake ζ³ with all its zeros on the critical line gives an integer-supported Weil-positive weight system `lam = Λ_F/3` for ζ's exact archimedean datum and pole (L222/L225). That is a producer independent of RH for ζ. The first obstruction is existence, i.e. C1 (is `V₃ = ℂζ³`?). This card supplies:
1. a structural reason to expect `dim V₃ = ∞`;
2. a proof of the corresponding abundance for Hecke-type degree-`d` functional equations;
3. a concrete analytic route to ¬C1.

## 1. The Hecke threshold is the Kulikov–Nazarov–Sodin critical density [P]
- **Background.** KNS call a pair of symmetric discrete sets `(Λ, M)` supercritical (with `p = q = 2`) when `limsup |λ_j|(λ_{j+1} − λ_j) < ½`, and likewise for `M`. They prove:
  - (Thm 1) supercritical pairs are Fourier uniqueness pairs for the Schwartz space;
  - (Cor 2) uniqueness upgrades to an interpolation formula;
  - (§2.3) hence the space `N(Λ, M)` of tempered locally finite measures `ν` with `supp ν ⊆ M` and `supp ν̂ ⊆ Λ` is **infinite-dimensional**;
  - (§7.3) for subcritical pairs `N(Λ, M)` is finite-dimensional.
- **Degree-2 dictionary.** Take `Λ = M = {±c√n}`. Then `λ_j(λ_{j+1} − λ_j) → c²/2`, so `a = c²`.
  - A measure `Σ α_n δ_{±c√n}` is the Fourier side of the theta series `Σ α_n e^{πic²nz}`, which has period `λ_H = 2/c²`. Hence **`a = 2/λ_H`**.
  - KNS critical `a = 1` ⟺ `λ_H = 2`, Hecke's threshold (the theta group, the Radchenko–Viazovska case).
  - Supercritical `a < 1` ⟺ `λ_H > 2`: infinite covolume and Hecke's infinite-dimensional spaces.
  - Subcritical `a > 1` ⟺ `λ_H < 2`: finite-dimensional.
  - KNS's density dichotomy therefore reproduces Hecke's group-theoretic dichotomy exactly, with no modular forms used.
- **Degree `d` (Fourier model).** For nodes `{±c n^{1/d}}`, `λ_j(λ_{j+1} − λ_j) ≍ (c²/d) j^{2/d − 1} → 0` for `d ≥ 3`. The pair is supercritical **for every `c`**, i.e. at every conductor.
- **Phase-space check for the exact `Γ_ℝ(s)^d` transform.** The Voronoi kernel of `Γ_ℝ(s)^d / Γ_ℝ(1−s)^d` has stationary phase at `xy = (t/2π)^d`.
  - A phase-space cell `(x, t)` is controlled by the `x`-nodes `ℕ` when `t ≲ 2πx`, and by the `y`-nodes when `t ≲ 2πy`.
  - For `d = 1` an infinite region is uncontrolled; Poisson summation is the only relation.
  - For `d = 2` the threshold depends on the conductor (as above).
  - For `d = 3` only a bounded low-frequency region is uncontrolled. The integer nodes heavily over-control phase space, which is the supercritical signature.

## 2. Theorem (abundance for Hecke-type degree-`d` equations) [P, given KNS]
**Statement.** Let `d ≥ 3` and `c > 0`. There are infinitely many linearly independent pairs `(A, B)` of Dirichlet series `A(w) = Σ_{n≥1} α_n n^{−w}`, `B(w) = Σ_{n≥1} β_n n^{−w}` with polynomially bounded coefficients such that:
- `Λ_A(w) = Γ_ℝ(dw) c^{−dw} A(w)` and `Λ_B` extend to entire functions, bounded in vertical strips of finite width away from `|Im w| → ∞` growth of finite order;
- `Λ_A(w) = c^{−1} Λ_B(1/d − w)`.

Recentring by `a_n = α_n n^{(d−1)/(2d)}` gives ordinary Dirichlet series with a symmetric functional equation `u ↔ 1 − u` and Gamma factor `Γ_ℝ(du − (d−1)/2)`.

**Proof.**
1. *Setup.* Let `Λ = {±c n^{1/d} : n ≥ 1}` (omit `0`). This pair `(Λ, Λ)` is supercritical (§1).
2. *Independent family.* Choose a lacunary set `{k_i}` (e.g. `k_i = 2^i`). Then `Λ* = Λ ∖ {±λ_{k_i}}` is still supercritical (KNS Claim 1 argument).
   - KNS Corollary 2 for `(Λ*, Λ)`, evaluated at `x = ±λ_{k_i}`, gives measures `ν^{(i)} ∈ N(Λ, Λ)`.
   - `ν̂^{(i)}` has coefficient 1 at `±λ_{k_i}` and 0 at `±λ_{k_j}` for `j ≠ i`, so the family is linearly independent.
   - Their even parts are independent for the same reason.
3. *Coefficient growth.* KNS's bound `sup|a_λ|, sup|b_μ| ≤ C(1+|λ|)^{O(1)}` gives polynomially bounded coefficients.
4. *Theta identity.* Pair `ν` with the Gaussians `f(x) = e^{−πtx²}` (`f̂(ξ) = t^{−½}e^{−πξ²/t}`). This gives
   `2Σ α_n e^{−πc²n^{2/d}t} = t^{−½}·2Σ β_n e^{−πc²n^{2/d}/t}`.
5. *Functional equation.* Mellin-transform and split at `t = 1`, as in Hecke's argument. This gives entire continuation of `Λ_A, Λ_B`, finite order, and `Λ_A(w) = c^{−1}Λ_B(1/d − w)`, using `∫θ_α(t)t^{s/2}dt/t = Γ_ℝ(s)c^{−s}A(s/d)` with `s = dw`. ∎

- **Remaining check before stage 2.** Confirm from KNS §7 that the measures in Corollary 3 can be taken with `0 ∉ Λ`, so that no polar terms appear. Their Claim 1 allows removing points freely.
- **Literature status.**
  - For `d = 2` the theorem is Hecke's abundance theorem for `λ_H > 2`, here re-derived analytically.
  - No reference found for `d ≥ 3`. Searched: KP survey (arXiv:1605.02354); KP degree-2 classification (arXiv:2009.12329); Bochner, Ann. Math. 67 (1958); Knopp's abundance principle; Radchenko–Viazovska and Gerbelli-Gauthier–Venkatesh.
  - Knopp (Invent. Math. 117, 1994; "abundance principle") gets infinitely many solutions of Riemann's degree-1 functional equation only after weakening the singularity conditions (rational period functions, extra poles). That is a different regime from §2, which has degree `≥ 3` and entire `Λ_A`.
  - **Novelty unconfirmed:** Bochner (Ann. Math. 67, 1958, multiple Gamma factors) has not been read. It must be checked before any claim.

## 3. Conjecture (¬C1) and the route [OPEN CORE]
- **Conjecture.** `dim V₃ = ∞`, where `V₃` is the space of Dirichlet series `F` with `Γ_ℝ(s)³F(s)` meromorphic (poles only at `0, 1`), of finite order, and symmetric under `s ↔ 1 − s`. Equivalently, the Hankel transform `H₃` with Mellin multiplier `Γ_ℝ(s)³/Γ_ℝ(1−s)³` has an infinite-dimensional space of tempered measures `ν` with `ν` and `H₃ν` both supported on `ℕ`.
- **Route.** Transfer KNS's Poincaré–Wirtinger mechanism from the Fourier transform to `H₃`.
  - Nodes `ℕ` have unit spacing in `x`.
  - `H₃` intertwines multiplication by `x²` with the third-order operator `(2π)^{−3}·(−y^{−2}θ³)`, from `θ³K₃ = −(2π)³y²K₃` (L245).
  - The phase-space count in §1 says the two node sets control everything except a bounded region.
  - arXiv:2509.14953 (spectral criteria for uniqueness pairs of unitary transforms, Hankel case included) is the nearest existing machinery. The `Γ_ℝ³` kernel needs a third-order replacement for its Sturm–Liouville input.
- **Then the producer question.** An element of `V₃` with all its zeros on the critical line gives the producer `Λ_F/3`.
  - L224's phase-twisted mean-square identity says such `F` must have zeros clustered in near-triples, or super-Lindelöf mean square. So abundance is necessary but not sufficient.
  - The second step is a real-rootedness selection inside the infinite-dimensional `V₃`.
- **How it could fail.** `H₃` might have an exact hidden rigidity (an analogue of the theta-group symmetry) that makes `N_{H₃}(ℕ, ℕ)` finite even though phase space is over-controlled. That would prove C1 and close the fake-ζ³ door.

## Gates
- [x] 0 → 1  in-progress: dictionary (§1), Fourier-model theorem (§2), open core stated (§3)
- [ ] 1 → 2  fully-proven: §2 dependency-closed against KNS §7 (removal of `0`, parity); novelty audit against Bochner 1958 and Knopp
- [ ] 2 → 3  formalized: §2 in Lean, with KNS imported as an explicit hypothesis or built
- [ ] 3 → 4  publication-ready

## Log
- 2026-10-01 — created; dictionary `a = 2/λ_H` and degree-`d` supercriticality found during producer loop L250.

## 4. The `Γ_ℝ(s)³` transform is a compact-type perturbation of the odd Fourier model [P, asymptotic computation]
- **Voronoi-kernel phase.** For `J_d(y) = (1/2πi)∫[Γ_ℝ(s)/Γ_ℝ(1−s)]^d y^{−s} ds` on `Re s = ½`:
  - The phase is `2dθ(t) − t log y`, with `θ` the Riemann–Siegel theta function.
  - The stationary point is `t₀ = 2π y^{1/d}`, the phase value there is `−2πd y^{1/d} − dπ/4`, and the second derivative is `d/t₀ > 0`.
  - Adding the conjugate branch gives
    `J_d(y) = C_d · y^{−½ + 1/(2d)} · cos(2πd·y^{1/d} + (d−1)π/4) · (1 + O(y^{−1/d}))`.
  - Checks: `d = 1` gives `cos(2πy)` (Poisson); `d = 2` gives `cos(4π√y + π/4)` (Voronoi for `d(n)`).
- **Chart.** Put `X = √d·x^{1/d}` and `Y = √d·y^{1/d}`, so that `2πd(xy)^{1/d} = 2πXY`. With the unitary Jacobian `F(X) = (dx/dX)^{½} f(x)`, the transform `H_d` has kernel `cos(2πXY + (d−1)π/4)·(1 + O((XY)^{−1}))`. The nodes `n ∈ ℕ` become `X_n = √d·n^{1/d}`.
- **`d = 3`.** The phase shift is `π/2`, so the kernel is `−sin(2πXY)·(1 + O((XY)^{−1}))`. This is the Fourier transform on **odd** functions, plus a correction that decays at high `XY`.
  - The node pair `{±√3 n^{1/3}}` is supercritical: `λ_j(λ_{j+1} − λ_j) ≍ j^{−1/3} → 0`.
  - KNS applies to odd Schwartz functions. The odd part of `N(Λ, Λ)` is infinite-dimensional: remove `±λ_k`, evaluate the interpolation formula at `±λ_k` and subtract.
- **Refined route to ¬C1.**
  - (a) Phase identification: done above.
  - (b) **[OPEN]** Factor `H₃ = S∘(I + K)` in the X-chart, with `S` the Fourier sine transform and `K` compact between KNS's weighted spaces `H_{s,2,2}` (the `O((XY)^{−1})` correction is order `−1` at high frequency; the low-frequency part is handled separately).
  - (c) KNS's frame inequality (Thm 2) for `S` with the odd nodes, then a Fredholm perturbation. The sampling map `f ↦ (f|_ℕ, H₃f|_ℕ)` is then injective modulo a finite-dimensional space, with closed range.
  - (d) Remove a lacunary infinite set of nodes; the pair stays supercritical. Each removed node gives an independent tempered measure `ν` with `ν` and `H₃ν` supported on `ℕ`. So `N_{H₃}(ℕ, ℕ)` is infinite-dimensional, and the pair space of `V₃` is infinite-dimensional.
  - (e) Split by the involution `H₃` (eigenvalues `±1`) to get infinite-dimensional `V₃` with root number `+1` or `−1`. Showing the `+1` part is infinite is a separate check.
- **Consistency.** For `d = 2` the same chart gives Hecke's `λ_H = 2` threshold (§1), and the phase shift `π/4` is the Bessel `Y₀`/`K₀` Voronoi kernel, as it should be.
- 2026-10-01 — §4 added: Maslov phase `(d−1)π/4`; the `d = 3` transform is a perturbation of the odd Fourier model; open core sharpened to the compactness lemma (b).

## 5. Real-rootedness constraints on a fake ζ³ [P]
- **Near ζ³ (cube-root splitting).** Let `F = ζ³ + εE` with `E ∈ V₃`, and let `ρ₀` be a simple zeta zero with `E(ρ₀) ≠ 0`.
  - The triple zero splits into `ρ₀ + w^{1/3}ωᵏ` (`k = 0, 1, 2`), with `w = −εE(ρ₀)/ζ'(ρ₀)³`.
  - Three points spaced at `120°` cannot all lie on the vertical line through `ρ₀`, so `F` has off-line zeros.
  - Avoiding this at every zero forces `E = ζE₁` with `E₁` in the degree-2 space, i.e. `E₁ ∈ ℂζ²` (Maass converse), so `E ∝ ζ³`.
  - **No small perturbation of ζ³ inside `V₃` satisfies RH.** This sharpens L226.
- **Far from ζ³ (L224).** For the producer `lam = Λ_F/3`, the producer's own zeta function is `F^{1/3}`. The phase-twisted mean square needs `∫|F(½+it)|^{2/3} w ≥ (R² − o(1))∫ w log t`.
  - So a real-rooted fake ζ³ must be cube-like in mean: `|F|^{2/3}` of ζ-size, with zeros in near-triples.
  - An Euler-product (Selberg-class) degree-3 function would give `(log T)^{1/9}` and fail. Fake elements of `V₃` have no Euler product, so this heuristic does not apply to them.
- **Step after ¬C1.** Select a real-rooted, cube-like element of the infinite-dimensional `V₃` (or of `V_k`, `k ≥ 3`, which has more room).

## 6. Theorem A (¬C1) — proof skeleton, an exact factorization, and the one remaining lemma
**Theorem A (target).** The space of Dirichlet series `E = Σ e_n n^{−s}` (polynomially bounded coefficients) with `Γ_ℝ(s)³E(s)` entire of finite order and `Γ_ℝ(s)³E(s) = Γ_ℝ(1−s)³E(1−s)` is infinite-dimensional. Hence `V₃ ⊋ ℂζ³` (take `ζ³ + E`), and C1 fails.

**Step 0 (Voronoi form) [P].**
- Put `G(s) = Γ_ℝ(s)³/Γ_ℝ(1−s)³` and `(Hf)(y) = ∫f(x)J(xy)dx`, with `M[J] = G`.
  - `H` is a unitary involution on `L²(0,∞)`: `M[Hf](s) = G(s)Mf(1−s)` and `G(s)G(1−s) = 1`.
  - Shifting contours gives `Σ e_n f(n) = Σ e_n (Hf)(n)` for `f ∈ C_c^∞(0,∞)`.
- Conversely, take test functions `f_y = K₃(·y)` (`M[K₃] = Γ_ℝ³`), for which `Hf_y = y^{−1}K₃(·/y)`.
  - The identity for them is the theta relation `Σe_nK₃(ny) = y^{−1}Σe_nK₃(n/y)`.
  - Hecke's argument then returns the functional equation with entire continuation.
- So Theorem A ⟺ an infinite-dimensional space of tempered measures `ν = Σe_nδ_n` with `Hν = ν`.

**Step 1 (exact factorization) [P].**
- In the chart `X = √3x^{1/3}`, with `(UF)(X) = (dx/dX)^{½}f(x)`, the operator `H̃ = UHU^{−1}` has kernel `k(XY)` with `k(z) = (z/√3)J(z³/27)`, and `M[k](w) = 3^{w−½}G((w+1)/3)`.
- The sine transform `S` (kernel `2sin(2πXY)`) has `M[2sin(2π·)](w) = Γ_ℝ(w+1)/Γ_ℝ(2−w)`.
- Gauss's triplication formula `Γ(3z) = (2π)^{−1}3^{3z−½}Γ(z)Γ(z+⅓)Γ(z+⅔)` gives **exactly**
  `M[k](w) / M[2sin(2π·)](w) = R(v)/R(1−v)`, with `v = (w+1)/3` and `R(v) = Γ(v/2)²/(Γ(v/2+⅓)Γ(v/2+⅔))`.
  - All powers of 3 cancel.
- So `H̃ = S∘V`, where `V` is the Mellin multiplier `w ↦ R(v')/R(1−v')`, `v' = (2−w)/3`. On the critical line it is unimodular, holomorphic for `−3 < Re w < 2`, and `V = −I + O(1/|Im w|)` uniformly on that strip (Stirling: `arg R(v) → ∓π/2`).
- `V` commutes with `X∂_X`, and its kernel in `log X` decays exponentially (Paley–Wiener). It is bounded on every KNS space `H_{s,2,2}` with `½ ≤ s < ¾`, since `∂_X V = (X^{−1}VX)∂_X` is again a multiplier on a shifted line inside the strip.

**Step 2 (the remaining lemma) [OPEN].** A Kulikov–Nazarov–Sodin frame inequality modulo compact operators for the twisted transform `S∘V`:
- **Statement.** For a separated supercritical symmetric subset `Λ'` of the nodes `{±√3n^{1/3}}`,
  `‖F‖_{H_{s,2,2}} ≤ C(‖F|_{Λ'}‖_w + ‖(SVF)|_{Λ'}‖_w) + ‖KF‖`, with `K` compact, for odd `F`.
- **Correction to §4(b).** `V + I` is **not** compact on `H_{s,2,2}`. Smooth bumps at large scale with low Mellin frequency are an obstruction (`‖X^{2s}(V+I)F_R‖ ↛ 0`).
- **Route.** Split by Mellin frequency.
  - High frequency: `V = −I + small`, and KNS for `S` applies.
  - Low frequency `|t| ≤ T`: the functions are smooth on log scale. At large `X` the dense nodes `Λ'` control them alone, by the weighted Poincaré–Wirtinger inequality (KNS §3). At large `Y` the nodes control `SVF` alone.
  - The leftover region (bounded `t`, `X`, `Y`) gives the compact `K`.
  - `V` is log-scale-local, so this phase-space partition commutes with it up to exponentially small errors.

**Step 3 (Fredholm ⇒ relations) [P, given Step 2].**
- Step 2 makes the sampling map semi-Fredholm (finite-dimensional kernel, closed range), and the same holds after removing a lacunary infinite subset `{x_i}` of nodes.
- Each `f ↦ f(x_i)` is then a combination of the remaining samples plus finitely many kernel corrections. Combinations of `K+1` such relations cancel the corrections.
- This gives infinitely many independent tempered measures `ν` on nodes with `⟨ν, F⟩ = ⟨ν', H̃F⟩`.

**Step 4 (root number +1) [P, given Step 2].** Run Step 3 on the closed subspace `E₋ = {F : H̃F = −F}`, sampling only `F` on `Λ' ∪ M'`.
- For `F ∈ E₋`: `SVF = −F`, so `½(F + SF) = F − ½S(V+I)F`, and the KNS frame on `{SG = G}` transfers.
- A relation annihilating `E₋ = Range(I − H̃)` satisfies `(I − H̃)ν = 0`, i.e. `H̃ν = ν`: root number `+1`.
- The same argument on `E₊` gives root number `−1`.

**Status.** Theorem A reduces exactly to the frame-modulo-compact lemma (Step 2) for `S∘V`, with `V` explicit (triplication formula). Every other step is standard or from KNS.
- 2026-10-01 — §6: exact factorization `H̃ = S∘V`; the compactness shortcut is refuted; the open core is Step 2.

## 7. Step 2 is proved: KNS's toy-model argument works for any twisted transform `S∘V` [P]
The compactness route of §4(b) is unnecessary. KNS's proof of their Theorem 2A (§4.2, `p = q = 2`, uniformly supercritical) uses the Fourier transform only through Plancherel, `‖f'‖ = 2π‖ξf̂‖`. With `H̃ = S∘V` this becomes an inequality with a constant `κ`, and the super-density of the cube-root nodes absorbs `κ`.

**Lemma B (frame inequality for `S∘V`).**
- Let `V` be a Mellin multiplier with symbol `v(w)` holomorphic and bounded on `½ ≤ Re w ≤ 3/2`, with `|v| = 1` on `Re w = ½`, and put `κ = sup_t |v(3/2+it)|`. Let `H̃ = S∘V` be an involution.
- Let `Λ⁺ ⊂ ℝ` be symmetric, separated (`λ_{j+1} − λ_j ≥ c/(1+|λ_j|)`) and uniformly supercritical: `max(|λ_j|,|λ_{j+1}|)(λ_{j+1}−λ_j) ≤ a/2` for all `j`, with `a²κ² < 1`.
- Then for all odd `F` with `F, F', XF, G, G', YG ∈ L²` (where `G = H̃F`):
  `A₀‖F‖²_* ≤ Σ_{λ∈Λ⁺}(1+|λ|)|F(λ)|² + Σ_{μ∈Λ⁺}(1+|μ|)|G(μ)|² ≤ B₀‖F‖²_*`, with `‖F‖²_* = ‖XF‖² + ‖F'‖² + ‖YG‖² + ‖G'‖²`.

**Proof.**
1. *Wirtinger on gaps.* KNS Lemma 1 applied on each gap of `Λ⁺`, exactly as in their (4.2.2), gives
   `∫X²|F|² ≤ a²(1+ε)(2π)^{−2}∫|F'|² + C_ε Σ(1+|λ|)|F(λ)|²`. This step is real-variable only.
2. *Plancherel for the sine transform.* Since `F = H̃G = S(VG)` and `(Sφ)' = 2π·C(Yφ)` with `C` the unitary cosine transform, `∫|F'|² = 4π²‖Y·VG‖²`.
3. *Mellin shift.* `M[Y·VG](w) = v(w+1)M[YG](w)`, so `‖Y·VG‖ ≤ κ‖YG‖`. This uses holomorphy of `v` on the strip and the Paley–Wiener property of `M[G]` there.
4. *Symmetric bound.* Steps 1–3 give `‖XF‖² ≤ a²(1+ε)κ²‖YG‖² + C S_Λ`. Symmetrically, with `G = S(VF)`, `‖YG‖² ≤ a²(1+ε)κ²‖XF‖² + C S_M`.
5. *Conclusion.* Add the two bounds and choose `ε` with `a²(1+ε)κ² < 1`. Use `‖F'‖ ≤ 2πκ‖YG‖` and `‖G'‖ ≤ 2πκ‖XF‖` for the derivative terms. The upper bound is KNS Lemma 2 plus separation, unchanged. ∎

**Application to `Γ_ℝ(s)³`.**
- Here `v(w) = R((2−w)/3)/R((1+w)/3)` (§6, Step 1). It is holomorphic on `−3 < Re w < 2` and unimodular on `Re w = ½`. On `Re w = 3/2` its arguments have real parts `1/6` and `5/6`, so there are no poles and `|v| → 1`. Hence `κ < ∞`.
- The integer nodes `X_n = √3n^{1/3}` satisfy `X_n(X_{n+1} − X_n) ≈ n^{−1/3} → 0`.
- A greedy separated subset `Λ'` (spacing `≈ δ/X`) is uniformly supercritical with parameter `≈ 2δ` beyond `n₀`. Adding finitely many points near `0` makes it uniformly supercritical everywhere with `a < 1/κ`.
- Lemma B then holds, and the finitely many added points are cancelled later by linear combinations.

## 8. Theorem A (C1 is false) — proof assembled [P]
1. **Frame (Lemma B).** The sampling map `F ↦ (F|_{Λ⁺}, H̃F|_{Λ⁺})` is injective with closed range on the space `𝓗` (§7).
2. **Self-dual relations.** Restrict to `E₋ = {F ∈ 𝓗 : H̃F = −F}`; there `G = −F`, so sampling `F` alone on `Λ⁺` is injective with closed range.
   - Remove a lacunary infinite set `{x_i} ⊂ Λ'` of integer nodes. The set stays uniformly supercritical with parameter `≤ 2a` (choose `2a < 1/κ` from the start) and stays separated.
   - By the closed-range theorem, each evaluation `F ↦ F(x_i)` on `E₋` is a combination of the remaining samples with polynomially bounded coefficients. This gives measures `ν_i = δ_{x_i} − Σ α^{(i)}_λ δ_λ` annihilating `E₋`.
   - `E₋ ⊇ (I − H̃)𝓗`, so `⟨ν_i, F⟩ = ⟨ν_i, H̃F⟩` for all `F ∈ 𝓗`.
   - The `ν_i` are linearly independent: `ν_i` has coefficient 1 at `x_i` and 0 at `x_j`, `j ≠ i`.
   - Finitely many linear combinations remove the atoms at the finitely many added non-integer points. An infinite-dimensional space of relations supported on integer nodes remains.
3. **Back to `x` and Dirichlet series.** Through the unitary chart, `Σ e_n f(n) = Σ e_n (Hf)(n)` with polynomially bounded `e_n`, for all `f` with `Uf ∈ 𝓗`.
   - This class contains `f_y = K₃(·y)`: in the chart `U f_y ≍ X log²X` at `0` and Gaussian decay `e^{−c X²}` at `∞`, and `Hf_y = y^{−1}K₃(·/y)` is of the same type.
   - So the theta relation `Σe_nK₃(ny) = y^{−1}Σe_nK₃(n/y)` holds. Hecke's argument gives `Γ_ℝ(s)³E(s)` entire, of finite order, and symmetric.
4. **Conclusion.** `dim{E : Γ_ℝ³E entire and symmetric} = ∞`. Hence `V₃ ⊋ ℂζ³` (`ζ³ + E ∈ V₃`). **C1 is false.** ∎

**Checks.**
- *Degree 2.* The nodes `√(2n/√N)` have `a = 2/√N`, so Lemma B needs `N > 4κ²`. For `V = ±I` (Hecke's `Γ(s)` model) this is `N > 4`, i.e. `λ_H > 2`, Hecke's abundance threshold. At conductor 1 it fails (`a = 2`), consistent with `V₂ = ℂζ²`.
- *Degree 1.* The nodes `n` have `a = ∞`: the method fails, consistent with Hamburger.
- *Degree 3.* `a → 0`, so it succeeds at every conductor.

**Before stage 2.** Write out the function-space details:
- `𝓗` is a Hilbert space on which `H̃` acts as an involution;
- `V` is bounded on `𝓗`;
- KNS Lemmas 1–2 apply to odd functions with the same constants;
- point evaluation is bounded on `𝓗`;
- `U f_y ∈ 𝓗` and Hecke's continuation with polynomially bounded coefficients.

Also check a numeric value of `κ`. The literature audit is still open: no prior statement of degree-3 non-uniqueness has been found.

- 2026-10-01 — §7–§8: Lemma B (KNS for `S∘V` with constant `κ`) and Theorem A assembled. **C1 is false (paper level).** Next: details, then the producer step (a real-rooted element of `ζ³ + E`).

## 9. The producer step inside `V₃`: what a real-rooted fake ζ³ must look like [P]
Producer requirement: `F ∈ V₃` with the triple pole, zero-free on `σ > ½`. Then `lam = Λ_F/3` is Weil-positive for ζ's exact datum.
- **(a) A small perturbation fails at low height.**
  - Write `F = ζ³ + E` (`E` cuspidal). If `|E| ≤ η` on `σ = 1+ε`, then by the functional equation `|E(−ε+it)| ≲ η|t|^{3(½+ε)}`, and Phragmén–Lindelöf makes `E` small on the strip for `|t| ≤ T₀(η)`.
  - At every zeta zero `ρ` below `T₀` with `E(ρ) ≠ 0`, the triple zero of ζ³ splits at `120°` with radius `|E(ρ)/ζ'(ρ)³|^{1/3}`, which forces off-line zeros (§5).
  - `E` cannot vanish at all zeta zeros (that forces `E ∝ ζ³`, §5). So **a producer `F ∈ V₃` must have `E` at least comparable to ζ³ somewhere on `σ > 1`**; smallness only at large height does not help low zeros.
- **(b) Zero-freeness on `σ > 1` (Bohr).**
  - `F` zero-free on `σ ≥ σ₀ > ½` means its Bohr lift `F̃(σ; z)`, a power series in the prime variables, is zero-free on the polydisc image.
  - So `F = exp(H)` with `H` a Dirichlet series converging there in Bohr's sense, which is Euler-like structure. KNS-built elements of `W` are produced by a linear closed-range argument and have no reason to be exponentials.
  - Selecting one is a nonlinear (multiplicative) problem inside the linear space `V₃`.
- **(c) Boundary.** The phase of `Ξ_F = e^{3iθ}F(½+it)` must advance by `π` per zero with no off-line zeros. The L224 dichotomy applies: either near-triple phase locking (then the phase-lock rigidity of MUST-617 pushes toward `F = ζ³`), or super-Lindelöf `∫|F|^{2/3}`. Elements of `W` have polynomially bounded but possibly large coefficients, so the super-Lindelöf branch is not excluded.
- **Status.** The existence door (C1) is open. A producer needs an exponential-type element of `ζ³ + W` that is large in `σ > 1` with all zeros real. No mechanism inside the KNS construction produces exponential structure; this is the new open core.
- 2026-10-01 — §9: producer-step constraints. Next: is there a multiplicative (log-convex) version of the KNS frame argument, i.e. relations for `log F` rather than `F`?

## 10. Corollary for slack producers (PBAP_c, ledger L239) [P, given Lemma B in degree 2]
- **Lemma B in degree 2.** In the chart `X = √2x^{½}N^{−¼}`, with `V₂` the duplication-formula multiplier and `κ₂ = sup|v₂(3/2+it)|`, Lemma B applies once `N > 4κ₂²`. So the Maass-type space (`Γ_ℝ(s)²`, conductor `N`) is infinite-dimensional for `N > 4κ₂²`.
  - For the model `V = ±I` the threshold is exactly Hecke's `N > 4`.
- **Slack producers.** A member `F` of that space with a double pole and all zeros on the critical line gives `lam = Λ_F/2`. This is an integer-supported, full-cone Weil-positive system for ζ's archimedean datum plus the constant `c = ¼ log N`, with the exact pole.
  - So **`PBAP_c` for `c > ¼log(4κ₂²)` reduces to RH for one member of an infinite-dimensional family.** Before this, L239 recorded existence as open at every `c` with no family to search.
- **Same open core in both degrees.** Select a real-rooted, exponential-type element of an infinite-dimensional Hecke/KNS family.
  - Degree 2 at large conductor gives a slack producer.
  - Degree 3 at conductor 1 gives an exact producer.

## 11. A constructive route to the producer: Gram-law design inside `V₃` [CONJECTURE + reduction lemma P]
- **Why abundance makes design possible.** Every `F ∈ V₃` with real coefficients has `Z_F(t) = e^{3iθ(t)}F(½+it)` real. Simple real zeros of a real function persist and stay real under small real perturbations inside `V₃`; only multiple zeros (ζ³'s triple zeros) split off the line.
  - Define degree-3 Gram points `g_k` by `3θ(g_k) = kπ`. Then `F(½+ig_k) = (−1)^k Z_F(g_k)`.
- **Lemma G (Gram positivity ⇒ RH for `F`) [P].** Let `F ∈ V₃` have the triple pole. Suppose:
  - (i) `F(½+ig_k) > 0` for all `k ≥ k₀`;
  - (ii) for every `k ≥ k₀`, `F(σ+ig_k)` has no zero and no net winding for `½ ≤ σ ≤ 2`, and `F(2+it)` stays in a fixed half-plane;
  - (iii) below `g_{k₀}` the zero count matches the real sign changes.
  - Then every zero of `Ξ_F` is real.
  - *Proof.* The argument principle on `[−1, 2] × [0, g_K]` gives `N_F(g_K) = (3θ(g_K) + Δ arg)/π + c` with `Δ arg = 0` by (ii). By (i), `Z_F` changes sign in each Gram interval, so there are `≥ K + O(1)` real zeros up to `g_K`; (iii) fixes the constant. Hence `N_F(g_K) =` (number of real zeros) for all `K`. ∎
- **Producer consequence.** Such `F = ζ³ + E` gives `lam = Λ_F/3`: an integer-supported, full-cone Weil-positive system for ζ's exact archimedean datum and pole, **independent of RH for ζ**.
- **Conjecture P (Gram design).** There is `E ∈ W` (cuspidal part of `V₃`) with `F = ζ³ + E` satisfying (i)–(iii).
  - All conditions are open (strict inequalities on compact segments). Gram points number `≍ (3/2π)log t` per unit height, while the free coefficients up to height `t` number `≍ t^{3/2}` (§1, L245).
- **Proof plan.**
  - (a) **Finite-height surjectivity.** The evaluation functionals `E ↦ E(σ+ig_k)` (finitely many points, modulo the conjugate pairing from the functional equation) are linearly independent on `W`. Equivalently, no combination of the corresponding Mellin kernels, sampled on integer nodes, lies in `T(E₋) + ` (FE-symmetric combinations). This is a finite-dimensional statement inside the KNS frame of §7–§8.
  - (b) **Uniform norm control (main obstacle).** Build `E = Σ_j E_j` multiscale, with `E_j` serving heights `[T_j, T_{j+1}]` and negligible below `T_j`. Mellin height `t` corresponds to phase-space hyperbolae `xy ≍ (t/2π)³` (§1, §4), and relations built from nodes at large `x, y` act at large heights.
  - (c) **Limit.** Locally uniform compactness plus Hurwitz preserves (i)–(iii) in the limit, giving `F` with all zeros real.
- **Consistency with L224.** `E` dominant means `|F|^{2/3}` is super-Lindelöf. That is the allowed branch (ii) of L224, so no phase locking is needed.
- 2026-10-01 — §11: Gram-law design route; reduction Lemma G; Conjecture P with plan (a)–(c). This is the first constructive plan for a producer that does not presuppose RH for ζ.

## 12. Calibration: what Conjecture P would imply for ζ [P]
- **Agreement on prime-blind tests.** If `F ∈ V₃` has all zeros real and `lam_F = Λ_F/3` is a producer, then for every prime-blind positive-definite `h` (`h(±log n) = 0`, `n ≥ 2`), the prime terms vanish for both systems. Hence
  `Σ_{ρ ζ-zero} ĥ(t_ρ) = arch(h) + pole(h) = (1/3)Σ_{γ zero of F} ĥ(γ) ≥ 0`.
  So the existence of a fake producer gives `PBAP` unconditionally. The ledger's duality equivalence `W ≠ ∅ ⟺ PBAP` (L68/L70/L79), restated in the `V₃` setting.
- **Consequence for RH.**
  - If prime-blind tests can detect every off-line ζ-zero (the L183 programme; L184 restores it heuristically through the near-radical blocks), then Conjecture P implies RH.
  - So the `V₃` route is RH-strength unless detection fails. Equally, it is a **proof strategy for RH**: construct `F` by Gram design (a positivity-constrained interpolation problem in a family where the conditions are open and the freedom is abundant), then apply detection.
  - Neither step is done. Each is a well-posed analytic problem that does not presuppose RH.
- **Where the difficulty now sits.**
  - (b) Uniform multiscale control in Conjecture P.
  - The L183/L184 detection lemma, which would make `W ≠ ∅ ⇒ RH` a theorem.

## 13. Step (a) of Conjecture P: evaluations factor through the `E₊`-projection [P] + exact range criterion
- **Evaluation kernels.** For a self-dual relation `ν` (giving `E_ν ∈ W`), the theta integral gives `Λ_{E_ν}(s) = ⟨ν, Ψ_s⟩`, where `ψ_s(x) = ∫_1^∞ K₃(xy)(y^s + y^{1−s})dy/y` and `Ψ_s = Uψ_s`.
  - Exactly, `ψ_s + Hψ_s = Φ_s := Γ_ℝ(s)³x^{−s} + Γ_ℝ(1−s)³x^{s−1}`, and `Φ_s` is `H`-invariant.
  - `Ψ_s ∉ 𝓗` because of power singularities at `0`. Regularize with a cutoff `χ₀` supported below the first integer node: `Ψ^{reg}_s = Ψ_s − χ₀Φ_s ∈ 𝓗`. It agrees with `Ψ_s` on all nodes.
  - Then `Ψ^{reg} + H̃Ψ^{reg} = −χ₀Φ + H̃((1−χ₀)Φ)`.
- **Factorization.** `ν` annihilates `E₋`, so `Λ_{E_ν}(s) = ⟨ν, Ψ₊^{(s)}⟩`, with `Ψ₊^{(s)} = ½H̃((1−χ₀)Φ_s)` on nodes. This is the transform of a cut-off power function; it decays faster than any power away from its stationary-phase location `Y ≍ |Im s|`.
  - Hence `E_ν(s)` at height `t` sees only `ν`'s coefficients on nodes near the stationary region. **This is the phase-space localization needed for the multiscale step (b).**
- **Exact criterion for (a).** The evaluations at `s₁, …, s_K` (one point from each FE pair) are linearly independent on `W` iff, for every `a ≠ 0`, the sample vector of `Σ_j a_jΨ₊^{(s_j)}` on nodes is not in `Range(T|_{E₋})` plus the span of the finitely many extra-point coordinates.
  - The naive Vandermonde heuristic (`E_i ≈ x_i^{−s}`) is **wrong**. Relations annihilate smooth functions, so `x_i^{−s}` cancels against its interpolant, and only the dual (`E₊`) part survives.
  - Independence is expected generically: `Range T` has infinite codimension, and the `Ψ₊^{(s_j)}` are distinct stationary-phase packets. A proof needs a non-membership argument, for example a weighted size or phase mismatch at the packets' locations.
- 2026-10-01 — §13: evaluation factorization; exact criterion for (a); localization principle for (b).

## 14. Step (b): multiscale construction plan and a compatibility check at low height [P-sketch]
- **Localized relations.**
  - The sampling system `{evaluation at λ} ∪ {evaluation of H̃ at μ}` is a frame of reproducing kernels. These kernels are localized in phase space: the Gram-matrix entries decay off the hyperbola structure `XY ≍ const`.
  - By the Jaffard / Gröchenig–Leinert inverse-closedness theorems, the canonical dual frame is localized too. So the relation `ν_i` produced by deleting a node `x_i` is concentrated near `x_i` and its dual region.
  - With §13, `E_{ν_i}(½+it)` is negligible unless `t` lies near the height `t_i` attached to `x_i`. This gives a **localized basis** `{E_i}` of `W`, indexed by height windows.
- **Locally finite design.**
  - In each height window `[T_j, T_{j+1}]`, choose finitely many coefficients of the local `E_i`. Prescribe positive values at the Gram points of that window (§13 independence, locally), plus no winding on the horizontal segments there.
  - Cross-window interactions decay faster than any power. The infinite system is diagonally dominant, so a Neumann-series or contraction argument converges.
  - Polynomially bounded targets suffice: `|ζ(½+it)|³ ≪ t^{¾}` by convexity.
- **Compatibility with §9(a) [checked].** §9(a) needs `E` comparable to or larger than ζ³ near the low zeros, while condition (ii) needs `F(2+it)` in a half-plane.
  - Both are compatible when `E`'s coefficients concentrate at moderate `n ≍ N`: `|E(½+it)| ≍ N^{½}·(mass)`, while `|E(2+it)| ≲ N^{−1}·(mass)`.
  - Example at the first zero (`t ≈ 14.1`, approximate-FE length `≈ t^{3/2} ≈ 53`): mass on `n ≈ 40` gives a ratio of about 250 between `σ = ½` and `σ = 2`. So `E` can exceed `|ζ|³` near the line while staying below `min|ζ(2+it)|³ ≈ 0.285` on `σ = 2`.
- **Remaining rigorous inputs.**
  - (1) Off-diagonal decay estimates for the twisted frame `S∘V`, so that inverse-closedness applies.
  - (2) Quantitative packet localization for `Ψ₊^{(s)}`, by stationary phase with explicit errors.
  - (3) Local independence (§13) with uniform constants per window.
  - (4) Low-height windows. These are finitely many conditions; they may need certified evaluation (a pod run for exact data only, per corpus rules).
- 2026-10-01 — §14: multiscale plan; low-height compatibility checked.

## 15. Correction to §13–§14: the localization is one-sided (triangular), and the crux of (b) is a growth problem [P-sketch]
- **Cancellation of power terms.** On nodes at large `y`,
  `Ψ₊^{(s)} = ½[Φ_s − H(χ₀Φ_s)]`, and `H(χ₀Φ_s)(y) = y^{s−1}G(1−s)Γ_ℝ(s)³ − y^{s−1}∫_{x₀y}^∞ u^{−s}J(u)du + …`.
  - Since `G(1−s)Γ_ℝ(s)³ = Γ_ℝ(1−s)³`, the `x^{s−1}` power terms cancel exactly.
- **What survives.** The remainder is the oscillatory tail `∫_{x₀y}^∞ u^{−s}J(u)du`, with phase `6πu^{1/3} − t log u` and stationary point `u = (t/2π)³`.
  - Hence `Ψ₊^{(½+it)}(y)` is of stationary-phase size for `y ≲ (t/2π)³/x₀` and decays faster than any power beyond that (integration by parts).
- **Corrected structure.** The localization is **one-sided**:
  - `E_ν(½+it)` depends on `ν` only on nodes below the stationary scale `(t/2π)³/x₀`, which is the approximate-functional-equation range.
  - A relation localized at node `x_i` affects only heights `t ≳ 2π(x_i x₀)^{1/3}`.
  - So the design system is **lower-triangular**: windows can be fixed in increasing order without disturbing lower windows. This replaces the two-sided diagonal-dominance claim of §14.
- **The real crux of (b): growth.**
  - A component built for window `j` keeps contributing oscillatory terms at all higher windows.
  - If the target at height `t` is about `|ζ(½+it)|³ ≲ t^{¾}`, then the old contributions at window `j'` sum to `Σ_{j<j'}(size_j × packet overlap)`.
  - With square-root cancellation this is about `t_{j'}^{¾}`: the same order as the target. That is borderline, not dominated.
  - The coefficients must stay polynomially bounded, so the construction needs either a decay mechanism for old components at higher heights (orthogonality of packets across windows) or a choice of new components that cancels the accumulated tail.
  - **This is the precise open estimate for (b).**
- 2026-10-01 — §15: power-term cancellation; triangular (one-sided) localization; growth/cancellation estimate isolated as the crux.

## 16. Two facts about Gram design [P]
- **Higher-height contributions are dual sums.**
  - Below the stationary scale, `|Ψ₊^{(½+it)}(n)| ≍ n^{−½}`, with a `t`-dependent phase; the stationary-phase size is `u₀^{1/6}t^{−½} ≍ 1`.
  - So a component with coefficients `c_n` (`n ≍ N_j`) contributes `≍ e^{iφ(t)}Σ c_n n^{−½+it}` at every height `t ≳ t_j`. This is exactly the dual sum of the degree-3 approximate functional equation.
  - Accumulated components therefore cannot be controlled independently: the dual sums are fixed by the same coefficients as the main sums.
  - Dyadic windows give the borderline `≍ t^{¾}` of §15. Unit-length windows give `≍ t^{5/4}`, which overwhelms the target.
  - **Gram design must be a coherent choice of the full coefficient sequence, not a superposition of independent local patches.**
- **No first-term dominance (Bohr–Landau barrier).**
  - Gram's law would follow trivially if `Σ_{n≥2}|f_n|n^{−½}` were below `|f_1|`, since then `Z_F ≈ 2f_1 cos 3θ`. This is impossible for any nonzero `F ∈ V₃`.
  - *Proof.* If `Σ|f_n|n^{−½+ε} < ∞`, then `F` is bounded on `σ = ½ − ε`. The functional equation then gives `|F(½+ε+it)| ≪ |t|^{−3ε} → 0`. But `F(½+ε+it)` is almost periodic with mean `f_1`. So `f_1 = 0`, and iterating gives `F ≡ 0`. ∎
  - Hence the coefficient sums `Σ_{n≤N}|f_n|n^{−½}` are unbounded. Gram positivity must come from cancellation, as for ζ itself, never from size.
- **Status of Conjecture P.** It is now a coherent-coefficient design problem with the same cancellation character as Gram's law for L-functions. No construction mechanism is known. The route stays open but is not easier in kind than the original producer problem.
- 2026-10-01 — §16: dual-sum accumulation; first-term dominance impossible; Conjecture P recalibrated.

## 17. Lean: the exact factorization of §6 Step 1 is formal
- Module `RHTower/DegreeThreeHankelTriplicationTwist.lean`, wired into `RHTower.lean` after `WeilBoundedDatumPoleObstruction`. `lake build` is green. Axioms: `propext, Classical.choice, Quot.sound`.
- **`gamma_cube_mul_inv_gamma_triple`:** `Γ(v/2)³Γ(3v/2)⁻¹ = C·3^{−3v/2}·R(v)`. Gauss triplication via the corpus `gauss_multiplication_complex`.
- **`gammaR_cube_mul_inv_gammaR_triple`:** the `Γ_ℝ` form; the powers of `π` cancel.
- **`triplication_twist_symmetric`:** the constant `C` cancels between `v` and `1 − v`.
- **`triplication_twist`:** `3^{w−½}·Γ_ℝ(v)³Γ_ℝ(3v)⁻¹·R(1−v) = Γ_ℝ(1−v)³Γ_ℝ(3(1−v))⁻¹·R(v)` with `w = 3v − 1`. This is exactly `H̃ = S∘V` at the level of Mellin multipliers.
- The lint gate shows 10 pre-existing "unreachable module" errors from other modules; none involve this file.

## 18. Theorem R (finite-height reduction): a producer exists if, for every height, some fake ζ³ has RH up to that height [P]
**Statement.** Suppose there are `A, s₀ ≥ 1` and a function `B(T)` with `log B(T) = o(T^{1/s₀})` such that, for every `T₀`, some `F = Σf_n n^{−s} ∈ ζ³ + W` (here `F` may depend on `T₀`) satisfies:
1. `|f_1| ≥ 1` and `|f_n| ≤ B(T₀)n^A`;
2. every zero `ρ` of `Λ_F` with `|Im ρ| ≤ T₀` lies on `Re s = ½`.

Then PBAP holds, hence `W_ζ ≠ ∅`: **an integer-supported full-cone Weil-positive weight system for ζ's exact archimedean datum and pole exists.** The last step is the corpus duality `exists_weilPositiveFull_iff_primeBlindPositive`, plus the single-function reduction of L248.

**Proof.**
1. *Explicit formula.* Let `g = f⋆f̃` with `f ∈ C_c^∞(−a,a)` in a Gevrey class of order `s₀`, and `g(±log n) = 0` for all `n ≥ 2`.
   - For every `F ∈ ζ³ + W` with `f_1 ≠ 0`, Weil's explicit formula (contour integration of `ĝ·Λ_F'/Λ_F`) holds. Its right edge sits where `F` is zero-free (`F → f_1` as `σ → ∞`), its archimedean term is `3·arch(g)`, its polar term is `3·pole(g)`, and its prime side is `Σ Λ_F(n)n^{−½}(g(log n) + g(−log n)) = 0`.
   - Hence `Σ_ρ ĝ(t_ρ) = 3(arch(g) + pole(g))`, **the same value for every member**.
2. *Zero strip.* Zeros satisfy `|Re ρ − ½| ≤ σ*(F)`. Since `Σ_{n≥2}|f_n|n^{−σ} < |f_1|` once `σ > A + 2 + log₂B`, we get `σ* ≤ A + 2 + log₂B(T₀)`. Jensen's formula gives `≪ log(T + B)` zeros in `[T, T+1]`.
3. *Split the zero sum.*
   - Zeros with `|γ| ≤ T₀` are real by hypothesis, and contribute `ĝ(γ) = |f̂(γ)|² ≥ 0`.
   - The tail: `|ĝ(t + iy)| ≤ e^{2a|y|}C exp(−c|t|^{1/s₀})`, so it is at most `B(T₀)^{2a}·e^{2a(A+2)}·Σ_{|γ|>T₀} exp(−c|γ|^{1/s₀})·log(|γ| + B) → 0`.
4. *Conclusion.* Letting `T₀ → ∞` gives `arch(g) + pole(g) ≥ 0`. Gevrey-class prime-blind tests are dense in the prime-blind cone used by the duality (a standard regularization, still to be checked). So PBAP holds. ∎

**Remarks.**
- The members may be **unrelated for different `T₀`**: no limit and no coherence across heights is needed. This removes the crux of Conjecture P (§15–§16).
- Under RH, `F = ζ³` satisfies the hypothesis trivially (triple zeros on the line, `ĝ ≥ 0`). So the hypothesis is implied by RH, and it implies the existence of a producer.
- With the L183/L184 detection lemma, the hypothesis implies RH. In that case an off-line ζ-zero would force **every** controlled member of the infinite family `ζ³ + W` to have off-line zeros near the detecting test's frequencies: all members share one prime-blind zero functional.
- **The open problem is now finite-height and linear-algebraic.** For each `T₀`, find `E ∈ W` with polynomially or subexponentially controlled coefficients such that `ζ³ + E` has only real zeros up to `T₀`.
  - Natural route: approximate an FE-symmetric degree-3 Pólya-type target (e.g. `Λ_T = P(s) + P(1−s)`, `P = cΓ_ℝ(s)³`, whose zeros are on the line) on the rectangle `[½, σ₁] × [0, T₀]`, then apply Rouché and Gram signs.
  - The approximation requires density of `W` on compacts modulo finitely many constraints. By §13, annihilating measures `σ` must have `∫Ψ₊^{(s)}dσ(s)` sampled in `Range(T|_{E₋})`. Such samples decay beyond the scale `T₀³`, which forces bounded phase-space support and hence finite dimension.
  - The approximation must also come **with coefficient control**.
- 2026-10-01 — §18: Theorem R (finite-height reduction).

## 19. Zero conservation law for `ζ³ + W`, and why the `V₃` route does not escape RH [P]
- **Conservation law.** For every `F ∈ ζ³ + W` with `f_1 ≠ 0`, and every prime-blind `g`,
  `∫ĝ dμ_F = 3∫ĝ dμ_ζ`, where `μ_F = Σ_{ρ zero of Λ_F} δ_{t_ρ}` (complex points allowed).
  - Equivalently, `μ_F − 3μ_ζ` annihilates the prime-blind cone: its Fourier side is carried by `±log ℕ_{≥2}`.
  - The zero sets of all members of the infinite-dimensional family are spectrally tied to ζ's zeros through `log ℕ`.
- **Consequence.**
  - Suppose ζ has an off-line zero `ρ₀`, and a prime-blind `g₀` detects it (`∫ĝ₀dμ_ζ < 0`, the L183/L184 detection lemma).
  - Then **every** member has `∫ĝ₀dμ_F < 0`. Real zeros contribute `ĝ₀(γ) ≥ 0`, so every member with coefficient growth controlled as in Theorem R has off-line zeros (or a large tail) where `ĝ₀` lives.
  - So local Gram design (§11–§18) cannot succeed near `γ₀`: the local surjectivity/approximation lemmas it assumes must **fail** there.
  - Hence, given detection, the finite-height design problem of Theorem R is **equivalent to RH**.
- **Low heights.** Up to the verified height (`3·10^{12}`, Platt–Trudgian), `F = ζ³` already satisfies the hypothesis of Theorem R (its zeros are on the line there). A non-trivial `E` is needed only where ζ might fail RH, and that is exactly where the conservation law forbids success if it does fail.
- **Verdict on the `V₃` door.** Existence of fake ζ³'s is proved (Theorem A). A fake producer would satisfy the conservation law. So, given detection, a fake producer exists iff RH holds, and the door gives no RH-independent producer.
  - The remaining question is detection itself (L183/L184). If prime-blind tests could fail to see some off-line zeros, the door might reopen.
- **Positive survivors** (no-go closure discipline):
  - Theorem A (C1 false; Lean brick `triplication_twist`).
  - The density dictionary `a = 2/λ_H`.
  - Lemma G and Theorem R.
  - The zero conservation law: an exact identity, `∫ĝ dμ_F = 3∫ĝ dμ_ζ` on prime-blind tests, for every member.
- 2026-10-01 — §19: zero conservation law; the `V₃` route is RH-equivalent given detection.
