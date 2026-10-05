# Weil-cone rigidity on every finite union of common-ratio geometric progressions, via Bohr-restricted non-vanishing of ζ on vertical arithmetic progressions

- **ID:** weil-common-ratio-unions-bohr
- **Stage:** 2-fully-proven (paper). Theorem A extends Li–Radziwiłł (arXiv 1208.2684, IMRN 2015), Proposition 3 and Theorem 3; Theorem B extends L166.
- **Type:** THEOREM [P] (two theorems)
- **Source:** `1-in-progress/hf-positive-hodge-attack/krein-producer-loops.md`, entry L167
- **Lean:** Theorem B is formal for every `b ≥ 2` and every finite coset set:
  `RHTower.WeilCommonRatio.eq_vonMangoldt_of_weilPositiveFull_of_commonRatio` and the gap-`10⁻³` instance
  `…_of_thousand` (module `RHTower/WeilFullConeCommonRatioRigidity`, axioms standard, 2026-10-05). The formal
  proof does not go through Theorem A: `Σ_{n∈S} n^{−1/4}` is a finite sum of geometric series, and the
  corpus abscissa rigidity `WeilAbscissa.eq_vonMangoldt_of_weilPositiveFull_of_sparse_rpow` (MUST-576)
  applies. Theorem A (Bohr-restricted Li–Radziwiłł) remains to be formalized; it needs the discrete
  mollified second moment of ζ along vertical progressions.

## Theorem A (Bohr-restricted non-vanishing on vertical progressions)

**Statement.** Let `α > 0`, `β ∈ ℝ`, `θ ∈ ℝ^K`, and let `H ⊂ T^K` be the closure of `{ℓθ mod 1 : ℓ ∈ ℤ}` with Haar probability measure `μ_H`. Let `U ⊂ T^K` be open with `U ∩ H ≠ ∅`. Then

`liminf_{T→∞} T^{−1} #{T ≤ ℓ ≤ 2T : ℓθ ∈ U, ζ(½ + i(αℓ + β)) ≠ 0} ≥ μ_H(U)²/3.`

For `K = 0` (or `U = T^K`) this is the Li–Radziwiłł bound `1/3`.

**Proof.**
1. *Setup.*
   - Fix smooth `0 ≤ φ ≤ 1` supported in `[1, 2]` and smooth `0 ≤ W ≤ 1` on `T^K` supported in `U`.
   - Put `t_ℓ = αℓ + β`.
   - Use the mollifier `M(s) = Σ_{d ≤ y} b(d) d^{−s}`, with `b(d) = μ(d)(1 − log d/log y)` and `y = T^ϑ`, `ϑ < ½`.
2. *Fourier expansion.* Write `W(x) = Σ_{m∈ℤ^K} Ŵ(m) e(⟨m, x⟩)`.
   - Since `e(ℓ⟨m,θ⟩) = Q_m^{i(t_ℓ − β)}` with `Q_m := e^{2π⟨m,θ⟩/α} > 0`, we get
     `S₁ := Σ_ℓ φ(ℓ/T) W(ℓθ) (ζM)(½ + it_ℓ) = Σ_m Ŵ(m) Q_m^{−iβ} I_m`,
     with `I_m := Σ_ℓ φ(ℓ/T) (ζM)(½ + it_ℓ) Q_m^{it_ℓ}`.
   - Uniformly in `m`, Cauchy–Schwarz and Li–Radziwiłł Theorem 3 give `|I_m| ≪ T`. So truncating at `|m| ≤ M₀` costs `≤ εT`.
3. *Twisted first moment `I_m` (the proof of Li–Radziwiłł Prop. 3 with a twist).*
   - Use `ζ(½+it) = Σ_{n ≤ 2αT} n^{−½−it} + O(T^{−½})` and `|M(½+it)| ≪ T^{ϑ/2+ε}`.
   - Poisson summation in `ℓ` gives
     `I_m = T Σ_{d ≤ y, n ≤ 2αT} b(d)(dn)^{−½}(dn/Q_m)^{−iβ} Σ_{j∈ℤ} φ̂(T(α log(dn/Q_m)/2π − j)) + O(T^{3/4})`.
   - Only pairs with `dn = N` and `α log(N/Q_m)/2π = j + O(T^{ε−1})` survive.
   - `N = 1`: this needs `⟨m, θ⟩ ∈ −j + O(T^{ε−1})`. For large `T` that happens iff `⟨m, θ⟩ ∈ ℤ`, i.e. iff `m` annihilates `H`. The contribution is `Tφ̂(0)Q_m^{−iβ}e(j·…)`. Summed over such `m`, this is exactly `Tφ̂(0)·∫_H W dμ_H`: Fourier inversion on `H`.
   - `N ≥ 2`: each such `N` contributes `≪ T d(N) log N /(√N log T)`, because `Σ_{d|N} b(d) ≪ d(N) log N/log T` for `N > 1`. For fixed `(m, j)` at most one `N ≤ T^{1−ε}` is admissible, and `N ≍ Q_m e^{2πj/α}` grows geometrically in `j`. The total is `O_m(T/log T)`.
   - Hence `S₁ = Tφ̂(0)∫_H W dμ_H + O(εT) + O_{M₀}(T/log T)`.
4. *Second moment.* Since `0 ≤ W ≤ 1`, `Σ_ℓ φ W |ζM|²(½+it_ℓ) ≤ Σ_ℓ φ |ζM|²(½+it_ℓ) = Tφ̂(0)(1 + 1/ϑ + o(1))` (Li–Radziwiłł Theorem 3 with Balasubramanian–Conrey–Heath-Brown).
5. *Cauchy–Schwarz.* `|S₁|² ≤ #{T≤ℓ≤2T : W(ℓθ) > 0, ζ(½+it_ℓ) ≠ 0} · Σ_ℓ φ W² |ζM|²`. Letting `ϑ → ½`, `φ → 1_{[1,2]}` and `W → 1_U` from below gives the claim. ∎

**Novelty and limits.**
- *Relation to Li–Radziwiłł.* The restriction to a Bohr set costs nothing at the level of the mollified first moment. The twists `Q_m^{it}` produce main terms only for characters that are trivial on the orbit closure. This is the Bohr-set form of their observation that mollification removes the Diophantine dependence.
- *Search.* A web search (2026-09-30) found no Bohr-restricted non-vanishing result.
- *Significance.* In its own field, a modest extension. It is what makes Theorem B unconditional.

## Theorem B (common-ratio unions)

**Statement.** Let `b ≥ 2` and let `c₁, …, c_K ≥ 1` be integers. Let `lam` be full-cone Weil-positive with `lam(n) = Λ(n)` for all `n ≥ 2` outside `S = ⋃_{i} {c_i b^j : j ≥ 0}`. Then `lam = Λ`.
- The cosets may be arbitrarily close: e.g. `{1000·2^j} ∪ {1001·2^j}`, log-gap `10^{−3}`.
- The deviation sizes are arbitrary, within the universal box.

**Proof.**
1. *Coset data.* Put `ℓ = log b`, `P = 1/ℓ`, `α_i = log c_i`. Cosets with `α_i − α_j ∈ ℓℤ` coincide; merge them. The base coset `α₀ = 0` is included. `v = normDeficit lam` vanishes off `S`.
2. *Fiber data.* For `ξ ∈ ℝ/Pℤ`:
   - fiber points `η_k = ξ + kP`;
   - orbit vectors `z_k(ξ) = (e^{2πiη_kα_i})_{i=1..K} ∈ ℂ^K`;
   - `k` is *blocked* if `Ξ(2πη_k) = 0`.
3. *Fiber-cone condition.* For every `ξ` there is a finite set of unblocked `k` whose orbit vectors have `0` in the interior of their convex hull, in `ℂ^K` or in the real subspace forced by the pairings `α_i + α_j ∈ ℓℤ`.
   - Proof: the unblocked orbit vectors are dense in the orbit closure. This is Theorem A with `α = 2π/ℓ`, `β = 2πξ`, `θ_i = α_i/ℓ`: every open set meets unblocked points.
   - The convex hull of an orbit closure of non-trivial, pairwise distinct characters contains its Haar mean `0` in its (relative) interior.
4. *Charts.* Blocked points are isolated in `ξ`. So each `ξ` has a neighbourhood on which a fixed finite block set `K_ξ` stays unblocked, with `|X| ≥ c > 0` on its fiber points and the cone condition holding uniformly. By compactness of `ℝ/Pℤ`, finitely many charts `(V_c, K_c)` cover the circle. Take smooth `P`-periodic `χ_c` with `Σ_c χ_c² = 1`, `supp χ_c ⊂ V_c`.
5. *Tests.*
   - For each target point `s₀ ∈ log S` and sign `σ`, take the L166 targets:
     - base point: mass `u = 1 + 2σε cos(2πtq₀ℓ)` and moment `x = 0`;
     - coset point: `u = 1` and moment `x_i = σε e^{−2πit(α_i + q₀ℓ)}/Ψ_{α_i}`-type, with the phases solved fiberwise.
   - On chart `c`, positive barycentric weights `w_k^{(c)}(ξ)`, `k ∈ K_c`, realize `(u, x)`, because the cone condition holds with margin and `ε` is small.
   - The test family is `h_{k,c}(η) = ψ(η − kP) χ_c(η − kP) √(w_k^{(c)}(η − kP))`, with profiles `h_{k,c}/X`. These are smooth and compactly supported, and `X ≠ 0` on their supports.
   - The fiber identity (L166 `integral_blockSq_spectralChar`, applied block by block) gives transform `∫₀^P u e^{2πiξqℓ}` on the base lattice and `∫₀^P x_i Ψ_{α_i} e^{2πiξ(α_i+qℓ)}` on coset `i`.
   - Hence the transform vanishes on `log S` except at `s₀`, where it equals `σεP`.
6. *Pairing.* The pairing lemma (L160/L165, `spectralWindowTests_pairing_nonneg`) gives `2σεP·v(s₀) ≥ 0` for both signs. So `v(s₀) = 0`. ∎

## What is new
- The lattice form of the Nyquist wall, identified in L166 as a question about arithmetic progressions of zero ordinates, is removed unconditionally. The input is a statement about the *values* of ζ on vertical progressions (Theorem A), not about the *positions* of its zeros. Value statistics along progressions are accessible to mollified moments below the `α = 1` barrier.
- Theorem B is the first Weil-cone rigidity theorem allowing arbitrarily small logarithmic gaps with arbitrary deviation sizes.
- **Limit.** The method needs a single ratio `b`: rank-one lattice plus finitely many cosets. Multiplicative semigroups of rank `≥ 2` have dense logarithms, and no Floquet reduction exists for them. The dense core (evaporation, Conjecture Ω of L143) is untouched.

## Gates
- [x] 0 → 1: mechanism (Floquet fibers plus Bohr non-vanishing)
- [x] 1 → 2: paper proofs above (Theorem A follows Li–Radziwiłł §4 line by line with the twist `Q_m^{it}`)
- [ ] 2 → 3: Theorem B formal (see Lean field). Theorem A open in Lean: needs the discrete twisted mollified second moment (Li–Radziwiłł Thm 3 with BCHB constant `1 + 1/ϑ`) and the Bohr-twisted first moment.

## Log
- 2026-09-30: L167.
- 2026-10-05: Theorem B formal via sparse abscissa rigidity (no Theorem A needed for B).
