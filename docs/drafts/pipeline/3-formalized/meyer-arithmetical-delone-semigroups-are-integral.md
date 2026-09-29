# Meyer arithmetical Delone semigroups lie in ℤ⁺ (the Meyer case of Lagarias's question)

- **ID:** MC-DELONE-MEYER
- **Stage:** 3-formalized for the real quadratic case `K = ℚ(√2)` (Lean capstone below). The general statement remains a paper proof, with classical inputs Meyer's Pisot–Salem theorem, Hecke equidistribution and Hall's theorem.
- **Type:** THEOREM (paper)
- **Source:** MC conjecture loop, cycles 121, 123, 127, 138 (`1-in-progress/mc-conjecture-loop-2026-09-28.md`)
- **Statement:** Let `S ⊂ [1,∞)` be an arithmetical Delone semigroup: a multiplicative semigroup with unit, unique factorization into irreducibles, and gaps bounded above and below. If `S` is a Meyer set (`S − S` uniformly discrete), then `S ⊂ ℤ⁺`, and by Lagarias's Theorem 1.1 its generators are `(ℙ∖E) ∪ C` with `E`, `C` finite.
- **Quantitative core (Theorem B):** For every number field `K ≠ ℚ` with a real embedding, every free submonoid `M` of `(S_K, ·)`, `S_K = {θ ∈ O_K : θ ≥ 1, |σ_j(θ)| ≤ 1 ∀ j ≥ 2}`, has `ζ_M(σ) ≪ (σ−1)^{−c}` as `σ → 1⁺`, for any `c > c_K`, with an explicit `c_K < 1`. Hence `Σ_{m∈M, m≤x} 1/m = O((log x)^{c})`, `M` has logarithmic density zero, and `M` is not relatively dense.

## Literature
- **Lagarias** ([Forum Math. 11 (1999) 295–312](https://www.degruyterbrill.com/document/doi/10.1515/FORM.1999.295/html)) classifies arithmetical Delone semigroups contained in ℤ⁺ (Thm 1.1–1.2) and asks: "The only such semigroups I know of are contained in ℤ⁺. Are there any others?"
- **Ruzsa** ([arXiv 2311.11127](https://arxiv.org/abs/2311.11127)) conjectures there are none.
  - He proves that one non-integer cannot be added to an almost full set of primes (Thm 1).
  - He builds uniformly discrete non-integer examples of density `≍ x/log x` in the generators (Thm 6). His quadratic example uses `g(p) = f(p)²` with `|g(p)′| ≍ p`, so it is outside every bounded window: it is not a Meyer set.
- **Multiplicatively closed Meyer sets** that are not free are known: β-integers for quadratic Pisot units (Burdík–Frougny–Gazeau–Krejcar).
- **Novelty.** No statement handling the Meyer case was found (web search 2026-09-29).
- **Consequence.** Lagarias's question is reduced to one step: *is every arithmetical Delone semigroup a Meyer set?* This is loop cycle 123, step (1).

## Proof of the Statement from Theorem B
1. **An order.** A Meyer set has finite local complexity, so the group `⟨S − S⟩` is finitely generated (Lagarias, *Geometric models for quasicrystals I*). Since `1 ∈ S`, `A := ⟨S⟩_ℤ` is finitely generated. `S·S ⊂ S` makes `A` a ring. So `A` is a finitely generated, torsion-free ring inside ℝ, i.e. an order in a number field `K ⊂ ℝ`, and `S ⊂ O_K`.
2. **Conjugates bounded.** For `θ ∈ S∖{1}` we have `θS ⊂ S` with `S` Meyer. Meyer's theorem says `θ` is a Pisot or Salem number, so `|σ_j(θ)| ≤ 1` for every conjugate embedding `σ_j ≠ id`. Hence `S ⊂ S_K`.
3. **Conclude.** If `K ≠ ℚ`, Theorem B contradicts relative density. Relative density gives `N_S(x) ≥ x/R − 1`, hence `ζ_S(σ) ≥ (1/R)/(σ−1) − O(1)`. So `K = ℚ`, `S_ℚ = ℤ⁺`, and Lagarias's Theorem 1.1 applies. ∎

## Proof of Theorem B
Notation: `P` is the set of prime ideals of `O_K`, `ι(θ) = (θ)`, `h(θ) = −Σ_{j≥2} log|σ_j(θ)| ≥ 0` for `θ ∈ S_K` (complex places counted twice), and `θ = |N(θ)|·e^{h(θ)}`.
1. **Ideal parts are almost independent.** `M` free on `G`. By freeness `ℤ^{(G)} → K^×_{>0}` is injective (a group relation is a monoid relation between two different elements). Elements with trivial ideal are units, so the kernel of `ℤ^{(G)} → ℤ^{(P)}` has rank `≤ r_u = r₁+r₂−1`. Choose a basis of relations and let `G₀` be the union of their (finite) supports; unit generators lie in `G₀`. Then `G₁ = G∖G₀` has ℤ-independent ideal parts, and `M = M₀ × M₁` with `ζ_{M₀}(1) < ∞`.
2. **Prime transversal.** Independence gives Hall's condition `|⋃_{g∈F} supp ι(g)| ≥ |F|`. Hall's theorem for countable families of finite sets gives an injection `τ: G₁ → P` with `τ(g) | ι(g)`.
3. **Bound.** Since `g ≥ |N(g)| ≥ Nτ(g)`, `log ζ_{M₁}(σ) = Σ_{g∈G₁} g^{−σ} + O(1)` and `g^{−σ} = |N(g)|^{−σ}e^{−σh(g)}`. Two cases:
   - If `ι(g) ≠ τ(g)`, then `g^{−σ} ≤ 2^{−σ}Nτ(g)^{−σ}`.
   - If `ι(g) = τ(g) = 𝔭` (principal), then `g` is an associate `εα_𝔭` in `S_K`. The vectors `(log|σ_j(εα_𝔭)|)_{j≥2}` run over `y₀(𝔭) + Λ_u` (Dirichlet: the log-units in the non-identity places form a full lattice), so `h(g) ≥ F(y₀(𝔭) mod Λ_u)`, where `F(y) = min{−Σ_j d_j y_j : y ∈ (y + Λ_u) ∩ (−∞,0]^{r_u}}`. `F` is bounded, piecewise continuous, and positive off a null set.

   Therefore `Σ_{g∈G₁} g^{−σ} ≤ Σ_{𝔭∈P} N𝔭^{−σ} Φ(𝔭)`, with `Φ(𝔭) = max(½, e^{−F(y₀(𝔭))}·[𝔭 principal])`.
4. **Equidistribution (Hecke).** For `m ≠ 0` in the dual of `Λ_u`, `χ_m(α) = Π_{j≥2}|σ_j(α)|^{2πi m_j}` is a well-defined Hecke character on principal ideals. It is nontrivial and not of the form `|N|^{it}`, because the log-embedding of `K^×` spans. So `Σ_𝔭 N𝔭^{−σ}χ_m(𝔭) = O(1)` as `σ → 1⁺` (`L(s,χ_m)` is entire and nonzero at `s = 1`). Class-group characters handle principality, which has density `1/h_K`. Hence
   `Σ_𝔭 N𝔭^{−σ}Φ(𝔭) = (c_K + o(1)) log(1/(σ−1))`, with `c_K = (1/h_K)∫_{ℝ^{r_u}/Λ_u} max(½, e^{−F}) + (1 − 1/h_K)·½ < 1`.
5. **Conclusion.** `ζ_M(σ) ≤ ζ_{M₀}(σ) exp(Σ_g g^{−σ} + O(1)) ≪ (σ−1)^{−c_K−o(1)}`. Rankin's trick with `σ = 1 + 1/log x` bounds the logarithmic count. ∎

For `K = ℚ(√2)` (`u = 1+√2`, `h = 1`, `r_u = 1`): `F(y) = {y/log u}·log u`, so `c_K = ∫_0^1 max(½, u^{−t}) dt ≈ 0.674`. A concrete check: cycle 127's one-associate-per-prime monoid has `ζ ≍ (σ−1)^{−κ}` with `κ = (1−u^{−1})/log u ≈ 0.665`.

## Meaning for route MC
Cycle 121 argued that O(1) count regularity (a lattice or crystal structure) is ℕ-specific, and that only ℕ-specific additive or Poisson structure can feed an MC producer. Theorem B makes the "crystal" half rigorous for quasicrystals. Every Meyer (quasicrystalline) free multiplicative Delone set is ℕ up to finitely many changes. So no quasicrystal Beurling model of ℕ exists in which RH could be tested separately. This is ζ-blind.

## Lean status
**Capstone (unconditional; axioms propext, Classical.choice, Quot.sound):** `RHTower.SqrtTwo.not_relativelyDense_of_free`.
- Hypotheses: `g : ι → ℤ√2` with `1 < emb (g i)` and `|emb (star (g i))| ≤ 1`, and `f ↦ Π g_i^{f_i}` injective.
- Conclusion: for every `R`, some `x ≥ 1` has no product in `[x, x+R]`.

This is Theorem B for `K = ℚ(√2)` without Hecke: the conjugate pairing plus the PNT in progressions mod 8 (PNTPlus `WeakPNT_AP`, `WeakPNT_AP_prelim`) replace equidistribution. Modules (2537 lines, all wired into `RHTower.lean`):
1. `SqrtTwoNormEuclidean`: `ℤ[√2]` is a Euclidean domain for `|N|`.
2. `SqrtTwoUnitsAndInertPrimes`: positive units are `(1+√2)^k`; `p ≡ 3, 5 (mod 8)` is inert.
3. `SqrtTwoFreeMonoidPrimeTransversal`: freeness gives proportional relations; after removing at most one generator, Hall gives a prime transversal.
4. `SqrtTwoWindowDefect`: the window defect `t`, its associate invariance, the window bound, conjugate pairing, and the per-generator bound.
5. `SqrtTwoPrimesAboveRational`: at most two primes above `p`, conjugate structure, per-`p` contributions `2p^{−σ}`, `p^{−2σ}` and `(2−η)p^{−σ}`.
6. `ResidueClassPrimeSumSharpUpper`: `Σ_{p≡a (q)} p^{−σ} ≤ (1/φ(q))log(1/(σ−1)) + C`, sharp constant, via a monotone auxiliary function.
7. `ResidueClassPrimeWindowLowerBound`: primes `p ≡ a` with phase `{log p/log ρ} ∈ [¼,¾]` carry `≥ c log(1/(σ−1)) − C`.
8. `FreeMonoidEulerBounds`: finite Euler bound, exponential form, relative density `⇒ Σ ≥ c/(σ−1)`.
9. `SqrtTwoPrimeSumBound`: `Σ_π (|Nπ|^{−σ}Φ(π) + 2|Nπ|^{−2}) ≤ (1−κ)log(1/(σ−1)) + D`.
10. `SqrtTwoModelSetFreeMonoidNotDelone`: assembly and contradiction as `σ → 1⁺`.

Reusable outside this card: the `ℤ[√2]` Euclidean domain and unit classification; sharp residue-class prime sums and phase-window lower bounds from PNTPlus; Euler and density bounds for free monoids.

## Log
- 2026-09-29: proved on paper (loop cycle 138). Audit: Lagarias 1999 (question stated, only the ℤ⁺ case solved); Ruzsa 2023 (non-Meyer examples only).
- 2026-09-29: Lean modules 1–5 built and wired (all axiom-clean):
  - `SqrtTwoNormEuclidean` (`instEuclideanDomain`);
  - `SqrtTwoUnitsAndInertPrimes` (`exists_zpow_eq_of_emb_pos`, `prime_natCast_of_mod_eight`);
  - `SqrtTwoFreeMonoidPrimeTransversal` (`exists_prime_transversal`);
  - `SqrtTwoWindowDefect` (`emb_rpow_neg_le`, `one_sub_fract_le_windowDefect_add`);
  - `ResidueClassPrimeSumSharpUpper` (`exists_sum_prime_rpow_le`, via PNTPlus `WeakPNT_AP_prelim`);
  - `ResidueClassPrimeWindowLowerBound` (`exists_window_prime_sum_lower`, via `WeakPNT_AP`).
  Remaining: primes above rational primes, the Euler-product and relative-density bounds, and the final assembly.
- 2026-09-29: capstone `not_relativelyDense_of_free` formalized (10 modules, axiom-clean); card moved to 3-formalized.
