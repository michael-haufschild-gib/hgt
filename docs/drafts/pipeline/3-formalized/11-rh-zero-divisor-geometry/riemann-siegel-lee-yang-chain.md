# Riemann–Siegel sums as domain-wall expansions of a Lee–Yang chain on the Γ sites

- **ID:** `riemann-siegel-lee-yang-chain`
- **Stage:** 3-formalized for the theorem part (route candidate open; STATUS MUST-820)
- **Type:** `[THEOREM + NEW ROUTE CANDIDATE]`
- **Parents:**
  - MUST-806 (`not_tendsto_lyApprox_mul_XiC`): prime fields cannot reach Ξ.
  - MUST-819 (`exists_resolution_law`): a stability producer at height `R` needs `≳ R` slow variables of frequency `≲ log R/R`, which are exactly the convergence factors `(1+1/m)^{s/2}` of the Euler product of `Γ(s/2)`.
  - Corpus tree Lee–Yang: `PrimeIsingTreeCavity.treePartition_ne_zero_of_fields_inside`.

## Statement

**Setup.**
- Sites `k = 0..N` carry fields `u_k`; edge `k` (between `k` and `k+1`) carries a wall fugacity `c_k ∈ [0,1]`.
- `Z = Σ_{σ ∈ {±}^{N+1}} ∏_{σ_k = −} u_k ∏_{σ_k ≠ σ_{k+1}} c_k` (ferromagnetic chain, `c = e^{−2J}`).
- Transfer form: `A_0 = 1`, `B_0 = u_0`, `A_{k+1} = A_k + c_k B_k`, `B_{k+1} = u_{k+1}(c_k A_k + B_k)`, `Z = A_N + B_N`.

1. **Lee–Yang.** If `‖u_k‖ < 1` for all `k`, then `‖B_k‖ < ‖A_k‖` and `Z ≠ 0`. Global spin flip gives `Z(u) = (∏ u_k)·Z(1/u)`. So for fields `u_k = e^{−iλ_k z}` with `λ_k > 0`, every zero is real, for every choice of fugacities in `[0,1]`.
2. **Telescoping.** For the Γ sites `λ_k = log((k+2)/(k+1))`:
   - `∏_{i≤k} u_i = (k+2)^{−iz}` and `∏_{k<i≤N} u_i = ((N+2)/(k+2))^{−iz}`;
   - so a single domain wall after site `k` carries the integer frequency `log(k+2)`.
3. **Riemann–Siegel at first order.** Along `c ↦ εc`:
   - `Z|_{ε=0} = 2(N+2)^{−iz/2} cos((z/2) log(N+2))`;
   - `∂_ε Z|_{ε=0} = 2(N+2)^{−iz/2} Σ_k c_k cos(z log(k+2) − (z/2) log(N+2))`.
   - With `c_{n−2} = n^{−1/2}` for `n ≤ M`, and `0` beyond, the first two orders are exactly the Riemann–Siegel main sum `Σ_{n≤M} n^{−1/2} cos(θ_N(z) − z log n)` with frozen phase `θ_N(z) = (z/2) log(N+2)`. Here `θ_N' = θ'` at height `2πe(N+2)`.
   - The full chain is real-rooted for every `ε ≤ 1`.

## Proof (paper)

(1)
- From `‖B‖ < ‖A‖` and `0 ≤ c ≤ 1`, we get `‖cA+B‖² − ‖A+cB‖² = (c²−1)(‖A‖²−‖B‖²) ≤ 0`.
- Also `A + cB ≠ 0`, since `‖cB‖ < ‖A‖`.
- Then `‖B_{k+1}‖ = ‖u_{k+1}‖·‖cA+B‖ < ‖A+cB‖ = ‖A_{k+1}‖`.
- For the reciprocal identity, induct with `A_k(u) = Π_k B_k(1/u)` and `B_k(u) = Π_k A_k(1/u)`, where `Π_k = ∏_{i≤k} u_i`.
- For `Im z < 0` all `‖u_k‖ < 1`. For `Im z > 0` all `‖1/u_k‖ < 1`.

(2) The sum telescopes: `Σ_{i≤k} log((i+2)/(i+1)) = log(k+2)`.

(3)
- At `ε = 0`: `(A_k, B_k) = (1, Π_k)`.
- Differentiating the recursion: `A'_{k+1} = A'_k + c_k Π_k` and `B'_{k+1} = u_{k+1}(c_k + B'_k)`.
- Hence `A'_N = Σ_{j<N} c_j Π_j` and `B'_N = Σ_{j<N} c_j ∏_{j<i≤N} u_i`.

## Route candidate (ALY: archimedean Lee–Yang completion of Riemann–Siegel)

- The slow Γ sites that MUST-819 makes *necessary* are *sufficient* to produce the Riemann–Siegel main term at first order inside an unconditionally real-rooted family.
- **Open core:** find ferromagnetic couplings (any graph on the Γ sites, possibly with prime-labelled interactions) whose higher domain-wall sectors reproduce the Riemann–Siegel remainder and the moving phase `θ(t)`.
- **Obstruction (paper):** on a chain, two walls at `a < b` contribute `c_a c_b cos(θ_N − z log(b/a))` with positive weight. This is a "rational pollution" at every ratio `b/a`.
  - Any ferromagnet has positive weight on every spin configuration. So its spectrum contains all subset products `∏_{m∈S}(1+1/m)`, with positive coefficients.
  - An exact match with an integer-supported Riemann–Siegel sum is impossible. Approximation needs the non-integer mass to be negligible.
  - With `c_n = n^{−1/2}` on `n ≤ M`, the two-wall mass is `Σ_{a<b≤M}(ab)^{−1/2} ≍ M`, so it is not negligible.

## Lean

`RHTower/RiemannSiegelLeeYangChain.lean` (namespace `RHTower.LeeYangChain`, standard axioms, wired):
- `chainPair` and `chainZ`: the transfer-form partition function.
- `chainPair_inside` and `chainZ_ne_zero_of_norm_lt_one`: Lee–Yang inside the polydisk.
- `chainZ_reciprocal`: global spin flip.
- `chainZ_ne_zero_of_im_ne_zero`: real zeros for exponential fields of any positive frequencies and any fugacities in `[0,1]`.
- `sum_gammaFreq`, `prod_gammaSiteField` and `prod_Ico_gammaSiteField`: telescoping of the Γ sites.
- `gammaChainZ_zero` and `hasDerivAt_gammaChainZ`: the zeroth and first order in `ε`.
- **`riemannSiegel_leeYang_chain`**: the headline theorem, packaging the three items.

Not formalized: the rational-pollution obstruction (paper, above).

## Log
- 2026-10-07 — card created and formalized the same day (MUST-820). The proof is elementary: the Lee–Yang step is the two-line identity `|cA+B|²−|A+cB|² = (c²−1)(|A|²−|B|²)`, iterated along the chain, and the Riemann–Siegel identification is the telescoping `∏(k+2)/(k+1)`.
