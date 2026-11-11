# Shortest twist family with a generic mean square

- **ID:** shortest-generic-twist-family
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-1111/obstacles-summary.md` §2.5 (B177, Π163) · `docs/reports/review-1011/fable.md`
- **Statement:** For smoothed Möbius sums of length `Z` twisted by residue symbols of order `n ≥ 2` up to norm `Z^θ`, the principal `n`-th-power subfamily is generic iff `θ ≥ (n/(n−1))(2 Θ_ζ − 1)` (attained minimum; `0` iff `RiemannHypothesis`); positive squarefree weights (`μ(m)²`) are generic iff `θ ≥ n/(n−1)` unconditionally; the full Jacobi twist family (`n = 2`) forces `Θ_ζ, Θ_{χ_{u₀}} ≤ min(1, ½ + θ/4)` for every odd squarefree `u₀ > 1` at `θ > 0` and has infimal generic exponent `0` (equivalently holds for all `θ ≥ 0`) iff GRH holds for `ζ` and all odd primitive real Dirichlet characters; and in `θ = (2n/(n−1))(σ₀ − ½)`, the reflection-and-large-sieve producer class has sharp floors `10/9` (optimal sextic multiplicative sieve), `1` (additive planar sieve / dual diagonal), `9/10` (published binding bin), `(5n−8)/(5(n−1))` (floor bin across all `n ≥ 2` and both Gram regimes), and `(n−2)/(n−1)` (free reflection-sieve floor).

## Goal
Resolve Question B177 unconditionally by determining the exact set of exponents `θ ≥ 0` at which residue-symbol twist families have generic mean square `O_ε(Z^{θ + 1 + ε})`, separating the intrinsic arithmetic threshold from the structural barriers of non-cancellative weights and of every sub-class of the reflection-and-large-sieve producer architecture.

## Gates
- [x] 0 → 1  in-progress: exact formulation on both the arithmetic twist mean square and the single-variable reflection-sieve producer budget
- [x] 1 → 2  fully-proven: `[PROVED HERE]`, complete dependency-closed proof with conductor-uniform Dirichlet subpolynomial lower bounds and single-variable threshold classification
- [x] 2 → 3  formalized: `GaloisForLFunctions.FamilyContinuationTheory.TheShortestGenericTwistFamily`, `GaloisForLFunctions.FamilyContinuationTheory.UniformSubpolynomialBoundsForDirichletTwists`, `GaloisForLFunctions.FamilyContinuationTheory.TheBudgetInTheTwistExponent` (`lake --old env lean` clean)

## Lean declarations

| Mathematical result | Lean declaration | Module |
|---|---|---|
| Exact two-term prime split & convergent geometric series | `twistedMoebiusSum_eq_sub_insert`, `twistedMoebiusSum_insert_eq_tsum` | `TheShortestGenericTwistFamily` |
| Finite-prime-avoidance Euler factor & `O_η(a^η)` bound | `norm_twistedMoebiusSum_le_of_base_le`, `exists_eulerProd_primeFactors_le_rpow` | `TheShortestGenericTwistFamily` |
| One-step prime-window signal drop & abscissa bound | `exists_signal_drop_of_primeWindow_meanSquare`, `abscissa_le_positiveFormBoundary_of_primeWindow_meanSquare` | `TheShortestGenericTwistFamily` |
| Exact generic ray & minimum `θ_min = (n/(n−1))(2 Θ_ζ − 1)` | `principalTwistGenericSet_poleKernel`, `principalTwistGenericSet_gaussianKernel`, `isLeast_principalTwistGeneric_poleKernel`, `isLeast_principalTwistGeneric_gaussianKernel` | `TheShortestGenericTwistFamily` |
| `θ_min = 0 ↔ RiemannHypothesis` | `principalTwistThreshold_eq_zero_iff_riemannHypothesis` | `TheShortestGenericTwistFamily` |
| Unconditional non-cancellative ray `[n/(n−1), ∞)` & minimum `n/(n−1)` | `positiveSquarefreeTwistGenericSet_eq`, `isLeast_positiveSquarefreeTwistGeneric` | `TheShortestGenericTwistFamily` |
| Conductor-uniform left-edge, strip, and subpolynomial `L(s, χ)` lower bounds | `exists_uniform_bound_LFunction_left_edge`, `exists_uniform_bound_LFunction_strip`, `exists_uniform_lower_bound_subpolynomial` | `UniformSubpolynomialBoundsForDirichletTwists` |
| Conductor-uniform pole-free Dirichlet Gaussian signal bound | `exists_uniform_signal_dirichletGaussianKernel_le` | `UniformSubpolynomialBoundsForDirichletTwists` |
| Jacobi twist family (`n = 2`) zero-free half-plane & quadratic GRH biconditionals | `zetaZeroAbscissa_and_jacobiPrimChar_le_of_jacobiTwistGeneric`, `forall_jacobiTwistGeneric_iff_quadraticGRH`, `sInf_jacobiTwistGeneric_eq_zero_iff_quadraticGRH` | `TheShortestGenericTwistFamily` |
| Bijection `θ ↔ σ₀` and sextic landmarks | `positiveFormTheta_le_iff`, `positiveFormTheta_six_landmarks` | `TheBudgetInTheTwistExponent` |
| Optimal sextic multiplicative sieve floor (`10/9`), Gauss-sum excess, additive planar floor (`1`), dual diagonal | `optimalSexticSieve_ge`, `optimalSexticSieve_attained`, `sieve_gaussSum_excess_obstruction`, `planar_sieve_min_order`, `dual_diagonal_barrier_iff` | `TheBudgetInTheTwistExponent` |
| Multi-row (`≥ n/(n−1)`), conductor-order corners (`14/15`, `22/21`, `11/9`), published binding bin (`9/10`) | `thetaDesign_ge_trivial`, `corner_theta_two_six`, `corner_theta_three_four`, `corner_theta_four_three`, `endpoint_binding_bin_pos_of_probeThetaGen_le` | `TheBudgetInTheTwistExponent` |
| Universal floor-bin barrier `(5n−8)/(5(n−1))`, free reflection floor `(n−2)/(n−1)`, twist circularity | `endpointExponentOrder_floor_bin_pos_of_lt`, `probeThetaGen_floor_attained`, `free_floor_le_probeThetaFree`, `probeThetaFree_with_principal_twists`, `le_probeThetaFree_with_principal_twists` | `TheBudgetInTheTwistExponent` |

## Proof

### 1. Telescoping prime-avoidance identity and finite Euler factor control
For any vertical-line weight `W : ℂ → ℂ` continuous along `linePoint y = 2 − iy` with `‖W(2 − iy)‖ ≤ C_W (1 + y²)⁻¹`, any bounded sequence `χ : ℕ → ℂ` (`‖χ(m)‖ ≤ 1`) satisfying `χ(p k) = χ(p) χ(k)` whenever `p ∤ k`, and any finite set `S` of primes, set `M_S^χ(Z) = ∑_{m ≥ 1, ∀ q ∈ S, q ∤ m} μ(m) χ(m) signal(W, 2, Z / m)`. Absolute convergence on `Re s = 2` gives `‖M_S^χ(X)‖ ≤ C₀ X²` uniformly in `S` and `χ`. For `p ∉ S` prime, partitioning squarefree `m` by whether `p ∣ m` yields `M_S^χ(Z) = M_{S ∪ {p}}^χ(Z) − χ(p) M_{S ∪ {p}}^χ(Z / p)` and, since `‖M_{S ∪ {p}}^χ(Z / p^K)‖ ≤ C₀ Z² p^{-2K} → 0`, the convergent geometric series `M_{S ∪ {p}}^χ(Z) = ∑_{k ≥ 0} χ(p)^k M_S^χ(Z / p^k)`. Inducting on `S = a.primeFactors` gives `‖M_{a.primeFactors}^χ(Z)‖ ≤ C (∏_{p ∣ a} (1 − p^{-b})⁻¹) Z^b` whenever `‖M_∅^χ(X)‖ ≤ C X^b` (`b > 0`). Splitting primes at `P₀ = ⌈4^{1/η}⌉₊` yields `∏_{p ∣ a} (1 − p^{-b})⁻¹ ≤ 4^{P₀} a^η` for all `b ≥ ½`, `a ≥ 1`.

### 2. One-step prime-window drop and exact principal `n`-th-power threshold (`n ≥ 2`)
Let `0 < θ < n/(n − 1)` and suppose `∑_{p ∈ (M, Q M]} ‖M_{{p}}^χ(Z)‖² = O_ε(Z^{θ + 1 + ε})` whenever `u_scale (Q M)^n ≤ Z^θ`. Fixing `Q = ⌈exp(2 c₁ + 1)⌉₊ + 1` (`c₁ = mertensFirstConst`) and `M = ⌊Z^{θ/n} / ((Q + 1) u_scale^{1/n})⌋₊`, Mertens' window estimate supplies `≫ Z^{θ/n} / log Z` primes `p ∈ (M, Q M]`. Averaging `‖M_∅^χ(Z)‖² ≤ 2 ‖M_{{p}}^χ(Z)‖² + 32 C_β² (Z / M)^{2β}` over `p ∈ (M, Q M]` lowers any global exponent `β ≥ ½` to every `b' > max(½ + (1 − 1/n)θ/2, β(1 − θ/n))`. Applying this at `β = Θ + δ` (`δ → 0⁺`) and noting `Θ(1 − θ/n) < Θ` forces `Θ ≤ min(1, ½ + (1 − 1/n)θ/2)`. Conversely, for `θ ≥ (n/(n − 1))(2 Θ_ζ − 1)`, taking `b = Θ_ζ + min(½, ε/6)` and `η = ε / (4(θ + 1))` bounds `principalTwistMeanSquare W n θ Z` by `O_ε(Z^{θ/n + 2b + 2θη}) = O_ε(Z^{θ + 1 + ε})`, establishing `{θ ≥ 0 : IsGenericMeanSquare (principalTwistMeanSquare W n) θ} = [(n/(n − 1))(2 Θ_ζ − 1), ∞)` with attained minimum `(n/(n − 1))(2 Θ_ζ − 1)` (`= 0 ↔ RiemannHypothesis`).

### 3. Sharp non-cancellative / operator-norm barrier `n/(n − 1)`
Replacing `μ(m)` by `μ(m)²` with `W = gaussianKernel c`, explicit squarefree sieving on `(N/9, N]` (`N = ⌊Z⌋₊ ≥ 36`) produces at least `N / 12` squarefree integers `m` avoiding any prime `p ≥ 19`, on each of which `signal(gaussianKernel c, 2, Z / m) > w_min(c) > 0`. Hence every prime twist `p^n ≤ Z^θ` (`p ≥ 19`) has sum `≥ γ Z`, so the `≫ Z^{θ/n} / log Z` prime `n`-th powers in `(M, Q M]` contribute `≫ Z^{2 + θ/n - ε}`, contradicting `O_ε(Z^{θ + 1 + ε})` whenever `θ < n/(n − 1)`. Above `n/(n − 1)`, absolute convergence at `s = 1 + δ` gives `O_ε(Z^{θ + 1 + ε})`.

### 4. Conductor-uniform Dirichlet subpolynomial lower bound and full Jacobi family (`n = 2`)
For primitive nonprincipal `χ` modulo `N`, shifting `Γ((w + d)/2)` (`d ∈ {0, 1}`) on `w = −2 + it`, `0 < |t| ≤ 2` places the `t = 0` pole of `Γ(w/2)` in the denominator of `L(w, χ)` in the functional equation, giving `‖L(−2 + it, χ)‖ ≤ A N^{5/2} (1 + |t|³)` with `A` absolute (extended to `t = 0` by continuity). Phragmén–Lindelöf on `−2 ≤ Re z ≤ 3` and two-radius three-circles interpolation at centre `a = 3` with uniform weight `θ_*(δ) < 1` across `zeroAbscissa χ ∈ [½, 1]` yield `‖L(s, χ)‖ ≥ κ(δ, ε) (N(2 + |Im s|))^{-ε}` (`κ(δ, ε) > 0` independent of `N, χ`), hence `‖signal(dirichletGaussianKernel χ c, 2, Z)‖ ≤ C(c, δ, η) N^η Z^b` for `b ∈ [zeroAbscissa χ + δ, 2]`. Decomposing odd `u = u₀ a²` (`u₀` squarefree) identifies `(m / u)` with `1_{gcd(m, a) = 1}` times the primitive CRT character `jacobiPrimChar u₀` (`u₀ > 1`) or `1` (`u₀ = 1`); prime subfamilies `u = p²` and `u = u₀ p²` force `Θ_ζ, zeroAbscissa(jacobiPrimChar u₀) ≤ min(1, ½ + θ/4)` at every `θ > 0`, while the conductor-uniform signal bound gives sufficiency for all `θ ≥ 0` under quadratic GRH.

### 5. Single-variable classification of the reflection-and-large-sieve producer class
Via `positiveFormTheta(n, σ₀) = (2n/(n − 1))(σ₀ − ½)`, the reflected optimal sextic multiplicative large sieve has sharp minimum `2β = 52/27` at `θ = 10/9 > 1` (and any Gauss-sum excess `u + v = 1 + η > 1` blocks `θ = 1`); the additive planar sieve `K + N` and dual diagonal have floor `θ = 1`; balanced `k ≥ 2` row designs satisfy `θ ≥ n/(n − 1)`; unslotted conductor corners `(2, 6), (3, 4), (4, 3)` give `14/15, 22/21, 11/9`; the published vertex reaches `θ = 9/10` (`δ = 79/204` binding in both Gram regimes); across all `n ≥ 2` and `(lx, ly, ℓ) ∈ ℝ³`, `probeThetaGen < (5n − 8)/(5(n − 1))` forces strictly positive floor-bin high exponent (`δ = 0, q = 0, R = 1`), attained at `(2/5, 2/5, 1/5)`; without the dual-length penalty, `2ℓ ≤ lx + ly` forces `probeThetaFree ≥ (n − 2)/(n − 1)`; and bounding reflected rows through the order-`n` twist family returns `(n/(n − 1))(2β − 1)` (`positiveFormBoundary = β`).

## Log
- 2026-11-11 — proved and formalized in `GaloisForLFunctions.FamilyContinuationTheory`.
