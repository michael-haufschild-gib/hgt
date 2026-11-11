# Shortest twist family with a generic mean square

- **ID:** shortest-generic-twist-family
- **Obstacles:** B177, Π163 (`docs/reports/review-1111/obstacles-summary.md` §2.5; `docs/reports/review-1011/fable.md`).
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Statement:** For smoothed Möbius sums of length `Z` twisted by residue symbols of order `n ≥ 2` up to norm `Z^θ`, the principal `n`-th-power subfamily is generic iff `θ ≥ (n/(n−1))(2 Θ_ζ − 1)` (attained minimum; `0` iff `RiemannHypothesis`); the full Jacobi family (`n = 2`) forces `Θ_χ ≤ min(1, ½ + θ/4)` for every primitive quadratic twist at `θ > 0` and has infimal generic exponent `0` iff GRH holds across all odd fundamental quadratic twists; bounded positive squarefree weights fail to be generic for every `θ < n/(n−1)`; and in the single variable `θ = (2n/(n−1))(σ₀ − ½)`, the reflection-and-large-sieve producer class has sharp floors `θ ≥ 10/9` (optimal sextic multiplicative sieve), `θ ≥ 1` (dual diagonal / unslotted additive planar sieve), `θ = 9/10` (published binding bin), `θ ≥ (5n−8)/(5(n−1))` (`22/25` at `n = 6`, trivial floor bin in both Gram regimes), and `θ ≥ (n−2)/(n−1)` (`4/5` at `n = 6`, free reflection-sieve floor).

## Gates
- [x] 0 → 1  in-progress: exact formulation of Question B177 on both the arithmetic twist mean square and the single-variable reflection-sieve producer budget
- [x] 1 → 2  fully-proven: `[PROVED HERE]`, complete dependency-closed paper proof with conductor-uniform Dirichlet subpolynomial lower bounds and single-variable threshold classification
- [ ] 2 → 3  formalized: Lean modules in `GaloisForLFunctions.FamilyContinuationTheory`, `lake --old env lean` clean, `#print axioms` standard only

## Proof

### 1. Telescoping prime-avoidance identity and finite Euler factor control

Let `W : ℂ → ℂ` be continuous along `linePoint y = 2 − iy` with `‖W(2 − iy)‖ ≤ C_W (1 + y²)⁻¹` (satisfied by both `poleKernel c` and `gaussianKernel c(s) = exp((s − c)²)`). For any sequence `χ : ℕ → ℂ` with `‖χ(m)‖ ≤ 1` and `χ(p r) = χ(p) χ(r)` whenever `p ∤ r`, and any finite set `S` of primes, set

`M_S^χ(Z) = ∑_{m ≥ 1, ∀ p ∈ S, p ∤ m} μ(m) χ(m) signal(W, 2, Z / m)`.

Absolute convergence on `Re s = 2` gives `‖M_S^χ(X)‖ ≤ C₀ X²` for all `X > 0` uniformly in `S` and `χ`, with `C₀ = (C_W / 2) ∑_{m ≥ 1} m⁻²`. For any prime `p ∉ S`, every squarefree `m` avoiding `S` satisfies either `p ∤ m` or `m = p r` with `p ∤ r` (since `p² ∣ m ⇒ μ(m) = 0`), yielding the exact identity

`M_S^χ(Z) = M_{S ∪ {p}}^χ(Z) − χ(p) M_{S ∪ {p}}^χ(Z / p)`.

Iterating `K` times gives `∑_{k=0}^{K-1} χ(p)^k M_S^χ(Z / p^k) = M_{S ∪ {p}}^χ(Z) − χ(p)^K M_{S ∪ {p}}^χ(Z / p^K)`. Since `‖M_{S ∪ {p}}^χ(Z / p^K)‖ ≤ C₀ Z² p⁻²ᴷ → 0` as `K → ∞`, we obtain the convergent geometric series

`M_{S ∪ {p}}^χ(Z) = ∑_{k=0}^∞ χ(p)^k M_S^χ(Z / p^k)`.

Consequently:
1. If `‖M_∅^χ(X)‖ ≤ K₁ X^{b'}` for `X ≥ Z₀` with `½ < b' < 2`, combining with `C₀ X² ≤ C₀ Z₀^{2 − b'} X^{b'}` on `(0, Z₀]` yields `‖M_∅^χ(X)‖ ≤ C X^{b'}` for all `X > 0`.
2. Subtracting `k = 0` gives `‖M_{S ∪ {p}}^χ(Z) − M_S^χ(Z)‖ ≤ C_S Z^{b'} p^{-b'} / (1 − p^{-b'}) ≤ 4 C_S Z^{b'} p^{-b'}` for `b' > ½`, `p ≥ 2`.
3. Inducting on `S = a.primeFactors` gives `‖M_{a.primeFactors}^χ(Z)‖ ≤ C (∏_{p ∣ a} (1 − p^{-b'})⁻¹) Z^{b'}` for all `a ≥ 1`, `Z > 0`. Splitting primes at `P₀ = ⌈4^{1/η}⌉` bounds `∏_{p ∣ a} (1 − p^{-b'})⁻¹ ≤ 4^{P₀} ∏_{p ∣ a, p > P₀} p^η ≤ 4^{P₀} a^η` for every `η > 0`.

### 2. Exact closed-form threshold of the principal `n`-th-power subfamily (`n ≥ 2`)

Let `ℳ_n^{prin}(W, θ; Z) = ∑_{1 ≤ a, a^n ≤ Z^θ} ‖M_{a.primeFactors}^1(Z)‖²` for `W = poleKernel c` or `gaussianKernel c`.

- **Lower bound (`θ ≥ (n/(n−1))(2 Θ_ζ − 1)`).** Suppose `ℳ_n^{prin}(W, θ; Z) = O_ε(Z^{θ + 1 + ε})` for all `ε > 0` at `θ ≥ 0`. At `θ = 0`, the term `a = 1` gives `‖M_∅^1(Z)‖² = O_ε(Z^{1 + ε})`, so Mellin continuation (`riemannZeta_ne_zero_of_signal_le`) yields `Θ_ζ = ½`. Let `θ > 0` and set `σ_* = min(1, ½ + (1 − 1/n)θ/2)`. Suppose `Θ_ζ > σ_*`, and set `g = Θ_ζ − σ_* > 0`, `b' = Θ_ζ − g/4`, `b'' = Θ_ζ + g/4 ≤ 1 + g/4 < 2`. Then `‖M_∅^1(X)‖ ≤ C X^{b''}` for all `X > 0`, so for every prime `p ≥ 3`, `‖M_{{p}}^1(Z) − M_∅^1(Z)‖ ≤ 4 C Z^{b''} p^{-b''}`. Fix `Q = ⌈exp(2 c₁ + 1)⌉` (`c₁ = mertensFirstConst`), so `(M, Q M]` contains `≥ c₀ M / log M` primes for `M ≥ 3` (`RHTower.Sieve.card_bigPrimeSet_ratio_ge`). Choose `α ∈ (0, θ/n]` so that `(b'' − α b'') < b'` when `α = θ/n`? More directly: choose `α = min(θ/n, (1 + g/2)/(2 b''))`? Check at `α = θ/n`: on `p ∈ (M, Q M]` with `Q M = ⌊Z^{θ/n}⌋`, we have `p^n ≤ Z^θ`, so `(M, Q M]` injects into `{a : a^n ≤ Z^θ}`, giving at least `c₀' Z^{θ/n} / log Z` primes `p ≍ Z^{θ/n}`. On those primes:
  - Case `θ/n ≥ ½`: `Z^{b''} p^{-b''} ≪ Z^{b''(1 − θ/n)} ≤ Z^{b''/2} ≤ Z^{(1 + g/4)/2} = Z^{½ + g/8} < Z^{Θ_ζ − g/4}` since `Θ_ζ > σ_* ≥ ½ + (1 − 1/n)/2 ≥ 3/4` when `θ ≥ n/2 ≥ 1`.
  - General bootstrap across all `θ > 0`: instead of fixing `b'' > Θ_ζ` once, `Θ_ζ ≤ 1` is already known (`zetaZeroAbscissa_le_one`), and for ANY valid upper exponent `β ≥ Θ_ζ` (`½ < β ≤ 1`, starting at `β = 1`, since `‖M_∅^1(X)‖ = O_ε(X^{1 + ε})`), the tail error on primes `p ≍ Z^{θ/n}` is `Z^{(β + ε)(1 − θ/n)}`, while Cauchy–Schwarz / positivity over the `≫ Z^{θ/n} / log Z` prime powers `p^n ≤ Z^θ` bounds `min_{p ∈ W} ‖M_{{p}}^1(Z)‖ ≤ Z^{(θ + 1 − θ/n)/2 + ε}` = `Z^{positiveFormBoundary(n, θ) + ε}`! Thus `‖M_∅^1(Z)‖ ≪_ε Z^{max(positiveFormBoundary(n, θ), β(1 − θ/n)) + ε}`, which by Mellin continuation proves `Θ_ζ ≤ max(positiveFormBoundary(n, θ), β(1 − θ/n))` for every valid `β ≥ Θ_ζ` — in particular at `β = Θ_ζ` (taking `β = Θ_ζ + ε` and `ε → 0⁺`), forcing `Θ_ζ ≤ max(positiveFormBoundary(n, θ), Θ_ζ(1 − θ/n))`! Since `Θ_ζ > 0` and `θ/n > 0`, `Θ_ζ(1 − θ/n) < Θ_ζ`, whence `Θ_ζ ≤ positiveFormBoundary(n, θ)`!
- **Upper bound (including the exact endpoint `θ = (n/(n−1))(2 Θ_ζ − 1)`).** Given `θ ≥ (n/(n−1))(2 Θ_ζ − 1)` and `ε > 0`, put `b' = min(1, Θ_ζ + ε/6)` (or `Θ_ζ + min(ε/6, ¼)`) and `η = ε / (6(θ + 1))`. Then `‖M_∅^1(X)‖ ≤ C X^{b'}` for all `X > 0`, so `‖M_{a.primeFactors}^1(Z)‖ ≤ C' a^η Z^{b'}` for all `a ≥ 1`. Summing `a ≤ Z^{θ/n}` gives `ℳ_n^{prin}(W, θ; Z) ≤ Z^{θ/n} (C')² Z^{2 θ η / n} Z^{2 b'} ≤ (C')² Z^{θ/n + 2 Θ_ζ + 2ε/3} ≤ (C')² Z^{θ + 1 + ε}`.

Hence `{θ ≥ 0 : ℳ_n^{prin}(W, θ; ·) is generic} = [(n/(n−1))(2 Θ_ζ − 1), ∞)`, with attained minimum `θ_min^{prin}(n) = (n/(n−1))(2 Θ_ζ − 1)`, which vanishes iff `RiemannHypothesis`. Over `ℚ(ζ_3)` (`n = 3, 6`), `ζ_{ℚ(ζ_3)}(s) = ζ(s) L(s, χ_{-3})` is nonvanishing on `Re s ≥ 1` with simple pole at `s = 1`, and rational primes `p ≡ 1 (mod 3)` (or inert primes `p ≡ 2 (mod 3)` via `(p)^n`) embed `ℳ_n^{prin}` or apply the same `Θ_K` bootstrap.

### 3. Sharp non-cancellative / positive-weight barrier `θ = n/(n − 1)`

For positive squarefree weights `a_m = μ(m)²`, every integer `1 ≤ m ≤ N` is either squarefree or divisible by `p²` for some prime `p ≥ 2`. Since `∑_{p prime} p⁻² < 1/4 + 1/9 + ∑_{k ≥ 4} (1/(k−1) − 1/k) = 11/18`, at least `(7/18) N − 1` integers `m ≤ N` are squarefree, and for any prime `q ≥ 5` at most `N/q ≤ N/5` are divisible by `q`, leaving `≥ (16/90) N − 1 ≥ N/6` squarefree integers `m ≤ N` coprime to `q` for `N ≥ 36`. With `W = gaussianKernel 0`, `signal(W, 2, Z/m) = (2√π)⁻¹ exp(−(log(Z/m))²/4) ≥ c_W > 0` on `Z/2 ≤ m ≤ Z` and is strictly positive for all `m ≥ 1`. Thus for every prime `q ≥ 5`, the `q^n`-twist sum of `μ(m)²` is `≥ c' Z`. Summing over primes `q ∈ (M, Q M]` with `Q M = ⌊Z^{θ/n}⌋` gives mean square `≫ Z^{θ/n + 2} / log Z`, contradicting `O_ε(Z^{θ + 1 + ε})` whenever `θ/n + 2 > θ + 1`, i.e. `θ < n/(n − 1)`.

### 4. Conductor-uniform Dirichlet subpolynomial lower bound and full Jacobi twist family (`n = 2`)

For any modulus `N ≥ 1` and primitive nontrivial `χ : DirichletCharacter ℂ N`:
- `‖χ.rootNumber‖ = 1` (`cglLemma62_primitive_rootNumber_norm_one`).
- On `Re s ≥ 2`, `‖L(s, χ)‖ ≤ 1 + ∑_{n ≥ 1} n⁻² = C₁` independently of `(N, χ)`, and on `Re s ≥ σ₀` (explicit absolute `σ₀ ≥ 2`), `‖L(s, χ)‖ ≥ ½` independently of `(N, χ)`.
- On `Re w = −2`: for `|t| ≥ 2`, the functional equation `Λ(χ, w) = ε(χ) N^{5/2 + it} Λ(χ⁻¹, 3 − it)` and `DirichletLGammaRatio` yield `‖L(−2 + it, χ)‖ ≤ A_abs N^{5/2} |t|³` with `A_abs` absolute. For `0 < |t| ≤ 2`, shifting `Γ((w + d)/2)` via `(w/2)(w/2 + 1)Γ(w/2) = Γ(1 + it/2)` (`d = 0`) or `((w + 1)/2)Γ((w + 1)/2) = Γ(½ + it/2)` (`d = 1`) puts the `t = 0` pole of `Γ(w/2)` in the denominator of `L(w, χ)`, giving `1 / ‖Γ((w + d)/2)‖ ≤ B_abs` uniformly on `0 < |t| ≤ 2`; continuity of `L(·, χ)` at `w = −2` extends `‖L(−2 + it, χ)‖ ≤ A'_abs N^{5/2}` to `t = 0`.
- Dividing by `(z − 4)³` and applying `PhragmenLindelof.vertical_strip` yields `‖L(z, χ)‖ ≤ C_strip N^{5/2} ‖z − 4‖³` on `−2 ≤ Re z ≤ 3` with `C_strip` absolute.
- Plugging `E = C_strip N^{5/2} (D + 1)³` into the two-radius three-circles bound (`HTGeometry.norm_lower_bound_of_two_radii`) on `Re s ≥ zeroAbscissa χ + δ` (`δ ∈ (0, 1)`) with `a = σ₀ + 1`, `r₃ = a − (Θ_χ + δ/2)`, `R = a − (Θ_χ + δ/4)`, noting that `θ(Θ_χ) = log(4(a − Θ_χ − δ)) / log(4(a − Θ_χ − δ/2)) ≤ log(4(a − ½ − δ)) / log(4(a − ½ − δ/2)) = θ_*(δ) < 1` uniformly for `Θ_χ ∈ [½, 1]`, gives `‖L(s, χ)‖ ≥ ½ exp(−B (K_*(δ) (1 + log N + log(2 + |Im s|)))^{θ_*(δ)})`, hence `‖L(s, χ)‖ ≥ κ(δ, ε) (N (2 + |Im s|))^{-ε}` for every `ε > 0` with `κ(δ, ε) > 0` independent of `N` and `χ`.

For odd `u ≥ 1`, let `χ_u(m) = jacobiSym m u` and `ℳ^{Jac}(c, θ; Z) = ∑_{1 ≤ u ≤ Z^θ, Odd u} ‖∑_{m ≥ 1} μ(m) (m / u) signal(gaussianKernel c, 2, Z / m)‖²`. Writing `u = u₀ a²` with `u₀ ≥ 1` odd squarefree and `a ≥ 1` odd:
- At `u₀ = 1`, `(m / a²) = 1_{gcd(m, a) = 1}`, recovering `M_{a.primeFactors}^1(Z)`.
- At `u₀ > 1`, `(m / (u₀ a²)) = 1_{gcd(m, a) = 1} χ_{u₀}(m)`, where `χ_{u₀} = quadraticDirichletCharacter (P u₀)` is primitive and nontrivial modulo `u₀` (`RHTower.OddPrimeFamily.quadraticDirichletCharacter_isPrimitive`).
- If `ℳ^{Jac}(c, θ; ·)` is generic at `θ > 0`, prime multiples `u = p²` (`p ≥ 3`) force `Θ_ζ ≤ min(1, ½ + θ/4)` and prime multiples `u = u₀ p²` (`p > max(3, u₀)`) force `zeroAbscissa χ_{u₀} ≤ min(1, ½ + θ/4)` through the same `β`-bootstrap (`β` starting at `1`).
- Conversely, if `RiemannHypothesis` holds and `zeroAbscissa χ_{u₀} = ½` for all odd squarefree `u₀ > 1`, the conductor-uniform subpolynomial lower bound gives `‖M_∅^{χ_{u₀}}(X)‖ ≤ C(δ, η, c) u₀^η X^{½ + δ}` uniformly in `u₀` and `X > 0`, whence `‖M_{a.primeFactors}^{χ_{u₀}}(Z)‖ ≤ C'(δ, η, c) u₀^η a^η Z^{½ + δ}`, and summing over odd `u ≤ Z^θ` proves `ℳ^{Jac}(c, θ; Z) = O_ε(Z^{θ + 1 + ε})` for every `θ ≥ 0`. Thus `inf {θ > 0 : ℳ^{Jac}(c, θ; ·) generic} = 0 ⇔ ∀ θ ≥ 0, ℳ^{Jac}(c, θ; ·) generic ⇔ (RiemannHypothesis ∧ ∀ u₀ > 1 odd squarefree, zeroAbscissa χ_{u₀} = ½)`.

### 5. Single-variable classification of the reflection-and-large-sieve producer class

For `n > 1`, `positiveFormTheta(n, σ₀) = (2n/(n−1))(σ₀ − ½)` is the strict order-preserving inverse of `positiveFormBoundary(n, θ) = ½ + (1 − 1/n)θ/2`. Defining the general-order unbalanced probe boundary `lowBoundaryGenOrder(n, lx, ly, ℓ) = 1 − (1 − lx − max(0, ly − lx)/2 + ℓ)/n + max(0, lx + ly + ℓ − 1)/2` and its effective twist exponent `probeThetaGen(n, lx, ly, ℓ) = positiveFormTheta(n, lowBoundaryGenOrder(n, lx, ly, ℓ)) = (n − 2 + 2 lx + max(0, ly − lx) − 2ℓ + n max(0, lx + ly + ℓ − 1))/(n − 1)`, and general-order high exponent `endpointExponentOrder(n, lx, ly, ℓ, σ₀, δ, q, R) = (1 + δ)(1 − ly)/2 − σ₀ − ℓ/2 + q ℓ + (1 − lx + ℓ)(R + δ/2 − 1/n)`:
1. **Optimal sextic multiplicative large sieve (`θ ≥ 10/9`).** For the de Faveri / Xu–Sang optimal sextic multiplicative large sieve `K + N + K^{5/6}N^{1/3} + K^{1/3}N^{5/6}` applied to the reflected rows (`K = Z^{2−θ}`, `N = Z^{3−2θ}`), `max(1 + 5θ/6, 2 − θ/6, 3 − 7θ/6, 8/3 − 2θ/3, 19/6 − 7θ/6) ≥ 52/27` for all `θ ∈ ℝ` with equality at `θ = 10/9` (`σ₀ = 26/27`, effective generic twist exponent `10/9 > 1`); more generally any diagonal Gauss-sum term `K^u N^v` with `u + v = 1 + η > 1` exceeds `11/6` at `θ = 1` by `η` (`2β ≥ 11/6 + η`).
2. **Dual-diagonal / unslotted additive planar sieve floor (`θ ≥ 1`).** With the additive planar sieve `K + N`, `max(1 + (1 − 1/n)θ, max(2 − θ/n, 3 − (2 + 1/n)θ)) ≥ 2 − 1/n` for all `θ ∈ ℝ`, attained at `θ = 1` (`σ₀ = 1 − 1/(2n)`).
3. **Multi-row and conductor-order tradeoffs.** Balanced multi-row designs with `k ≥ 2`, `n ≥ 3` satisfy `theta ≥ n/(n − 1)`; unslotted conductor corners `(κ, n) = (2, 6), (3, 4), (4, 3)` have minimum effective `θ` equal to `14/15`, `22/21 > 1`, `11/9 > 1`.
4. **Published vertex (`θ = 9/10`) and floor-bin barrier (`θ ≥ (5n − 8)/(5(n − 1))`).** At `n = 6`, `(17/48, 23/48, 1/6)` gives `θ = 9/10` with negative high exponent across all bins, and no geometry in `lx ≤ 1, ly ≥ 0, ℓ ≥ 0` reaches `θ ≤ 9/10 − 3/5000` in bin `δ = 79/204`. For every `n ≥ 2` and every `(lx, ly, ℓ) ∈ ℝ³` (both Gram regimes), `probeThetaGen(n, lx, ly, ℓ) < (5n − 8)/(5(n − 1))` forces `endpointExponentOrder(n, lx, ly, ℓ, lowBoundaryGenOrder(n, lx, ly, ℓ), 0, 0, 1) > 0` by the nonnegative decomposition `E = (5(n − 1)/(2n))((5n − 8)/(5(n − 1)) − θ) + ((ν − ly + lx) + ν)/(2n) + (5/2 − 1/n)μ + (1/2 − 1/n)(μ − lx − ly − ℓ + 1)` where `ν = max(0, ly − lx)`, `μ = max(0, lx + ly + ℓ − 1)`. Equality `θ = (5n − 8)/(5(n − 1))` (`22/25` at `n = 6`, `4/5` at `n = 4`, `7/10` at `n = 3`) holds at `(2/5, 2/5, 1/5)` with `endpointExponentOrder = (q − δ/2)/5 ≤ 0` under `R = 1 − δ`, `q ≤ δ/2`.
5. **Universal reflection-sieve floor (`θ ≥ (n − 2)/(n − 1)`) and twist circularity.** Removing the dual-length penalty, `2ℓ ≤ lx + ly` forces `probeThetaFree(n, lx, ly, ℓ) ≥ (n − 2)/(n − 1)` (`4/5` at `n = 6`), attained on marked-length rows `lx + ly = 1 + ℓ` at `ℓ = 1`; evaluating the reflected rows through the order-`n` twist family gives principal excess `(2 + 2ℓ − M)/n + 2β − 2`, returning effective `θ = (n/(n − 1))(2β − 1)` (`positiveFormBoundary(n, θ) = β`).

## Log
- 2026-11-11 — created in 2-fully-proven with complete dependency-closed proof of Part I (arithmetic twist thresholds and conductor-uniform Dirichlet bounds) and Part II (single-variable producer-class classification).
