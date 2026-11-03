# The Canonical System of the Window Tower (CSW)

Namespace `GaloisForLFunctions.CanonicalSystemOfTheWindowTower`; umbrella
`CanonicalSystemOfTheWindowTower.lean`. Every theorem is unconditional; equivalences with RH are
labelled. Companion of GWZ (`GrowingWindowsOfSpecZ`, kick law, lattice Schur parameters): CSW
computes the frozen two-collar data in closed form and states window growth as a continuum Schur
step.

## 1. Question

Review-0311 §2.5.1: for every prime-power stage `n = N+1` and collar width `ε`, compute the frozen
two-collar form `S^N_ε`, its evolution in `ε` and across stages, and its collar coupling in closed
form at the first two prime stages.

## 2. Answer

| Part | Statement | Lean |
|---|---|---|
| Coupling kernel | Ordered tests `f < g` couple through `κ(x) = 2cosh(x/2) − ω(x) = e^{x/2} − e^{−x/2}/(e^{2x}−1)` and the folds: `Q(f+g) = Q(f) + Q(g) + 2(∫_0^∞ κ c_{fg} − Σ_n Λ(n)n^{−1/2} c_{fg}(log n))` | `weilQuad_add_of_ordered`, `two_mul_cosh_sub_archLevyDensity` |
| Trivial divisor | `κ(x) = e^{(1−½)x} − Σ_{k≥1} e^{(−2k−½)x}`: pole `s = 1` with `+`, trivial zeros `s = −2k` with `−`; the Gamma pole `s = 0` cancels against the pole term | `hasSum_collarKernel` |
| Transmission | Across a cut the archimedean place and the pole transmit only the trivial-divisor moments: `∫_0^∞ κ c_{fg} = μ_1(f)ν_1(g) − Σ_{k≥1} μ_{−2k}(f)ν_{−2k}(g)` | `OrderedAt.integral_collarKernel_mul_eq_moments`, `weilQuad_add_of_ordered_of_primeFree` |
| Gluing | `Q(f+g+h) = Q(f+g) + Q(g+h) − Q(g) + 2Ξ(f,h)` for ordered pieces: a window is two windows of the previous length glued along the interior | `weilQuad_chain_three` |
| Two-collar identity | On a stage test `x_L + y + x_R`: `Q = F − 2w⟨x_L, J x_R⟩`, `F = Q(x_L+y) + Q(y+x_R) − Q(y) + 2⟨μ(x_L), ν(x_R)⟩`; `F` is the stage datum `Q_N` | `weilQuad_stageTest`, `stageForm_stageTest`, `stage_nonneg_iff` |
| Closed form | `F = Q(x_L) + Q(y) + Q(x_R) + 2(⟨μ(x_L),ν(y)⟩ + ⟨μ(y),ν(x_R)⟩ + ⟨μ(x_L),ν(x_R)⟩) − 2Σ_{m<n} w_m(⟨x_L,τ_m y⟩ + ⟨y,τ_m x_R⟩)`: the interior receives the trivial-divisor moments and the earlier-fold transports of the collars | `frozenTwoCollar_eq_transmitted` |
| Stage 1 | No earlier fold: the frozen form sees the collars through `Q(x_L)`, `Q(x_R)` and their moment sequences only | `firstStage_frozenTwoCollar_eq`, `firstStage_frozen_congr` |
| Stage 2 | The only earlier fold is `T₂`: moments plus `−2w₂(⟨x_L,τ₂y⟩ + ⟨y,τ₂x_R⟩)` | `secondStage_frozenTwoCollar_eq` |
| Growth law | `Q ≥ 0` on `W_{ℓ+ε}` ⟺ `Q ≥ 0` on `W_ℓ` and `W(τ_εu, v)² ≤ Q(u)Q(v)` for all `u, v` on `W_ℓ`: window growth is a translation contraction | `window_nonneg_iff_contraction` |
| Stage disk | At `ℓ = log(N+1)`: `W(τ_εu, v) = W_N(τ_εu, v) − w∫u(y)v(y+ℓ−ε)`; the fold lies in the disk of centre the frozen pairing and radius `√(Q(u)Q(v))` | `weilPair_stage_eq`, `stage_nonneg_iff_disk` |
| RH | RH ⟺ every growth step is a translation contraction | `riemannHypothesis_iff_translation_contraction` |

Evolution: in `ε` the disk centre moves by translation of one previous-window test against the
other (linear); across a stage the coupling receives the impulse `−w⟨x_L, J x_R⟩`, entering through
the lag `ℓ − ε`; composite stages carry none. The Riccati form of the law is the elimination of the
interior in the chain law.

## 3. Objects

| Object | Lean | Meaning |
|---|---|---|
| Ordered pair | `OrderedAt a f g` | `f = 0` right of `a`, `g = 0` left of `a` |
| Cross-correlation | `crossCorr f g x` | `∫ f(u) g(u + x)` |
| Collar kernel | `collarKernel x` | `e^{x/2} − e^{−x/2}/(e^{2x} − 1)` |
| Ordered coupling | `orderedCoupling f g` | `∫_0^∞ κ c_{fg} − Σ_n Λ(n)n^{−1/2} c_{fg}(log n)` |
| Moments | `leftMoment f σ`, `rightMoment g σ`, `trivialExponent k` | `∫ f e^{−σu}`, `∫ g e^{σv}`, `σ_k = −(2(k+1) + ½)` |
| Moment pairing | `momentPairing f g` | `μ_{1/2}ν_{1/2} − Σ_k μ_{σ_k}ν_{σ_k}` |
| Frozen two-collar form | `frozenTwoCollar xL y xR` | `Q(x_L+y) + Q(y+x_R) − Q(y) + 2⟨μ(x_L), ν(x_R)⟩` |
| Frozen pairing | `frozenPair N f g` | polarization of the stage datum `Q_N` |

## 4. Open

The interior infimum `inf_y F` as an operator on collar data (the universal function `Φ_ε` of the
moments at stage 1); the continuum limit of the chain law as a Riccati equation on the moment space.
