# The Weil energies of the arithmetic modes

- **ID:** rapt-weil-energies-of-the-arithmetic-modes
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** RAPT §9 topic 2 ("Open: the archimedean cross terms of distinct atoms on class
  profiles"); RP37, RP39; SSHA self-energy; ALG Robin–Euler threshold.
- **Statement:**
  - (A) For a bump `g ≥ 0` on `[0, w]` with `4w ≤ δ_N`, and `x_n = ψ(n)/√n` with `ψ` `q`-periodic,
    `|ψ| ≤ B` and of mean zero: `|L(f_x) − |x|² L(g)| ≤ 168 q B² (wN) ‖g‖²`.
  - (B) For a nonnegative Lipschitz `C²` profile `φ` on `[0, 1]`, a conductor `m ≥ 2` and
    `0 < K < 1/4`, the arithmetic mode `f_N = Σ_{n ≤ N} c_m(n)/√(φ(m) n) · φ((· − log n)N/K)` has
    `W(f_N)/‖f_N‖² → log(1/K) − log 2π + β(φ)/‖φ‖² + log m + d(m)`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized

## Paper proof

1. **Exact expansion.** The atoms are separated (`w < δ_N`), so `∫(f − f(·+s))² = |x|²∫(g − g(·+s))²
   − 2Σ_{m<n} x_m x_n G(s − log(n/m))`. Here `G` is the autocorrelation of `g`, and pairs with
   `m > n` vanish for `s > 0`. Integrating against `ω(s) = e^{−s/2}/(1 − e^{−2s})` gives
   `L(f_x) = |x|² L(g) − 2Σ_{m<n} x_m x_n Ω(log n − log m)`, with `Ω(t) = ∫_0^∞ ω(s) G(s − t) ds`.
2. **The cross kernel.** `G ≥ 0` is supported in `[−w, w]` with `G ≤ ‖g‖²`, and `ω` decreases. So
   `Ω(t) = ∫_{t−w}^{t+w} ω G` is nonnegative and decreasing in `t`. For `t ≥ 4w` it is at most
   `2w‖g‖² ω(t − w) ≤ 2w‖g‖²(1/t + 1)`.
3. **Linear pair sums.** Replace `Ω(t)` by `Φ(t) = Ω(max(t, δ_N))`; this agrees on all pairs.
   Group by gap `j = n − m`. The coefficient `ψ(m)ψ(m + j) − c_j` (with `c_j` the periodic
   autocorrelation) has partial sums `≤ 2qB²`. The kernel `Φ(log(1 + j/m))/√(m(m + j))` has
   total variation in `m` of `O(A N j^{−3/2})`, so Abel summation gives `O(qB²A N)` after summing
   over `j`. The remainder `Σ_j c_j T_j` has `c_j` periodic of mean zero and `T_j` decreasing, and a
   second Abel summation gives `O(qB² T_1) = O(qB²AN)`. In total `|S| ≤ 42 q B² A N` with
   `A = 2w‖g‖²`. This proves (A).
4. **Weil's form.** `W = M + 2A(f)B(f)` with `M = 2θ′(0)‖f‖² + L(f) − ‖g‖² P_N(x)`. The pole
   moments are `A(f) = A(g)Σψ(n)/n` and `B(f) = B(g)Σψ(n)`. Both sums are `≤ 2qB` by Abel
   summation against `1/n` and by periodicity, and `|A(g)| ≤ ∫g`, `|B(g)| ≤ e^{w/2}∫g`. So
   `|W − |x|²(2θ′(0)‖g‖² + L(g)) + ‖g‖² P_N(x)| ≤ 168 qB²(wN)‖g‖² + 8q²B² e^{w/2}(∫g)²`.
5. **Arithmetic modes.** `ψ = c_m/√φ(m)` is `m`-periodic, and for `m ≥ 2` it has mean zero
   (orthogonality to the conductor-one mode `1`). Take `w = K/N`. For `K < 1/4` and large `N`,
   `4K/N ≤ 1/(N + 1) ≤ δ_N`. The error over `|x|²‖g‖²` is `≤ C/|x|²` with `C` independent of `N`,
   because `‖g‖² = w‖φ‖²` and `(∫g)² = w²(∫φ)²`, and `|x|² ~ log N → ∞`. The self-energy satisfies
   `L(g)/‖g‖² = log(N/K) + κ_L(φ) + o(1)`. By Cauchy–Schwarz with the quasimode residual,
   `P_N(x)/|x|² = log N − γ − log m − d(m) + o(1)`. Summing, the `log N` cancels:
   `W/‖f‖² → 2θ′(0) + κ_L(φ) + γ + log(1/K) + log m + d(m)`, and
   `2θ′(0) + κ_L(φ) + γ = −log 2π + β(φ)/‖φ‖²`.

## Lean

- `RenormalizedArithmeticPotentialTheory/PeriodicPairSumsOfADecreasingKernelAreLinear.lean`:
  `abs_sum_periodicPair_le`.
- `RenormalizedArithmeticPotentialTheory/TheArchimedeanCrossTermsVanishOnPeriodicProfiles.lean`:
  `atomCrossKernel_nonneg`, `atomCrossKernel_anti`, `atomCrossKernel_le`,
  `levyEnergy_atomicTest_eq_cross`, `abs_levyEnergy_atomicTest_sub_le_of_periodic` (A).
- `RenormalizedArithmeticPotentialTheory/TheWeilEnergiesOfTheArithmeticModes.lean`:
  `abs_weilQuad_atomicTest_periodic_sub_le`, `sum_range_normalizedRamanujanMode`,
  `tendsto_atomicWeilForm_ramanujanPoleProfile_div`, `abs_weilQuad_arithmeticMode_div_sub_le`,
  `tendsto_weilQuad_arithmeticMode` (B).
- Axioms: `propext`, `Classical.choice`, `Quot.sound`.

## Limits

The cross bound needs `t ≥ 4w`, i.e. `K < 1/4`. The limit is `log(K_m/K)` with
`K_m = m e^{d(m)} e^{β(φ)/‖φ‖²}/(2π) > 1/4`, so on the proven range every mode with `m ≥ 2` has
positive limiting energy. Reaching the overlap regime `K ≈ K_m` requires `Ω` at `t < 4w`. That is
the open input for `selective-positivity-on-separated-atoms`.

## Evidence

Numerics at `K = 1/4` with the `sin²` profile, cross/mass for `N = 10³, 4·10³, 1.6·10⁴`:

| profile | `N = 10³` | `N = 4·10³` | `N = 1.6·10⁴` |
|---|---|---|---|
| pole | −0.160 | −0.161 | −0.162 |
| alternating | 0.0155 | 0.013 | 0.0113 |
| `c_3` | 0.0132 | 0.011 | 0.0094 |
| `χ_4` | 0.0071 | 0.0060 | 0.0053 |

## Log
- 2026-10-28 — created; formalized as RAPT RP40.
