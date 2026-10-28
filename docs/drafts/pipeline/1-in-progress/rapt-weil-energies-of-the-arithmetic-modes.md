# The Weil energies of the arithmetic modes

- **ID:** rapt-weil-energies-of-the-arithmetic-modes
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Source:** RAPT §9 topic 2 ("Open: the archimedean cross terms of distinct atoms on class
  profiles"); RP37, RP39; SSHA self-energy; ALG Robin–Euler threshold.
- **Statement:**
  - (A) For a bump `g ≥ 0` on `[0, w]`, `w ≤ δ_N/4`, and `x_n = ψ(n)/√n` with `ψ` `q`-periodic,
    `|ψ| ≤ B` and mean zero, the archimedean cross term is bounded:
    `|L(f_x) − |x|² L(g)| ≤ C(q, B) (∫g)² N`, so it is `O(wN ‖g‖²) = o(‖g‖² |x|²)`.
  - (B) For the Ramanujan modes (`m ≥ 2`) at overlap `K = wN`:
    `W(f)/‖f‖² → log(1/K) − log 2π + shape(φ) + log m + d(m)`.
    So mode `m` has critical overlap ratio `m e^{d(m)} · e^{shape(φ)}/(2π)`.

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  fully-proven
- [ ] 2 → 3  formalized

## Proof plan

1. **Exact expansion.** For separated atoms, `L(f_x) = |x|² L(g) − 2 Σ_{m<n} x_m x_n Ω(m, n)` with
   `Ω(m, n) = ∫_0^∞ ω(s) G(s − log(n/m)) ds`, where `G` is the autocorrelation of `g`. Pairs with
   `m > n` vanish.
2. **Bounds on `Ω`.** With `g ≥ 0`: `0 ≤ Ω ≤ (∫g)² (1/(2(t − w)) + 1)`, and `Ω` decreases in
   `t = log(n/m)`, because `ω` decreases.
3. **Abel summation.** Write `n = m + j` and `F(m, j) = Ω/√(m(m + j))`. The total variation of
   `F(·, j)` is `≲ (∫g)² N j^{−3/2}`. Since `ψ(m)ψ(m + j) − c(j)` has bounded partial sums,
   `Σ_m ψψF = c(j) T(j) + O((∫g)² N j^{−3/2})`. The autocorrelation `c` is `q`-periodic with mean
   zero, and `T` decreases, so `Σ_j c(j) T(j) = O(T(1)) = O((∫g)² N)`.
4. **Weil energy.** Combine with the self-energy `L(g) = ‖g‖²(log(1/w) + κ_L(φ)) + O(w)`. The pole
   term is `O(wN/√N)`. For the prime part, use the Ramanujan quasimode Rayleigh quotients. Finally
   `2θ′(0) + γ + κ_arch = −log 2π`.

## Evidence

Numerics at `K = 1/4` with the `sin²` profile, cross/mass for `N = 10³, 4·10³, 1.6·10⁴`:

| profile | `N = 10³` | `N = 4·10³` | `N = 1.6·10⁴` |
|---|---|---|---|
| pole | −0.160 | −0.161 | −0.162 |
| alternating | 0.0155 | 0.013 | 0.0113 |
| `c_3` | 0.0132 | 0.011 | 0.0094 |
| `χ_4` | 0.0071 | 0.0060 | 0.0053 |

The pole stays at `≈ −K a₁²/a₂`, while the periodic mean-zero profiles decay like `1/log N`.

## Log
- 2026-10-28 — created; plan above.
