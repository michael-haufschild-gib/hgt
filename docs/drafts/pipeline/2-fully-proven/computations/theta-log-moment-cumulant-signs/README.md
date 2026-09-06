# Cumulant signs of the tilted theta measures (guidance computation, 2026-09-06)

**Question.** For the theta source `Φ(x) = Σ_n (2π²n⁴e^{9x/2} − 3πn²e^{5x/2}) e^{−πn²e^{2x}}` and the
tilted probability measures `P_s ∝ x^{2s}Φ(x)dx` on `(0,∞)`, do the cumulants `κ_k` of `W = log x`
alternate in sign, `(−1)^k κ_k > 0`, for all `k ≥ 3` and all tilts `s ≥ 0`? (Equivalently: is
`(log M_s)''` completely monotone, `M_s = ∫x^{2s}Φ`? Card
`1-in-progress/theta-log-moment-complete-monotonicity.md`.)

**Method.** `theta_cumulants.py` (mpmath, 40 digits, 60 theta atoms; also the single atom `n = 1`):
raw moments of `W` by quadrature in `w = log x` on `[−40, 3]`, cumulants by the standard recursion,
`k = 2..8`, `s ∈ {0, ¼, ½, 1, 2, 3, 5, 10, 20, 50, 100}`. Run on the pod, ~1 min.

**Result** (`theta_cumulants.out`). Sign pattern `+ − + − + − +` for `κ₂..κ₈` at every tilt, for
both kernels. Magnitudes: at `s = 0`, `κ_k ≈ (−1)^k (k−1)!` (`1.21, −2.10, 6.09, −24.1, 120.2,
−720.3, 5040.8`); at `s = ½`, `κ_k ≈ (−1)^k (k−1)!/2^k` to 1–5 %: the higher cumulants are dominated
by the exponential left tail of `W` (rate `2s+1`, i.e. the pole of `M_z` at `z = −½`). For `s ≥ 5`
the single atom and the full kernel agree to six digits, and the magnitudes follow the saddle law
`|κ_k| ≍ (k−2)!/(s^{k−1} log s)` with the same alternating signs.

**Status.** Guidance only; nothing here is used in a Lean proof. The conjecture survives the test.
