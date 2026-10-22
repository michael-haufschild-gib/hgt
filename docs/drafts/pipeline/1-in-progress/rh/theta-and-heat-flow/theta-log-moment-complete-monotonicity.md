# The continued theta moments: complete monotonicity of `(log M_z)''` and the sign law of all tilted cumulants

- **ID:** `theta-log-moment-complete-monotonicity`
- **Stage:** 1-in-progress (conjecture under attack)
- **Type:** CONJECTURE (source law, pre-divisor) — successor of `jensen-quartic-dispersion-transfer.md`
  after the Holland audit (arXiv:2608.08682)
- **Source objects:** `Φ = thetaCuspFullSource` (Riemann's kernel in the log variable, `Ξ(t) = ∫Φ(x)cos(tx)dx`),
  the raw even moments `m(k) = thetaCuspRawEvenMoment k = 2∫₀^∞ x^{2k}Φ(x)dx`, their continuation
  `M_z := ∫₀^∞ x^{2z}Φ(x)dx` (Holland's `M_z`, `Re z > −½`), the tilted probability measures
  `P_s ∝ x^{2s}Φ(x)dx` on `(0,∞)`, and the statistic `W = log x`.

## The conjecture

Let `h(s) := log M_s` for real `s > −½`. Then `h^{(k)}(s)` is the `k`-th cumulant of `2W` under `P_s`
(`P_s` is the exponential family with natural parameter `2s` and sufficient statistic `W`; `h''(s) =
4·Var_{P_s}(W)`, Holland's saddle law `h''(x) = 2/(x𝓛_x)(1+O(1/𝓛_x))` for large `x`).

**Conjecture (CM).** `h''` is completely monotone on `(−½, ∞)`: `(−1)^k h^{(k)}(s) > 0` for every
`k ≥ 2` and every `s > −½`. Equivalently (Bernstein), `h''(s) = ∫₀^∞ e^{−su} dν(u)` for a positive
measure `ν`; equivalently, under every tilt the cumulants of `W = log x` alternate:
`κ₂ > 0, κ₃ < 0, κ₄ > 0, …`.

**Structural reading.** For the Gamma family (`Φ = e^{−x²}`-type kernels) `h = log Γ(s + ½) + const`
and `h'' = ψ'(s+½)` is CM: the theta kernel would share with the Gamma kernel the *complete* sign
law of its log-moment derivatives, not only the three signs (`h'' > 0`, `h''' < 0`, `h⁗ > 0`) that
Holland's Laguerre → Jacobi → finite-free matching consumes. In Thorin–Bondesson language: the law
of `−W` (up to shift, and after accounting for the double-exponential right tail of `W`) has the
generalized-gamma-convolution structure — its log-mgf has CM second derivative.

**Pole structure (exact).** `Φ` is even and analytic at `0` with `Φ(0) > 0`, so the density of `W`
is `ρ(w) = e^{w}Φ(e^{w}) = Σ_j Φ^{(2j)}(0) e^{(2j+1)w}/(2j)!` as `w → −∞`. Hence `M_z` is meromorphic
in `z` with simple poles exactly at `z = −(j + ½)`, `j ≥ 0`, residues `Φ^{(2j)}(0)/(2·(2j)!)`. The
pole-only Hadamard structure would give `h''(x) = Σ_j (x + j + ½)^{−2} = ψ'(x + ½) ≍ 1/x`, which is
*larger* than the true `2/(x log x)`; so `M_z` must have zeros, necessarily off the real segment
`(−½, ∞)` (Holland: `M_z ≠ 0` on a sector), whose contribution `−Σ_ζ (ζ − x)^{−2}` cuts `1/x` down to
`2/(x log x)`. Therefore `1/M_z` is **not** a Laguerre–Pólya function and `ρ` is **not** a Pólya
frequency function of infinite order; CM of `h''` is the weaker, real-axis statement.

**What is at stake.** Holland's wedge uses exactly three defect signs. With all signs, a `K`-factor
finite-free Jacobi tower matches `2K+1` ratios with positive parameters; but the model-matching
residual is `≍ (d + 2√(nd))^{2K+1}/(n^{2K}(2K+1)! log n)`, so even the full tower stops at
`d ≍ n log n` (CANNOT-322). CM is therefore a *source law about `Φ`* (pre-divisor), of the same kind
as the theta log-concavity laws already in the corpus, and not an RH producer by itself. Its
falsity would locate the first order at which the theta family stops being Gamma-like.

## Falsification tests (pod, guidance only; `2-fully-proven/computations/` if kept)

`theta_cumulants.py`: cumulants `κ₂..κ₈` of `W` under `P_s` for `s ∈ {0, ¼, ½, 1, 2, 3, 5, 10, 20, 50, 100}`,
full kernel (60 atoms) and single atom. First results (`s ≤ 1`, full kernel): signs `+ − + − + − +`
at every `s`; at `s = 0` the values are `1.21, −2.10, 6.09, −24.1, 120.2, −720.3, 5040.8`, i.e.
`(−1)^k (k−1)!` to within a few percent: the pole at `z = −½` (left exponential tail of `W` with
rate `2s + 1`) dominates every higher cumulant, `κ_k ≈ (−1)^k (k−1)!/(2s+1)^k` (at `s = ½`:
predicted `0.25, −0.25, 0.375, −0.75, 1.875, −5.625, 19.69`; observed `0.39, −0.30, 0.41, −0.78,
1.91, −5.67, 19.77`). The bulk (saddle) cumulants `(−1)^k (k−2)!·2/(s^{k−1} log s)` carry the same
sign, so the two mechanisms never compete in sign. Large-`s` and single-atom results: pending.

## Paper-proof plan (if the tests pass)

1. Exact decomposition of `h''` into the pole series and a remainder: `h''(s) = ψ'(s+½) − R(s)` with
   `R ≥ 0` explicit from the zeros/growth of `M_z`; CM needs `R` to be "CM-subordinate".
2. Alternative route avoiding zeros of `M_z`: the tilt measures `P_s` in the variable `y = e^{2x}`
   are `(½ log y)^{2s} Σ_n (2π²n⁴y^{5/4} − 3πn²y^{1/4}) e^{−πn²y} dy`; each atom is a Gamma-type
   law in `y` twisted by `(log y)^{2s}`; cumulant signs of `log log y` under Gamma laws.
3. Lean target (unconditional, source-only): the first new order, `h⁗ > 0` on all of `(−½, ∞)`
   (the corpus has `h'' ≥ 0` at integers via moment log-convexity, and Holland has `h''' < 0`
   only asymptotically).

## Gates

- G1: numerical alternation through `k = 8` for `s ≤ 100`, full kernel and single atom.
- G2: exact statement of the pole/zero decomposition of `h''`.
- G3: proof of `h''' < 0` (dispersions decrease) at all real tilts; then `h⁗ > 0`.
- G4: anti-theatre: is CM (or GGC of `−W`) a known property of theta-kernel log-moments? Search
  Bondesson/Thorin literature and the corpus before proving.

## Log

- 2026-09-06 — G1 passed: `κ₂..κ₈` alternate at every tested tilt `s ∈ {0,…,100}`, full kernel and
  single atom (`2-fully-proven/computations/theta-log-moment-cumulant-signs/`). Two regimes, one sign
  pattern: pole-dominated (`κ_k ≈ (−1)^k(k−1)!/(2s+1)^k`, `s ≲ 1`) and saddle-dominated
  (`|κ_k| ≍ (k−2)!/(s^{k−1}log s)`, `s ≳ 5`), where the single atom already gives six digits.
  Consequence: the law is archimedean (the second theta atom enters the tilted moments only at relative
  size `2^{−4s/log(s/π)}`, since `Φ_n(x) = n^{−1/2}Φ₁(x + log n)` is a translate of the first atom
  and the tilted mode sits at `e^{2x_s} ≈ s/π`). By the corpus's no-archimedean-universality law it
  cannot carry RH information; it is a source law of the theta-log-concavity type.
- Literature check: Michalowski, arXiv:2602.20313 (v2), certifies that the de Bruijn–Newman kernel
  `Φ(|u|)` is not `PF₅` (a `5×5` Toeplitz minor at `(u₀,h) = (0.01, 0.05)` is `≈ −1.85·10⁻⁹`). This
  concerns total positivity of `Φ` in the linear variable; the present law concerns the tilted
  cumulants in the logarithmic variable and is consistent with `ρ(w) = e^wΦ(e^w)` *not* being `PF_∞`
  (`M_z` must have zeros, see above). No literature statement of the tilted-cumulant sign law found.
- Verdict for the RH goal: INSIGNIFICANT as a producer (archimedean, RH-blind by CANNOT-322 /
  no-archimedean-universality); kept as a tested source conjecture with a Lean-shaped first target
  (`h''' < 0` on all real tilts). Not pursued further in the RH programme unless an arithmetic
  consumer appears.
