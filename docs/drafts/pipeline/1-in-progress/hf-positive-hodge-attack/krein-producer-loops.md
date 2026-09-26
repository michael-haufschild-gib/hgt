# HF: structural producer of Krein-extendability at every level

- **ID:** hf-krein-producer
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (loop log) + THEOREM (Lean, structural core)
- **Source:** frontier map HF; facts HF-F11/F12/F13
- **Statement:** find a construction, not a numerical certificate, that gives for every aperture `a` a positive-definite completion of the level-`a` Weil kernel (mod polar plane).

## Goal
The level-`a` Hodge index (pole-vanishing Weil positivity on `L²(−a,a)`, HF-F11) holds iff the Weil kernel on `(−2a, 2a)` has a positive-definite completion to `ℝ` (Krein). Doing this at every level is Bombieri–Yoshida, i.e. RH. A structural producer builds the completions from arithmetic, so their positivity is visible.

Gates it must pass (frontier map): no slack, exact primes, individual zeros, exponent not constant.

## External state of the art (checked 2026-09-26)
- Suzuki, arXiv 2606.09096 (June 2026). Unifies Yoshida, Bombieri, Connes–Consani and CCM through the screw function and de Branges spaces. Conjectures a zero operator as the `a → ∞` limit of nonlocal realizations of `d/dx` on `[−a,a]`. This is the same level-wise Krein/de Branges chain; no producer.
- Alpöge–Furman, arXiv 2608.13637 (Aug 2026). They take a Gabor compression of Weil's form, split it as `G = P + Q`, and bound `n₊(Q) ≤ #off-line pairs` by Sylvester inertia, each pair being a `(1,1)` block. A rank-trace inequality `r ≥ 2tr P + 4tr Q − 4b − ‖P+Q‖²_HS` then gives ≥ 2/3 of zeros simple and on the line. This is a structural use of the Hodge signature, but only for proportions: second moments, subject to the individual-zeros gate.
- Zhu, arXiv 2608.24827: certified window positivity and Landau–Widom decay of `μ₀` (HF-F12).
- Bombieri (2000): for large truncations the number of negative eigenvalues is half the number of off-line zeros.

## Loops

### L1 — Semilocal Euler completion. FALSE
- **Conjecture.** Complete with the full local distributions of the visible primes: `K_S = arch + Σ_{p ≤ e^{2a}} Δ_p`. Its symbol is `2 Re(Λ_S'/Λ_S)(½+it)` with `Λ_S = π^{−s/2}Γ(s/2)Π_{p∈S}(1−p^{−s})^{−1}`.
- **Failure [P].** A finite Euler product has poles on `Re s = 0` and no zeros. So `Δ̂_p = log p − 2Σ_k P_{1/2}(t − 2πk/log p)`, where `P_y` is the Poisson kernel: a positive background minus pole bumps of height 4.
  - At `S = {2}`, `ξ = 1/log 2`: `W + Δ̂_2 ≈ 0.37 − 2log2(√2+1) ≈ −2.98 < 0`.
- **Lesson.** Local factors carry wrong-sign spectral mass (poles), so positive mass must come from elsewhere.

### L2 — Prime-by-prime completion. FALSE
- **Conjecture.** Complete each visible prime's tower `{k log p < 2a}` separately.
- **Failure [P].** The prime symbol is additively separable on the Euler torus. Carathéodory–Toeplitz on the KMS matrix `[p^{−|i−j|/2}]` shows every completion of the `p`-tower leaves a negative part of at least `log p/√p` (one visible power) and up to `2log p/(√p−1)`. The costs add to `≍ e^{a}` (MUST-261 in local form).
- **Lesson.** A producer must couple distinct primes through invisible composite frequencies.

### L3 — Selberg-weighted completion. STRUCTURAL CORE PROVED [L]; pointwise positivity heuristically FALSE
- **Construction.** Take a weight `w` with `w(d) = 1` on `[1, e^{2a}]` and set `Λ_w = (μw) ⋆ log`. Proved in `RHTower.SelbergTruncatedVonMangoldtKreinCompletion` (axioms: propext, Classical.choice, Quot.sound):
  - `Λ_w = Λ` on `n ≤ e^{2a}`, so `Λ_w` is a genuine Krein completion (`ccmRestrictedWeilSourceQuadraticWith_selberg_eq`: the Weil source quadratic is unchanged for every cutoff `N ≥ ⌊e^{2a}⌋`).
  - `Λ_w(p) = log p` at every prime, visible or not, and `Λ_w(p^k) = log p (k − (k−1)w(p))`. The only freedom is at composite and large-prime-power frequencies, which couple the primes.
  - `Σ Λ_w(n)n^{−s} = −M_w(s)ζ'(s)` with `M_w = Σ μ(d)w(d)d^{−s}`: no `1/ζ`, and the series is entire apart from `s = 1`.
- **Symbol [P].** `S_w(t) = 2θ'(t) + 2 Re(ζ'M_w)(½+it) + (explicit polar terms)`, with `θ` the Riemann–Siegel theta function (`W = 2θ'` exactly).
  - Equivalently, in Hardy form, `S_w = 2θ'(1 − Re F_w) + 2Z' Im(e^{−iθ}M_w)`, with `F_w = ζM_w` the mollified zeta on the line.
  - Unconditionally, as distributions, `S_w = Σ_{critical γ} 2πδ_γ + 2Re[ζ'(M_w − 1/ζ)]`.
  - For every `f ∈ L²(−a,a)` and every admissible `w`, `Q_a(f) = ∫ S_w |f̂|²`: an exact family of identities.
- **Pointwise positivity (conjecture SM).** Not proven false. Heuristically it fails for every fixed `w`:
  - mean of `S_w` is `2θ'` (the zero density);
  - fluctuations are of order `θ'·|ζM_w − 1|`, and the mollifier defect is `O(1)` in mean square at heights `t` with `log Y/log t` bounded (Conrey), so `S_w < 0` on a positive-density set;
  - a height-adaptive `w` reduces the level-`a` positivity at height `T` to a pointwise mollifier-defect bound near `T`.
- **Lesson.** HF-Krein's producer lands on the mollifier/Möbius terminus (route MC). Averages give proportions (compare Alpöge–Furman); a producer needs pointwise control.

### L4 — Finite-level resolution law. BRIDGE (not a producer)
- **Conjecture [P sketch].** If `μ₀(a) ≥ 0`, every zero satisfies `β − ½ ≤ (log log|γ| + C)/(2a)`.
- **Mechanism.** At the zero's height use the odd test `sinh(δu)1_{[−a,a]}`. The pair gives `−ĥ(iδ)²`, of order `e^{2aδ}/δ`; the real zeros give a background of order `log γ`.
- **Status.** This is a finite-level quantitative form of Bombieri's negative-index count and a receiver-type statement.
- **Open core.** Control of the other off-line pairs' contributions (smooth `h`, extremal choice of zero).

## Open core after L1–L4
A producer must create positive spectral mass exactly at the zeros, with no slack. Arithmetic completions give zero-indexed, sign-indefinite corrections: pole bumps (L1), separable local costs (L2), mollifier defect (L3).

Next conjectures to test:
- (a) The rank-trace (Alpöge–Furman) with higher Schatten moments. Does `‖G‖_{S_{2k}}` control `n₊(Q)` with slack `→ 0` as `k → ∞`? The operator-norm endpoint is `μ₀ ≥ 0`.
- (b) Whether the Burg (maximum-entropy) completion of the level-`a` Weil kernel has Selberg-type invisible weights. That would link the Krein extremal problem to Selberg's `Λ²` extremal problem.

## Log
- 2026-09-26 — L1–L4 run; Selberg completion core formalized (`RHTower.SelbergTruncatedVonMangoldtKreinCompletion`, wired, `lake build --old` green, lint pass).
