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
- **Finite-cutoff symbol [L]** (`ccmRestrictedWeilSourceQuadratic_eq_integral_selbergSymbol`). On pole-vanishing inputs, `Q_a(u) = ∫ weilAtomSymbol(Λ_w, N) |û|²` for every `N ≥ ⌊e^{2a}⌋`, with `weilAtomSymbol(λ,N) = W − Σ_{2≤n≤N} 2λ(n)n^{−½}cos(2πξ log n)`.
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

### L5 — Rank-trace with higher Schatten moments. INSIGNIFICANT as a producer
- **Conjecture.** Bounds on `n₊(Q)` from `tr G^k`, `k ≥ 3`, with slack `→ 0` as `k → ∞`.
- **Failure [P].** Normalized moments `(1/d)tr G^k` of a `d`-dimensional compression move by `O(1/d)` when `o(d)` eigenvalues change sign. So every fixed-`k` moment method is blind to `o(d)` negative eigenvalues (the individual-zeros gate).
- **Inputs.** Computing `tr G^k` needs `k`-level correlations. They are unconditional only for restricted total Fourier support, which forces the Gabor window to shrink like `1/k`.
- **Survivor.** A possible improvement of Alpöge–Furman's proportion constants from `k = 3` moments (open side question), not level-wise positivity.

### L6 — Definite-type persistence (Krein collisions). CIRCULAR
In the Pontryagin picture the first failure is a degeneracy: `μ₀(a*) = 0` with a null vector. It is not a collision of real eigenvalues of opposite type. "All real eigenvalues of positive type" at level `a` is `μ₀(a) > 0` itself.

### L7 — Critical-level rigidity. FAIL (no contradiction mechanism)
- At a first failure `a*`, the positive completion is unique: a discrete measure `μ* = Σ m_j δ_{t_j}` on the real zeros of `f̂*`, where `f̂*` is of type `2πa*` and so has bounded zero density.
- `μ*` can still reproduce the archimedean `log t` density, because the masses `m_j` grow, and the prime atoms on `(−2a*,2a*)`.
- Quasicrystal rigidity (Lev–Olevskii, Kurasov–Sarnak) needs a discrete Fourier side, but the archimedean part is continuous.
- So the configuration is consistent, as it must be under ¬RH.

### L8 — Burg (maximum-entropy) completion versus Selberg. FALSE; survivor recorded
- **Failure.** At `a < ½log 2` the Burg completion of the archimedean kernel has no prime atoms, while every Selberg completion keeps `Λ_w(p) = log p` at all primes.
- **Survivor [P].** The exact-primes gate selects prime-exact completions, not maximum-entropy ones. `Δ` itself is prime-exact at every level, so RH ⇔ a prime-exact positive-definite completion exists at every level.
- **Caveat.** The Selberg subfamily alone is too rigid: the archimedean part and the continuum are fixed beyond `2a`. Its feasibility (a pointwise positive symbol) is strictly stronger than `Pos(a)`, so its failure refutes nothing.

### L9 — Rank-trace sharpening by the (1,1) signature of off-line pairs. FALSE
Alpöge–Furman's final LP sees off-line pairs `p` and multiple on-line zeros `s₂` only through `s₂+p`. The worst case, `p = 0`, is untouched by any constraint on off-line pairs alone. Progress needs multiplicity-sensitive data: triple correlations or pair-correlation support beyond 1.

### L10 — Riemann–Siegel phase-counting completion. = L1 [paper]; the failure region is located
- **Construction.** `F_P(t) = 2Re(e^{iθ(t)}E_P(½+it))` with `E_P = Π_{p≤P}(1−p^{−s})^{−1}` and `P = e^{2a}`.
  - `E_P` is zero-free and `log E_P(½+it)` converges absolutely (`p^{−1/2} < 1`).
  - The phase is `φ = θ + arg E_P`, with `φ′ = θ′ − Σ_{p≤P,k} Λ(p^k)p^{−k/2}cos(tk log p)`.
  - Then `φ′/π` is an exact finite-cutoff Weil symbol at level `a`. The archimedean part is exactly `θ′/π`; prime powers `p^k > e^{2a}` lie outside the window; polar terms vanish on pole-vanishing inputs.
  - So `Q_a(h) = ∫|ĥ|² φ′/π` exactly.
- **Hoped-for gain.** The real-zero measure of `F_P` is positive and equals `(|φ′|/π)(1 + 2Σ_m (−1)^m cos 2mφ)` by Poisson summation. Where `φ′ > a` the aliased terms are non-stationary on the window.
- **Failure.** `φ′/π` is L1's semilocal symbol. Where `φ′ < 0`, counting yields density `|φ′|` and the window transform no longer matches `W`, so phase counting adds nothing beyond L1.
  - Negativity region: `θ′(t) ≤ a + Σ_{p≤e^{2a}} log p/(√p−1)`, i.e. `|t| ≲ exp(4e^a)`. This is the same `exp(4e^a)` the corpus records for the certificate support (`weil-positivity-past-sqrt-two-lean`).
- **Survivor [P], structural.** Level-`a` positivity is equivalent to a finite-height problem. Above `exp(O(e^a))` the semilocal symbol is pointwise positive; all negativity sits in a compact height range, where Krein freedom (Fourier support outside `(−2a,2a)`, i.e. mass moved at `t`-scale `≲ 1/a`) must repair the pole bumps.
  - The canonical repair is the level-`a` de Branges function `E_a`: its real phase-crossings form the positive Gauss quadrature, and the true zeros are that quadrature if RH holds. So HF's producer problem equals constructing `E_a` from arithmetic (route SZ, Suzuki 2606.09096).
  - Finite Euler products are never Hermite–Biehler: `|1 − r₁e^{−iφ}|` vs `|1 − r₂e^{−iφ}|` with `r₁ = p^{−σ} < r₂ = p^{σ−1}` flips order between `φ = 0` and `φ = π`.

### L11 — Height localization of level-`a` positivity. FALSE as stated
- Modulation `h ↦ e^{iTu}h` is unitary on `L²(−a,a)`, so "positivity of the level-`a` form at height `T`" (all `h`) is exactly `μ₀(a) ≥ 0`, independent of `T`.
- A genuine local version needs a frequency-localized subspace. Route 1's R1-L15 (sinh test family) is such a version; its threshold `e^a = log T` is where level `a` starts to see depth `< ½`.
- Consequence: an off-line zero `(δ, γ)` makes `μ₀(a) < 0` exactly for `a ≳ log(δ log γ)/(2δ)` (L4). Level-`a` positivity certifies only heights `γ ≲ exp(e^{2aδ}/δ)`.

### L12 — One-prime positivity at every level. FALSE [paper]
- Conjecture: the Weil distribution with only the prime 2 (all powers) is positive definite mod the polar plane at every level. This would be the first all-level positivity for a single prime.
- Failure: its full-line symbol is `Ω(t) − 2 log 2 Re(x/(1−x))`, `x = 2^{−1/2−it}`, with `Ω(t) = Re ψ(¼ + it/2) − log π`. At `t = 2π/log 2 ≈ 9.06`: `Ω ≈ 0.366` and the prime term `≈ −2 log 2 (√2+1) ≈ −3.35`, so the symbol is negative on an open interval.
  - PW_a functions concentrate there as `a → ∞`, so the one-prime `μ₀(a) → ess inf symbol < 0` (Szegő limit) and positivity fails at a finite level.
  - With the first atom only (valid for `a < ½ log 3`) the symbol at 9.06 is `0.366 − 0.980 = −0.61`. It can be lifted by the Krein-free atom `c cos(t log 4)` with `c ∈ [0.61, 0.68]` (checked at `t = 4.53, 9.06, 13.6`). That is the certificate route (numerics), not a structural one.
- Lesson: exact primes (MUST-357–363) forbid any finite-prime model at all levels. An all-level producer must involve every prime at once.

### L13 — Positive Bohr-torus completion with coupling between primes. FALSE [paper]; quantitative form of the L2/Helson gate
- **Conjecture.** L2's per-prime completions cost `≍ e^a`. Coupling primes through invisible composites should lower the cost.
  - Formulation: find a positive measure `μ` on the Bohr torus `T^{S_a}` (`S_a` = primes `≤ e^{2a}`) with `μ̂(n) = −Λ(n)/√n` for `1 < n ≤ e^{2a}` and `μ̂(n)` free for `n > e^{2a}`.
  - Then `W_ζ|window = (W_arch + polar − M δ₀) + (PD almost-periodic part)`, and level `a` needs only `μ₀^{arch}(a) ≥ M_min(a) := min μ̂(1)`.
- **Failure.** By duality, `M_min(a)` is the norm of the prime-shift quadratic form `Σ_{p,k} log p · p^{−k/2}(S_{p^k} + S_{p^k}^*)` on Dirichlet polynomials of length `e^a`.
  - On `ℓ²(ℕ) = ⊗_p ℓ²(p^ℕ)` this form is a sum of commuting single-prime blocks. Product (multiplicative) test vectors add the block maxima `2 log p/(√p−1)`, so `M_min(a) ≳ Σ_{p ≤ e^a} log p/√p ≍ e^{a/2}`.
  - The archimedean ground energy is `O(1)` and eventually negative. Torus completions fail at a finite level.
- **Insight.** On the torus the phases `p^{−it}` are independent (Kronecker), so no coupling between primes is possible there. The only coupling is the restriction to the one-parameter line `t ↦ (p^{−it})_p`. This is the quantitative form of the corpus's Mellin-diagonal/Helson gate: a producer must use the line, where aligning primes costs height, and height buys archimedean energy `log t`.

### L14 — Three-regime map of level-`a` positivity along the line. DIAGNOSIS [paper]; new named sub-problem SP-L
The semilocal symbol mod polar at height `t` is `Ω(t) − 2Re D_P(t) + (continuum)`, with `D_P(t) = Σ_{p≤P,k} Λ(p^k)p^{−k/2−ikt}` and `P = e^{2a}`.
- **High heights, `log t ≥ 4e^a`.** The trivial bound `|D_P| ≤ Σ log p/(√p−1) ≈ 2e^a` gives positivity. [Structural, unconditional]
- **Near `t = 0`.** After removing the pole, the symbol involves `∫_1^{P} u^{−1/2−it} d(ψ(u) − u)`. Unconditional PNT gives only `O(e^{a−c√a})` against the needed `O(a^2)`: this is the exponent gate (MUST-250). For each finite `a` it is a finite check on `ψ` below `e^{2a}` (numerical verification, e.g. `|ψ(x)−x| < √x` in the verified range).
- **Moderate heights, `C a ≲ log t ≲ 4e^a`.** Negativity requires simultaneous alignment of the phases `t log p` for many `p ≤ P`, i.e. a pointwise large value of a short prime Dirichlet polynomial.
  - Random-phase heuristic: typical size `≍ a`, extremes `≍ a√(log t)`, so the true negative region is heuristically `log t ≲ C a²`, not `4e^a`.
  - Moment and large-values methods give only measure bounds. The moment method beats the trivial bound nowhere (the admissible `k ≤ log t/(2a)` forces the threshold up to `(4/e)a e^{2a}`).
  - Vinogradov–Korobov needs `log P ≫ (log t)^{2/3}`, but here `log P = 2a ≪ (log t)^{2/3}`.
- **SP-L (short prime polynomial alignment bound), new named target.** For `P = e^{2a}` and `t ≤ exp(4e^a)`: `Re D_P(t) ≤ ½ log(t/2π) − c`.
  - It follows from RH: `log ζ(½ + 1/log P + it) ≪ log t/(e log log t)`.
  - It is strictly weaker than RH: a fixed `a` needs only finitely many primes and a bounded height range.
  - Together with the `t ≈ 0` finite check and the high-height trivial bound, SP-L would give level-`a` positivity by an explicit Krein completion.
  - It sits in the Lindelöf regime of short Dirichlet polynomials, where no pointwise cancellation is currently provable.
- **Consequence for the producer.** An all-level producer must (i) beat the exponent gate at `t≈0` for every `a`, which is RH-strength as `a → ∞`, and (ii) bound short-prime alignment in the regime `2a ≪ (log t)^{2/3}`. The corpus has named (i) (MUST-250). (ii) is newly isolated here and not yet attacked.

## Open core after L1–L9
A producer must create positive spectral mass exactly at the zeros, with no slack. Arithmetic completions give zero-indexed, sign-indefinite corrections: pole bumps (L1), separable local costs (L2), mollifier defect (L3).

Next conjectures to test:
- (a) The rank-trace (Alpöge–Furman) with higher Schatten moments. Does `‖G‖_{S_{2k}}` control `n₊(Q)` with slack `→ 0` as `k → ∞`? The operator-norm endpoint is `μ₀ ≥ 0`.
- (b) Whether the Burg (maximum-entropy) completion of the level-`a` Weil kernel has Selberg-type invisible weights. That would link the Krein extremal problem to Selberg's `Λ²` extremal problem.

## Log
- 2026-09-26 — finite-cutoff Selberg symbol representation formalized (`weilAtomSymbol`); the `N → ∞` continuation to `2θ' + 2Re(ζ'M_w)` remains [P].
- 2026-09-26 — L5–L8 run (moments, collisions, critical rigidity, Burg); none gives a producer.
- 2026-09-26 — L1–L4 run; Selberg completion core formalized (`RHTower.SelbergTruncatedVonMangoldtKreinCompletion`, wired, `lake build --old` green, lint pass).
