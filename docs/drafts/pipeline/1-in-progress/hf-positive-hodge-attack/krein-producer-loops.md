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
- 2026-09-27: L26 run. The negative-value ⇒ deep-zero direction is formalized (`RHTower.zeta_exists_deep_zero_of_negative_weil`). Both directions of the user duality are now quantified.
- 2026-09-27: L25 run. Quantitative Hodge-index exclusion of low off-line zeros formalized (`RHTower.exists_hodge_violation_low_height`), with non-vacuity and the corollary `zeta_re_eq_half_of_hodgeIndex`.
- 2026-09-27: L24 run. The L23 companion law is formalized for the polar-constrained Hodge index (`RHTower.zeta_hodge_index_forces_offLine_companion`).
- 2026-09-26: L23 run. The rigorous direction is formalized: an isolated deep zero violates level-`a` Weil positivity (`RHTower.zeta_weil_positive_forces_offLine_companion`), with threshold `δ ≈ log log|γ₀|/(2a)`.
- 2026-09-26: L22 run (user's shadow-pole ⇔ deep-zero duality). FALSE as an equivalence. Survivor formalized: `RHTower.offLineLattice_weil_positive_iff`, the level-`a` Weil form sees the depth of a vertical zero lattice iff `a > π/spacing`.
- 2026-09-26: L15–L21 run. L15 survivor formalized: `‖T_a‖ = (1+o(1))e^a` via a pole-profile Schur test (`RHTower.primeTransport_horizon_law`). SP-L's open core is now shadow-pole exclusion below `exp((1+o(1))e^a)` plus RH-local PNT on `[1,e^{2a}]`.
- 2026-09-26 — finite-cutoff Selberg symbol representation formalized (`weilAtomSymbol`); the `N → ∞` continuation to `2θ' + 2Re(ζ'M_w)` remains [P].
- 2026-09-26 — L5–L8 run (moments, collisions, critical rigidity, Burg); none gives a producer.
- 2026-09-26 — L1–L4 run; Selberg completion core formalized (`RHTower.SelbergTruncatedVonMangoldtKreinCompletion`, wired, `lake build --old` green, lint pass).

### L15 — Attack on SP-L: the two walls and the exact prime-transport horizon. BRIDGE; survivor formalized
- **Conjecture.** SP-L (L14) can be split into a height range decided by operator norms and a range that needs arithmetic. The norm-decided range starts at `log t ≈ ‖T_a‖`, where `T_a = Σ_{2≤n≤e^{2a}} Λ(n)n^{−½}(τ_{log n}+τ_{−log n})` is compressed to `L²(−a,a)`, and `‖T_a‖ = (1+o(1))e^a`, not the trivial `2Σ Λ(n)/√n ≈ 4e^a` (L14 used `4e^a`; the corpus proves `21(e^a+e^{a/2})`).
- **Mechanism [P].** The Perron weight is the pole profile `w = e^{y/2}+e^{−y/2}` (sum of the two rulings). The corpus's exact ruling action (`ccmFinitePrimeOperator_polarPlus_coeFn`) gives `(T_a w)(y) = e^{y/2}[ψ(e^{a−y})+S₁(e^{a+y})] + e^{−y/2}[ψ(e^{a+y})+S₁(e^{a−y})]`, `S₁(x)=Σ_{2≤n≤x}Λ(n)/n`. With `ψ(x) ≤ Rx + D` and `S₁(x) ≤ log x + c`, this is `≤ (Re^a + D + 2a + c)·w(y)` on `[−a,a]`. The weighted Schur test (nonnegative translation kernel) gives `‖T_a‖ ≤ Re^a + D + 2a + c`. With PNT, `limsup ‖T_a‖/e^a ≤ 1`. The Rayleigh quotient at `w`, with `ψ(x) ≥ (1−ε)x − K` and `S₁ ≥ 0`, gives `⟨T_a w,w⟩ ≥ ((1−ε)e^a − K)‖w‖²`, so `‖T_a‖/e^a → 1`.
- **Two walls of SP-L [P].** (i) Below polynomial heights: V₀ removes the pole directions, and what remains is the Chebyshev fluctuation `ψ(x) − x` on `[1,e^{2a}]`. This is the exponent gate (MUST-250). (ii) Between `exp(c a^{3/2})` (the Vinogradov–Korobov range) and `exp((1+o(1))e^a)`, negativity needs a shadow pole. That is a height `t` where the phases `n^{−it}`, `n ≤ e^{2a}`, align well enough to push the twisted Perron value near `‖T_a‖`. Excluding shadow poles there is a simultaneous-Diophantine statement about `(log p)_{p≤e^{2a}}` beyond Baker's theory and beyond all exponential-sum methods (Vinogradov saves only constants at `log t ≍ (log P)^{3/2}`).
- **Necessity [P].** Positivity at level `a` bounds the prime operator at height `t` against the archimedean term there. Testing on modulated Perron vectors `e^{itx}w` gives: if all `n^{−it}` (n ≤ e^{2a}) were ε-aligned at some `t` with `Ω(t) < (1−ε)‖T_a‖`, the Hodge index would fail. So the constant in the horizon is sharp for any argument blind to height (an operator bound independent of `t`).
- **Verdict.** BRIDGE. The sharp horizon is new (corpus: 21e^a; L14: 4e^a). The open core of the level-wise producer is now two exact statements: RH-local square-root PNT on `[1,e^{2a}]`, and shadow-pole exclusion below `exp((1+o(1))e^a)`.
- **Survivor [L] (2026-09-26).** Module `RHTower/PrimeTransportPoleSchurNorm.lean`. Axioms: propext, Classical.choice, Quot.sound. Built with `lake build --old`; wired after `SelbergTruncatedVonMangoldtKreinCompletion`.
  - `primePoleRow_eq`: the exact Schur row sum against the pole profile `w = e^{y/2}+e^{−y/2}` is `e^{y/2}[ψ(e^{a−y})+S₁(e^{a+y})] + e^{−y/2}[ψ(e^{a+y})+S₁(e^{a−y})]`.
  - `norm_ccmFinitePrimeOperator_le_chebyshevMertens`: `ψ ≤ RX+B√X+D` and `S₁ ≤ log X + c` give `‖T_a‖ ≤ Re^a+Be^{a/2}+D+2a+c`.
  - `norm_ccmFinitePrimeOperator_le_log4`: `‖T_a‖ ≤ log4·e^a + 4a e^{a/2} + 2a + log4 + 4` (elementary). The corpus had 21(e^a+e^{a/2}).
  - `primeTransport_horizon_law`: `(1−ε)e^a ≤ ‖T_a‖ ≤ (1+ε)e^a` for all large `a` (PNT). The pole vector is an asymptotic Perron vector.
  - `ccmRestrictedWeilSourceQuadratic_ge_of_primeBound` / `_ge_log4Horizon`: on pole-constrained vectors, `Q_a(u) ≥ ‖u‖²_arch − (‖T_a‖+|2γ₀−1|)‖f‖²`.
  - Reusable tools: `lintegral_translation_sum_le` (weighted Schur test for finite nonnegative translation families) and `le_norm_ccmFinitePrimeOperator_of_poleRow_ge` (pointwise Rayleigh lower bound).

### L16 — Lorentzian (Castelnuovo–Severi) form of the level-wise Hodge index. REDISCOVERED structure; one exact survivor
- **Conjecture.** The polar-free form `H_a = Arch − T_a` has exactly one negative direction at every level if and only if RH. Its negative direction is represented by a positive even function (the Perron–Frobenius ample class).
- **Proof sketch [P].**
  - The archimedean part is `C g(0) + ∫D(u)·2e^{−u/2}/(1−e^{−2u})du`, with `D(u) = ‖f − τ_uf‖²/2` (corpus `ArchimedeanWeilKernelSign`). The prime part is `−c_P‖f‖² + Σ Λ(n)n^{−½}‖f−τ_{log n}f‖²`. So `H_a = E_ν − c_a·I` with `E_ν` the Dirichlet form of a killed Lévy process on `[−a,a]`: archimedean Γ-jumps plus prime jumps `±log n` at rates `Λ(n)/√n`. Beurling–Deny gives `H_a(|f|) ≤ H_a(f)`, so the ground state is positive, simple and even at every level, unconditionally.
  - (⇒) RH gives `Q_zero ≥ 0` on all of `L²(−a,a)`, and `H = Q − polar` with polar `= 2|∫f cosh(x/2)|² − 2|∫f sinh(x/2)|²`. So `H ≥ 0` on the hyperplane `{∫f cosh(x/2)=0}`.
  - (⇐) That hyperplane contains V₀, where `H = Q`, so Bombieri–Yoshida applies (corpus Lean).
  - Clean form: RH ⇔ for all `a`, `H_a ≥ 0` on `{∫_{−a}^{a} f(x)cosh(x/2)dx = 0}`.
- **Attack.** This is the Hodge-index/Castelnuovo–Severi picture already in the corpus (HF-F9, HF-F11) with the ample class made explicit. Lorentzian tools (Brändén–Huh reverse Cauchy–Schwarz, killed-Lévy spectral-gap and Cheeger bounds) lose constants, and the margin under RH is `λ₂ − c_a ≈ μ₀(a) ≈ exp(−c a e^{2a})` (Zhu's Landau–Widom rate). So no slack is available to any gap inequality (gate "No slack").
- **Verdict.** REDISCOVERED as a criterion. The spectral-gap route is closed by the no-slack gate.
- **Survivor.** The Beurling–Deny positivity of the polar-free form is unconditional at every level, but its ground state is the pole direction. By Connes–van Suijlekom its Fourier transform has only real zeros, which carries no ζ information (zero spacing `π/a`).

### L17 — Tilted Hodge index at every level. TRUE [P], INSIGNIFICANT
- **Conjecture.** For every `a`, the damped kernel `e^{−(σ−½)|u|}W(u)` on `(−2a,2a)` has a positive-definite completion for `σ ≥ σ_blind(a)`, with `σ_blind(a) → 1` explicitly.
- **Proof [P].** On the zero side the damped kernel is `Σ_ρ e^{iγu}e^{−(σ−β)|u|}`. Pairing `ρ` with `1−ρ̄` gives the pair kernel `e^{iγu}(e^{(β−σ)|u|}+e^{−(β+σ−1)|u|})`. This is positive definite (a Poisson kernel) when `β ≤ σ`. For `β > σ` it is positive definite on `[−a,a]` once `a ≤ a₀(β−σ,β+σ−1)`. The worst case is `β→1`. Only `β<1` is used (the kernel is modulation invariant, so height and the zero-free region do not help), and this gives `σ_blind(a) = 1 − Θ(1/a)`.
- **Verdict.** TRUE but PNT-strength (`ζ(1+it) ≠ 0`). Any `σ_blind ≤ 1−η` uniform in `a` would be a zero-free strip.

### L18 — Family-averaged Hodge index over characters mod q. TRUE [P], INSIGNIFICANT
- **Conjecture.** Averaged over χ mod q, the level-a Weil forms are positive for `a ≤ log q + O(log log q)`.
- **Proof [P].** The conductor term `log(q/π)` dominates the averaged prime atoms at `n ≡ 1 (q)` (Brun–Titchmarsh). In fact positivity holds for every individual primitive χ when `log q > (1+o(1))e^a` (L15 horizon), since non-principal χ have no pole.
- **Kill.** The sinh test shows these levels cannot see even a Siegel zero. This is the family dilution of CANNOT-469.

### L19 — Finite-verification transfer (RH up to height H ⇒ Hodge index up to level A(H)). BRIDGE
- **Attack [P].** Split the zero side and the semilocal symbol with a partition in `t` whose pieces have compactly supported Fourier transforms. The gluing error comes only from invisible prime atoms, but it has to be compared with the non-coercive sampling energy of the verified zeros. That energy is `≈ μ₀(a)`, super-exponentially small. So the transfer needs quantitative zero data (a certificate), which is Zhu's doubly-exponential resolution barrier (arXiv 2608.24827).

### L20 — Visible-unit (S-smooth) Krein completions. FALSE for |S|=1 [P]; no content for |S| ≥ 2
- **Conjecture.** At level `a`, positive-definite completions can be found with lags in `log⟨S⟩` (S = the visible primes).
- **Kill for |S|=1 [P].** With only prime 2 visible, the invisible part is `2π/log 2`-periodic with mean zero. Positivity forces `∫_0^{2π/log 2} Ω ≥ 0` (up to the two polar degrees of freedom), and `∫_0^{2π/log 2}Ω < 0`.
- **For |S|≥2.** `log⟨S⟩` is dense, so the class is as flexible as all completions.
- **Lesson.** Only a one-prime window forces invisible primes; the exact-primes gate at a single level is otherwise vacuous.

### L21 — Convexity of the ground-energy curve. FALSE [P]
- **Conjecture.** `a ↦ μ₀(a)` is convex. This would imply RH, since under ¬RH `μ₀ ≤ −c e^{2Θa}/a³` (MUST-259), which is incompatible with convexity.
- **Kill.** Log-soft prime entry (WEIL-ENTRY-001) makes the right slope at each `a = ½log n` equal to `−∞` against a finite left slope. That is a concave corner, so μ₀ is not convex even under RH.
- **Survivor.** None beyond the corner law.

### L22 — Shadow-pole ⇔ deep-zero duality (user conjecture). FALSE as an equivalence; sharp Nyquist survivor [L]
- **Conjecture.** A shadow pole at height `t ≤ exp(e^a)` forces a zero near `t` with `β − ½ ≳ log log t/(2a)`. With L4, "Hodge index at level `a`" ⇔ "an `a`-dependent zero-free region up to height `exp(e^a)`".
- **Mechanism.**
  - Depth enters the level-`a` zero side only through an exponential tilt. An off-line pair contributes `ĥ(2K cosh(δu))(γ)`, which is the doubled on-line term plus `ĥ(4K sinh²(δu/2))(γ)`.
  - Poisson summation over ordinates with spacing `2π/L` turns the zero sum into the lags `mL` of `K = f ⋆ f̃`.
  - Nonzero lags fall inside `supp K ⊆ [−2a, 2a]` only when `L < 2a`.
- **Kill [L] (`RHTower.ZeroLatticeDepthNyquistLaw`).** Two abstract Zeta23 `ZeroConfig`s:
  - `onLineLatticeConfig`: `{½ + 2πik/L}`, multiplicity 2.
  - `offLineLatticeConfig`: `{½ ± δ + 2πik/L}`, `0 < δ ≤ ½`.

  Results:
  - `W_offLineLatticeConfig_eq_onLine`: for `f, g` supported in `[−L/2, L/2]`, both Weil forms equal `2L⟨f, g⟩` at every depth, including `δ = ½`.
  - `exists_re_W_offLineLatticeConfig_neg`: for every `a > L/2`, a two-bump test in `[−a, a]` gives `W = −2LB(e^{δL/2} − e^{−δL/2})² < 0`.
  - `offLineLattice_weil_positive_iff`: level-`a` Weil positivity holds ⇔ `a ≤ L/2 = π/spacing`.
  - `re_W_onLineLatticeConfig_nonneg`: the on-line lattice is positive at every level.
  - Also `hasSum_paperFT_lattice` (Poisson on `(2π/L)ℤ` in Zeta23's `paperFT` convention) and `paperFT_sub_I_mul` (vertical shift = exponential tilt).
- **Consequence.**
  - At height `t` the ordinate spacing is `2π/log(t/2π)`. So level `a` can resolve depth only while the spacing exceeds `π/a`, i.e. for `t ≲ 2πe^{2a}`: exactly the prime window.
  - On `e^{2a} ≲ t ≲ exp(e^a)` the zero side cannot see depth when zeros are locally lattice-arranged.
  - So no argument that uses only zero-configuration structure (strip, reflection symmetry, local finiteness, local density `≍ log t`) can give "Hodge(`a`) ⇒ zero-free region up to `exp(e^a)`".
  - The missing input is arithmetic: exclude local lattice arrangements of ordinates at scale `1/a`. This is a Diophantine statement about the `γ`, dual under the explicit formula to the shadow-pole Diophantine statement about the `log p`. The duality exchanges one wall for the other; it does not reduce either to a zero-free region.
- **What survives.**
  - (i) The rigorous direction holds under an isolation hypothesis: a deep pair with no zeros within ordinate radius `R ≍ e^{(1−2δ)a}` is visible [P].
  - (ii) `β − ½ ≳ log log t/(2a)` is meaningful only below Nyquist (`t ≲ e^{2a}`), where it is a sampling statement [P].
- **Link.** These lattices are exactly the zero sets of single Dirichlet columns `1 − A b^{−s}` (`singleColumn_zeroLine_and_verticalLattice`, with `L = log b`). The lags `mL` are the column's prime powers `b^m`, so depth becomes visible exactly when `b` enters the prime window `e^{2a}`.
- **Next.**
  - Local Nyquist law: a finite lattice segment embedded in an on-line background.
  - Isolated-pair detection with an explicit radius `R`.

### L23 — Rigorous direction of the duality: an isolated deep zero violates level-`a` Weil positivity. TRUE [L]
- **Conjecture (survivor (i) of L22).** A zero `ρ₀ = ½ + δ + iγ₀` whose other zeros within ordinate distance `R` are on the line forces level-`a` negativity once `e^{2δa} ≳ A₀ log|γ₀|·poly(a, 1/δ)`.
- **Proof mechanism.**
  - Test `e^{−iγ₀u}s(u)` with `s` real and odd. Oddness gives `ŝ(∓iδ) = ±P`, `P = ∫ s sinh(δu)`, so the deep pair contributes exactly `−2m₀P²`.
  - Each other zero is bounded by the decay `‖ŝ(x)‖ ≤ e^{|Im x|a}·4N/(1+|Re x|)²`. On-line near zeros carry no exponential factor; far zeros carry `e^a/(1+R)`.
  - Unit windows of the local count bound the rest by `384 A₀ log(|γ₀|+3) N² (1 + e^a/(1+R))`.
- **Lean (`RHTower.IsolatedDeepZeroWeilDetection`; wired; `lake build --old` green; axioms propext/choice/Quot.sound).**
  - `re_W_modulatedTest_le_of_isolated`: the isolation inequality for any real odd `C²` test. `N = ‖s‖₁ + ‖s''‖₁`.
  - `exists_re_W_neg_of_isolated_deep_zero`: for the explicit test `sinh(δu)(a²−u²)₊^{5/2}`, if `384A₀ log(|γ₀|+3) N_b²(1+e^a/(1+R)) < 2P_b²` then a `C²` test in `[−a,a]` has negative Weil form. Here `N_b = 2a cosh(δa)(a⁵+δ²a⁵+10δa⁴+20a³)` and `P_b = w(wa)^{5/2}sinh²(δ(a−2w))`, with `0 < w ≤ a/4`.
  - `exists_offLine_companion_of_weil_positive` (contrapositive) and `zeta_weil_positive_forces_offLine_companion` (for ζ, via Zeta23's unconditional local count): level-`a` Weil positivity forces every such deep zero to have another off-line zero within `R`.
  - Reusable tools:
    - `window_tsum_le`: `Σ_ρ m_ρ(1+|γ−γ₀|)^{−3} ≤ 24A₀ log(|γ₀|+3)`.
    - `norm_paperFT_le_decay`.
    - `hasSum_inv_one_add_abs_sq`: `Σ_ℤ (1+|n|)^{−2} = π²/3 − 1`.
    - `paperFT_modulate`.
    - `sinhTest` with its `C²`, derivative and energy bounds.
- **Size of the threshold [P].**
  - Take `w = 1/δ` (needs `δa ≥ 4`) and `R = e^a`. The condition reads `e^{2δa} ≥ C·A₀·log(|γ₀|+3)·a^7 δ^{−7}(1+δ²)²`.
  - That is `δ ≥ (log log |γ₀| + 7 log(a/δ) + O(1))/(2a)`: exactly the user's `β − ½ ≳ log log t/(2a)`, up to the `log(a/δ)` correction, with isolation radius `e^a`.
  - For smaller `R` the condition is `R ≳ e^{(1−2δ)a}·poly`.
- **Complete answer to the duality (L22 + L23).**
  - Level-`a` Weil positivity ⇒ every zero of depth above the threshold has an off-line companion within `R`.
  - The companion requirement cannot be dropped: the lattice of L22 is a configuration with no isolated zero, and it is Weil-positive at every depth.
  - So "Hodge(a) ⇔ zero-free region" fails exactly by coherent deep clusters.
- **Scope note.**
  - The hypothesis is zero-side positivity on all `C²` tests in `[−a,a]`. HF's Hodge index is positivity on `V₀ = {h_f(±i/2) = 0}`, which is codimension 2.
  - Upgrade route [P]: add `λ₁ψ + λ₂ sinhTest(a,½)` to kill the polar values. Then `|λ| ≲ e^{a/2}N/γ₀²`, so the correction is negligible for `|γ₀| ≥ e^{O(a)}`. This is the next step.

### L24 — Hodge-index (polar-constrained) version of L23. TRUE [L]
- **Statement.**
  - `HodgeIndexAtLevel Z a` means Weil positivity on `C²` tests in `[−a,a]` with `h_f(±i/2) = 0` (HF's `V₀`).
  - Under `HodgeIndexAtLevel`, every zero `ρ₀ = ½+δ+iγ₀` with `384A₀L₀N_b²(1+e^a/(1+R)) + 768e^aA₀L₀N_b²(ε+ε²) < 2P_b²` has another off-line zero within `R`.
  - Here `ε = polarCorrectionBound a γ₀ = O(e^{a/2}/(1+|γ₀|)²)`. So for `|γ₀| ≫ e^{3a/4}` the condition is that of L23.
- **Mechanism.**
  - Correct the deep-zero test by `c₁ψ + c₂ sinh(u/2)ψ`, `ψ = (a²−u²)₊^{5/2}`, with polar values `(α,α)` and `(−β,β)`.
  - `c₁ = −(H₊+H₋)/(2α)` and `c₂ = (H₊−H₋)/(2β)` kill `h_f(±i/2)`.
  - `|H_±| ≤ 4e^{a/2}N/(1+|γ₀|)²`. The expansion costs `≤ 768e^aA₀L₀(NG+G²)`.
- **Lean (`RHTower.IsolatedDeepZeroHodgeIndex`; wired; `lake build --old` green; axioms propext/choice/Quot.sound).**
  - `exists_hodge_violation_of_isolated_deep_zero`, `exists_offLine_companion_of_hodge_index`.
  - ζ instance: `zeta_hodge_index_forces_offLine_companion`.
  - Tools: `polarCorrectedTest`, `re_W_polarCorrected_le`, `polarCorrectedTest_polar_zero`, `paperFT_even_(neg_)I_mul`, `sinhTestWeight` bounds.
- **Status of the user's duality.**
  - Rigorous direction: Hodge(a) ⇒ each deep zero (`δ ≳ log log γ₀/(2a)`, `|γ₀| ≳ e^{3a/4}`) has an off-line companion within `R ≍ e^a`.
  - Counter-direction: coherent deep lattices are invisible above the Nyquist height `e^{2a}` (L22).
- **Next (L25 candidate).** Sub-Nyquist zero-free region: Hodge(a) ⇒ no zero with `δ ≥ δ*(a)` and `|γ| ≤ e^{ca}`.
  - Kill all zeros in a window by exact interpolation: evaluations of `h_f` at distinct points are independent.
  - The open core is the norm of the interpolant: a Landau-type sub-Nyquist bound.

### L25 — Quantitative Weil criterion at low height (in progress)
- **Conjecture.** For a configuration with local count `A₀`, Hodge(a) ⇒ no zero with `|γ| ≤ exp(c√(a/log a)/A₀)` and `β − ½ ≥ e^{−c√(a log a)}`.
  - Equivalently: an off-line zero at height `T` and depth `δ` violates Hodge(a) once `a ≳ A₀²(log T)² log log T + log(1/δ)·log T`.
  - Configuration-level ceiling (L22): no argument using only zero structure passes height `e^{2a}`.
- **Literature.**
  - Li-coefficient analogues exist: Bombieri–Lagarias, and Freitas's τ-Li criteria, give zero-free regions from `λ_n ≥ 0, n ≤ N`.
  - No quantitative support-`a` Weil version was found. Zhu (arXiv 2608.24827) says restricted positivity alone does not exclude zeros, at the level of one-stroke certificates.
- **Proof plan [P].**
  - **Tests.** `F(x) = x(x−c)(x−c̄)((x+γ₀)²+¼)·Π_{ρ∈killed}(x−x_ρ)·ŵ(x)^K`, `x_ρ = γ_ρ−γ₀`, `w = (b²−u²)₊^{5/2}`, `b = a/K`. Realised as iterated `EF.weilTest` convolutions of `w` and `(I∂ − r̄)w`. Only the first factor needs to be `C²`; the support is `[−a,a]`.
  - **Real structure.** The roots are closed under conjugation and `ŵ` is real-structured, so `Wsummand(ρ) = m F(x_ρ)²`. On-line zeros give `≥ 0`, killed zeros give `0`.
  - **Cluster.** Zeros with `x_ρ` within `ε` of `±iδ`. Pigeonhole over `n+1` annuli of ratio `λ = 100n` gives an empty annulus `[ε, λε)`. Cluster members satisfy `F(x_ρ)² = F(x₀)²(1+O(0.1))`, since the product ratios and `ŵ` are Lipschitz at scale `ε ≤ min(δ,1/a)/100`.
  - **Phase.** Choose `c` with `arg F(x₀) = −π/2`, so `Re F(x₀)² = −|F(x₀)|²`.
  - **Tail.** `|Re x| > H`. `|ŵ(x)|/ŵ(0) ≲ C/(1+|x|)²` per factor, so the tail is `≤ e^a (C/H²)^K (|x|+H)^{2n}·…`. With `K = a/2` and `H ≈ 50` the tail is `e^{−ca}`.
  - **Balance.** `|P(x₀)| ≥ (ε₀λ^{−n})^n`. The condition is `0.1a ≳ 2n² log(100n) + 2n log(100/δ) + O(n log a)`, with `n ≈ 2HA₀ log T`.
- **Formalization modules planned.**
  1. Root-convolution tests with transform `Π(z−r_j)ŵ(z)^K`.
  2. Real-structure summand.
  3. Ratio and Lipschitz bounds for `ŵ`.
  4. Annulus pigeonhole.
  5. Polynomial product ratios.
  6. Tail window sums.
  7. Assembly.
  8. The ζ instance.

### L25 result — Quantitative Hodge-index exclusion of low off-line zeros. TRUE [L]
- **Lean.** Two modules, both wired; `lake build --old` green; axioms propext/choice/Quot.sound.
  - `RHTower.LowHeightWeilTests` (toolkit).
  - `RHTower.LowHeightHodgeExclusion`.
- **Main theorem: `exists_hodge_violation_low_height`.**
  - Setting: a configuration with local count `A₀`, a zero `ρ₀ = ½+δ+iγ₀` with `δ > 0` and `|γ₀| ≥ 1`, and at most `n` zeros with `γ₀−H < γ ≤ γ₀+H`. Let `2n+7 ≤ N₀ ≤ a`.
  - Condition: `C_tail·24A₀ log(|γ₀|+3) < (79/50)(1+H)^{4N₀−4n−11}·lowHeightFloor δ N₀ n`.
  - Constants:
    - `C_tail = (e^{1/2}·168)^{2N₀}(H+|γ₀|+1)^{4n+8}`;
    - `lowHeightFloor = ((3/4)^{5/2})^{2N₀}(ε₀/λ^n)^{4n}δ⁴`, with `λ = 100(n+1)` and `ε₀ = min(δ,1)/(100(3N₀+3))`.
  - Conclusion: a `C²` test in `[−a,a]` with `h_f(±i/2) = 0` has `Re W < 0`, so the level-`a` Hodge index fails.
- **Corollaries.**
  - `not_hodge_index_of_low_offLine_zero` and, for ζ, `zeta_hodge_index_excludes_low_offLine_zeros`.
  - `eventually_lowHeight_condition` (non-vacuity): for fixed data the condition holds at every large `N₀`, since `(101²(3/4)^{5/2}/(168e^{1/2}))^{2N₀}` beats `N₀^{4n}`.
  - `eventually_not_hodgeIndex`: every off-line zero with `|γ| ≥ 1` violates Hodge(a) at all large `a`.
  - `zeta_re_eq_half_of_hodgeIndex`: Hodge(a) for all `a` ⇒ every ζ-zero with `|γ| ≥ 1` has `β = ½`.
- **Mechanism.**
  - The test is `e^{−iγ₀u}·(w^{⋆k} ⋆ ⋆_r (I∂−r̄)w)`, `w = (1−u²)₊^{5/2}`. Its transform is `F(z−γ₀)`, `F = ŵ^{N₀}·Π_L(x−r)(x−r̄)`, and `Wsummand = m F(x_ρ)²`.
  - `L` contains the killed window zeros, the polar root `−γ₀+i/2`, and a real phase root `c ∈ [−δ,δ]` chosen by the IVT so that `F(−iδ) ∈ iℝ`.
  - Pigeonhole over `n+1` scales gives a cluster radius `ε` with a gap `[ε, λε)`. Product perturbation keeps `Re F² ≤ −0.79|F₀|²` on the cluster.
  - The tail decays like `ŵ^{2N₀}`, `(e^{1/2}·168/(1+H)²)^{2N₀}`, against the unit-window count.
- **Height horizon [P].** For ζ, `n ≍ 2HA₀ log|γ₀|`. The condition reads `a ≳ n² log n + n log(a|γ₀|/δ)`. So Hodge(a) excludes zeros with `|γ| ≤ exp(c√(a/log a))` and `β−½ ≥ exp(−c√(a log a))`.
  - Configuration-level ceiling (L22): `e^{2a}`. The gap is between `exp(c√a)` and `e^{2a}`.
- **Literature status.**
  - The analogue for Li coefficients (Bombieri–Lagarias, Freitas) is known.
  - No explicit support-`a` Weil-positivity ⇒ zero-free-region statement was found. Zhu (2608.24827) states that restricted positivity alone does not exclude zeros, for one-stroke certificates.
- **Open core (next).**
  - Raise the horizon from `exp(c√a)` towards `e^{ca}`. This needs a sub-Nyquist interpolation-norm bound that replaces the pigeonhole `λ^{n²}` loss with `e^{O(n)}`.
  - Or prove that `exp(c√a)` is sharp for configurations with local count `A₀`.

### L26 — Shadow pole ⇒ deep zero (the other direction of the duality). TRUE [L]
- **Lean (`RHTower.NegativeWeilValueForcesDeepZero`; wired; build green; axioms propext/choice/Quot.sound).**
  - `exists_deep_zero_of_negative_weil`, and the ζ instance `zeta_exists_deep_zero_of_negative_weil`.
  - Statement: if `Re W(e^{−itu}s) ≤ −μ < 0`, then either `μ ≤ 768A₀ log(|t|+3)N²e^a/(1+R)`, or some zero with `|γ−t| ≤ R` has `μ ≤ 768A₀ log(|t|+3)N²(e^{2|β−½|a} + e^a/(1+R))`.
- **Depth form.** A negative value `μ ≫ N² log t` at height `t` forces a zero within `R` of depth `β−½ ≥ log(μ/(768A₀N² log t))/(2a)`.
  - Your scaling `β−½ ≳ log log t/(2a)` corresponds to negativity `μ ≍ N²(log t)²`.
- **Duality verdict (L22–L26), quantitative.**
  - Shadow pole ⇒ deep zero: unconditional, with the explicit rate above (L26).
  - Deep zero ⇒ shadow pole, under isolation within `R ≍ e^{(1−2δ)a}·poly`: L23 (all tests) and L24 (the Hodge index `V₀`).
  - Deep zero ⇒ shadow pole, without isolation: at low heights, `|γ| ≤ exp(c√(a/log a))` [P horizon] (L25, Lean-explicit condition).
  - It fails without isolation above the Nyquist height `e^{2a}`: deep lattices are invisible (L22).
  - So "Hodge(a) ⇔ zero-free region up to `exp(e^a)`" is false as stated. The correct equivalence holds up to heights `exp(c√a)` unconditionally, and up to `e^{2a}` at best for any argument that uses only zero-side structure.

### L27 — Is `exp(c√a)` sharp with only a local count? NO. The level is linear in the window count, up to `log² a` [L]
- **Question (user).** Either build a masking configuration from geometric clusters of deep zeros, or find a cluster-robust construction that reaches `e^{ca}`.
- **Diagnosis.** The L25 horizon has two independent `√a` losses.
  1. The pigeonhole over `n+1` scales pins the centre at `ρ₀` and pays `λ^{−n}` in the killing distance, so `λ^{−4n²}` in the floor.
  2. The tail constant bounds all `2n+4` roots by `|γ₀|`, giving `|γ₀|^{4n}`. Only the polar root is at distance `|γ₀|`.
  - Tight clusters are harmless: a zero within the cluster radius of the centre is not killed, and it contributes negatively.
- **Construction (cluster-robust).**
  - **Halving selection** (`exists_empty_annulus_center`). If the ball `B(p,r)` has an occupied annulus `[r/2λ, r/2)` at some `q`, then `B(p,d/2)` and `B(q,d/2)` are disjoint and lie inside `B(p,r)`, so one of them holds at most half the points. After `⌊log₂ n⌋+1` halvings some zero `ρ₁` near `ρ₀` has an empty annulus at scale `t ≥ ε₀(4λ)^{−(⌊log₂ n⌋+1)}`.
  - **Re-centring** (`cluster_selection`). The test is modulated at `γ₁ = Im ρ₁`, with depth `δ₁ ≥ δ/2`. The pool is the window of half-width `H+1`, which contains the `γ₁`-window of half-width `H`.
  - **Reflection closure.** The kill/cluster split uses `x_{1−ρ̄} = conj x_ρ`, so both centres `±iδ₁` are handled by one annulus.
  - **Split tail** (`norm_sq_lowHeightProfile_tail_split`). The constant is `(e^{1/2}168)^{2N₀}(H+1)^{4n+4}(|γ|+1)⁴`.
- **Lean (`RHTower.ClusterRobustHodgeExclusion`; wired after `NegativeWeilValueForcesDeepZero`; `lake build --old` green; axioms propext/choice/Quot.sound).**
  - `exists_hodge_violation_cluster_robust`: the explicit criterion.
  - `not_hodgeIndex_below_cluster_horizon`: any configuration with local count `A₀`, any zero with `|β−½| ≥ δ` and `|γ| ≥ 2`, and `n = N_d(γ−101, γ+101)`. If `a ≥ max(e⁶, 1/δ)` and `100((n+1)log²a + log(A₀(|γ|+4))) ≤ a`, then Hodge(a) fails.
  - `zeta_hodge_index_cluster_horizon`: for ζ, `10⁵A₀ log(|γ|+306) log²a ≤ a` suffices, so the horizon is **`exp(a/(10⁵A₀ log²a))`**, up from `exp(c√(a/log a))`.
  - `offLineLattice_masks_at_linear_level`: the lattice `{½±δ+2πik/L}` has local count `(L/π+2)log(|t|+3)`, window count `≤ 1000L`, depth-`δ` zeros above every height, and it satisfies Hodge(a) for all `a ≤ L/2`.
  - `not_forall_hodge_exclusion_sublinear_level`: no criterion "window count `≤ 2000a` ⇒ violation" holds.
  - The L25 module was refactored: the tail constant is abstract (`re_W_lowHeightTest_le` takes a tail hypothesis), plus `lowHeight_tail_bound` and `norm_sq_lowHeightProfile_x₀_ge`.
- **Verdict.**
  - `exp(c√a)` is an artefact of the pigeonhole and of the uniform root bound. It is not sharp.
  - Geometric clusters cannot mask. Any configuration with window count `n ≪ a/log²a` and `log(A₀|γ|) ≪ a` loses the Hodge index at a deep zero, whatever the cluster geometry.
  - The threshold level for exclusion at window count `n` satisfies `n/2000 ≤ a*(n) ≤ C n log²a` (`a*` is the least level from which exclusion is forced). So the Hodge index resolves deep zeros exactly at sub-Nyquist window density, up to `log²a`.
- **Remaining gap.** The factor `log²a`.
  - One `log a` comes from the Lipschitz resolution `ε ≲ 1/N₀` of `ŵ^{N₀}`: killing roots within `1/a` costs `log a` each.
  - The other comes from `⌊log₂ n⌋ · log λ`.
  - A parallel route in the repo (`SubNyquistInterpolationTest`, `PolynomialWeilTests`, `HTGeometry.LagrangeRectangleContour`; unwired) prescribes `±i` at all cluster nodes by Lagrange interpolation, with a contour bound independent of node clustering. If completed, it removes the `λ`-loss and aims at `e^{ca}`.

### L28 — Remove the `log² a`: Lagrange interpolation at all deep nodes plus a forward-difference contour. TRUE [L]
- **Conjecture.** The Hodge(a) exclusion level is linear in the window count, with no power of `log a`: `a*(n) ≤ C·(n + 1)·log(C/δ) + C·log(A₀|γ₀|)`.
- **Kill attempts.**
  - *Circular?* No. The test is explicit, and the only analytic input is the unconditional local count.
  - *Parent theory?* The corpus parent is L27 (`n·log² a`); the literature has no exclusion-horizon theorem for compact-window Weil positivity. We checked arXiv 2608.24827 (certified two-sided λ_min bounds, no exclusion statement), arXiv 2609.20367, Connes–Consani 2006.13771, and Bombieri's semi-local functional.
  - *False?* No. Two lower bounds were proved separately and are consistent with the claim: the lattice lower bound `a* ≥ n/2000` (L27), and a constant-base product bound by forward differences.
- **Verdict: SURVIVES; PROVED.** The level-`a` Hodge index fails as soon as `4((n + 1)·log(10⁶/δ) + log(A₀(|γ₀| + 3))) ≤ a`, for `|γ₀| ≥ 102` and `n` the window count in `(γ₀ − 100, γ₀ + 100]`.
  - For `ζ`: Hodge(a) excludes depth-`δ` zeros up to height `exp(a/(2000·A₀·log(10⁶/δ))) − 3`.
  - With L27: `n/2000 ≤ a*(n) ≤ 4(n + 1)·log(10⁶/δ) + 4·log(A₀(|γ₀| + 3))`. The threshold is `Θ(n)` for fixed depth, which is the Nyquist scale.
- **Mechanism.**
  1. *Nodes and killed values.* The nodes are the window values in `[−X, X] × ±(y₀, 1)`. The test profile is `Ŵ^N·P·p`, where `p` interpolates `±i/(P·Ŵ^N)` at the nodes. Every node contributes exactly `−m_ρ/lc(Q)²` to the Weil form. The killed values, and the polar point, contribute `0`. The deep zero is an ordinary node, so no cluster estimate and no phase root are needed.
  2. *Tail.* Outside the window the barycentric formula, split over the two rectangles, becomes a contour integral of the holomorphic data against `1/((x − t)·ω(t))`. Only `|P·ω|` on the rectangle sides enters.
  3. *Choice of sides.* The sides `X ∈ [½, ¾]` and `y₀ ∈ [δ/4, δ/2]` are grid points where `Π|X − |Re v||` and `Π|y₀ − |Im v||` are at least `(1/8e)^{|V|}` and `(δ/8e)^{|V|}`. This comes from the `m`-th forward difference of a monic polynomial, which equals `m!`. Each window value is a root of `P·ω` with multiplicity at most two. The loss is `(16e·101/δ)^{4n}` — a constant raised to the power `n`, where L25's pigeonhole lost `λ^{n²}` and L27's halving lost `(4λ)^{n·log n}`.
- **Lean (all built, wired, standard axioms, lint clean).**
  - `HTGeometry/ForwardDifferenceProductSelection`: `exists_le_abs_eval_nat_of_monic`, `exists_mem_Icc_prod_abs_sub_ge`.
  - `HTGeometry/LagrangeRectangleContour`: `sum_nodalWeight_inside_eq_rectangleIntegral`, `norm_rectangleIntegral_le`.
  - `RHTower/PolynomialWeilTests`: `polyTest_props`, `Wsummand_polyTest`, `polyTest_polar_zero`.
  - `RHTower/SubNyquistInterpolationTest`: `re_unitHat_ge`, `interpProfile_node`, `interpQ_real`, `norm_rect_part_le`, `norm_interpProfile_le`.
  - `RHTower/SubNyquistHodgeExclusion`: `subNyquist_selection`, `border_lower_bound`, `sq_prod_le_killPoly_nodal`, `norm_sq_interpProfile_far`, `re_W_neg_of_window_profile`, `exists_hodge_violation_subNyquist`, `nyquist_horizon_condition`, `not_hodgeIndex_below_nyquist_horizon`, `zeta_hodge_index_nyquist_horizon`.
- **Remaining gap.** The factor `log(10⁶/δ)`.
  - It comes from the side `y₀ ~ δ`: the product selection in the depth direction costs `log(1/δ)` per window value.
  - Open: is `a*(n) ≍ n` uniformly in `δ`, or does a lattice with shallow companions force `a* ≳ n·log(1/δ)`?
  - This is the last parameter of the HF horizon question at fixed window count. What the local count gives for `ζ` is now `log T ≍ a/A₀` up to `log(1/δ)`.

### L29 — Localized finite-level resolution law: masking needs density or off-line crowding (in progress)
- **Conjecture.** Let `ρ₀` have depth `δ` at height `γ₀`, and let `k` be the number of zeros of depth `≥ δ/8` with `|γ − γ₀| ≤ 100`. Then Hodge(a) fails once `a ≥ (C/δ)·[log(A₀ log|γ₀|) + k·log(C/δ)]`.
  - For `ζ`: every zero of depth `δ` has at least `c·(δa − C log(A₀ log T))/log(C/δ)` zeros of depth `≥ δ/8` within distance 100.
- **Masking dichotomy.** A deep zero survives level `a` only by on-line density (`δa ≲ log log T`) or by off-line crowding (`k ≳ δa/log(1/δ)`).
  - Both mechanisms occur. An on-line lattice of spacing `2π/L` plus one pair satisfies Weil positivity for `a ≤ (1/2δ)·log(δL/2)`, by Poisson: `W ≥ L‖f‖² − 2|F(x₀)|²` and `|F(x₀)|² ≤ ‖f‖²·sinh(2aδ)/δ`. The off-line lattice masks at `a ≤ L/2` (L27).
- **Kill attempts.** Both lattices are consistent with the bound, and the conjecture is not circular. It improves L24 in two ways: the companion radius drops from `e^a` to `100`, and one companion becomes a count. It closes L4's open core. Verdict: SURVIVES.
- **Paper proof.**
  - *Weight.* `Ψ(x) = cos(a′x)·Ŵ(x)^N`. The test is the cosine translate of the polynomial test, support `a′ + N ≤ a`, transform `cos(a′(z−γ₀))·Ŵ^N·Q/lc`.
  - *Classification.* Let `D′` be the window values of depth `≥ δ/8` (count `k`). Choose `X ∈ [X₀/2, X₀]` (`X₀ = √δ/8`) and `y₀ ∈ [δ/4, δ/2]` by forward differences over `D′`.
    - Nodes: `D′ ∩ {|Re| < X, |Im| > y₀}`.
    - Killed: the rest of `D′`, plus the polar point.
    - Unkilled: window values of depth `< δ/8 ≤ y₀/2`.
  - *Contour lower bounds.*
    - `|cos(a′t)| ≥ sinh(a′|Im t|)`.
    - `Re Ŵ(t) ≥ cos X·∫w` for `|Re t| ≤ X`.
    - `|P ω| ≥ (δ/16e)^{2k}` on the sides.
    - The polar factor enters only as a ratio, at most `4(1+u)²`.
  - *Unkilled window zeros.* Distance to the border is `≥ δ/8`, so `|Φ| ≤ C₃·e^{−a′δ/8}·e^{NX²}`, with `C₃ = 64(2H+2)^{2k}(16e/δ)^{2k}(8/δ)`.
  - *Far zeros.* `|Φ|²(1+u)^{3+E} ≤ C₂·e^{a′}·K₁′^{2N}` with `K₁′ ≤ 664`. They are summed by `window_tsum_le`.
  - *Nodes.* Each node gives `−m/lc²`.
  - *Parameters.* `a′ ≈ (8/δ)[log(2n) + 2 log C₃]` and `N ≈ a′/5 + O(k log(C/δ) + log log|γ₀|)`.
- **Result (L29): TRUE [L].**
  - **Theorem** (`RHTower/FiniteLevelResolutionLaw:resolution_law_of_hodgeIndex`). If Hodge(a) holds and `ρ₀` has depth `δ` and `|γ₀| ≥ 103`, then `δa < 12((4n_δ + 2)·log(10⁶/δ) + log(A₀ log(|γ₀| + 3)) + 18)`. Here `n_δ` counts the zeros of depth `≥ δ/8` with ordinate in `(γ₀ − 100, γ₀ + 100]`.
  - For `ζ`: `zeta_resolution_law_of_hodgeIndex`. Axioms: propext, Classical.choice, Quot.sound.
  - **Modules.**
    - `RHTower/CosineTranslatedWeilTests`: cosine translate; transform `cos(c(z−γ₀))·ĝ`; Weil summand; polar zeros.
    - `RHTower/WeightedInterpolationContour`: interpolation with a general entire weight; contour bound at any distance `d`.
    - `RHTower/FiniteLevelResolutionLaw`:
      - cosine bounds `sinh|Im| ≤ |cos| ≤ cosh Im`;
      - `Re Ŵ ≥ cos θ·Ŵ(0)`;
      - summation lemma with a positive window part;
      - window-zero and far-zero bounds;
      - explicit size condition (`c = 3a/4`, `N = ⌊a/4⌋`).
  - **Status of the two regimes.**
    - Density masking: a lattice of spacing `2π/L` plus one pair satisfies Weil positivity for `a ≤ log(1 + δL)/(2δ)`. This is [P]; the union configuration is not yet built in Lean.
    - Off-line crowding: the off-line lattice masks at `a ≤ L/2` [L] (L27).
  - **Remaining gaps.** In the crowding regime the bound is `n_δ ≳ δa/log(1/δ)`, while the lattice only needs `≍ a`. Open: can crowding by comparably deep zeros mask at `n_δ ≪ a`, or does the factor `δ` come from the weight `cos(c x)`, which gains only at depth?
- **Density regime, Lean [L]** (`RHTower/LatticeMasksDeepPair:lattice_masks_isolated_deep_pair`). The doubled critical lattice of spacing `2π/L` plus one pair `½ ± δ + iγ*` satisfies:
  - local count `≤ (L/π + 6) log(|t| + 3)`;
  - its only zeros off the critical line are the pair;
  - the level-`a` Hodge index holds whenever `a ≤ L/2` and `2a e^{2aδ} ≤ L`.

  The density term `log A₀` of the resolution law is therefore necessary, up to its constant. Both masking regimes are now Lean-closed.

### L28 — Is HF-Krein at level `a` stronger than the known zero-free regions? YES: it is a critical strip of width `1/a` [L]
- **Question (user).** Can a finite-cutoff Selberg symbol inequality from HF-F16 hold at level `a` without implying a zero-free region beyond the de la Vallée-Poussin / Korobov–Vinogradov type?
- **Bridge.** In the Zeta23 normalization, via the proven explicit formula for ζ (`WeilEF.EF_lit_zetaZeroConfig`, `gammaFacts`).
  - `zeta_W_eq_integral_selbergSymbol`: for polar-constrained `C²` tests supported in `[−a,a]`, `W(f,f) = (1/2π)∫|h_f(τ)|² weilAtomSymbol(Λ_w,N)(τ/2π) dτ`. This holds for every weight `w = 1` on `[1,⌊e^{2a}⌋]` and every cutoff `N ≥ ⌊e^{2a}⌋`.
  - `weilAtomSymbol_vonMangoldt_eq`: `weilAtomSymbol(Λ,⌊X⌋)(τ/2π) = 2π(μ(τ)+P_X(τ))`, the Zeta23 density.
  - `integral_normSq_paperFT_mul_cos_eq_zero`: atoms at `n > e^{2a}` are invisible.
  - `integral_weilAtomSymbol_completion`: completion invariance.
- **Equivalence.** `hodgeIndexAtLevel_iff_selbergSymbolPositive`: every admissible Selberg symbol inequality at level `a` is exactly `HodgeIndexAtLevel zetaZeroConfig a`.
- **Strip.**
  - `zeta_selbergSymbol_forces_critical_strip`, and `…_nonneg_…` for a pointwise positive Krein symbol. At level `a ≥ e⁶`, every zero with `|γ| ≥ 2` and `10⁵A₀log(|γ|+306)log²a ≤ a` has `|β−½| < 1/a`.
  - Height form (`zeta_selbergSymbol_forces_strip_up_to_height`): one level `a ≍ A₀ log T (log log T)²` confines all zeros up to height `T` to `|β−½| < 1/a`.
  - Consistency: RH ⇒ the inequality at every level (`selbergSymbolPositiveAtLevel_of_forall_re_eq_half`), and the inequality at all large levels ⇒ `β = ½` for `|γ| ≥ 2` (`zeta_re_eq_half_of_selbergSymbol_eventually`).
- **Lean.** `RHTower.SelbergSymbolCriticalStrip`; wired after `ClusterRobustHodgeExclusion`; `lake build --old` green; axioms propext/choice/Quot.sound.
- **Verdict.**
  - No. Every finite-cutoff Selberg symbol inequality at a level `a ≥ e⁶` implies a quasi-RH strip `|β−½| < 1/a` up to height `exp(a/(10⁵A₀log²a))`.
  - dlVP and VK only confine `1−β` (`≫ 1/log T`, `≫ (log T)^{−2/3}(log log T)^{−1/3}`). No unconditional result bounds `β−½` by any constant `< ½` beyond the numerically verified height.
  - So HF-Krein at a level `a` with `exp(a/(10⁵A₀log²a))` above the verified height is strictly stronger than every known zero-free region.
  - The Selberg completion freedom cannot weaken this: the level-`a` form is completion-invariant.
- **Positive survivor / next.** The relaxed dictionary.
  - Unconditionally, HF-F17 gives `Q_a ≥ −(1+o(1))e^a‖f‖²`, i.e. error exponent `θ = 1`, which is the trivial region `β < 1`.
  - Conjecture [P]: `Q_a ≥ −e^{θa}‖f‖²` on polar-constrained tests, with `θ < 1`, forces `β ≤ (1+θ)/2 + ε` up to height `exp(cε a/(A₀log²a))`.
  - Paper mechanism: an edge-concentrated sinh weight, which gains `e^{2δa}`, times the cluster-robust root-killing polynomial, which costs `e^{O(n log²a)}`.
  - If true, the exponent of the prime-side error at level `a` is exactly twice the abscissa excess of the zeros. Any `θ < 1` would be a quasi-RH.

### L30 — Goal cycle "find the producer": the radical of the Weil form, the CCM producer, and the margin law (in progress)
- **Literature checked (2026-09-27).**
  - Connes–Consani–Moscovici, *Zeta spectral triples* (arXiv 2511.22755). Every finite-stage ground-state transform has only real zeros (Carathéodory–Fejér, rank-one perturbation). Two steps are listed as missing:
    - (S1) the ground state of `QW_λ` is simple and even;
    - (S2) the prolate/theta guess `k_λ = E(h_λ)` approximates the ground state well enough for the zeros to converge.
  - Connes, arXiv 2602.04022 (survey): the same strategy.
  - Zhu, arXiv 2608.24827:
    - `λ_min(L) ≤ exp(−L e^L)` is proved only under RH;
    - the unconditional upper bounds are interval-arithmetic values at fixed `L`;
    - the Landau–Widom law is empirical.
  - Connes–Consani, *Spectral triples and ζ-cycles* (arXiv 2106.01715): the radical of `QW` contains the range of `E`, and small eigenvalues are explained by "prolate vectors"; the support is numerical only.
- **Conjecture (radical producer).** Positivity at level `L` is produced by the radical. `QW_L` should dominate an explicit nonnegative leakage functional of a radical representative, and this domination would supply CCM's gap in (S2).
- **Kill: CIRCULAR.**
  - Under ¬RH, `QW_L` takes values `≤ −c e^{2Lδ}/L³` (MUST-259), while any leakage functional is `≥ 0`. So the conjecture is RH at level `L` with a constant.
  - Structurally, the radical is the kernel of the form. It can only produce near-null vectors (upper bounds on the margin), never lower bounds.
  - (S2) needs `|ε_λ| ≪ gap`, a lower bound on `ε_λ`, which is Weil positivity itself. CCM's strategy is therefore a receiver whose producer step is positivity.
- **Survivor (positive statement): the no-slack margin law.**
  - Riemann's kernel `Φ = T'' − T/4`, with `T(x) = e^{x/2}(θ(ie^{2x}) − 1)/2`, lies in the radical of the Weil form: `∫Φ(x)e^{(s−½)x}dx = ½s(s−1)Λ(s)` vanishes at every nontrivial zero, on or off the line.
  - Truncating `Φ` and convolving with `κ₂ = κ'' − κ/4` (whose transform vanishes at `±i/2`) gives Hodge-class tests on `[−L, L]` with `|W(f,f)| ≤ C e^{CL} exp(−π e^{2L−1/2}) ‖f‖²`.
  - Hence, unconditionally, the level-`L` Hodge/Weil ground energy is at most `exp(−π e^{2L−1/2} + O(L))`.
  - Any producer of level-`L` positivity must therefore deliver a margin below this. The mechanism behind the super-exponential smallness is the radical, unconditionally.
- **L30 result [L].** Two modules, both wired after `LatticeMasksDeepPair`; built; axioms propext/choice/Quot.sound; lint clean.
  - `RHTower/RiemannKernelWeilRadical`:
    - `riemannPhiTransform_eq`: `∫Φ e^{(s−½)x} = s(s−1)Λ(s)/2` on `ℂ∖{0,1}`, by two integrations by parts with a nonzero cusp value, the Mellin transform of `θ(iy) − 1`, and analytic continuation;
    - `riemannPhiTransform_eq_zero_of_nontrivial`;
    - `riemannPhiTransform_two_ne_zero`;
    - `paperFT_riemannPhiKernel`.
  - `RHTower/WeilMarginSuperexponentialLaw`:
    - `weilRadicalTest L = Φ_{≤L−1/4} ⋆ (κ''−κ/4)`, which is `C²`, supported in `[−L,L]`, and polar-free;
    - `norm_W_weilRadicalTest_le` (the tail factor times the `C²`-decay factor, summed with `WeilEF.zero_sum_inv_sq`);
    - `weilRadicalTest_mass_ge` (evaluation at `−3i/2`, where `Φ̂ = ξ(2)`);
    - `zeta_weil_margin_superexponential`.
- **Verdict.**
  - The radical-producer conjecture is CIRCULAR.
  - Survivor: an unconditional no-slack law. The margin at level `L` is at most `exp(−π e^{2L−1/2} + 12L)`.
  - This is new relative to Zhu (conditional, `exp(−L e^L)`) and to CCM/CC (numerical).
- **Lesson for the producer.** The only structure that arithmetic provides unconditionally at level `L` is the radical, which makes the margin tiny. A producer must supply a lower bound that matches it to within `exp(−π e^{2L})`. Such a lower bound can only come from an identity or a rigidity, not from an estimate.
- **L30 addendum: a false density argument, recorded so it is not retried.**
  - Claim tested: `QW > 0` on `V_L = {(Φ⋆g)χ_L}`, because the tails are narrow edge spikes. On such spikes only the archimedean term acts, since `log 2` exceeds the spike width. `V_L` is dense in the form domain (the duality argument uses the analyticity of `Φ` and `Ξ ≢ 0`). Together these would give Weil positivity at every level.
  - Kill: the Epstein zeta (theta representation plus FE, but off-line zeros) would satisfy the same argument, so it is wrong. The error is that the narrow-spike estimate needs `‖g‖₁` moderate. Approximating a general test needs `ĝ ≈ f̂/Ξ`, whose norm blows up near zeros. The tail width then grows like `e^{−2L}·log‖g‖` and reaches `O(1)`, so the primes re-enter.
  - Survivor [P]: `QW((Φ⋆g)χ_L) > 0` for every `g` with `log‖g‖₁ ≤ c e^{2L}` (bounded-quotient cone). It is positivity along near-radical directions only, and tautological in spirit.

### L29 — The relaxed dictionary: error exponent `θ` confines the zeros to `|β−½| ≤ θ/2 + ε`. TRUE [L]
- **Statement** (`relaxed_hodge_dictionary`).
  - Setting: `Z` has local count `A₀` and no zeros below ordinate 2; `θ ≥ 0`, `ε > 0`, `a ≥ max(e¹², 1/ε)`.
  - Hypothesis: `Re W(f,f) ≥ −e^{θa}∫|f|²` for every polar-constrained `C²` test in `[−a,a]` (`RelaxedHodgeIndexAtLevel Z θ a`).
  - Conclusion: every zero with `10⁴A₀(log(|γ|+306) + log a + 2/ε + 2)log²a ≤ εa` has `|β−½| ≤ θ/2 + ε`.
  - Height form (`relaxed_hodge_dictionary_height`): all zeros up to `exp(εa/(2·10⁴A₀log²a))`, once `a ≥ a₀(ε,A₀)`.
  - ζ (`zeta_relaxed_hodge_dictionary`): the low-height hypothesis comes from `riemannZeta_ne_zero_of_im_sq_le`.
- **Lean.** Three modules, all wired; `lake build --old` green; axioms propext/choice/Quot.sound.
  - `EdgeConcentratedWeilTests` (631 lines).
  - `RelaxedHodgeDictionary` (917 lines).
  - `RelaxedHodgeDepthDictionary` (641 lines).
  - Refactors: `cluster_selection_radius` in `ClusterRobustHodgeExclusion`; `norm_lowHeightProfile_sub_le_tenth` in `LowHeightHodgeExclusion`.
- **Mechanism.**
  1. **Test.** `f = e^{−iγu}(s ⋆ g̃)` with the odd edge weight `s = sinh(δu)(b²−u²)₊^{5/2}` and the L27 killing factor `g`. The profile `Ψ = I ŝ G` is real-structured, so `Wsummand = m Ψ²`.
  2. **Gain.** `ŝ(−iδ) = P ≥ b²e^{2δ(b−2)}/16` against `‖s‖_∞ ≤ cosh(δb)b⁵`. The physical-space bound `∫|f|² ≤ 2a(‖s‖_∞‖g‖₁)²` (Young-type, no Plancherel) gives a gain of `e^{2δb}` over `∫|f|²`.
  3. **Killing cost.** `‖g‖₁ ≤ |G(x₀)|·Π(‖w'‖₁+|r|‖w‖₁)/(‖w‖₁|x₀−r|)`. The `ŵ` factors cost nothing, since `|ŵ(x₀)| ≥ ‖w‖₁`. The roots cost `(122/η)^{2n}(990/δ)²`.
  4. **Centre.** A penalized deepest zero, maximizing `Re ρ − λ|Im ρ − γ₀|` with `λ = 1/(8b e^{2/ε})`. No zero within ordinate `R+1` is more than `1/(8b)` deeper, so near-tail zeros cost `e^{O(1)}`.
  5. **Far zeros** (depth up to ½) are paid for by `(1+R)^M ≥ e^b`, with `1+R = e^{2/ε}` and `M = ⌈εa/2⌉`.
  6. **Balance.** The losses are `M + O(n log²a)` and the gain margin is `2εa`.
- **Verdict.** TRUE, in the form asked.
  - The exponent `θ` of the prime-side error at level `a` controls twice the abscissa excess of the zeros up to height `exp(a^{1−o(1)})`.
  - `θ = 1` (HF-F17, unconditional) gives the trivial `β < 1+ε`. Any `θ < 1` would give the quasi-RH `β ≤ (1+θ)/2 + ε` at those heights.
  - Beating the trivial prime-transport norm `e^a` by any exponential factor at level `a` is therefore at least as strong as a quasi-RH.
- **Open / next.**
  - The converse: a zero-free half-plane `β ≤ ½ + η` gives `Q_a ≥ −C(a)e^{2ηa}∫|f|²`? This needs a Plancherel–Pólya bound at sub-Nyquist density; above Nyquist depth is invisible (L22).
  - Removing `hlow` in general.

### L31 — The radical as a Nyquist-resolution detector (in progress)
- **Exploration kills recorded first.**
  - Truncated-radical descent: it reduces to the two-bump energy `m_b²·W(g(·−b)+g(·+b))`, i.e. WL lag positivity. CIRCULAR.
  - CCM (S1), evenness of the ground state: odd near-radical vectors are derivatives `(Φ⋆H)'` of even ones. Differentiation multiplies the double-exponential tail by `≈2πe^{2L}`, so heuristically `λ_odd/λ_even ≳ e^{4L}`. Proving that needs a lower bound on the odd energy, which is positivity. CIRCULAR as a producer.
  - Markov/Lévy structure of the polar-free form: already L16. REDISCOVERED.
- **Conjecture (bold).** For `ζ`, the level-`a` Hodge index excludes every off-line zero up to height `c·e^{2a}`, uniformly in depth and clustering up to polylogarithmic losses. So `Hodge(a)` is RH up to the Nyquist height, with the constant.
  - Mechanism. `Φ̂ = Ξ` kills every zero at once. Dividing `Φ̂` by `(z−γ₀)^{m₀}(z−γ̄₀)^{m₁}` restores exactly one off-line pair. That is done at kernel level by the resolvent `D_γ g(x) = −i e^{−iγx}∫_{−∞}^x g(u)e^{iγu}du`, which keeps the double-exponential decay because `ĝ(γ)=0`.
  - The two restored nodes carry a hyperbolic `(1,1)` block of size `|Ξ^{(m)}(ρ₀)/m!|² ≈ e^{−π|γ₀|/2}`. Truncation to `[−a,a]` costs `exp(−πe^{2a−O(1)})`. Negativity therefore follows once `|γ₀| ≲ 2e^{2a}` (4e^{2a} with a two-sided tail estimate).
  - Compared with L28 (`exp(a/(2000A₀log(10⁶/δ)))`), the horizon improves exponentially and reaches the Nyquist scale, above which HF-F18 shows depth is invisible to abstract configurations.
- **Kill attempts.**
  - *False?* The lattice masking counterexamples (HF-F18, L27, L29) have compactly supported radicals of radius `L/2`. The same mechanism then detects exactly at `a ≥ L/2`, which is their proven threshold, so the conjecture is consistent with them and even predicts them.
  - *Circular?* No. The inputs are the unconditional radical identity and an unconditional local lower bound for `ξ` near a zero.
  - *Rediscovered?* Bombieri 2000 (negative eigenvalues ↔ off-line zeros, no horizon), arXiv 2607.02828 (finite Galerkin dictionary, no exclusion), 2608.24827, 2609.20367, and Connes' folklore "cutoff `λ` sees height `λ²`" (heuristic only). No theorem found.
  - *Insignificant?* It is a receiver, not a producer. But it closes the HF horizon question (HF-F21/F23, L27–L29): the finite-level Hodge index is, for `ζ`, at least RH up to height `≍ e^{2a}`.
  - Verdict: SURVIVES PRELIMINARY ATTACK.
- **Paper proof (Theorem A, flatness law).**
  - Setting: `ρ₀` off-line zero, `γ₀ = gammaOf ρ₀`, `γ₁ = conj γ₀`, orders `m₀, m₁`, local factors `Φ̂ = (z−γ_j)^{m_j}u_j`.
  - Construction:
    - `h = D_{γ₀}^{m₀}D_{γ₁}^{m₁}Φ`, so `ĥ = Φ̂/((z−γ₀)^{m₀}(z−γ₁)^{m₁})`.
    - `f = N_op P_op(χ_b h)`, where `P(z) = cos(sz)−cosh(s/2)` gives exact polar vanishing and `N(z) = c₁+c₂e^{isz}` interpolates `N(γ₀)=1`, `N(γ₁)=v`, `|v|=1`.
  - Non-node zeros see only the tail `E=(1−χ_b)h`. The node block has real part `−(m_{ρ₀}+m_{ρ̄'})|P(γ₀)P(γ₁)ĥ(γ₀)ĥ(γ₁)|` plus tail cross terms.
  - Hodge(a) therefore forces `|u₀(γ₀)u₁(γ₁)| ≤ (2|δ₀|)^{m₀+m₁}·(tail at a−O(1))·(poly)`.
  - Tail iteration: `∫_{|x|≥X}|D g|e^{λ|x|} ≤ 2∫_{|u|≥X}|g|e^{(λ+3/2)|u|}`.
- **Theorem B.** Combines Theorem A with the local lower bound `|ξ^{(m)}(ρ₀)/m!| ≥ e^{−π|γ₀|/4}·T^{−C}·Π_{nearby}|ρ₀−ρ|`. That bound comes from Borel–Carathéodory: `HTGeometry.BallLogarithm`, `AnalyticBallFinsetFactorization`.

### L32 — The converse of the relaxed dictionary: error exponent = 2 × abscissa excess, exactly when off-line multiplicity is bounded. TRUE [L]; the density hypothesis is sharp [L]
(Label L32 because L28–L31 are also used by a parallel cycle in this card.)
- **Question (user).** If all zeros up to height `T` satisfy `|β−½| ≤ η` and the local density there is sub-Nyquist, does `Q_a ≥ −C·a·e^{2ηa}∫|f|²` follow? Together with L29 (relaxed dictionary) this would make "error exponent = 2 × abscissa excess" an exact equivalence.
- **Answer, in three parts.**
  1. *"Up to height `T`" is false for every `T`.* The level-`a` form sees every height: a single pair `¾ + iT, ¼ + iT` has eventual error exponent exactly `½` (`offLinePairConfig_eventually_relaxed_iff`, any `T ≥ 2`). The hypothesis must be global.
  2. *Global converse, TRUE [L].* If every zero has `|β−½| ≤ η` and every unit window carries off-line multiplicity `≤ D`, then `Re W(f,f) ≥ −3500(2a+3)·D·e^{2η(a+2)}∫|f|²` for **every** continuous `f` on `[−a,a]` (`re_W_ge_of_depth_offLineDensity`). No polar constraint and no smoothness are needed. On-line zeros cost nothing, so `D = 0` gives Weil positivity, and "sub-Nyquist" is not needed: any finite `D` works.
  3. *Exact equivalence [L].* Assume the local count `A₀ log`, no zeros below ordinate 2, and off-line density `≤ D`. Then `∀ρ, |β−½| ≤ η` ⟺ `∀θ > 2η`, the relaxed index `Re W ≥ −e^{θa}∫|f|²` holds for all large `a` (`abs_re_sub_half_le_iff_eventually_relaxed`). So `inf{θ eventually admissible} = 2 sup|β−½|`.
- **Sharpness of the density hypothesis [L]** (`OffLineClusterWeilUnbounded`).
  - The cluster configuration has, at each height `e^{k+1}`, the pair `¾ + ie^{k+1}, ¼ + ie^{k+1}`, each of multiplicity `k+1 = ⌊log γ⌋`.
  - It has depth `¼` everywhere, the ζ-type count `N(t,t+1] ≤ 2log(|t|+3)`, and no zeros below 2.
  - Yet at every large level the relaxed index fails for **every** `θ`, and `Re W` is unbounded below on polar-constrained tests (`offLineClusterConfig_eventually_not_relaxed`, `offLineClusterConfig_weil_unbounded_below`, `exists_bounded_depth_without_error_exponent`).
  - So the uniform error exponent sees depth **and** off-line multiplicity. A multiplicity growing like `log γ` at fixed depth already makes it `+∞`.
- **Mechanism (converse).**
  1. `Re(AB̄) ≥ −|A−B|²/4`. This leaves only the depth differences `h_f(x_ρ) − h_f(x̄_ρ) = ∫f·(e^{ix_ρu} − e^{ix̄_ρu})`, which vanish on the line.
  2. A weighted Bessel inequality (pointwise AM–GM plus the Schur test, with no Cauchy–Schwarz on integrals).
  3. The plateau weight `h_J = Σ_{|j|≤J} w₁(·−j) ≥ (3/4)^{5/2}` on `[−J, J]`, with `ĥ_J = (Σ_j e^{izj})ŵ₁`.
  4. The Gram kernel is four values of `ĥ_J` at `|Im| ≤ 2η`, and unit windows give row sums `≤ 10D·672(2J+1)e^{2η(J+1)}`.
- **Mechanism (cluster).**
  - Polar-corrected deep-zero test at height `e^{k+1}`. Isolation holds at radius `e^a` for `k > a`.
  - The isolation inequality keeps the multiplicity: the pair gives `−2(k+1)P²`, and everything else gives `O((k+2)‖s‖²)`.
  - `P² ≥ 12288‖s‖²` for large `a`. The polar coefficients are `O(1/k)` and the test energy stays bounded, so taking `k` large beats `e^{θa}`.
- **Novelty audit.**
  - The Bessel core is the classical Plancherel–Pólya / Carleson-measure bound for Paley–Wiener spaces (uniform density in a strip ⇒ `Σ|F(z_k)|² ≲ e^{2ηa}(a+1)D‖F‖²`). BRIDGE.
  - The corpus had the fixed-test (Landau-type) version: `CCMRectangularOneSidedTransverseExponent`, where a power budget `n^α` of one observable holds iff `Re ρ ≤ ½+α`, unconditionally and with no density.
  - New here:
    - the exact equivalence for the **uniform** (quadratic-form) exponent;
    - on-line zeros being free, so the relevant density is the off-line one;
    - the counterexample showing the uniform exponent is **not** a function of the abscissa excess under ζ-type counts.
  - The fixed-test and uniform exponents differ precisely by off-line multiplicity growth.
- **Route consequence (HF).**
  - `θ*(a) < 1` for ζ ⟹ quasi-RH (L29, unconditional).
  - Quasi-RH ⟹ `θ* < 1` iff (up to the cluster obstruction) the off-line multiplicity of ζ is locally bounded.
  - For ζ only `θ* ≤ 1` is known (HF-F17).
  - Open: is the relaxed exponent of ζ equal to `2Θ_ζ` unconditionally? The zero side needs bounded off-line density. The prime side needs smoothness of `f`, which the `L²` index does not see.
- **Modules.** `RHTower/OffLineDensityWeilLowerBound` (835 lines), `RHTower/ErrorExponentAbscissaExcessLaw` (248), `RHTower/OffLineClusterWeilUnbounded` (654). All are wired into `RHTower.lean` and built with `lake build --old`. Axioms: propext, Classical.choice, Quot.sound.

### L33 — ζ-specific height reduction: the level-`a` Weil form of ζ sees only its zeros below `exp(O(e^a))`. TRUE [L]
- **Question.** L32 showed that for abstract configurations the depth hypothesis must be global: an off-line pair at any height has eventual exponent ½. Does ζ, through its explicit formula, have a finite horizon?
- **Theorem** (`RHTower/ZetaWeilFormHeightReduction:zeta_re_W_ge_of_depth_below_horizon`). There is `A₀` such that for `a > 0` and `0 ≤ η ≤ ½`: suppose every zero with `|γ| ≤ H(A₀,a)` has `|β−½| ≤ η`, and the unit windows below `H` carry off-line multiplicity `≤ D`. Then every polar-constrained `C²` test on `[−a,a]` has
  `Re W(f,f) ≥ −(7000(2a+3)·D·e^{2η(a+2)} + 2)∫|f|²`,
  with `log H(A₀,a) ≤ 7000e^a + log A₀ + 160` (`log_zetaHorizonHeight_le`).
- **Corollaries.**
  - "Zeros up to height `T`" form, for every `a` with `H(A₀,a) ≤ T` (`zeta_re_W_ge_of_depth_up_to_height`). This rescues the original L30 formulation for ζ. For abstract configurations it is false (L32 pair).
  - Relaxed-index form (`zeta_relaxedHodgeIndexAtLevel_of_depth_below_horizon`).
  - **Finite verification.** RH below `H(A₀,a)` gives `Re W ≥ −2∫|f|²` at level `a` (`zeta_re_W_ge_neg_two_of_critical_below_horizon`).
- **Mechanism.**
  1. Split `W(f,f) = W(f,g) + (W(f,f) − W(f,g))`, where `ĝ = f̂·q_b²`, `q_b = ŵ_b/ŵ_b(0)`, `w_b = (b²−u²)₊^{5/2}`, and `b = e^{−2E}/4`.
  2. **Symbol side** (`RHTower/ZetaSymbolArchimedeanHorizon`). The bilinear explicit formula (only `f` needs polar zeros) gives the density `|f̂|²(1−q_b²)(μ+P_X)`.
     - `μ ≥ (log(1+|τ|/4) − 10)/(2π)`, from two digamma recurrences plus `|ψ−log| ≤ 3/|z|`.
     - `P_X ≥ −(34/π)√X`, since `Σ_{n≤N}Λ(n)/√n ≤ 34√N` by dyadic induction on Chebyshev.
     - Hence `μ+P_X ≥ 0` above `4e^E`, with `E = 10 + 68√X`, `X = e^{2(a+2)}`.
     - Below that height `0 ≤ 1−q_b² ≤ (bτ)²`. Plancherel then gives the error `≥ −E e^{−2E}∫|f|²`.
  3. **Zero side.** The summand is `m·f̂(x)·conj f̂(x̄)·q_b(x)²`.
     - Below `H`: `Re(AB̄c) ≥ −|A−B|²/4 − |A||B||c−q_b(γ)²|`. This is summed by the height-restricted depth Bessel bound (L32 machinery restricted to `|γ| ≤ H`) and a plain Bessel bound over off-line zeros for the phase error `6b|β−½|`.
     - Above `H`: `|q_b|² ≤ e·400²/(b⁶(1+|γ|)⁴)`, summed by the local count.
- **Kill attempts.**
  - *Circular?* No. The inputs are the unconditional explicit formula, Chebyshev, digamma bounds and the local count.
  - *Rediscovered?* Smoothing the explicit formula so that far zeros are negligible is standard. The corpus had only the symbol-side horizon (`PrimeTransportPoleSchurNorm`: positivity for tests living above `exp((1+o(1))e^a)`). The zero-side reduction of the level-`a` index to finitely many zeros, with explicit height, is new in the corpus. Verdict: BRIDGE with a new quantitative statement.
- **Picture for ζ at level `a`.**
  - The index sees zeros up to `exp(εa/log²a)` (L29).
  - It is determined, from above, by zeros up to `exp(O(e^a))` (L33).
  - The region in between is the frontier map's "height-blind" zone. L31's conjecture (Nyquist height `e^{2a}`) targets its lower edge.
- **Horizon constant.** It is `7000` rather than `1+o(1)` because of the crude `√X` prime bound and the `b⁻⁶` tail. The sharp PNT constant (`primeTransport_horizon_law`) would give `log H ≍ e^a`.
- **Modules.** `RHTower/ZetaSymbolArchimedeanHorizon` (671 lines), `RHTower/ZetaWeilFormHeightReduction` (952). Both are wired and built with `lake build --old`. Axioms: propext, Classical.choice, Quot.sound.
- **L31 result [L]: the Nyquist flatness law.** Four modules, all wired after `WeilMarginSuperexponentialLaw`; built; axioms propext/choice/Quot.sound; the lint errors that remain belong to other, unwired modules.
  - `RHTower/ResolventDivisionDecay` (general).
    - `D_γ g(x) = −ie^{−iγx}∫_{u≤x} g e^{iγu}`.
    - `(z−γ)·(D_γ g)^ = ĝ` (`paperFT_resolventDiv_mul`).
    - Pointwise decay `‖D_γ g(x)‖ ≤ e^{−μ|x|}∫_{|u|≥|x|}‖g‖e^{(μ+½)|u|}` when `ĝ(γ)=0`.
    - Tail iteration `∫_{|x|≥X}‖D_γ g‖e^{c|x|} ≤ 2∫_{|u|≥X}‖g‖e^{(c+3/2)|u|}`.
    - Iteration at a zero of order `m`, with the leading factor carried along (`iterResolvent_spec`, `iterResolvent_eventually_ne`).
  - `RHTower/RadicalDetectionKernel`.
    - `Ξ = paperFT Φ` (`riemannXiHat`) and its local factorisation at zeros.
    - `OffLinePairData`, the kernel `h = D_{γ₀}^{m₀}D_{γ₁}^{m₁}Φ`.
    - `kernel_mul`: `(z−γ₀)^{m₀}(z−γ₁)^{m₁}ĥ = Ξ`; `kernel_eq_zero` at every other zero; `kernel_at_γ₀/γ₁`.
    - The smooth plateau, the polar operator and the node operator, and `kernel_calculus`.
  - `RHTower/HodgeOffLineFlatnessLaw`.
    - `re_W_le_node_add`: one pair against the rest, for any `C²` test.
    - The test `f = N P(χ h)`; `node_inequality`; `flatness` (node values ≤ tail of `Φ` × poly).
    - `exists_offLinePairData`.
  - `RHTower/HodgeZetaFlatnessLaw`.
    - `local_factor_unique`; transfer to `ζ` (`norm_leading_riemannXiHat`).
    - `|Γ(1+iy)|² = πy/sinh πy`, a lower bound for `Γ` in the strip, and `|ξ_unit(ρ)| ≥ e^{−π|t|/4}`.
    - Polar symbol lower bound `β(1−β)/128`.
    - Tail of `Φ`: `≤ 80Mθe^π e^{(c+9/2)X−πe^{2X}}/κ`.
    - **`hodgeIndex_zeta_flatness_explicit`.**
- **Verdict (L31).** SURVIVES and is PROVED as a flatness law. At every off-line zero below height `≈ 2e^{2a−3/4}`, the level-`a` Hodge index forces the product of the leading Taylor coefficients of `ζ` at the zero and at its mirror below `exp((π/2)|t₀| − πe^{2a−3/4} + O(Na))`.
  - The horizon is Nyquist, up to a constant factor `e^{−3/4}`. It is exponentially beyond L28's `exp(a/(2000A₀log(10⁶/δ)))`, and depth enters only polynomially.
  - The mechanism is structural: the radical is a killer of all zeros at once, and the only cost is its truncation.
- **What is still open for full exclusion (next loop).** An unconditional lower bound on `|ζ^{(m)}(ρ)/m!|`: Borel–Carathéodory gives `≥ e^{−C log²T}·Π_{nearby}|ρ−ρ'|`. Flatness then forces a super-tight cluster, with another zero within `exp(−c(e^{2a}−|t₀|/2)/log T)`.
  - To exclude clusters, divide `Φ̂` by the whole cluster polynomial and interpolate on the cluster. This is the L28 Lagrange/contour machinery, with the radical `Ξ` replacing `Ŵ^N·(killing polynomial)`.
  - That would make the level-`a` Hodge index for `ζ` exactly as strong as RH up to height `≍ e^{2a}`.
- **Producer lesson.** Level-`a` positivity is (at least) RH at the Nyquist height `≍ e^{2a}`, with margin `exp(−πe^{2a})` (MUST-478). A producer at level `a` must therefore decide the location of all `≍ ae^{2a}` zeros below `e^{2a}` from arithmetic alone. There is no shortcut: any partial positivity at level `a` already contains that information.

### L32 — From flatness to exclusion: the radical-weighted cluster test (in progress)
- **Conjecture.** For `ζ`, Hodge(a) excludes every off-line zero of depth `≥ δ` up to height `2e^{2a−3/4} − C·(A₀ log T)²·log(C/δ)`. The bound is uniform in clustering: internal cluster distances never enter.
- **Why L31 does not suffice.** The single-pair test normalizes the node block by `|Ξ-coefficient|`, which is `∝ Π_{nearby}|ρ₀−ρ'|`. A super-tight off-line cluster makes it arbitrarily small.
- **Mechanism.** Combine the L28 multi-node interpolation with the L31 radical.
  - Profile `Ψ(z) = Ξ(z)/P_S(z) · Ŵ(z−t₀)^N · P_pol(z)`, where `P_S` is the full cluster polynomial with multiplicities. At kernel level this is the composite resolvent `Π_σ D_{γ_σ}^{m_σ}Φ`.
  - `Q` interpolates `±i/Ψ` at the cluster nodes. It is realized on the bump side, `h ⋆ Q(i∂)(e^{−it₀x}W^{⋆N})`, so no smoothness is lost.
  - Each node pair contributes exactly `−(m+m')`. The on-line and shallow zeros are killed by `Ξ`, the far zeros are damped by `Ŵ^N`, and the truncation tail is `exp(−πe^{2a−3/4})`.
  - Only `|Ψω|` on the rectangle sides enters (`HTGeometry.sum_nodalWeight_inside_eq_rectangleIntegral`). The side selection by forward differences costs `(δ/16e)^{|S|}`, independent of cluster geometry.
- **Analytic input still needed.** A lower bound for `|Ξ/P_S|` on the rectangle sides: `≥ e^{−π|t|/4}T^{−C}·(side distance)^N`. This is Borel–Carathéodory on a disc with the zeros extracted (`HTGeometry.BallLogarithm`, `AnalyticBallFinsetFactorization`, the `ZetaLocalZeroCount` Jensen count).
- **L32 result [L]: Nyquist exclusion for separated zeros.** Module `RHTower/HodgeNyquistExclusion` (781 lines), wired after `HodgeZetaFlatnessLaw`; built; axioms propext/choice/Quot.sound.
  - Unconditional analytic lower bound.
    - `abs_log_norm_sub_le`: `log|f|` is Lipschitz along segments where `f'/f` is bounded.
    - Horizontal and vertical path bounds for `|ζ|`, from the corpus bound `|ζ'/ζ| ≪ log t/δ`.
    - `exists_good_height`: pigeonhole choice of a height.
    - `norm_leading_zeta_ge`: `|ζ^{(k)}(ρ₀)/k!| ≥ (1/3)exp(−C log(t₀+1)(16(N+1)/d+1))` at a `d`-separated zero with `β₀ > ½`. Proved by minimum modulus on the circle of radius `d/2`.
  - Symmetry: `riemannXiHat_conj` (`Ξ(conj z) = conj Ξ(z)`), and `OffLinePairData.norm_u₁_eq` (the mirror node has the same order and leading modulus).
  - **`hodgeIndex_excludes_separated_zero`** and **`hodgeIndex_nyquist_horizon`**. If Hodge(a) holds (`a ≥ 1`), every zero `ρ₀ = β₀+it₀` with `β₀ > ½`, `t₀ ≥ 8`, order `k`, separated by `d` from all other zeros (its mirror included), satisfies `πe^{2a−3/4} ≤ (π/2)t₀ + 2C log(t₀+1)(16(N+1)/d+1) + (3k+5)(a−3/8) + a/2 + log(9K·16^k(1+1/|β₀−½|)²(1+|γ₀|)²G_Φ(2k)/(β₀(1−β₀))²)`.
- **Verdict (L32).** The conjecture holds for separated zeros. The level-`a` Hodge index for `ζ` excludes every off-line zero below `2e^{2a−3/4} − O(polylog/d)`. Depth enters only through `d ≤ 2(β₀−½)`, as `1/δ` in the polylog term.
  - Remaining: super-tight clusters, meaning another zero within `O(log²t/e^{2a})`. These need the multi-node test.
  - `multiResolvent_spec` (division by a finite divisor) is written and compiles in scratch (`formal/tmp/l31/D1.lean`), ready for that.
- **Frontier consequence.** The HF horizon question (L25–L29, HF-F21/F23) is closed up to clusters. For `ζ`, Hodge(a) is RH up to height `≍ e^{2a}`, the Nyquist ceiling, which is exponentially beyond every previous exclusion horizon from finite-level positivity.

### L34 — Producer classes of the 2025–26 literature, and the cluster-robust Nyquist exclusion (in progress)
(Label L34 because L33 is taken by the parallel cycle.)
- **External state, checked 2026-09-27.**
  - CCM "Zeta spectral triples" (arXiv 2511.22755). If the lowest eigenvalue of `QW_λ` is simple with an even eigenvector, `ξ̂_λ` has only real zeros. They conjecture `ξ̂_λ → Ξ` on closed substrips of `|Im z|<½`, and Cor. 3.8 states `lim μ_λ = 0 ⇒ RH`.
  - Connes (arXiv 2511.23257): real zeros for the ground state of any lower-bounded convolution form (continuous Carathéodory–Fejér).
  - arXiv 2605.20224: numerics only, "no claim of proof".
  - arXiv 2608.24827: empirical decay `−ln λ_min ≈ 2π²N(T*)/ln N(T*)`, `T* = 2πe^{2L}`.
  - Suzuki (arXiv 2606.09096): screw-function operator framework, conjectural limit operator.
  - No finite-level exclusion theorem anywhere.
- **Producer classes tried first (kills).**
  1. *Level increment* (`Hodge(a) ⇒ Hodge(a+δ)` from primes in `(e^{2a}, e^{2a+2δ}]`).
     - For fixed ζ the implication is content-free unless RH fails. For free weights on the new primes it is false, because the admissible weights form a convex set with `Λ` at its boundary (exact-primes gate). CIRCULAR.
  2. *Hurwitz producer through a PSD convolution form* `B_ν(f) = ∫|f̂|²dν`, with `ν ≥ 0` supported on the real zeros of `Ξ`.
     - Such a form is PSD with no hypothesis, and `Φ` lies in its radical. But `D_{γ₀}D_{γ̄₀}Φ` (off-line pair divided out) also lies in its radical, and its truncation tail is smaller by `(t₀/2πe^{2a})²`.
     - So ground states can converge to `Ξ` with its off-line zeros removed. A real-rooted limit carries no information. Only the indefinite (hyperbolic) part of the Weil form sees off-line zeros. BLIND.
  3. *Fake continuation / Beurling extension* (primes beyond `e^{2a}` replaced by a system with a positive Weil distribution).
     - Continuing by `Π' = li` gives an entire zero-free `ζ'`. Its symbol is the truncated explicit-formula symbol `A − D_X + pole`, so positivity in the Fejér–Riesz cone is `Hodge(a)` itself. Duality: `Hodge(a) ⟺ ∃ ν ≥ 0` with `ν̂ = W` on `(−2a,2a)`. CIRCULAR.
  4. *Predictability of primes by the canonical (Krein) extension.*
     - Under RH the zero set is eventually denser than Nyquist. It is then a sampling, non-interpolating set for `PW_a`, so `PW_a` is not dense in `L²(Z)` and the extension problem is indeterminate.
     - The primes beyond `e^{2a}` are one of infinitely many admissible continuations. FALSE.
  5. *Grönwall barrier at `μ(a)=0`.* For Toeplitz/Krein systems, a singular PSD section extends PSD only through the canonical next moment, so zero is not a barrier. FALSE.
  6. *Lee–Yang torus realization.*
     - The Kurasov–Sarnak construction needs a reflector that is a product of torus variables (conductor `Π p`). The Γ-phase `θ(t)` is not almost periodic.
     - Its local linearization at height `T` is the Riemann–Siegel reflector `(T/2π)^{it}`, and the resulting Hermite–Biehler condition is Gram's law, which fails. FALSE.
  - Positive statement common to 2 and 4: at finite level, only the hyperbolic off-line blocks separate `ζ` from its RH shadow. Whatever a producer certifies at level `a`, it certifies RH to the height where the hyperbolic blocks are visible. That height is the object of the conjecture below.
- **Conjecture (cluster-robust Nyquist exclusion).** For `ζ`, `Hodge(a)` excludes every zero with `β₀ > ½` below height `2e^{2a−c} − C·n·(log(1/(β₀−½)) + log n + log t₀) − C·log²t₀`, where `n` is the number of zeros in the ordinate window of width 4. Internal cluster distances do not enter.
- **Mechanism.**
  - Divide `Ξ` by the whole node divisor `P_S`, where `S` is every zero of depth `> y₀` in the window. At the kernel level this is the composite resolvent `D_SΦ`, which keeps `Φ`'s double-exponential tail uniformly in the geometry.
  - Multiply by an exponential polynomial `q(z) = Σ c_k e^{iks z}`, i.e. a shift operator with `(n−1)s ≤ 1/8`, chosen to interpolate `±i/(P_pol·Ξ/P_S)` at the nodes. Every node then contributes `−m_σ`; every other zero is killed by `Ξ`, and the polar points by `P_pol`.
  - The size of `q` on `ℝ` comes from a rectangle contour in the `z`-plane with exponential nodal weight `Ω(e^{ist})`. Only `|Ω|` and `|Ξ/P_S|` on the rectangle sides enter.
  - Forward-difference side selection costs `(δ/8e)^{|V|}`. The Fourier coefficients of `q` are bounded by `sup_ℝ|q|`.
  - The lower bound for `|Ξ/P_S|` on the sides comes from Lipschitz continuity of `log|ζ/P_V|` with constant `C log t`, where `P_V` is the window divisor. The only input is `ζ'/ζ − Σ_{near} 1/(s−ρ) = O(log t)`.
- **Kill attempts.**
  - *False?* The two-node law (L31) and L32 hold. Super-tight clusters make the two-node block small, but here they are nodes, and `Ξ/P_S` is zero-free on the rectangle. No counterexample shape remains, since `ζ`'s configuration is fixed.
  - *Circular?* No. The inputs are the radical identity, the local zero count, and `ζ'/ζ` partial fractions.
  - *Rediscovered?* CCM Cor. 3.8 is the limit statement (`lim μ=0 ⇒ RH`) with no height. Bombieri 2000 and Yoshida 1992 give no horizon, and L28's horizon is `exp(a/(2000A₀log(10⁶/δ)))`.
  - *Insignificant?* It is a receiver. It closes three open items listed on the frontier map under HF ("multi-node cluster exclusion", "remove density/crowding masks", "uniform Nyquist constant"). It also fixes exactly what any producer at level `a` must certify: RH up to `≍ e^{2a}`.
  - Verdict: SURVIVES PRELIMINARY ATTACK.

### L34 — The finite-level inertia law: the negative squares of the level-`a` Hodge form of ζ are its off-line pairs between the visibility height and the archimedean horizon. TRUE [L]
- **Conjecture (bold).** At every level `a` and threshold `ε`, the `ε`-negative index of the polar-constrained level-`a` Weil form of ζ is at most the number of off-line pairs below `exp(O(e^a + log 1/ε))`. It is at least the number of separated, isolated, visible pairs (minus the two polar constraints).
  - This is a quantitative, level-wise form of Bombieri's count. His version holds only for large enough truncations and assumes finitely many off-line zeros.
- **Literature audit.**
  - Bombieri, "Remarks on Weil's quadratic functional I" (eudml 252338): the negative index of big truncations is half the number of off-line zeros, when that number is finite.
  - arXiv 2607.02828 (finite Guinand–Weil dictionary, eigenvalue certification) and 2608.24827 (finite reduction on compact windows; certificates must resolve frequencies up to `2πe^{A_L}`) work on the symbol side and do not count zeros.
  - No level-wise count with a horizon was found. Verdict: SURVIVES; BRIDGE (Bombieri + L33) with a new quantitative statement.
- **Theorem** (`RHTower/ZetaWeilFiniteLevelInertia:zeta_weil_inertia_law`). Let `weilNegIndex Z a ε` be the largest dimension of a space of polar-constrained `C²` tests on `[−a,a]` with `Re W < −ε∫|f|²` off `0`. There is `A₀` such that:
  - **(upper)** `weilNegIndex(a,ε) ≤ #{off-line pairs with |γ| ≤ H(A₀,a,ε)}`, where `log H ≤ 7000e^a + 7log A₀ + 7log(1/ε) + 150`. Each pair counts once whatever its multiplicity.
  - **(lower)** Let `T` be a set of zeros of depth `≥ δ`, pairwise `2R` apart with `R ≥ 1`, isolated at radius `R`, and visible (`visibleMargin > 0`, roughly `log H_m ≲ e^{2δa}/poly(a)` and `R ≳ e^a`). Then `weilNegIndex(a,ε) ≥ |T| − 2` for `ε ≤ λ/(|T|(∫s²+1))`.
- **Mechanism (upper, `ZetaWeilNegativeIndexHorizon`).**
  - Node conditions: `f̂(x_ρ) = f̂(x̄_ρ)` at the off-line zeros below `H` imply `Re W ≥ −ε∫|f|²`.
  - The L33 split is used with `b = εe^{−2E}/(8A₀)`. With the node condition, an off-line summand is `m|A|²Re q_b(x)²`, so its phase error is at most `2b²m|A|²`.
  - That error is summed by a plain Bessel bound with the unconditional density `A₀log(H+4)`. The symbol side contributes `ε/8`, the phase `ε/3`, and the tail `ε/3`.
  - One condition per pair (`x_{1−ρ̄} = x̄_ρ`) makes `f ↦ (f̂(x_ρ) − f̂(x̄_ρ))_ρ` injective on any `ε`-negative space.
- **Mechanism (lower).**
  - Tests: modulated sinh tests at the heights in `T`.
  - Diagonal: the isolation inequality, with energy monotone in depth.
  - Off-diagonal: decay `K/(1+Δ)²`, from `(1+d₁)²(1+d₂)² ≥ (1+Δ)²(1+min)²/4` and a new power-two window sum under the log count (`Σ log(1+|n|)/(1+|n|)² ≤ 12`, by a telescoping `(m+1)^{−3/2}` bound). Separation gives `Σ_{σ≠ρ} ≤ 10/R²`.
  - The Gram expansion plus the Schur test finish the negativity bound. The polar constraints are handled by rank–nullity on `(ĥ(i/2), ĥ(−i/2))`. The threshold comes from `|Σc_ρf_ρ| ≤ |s|Σ|c_ρ|`.
- **Route consequence (HF).**
  - The obstruction to `Hodge(a)`, measured as a Krein negative index, is a finite count of off-line pairs.
  - Every pair above `exp(O(e^a))` is invisible.
  - Every isolated deep pair below `exp(e^{2δa−O(log a)})` is one negative square.
  - The gray zone between these heights is exactly where masking can change the count.
- **Modules.** `RHTower/ZetaWeilNegativeIndexHorizon` (upper, ~705 lines) and `RHTower/ZetaWeilFiniteLevelInertia` (lower + law, ~990 lines). Both are wired and built with `lake build --old`. Axioms: propext, Classical.choice, Quot.sound.

### L35 — The near radical of the level-`a` Weil form has dimension `≍ e^{2a}` (in progress)
- **Literature (checked 2026-09-27).**
  - Connes–Consani, *Spectral triples and ζ-cycles* (arXiv 2106.01715, §3): QW_λ on `[λ⁻¹,λ]` has about `2λ²` "extremely small" eigenvalues, with eigenvectors close to `E(prolate)`. This is observed numerically and explained heuristically; there is no theorem.
  - CCM, *Zeta spectral triples* (arXiv 2511.22755, §8): `ε_λ ≈ 1 − χ(λ) ~ e^{−4πλ²}`, numerical.
  - Zhu (arXiv 2608.24827): Conj. 12.1, the fitted Landau–Widom law `−ln λ* ≈ C N(T*)/ln N(T*)`; Thm 1.3 is conditional on RH and bounds only `λ₁`.
  - Corpus: L30 gives one vector with margin `exp(−πe^{2a−1/2}+12a)`.
- **Conjecture (bold).** There are absolute constants `c, c' > 0` such that, for all large `a`, the polar-constrained `C²` tests on `[−a,a]` contain a subspace `V` with `dim V ≥ c e^{2a}` on which `|W(f,f)| ≤ exp(−c'e^{2a})∫|f|²`.
  - By min–max, the `⌊c e^{2a}⌋` lowest eigenvalues of the level-`a` Hodge form are all at most `exp(−c'e^{2a})`, unconditionally.
  - Sharp form [OPEN]: the count is `(2−O(η))e^{2a}` at margin `exp(−ηe^{2a})` (CC's prolate count). Polynomial multipliers can reach at most `(π/2)e^{2a}`.
- **Mechanism.**
  - The tests are `F_a = Σ_{k≤K} a_k Φ^{(k)}`, with transform `Q_a(−iz)Ξ(z)`, so they lie in the exact radical.
  - On `u > 0`, `Φ^{(k)}(u) = Σ_{n≥1} e^{u/2} P_k(n²e^{2u}) e^{−πn²e^{2u}}`, where `P_k = D^k(4π²X²−6πX)` and `DR = R/2 + 2XR' − 2πXR`. So `F_a` is a weighted polynomial `R_a` in `Y = e^{2u}` of degree `≤ K+2`.
  - Truncate with a cutoff `χ` (equal to 1 on `[−(a−1), a−1]`). The Weil energy is that of the tail `t = F(1−χ)`: `|W| ≤ (5/4)S_Z(∫(|t|+|t'|)e^{|u|/2})²`.
  - **Tail** (`Y ≥ Y₀ = e^{2a−2}`): Lagrange extrapolation from equispaced nodes on `[Y₀/8, Y₀/4]` gives `|R|, |R'| ≤ M·k·(16eY/Y₀)^k` with no factorial loss.
  - **Bulk** (`Y ∈ [Y₀/8, Y₀/4]`): a Remez inequality in the variable `e^{2u}` shows that `|R| ≥ (8e)^{−k}M` on a set of `u`-measure `≥ 1/11`. The `n ≥ 2` terms are smaller by `(8e)^k e^{−πY₀/2}`.
  - The negative side follows by the parity `Φ^{(k)}(−u) = (−1)^kΦ^{(k)}(u)`.
  - **Ratio**: `(128e²)^{2k} e^{−3πY₀/2}·poly ≤ e^{−3Y₀}` for `k ≤ Y₀/10`. Removing the two polar functionals costs 2 dimensions.
- **Target theorem.** For all large `a`: `dim V ≥ e^{2a−2}/10 − 4` and `‖W(f,f)‖ ≤ exp(−3e^{2a−2})∫‖f‖²` on `V`.

### L35 result — The near radical of the level-`a` Weil form has dimension `≍ e^{2a}`. TRUE [L]
- **Theorem** (`RHTower/WeilNearRadicalDimension:zeta_weil_near_radical_dimension`; unconditional; axioms propext, Classical.choice, Quot.sound).
  - For all large `a`, the Hodge-class tests (`C²`, `tsupport ⊆ [−a,a]`, `f̂(±i/2) = 0`) contain a subspace `V` with `dim V ≥ e^{2a−2}/20`.
  - On `V`, `‖W(f,f)‖ ≤ exp(−e^{2a−2})∫|f|²`.
  - By min–max, at least `e^{2a−2}/20` eigenvalues of the level-`a` Weil/Hodge form lie below `exp(−e^{2a−2})`.
  - This is the order of magnitude of Connes–Consani's numerically observed `≈ 2e^{2a}` extremely small eigenvalues, now a theorem.
- **Construction.**
  - `V` is the kernel of the two polar functionals inside `{(Σ_{i≤K} a_iΦ^{(i)})·χ_a}`, `K = ⌊e^{2a−2}/10⌋ − 3`.
  - `χ_a = ϑ(a−u)ϑ(a+u)` is 1 on `[−(a−1), a−1]`. `Φ^{(i)}` has transform `(−iz)^iΞ(z)`, so it lies in the exact radical, and the Weil energy is that of the tail.
  - Tail: Lagrange extrapolation from `[Y₀/8, Y₀/4]` with no factorial loss (the node products `i!(k−i)!` and `Σ1/(i!(k−i)!) = 2^k/k!`). Bulk: a Remez inequality in the chart `e^{2u}`, again with exponential rather than factorial loss.
  - Ratio: `137984·k²Y₀⁴(128e²)^{2k}e^{−3πY₀/2} ≤ e^{−Y₀}` for `k + 1 ≤ Y₀/10`, `Y₀ = e^{2a−2} ≥ max(100, log(720C+1))`.
- **Modules** (all wired, `lake build --old` green):
  - `HTGeometry/PolynomialExtrapolationRemez` (≈470 lines): sharp Lagrange value and derivative extrapolation; Remez sublevel bound in a monotone chart.
  - `RHTower/RiemannKernelCuspSeries` (≈560): `Φ = S_{4π²X²−6πX}` as the cusp series `Σ_n e^{u/2}R(n²e^{2u})e^{−πn²e^{2u}}`; `S_R' = S_{DR}`; parity; decay; transforms; radical; linear independence of `P_k = D^kR₀`.
  - `RHTower/CuspSeriesBulkTailBounds` (≈600): weighted tail bound `M·28k(16e)^kY₀²e^{−πY₀}e^{−u}` and bulk bound `∫S_R² ≥ M²e^{−πY₀/2}/(176(8e)^{2k})`.
  - `RHTower/TruncatedRiemannKernelWeilEnergy` (≈760): cutoff, truncated tests, Weil-energy bound, and the tail and bulk bounds in terms of bulk maxima.
  - `RHTower/WeilNearRadicalDimension` (≈330): ratio, linear algebra (rank–nullity, injectivity), final theorem.
- **Verdict: BRIDGE → new theorem.**
  - The phenomenon was observed and explained heuristically by Connes–Consani (2021) and CCM (2025), and fitted empirically by Zhu (2026). No proof of the count or the margin existed. L30 gave a single vector.
  - Consequence for HF: every certificate `W ≥ η‖f‖²` with `η > exp(−e^{2a−2})` on a subspace `U` has `U ∩ V = 0`, so `U` misses at least `e^{2a−2}/20` dimensions.
  - Any producer of Hodge(a) must therefore certify positivity on a `≳ e^{2a}`-dimensional block where the form is `exp(−e^{2a})`-degenerate. Finite-rank-correction producers and CCM's (S2) (ground state isolated from the rest) face this whole block, not one vector.
- **Open (sharp form).** The count is `(2−O(η))e^{2a}` at margin `exp(−ηe^{2a})` (prolate/Landau–Widom). Polynomial multipliers cap at `(π/2)e^{2a}`; reaching `2e^{2a}` needs square phase-space concentration (prolates or Gabor boxes).
- **L34 result [L]: cluster-robust Nyquist exclusion.** Six modules, wired (five in `RHTower.lean` after `HodgeNyquistExclusion`, one in `HTGeometry.lean`). Built with `lake build`; axioms propext, Classical.choice, Quot.sound. The remaining lint errors belong to other, unwired modules.
  - `HTGeometry/ExponentialLagrangeContour` (285 lines).
    - `sum_expNodalWeight_inside_eq_rectangleIntegral`: barycentric interpolation in `w = e^{iκz}` as a `z`-plane rectangle contour. The residue of `iκe^{iκt}/(e^{iκt}−ω)` is computed through `dslope`.
    - `norm_coeff_le_of_forall_real`: the coefficients are bounded by the supremum on the circle.
  - `RHTower/CompositeResolventDivision` (418 lines).
    - `multiResolvent_spec`: division by a finite divisor. `multiResolvent_tail`: the tail bound `2^{Σm}`, independent of the geometry.
    - `multiResolvent_two_step`, `resolvent_pair_calculus`: two derivatives.
    - `expPolyShiftOp`: a shift operator with symbol `Q(e^{iκz})`.
  - `RHTower/XiWindowQuotient` (519 lines).
    - `card_windowCopySet_le`: the window of multiplicity copies has `O(log t₀)` elements.
    - `norm_logDeriv_xi_sub_window_le`: `|ξ'/ξ − Σ_V (s−ρ)⁻¹| ≤ C log t₀`, with no distance hypothesis.
    - `abs_log_windowQuotient_sub_le`: Lipschitz bound. `log_norm_windowQuotient_anchor_ge`: the anchor at `Re s = 2`.
  - `RHTower/ClusterNodeFrame` (296 lines).
    - Node set and node divisor with the multiplicities of the `ξ`-divisor. `riemannXiHat_local_factor`: the local factor of `Ξ` of exactly the divisor order.
    - `prod_norm_sub_ge_on_frame`: frame products are `≥ (δ₀/(16e))^N`. `prod_windowCopySet_conj`: reflection with multiplicity.
  - `RHTower/ClusterInterpolationContour` (1195 lines).
    - `ClusterSetup` with forward-difference selection (`exists_clusterSetup`).
    - `Lh_le_norm_Khat`: `|K̂| ≥ e^{L(t₀)}(δ₀/16e)^N` on both frames, by zero-free paths of length `≤ 3` plus symmetry.
    - `one_le_norm_polarSymbol`: `|P| ≥ 1` for the adapted polar shift `(2k+1)π/t₀`.
    - `norm_Q_eval_le`: the interpolant is at most `2·3^N·Mb` on `ℝ`.
  - `RHTower/HodgeClusterNyquistExclusion` (1072 lines).
    - `re_W_le_nodes_add`: finitely many nodes against the rest. `re_summand_node_le`: each node contributes `≤ −m(1−2η−η²)`.
    - `cluster_inequality`.
    - **`hodgeIndex_excludes_clustered_zero`** (product form) and **`hodgeIndex_cluster_nyquist_horizon`** (logarithmic form).
- **Theorem (L34).** Assume Hodge(a) with `a ≥ 1`, and let `ρ₀ = β₀+it₀` have `β₀ > ½`, `t₀ ≥ 101`, and `6+3N ≤ 2πe^{2X}`, where `X = a−3/8` and `N` is the number of window zeros with multiplicity. Then
  `πe^{2X} ≤ π(t₀+1)/2 + 2log(N+1) + 2L_N + a/2 + 2log(t₀+3) + (5+3N)X + log(K₀2^N B_N)`,
  where `L_N = log32 + N log3 + N log(32(N+1)) + 2N log(16e/δ₀) + 2 + N log5 + 3C log t₀ − log δ₀`.
  - With `N = O(log t₀)` the right side is `πt₀/2 + O(log t₀(log log t₀ + log(1/δ₀)) + a log t₀)`.
  - So the level-`a` Hodge index excludes every off-line zero below `2e^{2a−3/4} − O(log t₀·(log log t₀ + log 1/δ₀))`, uniformly in clustering.
- **Paper proof (outline, all steps formalized).**
  1. Selection. Choose `X ∈ [½,¾]` and `y₀ ∈ [δ₀/4, δ₀/2]` by forward differences. Every sub-product of the window divisor on the frame of the rectangles `[t₀±X]×±[y₀,1]` is then `≥ (δ₀/16e)^N`.
  2. Nodes. The nodes are the zeros inside the rectangles. Divide `Φ` by the node divisor to get `K = D_LΦ`, with `K̂ = Ξ/Π(z−γ)^m`. This is holomorphic and zero-free on the closed rectangles.
  3. Frame bound. `|K̂| = |ξ/P_V|·Π_{non-node window zeros}|t−γ|`. `log|ξ/P_V|` is `C log t₀`-Lipschitz on zero-free segments of total length `≤ 3` to `Re s = 2`, where it is `≥ −πτ/4 − 2 − N log 5`.
  4. Interpolant. Let `Q` interpolate `±i/(PK̂)` at `e^{iκγ}`. By the exponential contour on the two rectangles, `|Q(e^{iκx})| ≤ 2·3^N·Mb` on `ℝ`, so the coefficients are `≤ Mq`.
  5. Test. The test `f = N_Q P_s(χK)` is `C²`, supported in `[−a,a]`, and vanishes at `±i/2`. Its transform is `±i − Y` at the nodes and `−Y` at every other zero, with `|Y| ≤ 6Σ|c_k|·tail(K)`.
  6. Contradiction. The node block is `≤ −3/8` once `η ≤ ¼`. Hodge positivity then forces `1 ≤ η(4 + 14S_Z e^{a/2}N₁₂)`, and `tail(K) ≤ 2^N·tail_Φ(a−3/8) ≤ exp(−πe^{2a−3/4}+O(Na))`.
- **Verdict (L34).** PROVED. The level-`a` Hodge index for `ζ` is at least RH up to height `≍ 2e^{2a−3/4}`, with only polylogarithmic losses and no separation hypothesis.
  - This removes the "super-tight cluster" and "density/crowding mask" caveats of L28–L32 inside the Nyquist regime.
  - Novelty: CCM Cor. 3.8 (arXiv 2511.22755) is the limit statement `lim μ = 0 ⇒ RH`. No finite-height version appears in the literature (checked: 2511.22755, 2511.23257, 2605.20224, 2606.09096, 2608.24827).
- **Producer consequence.** A producer of level-`a` positivity is a proof of RH up to `2e^{2a−3/4}` (MUST-481). Combined with L33, the finite-level problem sits between RH to `≍ e^{2a}` and RH to `exp(O(e^a))`. That window is the "blind zone", where HF-F29 counts deep pairs of the other cycle.

### L35 — Spectral separation at finite level: off-line zeros below Nyquist create eigenvalues `≤ −e^{−(π/2)t}` (in progress)
- **Context.** CCM (arXiv 2511.22755, Cor. 3.8) proves only the limit statement `lim_λ μ_λ = 0 ⇒ RH`. HF-F30 (other cycle) shows that `≍ e^{2a}` eigenvalues of the level-`a` Weil form lie within `exp(−e^{2a−2})` of `0`, unconditionally. HF-F29 shows the negative index counts off-line pairs.
- **Conjecture (spectral separation law).** Let `μ(a)` be the bottom of the polar-constrained level-`a` Weil form (relative to `∫|f|²`).
  - For every zero `β₀+it₀` with `β₀ > ½`, `t₀ ≥ 101`: either `πe^{2a−3/4} ≤ π(t₀+1)/2 + O(polylog)` (the zero is above Nyquist), or `μ(a) ≤ −exp(−π(t₀+1)/2 − O(polylog))`.
  - Equivalently, `μ(a) ≥ −η` excludes all off-line zeros below `min(2e^{2a−3/4}, (2/π)log(1/η)) − O(log t(log log t + log 1/δ))`.
  - So the spectrum near `0` splits in two: the near-radical cluster `|μ| ≤ exp(−e^{2a−2})` (`≍ e^{2a}` eigenvalues), and one eigenvalue `≤ −e^{−πt/2}` per off-line zero at height `t` below Nyquist. Nothing lies in between, up to the blind zone.
- **Why a producer needs it.** A producer must deliver `μ(a) ≥ −o(1)`. This law says what "almost positive" certifies: `μ(a) ≥ −η` is RH up to height `(2/π)log(1/η)`. It is the height-resolved form of CCM's criterion, and it quantifies how numerical lower bounds on `μ(a)` translate into zero-free heights.
- **Kill attempts.**
  - *False?* No shape contradicts it. The L34 node test has `Re W ≤ −3/8` and `∫|f|² ≲ e^{π(t₀+1)/2+polylog}`.
  - *Circular?* No. The input is the L34 test plus an `L²` bound `∫|f|² ≤ 2a(‖f‖₁+‖f''‖₁)²`.
  - *Rediscovered?* Bombieri 2000 and CCM have no heights. 2608.24827 has certified `λ_min` bounds only at `L ≤ 0.8`, with no zero statement.
  - *Insignificant?* It is a receiver in quantitative form. It turns the CCM program's numerical object `μ(a)` into zero-free heights, and it supplies the missing half of the spectral picture next to HF-F30.
  - Verdict: SURVIVES PRELIMINARY ATTACK.

### L36 — Krein pinning law: every positive completion of the level-`a` Weil form is the zero measure of ζ below height `≍ e^{2a}` (in progress)
- **Context.**
  - HF's level-wise producer object is a positive Krein completion: a positive measure `ν` with `∫|f̂|²dν = W(f,f)` on the level-`a` Hodge class. It exists iff Hodge(a).
  - The corpus has the global statement: a nonnegative theta-null Schwartz form has a unique spectral measure, supported on the real Ξ divisor (`HedenmalmUniversalPositiveFormClassification`).
  - At finite level the extension problem is indeterminate, so no uniqueness is known there.
- **Literature (checked 2026-09-27).**
  - Suzuki (arXiv 2206.03682, 2606.09096; screw function, de Branges spaces) conjectures a zero operator as the `a → ∞` limit of finite-interval realizations. No quantitative pinning of extensions.
  - CC, CCM, Zhu: numerics only.
- **Conjecture (bold).** There are `c, c' > 0` such that, for all large `a`, every positive measure `ν` dominated by the level-`a` Weil form on the Hodge class (`∫|f̂|²dν ≤ |W(f,f)|`) satisfies:
  - **(P1)** `ν(I) ≤ exp(−c e^{2a})` for every interval `I ⊂ [−c'e^{2a}, c'e^{2a}]` at distance `≥ δ` from all zero ordinates, with `δ ≥ e^{−c e^{2a}/log}`;
  - **(P2)** for an exact representation `ν`, `|ν(B(γ,r)) − m_γ| ≤ exp(−c e^{2a})` at every isolated on-line zero below `c'e^{2a}`.
  - Hence every producer of Hodge(a) is a spectral realization of the zeros below the Nyquist-scale height, to super-exponential precision.
- **Mechanism.**
  - This is a Christoffel-function bound. The modulated radical test `f_ω = Φ_{≤a−1/4} ⋆ (∂²−¼)(κe^{−iω·})` has transform `Φ̂_core·(−z²−¼)κ̂(z−ω)`: polar-free, radical, and localized at `ω`.
  - Take `ω = τ₀`. Then `ν(I)·min_I|f̂_ω|² ≤ |W(f_ω,f_ω)| ≤ poly·e^{−πe^{2a−1/2}}`, while `|f̂_ω| ≳ |Ξ(τ₀)| ≳ e^{−πτ₀/2}·exp(−C log τ₀/δ)`. This uses the lossy Gamma bound and the corpus lower bound for `|ζ|` along a horizontal path.
  - (P2) uses the resolvent division `D_γ` (`ResolventDivisionDecay`).
- **L35 result [L]: spectral separation.** Module `RHTower/WeilFloorSpectralSeparation`, wired after `HodgeClusterNyquistExclusion`; built; axioms propext/choice/Quot.sound.
  - `WeilFloorAtLevel Z a η` means `μ(a) ≥ −η`: `Re W(f,f) ≥ −η∫|f|²` on polar-constrained `C²` tests in `[−a,a]`.
  - `norm_le_of_contDiff_two_supp`: `sup|f| ≤ 2a‖f''‖₁`. `integral_norm_sq_le`: `∫|f|² ≤ 2a‖f''‖₁‖f‖₁`.
  - `cluster_floor_inequality`: `1 ≤ η_t(4 + 14S_Z e^{a/2}B') + 6aηB'²`.
  - **`weilFloor_excludes_clustered_zero`** (product form) and **`weilFloor_spectral_separation`** (logarithmic form). Under `μ(a) ≥ −η`, every zero with `β₀ > ½`, `t₀ ≥ 101`, and `6+3N ≤ 2πe^{2X}` satisfies one of:
    - `πe^{2X} ≤ π(t₀+1)/2 + 2log(N+1) + 2L + a/2 + 2log(t₀+3) + (5+3N)X + log(2K₀2^N B)`, or
    - `log(1/η) ≤ π(t₀+1)/2 + 2log(N+1) + 2L + 4log(t₀+3) + 2log B + log(2K₁a)`.
- **Verdict (L35).** PROVED.
  - An off-line zero at height `t` below `≈2e^{2a−3/4}` produces an eigenvalue `≤ −e^{−πt/2−O(log t(log log t + log 1/δ) + log a)}`, whatever the configuration of nearby zeros.
  - With HF-F30, the spectrum near `0` separates into the near-radical cluster (`≍e^{2a}` eigenvalues, `|μ| ≤ exp(−e^{2a−2})`) and one eigenvalue `≤ −e^{−πt/2}` per off-line zero below Nyquist.
  - CCM's `lim μ = 0 ⇒ RH` becomes height-resolved: `μ(a) ≥ −η ⇒` RH below `min(2e^{2a−3/4}, (2/π)log(1/η)) − polylog`.
- **Next (L36): producer side.** From the L35 exploration: on the near radical, the radical identity reduces `Q(χ(Φ⋆ψ))` to `Q` of the tail. The tail is a two-bump function of width `≍e^{−2a}` at `±(a−1/8)`. Its self-correlation avoids every `log n`, and the cross term meets only the prime powers near `e^{2a−1/4}`.
  - So the archimedean `log|τ|` symbol should make `Q ≥ 0` there, unconditionally.
  - Candidate unconditional producer class: Weil positivity on thin tests whose autocorrelation support avoids the prime logarithms.

### L37 — Nyquist inertia law: below Nyquist, every off-line zero is its own negative square (in progress)
- **Context.**
  - HF-F29 (`zeta_weil_inertia_law`) gives two bounds on the `ε`-negative index of the level-`a` Weil form.
    - Upper: at most the off-line pairs below `exp(O(e^a) + O(log 1/ε))`.
    - Lower: at least `|T| − 2`, but only for zeros that are deep (`β ≥ ½ + δ`), isolated at radius `R` from other off-line zeros, and below the visibility height `exp(e^{2δa − O(log a)})`.
  - The lower bound misses three cases:
    - shallow zeros (for `δ ≲ log a / a` the visibility height is below `e^{2a}`);
    - clusters;
    - the two polar constraints.
  - L34/L35 give one negative direction per zero, with no configuration hypothesis. They say nothing about how several zeros interact.
- **Conjecture (Nyquist inertia law).** There are absolute `K₀, K₁` with the following property. Let `a ≥ 1`, and let `T` be a finite set of zeros with `β > ½`, `t ≥ 101`, and pairwise `|t_ρ − t_σ| ≥ 3/2`.
  - Suppose `K₀·|T|·e^{a/2}·Λ²·τ ≤ 1`. Here `Λ` bounds the per-zero size `2^N B_N (N+1) M_{t,δ,N} (t+3)²` of the L34 test, and `τ` bounds its tail `e^{(5+3N)X − πe^{2X}}`.
  - Then the `1/(K₁ a |T| Λ²)`-negative index of the level-`a` Weil form is `≥ |T|`.
  - The loss relative to L34 is `log|T|`, in logarithmic form. There is no isolation, no depth-dependent visibility and no `−2`: each cluster test is polar-free by construction.
- **Consequence.** The HF-F29 upper bound and this law sandwich the negative index. Between the Nyquist height `≈ 2e^{2a}` and the archimedean horizon `exp(O(e^a))` lies the blind zone. Below Nyquist, the negative index of the finite-level Weil form counts separated off-line zeros exactly, at any depth and in any configuration.
- **Kill attempts.**
  - *False?* The Gram matrix of the cluster tests is diagonally dominant. Test `j` has transform `±i` at its own nodes and `≤ η_j` at every other zero. Disjoint reflect-closed node sets make each cross summand `≤ m(η_j E_k + η_k E_j)/(1+|t|)²`. No shape contradicts it.
  - *Circular?* No. It is a Gram argument on unconditional tests.
  - *Rediscovered?* Weil and Bombieri (2000): the full index counts off-line zeros (no level). Yoshida (1992): positivity on small support. HF-F29: margins as above. None gives a finite-level lower bound for clusters.
  - *Insignificant?* It is receiver-side. Its value is structural: below Nyquist, the finite-level Weil form is exactly the zero trace form. Any producer at level `a` must certify an index of `0`, which is RH below Nyquist, zero by zero and with no averaging.
  - Verdict: SURVIVES PRELIMINARY ATTACK.
- **Paper proof.**
  1. For each `ρ ∈ T` take the L34 cluster setup at `t_ρ`. Its nodes lie in `|Im − t_ρ| < 3/4`, so the node sets are pairwise disjoint and reflect-closed.
  2. Diagonal: `Re W(f_ρ,f_ρ) ≤ −3/8 + 5S_Z η_ρ e^{a/2} B'_ρ` when `η_ρ ≤ ¼` (the L34 node block).
  3. Cross terms: `|W(f_ρ,f_σ)| ≤ (5/4)S_Z(η_ρE_σ + η_σE_ρ)`, where `E = e^{a/2}·4(‖f‖₁+‖f''‖₁)`. Each zero is off the nodes of `f_ρ` or of `f_σ`, and so is its reflection.
  4. Gram: `Re W(Σc f) ≤ (−3/8 + D + (|T|−1)O)‖c‖² ≤ −¼‖c‖²`, and `∫|Σc f|² ≤ |T|‖c‖² max∫|f|² ≤ |T|‖c‖²·2aB'²`.
  5. So the synthesis map is injective and its range is `|T|`-dimensional, polar-free, supported in `[−a,a]`, and `ε`-negative. Conclude with `le_csSup`, with bounded-above from the HF-F29 upper bound.

### L36 result — Positive completions are pinned to the zeros below `≈ e^{2L−1/2}`. TRUE [L] for (P1); (P2) open
- **Theorem** (`RHTower/KreinCompletionPinning:zeta_krein_completion_pinned_off_zeros`; unconditional; axioms propext/choice/Quot.sound).
  - There are `K > 0` and `L₀` such that, for `L ≥ L₀`, every positive measure `ν` with `∫|f̂|²dν ≤ |W(f,f)|` on the level-`L` Hodge class satisfies `ν([τ₀−δ/2, τ₀+δ/2]) ≤ K e^{12L} e^{−πe^{2L−1/2}}`.
  - Conditions: `τ₀ ≥ 5` is at distance `≥ δ` from every zero ordinate (`0 < δ ≤ 1`), and `π(τ₀+½) + 6C log(τ₀+1)/δ ≤ πe^{2L−1/2}`, where `C` is the corpus `ζ'/ζ` constant.
  - Every positive Krein completion of the level-`L` Weil form is such a `ν`, and the RH zero measure is one of them.
  - So below height `≈ e^{2L−1/2}` a positive completion is super-exponentially close to being supported on the zero ordinates. In the indeterminate extension problem, positivity forces the spectrum.
- **Proof.** A Christoffel-function bound, using the modulated radical test `f_{L,τ₀} = Φ_{≤L−¼} ⋆ (κe^{−iτ₀·})₂` (`RHTower/ModulatedRiemannRadicalTest`).
  - The test is polar-free and radical, with transform `Φ̂_core(z)(−z²−¼)κ̂(z−τ₀)`.
  - `W(f,f) ≤ ε_L²C_κ²(1+τ₀)⁴·24A₀log(τ₀+3)`. Both evaluation points see only the tail, and there is fourth-order bump decay.
  - On the window, `|f̂| ≥ (|Ξ| − ε_L)(τ²+¼)cos(⅛)∫κ`. Also `|Ξ(τ)| ≥ c_Ξτ²e^{−πτ/2}exp(−(3/2)C log τ/δ)`, from the duplication-lossy Gamma bound and the `|ζ|` horizontal-path bound.
- **Modules.** `RHTower/ModulatedRiemannRadicalTest` (≈510 lines) and `RHTower/KreinCompletionPinning` (≈450 lines). Both are wired and built with `lake build --old`, and lint is clean for these modules.
- **Verdict.** New theorem, a rigidity law for the producer object of HF.
  - The corpus global version (`HedenmalmUniversalPositiveFormClassification`: a theta-null form has a unique spectral measure on the real Ξ divisor) is the `L = ∞` shadow. L36 is its quantitative finite-level form.
  - Literature: Suzuki (screw/de Branges) conjectures limits but gives no finite-level pinning; CC/CCM/Zhu are numerical.
- **Route consequence (HF).**
  - Any producer of a positive Krein completion at level `L` must place its spectral mass on the zero ordinates of ζ below `≈ e^{2L}`, to precision `exp(−πe^{2L−1/2})`.
  - So a producer is a finite-level spectral realization of the zeros below the Nyquist-scale height.
  - Together with HF-F31 (Hodge(a) ⇒ RH up to `≍e^{2a}`): positivity at level `L` is at least RH to height `e^{2L}`, and its witness measure is the zero measure there.
- **Open (P2).** Masses: `ν(B(γ,r)) = m_γ + tiny` at isolated on-line zeros.
  - The upper half should follow from the resolvent-divided test `D_γΦ`.
  - The lower half needs `ν` controlled super-close to every other zero. Polynomial bump decay (`κ̂`) is too weak at low frequencies, where `|Ξ|` is large, so a new idea is needed.
- **L37 result [L]: Nyquist inertia law.** Module `RHTower/WeilNyquistInertia`, wired after `WeilFloorSpectralSeparation`. Checked with `lake env lean`; axioms propext/choice/Quot.sound.
  - `norm_W_le_of_split`: if `f̂` is `≤ η_f` off a set `F` of zeros and `ĝ(conj γ)` is `≤ η_g` on `F`, then `‖W(f,g)‖ ≤ (5/4)S_Z(η_f E_g + η_g E_f)`.
  - `exists_negative_subspace_of_gram`: a diagonally dominant Weil Gram matrix of polar-constrained tests (`Re W_ii ≤ −3/8 + D`, `‖W_ij‖ ≤ O`, `D + (n−1)O ≤ 1/8`) gives an `n`-dimensional `ε`-negative subspace, for `εn·max∫|f_i|² ≤ 1/8`.
  - Cluster pieces:
    - `ClusterSetup.re_W_test_le` (diagonal);
    - `norm_W_cluster_tests_le` (cross terms; node sets are disjoint for heights `3/2` apart, and closed under reflection);
    - `testTail_le`, `normBound_le`, `size_bounds` (explicit sizes);
    - `exists_clusterSetup_node`.
  - **`weilNegIndex_ge_card_offline_zeros`.** There are absolute `K₀, K₁` with the following property. Let `T` be a set of zeros with `β > ½`, `t ≥ 101`, ordinates pairwise `≥ 3/2` apart, each satisfying `6+3N ≤ 2πe^{2X}`, with `nyquistSize ≤ Λ` and `nyquistTail ≤ τ`. If `K₀|T|e^{a/2}Λ²τ ≤ 1`, then `|T| ≤ weilNegIndex ζ a (1/(K₁ a|T|Λ²))`.
- **Verdict (L37).** PROVED.
  - Below Nyquist, every off-line zero is a negative square of the level-`a` Weil form, at any depth and in any configuration (separated ordinates only).
  - The loss is `log|T|` in the horizon. No isolation, no `−2`, and no depth-dependent visibility enter.
  - With the HF-F29 upper bound: `#{3/2-separated off-line zeros below 2e^{2a−3/4} − polylog − (2/π)log|T|} ≤ index(a, ε) ≤ #{off-line pairs below exp(O(e^a) + O(log 1/ε))}`.
- **Producer consequence.** A level-`a` producer certifies index `0`. This is not "RH on average": each separated off-line zero below Nyquist independently forces its own negative direction.
  - So the finite-level form offers no cancellation between zeros that a producer could exploit.
  - Any producer at level `a` is a zero-by-zero certificate of RH below `≈2e^{2a}`.

### L38 — Landau-sharp Krein pinning: positive completions are pinned up to height `(1−η)·2πe^{2L}` (in progress)
- **Context.**
  - L36 (HF-F33) pins positive completions below `≈ e^{2L−1/2}`. Its method is limited to `≈ 4e^{2L}`, because cutting `Φ` at `L` leaves an artifact of size `e^{−πe^{2L}}`, while `|Ξ(τ)| ≍ e^{−πτ/4}`.
  - The Landau heuristic says the pinning height should be `2πe^{2L}`, where the zero density `(1/2π)log(τ/2π)` equals the Nyquist rate `L/π` of tests supported in `[−L, L]`.
  - This is also Connes–Consani's natural scale `2πλ²` (arXiv 2106.01715, Prop. 4.2). There it appears only as a heuristic eigenvalue-count match for their spectral triple, not as a theorem.
- **Conjecture (bold).** For every `η ∈ (0, ½]` there is `L₀` such that, for all `L ≥ L₀` and every positive measure `ν` dominated by the level-`L` Hodge form: `ν([τ₀ ± δ/2]) ≤ exp(−(π/2)η^{3/2}e^{2L})`.
  - Conditions: `5 ≤ τ₀ ≤ (1−η)·2πe^{2L}`, `τ₀` is at distance `≥ δ` from all zero ordinates, and `12C log(τ₀+1)/δ ≤ (π/2)η^{3/2}e^{2L}`.
  - Sharpness (heuristic, under RH): above `(1+η)·2πe^{2L}` the ordinates oversample `PW_L`, so the Christoffel function of the zero measure is `≳ 1` and no pinning holds. The constant `2π` is therefore exact.
- **Mechanism (new tool: tilted radical kernels).**
  - `Φ_θ(u) = Φ_ℂ(u + iθ)` is the horizontal slice of the complexified theta source at height `θ < π/4`.
  - A contour shift gives `Φ̂_θ(z) = e^{zθ}Ξ(z)`. So `Φ_θ` is exactly radical, and the tilt `e^{τθ}` cancels `Ξ`'s decay: `e^{τθ}|Ξ(τ)| ≍ e^{−(π/4−θ)τ}`.
  - `Φ_θ` still decays like `e^{−π cos(2θ) e^{2|u|}}`.
  - With `θ = π/4 − ε`: the cut artifact is `e^{−π sin(2ε)e^{2L}}` against a signal of `e^{−ετ₀}`, so the ratio is small iff `τ₀ < 2πe^{2L}·(sin 2ε/2ε)`.
  - This needs the sharp quarter-line Gamma bound `|Γ(¼ + iτ/2)| ≥ e^{−πτ/4}/(1+τ)`, from duplication plus the digamma ratio `|Γ(¾+iy)/Γ(¼+iy)| ≤ e(1+y)`. The corpus bound `e^{−πτ/2}` is too weak.
- **Kill attempts.**
  - *False?* No: the mechanism is explicit below the threshold, and sampling blocks it above.
  - *Circular?* No: it is a Christoffel bound on an explicit Hodge-class test.
  - *Rediscovered?* CC give the scale `2πλ²` only heuristically, as a count match. There is no finite-level Krein pinning in the literature (Suzuki 2206.03682/2606.09096, CC, CCM 2511.22755). The corpus L36 reaches `0.61e^{2L}`. Tilted theta slices appear classically (Pólya, de Bruijn), but not as finite-level radical tests.
  - *Insignificant?* It gives the exact threshold. It identifies the pinning height with the Landau height where the zero density equals the Nyquist rate. So a positive completion at level `L` determines the zeros up to exactly `2πe^{2L}`.
  - Verdict: SURVIVES PRELIMINARY ATTACK.
- **Paper proof.** Take `ε = √η/2`, `θ = π/4 − ε`, `w = η/8`, `U = L − w`, and let `κ_w(u) = κ(u/4w)` be the scaled bump. Take the test `T = (Φ_θ·1_{[−U,U]}) ⋆ (κ_{w,τ₀}'' − κ_{w,τ₀}/4)`. It is `C²`, supported in `[−L, L]`, and polar-free.
  1. At every zero, `T̂ = −Φ̂_{θ,>U}·κ̂₂`, so `‖W(T,T)‖ ≤ ε_U²·C_κ²(4w)^{−6}(1+τ₀)⁴·24A₀log(τ₀+3)`.
  2. The tail satisfies `ε_U ≤ 2M_θe^{5U}e^{−π sin(2ε)e^{2U}}`, using the per-term strip bound and evenness.
  3. On the window, `|T̂| ≥ (e^{τθ}|Ξ(τ)| − ε_U)(τ²+¼)·4w cos(⅛)∫κ`. Also `e^{τθ}|Ξ(τ)| ≥ c τ²e^{−ετ}/(1+τ)·(1/3)e^{−(3/2)C log τ/δ'}`, using the sharp Gamma bound and the `|ζ|` path bound.
  4. Exponent: `sin 2ε ≥ 2ε(1−ε²)` and `e^{−2w} ≥ 1−2w` give `−2π sin(2ε)e^{2U} + 2ετ₀ ≤ −4πεe^{2L}[(1−ε²)(1−2w) − (1−η)] ≤ −πη^{3/2}e^{2L}`.

### L39 — Landau-sharp cluster exclusion: `Hodge(a)` excludes every off-line zero below `(π sin 2ε/ε)·e^{2a−3/4}`, which tends to `2π·e^{2a−3/4}` (in progress)
(Label L39: the parallel cycle's L38 is the tilted-kernel Krein pinning. Its module `TiltedRiemannKernel` is this cycle's input.)
- **Context.**
  - L34 (HF-F31) excludes clustered off-line zeros below `2e^{2X}`, `X = a − 3/8`. The constant 2 has two sources:
    - `|Ξ(τ)| ≍ e^{−πτ/4}` makes the interpolant `e^{πt/4}` large;
    - the positive remainder of the off-node zeros is bounded by `η·‖f‖`, and `‖f‖` contains the interpolant a second time.
  - The Landau density heuristic puts the exact threshold at `2π·e^{2X}`.
- **Conjecture.** Let `0 ≤ θ < π/4` and `ε = π/4 − θ`. `Hodge(a)` excludes every zero with `β > ½`, `t ≥ 101`, whenever
  `π cos(2θ) e^{2X} > ε t + O(N(log N + log 1/δ) + log t + N X)`.
  - At `θ = 0` the horizon is `4e^{2X}`, twice L34's.
  - As `θ → π/4` it is `(π sin 2ε/ε)e^{2X} → 2πe^{2X}`.
- **Mechanism.**
  1. *Tilt only the kernel.* Keep L34's cluster setup and its untilted interpolant `Q`, with `QPK̂ = ±i` at the nodes. Replace `K = D_LΦ` by `K_θ = D_LΦ_θ`. Since `Φ̂_θ = e^{θz}Ξ`, we get `K̂_θ = e^{θz}K̂`, so at a node the test's transform is `e^{θγ}·(±i) − Y`.
  2. *Node block.* For a node `ν` and its reflection, `(e^{θγ}X)·conj(e^{θγ̄}X') = −e^{2θγ}`. Its real part is `≤ −e^{2θ Re γ}cos(2θ Im γ) ≤ −(2/3)e^{2θ Re γ}`, because `|2θ Im γ| < π/4`.
  3. *Refined off-node remainder.* At an off-node zero the transform is `−Q P·tail_θ^(γ)`. The tail `(1−χ)K_θ` is `C²`, and `tail''` is built from `K_θ, k₁, k₂` on `|u| ≥ X`. So `(1+|t|)²|tail^(γ)| ≤ T`, where `T` is tail-sized. Both factors of every off-node summand are therefore `≤ 6c_M T/(1+|t|)²`, and the whole off-node sum is `≤ 45 S_Z c_M² T²`. The test norm `‖f‖` never enters.
  4. *Balance.* `(3/8)e^{2θ(t−3/4)} ≤ 45 S_Z c_M² T² ⇒ e^{θ(t−3/4)} ≲ c_M T`. Here `c_M ≍ e^{π(t+1)/4}·polylog` and `T ≍ poly·e^{O(NX)}·e^{−π cos(2θ)e^{2X}}`. This gives the conjectured horizon.
- **Kill attempts.**
  - *False?* Every factor is explicit. Only the single-factor balance `e^{εt} ≷ e^{−π cos 2θ e^{2X}}` enters, and at `θ → π/4` it is exactly the Landau count `2πe^{2X}`. Above that height the zeros oversample `PW_a`, so no pinning or exclusion is expected (the parallel L38 heuristic).
  - *Circular?* No. The inputs are L34's unconditional setup, the tilted kernel identity, and tail bounds.
  - *Rediscovered?* Finite-level exclusion exists only in this corpus (L34). Tilted slices of `Φ` are classical (Pólya, de Bruijn, Hardy), but not as finite-level radical tests; the parallel cycle uses them only for pinning.
  - *Insignificant?* It fixes the constant of the Nyquist law at the Landau value. So: `Hodge(a) ⇒` RH up to `(2π − o(1))e^{2a−3/4}`. At `θ = 0` alone the refined remainder already doubles L34's horizon.
  - Verdict: SURVIVES PRELIMINARY ATTACK.
- **Paper proof.**
  1. The input from `TiltedRiemannKernel` is `paperFT Φ_θ = e^{zθ}Ξ` on `|Im z| ≤ ½`, with double-exponential decay. Hence `Φ_θ` is SuperExpDecay, and `DivisorData L Φ_θ` holds with local factor `e^{zθ}u(z)`.
  2. `K̂_θ·P_L = e^{θz}Ξ = e^{θz}K̂·P_L`, so `K̂_θ = e^{θz}K̂` off the nodes. It also holds at the nodes by continuity, since the node set is finite.
  3. Write `K_θ = D_aD_bg₂` (two outer divisions). Then `k₁ = −iaK_θ − i·D_bg₂`, `p₁ = −ib·D_bg₂ − ig₂`, `k₂ = −iak₁ − ip₁`. Each tail is `≤ (1+Γ)^j·2^N·tail_{Φ_θ}(½ + 3N/2, X)`.
  4. Put `tail = (1−p)K_θ`, so `tail'' = −p₂K_θ − 2p₁k₁ + (1−p)k₂`. This vanishes on `|u| < X`, and `|p_j| ≤ Kp`. Two integrations by parts (`paperFT_deriv_of_superExpDecay`) give `|z|²|tail^(z)| ≤ Kp(tail_K + 2tail_{k₁}) + tail_{k₂}` on `|Im z| ≤ ½`.
  5. Node block `≤ −(3/8)e^{2θ(t₀−3/4)}`, provided `6c_M·tail_K ≤ e^{θ(t₀−3/4)}/8`. The off-node sum is `≤ 45S_Z c_M²T²`. Hodge then forces `e^{θ(t₀−3/4)} ≤ max(48, 11√(S_Z+1))·c_M T`.
  6. Tail of `Φ_θ` with weight `c`: `∫_{|u|>X}‖Φ_θ‖e^{c|u|} ≤ 2M e^{(c+11/2)X}e^{−π cos(2θ)e^{2X}}` once `π cos(2θ)e^{2X} ≥ c + 11/2`. This follows from `norm_tiltedPhi_le_of_rate` and the monotonicity of `(c+11/2)u − πc₂e^{2u}`.

### L38 result — Krein pinning holds up to the Landau height `(1−η)·2πe^{2L}`. TRUE [L]
- **Theorem** (`RHTower/LandauHeightKreinPinning:zeta_krein_completion_pinned_below_landau_height`; unconditional; axioms propext/choice/Quot.sound).
  - For every `0 < η ≤ ½` there is `L₀` such that, for `L ≥ L₀`, every positive measure `ν` dominated by the level-`L` Hodge form satisfies `ν([τ₀ ± δ/2]) ≤ exp(−(π/2)η^{3/2}e^{2L})`.
  - Conditions: `5 ≤ τ₀ ≤ (1−η)·2πe^{2L}`, zero-ordinate separation `δ ∈ (0,1]`, and `12C log(τ₀+1)/δ ≤ (π/2)η^{3/2}e^{2L}`.
- **Improvement over L36.** The pinning height goes from `0.61e^{2L}` to `(1−η)·6.28e^{2L}`, and the bound is `exp(−cη^{3/2}e^{2L})` with no polynomial prefactor.
  - `2πe^{2L}` is where the zero density `(1/2π)log(τ/2π)` equals the Nyquist rate `L/π`. It is Connes–Consani's scale `2πλ²`, which they give only heuristically, as a count match (2106.01715, Prop. 4.2).
  - Sharpness (heuristic, RH plus sampling): the constant `2π` cannot be raised.
- **New tools.**
  - `RHTower/TiltedRiemannKernel`:
    - `Φ_θ(u) = Φ_ℂ(u+iθ)` has `Φ̂_θ(z) = e^{zθ}Ξ(z)` for `|Im z| ≤ ½` (`paperFT_tiltedPhi`, a contour shift in the theta strip).
    - `Φ_ℂ = Φ` on the real line (`thetaCuspStripSource_ofReal_eq`).
    - Double-exponential tail `‖Φ_θ(u)‖ ≤ M e^{9|u|/2}e^{−π cos(2θ)e^{2|u|}}` (`norm_tiltedPhi_le_of_rate`), with tail mass `2Me^{6U}e^{−π cos 2θ e^{2U}}`.
    - At zeros only the tail is seen (`paperFT_tiltedCore_at_zero`).
  - `RHTower/LandauHeightKreinPinning`:
    - Scaled bump `κ(u/4w)` with its transform bounds.
    - Tilted radical test `landauRadicalTest` (Hodge class) with its Weil bound `norm_W_landauRadicalTest_le`.
    - **Sharp quarter-line Gamma** `|Γ(¼+is/2)| ≥ e^{−πs/4}/(1+s)` (`norm_Gamma_quarter_line_sharp`, from duplication plus the digamma segment ratio `|Γ(¾+iy)| ≤ e(1+y)|Γ(¼+iy)|`). The corpus previously had only `e^{−πs/2}`.
    - Tilted Ξ line bound `e^{τθ}|Ξ(τ)| ≥ c τ²/(1+τ)·e^{(θ−π/4)τ}·e^{−(3/2)C log τ/δ}` (`tilted_xi_line_ge`).
- **Route consequence (HF).** A positive completion at level `L` is a spectral realization of the zeros exactly up to the Landau height `2πe^{2L}`, which is where the finite-level Weil data stop determining the zero set. Any producer must reproduce the zeros to precision `exp(−cη^{3/2}e^{2L})` below `(1−η)·2πe^{2L}`.
- **Next.**
  - (a) The tilted kernel should also sharpen the Nyquist exclusion (HF-F31, `2e^{2a−3/4}`) to the Landau height.
  - (b) It should give the near-radical count with CC's constant 2: dimension `≥ (2−η)e^{2L}` (HF-F30 has `e^{2L−2}/20`). Tilted tests `Φ_θ ⋆ g` with `g` localized in phase space cover the region `|u| + ½log(|τ|/2π) < L`, whose area is exactly `2·2πe^{2L}`.
- **L39 result [L]: Landau-sharp cluster exclusion.** Module `RHTower/TiltedClusterNyquistExclusion`, wired after `WeilNyquistInertia`. Checked with `lake env lean`; axioms propext/choice/Quot.sound.
  - Input: the parallel cycle's `TiltedRiemannKernel` (`tiltedPhi`, `paperFT_tiltedPhi`, `norm_tiltedPhi_le_of_rate`).
  - New general tools:
    - `superExpDecay_tiltedPhi`;
    - `paperFT_tiltedPhi_eq` (`Φ̂_θ = e^{zθ}Ξ` on all of ℂ, by the identity theorem);
    - `divisorData_nodeList_tilted`;
    - `expTail_tiltedPhi_le` (weight `c`: `≤ 2M e^{(c+11/2)X} e^{−π cos(2θ)e^{2X}}`);
    - `expTail_add_le`, `expTail_const_mul`;
    - `norm_paperFT_tailK_decay`: the discarded tail's transform decays like `(1+|t|)^{−2}` with a tail-sized constant, via `tail''` supported on `|u| ≥ X`;
    - `re_W_le_nodes_add_decay`: a quadratic remainder `(5/4)S_Z B²` when both factors decay;
    - `re_tilted_node_pair_le`, `re_neg_cexp_two_mul_le`.
  - Cluster pieces: `Kθ_spec` (`K̂_θ = e^{zθ}K̂`), `Kθ_calculus` (derivative tails `(1+Γ)^j T`), `testθ_at_node`, `testθ_off`, `tilted_cluster_inequality`.
  - **`hodgeIndex_excludes_tilted_cluster`** (product form) and **`hodgeIndex_tilted_cluster_horizon`** (log form). For every `0 ≤ θ < π/4`, Hodge(a) and a zero with `β₀ > ½`, `t₀ ≥ 101`, `6 + 3N/2 ≤ 2π cos(2θ)e^{2X}` give
    `π cos(2θ)e^{2X} ≤ (π/4 − θ)t₀ + π/4 + 3θ/4 + log(K₀2^N(N+1)) + L_N + 2log(t₀+3) + (6+3N/2)X`.
- **Verdict (L39).** PROVED.
  - The level-`a` Hodge index excludes every off-line zero below `(π sin 2ε/ε)e^{2a−3/4} − O(log t(log log t + log 1/δ) + NX)/ε`, and `π sin 2ε/ε ↑ 2π` (Landau).
  - At `θ = 0`, the quadratic remainder alone doubles L34's horizon to `4e^{2X}`.
  - Why this constant is sharp: at `2πe^{2X}` the zero density `(1/2π)log(t/2π)` reaches the Nyquist rate `X/π`. Above that, the ordinates oversample the tests' Paley–Wiener space and no interpolating test exists. This matches the parallel L38 pinning height.
- **Producer consequence.** A level-`a` producer is RH up to `(2π − o(1))e^{2a−3/4}`, exactly the Landau height, where the finite-level form stops resolving individual zeros.
  - Below it, the form is the zero trace form (L37). Above it, a sampling phenomenon takes over. So the finite-level Weil form is an RH certificate of exactly the Landau height, no more and no less (up to the blind zone of deep zeros).

### L40 — Landau-sharp spectral separation: below the Landau height, an off-line zero at height `t` forces `μ(a) ≤ −e^{−2εt}·(poly·B_θ)^{−2}` for every `ε` (in progress)
- **Context.**
  - L35 (HF-F32) gives spectral separation: `μ(a) ≥ −η` excludes off-line zeros below `min(2e^{2X}, (2/π)log(1/η))`. The eigenvalue scale `e^{−πt/2}` is the Gamma decay squared.
  - L39's tilt removes the Gamma decay down to `e^{−εt}`, and its quadratic remainder reaches the Landau height.
- **Conjecture.** Let `θ = π/4 − ε` with `ε ∈ (0, π/4]`. There are absolute `K₀, K₁` such that, under `μ(a) ≥ −η`, every zero with `β₀ > ½`, `t₀ ≥ 101`, `6 + 3N/2 ≤ 2π cos(2θ)e^{2X}` satisfies
  `e^{2θ(t₀−3/4)} ≤ K₀[2^N(N+1)M(t₀+3)²e^{(6+3N/2)X}e^{−π cos(2θ)e^{2X}}]² + K₁aη[(N+1)M(t₀+3)²B_θ]²`,
  where `B_θ = 2^N∫‖Φ_θ‖e^{3N|u|/2}`.
  - Below the Landau horizon the first term is `≤ ½e^{2θ(t₀−3/4)}`. There, `log(1/η) ≤ 2εt₀ + O(log t(log log t + log 1/δ) + log B_θ + log a)`.
  - So `μ(a) ≥ −η` certifies RH up to `min((π sin 2ε/ε)e^{2X}, (1/2ε)log(1/η))` minus polylog.
- **Why it matters (CCM interface).** CCM and Zhu compute `λ_min(L)` numerically. This says what precision certifies what height. Compared with L35, precision `η` now reaches height `(1/2ε)log(1/η)` instead of `(2/π)log(1/η)`, for every `ε > 0` (with `B_θ` growing as `ε → 0`).
- **Kill attempts.** False? No: it is the L39 node block with the floor added, and `∫|f|² ≤ 2a‖f‖₁‖f''‖₁`. Circular? No. Rediscovered? No finite-level spectral separation exists in the literature (checked for L35). Insignificant? It is the sharp quantitative form of CCM Cor. 3.8. Verdict: SURVIVES PRELIMINARY ATTACK.
- **Paper proof.**
  1. Floor: `−η∫|f|² ≤ Re W ≤ Σ_nodes + (5/4)S_Z B_d²`.
  2. If `η_t ≤ A/8`, the node block is `≤ −(3/8)A²`, so `A² ≤ (10/3)S_Z B_d² + (8/3)η∫|f|²`. Otherwise `A ≤ 4B_d`. In both cases `A² ≤ (16 + 4S_Z)B_d² + 3η∫|f|²`.
  3. `∫|f|² ≤ 2a(‖f‖₁+‖f''‖₁)²`, with `‖f‖₁+‖f''‖₁ ≤ 4Kp·Σ|c_k|(1+cosh(s/2))(t₀+3)²B_θ`. Here the derivative tails of `K_θ` at `c = 0`, `X = 0` bound `‖K_θ‖₁, ‖K_θ'‖₁, ‖K_θ''‖₁` by `(1+Γ)^j B_θ`.
- **L40 result [L]: Landau-sharp spectral separation.** Module `RHTower/TiltedWeilSpectralSeparation`, wired after `TiltedClusterNyquistExclusion`. Built with `lake build`; axioms propext/choice/Quot.sound.
  - `testθ_norm`: `‖f‖₁ + ‖f''‖₁ ≤ 4Kp Σ|c_k|(1+cosh(s/2))(t₀+3)²B_θ`.
  - `tilted_cluster_floor_inequality`: `A² ≤ (16+4S_Z)B_d² + 6aηN₁₂²`, with `A = e^{θ(t₀−3/4)}`.
  - **`weilFloor_excludes_tilted_cluster`** (product form): `e^{2θ(t₀−3/4)} ≤ K₀P_H² + K₁aηP_F²`.
  - **`weilFloor_tilted_spectral_separation`** (logarithmic form): below the Landau horizon (`2K₀P_H² ≤ e^{2θ(t₀−3/4)}`),
    `log(1/η) ≤ 2(π/4−θ)t₀ + π/2 + 3θ/2 + 2L_N + 2log(N+1) + 4log(t₀+3) + 2log B_θ + log(2K₁a)`.
- **Verdict (L40).** PROVED.
  - `μ(a) ≥ −η` certifies RH up to `min((π sin 2ε/ε)e^{2a−3/4}, (1/2ε)log(1/η))`, minus polylog terms and `log B_θ`, for every `ε ∈ (0, π/4]`.
  - Compared with L35, the eigenvalue scale improves from `e^{−πt/2}` to `e^{−2εt}·B_θ^{−2}`, and the horizon from `2e^{2X}` to Landau.
- **CCM reading.** A certified lower bound `λ_min(a) ≥ −η` verifies RH up to `≈ min(2πe^{2a−3/4}, (1/2ε)log(1/η))`.
  - The price of small `ε` is `B_θ`, the `L¹` hump of `Φ(u+iθ)` near the edge of its strip. It grows like `ε^{−O(N)}` (heuristically, from the theta modular transformation). That is not yet formal.

### L41 — Quasi-polynomial precision: `μ(a) ≥ −exp(−C log²t)` certifies RH at height `t` below `(1−o(1))·2πe^{2a−3/4}` (in progress)
- **Context.** L40 prices the tilt through `B_θ = 2^N∫‖Φ(u+iθ)‖e^{3N|u|/2}`, which is finite but not explicit. Everything else is polylogarithmic.
- **Conjecture.** With `c = cos 2θ`: `log B_θ ≤ N log 2 + log(56U/c³ + 2M) + (3N/2 + 11/2)U`, where `U = ½ log((3N/2 + 6)/c)`. So `B_θ ≤ (N/c)^{O(N)}`.
  - Take `θ = π/4 − ε` with `ε ≍ log t·(log log t + log 1/δ)/t` (polylog over `t`).
  - Then L40 gives: an off-line zero at `t ≤ (1 − O(1/log t))·2πe^{2a−3/4}` forces `μ(a) ≤ −exp(−O(log²t·(log log t + log 1/δ)))`.
- **Mechanism (hump bound).** Each term of `Φ(u+iθ)` is `≤ e^{u/2}·2π(2πn⁴x² + 3n²x)e^{−πcn²x}`, with `x = e^{2u}`.
  - Using `s²e^{−s} ≤ (16/e²)e^{−s/2}` and `se^{−s} ≤ (2/e)e^{−s/2}` (`s = πcn²x`), the sum over `n` is geometric: `Σe^{−αn²} ≤ 1 + 1/α`.
  - Hence `‖Φ(u+iθ)‖ ≤ (14/c²)(e^{u/2} + (2/πc)e^{−3u/2})`, and `≤ (28/c³)e^{3U/2}` on `|u| ≤ U`.
  - Beyond `U`, use `expTail_tiltedPhi_le`.
- **Kill attempts.** Circular? No. Known? The trivial `θ(x+iy) ≪ y^{−1/2}` bound is classical; the finite-level consequence is new. Insignificant? It turns L40's "exponential with small rate" into quasi-polynomial precision. Verdict: SURVIVES.
- **L41 result [L]: quasi-polynomial precision.** Module `RHTower/QuasiPolynomialWeilSeparation`, wired after `TiltedWeilSpectralSeparation`. Built with `lake build`; axioms propext/choice/Quot.sound.
  - `norm_tiltedPhi_le_hump`: `‖Φ(u+iθ)‖ ≤ (18/c²)(e^{u/2} + (2/πc)e^{−3u/2})`, with `c = cos 2θ`.
  - `expTail_tiltedPhi_zero_le`, `log_tiltedSize_le`: `log B_θ ≤ N log 2 + log(72U/c³ + 2M) + (3N/2+11/2)U`, where `U = ½log((3N/2+6)/c)`.
  - **`weilFloor_quasipolynomial_separation`**: below the Landau horizon,
    `log(1/η) ≤ 2(π/4−θ)t₀ + π/2 + 3θ/2 + 2L_N + 2log(N+1) + 4log(t₀+3) + 2(N log 2 + log(72U/c³+2M) + (3N/2+11/2)U) + log(2K₁a)`.
- **Verdict (L41).** PROVED.
  - Correction (checked after L42): the Landau hypothesis contains the tail term `(6+3N/2)X ≍ log²t`, which must be absorbed by `ε`. Consequences:
    - with `ε ≍ C_κ(log²t + log t log 1/δ)/t`, a floor `μ(a) ≥ −exp(−C'_κ(log²t + log t log 1/δ))` excludes every off-line zero up to `t ≤ 2πe^{2a−3/4}/(1+κ)`;
    - `(1−o(1))·2πe^{2a−3/4}` needs precision `exp(−ω(log²t))`.
  - Earlier text in this entry claiming `(1−O(1/log t))` at precision `exp(−O(log²t…))` overstated the result.
  - The finite-level Weil form is therefore a numerically well-conditioned RH certificate: quasi-polynomially many digits in `λ_min` certify RH up to the Landau height. L35 needed `≍ πt/2` digits.

### L42 — Landau-sharp inertia: below `(1−o(1))·2πe^{2a−3/4}`, every separated off-line zero is a negative square with quasi-polynomial margin (in progress)
- **Conjecture.** Let `T` be a finite set of zeros with `β > ½`, `t ≥ 101`, pairwise ordinate gaps `≥ 3/2`, each below the tilted Landau horizon with margin `log|T|`. Then `|T| ≤ weilNegIndex ζ a ε`, where `ε ≍ min_ρ e^{−2(π/4−θ)t_ρ}/(poly·B_θ²·|T|·a)`. With `ε ≍ polylog/t`, the margin is `exp(−O(log²t))`.
- **Mechanism.**
  - Use the normalized tilted tests `g_j = e^{−θ(t_j−3/4)}·testθ_j`. Their node values have modulus in `[1, e^{3θ/2}]`, so the diagonal is `≤ −3/8 + O(S_Z(B_j/A_j)²)`.
  - Cross terms split three ways: nodes of `j` against the decaying tail of `k`, nodes of `k` against the tail of `j`, and both tails. This gives `|W(g_j,g_k)| ≤ O(S_Z(B_j/A_j + B_k/A_k + B_jB_k/A_jA_k))`.
  - Finish with the Gram lemma of L37.
- **Kill attempts.** No obstruction: it is L37 with L39's tests. Verdict: SURVIVES (completion).
- **L42 result [L]: Landau-sharp inertia.** Module `RHTower/TiltedWeilNyquistInertia`, wired after `QuasiPolynomialWeilSeparation`. Built with `lake build`; axioms propext/choice/Quot.sound.
  - Tools:
    - `W_const_mul` (sesquilinearity);
    - `norm_W_le_of_pointwise` (`‖W‖ ≤ (5/4)S_Z C` from pointwise products);
    - `ClusterSetup.re_W_testθ_le` (tilted node block without positivity);
    - `norm_testθ_node_le`, `testθ_off_carrier`, `norm_W_tilted_tests_le` (three-way cross split);
    - `tiltBd_le`, `tiltN12_le` (explicit sizes).
  - **`weilNegIndex_ge_card_tilted`.** Suppose `tiltedHodgeRatio ≤ R`, `tiltedNormRatio ≤ Λ`, pairwise gaps are `≥ 3/2`, and `K₀|T|R ≤ 1`. Then `|T| ≤ weilNegIndex ζ a (1/(K₁a|T|(Λ²+1)))`.
- **Verdict (L42).** PROVED. The finite-level triple is now Landau-sharp:
  - exclusion (L39);
  - spectral separation (L40/L41, quasi-polynomial);
  - inertia (L42, quasi-polynomial margins).
  Below `2πe^{2a−3/4}/(1+κ)`, the negative squares of the level-`a` Weil form at margin `exp(−O_κ(log²t))` are exactly the off-line zeros (separated ones counted from below; the upper bound is HF-F29). At `(1−o(1))·Landau` the margin is `exp(−ω(log²t))`.

### L43 — Producer sweep after the finite-level dictionary closed (kills and survivors)
- **Frame.** L39–L42 plus the corpus lattice law (`offLineLattice_weil_positive_iff`) give a sharp dictionary. Up to the deep-zero blind zone, level-`a` Weil positivity is RH below the Landau height `(1±o(1))·2πe^{2a}`; the constant 2π is sharp for lattice-like configurations. A producer must certify this from source data. Five candidate mechanisms:
  1. **Near-radical quotient positivity.** Claim: `W ≥ 0` on `R_a^⊥`, the complement of the near radical.
     - Kill: `W(r, ·) ≈ 0` for near-radical `r`, so negative directions survive projection, and positivity on `R_a^⊥` is RH below Landau. CIRCULAR.
     - Survivor: `W` descends to `V₀/R_a` up to `exp(−c e^{2a})`, and on the quotient it is the zero trace form. This is structural and is the L37/L42 picture.
  2. **Monotone-in-level barrier.** Claim: `μ(a)` obeys a differential inequality that keeps it `≥ 0`.
     - Kill: L34 #5 (the Krein barrier is not a barrier). By L41, `μ` drops to `−exp(−C log²t₁)` within a window of width `O(log t₁/t₁)` in `a` around `½log(t₁/2π)`. No regularity in `a` forbids that. FALSE.
  3. **Tilt-phase positivity.** Claim: the tilted forms `Σe^{2θγ}f̂(γ)conj f̂(γ̄)` are positive for some `θ` for structural reasons.
     - Kill: they are ordinary Weil forms of complex-shifted analytic tests. Positivity for all `θ` is positivity on analytic tests, which is RH. CIRCULAR.
     - Survivor: the tilt rotates the phase of an off-line pair by `−2θδ` and rescales by `e^{2θt}`. This is exactly why L39's node block has real part `−cos(2θ Im γ)e^{2θ Re γ}`.
  4. **Landau-excess prolate law** (a producer of *size*, not of sign). Conjecture: `λ_min(L) = exp(−π²(S_L − 2N(T*))(1+o(1)))` under RH, where `S_L − 2N(T*) = T*/π` is the Shannon number minus the zero count below `T* = 2πe^{2L}`. This matches the empirical `−ln λ_min ≈ 2π²N/ln N` of arXiv 2608.24827 to leading order (both `≈ 2π²e^{2L}`).
     - Not a sign producer, so it does not decide RH. SURVIVES as a conjecture about the near radical.
  5. **Finite-level de Bruijn–Newman.** Let `Λ(a) := inf{t : Hodge_t(a)}` for `H_t`, with kernel `e^{tu²}Φ`. `Λ(a) ↑ Λ ≥ 0` (Rodgers–Tao), and RH ⟺ `Λ(a) ≤ 0` ∀a. The heat flow is a producer for `t ≥ 0.2` (Polymath, with computation), and none at `t = 0`.
     - The tilt/cluster machinery transfers to `Φ_t = e^{tu²}Φ`, which is still double-exponential. But the window inputs (`ξ/P_V` Lipschitz bounds, local counts) need `H_t` analogues. BRIDGE, not a producer.
- **Verdict.** No producer survives. The positive survivors are structural.
- **Consequence for other routes.** The frontier's LA route asks for "an arithmetic O-charge/M-charge separator at Dirichlet length `≍ t`" for near-double off-line pairs.
  - L39 is such a separator: the level-`a` Weil form with `2πe^{2a−3/4} ≈ t` (Dirichlet length `e^{2a} ≍ t`) excludes every off-line zero at height `t`, super-tight clusters included.
  - So LA's separator exists; what remains open is its positivity, i.e. the producer.
- **Next.** Leave zero-side analysis. Candidate: survivor 5, a finite-level de Bruijn–Newman dictionary, using the heat-flow producer for `t > 0` as a genuine source of positivity. Question: what does the heat flow produce at finite level, and how does `Λ(a)` behave?

### L44 — The pole-compressed prime transport is never sub-exponential: Dirichlet resonance kills MUST-261's "source problem". TRUE [L]
- **Target claim (STATUS MUST-261, frontier RW "Open").** "The source problem is exactly the exponential growth rate of the pole-compressed prime translation operator `P_{V₀}(Σ_nΛ(n)n^{−½}τ_{log n})P_{V₀}` on `L²(−A,A)`: trivial rate `e^A`, rate `< 1` by any margin gives a zero-free strip, sub-exponential ⟺ RH."
- **Conjecture (kill).** Unconditionally, for all large `A` there is a pole-constrained `f ∈ L²(−A,A)` (`∫f e^{±u/2} = 0`) with `Re⟨T_A f, f⟩ ≥ (e^A/8A)∫|f|²`. So the compressed norm is `≥ e^A/8A`, the implication RH ⇒ sub-exponential is false, and the stated "source problem" is the wrong object.
- **Mechanism.**
  - `g = e^{iτu}1_{[−A,A]}` has `⟨Tg,g⟩ = 2Σ Λ(n)n^{−½}(2A − log n)cos(τ log n)`.
  - Kronecker/Dirichlet (`exists_fin_simultaneous_two_pi_phase_approximation_delayed_quantitative`) gives arbitrarily large integer `τ` with `cos(τ log n) ≥ ½` for all `n ≤ e^{2A}`. Hence `⟨Tg,g⟩ ≥ Σ Λ(n)n^{−½}(2A − log n) ≥ e^{−A+½}ψ(e^{2A−1}) ≥ e^{A}/3` (PNT).
  - The pole constraint costs `|∫g e^{±u/2}| ≤ 2e^{A/2}/τ`, which tends to 0 as `τ → ∞`. A 2×2 correction by `e^{±u/2}1_{[−A,A]}` makes `f` exactly pole-free, and the change in the form is `O(e^A·e^{A}/τ)`.
- **Why the low-frequency attempt fails (recorded).** For pole-free tests at bounded frequency the main term cancels exactly: `∫e^{y/2}R_g(y)dy = ĝ(i/2)ĝ(−i/2) = 0`. There `⟨Tg,g⟩ = Arch(g) − W(g,g) + 0`, which is small. The e^A growth lives only at Dirichlet-resonant frequencies `τ ~ exp(O(e^{2A}))`, where `Arch ~ log τ ≫ e^A` keeps the Weil form positive.
- **Positive survivor.** The RH content of the prime side is the archimedean-relative (frequency-aware) bound `⟨T_Af,f⟩ ≤ Arch(f) + o(1)‖f‖²` on pole-free `f`, i.e. Hodge(A). This is the finite-level Weil form, whose dictionary is L39–L42. No operator-norm (height-blind) formulation can carry RH, pole-compressed or not.
- **Verdict.** SURVIVES as a kill of the stated RW open core.
- **Lean.** `RHTower.PoleFreePrimeTranslationResonance`: `poleFree_primeTranslation_resonance`. For all large `A` there is a bounded `f` supported in `[−A,A]` with `∫f e^{±x/2} = 0`, `∫|f|² > 0` and `(e^A/(64A))∫|f|² ≤ Re Q_A(f,f)`. The constant is `1/64` rather than the paper `1/8`, because the PNT step is used as `≥ e^A/4` and the `L²` mass as `≤ 9A/2`. Pieces:
  - `exists_resonant_frequency`: Dirichlet via `exists_fin_simultaneous_two_pi_phase_approximation_delayed_quantitative`, `Q = 9`.
  - `exists_primeHinge_ge`: PNT.
  - `norm_poleMoment_modulatedFlat_le`: `≤ 2e^{|s|A}/τ`.
  - `pole_system_solve`, `norm_pole_coefficient_le`.
  - `norm_primeTranslationForm_sub_le`: stability `4Aε(2+ε)·ΣΛ(n)n^{−½}`.
  - `l2mass_modulatedFlat_sub`.

  Axioms propext/choice/Quot.sound. STATUS CANNOT-474; MUST-261 corrected in place.

### L39 — Finite-level Krein determinacy: representations carry the multiplicities below the Landau height. TRUE [L]
- **Conjecture (L36 P2, sharpened to the Landau height).** Every positive measure representing the level-`L` Hodge form (`∫|f̂|²dν = |W(f,f)|`) gives each isolated on-line zero its exact multiplicity below `(1−η)·2πe^{2L}`, up to super-exponentially small error.
- **Kill attempts.**
  - *False?* No. The zero measure is itself such a representation under RH.
  - *Circular?* No: it is a Christoffel argument with an explicit resolvent test.
  - *Rediscovered?* The `L = ∞` uniqueness is the corpus Hedenmalm classification. There are no finite-level mass statements in Suzuki (de Branges / screw), CC or CCM.
  - *Insignificant?* No. It completes the finite-level determinacy of the indeterminate extension problem.
  - Verdict: SURVIVES.
- **Theorem** (`RHTower/KreinRepresentationMassLaw:zeta_krein_representation_masses_below_landau_height`; unconditional; axioms propext/choice/Quot.sound).
  - For `0 < η ≤ ½` and `M ≥ 1` there is `L₀` such that, for `L ≥ L₀`, every representing `ν` and every on-line zero `½+iγ₀` of multiplicity `m₀ ≤ M` satisfy `|ν([γ₀ ± r_L]) − m₀| ≤ exp(−πη^{3/2}e^{2L}/(64M))`, with `r_L = exp(−πη^{3/2}e^{2L}/(8M))`.
  - Conditions: `7 ≤ γ₀ ≤ (1−η)2πe^{2L}`, ordinate separation `δ ≤ ½`, and `(48C log(γ₀+1) + 32M)/δ ≤ πη^{3/2}e^{2L}`.
- **Proof.**
  1. Test `f = (D_{γ₀}^{m₀}Φ_θ)_{≤L−w} ⋆ κ₂`, where `D` is the corpus iterated resolvent division applied to the tilted kernel.
  2. Weil form. `W(f,f) = m₀|f̂(γ₀)|² + O(ε_F²·poly)`: at every other zero, `F̂ = Φ̂_θ/(z−γ₀)^{m₀}` vanishes up to the tail (`norm_W_resolventTest_sub_le`).
  3. Ratio form of Christoffel, the new mechanism.
     - Off the ball, `|f̂| ≤ r^{−m₀}|ĝ| + (r^{−m₀}ε_Φ+ε_F)|κ̂₂|`. Here `ĝ` is the tilted radical test and `κ̂₂` the plain bump at the same frequency, and the two share the bump factor, so no lower bound on ζ is needed off the ball (`norm_paperFT_resolventTest_le`).
     - Their energies are `O(ε_Φ²·poly)` and `O(poly)`.
  4. On the ball.
     - `F̂` is nearly constant: minimum modulus of `V = Φ̂_θ/(z−γ₀)^{m₀}` on the circle of radius `δ/2` (via `|Ξ(z̄)| = |Ξ(z)|`, the path lower bound for ζ, and the sharp Gamma bound), plus Borel–Carathéodory for `log V` with a ceiling on the radius-`3δ/4` circle (`divided_tilted_kernel_near_zero`).
     - The bump transform is Lipschitz: `|κ̂_w(s)−κ̂_w(s')| ≤ 2w²|s−s'|`.
  5. Two-sided mass bound and exponent bookkeeping, with one master level inequality (`landau_small_package`).
- **Modules** (all wired after `LandauHeightKreinPinning`; all built with `lake build --old`; lint clean for these):
  - `RHTower/TiltedKernelResolventTest`: SuperExpDecay of `Φ_θ`, weighted tails, local factor at an on-line zero, truncation, bumped tests, and the plain-bump Weil bound.
  - `RHTower/XiOnLineZeroLocalBounds`: `|Ξ|` two-sided near the line, and the divided-kernel floor, ceiling and variation.
  - `RHTower/KreinRepresentationMultiplicities`: `RepresentsHodgeForm`, the measure inequalities, and the resolvent-test bounds.
  - `RHTower/KreinRepresentationMassLaw`: arithmetic core and the final theorem.
- **Route consequence (HF).** With L38, any positive representation of the level-`L` Weil form equals the zero measure of ζ below `(1−η)·2πe^{2L}`, including multiplicities, up to `exp(−c_{η,M}e^{2L})`.
  - So the finite-level positivity problem has an essentially unique solution below the Landau height.
  - A producer of positivity is a finite-level spectral realization that must compute the zeros and their multiplicities.
- **Next.**
  - The remaining freedom of representations lies above `2πe^{2L}`: an indeterminacy theorem under RH via oversampling.
  - Landau-sharp Nyquist exclusion, i.e. HF-F31 with the tilted kernel.

### L45 — Theta threshold: no function decaying faster than Riemann's kernel has a ξ-divisible transform. TRUE [L]
- **Pivot reason.** L39–L44 closed the finite-level dictionary and the height-blind prime side. The sweep for new producer mechanisms found only rediscoveries:
  - the AFE reflection of `ζ'/ζ` is the explicit formula;
  - a Lévy-coupling producer fails the exact-primes gate, since coupling bounds survive prime deletion;
  - the Krein–Riccati continuation is killed at card line 687;
  - the CCM ground-state Hurwitz route is blind.
  L43 survivor 4 (a prolate/Landau–Widom constant `2π²` for the near-radical) was re-examined. A generic-point prolate count predicts `exp(−π²e^{2a}/a)`, far larger than the theta radical `exp(−2πe^{2a})`. The near-radical is theta-driven, not prolate-driven. The structural question: how small can a radical vector's tail be?
- **Conjecture (bold form).** The zero divisor of `ζ` (with multiplicity) is a uniqueness set for `{F : |F(x)| ≤ Ce^{−ce^{2|x|}}}` iff `c > π`. That is, `ξ ∣ M_F` and rate `c > π` force `F = 0`; `Φ` has every rate `c < π`.
- **Attack (Phase 4).**
  - False? The argument has three steps. The quotient `h = M_F/ξ` has exponential type (Stirling floor off the strip, Burnol good heights inside it). It decays like `e^{−(σ/2)log(c/π)}` along both real rays (Binet vs Legendre transform of the decay). The two-ray Paley–Wiener theorem then applies. No hole found.
  - Circular? No zero-location input.
  - Rediscovered? No statement found in the corpus or the literature (compact support, `c = ∞`, is `SuzukiCompactL2Fourier`). The mechanism is classical Legendre duality, so experts would find it natural.
  - Significance: it identifies `Φ` as the extremal generator of the Weil radical. Complex shifts `Φ(·−w)` have rate `πe^{−2|Re w|}cos(2 Im w)`, so the rate-`c` radical is at most a shift window that closes at `c = π`.
- **Verdict.** SURVIVES. Paper proof and Lean in `P3:theta-threshold-xi-divisible-uniqueness`.
- **Lean.** `RHTower.ThetaThresholdXiDivisibleUniqueness`: `theta_threshold_xi_divisible`.
  - For `c > π`: rate `c` together with `M_F = ξ·h` (`h` entire) gives `F = 0` a.e.
  - For `0 ≤ c < π`: `Φ` is a nonzero example with `h = 1`.
  - Axioms propext/choice/Quot.sound. The boundary case `c = π` is open; `Φ` misses it only by its polynomial prefactor.
- **Collateral repair.**
  - `HodgeNyquistExclusion`'s pigeonhole lemma duplicated `RHTower.exists_good_height` from `XiHeightSelection`, which broke the umbrella. It is renamed `exists_height_far_from_finset`, and its 18 dependents were rebuilt.
  - `PoleFreePrimeTranslationResonance`'s `primeLogWeight_nonneg` duplicated `VonMangoldtSquarePowerMoments`. It is renamed `vonMangoldtHalfWeightSum(_nonneg)`.
- **What it says about producers.** The Weil radical is generated by `Φ`, and `Φ` is extremal: no radical vector decays faster. A positivity producer built on near-radical structure (CCM S2, prolate) is therefore anchored at the theta tail, with no faster-decaying radical direction to exploit. Correction to L43 survivor 4. The deepest near-null directions are radical truncations, and no radical vector beats `Φ`'s tail (L45); a lower bound for `λ_min` is open. The near-radical *bulk*, of dimension `≈(2−η)e^{2L}` with margin `exp(−η²e^{2L}/(300L))` (HF-F41, other cycle), is prolate/Landau–Widom-type. Both pictures hold, at different depths of the spectrum.

### L45 — The near radical of the level-`L` Weil form has at least `(2−η)e^{2L}` dimensions: Connes–Consani's constant 2 (in progress)
- **Context.**
  - HF-F30 gives `≥ e^{2L−2}/20` near-null directions at margin `exp(−e^{2L−2})`, using polynomial multipliers of `Φ` with Remez losses.
  - CC (2021) and CCM (2025) observed about `2e^{2L}` tiny eigenvalues numerically; Zhu and 2608.24827 fit the decay empirically. No rigorous count exists (2608.24827 re-checked: it proves only a `λ_min` bound).
  - The heuristic: Shannon number of `[−L,L] × [−T,T]` minus the zero count below `T`, maximised at `T = 2πe^{2L}`, which gives `(T/π)(2L − log(T/2πe)) = 2e^{2L}`.
- **Conjecture (L45).** For every `0 < η ≤ 1` there is `L₀` such that for `L ≥ L₀` the Hodge-class tests at level `L` contain a subspace `V` with `dim V ≥ (2−η)e^{2L}` and `‖W(f,f)‖ ≤ exp(−η²e^{2L}/(300L))∫|f|²` on `V`.
- **Kill attempts.**
  - *False?* Heuristically the count is `≈ 2e^{2L}` (CC numerics), so a `(2−η)` lower bound is consistent.
  - *Circular?* No. It uses only Riemann–von Mangoldt, local zero counts and linear algebra; no positivity.
  - *Rediscovered?* The counting heuristic is CC's; no proof of any count with constant `> 1/(20e²)` exists (corpus HF-F30, 2608.24827, CCM 2511.22755).
  - *Insignificant?* It proves the leading constant of the CC small-eigenvalue phenomenon (lower bound).
  - *Margin.* The `1/L` in the margin is the Landau–Widom plunge of a sharp time cutoff: a guard band of width `Δ` costs `ΔL/π` frequencies. The empirical law `−log λ_min ≈ 2π²e^{2L}` suggests the plunge is absent for the true form; that needs zero structure beyond counting.
  - Verdict: SURVIVES PRELIMINARY ATTACK.
- **Paper proof.**
  1. Parameters: `σ = η/8`, `ℓ = L − σ`, `T = 2πe^{2ℓ}`, `Δ = πηe^{2L}/(8L)`, `N = ⌊σΔ/(8e)⌋`.
  2. Plateau: `b = 1_{[−(ℓ+σ/2), ℓ+σ/2]} ⋆ β ⋆ B_h^{⋆N}`, with `β` a smooth unit bump of radius `σ/4` and `B_h` the unit box of half-width `h = σ/(4N)`.
     - Then `b` is smooth, `0 ≤ b ≤ 1`, `b = 1` on `[−ℓ,ℓ]`, and `supp b ⊆ [−L,L]`.
     - `b̂(z) = (2 sin((ℓ+σ/2)z)/z)·β̂(z)·(sin(hz)/(hz))^N`, so on the strip `|b̂(z)| ≤ 4e^{L/2}e^{−N}Δ/|Re z|²` for `|Re z| ≥ Δ`.
  3. Test space: `E = {b·p : p = Σ_{|k|≤k₀} c_k e^{iτ_k u}}` with `τ_k = kπ/ℓ` and `k₀ = ⌊(T−Δ)ℓ/π⌋`, so `dim E = K = 2k₀+1`.
     - Orthogonality on `[−ℓ,ℓ]` gives `∫|bp|² ≥ 2ℓ‖c‖²`.
  4. Constraints: `f̂(γ_ρ) = 0` for every distinct zero with `|Im ρ| ≤ T`, and `f̂(±i/2) = 0`.
     - Their number is `≤ 2N(0,T) + 2` (conjugation symmetry of the zero set, `mult ≥ 1`).
     - Dyadic summation of `rvM_main` gives `N(0,T) ≤ (T/2π)log(T/2πe) + C log²T`.
     - Hence `dim V ≥ K − 2N(0,T) − 2 ≥ 2e^{2ℓ} − 2Δℓ/π − O(L²) ≥ (2−η)e^{2L}`.
  5. Energy: `W(f,f) = Σ m_ρ f̂(γ_ρ) conj f̂(γ̄_ρ)` has only terms with `|t_ρ| > T`.
     - There `|f̂| ≤ ‖c‖₁·4e^{L/2}e^{−N}Δ/(Δ+|t|−T)²`.
     - `window_tsum_le` at `ω = ±T` then gives `|W| ≤ K·16e^Le^{−2N}Δ²·48A₀log(T+3)·‖c‖² ≤ exp(−η²e^{2L}/(300L))∫|f|²` for large `L`.
- **Lean plan.**
  - `HTGeometry/BoxConvolutionPlateau`: iterated box convolution, transform, decay, smoothness, plateau.
  - `RHTower/ZetaZeroCountUpperBound`: `N(0,T)` upper bound and the distinct-zero count for `|Im ρ| ≤ T`.
  - `RHTower/SharpWeilNearRadicalCount`: test space, constraints, energy bound, final theorem.

### L46 — Hardy equality case for ξ: theta-rate ξ-divisible functions are polynomial multiples of Φ. TRUE [L]
- **Conjecture.** Suppose `|F(x)| ≤ C e^{k|x|} exp(−π e^{2|x|})` for some `k ≥ 0`, and `M_F = ξ·h` with `h` entire. Then `h` is a polynomial, i.e. `M_F = P·ξ`. This is the exact analogue of Hardy's theorem (Gaussian decay on both sides forces polynomial × Gaussian), with the theta kernel as the extremal and the zero divisor of `ζ` as the vanishing set. It would complete L45: the Weil radical at theta rate is `{P(∂)Φ}`.
- **Attack (Phase 4).**
  - Pointwise growth bounds cannot decide it. `h(s) = cos(b(s−½))` (`b < π/4`) satisfies every bound available at fixed height `t`: it is bounded on the real axis with vertical type `b`. The corresponding `F = (Φ(·+ib)+Φ(·−ib))/2` has modulus rate `π cos 2b < π`, which only its phase cancellation hides.
  - The decisive information is directional. The exact imaginary-shift Γ bound gives `|h(re^{iθ})| ≤ poly·exp(r sin²θ/(4cos θ))`, which is quadratic in `θ`. `cos(b(s−½))` grows like `e^{brθ}`, linearly in `θ`, and violates it.
  - A sector Phragmén–Lindelöf argument on `δ ≤ arg z ≤ π−δ` with multiplier `e^{iβz}`, `β = δ²/(2 sin δ) → 0`, gives `|h(z)| ≤ A|z+i|^m` uniformly. So `h` is a polynomial.
  - Verdict: SURVIVES.
- **Lean.** `RHTower.ThetaRigidityHardyEqualityCase`, main theorem `theta_rigidity_polynomial_quotient`: if `|F| ≤ Ce^{k|x|}e^{−πe^{2|x|}}` and `M_F = ξ·h`, then `h` is a polynomial. `riemannPhiKernel_theta_rate` shows `Φ` meets the hypothesis with `k = 9/2`. Axioms propext/choice/Quot.sound. Reusable pieces:
  - `norm_le_sector_of_rays`: sector Phragmén–Lindelöf through `z = e^w`;
  - `Gamma_mul_quadratic_le_norm_Gamma`: `|Γ(x+iy)| ≥ Γ(x)(1+y²/x²)^{−½}e^{−y²/x}`;
  - `xi_floor_quadratic`;
  - `ray_core`, `norm_le_upper_half_plane`;
  - `centredLaplace_conj`.
- **Classification (L45 + L46).** At decay rate `≥ π`, the ξ-divisible class is `{F : M_F = P·ξ}` with `P` polynomial (up to the polynomial prefactor). Above `π` it is `{0}`. So the Weil radical at theta rate is finite-dimensional per degree, spanned by `Φ` and its polynomial-multiplier images.
- **Producer relevance (honest).** L45/L46 classify the theta-rate Weil radical. They do not supply a producer.
  - A real-rooted transform `Ĝ = h·ξ` already gives RH for any entire `h`; the polynomial structure is not needed for that step.
  - The hard input for CCM (S2) is ξ-divisibility of limits of real-rooted ground states. Under ¬RH, ground states concentrate on off-line zeros and are not ξ-divisible, so that input is RH-strength.
  - What the classification adds: any ξ-divisible theta-rate limit is identified as `P(∂)Φ`. There is no exotic radical direction for a limit to escape into.
- **L45 result [L]: sharp near-radical count.** Theorem `RHTower/SharpWeilNearRadicalCount:zeta_weil_near_radical_sharp_count` (unconditional; axioms propext/choice/Quot.sound).
  - For `0 < η ≤ 1` and all large `L`, the level-`L` Hodge class contains `V` with `dim V ≥ (2−η)e^{2L}` and `‖W(f,f)‖ ≤ exp(−η²e^{2L}/(300L))∫|f|²` on `V`.
  - HF-F30 had constant `1/(20e²) ≈ 0.0068`. This one is CC's observed constant `2`.
- **Modules** (wired after `KreinRepresentationMassLaw`; built with `lake build --old`; lint clean for these):
  - `RHTower/BoxConvolutionPlateau`: `boxPower`, `boxPlateau`, and the transform bound `(2e^{A|y|}/|z|)(e^{h|y|}/(h|z|))^n e^{r|y|}`. With `n ≍ h|x|` this gives `e^{−n}`: exponential decay at a prescribed frequency.
  - `RHTower/ZetaZeroCountUpperBound`: `zeroCount_upper`, `N(0,T) ≤ (T/2π)(log(T/2π)−1) + C log²T`, by dyadic telescoping of `rvM_main`; and `ncard_lowZeros_le`.
  - `RHTower/PlateauTrigonometricTests`: Parseval on `[−ℓ,ℓ]`, bulk bound, injectivity, and `norm_W_trigTest_le` (both factors are tail-sized at every zero above `T`).
  - `RHTower/SharpWeilNearRadicalCount`: far-field plateau decay, dimension and margin arithmetic, and the level and final theorems.
  - Also fixed three umbrella collisions in the L39 modules: `truncCore`/`truncTail` → `cutoffCore`/`cutoffTail`, `superExpDecay_tiltedPhi` → `superExpDecay_tiltedRiemannKernel`, `expTail_tiltedPhi_le` → `expTail_tiltedPhi_le_of_rate`. They clashed with `TiltedClusterNyquistExclusion` and `HeatEnergyBridge`.
- **Verdict.** PROVED. The leading constant of the Connes–Consani count is now a theorem as a lower bound.
- **What it says for HF.** A producer of Hodge(L) must certify positivity on a `(2−o(1))e^{2L}`-dimensional block where the form is `exp(−cη²e^{2L}/L)`-degenerate.
  - The block is spanned by band-limited tests that vanish at the zeros below the Landau height. So it is the same `2πe^{2L}` phenomenon seen from the kernel side: Shannon number minus zero count.
- **Open.**
  - (a) Upper bound: under RH, at most `(2+η)e^{2L}` eigenvalues below `exp(−ηe^{2L})`. This needs a sampling inequality in the oversampled range `t > 2πe^{2L}` together with the undersampled count.
  - (b) Margin without the `1/L`. Landau–Widom says any sharp-time-cutoff construction loses it, while the empirical law `−log λ_min ≈ 2π²e^{2L}` suggests the true form does not.

### L47 — Theta-window law: the Weil radical at rate `c` is the Paley–Wiener space of the shift window `D_c`. TRUE [L] (forward law + window identity)
- **Conjecture (directional form).** Let `|F(x)| ≤ Ce^{k|x|}e^{−ce^{2|x|}}` with `0 < c ≤ π`, and `M_F = ξ·h`. Then on `Re s ≥ 2`, `s = re^{iφ}`,
  `log|h(s)| ≤ r·J_c(φ) + O(log r)`, where `J_c(φ) = ½[cos φ·log(π cos φ/c) + |φ| sin|φ|]`.
  In coordinates the exponent is `(σ/2)log(π/c) + ½|t|arctan(|t|/σ) − (σ/4)log(1+t²/σ²)`.
- **Window identity.** `J_c(φ) = sup{v cos φ + |θ| sin|φ| : πe^{−2|v|}cos 2θ ≥ c}`. The supremum is attained at `θ = φ/2`, `v = ½log(π cos φ/c)`.
  - `|Φ(x−w)|` decays at rate `πe^{−2|Re w|}cos(2 Im w)`, and `M_{Φ(·−w)} = e^{w(s−½)}ξ`. So every direction's bound is attained by a single complex shift of `Φ` from the window `D_c = {w : πe^{−2|Re w|}cos 2 Im w ≥ c}`.
  - The directional law equals the support function of `D_c` in the directions `π cos φ ≥ c`. In steeper directions it only dominates it (correction after Lean).
  - `c = π`: `D_π = {0}`, giving L46. `c > π`: `D_c = ∅`, giving L45.
- **Attack.** False? The exact imaginary-shift integral gives `½I(σ/2,t/2) = (r/2)(φ sin φ + cos φ log cos φ)` with no slack. The window supremum is a one-variable concave maximization, and the tangent-line inequality for `cos` on `[0, π/2]` proves it. SURVIVES. Lean next (the forward law, plus the window inequality and its equality case).
- **Lean.** `RHTower.ThetaWindowDirectionalLaw`. Axioms propext/choice/Quot.sound.
  - `theta_window_directional_law`: the forward law with the exact exponent.
  - `theta_window_le`: every window shift is dominated.
  - `theta_window_attained`: equality in every direction with `c ≤ π cos φ`.
  - `theta_window_real_axis_attained`: `Φ(·−½log(π/c))` realizes the law on the real axis.
  - Reusable: `gammaShiftIntegral_half_eq` (exact Γ imaginary-shift integral in `(σ,t)`), `xi_floor_exact`, `legendre_rate_div_Gamma_le`, `cos_le_tangent`, `centredLaplace_shift`.
  - Not formalized: the converse (every `h` whose indicator is below the support function of `D_c` is realized), and attainment in oblique directions by complex shifts. The latter needs the tilted kernel decay.
- **Radical picture (L45–L47).** Graded by decay rate, the Weil radical is `Φ` smeared over the theta window `D_c`:
  - empty above `π`;
  - `{0}` at `π` (polynomial quotients);
  - for `c < π`, growth bounded by `J_c`, which equals the support function of `D_c` where `π cos φ ≥ c`. In steeper directions `J_c` exceeds the window's support function `½arccos(c/π) sin φ`; sharpness there is open.
- **Verdict for the producer.** A complete structural picture of the radical, but no positivity mechanism. The next cycle pivots to producer attempts.

### L48 — Heavy prime perturbations: radical two-point tests expose the perturbation's own L-zeros (paper; Lean blocked on the Dirichlet-L explicit formula)
- **Target.** MUST-357's open core: heavy perturbations `Σ|w_n| log n/√n = ∞`, for example deleting a residue class of primes.
- **Mechanism tried (new).** Use the real shifts `F₁(·+v)` of the pole-free radical kernel `F₁ = (¼−∂²)Φ`. They are exact radical vectors (transform `e^{ivt}G(t)`, `G = ξ·(t²+¼)`), and their truncations have `W_ζ → 0`.
  - Suppose the perturbed form `W_{Λ+w}` is positive at every aperture. Then `B_w(v) = Σ_n w_n n^{−½}[K(v+log n)+K(v−log n)]` (`K` = autocorrelation of `F₁`) is negative semidefinite.
  - Hence `|B_w(v)| ≤ −B_w(0)`, and `B̂_w = G²μ̂_w ≤ 0`.
- **Kill of the naive version (learned).** One might hope that one-signed `w` with growing local sums make `B_w(log m)` unbounded. It fails, because `∫e^{±y/2}K = |F̂₁(±i/2)|² = 0`: pole-freeness annihilates the smooth main term of any regularly distributed prime set (the L44 cancellation again). So `B_w` sees only the prime *fluctuations* of the deleted set. For `w = ±εΛ` the main terms cancel and `B` stays bounded. The Arch-sign argument still kills scaling, since off the zeros `μ̂_{εΛ} = ε·Arch` changes sign.
- **Positive survivor (paper theorem).** For `w = (Λχ₄ − Λ)/2` (keep `p ≡ 1 (4)`, delete the odd powers of `p ≡ 3 (4)`, halve `p = 2`):
  - on radical tests, `S_w(E) = ½∫|E|²G²(Arch_{χ₄} − Arch_ζ) − ½Σ_{ρ_χ}|E(γ_χ)|²G(γ_χ)²`;
  - the zeros of `L(s,χ₄)` enter as negative atoms, and the archimedean mismatch `Re ψ(3/4+it/2) − Re ψ(1/4+it/2) + log 4 > 0` is a positive density;
  - a trigonometric polynomial `E` vanishing at the first `L(χ₄)`-zeros (where `G²` is not negligible) makes `S_w(E) > 0`, so `W_{Λ+w}` fails positivity at a finite aperture;
  - the argument works for any character-defined deletion `(Λ ± Λχ)/2` with an archimedean mismatch of fixed sign.
- **New insight.** Radical tests turn every heavy perturbation into a statement about the zeros of the perturbation's own Dirichlet series. Prime-counting information (main terms, Chebyshev, local sums) is invisible to them; only the L-zeros and the Γ-factor mismatch remain.
- **Lean status.** Blocked: needs the Guinand–Weil explicit formula for `L(s,χ₄)`, which is not in the corpus (it has zero boxes, zero density and contour pieces for Dirichlet L, but no explicit formula). Backlog card `P0:dirichlet-l-guinand-weil-and-heavy-deletion`.

### L49 — Sharp theta-window law in the steep directions. TRUE [L]
- **Conjecture.** Let `|F| ≤ Ce^{k|x|}e^{−ce^{2|x|}}` with `0 < c ≤ π`, `M_F = ξh`, and set `φ₀ = arccos(c/π)`, `θ* = φ₀/2`. On the steep sector `φ₀ ≤ arg z ≤ π − φ₀` (and its conjugate), `|h(z)| ≤ B(1+|z|)^m e^{θ*|Im z|}`, where `θ*|sin φ|` is exactly the support function of `D_c` there. Together with L47 on `|arg z| ≤ φ₀`, the growth indicator of `h` is at most the support function of `D_c` in *every* direction.
  - Sharpness: `Φ(·+iθ*)` has rate `π cos 2θ* = c` and quotient `e^{−iθ*(s−½)}`, of modulus `e^{θ* t}`.
  - So the rate-`c` radical has growth indicator exactly the support function of `D_c`.
- **Attack.** On the boundary rays `±φ₀` the L47 exponent is exactly `θ*|t|`, since `log(π cos φ₀/c) = 0` and `½log(1+tan²φ₀) = log(π/c)`. The rays `π ∓ φ₀` follow from the functional equation. Phragmén–Lindelöf in a sector of opening `π − 2φ₀ < π`, with multiplier `e^{iθ*z}`, transports the boundary bound inside. No hole found. SURVIVES.
- **Lean.** `RHTower.ThetaWindowSteepLaw`. Axioms propext/choice/Quot.sound.
  - `theta_window_steep_law`: `|h(½+u)| ≤ B(|u|+1)^m e^{θ*|Im u|}` on `φ₀ ≤ |arg u| ≤ π−φ₀`.
  - `theta_window_tilt_attained`: `Φ(·+iθ*)` has rate `c` and quotient modulus `e^{θ* Im s}`.
  - Reusable: `windowTail_antitone`, `windowExponent_on_boundary_ray`, `norm_le_sector_of_rays_exp_im` (sector Phragmén–Lindelöf with an `e^{β Im z}` weight), `tiltedPhi_rate` (global tilt decay), `centredLaplace_tiltedPhi`.
- **Radical classification, final form (L45–L49).** Graded by decay rate `c`, the ξ-divisible class has quotients whose growth indicator is at most the support function of the theta window `D_c`, and it is attained in every direction.
  - Endpoints: `D_c = ∅` for `c > π`; `D_π = {0}` (polynomials).
  - Not formalized: the converse Paley–Wiener representation (every such `h` realized).
- **For the producer.** None. This is the complete structure of what the Weil form cannot see.

### L50 — Perturbation-symbol criterion: Weil positivity near `Λ` is the sign of `Re D_w` on the critical line; deleting even prime powers breaks it (in progress)
- **Criterion.** Let `w` be polynomially bounded with `w_1 = 0`, and `D_w(s) = Σ w_n n^{−s}`. For radical tests `f` (transform `E·G`, `G = ξ(½+it)(t²+¼)`), `W_ζ(f) = 0` and
  `W_{Λ+w}(f) = −(1/π)∫|f̂(t)|² Re D_w(½+it) dt`,
  with the boundary value taken from `Re s > 1`, and continuation where it exists.
  - (i) Unconditionally, positivity at every aperture forces `Re D_w(½+it) ≤ 0` on `ℝ` minus the real zeros of `Ξ`.
  - (ii) Under RH, `Re D_w ≤ 0` on the line suffices for positivity.
  - The tangent cone of Weil positivity at `Λ` is the cone of Dirichlet series with nonpositive real part on the critical line.
  - Light `w` (continuous `D_w`) with `Re D_w ≤ 0` have mean `w_1 = 0`, which forces `w = 0`. This recovers MUST-357's light rigidity. Heavy `w` are decided by the sign of the continued `D_w`.
- **Heavy example, ζ only.** Delete all even prime powers `p^{2j}` (heavy: `Σ_p log p·2log p/p = ∞`).
  - `W'(f) = W_ζ(f) + 2Σ_m Λ(m)/m·Re A_f(2 log m) = W_ζ(f) + (1/π)∫|f̂|² Re(−ζ'/ζ(1+2it)) dt`.
  - `−ζ'/ζ(s) = 1/(s−1) − γ + O(s−1)`, so `Re(−ζ'/ζ(1+2it)) → −γ < 0` as `t → 0`.
  - Take `f̂ = E·G` with `E(t) = t·sinc²(Lt)`. It vanishes at `0` (no pole mass) and concentrates at `|t| ≲ 1/L`.
  - The main term is `≈ −γ|G(0)|²·c/L³`; the tail is `O(L^{−4}·log)` via `|ζ'/ζ(1+it)| ≪ log|t|`. So `W' < 0` after truncation at a large aperture.
  - The Euler–Mascheroni constant makes the even-power block load-bearing.
- **Attack.**
  - False? The sign chain checks: `ζ'/ζ = −1/(s−1) + γ + O(s−1)`.
  - Circular? No zero input: radical tests, the Laurent expansion and the ζ'/ζ bound on `Re s = 1` are all unconditional.
  - Known? The corpus did the light case via cosine-series uniqueness (MUST-357). The radical-test reduction to the symbol, and the heavy example, are new to the corpus. No literature statement found.
  - Verdict: SURVIVES. Lean next (the even-power theorem; the general criterion stays a paper statement).
- **L50 result: TRUE [L].**
  - `RHTower.mertens_constant_nonpos_of_weilAtomSymbol_nonneg`: Weil positivity for weights `λ` with `∑_{2≤n≤x}(λ−Λ)n^{−1/2} = A log x + B + o(1)` forces `B ≤ 0`.
  - `RHTower.squareDeletedVonMangoldt_weilAtomSymbol_not_nonneg`: deleting the even prime powers gives `B = γ`, so positivity fails.
  - Modules: `WeilSymbolMertensExpansion` (the exact Mertens expansion of the perturbed symbol energy) and `WeilPositivityMertensConstantObstruction`.
  - Tests: truncated radical tests at level `log S`, spread by a mean-zero probe at scale `S`. The zero side is `O(S^{10}e^{−S})` and the mass is `≥ cS`.
  - Card: `3-formalized/weil-positivity-mertens-constant-obstruction.md`.
  - This is the first heavy-perturbation rigidity result for MUST-357's open core. Residue-class deletions (`C(x) ≍ √x`) remain; they need the modulated version or L48.

### L51 — The conductor obstruction: weighting down the primes `p ≡ ±3 (mod 8)` breaks Weil positivity. TRUE [L]
- **Conjecture.** For every `t > 0` the weights `Λ(1−t+tχ₈)` violate Weil positivity. At the double radical, the energy is `−t log 8 ∫|h|²`.
- **Attack.**
  - False? The exact identity reduces the energy to `2π(1−t)Re W_ζ + 2πt Re W_{χ₈} − t log 8∫|h|²`. Both zero sides are killed by a test radical for both `ζ` and `L(χ₈)`.
  - Circular? No: no zero locations are used, only vanishing of the transforms at the zeros.
  - Known? This is MUST-357's headline open example (deleting a residue class).
  - Verdict: SURVIVES.
- **Proof and Lean.**
  - Theorem `RHTower.chiEightMix_weilAtomSymbol_not_nonneg`, module `WeilPositivityConductorObstruction`. Axioms: propext, Classical.choice, Quot.sound.
  - Inputs: Zeta23 `EF_lit_chi_L` and the corpus χ₈ theta kernel.
  - Card: `3-formalized/dirichlet-l-guinand-weil-and-heavy-deletion.md`.
- **Insight.**
  - At the joint radical of `ζ` and `L(χ)`, Weil energy in the character direction is pure archimedean mismatch: `log q` for even `χ`, `π sech(πr) + log 4` for `χ₄`.
  - The zero sides of both functions drop out exactly.
  - So Weil positivity at `Λ` fails in the direction `Λ(χ−1)` for *every* `t > 0` because the conductor is `> 1`.
  - The opposite direction (`t < 0`) has positive mismatch. There positivity is decided by the `L(χ₈)` zeros (sign of `W_{χ₈}`), which is open.

### L51b — χ₈ line, direction t < 0: reduction to zero independence [paper]
- For `t = −s < 0`, divide the χ₈ kernel by the zero factor `(z−z₁)^m(z−z̄₁)^m` at one zero `ρ₁` of `L(χ₈)`. The kernel of `K̂/(z−w)` is `−i e^{−iwx}∫_{−∞}^x K(y)e^{iwy}dy`, which is super-exponentially decaying when `K̂(w) = 0`. Spreading the probe at `Re z₁` then gives energy `2π[(1+s)m_ζ(ρ₁) − s·m_χ(ρ₁)]·Pair + s log8∫|h|²`.
  - The pair term `2Re(h(z₁)conj h(z̄₁))` has free sign when `ρ₁` is off the line: choose the multiplier `1 + b(z−γ)`.
  - Off the line, or `m_ζ(ρ₁) = 0`: violation.
  - The only surviving configuration: every zero of `L(χ₈)` is on the critical line and is a zero of `ζ` with `(1+s)m_ζ ≥ s·m_χ`.
  - Zero counting (`N_χ ~ 2N_ζ`) excludes this for `s > 1`.
- **Result [P].** Positivity fails for `t < −1` unconditionally. For `−1 ≤ t < 0` it fails unless GRH(χ₈) holds and the zeros of `L(χ₈)` are zeros of `ζ` of comparable multiplicity. The window `[−1, 0)` is exactly an independence-of-zeros question. Lean: not started (division machinery plus two Riemann–von Mangoldt counts).

### L52 — Twist rigidity: `Λ(1 + t cos(α log n))` (conjecture)
- **Exact identity [P].** Let `f₊ = f e^{iαx}` and `f₋ = f e^{−iαx}` (tests with `f, f₊, f₋` polar-constrained), and `A(τ) = Re ψ(¼+iτ/2) − log π`. Then
  `∫|h|²S_{Λ(1+t cos(α log n))} = 2πReW(f) + πt(ReW(f₊) + ReW(f₋)) − (t/2)∫|h(τ)|²(A(τ−α)+A(τ+α))dτ`.
  - Mechanism: `k_{f±}(y) = e^{±iαy}k(y)`, and the twisted prime sum is the ζ prime sum of the modulated tests.
- **Theorem [P].**
  - If `t·(A(τ₁−α)+A(τ₁+α)) > 0` for some `τ₁`, the weights violate Weil positivity.
  - Tests: triple radical `B_R ⋆ B_R e^{iα·} ⋆ B_R e^{−iα·}` (transform `B̂(z)B̂(z+α)B̂(z−α)`), spread probe `κ(x/S)e^{−iτ₀x}` at `R = log S`.
  - Consequences:
    - `t > 0`: every `α` (take `τ₁` large).
    - `t < 0`: every `α` with `A(α) < 0` (take `τ₁ = 0`), in particular `|α|` small.
    - `α = 0`: scaling `cΛ` fails for every `c ≠ 1`.
  - Two-sided isolation of `Λ` along twist lines for small `|α|`. For large `|α|` (`A(τ−α)+A(τ+α) > 0` for all `τ`, roughly `|α| ≳ 670`) the direction `t < 0` is not seen by the triple radical.
- **Attack.**
  - False? No zero input: `W` of the three modulated tests is tiny, because each transform contains `B̂(z)`.
  - Known? Scaling to `c = 0` (prime-free) is in MUST-357; general `c` and twists are new to the corpus.
  - Verdict: SURVIVES. Lean next.
- **L52 result: TRUE [L].** Module `RHTower/WeilPositivityTwistObstruction.lean` (1343 lines). Axioms: propext, Classical.choice, Quot.sound. Wired.
  - `integral_weilAtomSymbol_twist`: the exact identity.
  - `twist_weilAtomSymbol_not_nonneg`: violation whenever `t(A(τ₁−α)+A(τ₁+α)) > 0`.
  - `twist_pos_weilAtomSymbol_not_nonneg`: every `α`, every `t > 0`.
  - `twist_neg_weilAtomSymbol_not_nonneg`: every `t < 0` when `A(α) < 0`.
  - `exists_twist_isolation`: two-sided isolation of `Λ` along all small twists.
  - `scaled_vonMangoldt_weilAtomSymbol_not_nonneg`: `cΛ` fails for every `c ≠ 1`.
  - **Insight.** Along twist directions, the tangent cone of Weil positivity at `Λ` is computed purely by the archimedean symbol `A` at shifted frequencies. `Λ` is isolated in both directions exactly where `A(τ−α)+A(τ+α)` changes sign. For `|α|` so large that it is positive for all `τ`, the `t < 0` direction is invisible to radical tests; there positivity would be decided by zero-side information.
- **Correction to L51b.** Counting zeros with `|γ| ≤ T` gives `N_χ(T) ~ N_ζ(T) ~ (T/π)log T`, not `N_χ ~ 2N_ζ`. So counting yields nothing for `t < −1`. The whole `t < 0` direction of the χ₈ line is tied to common zeros of `ζ` and `L(χ₈)`, i.e. zero independence.

### L53 — The conductor law for every real primitive character (conjecture)
- **Statement.** For every real primitive Dirichlet character `χ` mod `q > 1` and every `t > 0`, the weights `Λ(n)(1 − t + tχ(n))` violate Weil positivity (with `ζ`'s archimedean term).
  - On tests radical for both `ζ` and `L(s,χ)`, the energy is `−t∫|h|²(log q + κ·π sech(πr))dr`, where `κ` is the parity of `χ`.
  - The even case has the constant `log q`.
  - In the odd case, `Re ψ(¾+iy) − Re ψ(¼+iy) = π sech(2πy)` by the digamma reflection formula (corpus `HTGeometry.GammaLogDeriv.digamma_reflection`).
- **Kernel.** Take `K_χ(x) = Σ_j χ(j)·evenKernel(j/q)(x)` (for odd `χ`, use `oddKernel` with weight `e^{3u/2}`) and `Φ_χ(u) = 2e^{u/2}K_χ(e^{2u})`.
  - Transform: `paperFT Φ_χ z = 2q^{s}·completedLFunction χ s`, with `s = ½ + iz`, via `WeakFEPair.hasMellin` and `completedLFunction_def_even`.
  - Super-exponential decay at both ends: `isBigO_atTop_evenKernel_sub`, the kernel functional equation, and `Σχ(j) = 0`.
- **Attack.** Known? This generalizes L51 (χ₈) to all quadratic characters, including every quadratic residue-class deletion. No literature statement found. Verdict: SURVIVES. Lean: in progress.
- **L53 result (even case): TRUE [L].** Modules `RHTower/DirichletEvenThetaAxisKernel.lean` and `RHTower/WeilPositivityQuadraticConductorLaw.lean`. Axioms: propext, Classical.choice, Quot.sound. Wired.
  - `dirichletMix_weilAtomSymbol_not_nonneg`: for every even real primitive `χ` mod `q > 1` and every `t > 0`, the weights `Λ(1−t+tχ)` break Weil positivity. The defect is `t log q ∫|h|²`.
  - `integral_weilAtomSymbol_dirichlet`: `∫|h|²S_{Λχ} = 2πRe W_χ − log q∫|h|²` for every even real primitive `χ`.
  - `paperFT_dirichletAxisKernel`: the theta axis kernel of `χ` has transform `q^sΛ(s,χ)`, so it is an entire, super-exponentially decaying radical source for `L(s,χ)`.
  - The kernel in the corpus was built for χ₈ from the theta-power family; this one works for every even `χ` directly from mathlib's Hurwitz kernels.
  - **Insight.** Weil positivity for `ζ` fixes more than `Λ` up to scale and twist: it fixes the whole splitting law of every real quadratic field. Tilting toward any quadratic character costs exactly the log of its conductor, and no zero-side information enters for `t > 0`.
  - Odd case: not formalized (needs `oddKernel` and the digamma reflection).

### L54 — The quadratic conductor law for every quadratic field. TRUE [L]; two-sided isolation [P]
- **Theorem [L]** `RHTower.quadraticMix_weilAtomSymbol_not_nonneg`: for every real primitive `χ` mod `q > 1`, even or odd, and every `t > 0`, the weights `Λ(1−t+tχ)` break Weil positivity (ζ's archimedean term).
  - Odd case (imaginary quadratic fields): the defect is `t∫|h|²(log q + π sech(πτ))`. This rests on `Re ψ(¾+ir/2) − Re ψ(¼+ir/2) = π/cosh(πr)` (digamma reflection).
  - `χ₄` at `t = ½` is L48's example: keep `p ≡ 1 (4)`, delete the odd powers of `p ≡ 3 (4)`, halve the powers of 2. Now formal.
  - Modules:
    - `RHTower/DirichletOddThetaAxisKernel.lean`: odd theta axis kernel `e^{3u/2}Σχ(j)oddKernel(j/q)(e^{2u})` with transform `q^sΛ(s,χ)`. There is no pole correction in the odd case.
    - `RHTower/WeilPositivityImaginaryQuadraticConductorLaw.lean`: contains a generic `JointRadical` section. Any super-exponentially decaying kernel radical for a zero configuration `Z` gives both zero sides `O(Re^{−R/2})` and mass `≥ c`. `weilAtomSymbol_not_nonneg_of_joint_radical` turns an energy bound into a violation.
  - Axioms: propext, Classical.choice, Quot.sound. Wired.
- **Two-sided isolation on every real-character line [P].** The `t < 0` direction also fails, for every `t < 0`.
  - L51b's division argument gives a violation as soon as `L(s,χ)` has a zero where `ζ ≠ 0` (on the line), or any off-line zero.
  - Such a zero exists unconditionally: Banks–Loftus, arXiv 2607.22930 (no Dirichlet L-function vanishes at every zero of a fixed `L(s,χ₀)`); earlier Fujii, Bombieri–Perelli 1998.
  - So `W ∩ {Λ(1−t+tχ)} ⊆ {Λ}` for every quadratic `χ`.
  - Lean: needs a formal distinct-zero theorem (discrete moment `Σ_{ρ_χ} ζ(ρ_χ)`, Landau–Gonek type). Not started.
- **Summable weights are never Weil-positive [P].** If `Σ|λ(n)|n^{−1/2} < ∞`, then `S_λ = A − 2Re D_λ(½+i·)` is continuous, and positivity forces `S_λ ≥ 0` pointwise (concentrated polar-free tests).
  - `D_λ` has no frequencies in `(−log 2, log 2)`, so `∫S_λφ = ∫Aφ` for the Fejér kernel `φ = (sin bτ/τ)²`, `b = ½log 2`.
  - By Gauss's digamma integral, `∫Aφ/π = b(ψ(¼) − log π) + I₁ + bI₂`, with `I₁ ≤ b + b² + 4b³/9` and `I₂ ≤ (16/3)2^{−1/2}`.
  - Hence `∫Aφ/(πb) ≤ −5.372 + 5.171 < 0`, a contradiction.
  - Positivity needs the pole: for `λ` with a meromorphic `D_λ` (residue `r` at `s = 1`), `∫S_λφ = ∫Aφ + 2πr(φ(i/2)+φ(−i/2))`. Positivity forces `r ≥ r** ≈ 0.8`, a PNT-type lower bound.
- **Kill (resonant radical tests).** Radical tests cannot be moved to Dirichlet-resonant heights.
  - Resonance for all primes up to `e^S` needs `τ₀ ~ exp(e^S)`.
  - At such heights `|Ξ(τ₀)|² ~ e^{−πτ₀/2}` is beaten by the low-frequency leakage of any compactly supported probe unless `S ≳ log²τ₀`, which is circular.
  - This is why every rigidity result reaches only directions whose Dirichlet series continues to the line.
- **Weil cone [P, structural].**
  - Let `W` = the Weil-positive weight systems with ζ's archimedean term. `W` is convex, and each level `W_a` is compact.
  - The radical-test criterion (L50) gives `W ⊆ Λ + T`, with `T = {w : Re D_w ≤ 0 on the line}`.
  - By Farkas duality, `W ≠ ∅` ⟺ PB, a prime-blind positivity: `Σ_i∫A|ĥ_i|² ≥ 0` for polar-constrained families whose autocorrelations sum to 0 at every `log n`. PB is prime-free.
  - **Uniqueness conjecture** (`W ⊆ {Λ}`, which would give RH ⟺ PB): heuristically FALSE under RH. Hahn–Banach produces weights with absolutely continuous `S_λ` as soon as PB holds.
  - Survivor: `Λ` is the element of `W` with purely atomic `S`. Extremality of `Λ` in `W` reduces to a Fourier uniqueness question for the pair (zeros of ζ, `{±log n}`), at the Connes–Consani/Landau density 2.

### L55 — Summable prime weights are never Weil-positive. TRUE [L]
- **Theorem [L]** `RHTower.summable_weights_weilAtomSymbol_not_nonneg`: if `Σ|λ(n)|n^{−1/2} < ∞`, the finite-atom Weil symbol with weights `λ` (ζ's archimedean term) is negative on some polar-constrained `C²` test at some level.
  - This covers `λ = 0` and every finite truncation `Λ·1_{n≤N}`.
  - Together with MUST-357 it gives `W ∩ (ℓ¹(n^{−1/2}) ∪ (Λ + ℓ¹(n^{−1/2}))) ⊆ {Λ}`.
- **Mechanism.** A prime-blind test (support `[−0.34, 0.34]`, autocorrelation inside `(−log 2, log 2)`) has `∫|h|²A < 0`. On it every atom integrates to zero, so the full symbol of any summable `λ` has negative mean against `|h|²` and is negative somewhere. Concentrated radical tests finish.
- **Reusable [L].**
  - The x-space form of the archimedean energy: `∫|h|²A = (Re ψ(¼) − log π)∫|h|² + ∫_0^∞ w(t)∫|h|²(1 − cos(τt/2))`, with the positive jump density `w(t) = e^{−t/4}/(1 − e^{−t})` (`integral_normSq_mul_arch_eq_jump`).
  - A computer-free negativity certificate for the prime-free archimedean form below the first prime.
- **Producer reading.**
  - Summable prime data can never produce positivity. The divergence of `Σλ(n)n^{−1/2}`, i.e. the pole of `D_λ` at `s = 1`, is load-bearing.
  - In Beurling–Deny form, `ψ(¼) − log π ≈ −5.37` is a negative killing constant that only the non-summable prime jumps can repay.
  - This is the sharp form of "prime-free fails", extended to every absolutely summable perturbation of `0`.
- Card: `3-formalized/summable-weights-never-weil-positive.md`.

### L56 — The character-span half-space law. TRUE [L]
- **Theorem [L]** `RHTower.twoCharacterMix_weilAtomSymbol_not_nonneg`. Take real primitive `χ₁, χ₂` (moduli `q_i > 1`) and real `t₁, t₂` with `t₁ log q₁ + t₂ log q₂ > 0`, where `t_i ≥ 0` whenever `χ_i` is odd. Then the weights `Λ(1 + t₁(χ₁ − 1) + t₂(χ₂ − 1))` break Weil positivity.
  - Mixed signs are allowed. So `W ∩ span{Λ, Λχ₁, Λχ₂} ⊆ {t₁ log q₁ + t₂ log q₂ ≤ 0}`: the conductor-weighted balance is a supporting half-space of the Weil cone at `Λ`.
- **Machinery [L].**
  - `AllExpDecay` kernels are closed under convolution, and the transform of a convolution is the product.
  - `exists_dirichlet_radical_kernel` gives a radical kernel for every real primitive character.
  - `weilAtomSymbol_not_nonneg_of_joint_radical₂` handles two zero configurations. The tests use `Ψ₁ ⋆ Ψ₂`, radical for `ζ`, `L(χ₁)` and `L(χ₂)`.
- With the paper two-sided isolation (L54), the expected picture is `W ∩ (character span) = {Λ} ∩ W`.
- Module `RHTower/WeilPositivityCharacterSpanHalfSpace.lean`. Built and wired; axioms propext/Classical.choice/Quot.sound.

### Open core recorded after L50–L56: smooth elements of the Weil cone [P]
- Let `W` be the Weil-positive weight systems with ζ's archimedean term. By duality, `W ≠ ∅` ⟺ PB (prime-blind positivity, a prime-free statement).
- **Uniqueness conjecture:** `W ⊆ {Λ}`. It would give RH ⟺ PB.
- **Reduction [P].** A segment of `W` through `Λ` exists ⟺ `W` contains a *smooth element* `u`. That is: `D_u` is analytic on `Re s ≥ ½` except a simple pole at `1`, and `Re D_u(½+iτ) ≤ A(τ)/2` for all `τ`, so the symbol is absolutely continuous and `≥ 0`.
- **Natural candidates all fail [P]:**
  - `u = ζ − 1 + light`: the Ω-results for `Re ζ(½+it)` beat `½ log t`.
  - The Möbius–ζ-ratio deformation `u^{(δ)}(n) = δ^{−1}∏_{p|n}(1 − p^{−δ})`, with `D = δ^{−1}(ζ(s)/ζ(s+δ) − 1)`. It fails at `τ = 0` for every `δ > 0`: the first-order term is `(L'² − L'')(½) ≈ +3.47`, and numerically the inequality fails for `δ ∈ (0, 0.5)`. It also fails at large `τ`.
  - Summable `u` fail by L55.
- Deciding existence of a smooth element decides whether the Weil cone is a single point.

### L57 — The Nyquist constant is 2π: Hodge(a) excludes separated off-line zeros below `(1−η)·2πe^{2a}` (in progress)
- **Context.**
  - Current horizons: HF-F31/HF-F34 reach `2πe^{2a−3/4}` (tilted cluster test with shifts `1/8`, `1/4`).
  - The lattice law (`offLineLattice_weil_positive_iff`) is blind exactly at spacing `π/a`, i.e. at the ζ-density height `2πe^{2a}`.
  - So the "uniform-in-δ Nyquist constant" (frontier open item) sits in `[2πe^{−3/4}, 2π]`.
- **Conjecture (L57).** For `0<η≤½` and `M≥1` there is `a₀` such that, for `a ≥ a₀`, Hodge(a) excludes every nontrivial zero `ρ₀ = β₀+it₀` with:
  - `β₀ > ½`, `8 ≤ t₀ ≤ (1−η)2πe^{2a}` and `mult ρ₀ ≤ M`;
  - ordinate separation `δ ≤ ½` from every zero other than `ρ₀` and `1−ρ̄₀`, and depth `β₀−½ ≤ δ/2`;
  - `12C log(t₀+1)/δ + 4 log(1/(β₀−½)) ≤ (π/2)η^{3/2}e^{2a}`.
  With the lattice law this determines the constant: 2π.
- **Kill attempts.**
  - *False?* The depth loss `log(1/δ₀)` is necessary. A pair's negativity is `O(δ₀²)` against a tail floor `exp(−ce^{2a})`, so shallower zeros are invisible, uniformly in any method with bounded symbols (Cauchy on the strip).
  - *Circular?* No.
  - *Known?* Corpus: `2πe^{2a−3/4}`. Literature: only CCM Cor. 3.8 (limit).
  - *Insignificant?* It closes the frontier item "determine the Nyquist constant".
  - Verdict: SURVIVES.
- **Paper proof.**
  1. Kernel `h = D_{γ₀}^{m}D_{γ₁}^{m}Φ_θ`, `θ = π/4−√η/2`, `γ₀ = t₀−iδ₀`, `γ₁ = γ̄₀`.
     - `ĥ` is entire and `(z−γ₀)^m(z−γ₁)^m ĥ = e^{zθ}Ξ`.
     - Minimum modulus on `|z−t₀| = 3δ/4`, using the lower semicircle path bound and `|Ξ(z̄)| = |Ξ(z)|`, gives `|ĥ(γ_j)| ≥ m_V(θ,t₀,δ/2)`.
  2. Test `f = N_{c₁,c₂,s}((h_{≤U}) ⋆ κ₂^{(w,t₀)})` with `U = a−η/8` and `w = s = η/16`.
     - `N(γ₀) = 1`, `N(γ₁) = v` aligns the pair phase; `|N| ≤ 1+3/(sδ₀)`.
  3. `Re W ≤ (2m)(−|X₀||X₁| + e(|X₀|+|X₁|) + e²) + (N_max ε B_w(1+t₀)²)²·24A₀log(t₀+3)`, where `e = εB_w(1+t₀)²` and `ε = expTail h ½ U`. Both factors are tail-sized at every other zero because of the bump.
  4. Hodge(a) gives `λ ≤ e(3+24N_max²A₀log)`, with `λ = m_V·t₀²·4w e^{−1/16}∫κ`.
  5. `landau_gain`: the exponent gap is `(π/2)η^{3/2}e^{2a}`. Contradiction.
- **L57 result [L]: the Nyquist constant is 2π.** Theorems `RHTower/LandauSharpOffLineExclusion`:
  - `hodgeIndex_excludes_offLine_below_landau`;
  - `hodgeIndex_forces_critical_line_below_landau` (the two-sided form: such a zero has `β₀ = ½`).
  Both are unconditional; axioms propext/choice/Quot.sound.
  - For `0<η≤½` and `M`, for all large `a`, Hodge(a) puts on the critical line every zero with `mult ≤ M` and `8 ≤ t₀ ≤ (1−η)2πe^{2a}` that satisfies:
    - ordinate separation `δ ≤ ½` from all zeros except itself and its mirror;
    - `|β₀−½| ≤ δ/2`;
    - `12C log(t₀+1)/δ + 4 log(1/|β₀−½|) ≤ (π/2)η^{3/2}e^{2a}`.
  - With `offLineLattice_weil_positive_iff` (blind exactly at density `a/π`, i.e. height `2πe^{2a}`), this determines the constant as 2π. The previous corpus horizon was `2πe^{2a−3/4}`.
- **Modules** (wired after `SharpWeilNearRadicalCount`; `lake build --old`; lint clean for these):
  - `RHTower/TiltedOffLinePairKernel`:
    - local factor of `Φ̂_θ` at any `gammaOf ρ` (`exists_tiltedPhi_local_factor_gammaOf`);
    - `pairKernel_spec`;
    - near-pair zero-freeness and the lower-semicircle path lemma;
    - `pair_circle_floor`;
    - minimum modulus on the symmetric disc `|z−t₀| ≤ 3δ/4` (`norm_divided_pair_ge`);
    - `offLine_pairKernel_package`.
  - `RHTower/LandauPairTest`:
    - pair phase alignment for general `s` (`pairC₁/pairC₂`, `|N| ≤ 1+4/(s|Im γ₀|)`);
    - the bump on the imaginary axis `|κ̂_w(iy)| ≥ 4we^{−w|y|}∫κ`;
    - the Landau test `N_{c,s}((h_{≤U})⋆κ₂)` with its Hodge-class properties;
    - `re_W_le_pair_add_window` (both factors tail-sized at other zeros);
    - `pairLandau_inequality`.
  - `RHTower/LandauSharpOffLineExclusion`: level bound, exponent balance, `N`-factor bound, level balance, and the final theorems.
- **Mechanism, compared with the corpus.**
  - No polar shift and no smooth truncation plateau: the polar-free bump carries both the pole constraint and the other-zero decay.
  - The only support cost is `w+s = η/8`.
  - The depth enters only through `log(1/|β₀−½|)` (the node symbol), which is necessary.
- **Verdict.** PROVED. The frontier item "determine the uniform-in-δ Nyquist constant" is closed at 2π, up to the unavoidable depth loss `log(1/δ₀) ≲ η^{3/2}e^{2a}`.

### L57 — The Weil–Toeplitz law: Weil positivity bounds the multiplicative Toeplitz matrix of the prime weights by `log N`. TRUE [L]
- **Question (from the open core).** Can a smooth element of the Weil cone exist? A density-only obstruction would decide it if it forced the density above what the prime-blind tests allow, or below.
- **Theorem [L]** `RHTower.weil_multiplicativeToeplitz_bound`. Let `lam` be any Weil-positive weight system (ζ's archimedean term, polar-constrained `C²` tests, every level). There is an absolute `C₀` such that for every `N ≥ 1` and every `c` supported in `[1,N]`:
  `2 Σ_{2≤n≤N} lam(n) n^{−½} Re Σ_m c(nm) conj c(m) ≤ (log N + C₀) Σ_m |c(m)|²`.
  - Equivalently, the `N×N` multiplicative Toeplitz matrix of `lam(n)n^{−½}` has top eigenvalue `≤ log N + C₀`.
- **Mechanism.**
  - Tests are resonators: narrow polar-free bumps `g_w(x − log m)` with `w = 1/(N+1)` and `g_w = ψ_w'' − ψ_w/4`.
  - Distinct `log m` with `m ≤ N` are `≥ 1/(N+1)` apart. So the autocorrelation meets the atom `log n` exactly on the multiplicative diagonal `m = nm'`: the prime side is an exact matrix.
  - The archimedean symbol satisfies `A(τ) ≤ log(1+|τ|) + 4` (vertical digamma bound). On the bump spectrum it is `≤ log(1/w) + ½ + w²τ²/2 + 4`.
  - The `τ²` term is paid by `w²‖g_w'‖²/‖g_w‖² ≤ K`, a scale-free profile constant obtained by integration by parts: `∫ψ''ψ = −∫ψ'²`.
- **Corollaries [L].**
  - `weil_twisted_density_bound`: for every completely multiplicative unimodular `χ`,
    `2 Σ_{nm≤N, n≥2} lam(n) Re χ(n)/(nm) ≤ (log N + C₀) Σ_{m≤N} 1/m`.
  - `weil_log_density_le`: `Σ_{nm≤N, n≥2} lam(n)/(nm) ≤ (½ + ε)(log N)²` eventually. In the logarithmic mean `Σ_{k≤N}(lam⋆1)(k)/k`, every Weil-positive system has density at most 1. The constant is sharp at `Λ`: `Σ_{k≤N} log k/k = ½log²N + O(1)`.
- **Attack.**
  - False? No. The prime side is exact, and the archimedean side is a pointwise upper bound on a positive spectral measure.
  - Circular? No zeros are used.
  - Known? Multiplicative Toeplitz and GCD matrices appear in Ω-results for `ζ` (Hilberdink; Aistleitner–Berkes–Seip; Bondarenko–Seip). I found no statement bounding them by Weil positivity, and none giving a universal upper density for Weil-positive weights. The corpus had only `cΛ` (L52).
  - Verdict: SURVIVES; modest.
- **Paper findings (same cycle) [P].**
  - **Regular rigidity.** If `D_w` continues meromorphically past the critical line, with finitely many poles in `Re s > ½`, none on the line, and polynomial growth, and if `Re D_w ≤ 0` on the line, then `w = 0`.
    - Proof: a two-bump test isolates `w(n)` at mass `1/ε` against `O(1)` pole terms. Equivalently, Herglotz with finite mass (`μ(ℝ) = 2π·res`), so `μ̂` is continuous and has no atoms.
    - So the tangent cone of `W` at `Λ` contains no regular direction. Every admissible direction is singular exactly on the critical line.
    - This generalizes MUST-357's light case to all regular heavy perturbations. Lean: not done; it needs a contour shift for general meromorphic Dirichlet series.
  - **Density window for smooth elements.** A smooth element (regular `D_u`, residue `r`) has full positivity `k_A + 2r cosh(x/2) − atoms ⪰ 0`.
    - Even prime-blind tests give `r ≥ r*` (about 0.8 from the Fejér test).
    - Odd prime-blind tests give an upper bound on `r` (the cosh pairing is `−ĝ(i/2)²` for odd `g`).
    - L57 gives `r ≤ 1`. So smooth elements, if any, have `r ∈ [r*, 1]`.
  - **Gaussian threshold (heuristic).** For a density-`r` regular Dirichlet series, `Var Re D(½+it) ≥ ½r² log T` on `[T,2T]` (Cauchy–Schwarz on `Σ|u|²/n`). Gaussian extremes over `T log T` samples are about `r log T`, against the allowance `A/2 ≈ ½ log T`. So generic smooth candidates need `r ≤ ½ < r*`; a smooth element would need sub-Gaussian upper tails.
  - The resonance method saturates at exactly `r ≤ 1`. Autocorrelations of length-`N` resonators give at most `(r/2) log N`: the `½` is `∫₀¹(1−y)dy`, which is optimal. `Λ` attains it.
  - So density-only resonance cannot see the Gaussian extremes. Deciding smooth elements needs structure beyond density.
- **Producer reading.** `Λ` saturates every resonance inequality of the Weil cone to leading order, with slack `(log(T/N) + 2γ) log N` against a main term of `(log N)²`. A producer must in particular certify `λ_max(T_N(Λ)) ≤ log N + O(1)` for the multiplicative Toeplitz matrix of `Λ(n)n^{−½}`. This is a finite-dimensional arithmetic operator inequality implied by RH, and its unconditional status is open.
- Module `RHTower/WeilPositivityMultiplicativeToeplitzBound.lean` (1079 lines). Built and wired after `WeilPositivityCharacterSpanHalfSpace`. Axioms: propext, Classical.choice, Quot.sound.
- **L57 correction (same day).** The "producer reading" above is wrong. `λ_max(T_N(Λ)) ≤ log N + O(1)` holds unconditionally and elementarily.
  - Schur test with `h(m) = m^{−½}`: the row sums give `m^{−½}(Σ_{d|m}Λ(d) + Σ_{n≤N/m}Λ(n)/n) = m^{−½}(log N + O(1))`, by `Σ_{d|m}Λ(d) = log m` and Mertens.
  - So the Weil–Toeplitz law is a Mertens-level necessary condition. `Λ` meets it without RH, and resonator tests (bumps at `log m`) never see the zeros.
  - Its content is only as a constraint on *other* weight systems: log-density `≤ 1`. It is not a producer target.

### L58 — "Lorentzian arithmetic" (user prompt: a field bridging spectral, algebraic and geometric facts). Bridge theorem [P]; Perron seed TRUE [L]; local test FALSE [P]
- **Bridge theorem [P, exact].** Take the level-`a` Weil form without its pole term, `Q₀(f) = ∫∫ f f̄ K₀`.
  - Its off-diagonal kernel is `−w(2|t|) − Σ Λ(n)n^{−½}δ_{±log n}`, with `w(t) = e^{−t/4}/(1−e^{−t})`: every entry is ≤ 0.
  - Adjoin the rulings `e_±(x) = e^{±x/2}` with the hyperbolic block `H = [[0,1],[1,0]]` and the coupling `B = [e₊ e₋]`. The result `I_ext = [[−Q₀, B],[B*, H]]` is **Metzler**: every off-diagonal coefficient is ≥ 0.
  - Its Schur complement over `H` is `−Q_full` (the pole term is `B H^{−1} B*`, i.e. the kernel `2cosh((x−y)/2)`).
  - Haynsworth inertia: `#pos(I_ext) = 1 + #neg(Q_full)`. So **Weil positivity at level `a` ⟺ the Metzler form `I_ext(a)` has exactly one positive eigenvalue** (Brändén–Huh Lorentzian signature, i.e. the Castelnuovo inequality).
- **Dictionary.**
  - Ample class = Perron vector of the Metzler form.
  - On the divisor lattice this is the critical Bost–Connes Gibbs vector `m^{−½}`.
  - Hodge index = second eigenvalue ≤ 0.
  - The Euler product enters twice: through `Λ ≥ 0`, and through `Σ_{d|m}Λ(d) = log m` (the height), which makes `m^{−½}` a Perron vector.
- **Seed theorem [L]** `RHTower.CriticalGibbs.gibbs_perron_polarization` (module `CriticalGibbsPerronPolarization`, 581 lines; axioms propext, Classical.choice, Quot.sound):
  - on `[1,N]`, the critical Gibbs vector has von Mangoldt Toeplitz Rayleigh quotient `log N − γ + o(1)` (`tendsto_gibbs_rayleigh`);
  - unconditionally, every vector has Rayleigh quotient `≤ log N + C` (`exists_vonMangoldt_toeplitz_le`, Schur).
  - Mechanism: `P(N) = Σ_{nm≤N}Λ(n)/(nm)` equals both `Σ_{k≤N} log k/k` (divisor reindexing) and `Σ_m S(⌊N/m⌋)/m` (Mertens sums). So `2P − (log N−γ)H` is a `1/m`-average of Mertens remainders, which is `o(H)` by a Cesàro lemma on the divisor lattice.
  - Reading: the polar constraint of the Weil form removes exactly the top eigen-direction of the prime correspondence, and γ is the defect of the Perron eigenvalue. On the lattice slice the decision is Mertens-level, not zero-level.
- **Local Lorentzian test: FALSE [P].** The signature is not local.
  - The archimedean-only extended form fails: `A` is negative near 0, and concentrated polar-free tests give a second negative direction of `Q_full` (L55).
  - Every single-prime form fails too: its symbol at `τ = 0` is `A(0) − 2log p·p^{−½}/(1−p^{−½}) < 0` (`≈ −8.7` for `p = 2`).
  - So Lorentzian closure cannot act additively over primes: sums preserve the signature only on a common nonpositive hyperplane, which is the L1/L2 failure. Any closure must act on the complete Euler product.
- **Open core of the field.** A multiplicative (Euler-product) realization of `I_ext` in which Lorentzian signature is produced by closure (products or limits of Lorentzian or stable objects). Candidate carrier: the Bohr-lifted Euler product `∏_p(1 − z_p p^{−s})^{−1}`, which is stable in the `z_p`. The gap is the passage from multivariate stability to the one-variable critical-line signature.

### L59 — Weil's criterion needs only nonnegative tests (Castelnuovo form). TRUE [P]; RH-equivalent reformulation
- **Linear-algebra lemma [P].** Let `A` be real symmetric with strictly positive off-diagonal entries. Then `A` has at most one positive eigenvalue ⟺ for all `x, y ≥ 0` with `xᵀAx > 0`, `(xᵀAy)² ≥ (xᵀAx)(yᵀAy)`.
  - (⇒) Restrict to `span{x, y}`. A 2×2 block with `a > 0` and `ac > b²` would be positive definite, giving two positive directions.
  - (⇐) The top eigenvector can be taken nonnegative (`|v|` has at least the Rayleigh quotient of `v`, since off-diagonals are ≥ 0). It is strictly positive: if `v_i = 0` then `(Av)_i = Σ_{j≠i}A_ij v_j > 0 = λ₁v_i`.
  - Let `q` be a second positive eigenvector, `q ⊥ p`. Then `x = p` and `y = p + εq ≥ 0` span a positive-definite plane, which violates reverse Cauchy–Schwarz.
  - Brändén–Huh prove this for nonnegative matrices, where every nonnegative vector is time-like. Here the diagonal is arbitrary (negative self-intersections are allowed), so the time-like condition `xᵀAx > 0` is needed.
- **Arithmetic application [P].** The extended Weil form `I_ext(a)` of L58 is Metzler with strictly positive off-diagonals: the archimedean jump density `w(2|t|) > 0` connects every pair of points, and the ruling couplings are `e^{±x/2} > 0`.
  - With L58's Haynsworth identity: **RH ⟺ at every level `a`, for all nonnegative `x = (f, α, β)` and `y = (g, α', β')` with `I_ext(x,x) > 0`: `I_ext(x,y)² ≥ I_ext(x,x) I_ext(y,y)`.**
  - Weil's criterion is thus decided by pairs of nonnegative test functions. The sign-changing directions that detect off-line zeros are produced inside the span of two positive tests.
- **Attack.**
  - False? No: the lemma is elementary, and the sign structure is L58's.
  - Circular? It is an equivalent reformulation.
  - Known? I found no literature statement. Brändén–Huh cover nonnegative matrices and volume polynomials; the Weil-criterion literature uses signed tests.
  - Verdict: SURVIVES as a reformulation; significance moderate. It localizes RH content to "Castelnuovo on pairs of positive functions", the form in which Lorentzian and log-concavity methods operate.
- **Single positive tests are RH-blind [P, heuristic].** For `g ≥ 0`, the pole term `2⟨g,e₊⟩⟨g,e₋⟩ = 2∫(g⋆g̃)(t)cosh(t/2)` dominates off-line contributions, and narrow bumps are controlled by the archimedean diagonal. So pairs, not single tests, carry the content.
- **Lean.** Not started. The lemma needs Perron–Frobenius-free spectral linear algebra (mathlib has the Hermitian spectral theorem) and a Courant–Fischer step. The arithmetic side is the L58 sign structure.

### L60 — Perron–Frobenius split of Weil positivity: one bound state plus a 2×2 ruling condition. TRUE [P]
- **Setting.** `Q_full = Q₀ + 2|c⟩⟨c| − 2|s⟩⟨s|` on `L²(−a,a)`, with `c = cosh(x/2)`, `s = sinh(x/2)`. The pole term `2⟨f,e₊⟩⟨f,e₋⟩` splits into its even and odd parts.
  - `Q₀` is a Z-form: its off-diagonal kernel is `−w(2|x−y|) − Σ Λ(n)n^{−½}δ_{±log n} ≤ 0`, strictly negative off the diagonal. So `−Q₀` is Metzler and irreducible.
- **Facts [P].**
  1. (Unconditional) The ground state of `Q₀` is simple, strictly positive and even: Perron–Frobenius, since `|f|` does not raise the energy of a Z-form. For `a ≳ 1`, `Q₀(c) < 0` (the prime sum dominates by Chebyshev), so `#neg(Q₀) ≥ 1`.
  2. `|#neg(Q₀) − #neg(Q_full)| ≤ 1`, because the pole term has signature `(1,1)`.
  3. (Haynsworth on `I_ext` with the `Q₀` block) `#neg(Q_full) = #neg(Q₀) + #pos(M₂) − 1`, where `M₂ = H + [⟨e_i, Q₀^{−1} e_j⟩]` is the 2×2 ruling resolvent matrix.
- **Theorem [P].** RH ⟺ at every level `a`, both hold:
  - (i) `Q₀(a)` has exactly one negative eigenvalue (one bound state);
  - (ii) `M₂(a) ⪯ 0`.
- **Nodal form of (i) [P].** For a Z-form, `λ₂ < 0` ⟺ some two disjointly supported nonnegative `f, g` span a negative-definite plane.
  - (⇒) Take the positive and negative parts of the second eigenfunction. With `Q₀(f^±) = λ₂‖f^±‖² + c` and `c = Q₀(f⁺,f⁻) ≤ 0`, the Gram determinant is `λ₂²pq + λ₂c(p+q) > 0` and the trace is `< 0`.
  - So (i) ⟺ **DPC**: `Q₀(f,g)² ≥ Q₀(f)Q₀(g)` for all disjointly supported `f, g ≥ 0` with negative self-energies. Every quantity here is a positive-function integral, and the interaction `−Q₀(f,g) = ∫∫ f g ν`, with `ν = w(2|·|) + prime atoms`, is ≥ 0.
- **Content of (i) alone.** (i) implies `#neg(Q_full) ≤ 2` at every level: at most one off-line quadruple is visible per level. That is weaker than RH but still RH-strength-like. RH itself sits in the 2×2 condition (ii), which is a PNT-level balance (`vvᵀ/|μ₀|` against `H`, both `O(1)`).
- **CCM (S1) check.** CCM's `QW_λ` includes the pole terms `F̂(±i/2)`, so it is not a Z-form and Perron–Frobenius does not give its ground-state simplicity. The pole-free ground state is simple, positive and even unconditionally, but it is the prime Perron mode, not the near-radical vector CCM need.
- **Attack.**
  - Circular? Parts (i) and (ii) are an exact equivalent split.
  - New? I found no statement of RH as "one bound state of the pole-free Weil operator plus a 2×2 ruling condition", nor of the DPC form.
  - Verdict: SURVIVES as a reformulation. The positive-geometry target is DPC: reverse Cauchy–Schwarz for disjoint positive pairs, a statement about positive measures only.
- **Tested, fails for the log-concavity shortcut.** For `w(t) = exp(−t/4)/(1−exp(−t))`, `(log w)'' = exp(−t)/(1−exp(−t))² > 0` on `t > 0`. Thus `w(2|t|)` is strictly log-convex on the positive ray and singular at zero; the prime atoms also do not supply a log-concave density. The proposed Karlin-type TP₂ argument therefore does not establish DPC. This rejects that sufficient-condition argument, not every possible proof of DPC.

### L61 — Weil positivity pins the log-density at Λ's: no supersystem of Λ has positive excess. TRUE [L]
- **Theorem [L]** `RHTower.weil_supersystem_excess_small`. If `lam ≥ Λ` pointwise and `lam` is Weil-positive (ζ's archimedean term, polar-constrained `C²` tests, every level), then `Σ_{n≥2, nm≤N}(lam(n) − Λ(n))/(nm) = o((log N)²)`.
  - The L57 ceiling `(½+ε)log²N` meets the L58 floor for `Λ`: `P(N) ≥ (½−ε)log²N`, lemma `eventually_gibbsEnergy_ge`.
- **Corollary [L]** `RHTower.vonMangoldt_add_const_not_weilPositive`. For every `c > 0`, the weights `Λ(n) + c` are not Weil-positive.
  - This is a heavy perturbation: `Σ c n^{−½} = ∞`, outside MUST-357's light rigidity.
  - Proof: the excess `c Σ_{nm≤N}1/(nm) ≥ (c/8)log²N`, obtained by restricting to `n, m ≤ √N`.
- Module `RHTower/WeilPositivityLogDensityMaximality.lean`. Built and wired; axioms propext, Classical.choice, Quot.sound.
- **Reading.** In log-density, Λ is maximal in the Weil cone among its supersystems. The downward direction (`Λ − c`, density below 1) is not reached by density arguments; it needs regular rigidity (HF-F54, paper).

### L62 — Two producer shortcuts tested: arithmetic Markov gap with positive slack and adelic Pitt log-convexity (averaged only). SHORTCUTS REJECTED [P]; survivors recorded
- **(A) Arithmetic Markov chain.** Doob-transform the Metzler form `−Q₀` by its positive ground state `φ₀` (eigenvalue `λ₀`, with `|λ₀| ≍ e^{a}`). This gives a conservative jump chain on `[−a,a]` with rates `ν(y−x)φ₀(y)/φ₀(x)`, where `ν` = archimedean jumps plus prime-power jumps.
  - Part (i) of L60 (one bound state) ⟺ `gap(chain) ≥ |λ₀|`.
  - **Obstruction to positive slack.**
    - Upper side: the polar-free near radical (dimension `≥ (2−η)e^{2a}`, energy `≤ exp(−η²e^{2a}/(300a))` times its norm, from L35/L45) contains a vector orthogonal to `φ₀`. Since `Q₀ = Q_full` on polar-free vectors, `λ₂(Q₀) ≤ exp(−c e^{2a})`, unconditionally.
    - Lower side: interlacing gives `λ₂(Q₀) ≥ λ₁(Q_full)`.
    - These imply only the one-sided bound `gap ≤ |λ₀| + exp(−c e^{2a})`. Interlacing supplies no unconditional matching lower bound near `|λ₀|`: the sign of `λ₁(Q_full)` is the unresolved issue. A bound with a fixed positive margin above `|λ₀|` is excluded. An exact curvature, coupling or other identity proving `gap ≥ |λ₀|` is not excluded by these estimates and remains unproved. In particular, the previously stated two-sided `O(exp(−c e^{2a}))` error does not follow.
  - **Survivor [P].** Unconditionally, the pole-free Weil operator has a second eigenvalue `λ₂(Q₀) ≤ exp(−c e^{2a})`. One bound state is exactly the no-slack statement `λ₂(Q₀) ≥ 0`.
- **(B) Adelic Pitt / log-uncertainty.** Beckner's logarithmic uncertainty constant is `ψ(¼) − log π = A(0)`, exactly the archimedean Weil symbol at 0. Its proof differentiates Pitt's inequality at `α = 0`.
  - Globally: for real Fourier-self-dual `F` with `F(0) = 0`, `P(α) = ∫_{ℚ*\𝔸*} |x|^{−2α}|E(F)|² d*x` is a moment generating function in `α`, hence log-convex (Hölder).
  - By Plancherel on `Re s = ½+α` it equals `∫|ξ(½+α+it)|² |F̃/G(½+α+it)|² dt`, with `G(s) = π^{−s/2}Γ(s/2)`. Tate's local FE makes it even in `α`, so `P` is nondecreasing on `[0, ½)` unconditionally.
  - This is the Hardy–Ingham–Pólya convexity of mean values combined with the functional equation: known type. The RH-equivalent statement is the *pointwise* monotonicity `|ξ(σ+it)| ↑` in `σ > ½`.
  - **Kill (localization).** Localizing the weight at `t₀` with width `1/√T` costs a factor `e^{2Tα²}`. At second order this detects only off-line zeros with `δ ≲ 1/√T`, below the localization width. So the averaged monotonicity is blind: the individual-zeros gate.
  - **Survivor.** Weil positivity is an adelic log-uncertainty principle (Burnol's conductor operator). Its local constants are Beckner's, and the global form sums them. The averaged global inequality is unconditional; RH is its pointwise version.

### L63 — Constant-shift rigidity: the line Λ + ℝ meets the Weil cone at most in Λ. PROVED [Lean]
- **Conjecture.** The downward half of regular rigidity (HF-F54), at the central point `τ = 0`, holds for deviations with a *pole at s = 1*.
  - If `Σ_{2≤n≤x}(lam(n)−Λ(n))n^{−½} = 2κ√x + A log x + B + o(1)` and `lam` is Weil-positive, then `B ≤ 0`, whatever `κ` and `A` are.
  - `B` is the regularized central value `D_{lam−Λ}(½)`.
  - It can fail if the √x slope leaks into the energy at order `S`.
- **Kill attempt.** The slope contributes `2κ ∫(φ∘log)'√t = −2κφ(0) − κ∫₀^L φe^{u/2}`, and each term is `≍ S`.
  - The polar constraint turns `∫φe^{u/2}` into `−∫φe^{−u/2} = −2φ(0) + O(sup|φ'|)`.
  - So the two `≍ S` terms cancel exactly, leaving `O(|κ| sup|φ'|)`, bounded uniformly in `S`. The conjecture survives.
- **Proof [Lean, `RHTower.WeilPositivityConstantShiftRigidity`].**
  - `polar_mertens_constant_nonpos_of_weilAtomSymbol_nonneg` (general theorem).
  - `vonMangoldt_sub_const_not_weilPositive`: `κ = −c`, `B = c(1−ζ(½)) ≥ 2c`, with `ζ(½) := lim(Σ_{n≤N} n^{−½} − 2√N) ≤ −1` proved from scratch by AM–GM telescoping (`halfPowerConstant`).
  - `eq_zero_of_vonMangoldt_add_const_weilPositive`: combined with L61 (`Λ + c ∉ W` for `c > 0`, density ceiling), `Λ + c ∈ W ⇒ c = 0`.
  - Axioms: standard only.
- **Meaning.** Both directions along constants are closed by different mechanisms:
  - upward, the Toeplitz density ceiling (resonance, L57/L61);
  - downward, the central Mertens constant (spread radical tests whose zero side is super-exponentially small unconditionally).
  - `Λ` is two-sided extreme in the constant direction, unconditionally, so a producer must be exact in that direction.
- **Not settled.** Whether `Λ` is extreme in *every* regular direction, i.e. the full HF-F54. The next step is twisting the spread radical test to reach `Re D_w(½+iτ₀) ≤ 0` at every `τ₀`.

### L64 — Summable-perturbation rigidity: Weil positivity fixes every prime weight. PROVED [Lean]
- **Conjecture.** For every nonzero `w` with `Σ|w(n)|n^{−½} < ∞`, `Λ + w ∉ W`.
  - This is regular rigidity (HF-F54) in its absolutely convergent case.
  - It can fail if `P_w(τ) = Σ 2w(n)n^{−½}cos(τ log n)` is `≤ 0` everywhere for some `w ≠ 0`, i.e. a nonzero Dirichlet polynomial/series with nonpositive real part on the whole critical line.
- **Kill attempt.** None. A nonzero `P_w ≤ 0` is impossible, because two-point resonators read off each coefficient with either sign. The conjecture survives.
- **Proof [Lean, `RHTower.WeilPositivitySummablePerturbationRigidity`].**
  1. `integral_weilAtomSymbol_vonMangoldt_add_le`: energy `≤ 2π‖W(f)‖ − ∫|h|²P_w + tail`.
  2. `eq_zero_of_perturbationSymbol_nonpos`: two-point resonators `g(x) ± g(x − log n₀)`, built from L57's narrow polar-free bumps, see only the atom `n₀`, with sign `±`.
  3. `vonMangoldt_add_violation_of_concentration`: the corpus's spread radical tests, concentrated where `P_w > 0`, have zero side `O(S^{10}e^{−S})`.
- **Theorems.**
  - `vonMangoldt_add_summable_not_weilPositive`.
  - `eq_vonMangoldt_of_weilPositive_of_summable_sub`: `lam ∈ W` and `lam − Λ ∈ ℓ¹(n^{−½})` ⇒ `lam = Λ`.
  - `vonMangoldt_update_not_weilPositive`: changing a single weight `Λ(n₀)` by any `c ≠ 0` breaks positivity.
  - Axioms: standard only.
- **Meaning.** This is the "exact primes" gate as an unconditional theorem.
  - With `summable_weights_weilAtomSymbol_not_nonneg` (corpus), `W ∩ (Λ + ℓ¹) ⊆ {Λ}` and `W ∩ ℓ¹ = ∅`.
  - Together with L61/L63 (constant shifts, which are not in ℓ¹), Λ is isolated in W along every direction tested so far.
- **Survivor / next conjecture (L65).** *W is at most a point: W ⊆ {Λ}.*
  - Open core: a Weil-positive `lam` with `lam − Λ ∉ ℓ¹`, for example with `Σ_{n≤x}(lam−Λ)(n)n^{−½}` growing but not of polar-Mertens type.
  - The obstruction mechanism for such `w` needs `P_w` as a distribution. Its positivity somewhere would follow from a "no nonpositive almost-periodic distribution with frequencies `{log n}` and zero mean" lemma, plus concentrated radical tests.

### L65 — "W is at most a point" (uniqueness of the positive completion). OPEN; partial results
- **Conjecture.** `W ⊆ {Λ}`.
  - The prime weights are the unique positive completion of the ζ-archimedean place with its pole. Then RH ⟺ W ≠ ∅.
  - The analogy is uniqueness in Minkowski's problem, which is what drives Hilbert's positivity proof.
- **Proved.**
  - L61/L63: constants.
  - L64: the whole ℓ¹(n^{−½}) neighbourhood.
  - Corpus: twists, scalings.
  - HF-F61: W is compact, since `|lam(n)| ≤ √n(log n + C₀)`.
- **Discrete case (paper, classical input).** Suppose the positive spectral measure `ν_lam` (the Bochner–Schwartz transform of the lam-Weil distribution) is discrete, so that its Hadamard product is of finite order.
  - Then `ζ_lam = exp Σ lam(n)n^{−s}/log n` is a Dirichlet series with ζ's gamma factor, pole and functional equation.
  - Hamburger's theorem (1921) gives `ζ_lam = ζ`, hence `lam = Λ`.
- **Open core.** Non-discrete `ν_lam`: a positive even measure with an absolutely continuous part whose Fourier transform is ζ's archimedean-plus-pole distribution plus atoms on `{±log n}`.
  - This is a "Hamburger theorem for positive Fourier pairs".
  - Frequency concentration fails here: the radical factor `|Ξ|²` blurs log-frequencies at scale 1, while `|w(n)|` can be as large as `√n log n`.
- **Dual form (paper, from compactness).**
  - `W = ∅` ⟺ some finite positive combination `μ = Σα_i[f_i]` of polar tests has `arch(μ) + Σ_n b_n|c_n(μ)| < 0`, with `b_n = √n(log n + C₀)`.
  - This is a criterion for "some positive completion exists" in which no primes appear.

### L66 — The Minkowski-problem route (user steer, 2026-09-28). Exact dictionary + mechanism audit [P]
- **Dictionary (exact).** Take normals `u(x) = (e^{x/2}, e^{−x/2})` on the hyperbola, with `x` the log scale.
  - The polar constraint `F̂(±i/2) = 0` is exactly Minkowski's closure condition `∫ f u = 0`.
  - The rulings `e^{±x/2}` are the support functions of points, i.e. translations.
  - Polar-free tests are exactly the curvature measures `f = h'' − h/4` of compactly supported support perturbations `h`, with `h` unique. Solvability ⟺ closure, which is the 2-D Minkowski theorem here.
  - L57 resonators are narrow caps at the normals `log m`.
  - The covolume of such coconvex bodies is `½∫(h'² + h²/4)`, with symbol `τ² + ¼`: the factor `s(s−1)` of `ξ`.
- **Mechanism audit.**
  1. **Brunn–Minkowski / Prékopa** (log-concave volume ⇒ Lorentzian Hessian).
     - *Spectral-domination no-go [P]:* if `Q_Λ = Σ Q_i` with each `Q_i ≥ 0`, then each spectral measure satisfies `μ_i ≤ ν_ζ`. So every positive summand is supported on the zeros and is annihilated (up to truncation) by Riemann's `Φ`-radical tests.
     - Convexity criteria (Pólya, Koldobsky intersection bodies, Brunn sections) yield absolutely continuous spectra and cannot be summands.
  2. **Alexandrov mapping lemma** (uniqueness + properness + openness ⇒ existence).
     - Properness holds: W is compact (HF-F61).
     - Uniqueness holds in every tested direction (L61, L63, L64; L65 conjecture).
     - Openness fails at ζ. The FE forces `Re ξ'/ξ = 0` on the line (critical completion).
     - Finite-perturbation Beurling rigidity [P]: a finite even measure `β` supported away from 0 with `β̂ ≤ 0` vanishes, since a positive-definite distribution vanishing near 0 is 0. So there are no slack completions near ζ, even with prime positions moved.
     - At a finite level `a`, under RH, Λ is interior to `W_a` (margin about `e^{−ca}`). So the continuity method runs in `a`.
  3. **Flat-body limit.** Vacuous: level-`a` positivity sees only `n ≤ e^{2a}`, so approximants agree with Λ at every level.
- **Surviving core (L67 target).** *No first touching*: there is no level `a*` at which `Q_{Λ,a*} ⪰ 0` has a kernel.
  - A kernel vector `f*` is a flat (degenerate) Minkowski solution. Equivalently, every positive-definite extension is supported on the zeros of `f̂*` (exponential type `a*`): a Gauss quadrature of ζ's Weil functional on `PW_{2a*}`.
  - Density alone does not exclude it: nodes of linear density with masses growing like `log t` can reproduce the arch singularity.
  - This is the Krein-degeneracy question in polytope form. The next step is to exclude it using the arithmetic (prime atoms at `log n`).

### L67 — Beurling rigidity: the positive completion of ζ's archimedean place has no nearby deformation. PROVED [Lean]
- **Conjecture (from L66).** In the Minkowski/Alexandrov scheme, openness would need Weil-positive completions near Λ with prime atoms moved or added at arbitrary real positions (Beurling primes).
  - Claim: none exist.
  - For every finite signed measure `μ₁ − μ₂` carried by `[ε, ∞)`, Weil positivity of `S_Λ − C_{μ₁} + C_{μ₂}` forces `μ₁ = μ₂`.
- **Proof [Lean, `RHTower.WeilPositivityBeurlingPerturbationRigidity`].**
  1. Concentration for any bounded continuous perturbation symbol, using spread radical tests.
  2. Prime-blind extraction: probes supported in `[−ε/4, ε/4]` see no atoms, so `P ≤ 0` ⇒ `P ≡ 0`.
  3. Fourier uniqueness: the symmetrization `μ + (−)_*μ` has characteristic function equal to the cosine symbol (`Measure.ext_of_charFun`).
- **Theorems.**
  - `vonMangoldt_sub_measure_weilPositive_eq`.
  - `vonMangoldt_move_atom_not_weilPositive`: moving one atom anywhere breaks positivity.
  - Axioms: standard only.
- **Meaning.** Alexandrov's continuity step is unavailable at ζ, even among generalized primes.
  - The Minkowski route's continuity parameter must therefore be the level `a` (finite-level interiority), which reduces to L7/L10.
  - This strengthens L64 (fixed positions, summable weights) to arbitrary positions and continuous mass, with a cleaner proof (Fourier uniqueness instead of resonators).

### L68 — Minkowski split: existence reduces to finite levels. PROVED [Lean]
- **Theorem [Lean, `RHTower.WeilPositivityFiniteLevelExistence`].**
  - `exists_weilPositive_iff_forall_level`: a Weil-positive weight system exists ⟺ every finite level `A` admits a system Weil-positive up to `A`.
  - Level-wise box `|lam(n)| ≤ √n(log n + C₀)` (via the refactored single-level `weil_multiplicativeToeplitz_bound_at`); Tychonoff; affine energies.
  - Paper remark (not in Lean, since it is conditional on the open uniqueness conjecture): if W ⊆ {Λ}, then RH-positivity of Λ ⟺ finite-level existence.
  - Axioms: standard only.
- **Meaning.** This is exactly Minkowski's existence/uniqueness structure for ζ.
  - Existence: a finite-level Krein problem with free prime weights.
  - Uniqueness: a Hamburger-type rigidity for positive Fourier pairs. Known along every summable, constant and finite-measure perturbation (L61, L63, L64, L67).
- **Open.** Both halves.
  - Existence at level `A` with free weights: is the feasible region `W_A` fat at finite `A`?
  - Uniqueness for non-finite perturbations.

### L69 — Regular rigidity: oscillating (non-summable) perturbations of Λ. PROVED [Lean]
- **Theorem [Lean, `RHTower.WeilPositivityRegularPerturbationRigidity`].**
  - `vonMangoldt_add_eq_zero_of_symbol`: if the atoms of `w` pair with tests through a continuous symbol `P` of linear growth, then Weil positivity of `Λ + w` forces `w = 0`.
    - Concentration gives `P ≤ 0`.
    - Prime-blind probes give `P ≡ 0`.
    - Two-point resonators give `w(n) = 0`.
  - `vonMangoldt_add_oscillating_eq_zero`: weights `c·b` with bounded partial sums `Σ_{2≤k≤n} b(k)`. The symbol is the absolutely convergent Abel series `2Σ B(n)(g_τ(n) − g_τ(n+1))`.
  - `vonMangoldt_add_chiFour_weilPositive_eq_zero`: `Λ + cχ₋₄` Weil-positive ⇒ `c = 0`.
  - Axioms: standard only.
- **Meaning.** Uniqueness (L65) now holds on:
  - ℓ¹ perturbations (L64);
  - finite measures at any positions (L67);
  - constants (L61/L63);
  - all bounded-partial-sum perturbations, i.e. every real non-principal character and `(−1)^n`, among others (L69).
- **What remains open for uniqueness.**
  - Perturbations with growing partial sums that are not polar-Mertens type (e.g. `B(x) ≍ x^θ`, `0 < θ < ½`, irregular).
  - Irregular deviations of prime-number-theorem type.

### L70 — The existence half is prime-blind archimedean positivity, and it only sees low frequencies. CONJECTURE [P]
- **Duality [P].** By L68 and Farkas with the level-wise box:
  - `W_A ≠ ∅` ⟺ PBAP_A: `arch(Φ) ≥ 0` for every positive-definite combination `Φ = Σ α_i φ_{f_i}` of polar level-`A` tests with `Φ(±log n) = 0` for `2 ≤ n ≤ e^{2A}`.
  - (Box form: `arch(μ) + Σ b_n|c_n(μ)| ≥ 0`. The exact prime-blind version is the limit.)
  - No primes and no zeros appear: only the ζ archimedean symbol `A(τ) = Re ψ(¼+iτ/2) − log π` and the set `{log n}`.
- **Explicit-formula reading.** For prime-blind polar `Φ`, `Σ_ρ Φ̂(γ_ρ) = arch(Φ)` identically.
  - Since `A(τ) > 0` for `|τ| > τ* ≈ 6.3`, a prime-blind test with spectrum above `τ*` has positive zero-sum whatever the zeros are.
  - So prime-blind tests cannot see off-line zeros at large height, and PBAP is a low-frequency (small-height) statement.
  - Negativity needs spectral mass in `|τ| < τ*` while vanishing at `log 2, log 3, …`. Near `u = 0` there are no constraints, but there Weil positivity past √2 (corpus, margin 1/10) applies.
- **Conjecture L70.** PBAP_A holds for every `A`, so W ≠ ∅ unconditionally.
- **Dichotomy.**
  - If L70 holds, then RH ⟺ uniqueness (W ⊆ {Λ}), and ¬RH would produce an irregular Weil-positive system `lam* ≠ Λ` with ζ's archimedean data (not ℓ¹, not bounded-partial-sum; L64/L67/L69).
  - If L70 fails, RH fails, witnessed by an explicit prime-blind positive-definite function with negative archimedean energy.
- **Open core.**
  - A quantitative uncertainty principle: positive-definite functions vanishing on `{±log n}` cannot put enough spectral mass below `τ*` relative to the `A`-weighted mass above.
  - The danger is internal cancellation: combinations of large-support tests whose autocorrelations cancel at each `log n`.
- **Relation to the corpus.** L20 (visible-unit completions) and L8 (prime-exact completions) study prescribed visible weights. Free visible weights (existence) are new.

### L71 — Regular rigidity for growing oscillations (partial sums `O(n^θ)`, `θ < ½`). PROVED [Lean]
- `vonMangoldt_add_oscillating_eq_zero` now takes `|Σ_{2≤k≤n} b(k)| ≤ K n^θ` with `θ < ½`. The Abel series converges because `Σ n^{θ−3/2} < ∞`.
- Covers growing perturbations such as `c χ(n) n^{θ'}` (`θ' < ½`), whose size `n^{θ'}` is far from summable against `n^{−½}`.
- Remaining uniqueness gap: partial sums of size `≳ √n`, other than the polar (constant-shift) type handled by L63.
- Module updated in place: `RHTower.WeilPositivityRegularPerturbationRigidity`. Axioms: standard.

### L72 — Attempted PBAP counterexample (far polar corrections). FAILS; the positive reason is recorded [P]
- **Attempt.** Take `f = f₁ + εf₂ + ε'f₃`, with:
  - `f₁` a low-frequency bump in `|x| < ¼log 2`, non-polar, with `arch(f₁) < 0` (the corpus Fejér test);
  - `f₂`, `f₃` tiny corrections at `x ≈ ±A` that restore both polar moments. The shifts amplify `e^{±x/2}` by `e^{A/2}`, so `ε, ε' ≈ e^{−A/2}` suffice.

  Then `arch(f) ≈ arch(f₁) < 0`. If `Φ = φ_f` could also be made prime-blind, Weil positivity would fail for every weight system, and RH would be false.
- **Why it fails.** The cross-correlation `C = f₁ ⋆ f̃₂`, at lags near `A`, inherits the smoothness of `f₁` (scale about 0.35).
  - Prime-blindness demands `C(log n) = 0` at all `n` in that window, with spacing `e^{−A}` far below 0.35. This forces `C ≈ 0` on the window.
  - Polarity forces the Chebyshev-weighted mass `∫ C(u) e^{u/2} du ≈ −(f̂₁(−i/2))²`, which is nonzero.
  - Contradiction. Far corrections cannot restore polarity while staying invisible to the integers.
- **Positive insight [P].** Prime-blind archimedean positivity is protected by the density `e^u` of `{log n}`.
  - The integers are dense enough to see the polar (`e^{u/2}`) moment of any smooth far cross-correlation.
  - This is the pole/Chebyshev coupling in dual form: vanishing on `{log n}` and the polar constraint together pin the large-lag structure of prime-blind positive-definite functions.
- **Next.** Turn this into a quantitative lemma: for positive-definite `Φ` vanishing on `{±log n}` with `∫Φ cosh(u/2) = 0`, bound `∫_{|u|>U} |Φ| cosh(u/2)` by the smoothness of `Φ`. That would reduce PBAP to bounded lags, i.e. to a finite-level statement.

### L73 — The Minkowski reformulation of RH (conditional on the uniqueness half). [P]
- **PBAP is a fixed, zeros-free, primes-free statement.**
  - PBAP_A says: for every positive-definite combination `Φ` of polar level-`A` tests with `Φ(±log n) = 0` for `n ≤ e^{2A}`, `∫ A(τ) Φ̂(τ) dτ ≥ 0`, where `A(τ) = Re ψ(¼+iτ/2) − log π`.
  - It involves only the Γ-factor and the set `{log n : n ≥ 2}`, the logarithms of all integers (not just the primes).
  - RH ⇒ PBAP (Λ is a positive completion). By L68 and the duality of L70: PBAP (all `A`) ⟺ W ≠ ∅.
- **Prime-blind tests never see off-line zeros.** For prime-blind polar `Φ` the explicit formula reads `Σ_ρ Φ̂(γ_ρ) = arch(Φ)`, a quantity independent of where the zeros are.
  - So if PBAP holds (a fixed fact), no prime-blind test detects any off-line zero at any height.
  - If PBAP fails, RH fails, witnessed without zeros or primes.
- **Reformulation.** Given uniqueness (W ⊆ {Λ}; proved along summable, finite-measure, constant and `O(n^θ)`-oscillating directions, L61–L71):

  **RH ⟺ PBAP.** The archimedean (Γ-factor) Weil form is nonnegative on positive-definite polar functions vanishing at the logarithms of the integers.
  - The primes disappear. They re-enter only through the uniqueness half, a Hamburger-type rigidity (the integer positions `log n` force the weights to be Λ).
- **No free lunch.** Under uniqueness, PBAP is exactly as hard as RH.
  - The Minkowski route therefore splits RH into a primes-free positivity problem (existence) and a Fourier-rigidity problem (uniqueness).
  - The analogue of the polytope theory: existence by variational/compactness methods, uniqueness by a Brunn–Minkowski-type equality case.
- **Status.** L68 formal (existence reduces to finite levels). Uniqueness formal in all regular directions (L63, L64, L67, L69, L71). PBAP open; the far-correction counterexample is blocked by integer density (L72).

### L74 — Universal near-radical: no weight system is Weil-positive with slack. CONJECTURE with proof sketch [P-sketch]
- **Claim.** For every `ε > 0` and every weight system `lam`, some polar test has `Q_lam(f) < ε‖f‖²`. Equivalently, `σ_pb := inf{arch(Φ)/(2πΦ(0)) : Φ prime-blind polar positive-definite} ≤ 0`.
  - With RH, `σ_pb = 0`. Every positive completion of ζ's archimedean datum is critical.
  - In Minkowski terms, the Γ-datum is degenerate (like data on a great subsphere), and all its solutions are flat.
- **Mechanism.**
  - For a prime-blind polar combination `Φ = Σ α_i φ_{f_i}`, the energy is weight-independent: `Σα_i Q_lam(f_i) = arch(Φ) = 2π Re W_ζ(Φ)` (zero side).
  - So a prime-blind combination of near-radical tests of `Q_Λ` is near-null for every `lam` simultaneously: a universal near-radical.
- **Sketch of existence.**
  - Let `V` be the level-`a` near radical of `Q_Λ` (dimension `≍ 2e^{2a}`, L35). Prime-blindness is `⟨G, M_n⟩ = 0` for a PSD Gram matrix `G` on `V`, with `M_n` the lag-`log n` autocorrelation forms, `n ≤ e^{2a}`.
  - By Gordan's alternative, a nonzero PSD `G` exists unless some `Σ c_n M_n` is positive definite on `V`.
  - `tr(P_V τ_{log n}) ≈ 0`: autocorrelations at nonzero lags average out over a large nearly translation-invariant space. So `tr(Σ c_n M_n) ≈ 0`, and no such combination is positive definite.
  - Hence a prime-blind PSD `G` exists, with `arch/mass ≤ exp(−c e^{2a})`.
- **Why the naive routes fail.**
  - Mixing concentrated radical tests blurs log-frequencies at scale 1 (radical autocorrelation), so mixtures are not prime-blind.
  - Small-support probes are prime-blind but not radical.
  - Exact prime-blindness needs the Gordan/trace argument on the near radical.
- **Consequences.**
  - Refutes the scenario "prime-blind slack ⇒ slack completions ⇒ uniqueness fails".
  - Shows that existence (PBAP) can never be proved by slack/openness (consistent with L66/L67).
  - The Weil-positive set W, if nonempty, consists only of critical points.
- **Status.** Sketch; the trace approximation and the near-radical structure need quantitative control. Lean: open (needs the L35 near-radical as a subspace plus a finite Gordan lemma).
- **L74 refinement (same session).**
  - The naive proof ("slack ⇒ the smoothed perturbation symbol `T_w ≤ −ε` everywhere ⇒ contradiction with mean zero") fails. `T_w` may carry huge positive mass in `1/S`-neighbourhoods of the zeros of ξ; the box allows `|T_w| ~ e^{2S}`, and mean zero is then consistent (`N(X) ≍ X log X ≫ εX`). Structurally, `ν_lam = (1−θ)ν_ζ + ρ` with `ρ ≥ ε` is not excluded by averaging.
  - Such slack completions exist iff `σ_pb > 0`. Testing `ρ` on prime-blind polar `Φ` gives `θ·arch(Φ) ≥ ε·Φ(0)`.
  - **Precise open core.** Is the Toeplitz form `g ↦ ∫ |B̂ ĝ|² T_c` (radical weight `|B̂|²`, `T_c = Σ_{n≤e^{2a}} c_n cos(τ log n)`) indefinite on `PW_{a−R}` for every `c ≠ 0`?
    - If yes, Gordan gives prime-blind radical combinations at every level, so `σ_pb = 0` and no slack points exist.
    - If no, the definite `T_c` is an explicit prime-weight perturbation that could carry slack.
  - The difficulty: `T_c` oscillates faster (frequencies up to `2a`) than the resolution `1/(a−R)` of `PW_{a−R}`.

### L75 — Weil positivity forces a pole: sparse weight systems are never Weil-positive. PROVED [Lean]
- **Conjecture (from L72).** The far-correction attack on PBAP (L72) fails on the integers because of their density. It should succeed exactly when the atoms are sparse. Then every Weil-positive completion of ζ's archimedean datum must carry atoms of prime-number-theorem density, i.e. a pole.
- **Mechanism: the polar constraint is asymptotically free on the frequency side.**
  - The corrected test is `f_X = ψ − c_X(ψ(·−X) + ψ(·+X))/2`, with `c_X = 1/cosh(X/2)` and `ψ` the corpus Fejér test (support `[−0.34, 0.34]`, `∫|ψ̂|²A < 0`).
  - It has `f̂_X(z) = ψ̂(z)(1 − c_X cos(Xz))`. This vanishes at `z = ±i/2` exactly, since `cos(±iX/2) = cosh(X/2)`.
  - On the real line the multiplier `1 − c_X cos(τX)` tends to `1` uniformly. So the archimedean energy of `f_X` tends to `∫|ψ̂|²A < 0`, with explicit error `(2c_X + c_X²)∫|ψ̂|²|A|`.
  - The whole polar cost is carried by the atoms at the lags `X` and `2X`. Exactly: `∫|f̂_X|² cos(τ log n) = 2π((c²/4)R(log n − 2X) − cR(log n − X))`, with `R` the autocorrelation of `ψ`.
- **Theorems [Lean, `RHTower.WeilPositivitySparseWeightsObstruction`].**
  - `weilPositive_farPolar_inequality` (Chebyshev inequality at every scale). For Weil-positive `lam` and every `X ≥ 0`:
    `η − (2c_X + c_X²)I ≤ 4π Σ_n lam(n) n^{−1/2}(c_X R(log n − X) − (c_X²/4)R(log n − 2X))`,
    where `η = −∫|ψ̂|²A > 0` and `I = ∫|ψ̂|²|A|`.
  - `not_weilPositive_of_localAtomMass`: if `Σ_{|log n − X| ≤ 1}|lam(n)|n^{−1/2} = o(e^{X/2})`, then `lam` is not Weil-positive.
  - `not_weilPositive_of_sparse_support`: if `lam` vanishes off `P` with `#(P ∩ [2,N]) ≤ CN^θ` and `θ < ½`, then `lam` is not Weil-positive. This covers S-units of finitely many primes, k-th powers (k ≥ 3), and lacunary sets.
  - Axioms: standard only.
- **Meaning.**
  - *Positivity produces the pole.* Any positive completion must reproduce the polar term `4πp₊p₋` of the Fejér test through its atoms at scales `e^X` and `e^{2X}`.
    - For Λ, the prime number theorem gives local means `s₁(X) → 1` and `s₂(2X) → 1`. The combination `2s₁(X) − s₂(2X) → 1` then reproduces exactly Weil's pole term `ĝ(i/2) + ĝ(−i/2)`, so `Q_Λ(f_X) → W_Λ(ψ) = arch(ψ) + pole(ψ) ≥ 0` (Yoshida/Connes–Consani small-support positivity).
    - For a general Weil-positive `lam`: `liminf [2s₁(X) − s₂(2X)] ≥ θ(ψ) = −arch(ψ)/(4πp²) > 0`. Using `ψ` with polar moments of opposite sign gives an upper window as well. This is a Chebyshev theorem for every positive completion, produced by positivity alone.
  - *Sharp boundary for L72.* The integer density `e^X` (local mass `≍ e^{X/2}` after the `n^{−1/2}` weight) is exactly what blocks the far-correction counterexample to PBAP. Position sets with fewer than `√N/log N` elements in `[N, eN]` admit no completion at all.
    - Open: whether the √N threshold is sharp, e.g. whether some weight system on the squares or on the prime squares (`#≍√N/log N`, at the box constant) is Weil-positive.
  - *Existence half.* This is the first structural theorem on the existence side. Completions exist only with PNT-density atoms and a positive residue. It extends the corpus result for summable weights (`summable_weights_weilAtomSymbol_not_nonneg`) to all non-summable sparse systems (e.g. S-unit systems with box-size weights, whose `Σ|lam|n^{−1/2}` diverges).
- **Novelty audit.**
  - Corpus: the summable case and the unit-shift polar multipliers `(cos 2πξ − 1)(cos 2πξ − cosh ½)` exist. The far multiplier `1 − cos(τX)/cosh(X/2)`, uniformly close to 1, and the sparse/Chebyshev laws are new.
  - Literature: Weil/Yoshida/Bombieri/Connes–Consani treat Λ (or semilocal Λ restricted to S) with fixed weights. The free-weight cone W and its density law are not in the literature I know of.

### L76 — Rigidity across the √n barrier: the half-pole atom. PROVED [Lean]
- **Why (stop-hook steer: find the producer).** In Minkowski's scheme, uniqueness turns *any* positive completion into Λ, so full uniqueness would make every construction of a positive completion a producer of Λ's positivity. Uniqueness had stopped at partial sums `O(n^θ)`, `θ < ½` (L71). At `θ = ½` sit the prime powers (`Σ_{p²≤x} log p ~ √x`) and the squares.
- **Mechanism: the `√n` main term is an atom.**
  - `β(n) = √n − √(n−1)` (partial sums `√n − 1`) satisfies `β(n)/√n = ∫_{log(n−1)}^{log n} ½ e^{(u−log n)/2} du`.
  - Hence `2π Σ β(n) n^{−½} φ_f(log n) = π|ĥ_f(0)|² + ∫|ĥ_f|² P_β` (`pairing_sqrtStep`).
    - The atom `π|ĥ_f(0)|²` comes from `½∫_0^∞ φ_f = ½|ĥ_f(0)|²`. It is the pole of `ζ(2s)` at `s = ½`, a *boundary* pole.
    - `P_β = 2Σ K_n` with `|K_n| ≤ (1+|τ|)/(n−1)²` is continuous of linear growth.
- **Theorems [Lean, `RHTower.WeilPositivityHalfPoleRigidity`].**
  - `vonMangoldt_add_eq_zero_of_symbol_atom`: symbol = continuous `P` of linear growth plus `m|ĥ(0)|²`; Weil positivity of `Λ + w` ⇒ `w = 0`.
    - Concentrated radical tests centred at `τ₀ ≠ 0` force `P ≤ 0`; there `|ĥ(0)|² = O(S^{−6})` (`vonMangoldt_sub_symbol_atom_violation`).
    - Probes force `m ≥ 0`.
    - Zero-mean probes `p_t − (κ̂(εt)/κ̂(0))p_0` (transform `0` at `0`, `≠ 0` at `t`, via the strict bound `|κ̂(v)| < κ̂(0)`) force `P ≡ 0`, then `m = 0`.
    - Resonators finish.
  - `vonMangoldt_add_halfPole_eq_zero`: partial sums `κ(√n − 1) + E(n)` with `Σ|E(n)|/(n√n) < ∞`, κ arbitrary ⇒ `w = 0`. The remainder uses the L69 Abel symbol under the weaker summable-weight hypothesis (`pairing_eq_integral_oscSymbol`).
  - `vonMangoldt_add_squares_weilPositive_eq_zero`: `Λ + c·1_{n=m²}` Weil-positive ⇒ `c = 0`. This is the first uniqueness result *at* the √n barrier.
  - Axioms: standard only.
- **Meaning.**
  - Weil positivity cannot absorb a boundary pole of either sign.
    - A positive atom in the perturbation symbol would need a nonpositive continuous part with the same spectral gap. The zero-mean probes show this forces both to vanish.
    - A negative atom is excluded directly.
  - The uniqueness frontier moves from `O(n^θ)`, `θ<½` to "`κ√n` + summable-weight remainder". Remaining gap: genuinely oscillating `√n`-size partial sums (e.g. `Λχ`, whose Dirichlet series has zeros, not poles, on the boundary) and irregular growth.
- **Next.** The arithmetic corollary "the prime powers are forced" (Λ restricted to primes is not Weil-positive) needs only `Σ_n |θ(√n) − √n|/(n√n) < ∞`, i.e. the medium PNT (Zeta23 `MediumPNT`) plus Chebyshev for the `k ≥ 3` powers.
- **L76 corollary: the prime powers are forced. PROVED [Lean, `RHTower.WeilPositivityPrimePowersForced`].**
  - `vonMangoldt_add_primePowerPart_weilPositive_eq_zero`: rescaling the weights on the non-prime prime powers by `1 + c` keeps Weil positivity only for `c = 0`.
  - `primeWeights_not_weilPositive`: `n ↦ log p·1_{n = p}` is not Weil-positive.
  - Inputs:
    - the Mathlib sandwich `ψ(√x) ≤ ψ − θ ≤ ψ(√x) + ψ(x^{1/3}) + ψ(x^{1/5})`;
    - Zeta23 `MediumPNT` (standard axioms);
    - Cauchy condensation for `Σ e^{−b(log n)^{1/10}}/n`.
  - Meaning: positivity sees the prime squares, through the boundary pole of `ζ(2s)`. A producer must generate the full prime-power structure `log p` at every `p^k`, not just the primes.

### L77 — Weil positivity produces a Chebyshev lower bound. PROVED [Lean]
- **Theorem [Lean, `RHTower.WeilPositivityChebyshevLowerBound`].**
  - `weilPositive_smoothedMean_lower`: for Weil-positive `lam`, if `e^{−Y/2}Σ_n lam(n)n^{−½}R(log n − Y) → L`, then `4πL ≥ −∫|ψ̂|²A > 0`.
  - `not_weilPositive_of_smoothedMean_zero`: zero smoothed mean density ⇒ not Weil-positive (e.g. Λχ for non-principal χ, Möbius-type weights, any mean-zero system).
  - Axioms: standard.
- **Proof.** Pass to the limit in the L75 far-polar inequality: `c_X e^{X/2} → 2`, so `4π(c_X S(X) − c_X²S(2X)/4) → 4π(2L − L)`.
- **Meaning.**
  - Positivity alone produces the Chebyshev phenomenon: the mean density of prime atoms is bounded below by an explicit archimedean constant.
  - For Λ, `L = (∫ψe^{x/2})²` by the PNT, and the inequality is exactly small-support Weil positivity of `ψ` with its pole term (Yoshida / Connes–Consani). This is the consistency check.

### L78 — Residue rigidity and the regular uniqueness theorem (both poles). PROVED [Lean]
- **Conjecture (the uniqueness counterpart of L77).** L77: every completion has residue ≥ θ*. Near Λ, the residue should be pinned exactly: perturbations whose partial sums carry a pole-type main term `κ(n−1)` are excluded, whatever the sign of `κ`.
- **Mechanism: the pole of ζ is a polar atom.**
  - `n^{−½} = ∫_{log(n−1)}^{log n} e^u n^{−½} du` telescopes to `∫_0^∞ e^{u/2}φ_f`.
  - With `e^{|u|/2} = 2cosh(u/2) − e^{−|u|/2}`, this equals `2Re(ĥ(i/2) conj ĥ(−i/2)) − ∫_0^∞ e^{−u/2}φ_f`.
  - So constant weights pair as `4π·(polar pairing) + ∫|ĥ|²P_1`, with `P_1` continuous of linear growth.
  - Polar-constrained concentration tests don't see the polar atom. Probes with polar pairing of both signs (the bump, `+`; the odd probe, `−`) kill it.
- **Theorems [Lean, `RHTower.WeilPositivityResidueRigidity`].**
  - `vonMangoldt_add_eq_zero_of_symbol_polar`: continuous symbol + polar atom ⇒ `w = 0`.
  - `vonMangoldt_add_residue_eq_zero`: partial sums `κ(n−1) + E(n)`, `Σ|E|/(n√n) < ∞` ⇒ `w = 0`. It extends the constant shifts of L63 to every regular residue shift. Example: `Λ + c·1_{2|n}` ⇒ `c = 0`.
  - `vonMangoldt_add_eq_zero_of_symbol_two_atoms`: both atoms at once (origin + poles `±i/2`). The even zero-mean probe `κ(x/ε₁) − (ε₁/ε₂)κ(x/ε₂)` has positive polar pairing because `∫κ cosh(cx)` increases with `|c|`.
  - `vonMangoldt_add_twoPole_eq_zero`: **regular uniqueness theorem.** Partial sums `κ₁(n−1) + κ₂(√n−1) + E(n)` with `Σ|E(n)|/(n√n) < ∞` ⇒ `w = 0`.
  - Axioms: standard.
- **Meaning.**
  - The uniqueness half of the Minkowski split now holds on the whole *regular* class: every perturbation whose Dirichlet series has, in `Re s ≥ ½`, at most the two natural poles (`s = 1`, residue shift; `s = ½`, prime-power shift) plus an Abel-summable remainder.
  - The only perturbations left are those with singularities *at zeros* (boundary atoms at zeros of `ζ` or of other L-functions, interior poles at off-line zeros). These are exactly the RH-relevant ones: as shown in the L76 discussion, `lam* − Λ` for any hypothetical second completion has its singularities at the zeros of `ζ`.
  - This is the sharp boundary of the regular method. What remains of uniqueness is "positive Hamburger at the zeros".

### L79 — PBAP localization: localization with a margin is incompatible with uniqueness; the exact duality holds. KILL [P] + DUALITY PROVED [Lean]
- **Conjecture (L79-Q, quantitative localization).** Let `M(A) := inf Σα_iA(f_i)/Σα_i‖f_i‖²` over prime-blind polar families at levels `≤ A`. Claim: there are `A₀` and `c > 0` with `M(A) ≥ c·M(A₀)` for all `A ≥ A₀`.
  - Motivation: far lags must carry the polar moment through spectrum near the Nyquist height `e^{2A}`, which costs about `½·log(height)` per unit mass (L70, L72). Since `M(A₀) > 0` at small levels, this would give `W ≠ ∅`.
- **Attack: minimax.** Replacing `A(f)` by `A(f) − c‖f̂‖²` in the separation argument of the duality below gives `M(A) = sup_lam σ_A(lam)`, where `σ_A(lam) = inf_f Q_lam(f)/‖f̂‖²` is the best Weil margin at level `A` [P].
  - So L79-Q ⟺ a completion with uniform slack exists (by compactness, as in L68) ⟺ `W(A−c) ≠ ∅` for some `c > 0`.
  - `W(A−c) ⊆ W(A)`: lowering the archimedean symbol only makes positivity harder.
- **Kill: Λ never has slack (unconditional, by cases).**
  - If RH fails, `Q_Λ < 0` somewhere.
  - If RH holds, polar tests with `f̂` concentrated below height 14 have `Q_Λ(f) = Σ_γ|f̂(γ)|² → 0` relative to `‖f̂‖²`, because no zero lies below 14.
  - Either way, `limsup σ_A(Λ) ≤ 0`, so `Λ ∉ W(A − c)`.
  - Under the uniqueness conjecture (`W ⊆ {Λ}`), `W(A−c) = ∅`, hence `M(A) → 0` and L79-Q is FALSE.
  - Unconditionally, L79-Q would itself produce a second completion. **Verdict: CIRCULAR / FALSE under uniqueness.** No localization with a margin can prove existence. Existence must be exact, which is L74's no-slack picture, now derived from uniqueness rather than from the near-radical sketch.
- **Far-lag cost principle (heuristic, open core).** Positive-definite `Φ` vanishing at `{log n}` with `Φ(0) = 1` cannot carry polar moment `m` at lags `~U` cheaply.
  - Vanishing at spacing `e^{−U}` forces oscillation at frequency `~e^U`. Pure tones fit only windows of width `≲ e^{−U/2}`, and a burst of amplitude `a` needs spectral `L¹` mass `≳ a`. Hence archimedean cost `≳ c·U·m`.
  - The upper bound through `Φ(u)² ≤ 2Φ(0)(Φ(0) − Φ(d))` gives only `m²`-type costs. That bound is lossy.
  - Cheaper transport would need spectral mass at resonant heights, where Dirichlet dual sums take large values. There, however, `n^{iτ} ≈ 1` for small `n`, which contradicts vanishing at small `log n`. Resonance and blindness exclude each other.
  - Spectral form: a positive-definite `Φ` with compactly supported spectrum `[−T, T]` vanishing at `log n`, `n ≤ N`, needs `T ≳ N/log N` (Jensen zero count). Prime-blindness pushes spectrum to the Nyquist height `e^{2A}`.
  - A rigorous multi-scale version of this principle would be the existence-side analogue of L75.
- **Theorem [Lean, `RHTower.WeilPositivityPrimeBlindDuality`]. The existence half is prime-blind archimedean positivity.**
  - `PrimeBlindPositive A`: every finite family of polar-constrained `C²` tests at levels `≤ A` with weights `α_i ≥ 0` and combined autocorrelation vanishing at every `±log n`, `n ≥ 2`, has `Σα_i∫|f̂_i|²A ≥ 0`.
  - `primeBlindPositive_of_weilPositiveUpTo`: `W_A ≠ ∅ ⇒ PBAP_A`.
  - `exists_weilPositiveUpTo_of_primeBlindPositive`: `PBAP_{A+1} ⇒ W_A ≠ ∅`.
  - `exists_weilPositive_iff_primeBlindPositive`: `(∃ lam, WeilPositive lam) ⟺ ∀A, PBAP_A`.
  - Proof:
    - Compactness of the box `|lam(n)| ≤ √n(log n + C₀)` reduces to finitely many tests.
    - Hahn–Banach separation of the compact convex set of energy vectors from the orthant gives `α ≥ 0` with negative combined energy on the whole box.
    - At each atom, the two-point resonator `g_w(x+log n/2) ± g_w(x−log n/2)` has atom coefficient exactly `2‖g_w‖²·(±1)·1_{m=n}`, and archimedean energy at most `4π‖g_w‖²(log n + C₀)`. With weight `|C_n|/(2‖g_w‖²)` it cancels the atom and costs exactly the worst box corner `b_n|C_n|/√n`.
    - The resulting family is exactly prime-blind with negative archimedean energy.
  - Axioms: standard.
- **Insight.**
  - The level-wise box (L68) and the two-point resonators are dual: every face of the box is realized by a test whose energy is affine in a single weight. This is what makes the existence dual *exactly* prime-blind rather than box-weighted.
  - With uniqueness, `Λ`'s positivity is a statement about `Γ_ℝ` and `{log n}` only, and it has no margin at infinity. Any proof of it must be exact at every level, which excludes every open-condition, perturbative or localization-with-margin argument.
- **Next.** The two open cores are now sharply separated:
  - exact PBAP, a primes-free and zeros-free positivity statement with zero margin at infinity;
  - uniqueness for perturbations singular at zeros.
  - L80 attacks uniqueness at the zeros through the Herglotz picture. Weil positivity of `lam` makes `ξ_lam'/ξ_lam := G_∞ + β(1/s + 1/(s−1)) − D_lam` a Herglotz function on `Re s > ½` (Bochner–Schwartz on polar tests). Hence `ζ_lam = exp(−∫D_lam)` is zero-free there, and a second completion is `ζ` with some zeros removed and redistributed. The removal-only case is Beurling-rigid (L67). The redistribution case is the core.

### L80 — Positivity forces the functional equation at the zeros: dilated von Mangoldt weights are rigid. PROVED [P]; Lean planned
- **Why.** L78 settled every perturbation regular at the zeros. What is left of uniqueness is perturbations whose Dirichlet series is singular at the zeros of `ζ` itself.
  - The simplest such class is the *dilations* `w = Λ⋆b`, with `b` finitely supported: `lam(n) = Λ(n) + Σ_m b(m)Λ(n/m)`, for example `Λ(n) + cΛ(n/2)`.
  - Here `D_w = −B(s)ζ'/ζ(s)` with `B(s) = Σ b(m)m^{−s}`. It has a pole at every zero of `ζ`, with residue `B(ρ)m_ρ`.
  - This is outside L69–L78, and outside the twists (L52, poles at `ρ ± iα`) and characters (L53–L56, poles at zeros of other L-functions).
- **Theorem [P].** If `Λ⋆(δ₁ + b)` is Weil-positive (ζ's archimedean term, polar tests, all levels) with `b` finitely supported, then `b = 0`.
- **Proof.**
  1. *Tangent criterion (L50(i)).* `D_w` is meromorphic, and on the line it has poles only at on-line zeros.
     - Spread radical tests at `τ₀` (not an ordinate of an on-line zero) have zero side `O(S^{10}e^{−S})`.
     - Their perturbation energy is `−(1/π)∫|f̂|²Re D_w(½+it)dt` up to tiny terms. Shift the contour from `Re s > 1`:
       - the residue at `s = 1` is `F(1)B(1) = 0` for polar `f`;
       - residues at off-line zeros are `≈ 0` for radical `f`;
       - on-line poles are cancelled by the double zero of `|f̂|²`.
     - Concentration gives `Re D_w(½+iτ₀) ≤ 0` wherever `ζ(½+iτ₀) ≠ 0`.
     - With `ζ(½+iτ) = e^{−iθ(τ)}Z(τ)`, `ζ'/ζ(½+iτ) = −θ'(τ) − iZ'/Z(τ)` and `θ' = A/2`. The condition reads `Re B(½+iτ)·θ'(τ) ≤ Im B(½+iτ)·Z'/Z(τ)`.
  2. *Residues are real.* At an on-line zero `½+iγ` of multiplicity `m`, `Re D_w(½+iτ) = −m·Im B(½+iγ)/(τ−γ) + O(1)`. This is unbounded above on one side unless `Im B(½+iγ) = 0`. Hence **`B(ρ) = B(1−ρ)` at every zero on the critical line.**
  3. *Density.* `F(τ) = Im B(½+iτ) = −Σ_{2≤m≤M}b(m)m^{−½}sin(τ log m)` is an exponential sum of type `log M`. If nonzero, it has at most `(log M/π)T + O_M(1)` real zeros in `[0,T]`. By Selberg (1942), `ζ` has `≫ T log T` zeros on the line up to `T`. So `F ≡ 0`, and `b(m) = 0` for `m ≥ 2` by independence of `sin(τ log m)`.
  4. *Scaling.* `w = b(1)Λ`, and scaling rigidity (L52, `scaled_vonMangoldt_weilAtomSymbol_not_nonneg`) gives `b(1) = 0`. ∎
- **Variants.**
  - Selberg can be replaced by off-line information: the division tests of L51b force `1 + B(ρ) = 0` at every off-line zero, hence `B(ρ) = B(1−ρ) = −1` there. Then `E(s) = B(s) − B(1−s)`, entire of exponential type `log M`, vanishes at *all* nontrivial zeros, and Riemann–von Mangoldt `N(T) ≍ T log T` against Jensen's `O(T)` gives `E ≡ 0`. Under RH, step 3 needs only Riemann–von Mangoldt.
  - Infinite `b` with `Σ|b(m)|m^{−½+δ} < ∞` works the same way: `F` is analytic and bounded in a strip, so it has `O(T)` zeros.
  - A regular part can be added: `w = Λ⋆b + v` with `v` in the L78 class. `v` adds a continuous symbol and no poles at the zeros, so steps 1–2 still force `Im B = 0` at the zeros.
- **Meaning: the uniqueness half at the zeros is a Hamburger problem on the zero set.**
  - Positivity forces every residue of `D_w` at an on-line zero to be real. For the dilation class this is `B(ρ) = B(1−ρ)`: the *degree-0 functional equation* holding at the zeros of `ζ`.
  - The zeros are dense enough (`T log T` against the `T` of a Dirichlet polynomial) to be a uniqueness set, so the functional equation holds identically. A degree-0 Dirichlet polynomial with a functional equation and no Γ-factor is constant (degree-0 Hamburger), which leaves only scaling, and scaling is rigid.
  - This is the first uniqueness theorem for perturbations singular at the zeros of `ζ`. It uses the zeros themselves (their number on the critical line), not only the archimedean mismatch.
- **Structural corollary [P].** For every `w` with `D_w` meromorphic across the critical line, `Λ + w ∈ W` forces all residues of `D_w` at on-line zeros of `ζ` to be real, and `Re D_w ≤ 0` elsewhere on the line.
  - The residues of a genuine second completion are real and in `(0, m_ρ]`, since that completion removes zero mass. So the remaining uniqueness core is exactly *partial zero removal with real residues*: Dirichlet series whose residues at the zeros are real but not of the form `B(ρ)m_ρ` for a small `B`.
- **Novelty audit.**
  - Corpus: twists and characters have poles away from `ζ`'s zeros, and dilations are absent (search: "dilation", `Λ(n/2)`, `Λ⋆b`, no hits).
  - Literature: `Im B(½+iγ) = 0` at all zeros is a statement about Dirichlet polynomials at zeta zeros, related to Gonek/Fujii discrete moments. The Weil-positivity reading ("positivity forces the functional equation at the zeros") and the rigidity theorem are not in the literature I know.
- **Lean plan.**
  - (a) The singular tangent criterion for `D_w = −Bζ'/ζ`: one-sided twisted explicit formula plus truncated radical concentration. This is new infrastructure.
  - (b) Residue realness from the pole of `Z'/Z`.
  - (c) The density step, via the off-line division variant (L51b machinery) plus Riemann–von Mangoldt, or via Selberg's positive proportion. Neither is formal yet.
  - (d) Scaling rigidity, already formal.
- **L80 Lean result. PROVED [Lean], standard axioms.**
  - `RHTower.WeilDilationCriticalLineShift`: the dilated prime sum as a line integral (`dilated_prime_side_line`).
    - The ξ log-derivative identity, the analytic shift integrand, and the vertical shift to `Re s = ½` (`integral_dilationShiftIntegrand_eq`).
    - The spread-test factorization and the truncation-error bound on `Re s = c`.
  - `RHTower.WeilDilationResidueRealness`:
    - `dilation_tangent_criterion`: Weil positivity of `Λ + Σ b(m)Λ(·/m)` ⇒ `Re V(t) ≤ 0` for all `t`, where off zeros `V = |ξ|⁶|ĥ|²·B(−ζ'/ζ)` on the critical line.
    - `dilationPoly_im_eq_zero_of_weilPositive`: `Im B(½+iγ) = 0` at every critical zero.
    - `single_dilation_critical_ordinates`: `Λ(n) + cΛ(n/m)` Weil-positive with `c ≠ 0` ⇒ every critical ordinate has `γ log m ∈ πℤ`.
  - This is the first formal uniqueness-type theorem for a perturbation singular at the zeros of `ζ`. It needs no zero statistics.
  - The step to `b = 0` (density of critical zeros, via Selberg or off-line division tests plus Riemann–von Mangoldt) remains paper-only.
  - Reusable machinery:
    - one-sided prime sums of translates via Zeta23 `prime_side_line`;
    - the removable-singularity form of `ξ·ζ'/ζ`;
    - strip bounds of `ξ` from the kernel representation;
    - tilted Plancherel for probe masses;
    - the concentration limit `(1/S)∫V|q̂_S|² → V(τ₀)∫|κ̂|⁴`.

### L81 — A Selberg-free density step for dilations: Kronecker plus mean motion (analysis in progress) [P-sketch]
- **Goal.** Deduce `b = 0` from the formal L80 outputs without zero statistics. Two formal inputs:
  - `Re V(t) ≤ 0` for all `t`;
  - `Im B = 0` at critical zeros.
- **Pointwise form.** `V(t) = s(t)[Re B·θ'·Z⁶ − Im B·Z⁵Z']`, where `s > 0` is smooth, `Z` is Hardy's function and `θ' = A/2`. So:
  - (a) at `t = 0` (`Im B(½) = 0`, `Z'(0) = 0`, `θ'(0) < 0`): `B(½) ≥ 0`;
  - (b) at any `t ≥ 7` with `Im B(½+it) = 0`, `Z(t) ≠ 0`: `Re B(½+it) ≤ 0`;
  - (c) at a critical zero `t*` of order `m` with `Im B(t*) = 0`: `Re B(t*)θ'(t*) ≤ m·(Im B)'(t*)`.
  - Hence at a *downward* crossing of `(0, ∞)` by `G(t) = B(½+it)` (`(Im B)' ≤ 0`) there is a contradiction whether or not `t*` is a zero of `ζ`.
- **Existence of downward crossings.** Let `P` be the torus polynomial of `B` (variables `p^{−it}`, nonnegative exponents, real coefficients, constant term `b₁`). The flow `t ↦ (p^{−it})_p` is equidistributed (Kronecker–Weyl; the `log p` are ℚ-independent).
  - The net downward crossing rate of any ray equals the mean motion `μ` of `G` around the ray's vertex (flux balance for the invariant measure).
  - Jessen: `μ = −J'(0)`, with `J(y) = ∫_𝕋 log|P(e^{−y log p} z)|` convex and `J(∞) = log|b₁|`.
  - Cases:
    - `b₁ ≥ 0`: `G − b₁` has no constant term, so it winds clockwise, which gives downward crossings of `(b₁, ∞) ⊆ (0, ∞)`.
    - `b₁ < 0` and `P` has a zero in the open polydisc: `μ > 0` around `0`, again giving downward crossings.
    - Edge case: `b₁ < 0` and `P` zero-free in the open polydisc. Then `P(r·1) < 0` for `r < 1`; with (a) this forces `B(½) = 0`. Still open.
- **Status.** Paper sketch. The edge case and the Lean cost (Kronecker–Weyl on a finite torus, Jessen's formula) are to be settled in L81.
- **L81 result.**
  - **Kill of the Selberg-free crossing route [P].** Take `B = b₁(1 − 2^{½−s})` with `b₁ < 0`.
    - `G(t) = B(½+it) = b₁(1 − 2^{−it})` traces the circle of centre `b₁` and radius `|b₁|`. It lies in `Re ≤ 0` and meets `[0, ∞)` only at `0`, so it never enters `(0, ∞)` and no crossing argument applies.
    - For this `B`, positivity forces every critical ordinate into `(2ℤ+1)π/log 2`. At the transversal zeros `t = 2πk/log 2` of `G` it also forces `Z'(2πk/log 2) = 0`: when `G` passes through `0` along the imaginary axis, the tangent criterion requires `Re G'·θ' = Im G'·Z'/Z` there.
    - These are pure zero-location constraints, so no argument that avoids counting zeros can exclude this `B`.
  - **Positive survivor [P].** The density input needed is exactly: *the critical zero set is not contained in the zero set of a nonzero real sum `Σ_{2≤m≤M} a_m sin(t log m)`*.
    - The corpus supplies it. The unconditional superlinear count of simple critical zeros (`eventually_superlinear_xiSimpleCriticalZeroCount`, Alpöge–Furman via Zeta23) feeds the bounded-support Mellin uniqueness engine `weilTest_eq_zero_of_cofinite_simpleCritical_mellin_zero`.
  - **Mechanism.** The degree-0 functional-equation defect `B(s) − B(1−s)` is realised as a Mellin transform of a compactly supported test.
    - The test is `g(x) = Σ b(m)(h(mx) − h(x/m)/m)`, with `h` a narrow tent at `1`, and `Mellin g(s) = (Σ b(m)(m^{−s} − m^{s−1}))·Mh(s)`.
    - On the critical line this equals `2i·Im B(½+it)·Mh(½+it)`, which vanishes at every critical zero, so the engine gives `g = 0`.
    - The tents are disjoint, so `g(m₀) = −b(m₀)δ/m₀` isolates each coefficient.
  - **Theorem [Lean, `RHTower.WeilDilationRigidity`, standard axioms].** `dilatedVonMangoldt_eq_zero_of_weilPositive`: if `Λ(n) + Σ_{m∈S} b(m)Λ(n/m)` is Weil-positive (finite `S ⊆ ℕ_{≥1}`), then `b = 0` on `S`.
    - This is the first formal uniqueness theorem, closed end to end, for a family of perturbations with poles at the zeros of `ζ`.
  - **Side result [P]: regular perturbations of multiples of Λ are rigid by a pointwise Fejér argument.** Let `h₁Λ + r ∈ W` with `r` regular.
    - The tangent criterion gives `Re D_r(½+it) ≤ (1−h₁)θ'(t)` pointwise.
    - Integrate against `|ψ̂|²` for the corpus Fejér test `ψ` (support below `log 2`, so `arch(ψ) < 0`). The atoms of `D_r` sit at lags `≥ log 2` and are invisible, which gives `0 ≤ (1−h₁)·arch(ψ)`. This is impossible for `h₁ < 1`.
    - `h₁ > 1` fails at large `t`, since `θ' → ∞`.
    - A pole at `s = 1` is the only way to fix the low frequencies (L75, L77).

### L82 — The producer conjecture and the zero-consumption law for Möbius-type completions. CONJECTURE + THEOREM [P]
- **Phase 1 (frontier).**
  - Existence is W ≠ ∅ ⟺ PBAP (L79). Uniqueness is proven for regular perturbations (L78), finite dilations (L81, Lean), characters and twists (L52–L56), and `O(n^θ)` perturbations (L71).
  - Every `lam ∈ W` has a Herglotz function `Φ_lam = G_∞ + β(1/s+1/(s−1)) − D_lam` on `Re s > ½`, so `ζ_lam = exp(Σ lam(n) n^{−s}/log n)` is zero-free there. On the critical line, Weil positivity says the phase `φ_lam(t) = θ(t) + arg ζ_lam(½+it)` is nondecreasing, with positive jumps allowed at zeros of `ζ_lam` on the line.
- **Phase 2 (SOTA).**
  - arXiv:2608.24827 (Aug 2026) certifies Weil positivity for `supp f ⊆ [−0.8, 0.8]`. Its Landau–Widom law `−ln λ_min(L) ~ 2π² N(T*)/ln N(T*)`, with `T* = 2πe^{2L}`, confirms there is no slack (L74).
  - Gonek–Montgomery (IMRN 2013): `Σ_{n≤N} n^{−s} + χ(s)Σ_{n≤N} n^{s−1}` has 100% of its zeros simple and on the critical line.
  - I know of no study of second completions or of the Weil cone for general weights.
- **Phase 3 — Producer Conjecture PC-82 (the functional equation is the only producer).** A weight system `lam` in the box is Weil-positive iff (a) and (b) hold:
  - (a) `ζ_lam` satisfies `Γℝ(s)ζ_lam(s) = Γℝ(1−s)ζ_lam(1−s)`, so its Hardy function `e^{iθ}ζ_lam(½+it)` is real;
  - (b) the Weil measure `μ_lam` is purely singular: its phase is a staircase that jumps only at real zeros.

  Equivalent forms:
  - Every Weil-positive `μ_lam` is singular. The absolutely continuous part is the part that would come from any "producer" other than a functional equation.
  - Via Hamburger, PC-82 ⟺ uniqueness (`W ⊆ {Λ}`). It is falsified by any Weil-positive `lam` whose `μ_lam` has an absolutely continuous part.
  - What becomes visible if it is true: positivity cannot be manufactured by any mechanism except a Γℝ-functional equation plus reality of zeros. So the producer IS ζ's FE, and RH ⟺ PBAP.
  - `[OPEN CORE]`: the absolutely continuous part of `μ_lam` vanishes for every `lam ∈ W`.
- **Reduction of the core.** Every `lam ∈ W` is `Λ + w` with `E := D_w·ζ` holomorphic on `Re s > ½`. Two cases are closed:
  - `E = Cζ` (regular, L78);
  - `E = −Bζ'` (dilation, L81).
  - New class: **Möbius-type** `E` = a Dirichlet polynomial, i.e. `w = e⋆μ`, `D_w = E/ζ`, `e(1) = 0`, `n₀ = min supp e ≥ 2`.
- **Theorem L82 (zero-consumption law) [P].** If `Λ + e⋆μ` is Weil-positive with `e ≠ 0` finitely supported and `e(1) = 0`, then for all large `T`:

  `N(T) − N₀^{distinct}(T) ≥ (log n₀/π)·T − C_e log T`.

  So a Weil-positive Möbius-type second completion needs a linear density (at least `log 2/π` per unit height) of zeros that are off the line or multiple.
- **Proof.**
  1. *Realness and multiplicity* (the L80 tangent criterion carries over; residues at off-line zeros are killed by the radical factor). At a simple critical zero, the residue `E(ρ)/ζ'(ρ)` of `D_w` is real. At a multiple critical zero, `E(ρ) = 0`: a double pole on the line would make the Weil distribution non-positive.
     - Since `ζ'(1−ρ) = −χ(1−ρ)ζ'(ρ)` at zeros, both statements say that `G_E(s) := E(1−s) + χ(1−s)E(s)` vanishes at every distinct critical zero.
     - Check: `G_E(½+it) = 2e^{iθ(t)} Re(e^{iθ(t)}E(½+it))`.
  2. *Counting `G_E`.* Use the argument principle on `[−A, 1+A] × [t₁, T]` with `A = A(e)` large.
     - On `σ = 1+A`, `χ(1−s)E(s)` dominates, since `|χ(−A−it)| ≍ t^{½+A}` and the `n₀` term of `E` dominates. Its argument grows by `2θ(T) − T log n₀ + O(1)`.
     - On `σ = −A`, `E(1−s)` dominates, since `|χ(1+A−it)| ≍ t^{−½−A}`. Its argument change is `−T log n₀ + O(1)`.
     - The horizontal segments give `O(log T)` (Backlund). Hence `N_{G_E}(T) = (θ(T) − T log n₀)/π + O_e(log T)`.
  3. From step 1, `N₀^{distinct}(T) ≤ N_{G_E}(T)`. With `N(T) = θ(T)/π + 1 + S(T)` and `S(T) = O(log T)`, this gives the bound. ∎
- **Corollaries.**
  - (i) Under RH with at most `o(T)` multiple zeros up to `T`, no Möbius-type second completion exists.
  - (ii) Contrast with dilations. For dilations, realness lives on the sparse zero set of `Im B` (`O(T)` zeros), so the Alpöge–Furman density kills them unconditionally (L81).
    - For Möbius type, realness lives on the zero set of `Re(e^{iθ}E)`, which has `N(T) − (T/π)log n₀` zeros, the same order as ζ's.
    - Only a linear-scale zero statistic can exclude them. This is the first class in the uniqueness core whose rigidity is equivalent in strength to zero statistics at linear scale.
  - (iii) Producer reading: an alternative producer of Möbius type must use up at least `log 2/π` off-line or multiple zeros per unit height.
- **Phase 4 (attack).**
  - *False?* Test `E = 2^{−s}`: `Re(e^{iθ}2^{−½−it}) = 2^{−½}cos(θ − t log 2)` has `(θ(T) − T log 2)/π + O(1)` zeros, matching the count.
  - *Circular?* No: only Weil positivity is used.
  - *Known?* The count is Gonek–Montgomery-type, extended to `n₀ ≥ 2`. The Weil-completion application and the deficit law are, to my knowledge, new.
  - Verdict: **SURVIVES PRELIMINARY ATTACK** (theorem on paper).
  - PC-82 itself stays a conjecture, equivalent to uniqueness.
- **Lean plan.**
  - (A) Realness for `Λ + e⋆μ`. The line identity uses the LSeries of `μ` (`1/ζ`) as in Zeta23 `integrand_eq_tsum`. The shift integrand becomes `E·(rPT/ζ)·rPT²·xiConj³·H`, with `rPT/ζ = s(s−1)Γℝ(s)/2` analytic on the strip, so no `dslope` is needed.
  - (B) The argument-principle count of `G_E`, using the Zeta23 RvM machinery as a template.
- **L82 upgrade — Möbius-type completions are rigid UNCONDITIONALLY (twisted first moment + Bohr torus) [P].** This supersedes the zero-consumption law above. That law stays correct but is no longer needed for this class.
  - **Theorem.** Let `e` be real with `e(1) = 0` and `Σ|e(n)| n^{−½+δ} < ∞`. If `Λ + e⋆μ` is Weil-positive, then `e = 0`.
  - **Proof.**
    1. *Tangent criterion.* It holds exactly as in L80. `D_w = E/ζ` has no pole at `s = 1`, and the radical factor kills the residues at off-line zeros. So `Re(E/ζ)(½+iτ) ≤ 0` off the zeros.
       - Multiplying by `|ζ|²` gives the continuous inequality `Re(E(½+it)·conj ζ(½+it)) ≤ 0` for all `t`. No realness and no zero statistics are used.
    2. *Twisted first moment.* For positive rationals `q`, `(1/T)∫_1^T ζ(½−it) q^{−it} dt → [q ∈ ℕ]·q^{−½}`.
       - Shift to `σ = 2` using a convexity bound for the horizontal segments; the χ-part of the AFE has only `O_q(1)` stationary points.
       - So for every Dirichlet polynomial `A(½+it) = Σ α_k k^{−it}`, `0 ≥ lim M_T[Re(E conj ζ)|A|²] = Re Σ_{k,l} α_k ᾱ_l √(l/k) Σ_{n: l | nk} e(n)/n`.
    3. *Torus.* Fix a finite set `S` of primes. Lift `n^{−it} ↦ z^n` on `𝕋^S`. The form in step 2 is `∫_{𝕋^S} Re(P_E · conj Z_S)|Q_A|²`, where `P_E = Σ e(n) n^{−½} z^n` and `Z_S = Π_{p∈S}(1 − p^{−½}z_p)^{−1}`.
       - Choose `Q_A = R·Π_{p∈S}(1 − p^{−½}z_p)`, a polynomial. The condition becomes `∫ Re(Q)|R|² ≤ 0` for all polynomials `R`, where `Q = P_E·Π_{p∈S}(1 − p^{−½}z_p)` has no constant term (`e(1) = 0`).
       - With `R = 1 + c z^a`, `∫ Re(Q)|R|² = Re(c̄ q_a)` for `a ≠ 0`. This must be `≤ 0` for every `c ∈ ℂ`, so `q_a = 0`.
       - Hence `Q = 0`, so `E·Π_{p∈S}(1 − p^{−s}) = 0` (coefficients coprime-restricted to `S`). Letting `S` exhaust the primes gives `e = 0`. ∎
  - **Example.** `e = cδ₂`: `Re Q = c(cos φ/√2 − cos 2φ/2)` takes both signs for every `c ≠ 0`.
  - **Mechanism, a new tool for the uniqueness core.** The pointwise sign law is pulled back to the Bohr torus through the twisted first moment of ζ. There the pole-free, constant-term-free Dirichlet object `E/ζ_S` must have nonpositive real part and mean zero, hence it vanishes.
    - This complements L81. Density plus realness kills the ζ'-type (degree-1) singular part; the torus moment kills the degree-0 part.
  - **Status of the uniqueness core.**
    - Closed: `E = Cζ` (L78), `E = −Bζ'` with finite `B` (L81, Lean), `E` of degree 0 (L82, paper).
    - Open: mixtures (`E = −Bζ' + F`, where the leading `log²T` term of the twisted second moment forces `Re B ≤ 0` on the torus); and completions whose `D_lam` does not continue across the line.
  - **Verdict: THEOREM [P]. Lean planned** in three parts:
    - (i) tangent criterion for `E/ζ`;
    - (ii) twisted first moment of ζ;
    - (iii) the torus coefficient extraction.
- **L82 Lean status.**
  - `formal/tmp/l82/A.lean` compiles clean (no errors, no warnings).
  - Contents:
    - `tendsto_twisted_zeta_first_moment`, the twisted first moment of ζ on the critical line;
    - `tendsto_zeta_mobiusPoly_moment`;
    - `sum_mobius_zetaFreqWeight`, the Möbius collapse;
    - `critDirPoly_eq_zero_of_re_mul_conj_zeta_nonpos`: a Dirichlet polynomial with no constant term that satisfies `Re(E·conj ζ) ≤ 0` on `y ≥ 8` is zero.
  - Not done: the axiom check and module install (interrupted by system memory pressure), and the Weil-positivity ⇒ `Re(E·conj ζ) ≤ 0` link.

### L83 — The producer characterization and the ε-core of uniqueness. THEOREM [P] + NO-GO [P]
- **Phase 3 (producer conjecture, refined): PC-83.** Weil positivity is produced exactly by the Hermite–Biehler property of the completed Dirichlet exponential.
  - Statement: `lam ∈ W` ⟺ `E_lam(s) := [s(s−1)]^β Γℝ(s) ζ_lam(s)`, with `ζ_lam = exp Σ lam(n) n^{−s}/log n`, has `Re E'/E ≥ 0` on `Re s > ½`.
  - Equivalently: `ζ_lam` is zero-free there, and the phase `φ_lam(t) = θ(t) + arg ζ_lam(½+it)` is nondecreasing, with only upward jumps of `π·(multiplicity)`.
  - For `Λ` the functional equation makes `e^{iθ}ζ(½+it) = Z(t)` real. So `φ_Λ` is automatically a staircase and **the FE produces boundary positivity unconditionally**. RH is exactly the absence of the only other obstruction, interior poles from off-line zeros.
  - A second producer must be an HB Dirichlet exponential with no functional equation that still yields a monotone phase.
  - Proof sketch [P-sketch]: Bochner–Schwartz on polar tests plus the far-correction pole identification (L75, L77) gives a positive boundary measure with Poisson extension `Re Φ_lam`; the log² growth of D_lam gives the Phragmén–Lindelöf step.
- **The ε-core [P].** Take `lam = (1−ε)Λ + e⋆μ`, with `0 < ε ≤ 1`, `e ≠ 0` finitely supported, `e(1) = 0`, `n₀ = min supp e`.
  - (i) `ε = 1` is killed by L77: `β = 0` contradicts the Chebyshev lower bound. The core is therefore `0 < ε ≤ 1 − β₀`.
  - (ii) The tangent criterion becomes `Re(E·conj ζ)(½+it) ≤ ε θ'(t) |ζ(½+it)|²` for all `t`.
  - (iii) Realness: `G_E(s) = E(1−s) + χ(1−s)E(s)` vanishes at every distinct critical zero. At multiple zeros `E(ρ) = 0`: a double pole on the line would put a finite-part distribution into `μ_lam`.
  - (iv) At every off-line zero `ρ` with `Re ρ > ½`: `E(ρ) = (1−ε)ζ'(ρ)`, because `D_lam` must be regular inside the half-plane.
  - (v) The zero-consumption law of L82 applies verbatim: `N(T) − N₀^{distinct}(T) ≥ (log n₀/π)T − O_e(log T)`.
  - **Corollary.** If all but `o(T)` zeros up to `T` are simple and critical, no ε-core completion exists.
- **No-go (why the L82 torus method stops here).** Against any fixed weight `|A|²`, the right side of (ii) has mean `≍ ε log²T`, while the left side has the `O(1)` torus value. So twisted moments cannot see the ε-core.
  - Pointwise, (ii) binds only where `|Z| ≲ |E|/(ε log t)`, i.e. at the zeros, which is realness again.
  - The constraint set of the ε-core has zero density `θ'/π − (log n₀)/π`. That is linearly (not logarithmically) below ζ's, so neither the Alpöge–Furman `T log T` count nor any proportion `< 1` of critical zeros excludes it.
  - Explicit consistency check: `E = 2^{−s}(1 − √2·2^{−s})` has linear-density zeros exactly on the critical line. So the multiplicity-excess scenario is not excluded by the structure of `E`.
- **Positive survivor.** The deficit law above is rigorous. It gives the first linear-scale lower bound on defective zeros forced by a hypothetical second completion.
  - **Reframing of the programme.** The implication actually needed is **"W ≠ ∅ ⇒ RH"**, not full uniqueness. In the ε-core the obstruction to it is exactly a zero statistic at linear scale (off-line or multiple zeros of density `≥ log 2/π`, sitting on zeros of `E` or on the interpolation set `E = (1−ε)ζ'`).
  - Status: `NO POSITIVE SALVAGE FOUND` for a statistics-free kill of the ε-core. The deficit law is the salvage.
- **Next.**
  - Attack the ε-core with (iv), off-line interpolation, combined with (v). Can `≥ (log 2/π)T` defective zeros satisfy `E(ρ) = (1−ε)ζ'(ρ)` and `G_E(ρ) = 0` simultaneously?
  - Near-line off-line pairs make `ζ'(ρ)` small, so `E(ρ)` must be small at linear density. That needs `E` to have linear-density zeros hugging the line, and `n₀ ≥ 2` bounds this density by `(log(max supp e) − log n₀)/2π`.
  - The quantitative comparison of these two densities is the next conjecture (L84).

### L84 — ε-core: interpolation versus deficit (analysis) [P-sketch, OPEN]
- **Setting.** Take `lam = (1−ε)Λ + e⋆μ ∈ W`, with `supp e ⊆ [n₀, N_e]` and `n₀ ≥ 2`.
- **Multiplicity channel.** Multiple critical zeros need `E(ρ) = 0` on the line, and `E` has multiplicity `≥ m−1` there.
  - Zeros of the exponential polynomial `E` in any vertical strip up to height `T` number at most `(log(N_e/n₀)/2π)T + O(1)`. So the multiplicity excess is `Σ(m−1) ≤ (log(N_e/n₀)/2π)T + O(1)`.
- **Off-line channel.** Density theorems give `N(½+δ, T) = o(T)` for each fixed `δ > 0`.
  - Linear-density off-line zeros must therefore hug the line (`β − ½ → 0`). Each is half of a near-double pair on which `ζ'(ρ)` is small.
  - The interpolation `E(ρ) = (1−ε)ζ'(ρ)` then forces `|E(ρ)|` to be small at linearly many near-line points.
- **Consequence [P].** If `N_e < n₀³`, the multiplicity channel alone cannot pay the deficit `(log n₀/π)T`. Some positive linear density of near-line off-line pairs is then needed: at least `½[(log n₀)/π − log(N_e/n₀)/(2π)]` per unit height.
- **Counting cannot close this.** `H = E − (1−ε)ζ'` has about `T log T` zeros in `σ > ½` (Levinson–Montgomery zeros of `ζ'`), so vanishing at a linear set is consistent.
- **Conjecture L84 (open core).** A real Dirichlet polynomial `E` cannot satisfy `E(ρ) = (1−ε)ζ'(ρ)` at a set of zeros of ζ of positive lower linear density that lie within `o(1)` of the critical line. Evidence: the two sides are independent random-like objects, and the equation imposes two real conditions per point.
- **Status.** L84 is a statement about the joint distribution of `(ζ'(ρ), E(ρ))` at near-line off-line zeros, which are unknown objects. The ε-core is the frontier of the uniqueness half.

### L85 — Can the existence half (PBAP) be proved without zeros? Multiscale uncertainty versus the Landau–Widom decay. NO-GO [P] + producer reframing
- **Conjecture L85 (tested).** PBAP is true even if RH fails, and it can be proved by a multiscale prime-blind uncertainty principle. That would give an unconditional abstract producer (Hahn–Banach), i.e. W ≠ ∅.
  - Motivation: prime-blind tests whose spectrum lies above τ* have `arch > 0` whatever the zeros are (L70, L73). So PBAP concerns only low-frequency mass, and far off-line zeros are invisible to it.
- **Attack.** Split a prime-blind level-`A` PD function as `Φ = Φ_L + Φ_H` at frequency `τ₁`. Write `m_L = Φ_L(0)` and `m_H = Φ_H(0)`.
  - Bernstein's inequality plus the vanishing of `Φ` at `log n` (spacing `1/n`) gives `|Φ_L| ≤ m_H + η` on `|x| ≥ log N₀`, where `N₀ = τ₁ m_L/η`.
  - So `Φ_L` is a near-prime-blind test at the smaller level `½ log N₀`, and `arch(Φ) ≥ M(½ log N₀)·m_L − O(m_H + η) + A(τ₁) m_H`.
- **Kill.** The recursion cannot close.
  - Under the Landau–Widom law, `M(x) ≈ exp(−c N(2πe^{2x})/log N)`, so `M(½ log N₀) ≈ exp(−c N₀ log N₀)` with `N₀ ∝ 1/η`.
  - The error `η` must be `≪ exp(−c/η · log(1/η))`, which is impossible for small `η`.
  - Every perturbative (error-absorbing) multiscale argument therefore fails. This is the quantitative form of CANNOT-478: margins decay super-exponentially in the level, faster than any approximation error.
  - Verdict: **FALSE as a strategy** (not as a statement). PBAP may still be true, but not provably by estimates with errors.
- **Positive survivor [P]: any proof of PBAP must be an exact identity.** It must be a sum-of-squares certificate `arch(Φ) = Σ_k |L_k(Φ)|²` (or a positive measure) that holds exactly on the prime-blind cone.
  - The explicit formula of any L-function with Γℝ archimedean data supplies such identities with slack `½ log(conductor)·Φ(0) ≥ 0`. For example, a real quadratic `ζ_K = ζ L(χ_d)` gives `arch(Φ) ≥ −c log(rd_K)·Φ(0)` under GRH, and bounded-root-discriminant towers cannot push the slack to zero.
  - Zero slack forces conductor 1 with archimedean factor exactly Γℝ. By the degree-1 Selberg-class classification (Kaczorowski–Perelli) that is ζ itself.
  - **Producer statement (PC-85).** Among all L-function–type positive certificates, the unique exact producer of prime-blind archimedean positivity is ζ's own explicit formula. Any other producer of W ≠ ∅ must be an exact identity of non-L-function type.
    - This separates the existence problem cleanly: find an exact, non-arithmetic SOS certificate for `arch` on the integer-lag-blind cone.
- **Finite-level transfer [P-sketch].** A prime-blind test concentrated at height `γ₀` has `arch ≥ ½ log(γ₀/2π)·mass`, so it detects off-line zeros only through low-frequency mass.
  - A level-`A` test resolves an off-line pair at height `γ₀` only if `e^{2Aδ}` beats the `≈ log γ₀/(2πA)` on-line zeros in its resolution cell. So RH verified to height `exp(4πA e^A)` gives Weil positivity of `Λ` at level `A`.
  - With Platt–Trudgian (`3·10^{12}`) this gives `A ≈ 1.1`, compared with 0.8 certified in arXiv:2608.24827. This uses external verified data, so it is not a Lean target (no computations).

### L86 — ε-core: the interior Herglotz constraint at off-line zeros [P]; the core survives
- **New constraint.** Inside the half-plane, `Φ_lam` is analytic at an off-line zero `ρ` (by (iv), `E(ρ) = (1−ε)ζ'(ρ)`). Its value there is
  `Φ_lam(ρ) = G_∞(ρ) + β(1/ρ + 1/(ρ−1)) − [E'(ρ) − (1−ε)ζ''(ρ)]/ζ'(ρ)`,
  and Weil positivity forces `Re Φ_lam(ρ) ≥ 0`.
- **Near-double pairs.** Write `ζ ≈ c(s−ρ)(s−ρ')h`, with the pair `ρ, ρ' = ½ ± δ + iγ` and `δ → 0`.
  - Then `ζ''/ζ'(ρ) ≈ 1/δ` and `ζ'(ρ) ≈ 2δ c h(ρ)`.
  - The constraint reads `Re(E'(ρ)/(c h(ρ))) ≤ 2(1−ε) + O(δ log γ)`: a one-sided bound on `E'` at each defective pair.
  - It is consistent with the interpolation (iv) and with the deficit (v). No contradiction.
- **Status of the ε-core.** Five constraints are now listed: (ii) pointwise dissipativity, (iii) realness, (iv) interpolation, (v) deficit, and the interior bound above.
  - All five are simultaneously consistent with a hypothetical ζ that misses the critical line at linear rate `log n₀/π` through near-double off-line pairs.
  - Every constraint is local at zeros or averaged, and linear-scale defect statistics are beyond current zero-density technology (known: `N − N₀ ≤ 0.59 N`).
- **Conclusion.** The ε-core is a genuine barrier. Proving uniqueness (or "W ≠ ∅ ⇒ RH") in this class is at least as strong as showing that ζ has `o(T)` defective zeros that are both near-double and on the zero set of `G_E`, for every fixed Dirichlet polynomial `E`. Recorded as the precise open core (L84 conjecture).

### L87 — A candidate producer: the margin-optimal (Minkowski-type) completion. CANDIDATE + finite-level theorems [P] + conjecture
- **Idea (the Minkowski analogy, made operational).** Minkowski gets existence from a variational principle (maximize volume under a linear constraint), not from an explicit formula. The analogue here: at each level `A`, take the weights that maximize the Weil margin, and send `A → ∞`.
- **Definition.**
  - The level-`A` margin is `σ_A(lam) := inf{Q_lam(f)/‖f̂‖² : f polar, supp f ⊆ [−A, A]}`. It is concave in `lam`, as an infimum of affine functions.
  - `M(A) := max_{box} σ_A`. The *optimal producers* are `𝒫_A := argmax σ_A`.
- **Theorem L87.1 [P].**
  - (a) `𝒫_A` is a nonempty compact convex subset of the level-`A` box (the box is compact and `σ_A` is concave and upper semicontinuous).
  - (b) `M(A)` is nonincreasing in `A`.
  - (c) If `M(A) ≥ 0` for all `A`, every limit point `lam*` of `lam_A ∈ 𝒫_A` lies in `W`, by the closedness argument of L68. In that case the optimal producers are a canonical construction of a Weil-positive system.
  - (d) Euler–Lagrange (minimax of L79): for `lam ∈ 𝒫_A` there is a probability combination `ν_A` of level-`A` polar tests with `Σα Q_lam(f) = M(A)`. At every atom `n` where `lam(n)` is strictly inside the box, `ν_A` is **prime-blind at `n`**: its autocorrelation vanishes at `±log n`.
    - So the extremal dual of the optimal producer is prime-blind exactly at the unsaturated atoms. Saturated atoms sit on the box faces realized by the two-point resonators.
- **Producer Conjecture L87 (falsifiable).**
  - (i) `M(A) > 0` for every `A`. Equivalently, PBAP holds with strict margins at every finite level.
  - (ii) Λ is asymptotically optimal: `log M(A) = −(2π² + o(1))·N(T*)/log N(T*)` with `T* = 2πe^{2A}`. This is the Landau–Widom rate observed for `λ_min(Λ)` in arXiv:2608.24827.
  - (iii) `𝒫_A → {Λ}` coefficientwise.
  - If (i) holds, (c) gives an unconditional producer `lam* ∈ W`. If in addition (iii) holds, `lam* = Λ`, so `Λ ∈ W` and RH follows.
  - Evidence:
    - `Λ ∈ W_A` for `A ≤ 0.8` (certified), so `M(A) ≥ λ_min(Λ, A) > 0` there;
    - under RH, `M(A) ≥ λ_min(Λ, A)`;
    - L74 and L85 say no producer can beat `exp(−c e^{2A})`, because a prime-blind test at level `A` can put its spectrum up to the Nyquist height `T*`, where the `e^{2A}` integer lags balance the zero count `N(T*) ≈ (A/π)T*`.
- **Why this is a producer and not a constraint.** `𝒫_A` is constructed (compactness plus concavity) at every level where `M(A)` is finite. The positivity of the limit reduces to one scalar inequality per level (`M(A) ≥ 0`), and the Euler–Lagrange equation (d) makes the optimal producer computable as a finite convex program at each level.
  - The next provable targets:
    - the Nyquist balance: `M(A) ≤ exp(−c e^{2A})` unconditionally, by explicit prime-blind extremal tests;
    - whether the optimal producer at the first nontrivial level (one free atom, `n = 2`) has `lam*(2) → log 2`.
- **L87 first-level analysis [P-sketch].** Take `2A ∈ (log 2, log 3)`, so only the atom `n = 2` is visible. Write `σ_A(λ₂) = inf_f [arch(f) − √2 λ₂ Re g_f(log 2)]/‖f̂‖²`.
  - By first-order perturbation at `λ₂ = 0` (simple archimedean ground state `f₀`), `σ_A'(0) = −√2 Re g_{f₀}(log 2)`.
  - For `2A` just above `log 2`, `g_{f₀}(log 2)` is the product of the two edge tails of the even ground state, so it is positive. Hence **the optimal weight at 2 is NEGATIVE at the first prime level**. `Λ(2) = log 2` lies in `W_A` (certified margin), but it is not margin-optimal there.
  - Consequence for the candidate: the optimal producer is non-arithmetic at small levels. Prime weights can only emerge in the limit, as in Conjecture L87(iii): `λ₂*(A) → log 2`, through a sign change of the optimal weight at 2.
  - The first predicted crossing level of `λ₂*` through `0` is a falsifiable, finite-dimensional test of the candidate.

### L88 — Explicit producers with conductor slack, and why the pole must be logarithmic [P]
- **Setting.** `W_c` is the Weil cone for ζ's archimedean datum plus a constant `c`, i.e. conductor `e^{2c}`. Producers for `c ≥ 2.69` are trivial (`lam = 0`).
- **Theorem L88.1 (finite-weight threshold, duality) [P].** Let `c_fin := inf{c : ∃ finitely supported lam ∈ W_c}`.
  - Finite `lam` has no pole (`β = 0`). Far corrections (L75) then make every test effectively admissible, so `lam ∈ W_c` ⟺ the symbol `A(t) + c − Σ lam(n) n^{−½} cos(t log n)/π` is `≥ 0` pointwise.
  - By LP duality, `c_fin = sup{−∫A dν : ν a probability measure with ν̂(±log n) = 0 for all n ≥ 2}`, a *prime-blind Fejér problem* with no level and no polarity restriction.
  - Band-limited `ν` (`ν̂` supported in `(−log 2, log 2)`) are automatically prime-blind and give `c_fin ≥ c_F := −λ_min(arch, non-polar, L²[−½log 2, ½log 2]) > 0` (the Fejér threshold). The trivial bound gives `c_fin ≤ 2.69`.
  - One negative atom, `lam(2) = −κ`, balances `t = 0` against `t = π/log 2` and gives roughly `c_fin ≲ 1.45` (rough estimate, not certified).
- **Theorem L88.2 (ζ-type poles fail at every slack) [P, conditional on a known large-values input].**
  - Let `D = β(ζ − 1) + D₀` with `β > 0` and `D₀` absolutely convergent on `σ ≥ ½`. Weil positivity in `W_c` would force `β Re ζ(½+it) ≤ θ'(t) + c + ‖D₀‖ = O(log t)` for all `t`.
  - The resonance method (Bondarenko–Seip type large values in a prescribed direction) gives `Re ζ(½+it) ≫ exp(c'√(log t/loglog t))` infinitely often. So such `lam` fails for every `c`.
- **Consequence (structural).** A producer below the finite threshold (`c < c_fin`, in particular ζ's datum `c = 0`) needs a pole at `s = 1` (L75, L88.1). Its Dirichlet series must have one-sided bounded real part on the critical line *despite* the pole, which rules out every form "ζ plus an absolutely convergent series".
  - The only known mechanism with this property is a logarithmic derivative whose real part on the line is pinned by a functional equation: `Re(−ζ'/ζ) = θ'`.
  - So **the producer is forced to be logarithmic, and FE-pinned in every known instance.** The quantitative gap between `c_fin > 0` and `c = 0` is exactly the part of ζ's datum that only the explicit formula supplies.
- **Next.** Pin down `c_fin`: its exact extremal prime-blind measure, and whether `c_fin = c_F` or strictly larger. It is a finite-dimensional-in-spirit extremal problem with an arithmetic constraint set `{log n}`.

### L89 — ε-core completions are excluded by finite zero verification, one `e` at a time [P]
- **Observation.** The ε-core cannot be excluded by statistics (L83–L86), but it *can* be excluded by finitely many zeros.
  - Realness (iii) says `X_E(t) = Re(e^{iθ(t)} E(½+it))` vanishes at every distinct critical zero.
  - The count lemma (L82 proof, step 2) bounds the zeros of `G_E` up to `T` by `(θ(T) − T log n₀)/π + C_e log T`.
  - Riemann–von Mangoldt gives `N(T) = θ(T)/π + 1 + S(T)`, with `|S(T)| ≤ 0.112 log T + 0.278 log log T + 2.51` (Trudgian).
- **Theorem L89 [P, with external verified input].**
  - Fix `e ≠ 0` finitely supported with `e(1) = 0` and `n₀ = min supp e`. Let `T(e)` be the least `T` with `(T/π) log n₀ > C_e log T + |S(T)| + 1`.
  - If all zeros of ζ with `0 < γ ≤ T(e)` are simple and critical, then `(1−ε)Λ + e⋆μ ∉ W` for **every** `ε ∈ (0, 1]`. The case `ε = 0` is L82, which is unconditional.
  - With the Platt–Trudgian verification (all zeros up to `3·10^{12}` simple and critical), this excludes every `e` whose count constant satisfies `C_e ≲ 10^{10}`.
- **Proof.** Up to `T(e)`, every zero is a distinct critical zero, so `X_E` would need `N(T(e)) > (θ(T(e)) − T(e) log n₀)/π + C_e log T(e)` zeros, more than `G_E` has. ∎
- **Meaning.**
  - Excluding the ε-core is *decidable per `e`*. For each fixed Dirichlet polynomial, a finite verification suffices, uniformly in `ε`. Linear-scale statistics are needed only for a *uniform-in-`e`* statement.
  - Combined with L81 (degree-1 part, unconditional) and L82 (pure Möbius part, unconditional), every finite-support singular perturbation class studied so far is either excluded unconditionally or reduced to finite verification.
  - `C_e` is explicit: it comes from the dominance abscissa `A(e)` and a Jensen bound on the horizontal segments. So `T(e)` is effectively computable.
- **Lean.** Not a Lean target, because it needs verified zero data (no computations). The unconditional count lemma for `G_E` is a Lean target, reusing the Zeta23 RvM argument-principle machinery.

### L90 — Existence from zero-density? A PBAP proof via prime-blind spreading. ATTEMPT + KILL [P]
- **Conjecture L90.** Prime-blindness forces a test's spectrum to spread up to the Nyquist height `T* = 2πe^{2A}` (L85). A spread spectrum averages over many zeros, so the off-line contributions to `arch(Φ) = Σ_ρ Φ̂(γ_ρ)` might be controlled by *unconditional* zero-density and displacement bounds. That would prove PBAP, i.e. W ≠ ∅, without RH.
- **Mechanism (proved) [P].**
  - For `Φ̂ = Σ α_i F̂_i F̂_i^*` with `F̂_i` of exponential type `A`, an off-line pair `½ ± δ + iγ` contributes `2 Re Σ α_i F̂_i(γ+iδ) conj F̂_i(γ−iδ)`.
  - This is at least `2Φ̂(γ) − C (Aδ)² (P_δ ⋆ Φ̂)(γ)` when `Aδ ≤ 1`. When `Aδ > 1` it is at least `−2e^{2Aδ} (P_δ ⋆ Φ̂)(γ)`. Here `|F̂(x+iy)|² ≤ e^{2A|y|} (P_y ⋆ |F̂|²)(x)` by Jensen and Cauchy–Schwarz.
  - Hence `arch(Φ) ≥ −C ∫ Φ̂ K_dev`, with `K_dev(τ) = Σ_{off} min((Aδ_ρ)², e^{2Aδ_ρ}) P_{δ_ρ}(τ − γ_ρ)`.
  - By Selberg's `Σ (β−½) ≪ T` and density theorems, `K_dev` has average `O(A² + e^A T^{−c})` per unit height.
- **Kill.** `arch < 0` needs the deviation to beat the positive zero sum, which has density `≈ (1/2π) log τ` wherever `Φ̂` has mass.
  - The comparison `A² ≷ log τ` is decided in favour of the deviation up to height `e^{cA²}`. That height exceeds the Nyquist height `e^{2A}`, where prime-blind spectra live.
  - The spreading does reach many zeros, but the unconditional displacement moments are too weak by exactly the Nyquist margin.
  - More fundamentally, the bound is `arch ≥ −(deviation)`, never `arch ≥ 0`. It is again an estimate with error, which cannot prove an exact statement (CANNOT-478).
  - **Verdict: FAILS.**
- **Positive survivor [P] ("PBAP with explicit slack from zero displacement").** For every prime-blind level-`A` polar Φ:
  `arch(Φ) ≥ −C ∫ Φ̂(τ) K_dev(τ) dτ`.
  - Equivalently, `A + C·K_dev` (the archimedean symbol plus a zero-displacement kernel) is prime-blind-positive unconditionally.
  - So `W(A + C K_dev) ≠ ∅` unconditionally: an explicit *producer at conductor 1 up to the off-line displacement kernel*. The slack is exactly the Poisson-smoothed off-line zero measure, weighted by `(Aδ)² ∧ e^{2Aδ}`.
  - The slack vanishes iff there are no off-line zeros. This is a precise producer with an explicitly RH-shaped defect, sharper than the conductor slack of L88 (constant `c_fin`).

### L91 — First test of the margin-optimal producer (L87): the optimal weight at 2 is negative at the first prime level [P, conditional on two ground-state facts]
- **Setting.** Levels `A` with `w := 2A − log 2 ∈ (0, log(3/2))`, so only the atom `n = 2` is visible. Write `σ_A(λ₂) = inf_f Q_{λ₂}(f)/‖f̂‖²`, where
  `Q_{λ₂}(f) = arch(f) − 2√2 λ₂ Re g_f(log 2)` and `g_f = f ⋆ f̃`.
- **Two ground-state facts.**
  - (G1) The polar archimedean ground state `f₀` at level `A` is simple and even (reported in arXiv:2608.24827).
  - (G2) The minimizer, taken in the `L²[−A, A]` closure, has `f₀(±A) ≠ 0`, as prolate-type extremals do.
- **Theorem L91 [P, given G1 and G2].**
  - `g_{f₀}(log 2) = ∫_0^w f₀(A−u) f₀(−A+w−u) du = w f₀(A)² + O(w²) > 0` for small `w`, by evenness.
  - Hence `σ_A'(0) = −2√2 Re g_{f₀}(log 2)/‖f̂₀‖² < 0`, and the optimal weight satisfies `λ₂* < 0`.
  - Quantitatively, `λ₂*` sits where the even branch `σ_even(λ₂)` meets the odd branch `σ_odd(λ₂)`. The odd ground state has `g(log 2) ≈ −w f_odd(A)² < 0`, so it rises as `λ₂` decreases.
  - Therefore `λ₂* = −(σ_odd(0) − σ_even(0))/(2√2 w (f₀(A)² + f_odd(A)²)) + O(1)`: **large and negative as `w → 0⁺`**.
- **Consequence for Producer Conjecture L87(iii).** The margin-optimal producer starts at `λ₂* ≈ −C/w` at the first prime level. It would have to cross zero and converge to `log 2`, so prime weights appear only as a limit.
  - Any analytic proof of L87(iii) must explain this crossing. The candidate producer is genuinely non-arithmetic at finite levels.
- **Status.** G1 is numerical (from the literature) and G2 is standard for prolate-type extremals but unproved here. The crossing level is a finite-dimensional, falsifiable prediction, deferred because of the no-computations rule.

### L92 — Exact identities on the integer-blind cone, and the square-of-ζ producer. IDENTITIES [P] + OBSTRUCTION [P]
- **Motivation (L85/PC-85).** Existence needs an *exact* positive identity on the integer-blind cone `𝒞 = {Φ PD, compact support, polar, Φ(±log n) = 0 for n ≥ 2}`. So look for exact identities on `𝒞` that involve no zeros.
- **Identity I1 (zero-free, prime-free) [P].**
  - For `Φ ∈ 𝒞` and `Re s > 1`: `(1/2π)∫ Φ̂(τ) ζ(s − iτ) dτ = Σ_n Φ(log n) n^{−s} = Φ(0)`.
  - Continue analytically to `Re s = ½`. The only singularity crossed is the pole of ζ at `s − iτ = 1`, at `τ = t + i(1−σ)`.
  - Result: `(1/2π)∫ Φ̂(τ) ζ(½ + i(t−τ)) dτ = Φ(0) − κ Φ̂(t + i/2)`, with `κ = ±1` fixed by orientation. By polarity this reduces to `Φ(0)` at `t = 0`.
  - The convolution of an integer-blind spectrum with `ζ(½+i·) = e^{−iθ} Z` is exactly explicit. With `−ζ'/ζ` in place of ζ, the same continuation crosses the zeros and returns the explicit formula.
  - **Moral:** on `𝒞`, ζ itself is zero-free-computable; only its logarithm sees the zeros.
- **The square-of-ζ producer (positivity for free) [P-sketch].** `∫ Φ̂ |ζ(½+i·)|² ≥ 0` trivially. The exact mean-value expansion (diagonal plus off-diagonal, with the functional equation supplying `log(t/2π) = 2θ'(t) + O(t^{−2})`) gives, for `Φ ∈ 𝒞`,
  `2π·arch(Φ)·c₁ = ½ ∫ Φ̂ |ζ(½+i·)|² − c₂ Φ(0) − ½ R_rat(Φ)`,
  where `R_rat(Φ) = 2π Σ_{m ≠ n, n ∤ m, m ∤ n} (mn)^{−½} Φ(log(m/n))`.
  - Integer-blindness kills every integer and reciprocal-integer lag. Only the coprime-ratio lags `log(m/n)` survive.
  - So `arch ≥ −c Φ(0)` (a constant conductor slack) holds on the sub-cone where `R_rat ≤ 0`.
- **Obstruction [P].** `R_rat` involves lags `log(m/n)`, which are dense in `ℝ`. A rational-blind PD function vanishes on a dense set and is therefore zero, so the square-of-ζ producer cannot be made exact by blindness.
  - Mollified squares `∫ Φ̂ |ζM|²` generate lags `log(hm/(kn))`, which are still dense. This is the mollified-mean-square terminus of the corpus again, now seen as the exact defect of a positivity producer.
- **What is new.** The two exact identities on `𝒞` separate cleanly: ζ-convolutions are zero-free (I1), and log-derivative convolutions carry the zeros. The only free positivity (`|ζ|²`) fails to be exact by precisely the coprime-rational-lag sum `R_rat`.
  - A producer at conductor 1 of this type would need a sign law `R_rat(Φ) ≤ c₂ Φ(0)` on `𝒞`.
  - **Next conjecture (L93):** that sign law holds at levels `A` where the only rational lags in `[−2A, 2A]` with `m, n ≤ e^{2A}` are few, and it fails beyond. Test the first rational lag `log(3/2)`, which enters at `2A > log(3/2)` before `log 3`.
- **L92 correction (self-audit).** The square-of-ζ expansion is not exact as written.
  - For compactly supported Φ, the off-diagonal sum `Σ_{m≠n} (mn)^{−½} Φ(log(m/n))` over *all* `m, n` diverges: there are about `n·(e^{2A} − e^{−2A})` values of `m` per `n`, each weighted `1/n`.
  - The identity holds only as a truncated mean value, with AFE lengths `m, n ≤ √(t/2π)` and `O(T^{½+ε})` errors. It is therefore an estimate with error, not an exact certificate, and falls under CANNOT-478 again.
  - Identity I1 (ζ-convolution) *is* exact. It carries no positivity.
  - **Verdict: the square-of-ζ route fails** for the same reason as L85 and L90, and L93 is withdrawn. The surviving knowledge is the clean split: exact zero-free identities (I1) carry no sign; signed identities (squares, logarithms) are either inexact or pass through the zeros.
- **L91 refinement (hypothesis G2 replaced).** The archimedean Weil operator on `[−A, A]` has symbol `≈ ½ log|τ|`, a logarithmic Laplacian.
  - For Dirichlet eigenfunctions of the logarithmic Laplacian on an interval, the boundary behaviour is `f(A − u) ≍ |log u|^{−1/2}` (Chen–Weth-type boundary regularity; to be checked against the literature). So `f₀(±A) = 0` and G2 as stated is false.
  - The conclusion survives. With `f₀` even and of one sign near the edges, `g_{f₀}(log 2) ≍ ∫_0^w |log u|^{−½} |log(w−u)|^{−½} du ≍ w/log(1/w) > 0`.
  - So `σ_A'(0) < 0` and the optimal weight is `λ₂* ≍ −C log(1/w)/w`: still large and negative at the first prime level. L91 holds with (G2) replaced by "`f₀` has one sign near the edges".

### L95 — The finite-weight producer threshold is strictly beyond the Fejér threshold: `c_fin > c_F` [P, generic nondegeneracy]
- **Recall (L88).** `c_fin = sup{−∫A dν : ν a prime-blind probability measure}` and `c_F = sup{…: ν̂ supported in (−log 2, log 2)}`.
- **Theorem L95 [P, assuming one generic nondegeneracy].** `c_fin > c_F`.
  - Let `ν₀ = |φ₀|²` be the band-limited extremal, with `φ̂₀` supported in `[−½ log 2, ½ log 2]` and `‖φ₀‖ = 1`. Perturb to `φ = φ₀ + εφ₁`, with `φ̂₁` supported in `[−½ log 3, ½ log 3]`.
  - Prime-blindness up to `log 3` needs one real condition at first order: `Re(φ̂₁ ⋆ φ̂̃₀)(log 2) = 0`, the cross term at lag `log 2`. The lag `log 3` sits on the boundary and is free.
  - The mass needs one more: `Re⟨φ₀, φ₁⟩ = 0`.
  - The first variation of `−∫A|φ|²` is `−2ε Re⟨Aφ₀, φ₁⟩`. It vanishes on the band-limited `φ₁` (extremality) but not on the enlarged space, unless `Aφ₀` lies in the span of the two constraint representers. That is the nondegeneracy assumption; it is codimension ≥ 1 and generically true.
  - Choosing the sign of `ε` strictly increases `−∫A dν`. ∎
- **Consequence.** The optimal slack for arithmetic-free (pole-free) producers is not attained at any finite bandwidth. Each new integer lag `log n` both constrains and enlarges the admissible cone, and the net effect is strictly favourable at the first step.
  - `c_fin` is therefore a genuinely infinite-dimensional constant of the pair (Γℝ, `log ℕ`). It is the pole-free analogue of `M(A)` from L87, and it sits strictly between `c_F` and the one-atom value (`≈ 1.45`).
  - Open core: whether `c_fin` is attained in the limit, and its value. This is the "prime-blind Fejér constant" of ζ's archimedean place.

### L96 — The F₁ reading of the three terms of Weil's explicit formula; the producer as a limit of Weil's theorem for curves [P + CONJECTURE]
- **Exact computation (polar term as the q → 1 limit of P¹) [P].**
  - For `P¹/F_q`, the degree-`k` prime weight in the explicit formula (lag `k log q`) is `N_k(P¹) q^{−k/2} log q = (q^{k/2} + q^{−k/2}) log q`.
  - As `q → 1` with `x = k log q` fixed, the atomic measure `Σ_k (q^{k/2} + q^{−k/2}) log q · δ_{k log q}` converges weakly to `(e^{x/2} + e^{−x/2}) dx = 2cosh(x/2) dx`.
  - That is exactly the **polar term** of ζ's explicit formula (the pole at `s = 1` and its reflection). So ζ's polar part is the `F₁`-limit of the point count of `P¹`.
- **The archimedean term as an F₁ point count [P].**
  - `Â(x) = c₀δ₀ − K(|x|)` with `K(x) = Σ_{k≥0} e^{−(2k+½)x} = e^{−x/2}/(1 − e^{−2x})` (trivial zeros at `−2k`).
  - In the normalization used for curves, `K(x) = e^{−x/2}·N_∞(x)` with `N_∞(x) = 1/(1 − e^{−2x}) = Σ_k e^{−2kx}`. The archimedean place contributes like an `F₁`-object whose "number of points of degree `x`" is `Σ_k e^{−2kx}`. This is the regularized-determinant spectrum `{−2k}` of Deninger and Manin, here read directly off the explicit formula.
- **Consequence (structural).** ζ's explicit formula has three terms, each an `F₁`-limit point count:
  - finite primes (atoms at `log p^k`),
  - the archimedean object (continuous density `K`),
  - `P¹` (polar `2cosh(x/2)`).
  Weil's theorem for curves proves positivity when all terms are point counts of *one* curve, via Hodge index on `C × C`.
- **Conjecture L96 (producer as a limit of Weil's theorem).** There is a family of curves `C_j/F_{q_j}` with `q_j → 1` (formally) and `g_j log q_j → const` whose normalized explicit-formula distributions converge on polar tests to ζ's. Each is positive by Weil's theorem, so the limit is positive: RH as a limit of Hodge index.
  - **Test.** The limiting prime part of any such family is a *continuous* positive density: the lags `k log q_j` fill `ℝ`. ζ's finite-prime part is *atomic* at `log n`. So the finite primes cannot be such a limit.
  - Only the polar and archimedean terms admit `F₁`-curve limits. The finite primes must come from a genuinely arithmetic object (`Spec ℤ` itself).
  - **Verdict:** the naive limit **FAILS** for the finite-prime term. What survives is that the archimedean and polar terms are `F₁` point counts, and the missing producer is a Hodge index theorem on `(Spec ℤ ∪ ∞) × (Spec ℤ ∪ ∞)` over `F₁` that pairs the atomic finite part with these two continuous parts.
  - This is the Connes–Consani/Deninger programme; the explicit identification above of the archimedean point count `1/(1 − e^{−2x})` is only a recasting of known material.

### L97 — Pólya's theorem as the one known conductor-1 real-rootedness producer; the truncation ladder fails by tail non-convergence [P]
- **Observation.** Riemann's kernel is `Φ(u) = Σ_{n≥1} n^{−½} φ₁(u + log n)`, with `φ₁(v) = (2π²e^{9v/2} − 3πe^{5v/2}) exp(−πe^{2v})` the single-theta-term kernel. In Weil language: a positive combination, with weights `n^{−½}`, of translates by `log n` of one archimedean kernel.
  - Pólya (1926): the symmetrized `n = 1` kernel has a Fourier transform with **only real zeros**. That transform is `G(s) + G(1−s)` (with `G(s) = ½ s(s−1) Γℝ(s)`), i.e. ξ with ζ replaced by its one-term approximate functional equation `1 + χ(s)`.
  - This is an unconditional producer of positivity at **conductor 1** with ζ's exact archimedean factor. It lies outside the Dirichlet framework: its "prime side" is `χ(s)`, not atoms at `log n`.
- **Truncation ladder (conjecture tested).** Let `Φ_N^{sym}(u) = ½[Φ_N(u) + Φ_N(−u)]` with `Φ_N = Σ_{n≤N}`. Its transform is the Gonek–Montgomery function `G·ζ_N`, which satisfies the FE and has 100% of its zeros on the line asymptotically.
  - If `Φ_N^{sym}` gave real zeros for all `N` and converged to Φ in `L¹(e^{c|u|})`, Hurwitz would give RH.
- **Kill (tail non-convergence) [P].** At `u ≈ −log N`, `Φ(u) = Φ(log N)` is doubly-exponentially small by the theta functional equation.
  - That smallness comes from cancellation between `n ≤ N` and `n > N`: the terms `n^{−½} φ₁(log(n/N))` are of size `N^{−½}` for `n ≍ N`.
  - Truncation leaves `Φ_N(−log N) − Φ(−log N) ≍ Σ_{n>N} n^{−½} φ₁(log(n/N)) ≍ N^{½} ∫_1^∞ φ₁(log x) dx/x`, which does not tend to 0.
  - So `Φ_N^{sym}` does not converge to Φ in any norm controlling Fourier zeros. This matches the known non-convergence of `ζ_N` to ζ in the strip. **FAILS.**
- **Positive survivor.** The theta functional equation *is* the cancellation between short and long translates. The one conductor-1 producer known (Pólya) is the `N = 1` shadow of that cancellation, and any extension must keep the full cancellation.
  - The candidate object is therefore a family that interpolates `Φ₁^{sym} → Φ` *through modular kernels*, such as partial theta sums completed by their modular images, rather than through Dirichlet truncation.
  - **Conjecture L98 (next):** the modular completions `Φ^{(N)}(u) := Σ_{n≤N} n^{−½}[φ₁(u + log n) + φ₁(−u + log n)] − (overlap corrections from θ(1/x) = √x θ(x))` have Fourier transforms with only real zeros. Test at `N = 2`.

### L98 — Modular completions of truncated theta: exact functional equation and Hurwitz convergence, but zero-annihilation at the cutoff. KILL + refined conjecture [P]
- **Construction.** Take Riemann's symmetric integral with a truncated theta series, `ψ_N(x) = Σ_{n≤N} e^{−πn²x}`:
  `ξ_N(s) := ½ + (s(s−1)/2) ∫_1^∞ ψ_N(x) (x^{s/2} + x^{(1−s)/2}) dx/x`.
  - Exactly `ξ_N(s) = ξ_N(1−s)`, and it is real on the critical line.
  - Since `sup_{x≥1} |ψ − ψ_N| ≤ Σ_{n>N} e^{−πn²}`, we get `ξ_N → ξ` locally uniformly, so **Hurwitz applies**: every zero of ξ is a limit of zeros of `ξ_N`. This is the correct modular completion. The L97 truncation had no such convergence.
- **Explicit form.** `∫_1^∞ e^{−πn²x} x^{a−1} dx = (πn²)^{−a} Γ(a, πn²)`. Writing `Γ(a, ·) = Γ(a) − γ(a, ·)` and expanding `γ(a, πn²) = (πn²)^a e^{−πn²} Σ_k (πn²)^k/(a)_{k+1}`:
  - the `Γ(a)` parts give `Σ_{n≤N} n^{−s}` times the archimedean factor, together with the reflected term;
  - the `k = 0` parts give the *non-decaying* constant `Σ_{n≤N} e^{−πn²}`, since `(s(s−1)/2)(2/s + 2/(1−s)) = −1`.
  - So `ξ_N(½+it) = c_N + (oscillation of size ≍ |G(½+it)|·|P_N|) + O(1/t)`, with `c_N = ½ − Σ_{n≤N} e^{−πn²} − … → 0`. For `N = ∞` the constant cancels exactly, which is the theta functional equation at `x = 1`.
- **Kill of "all zeros real" [P].** For finite `N`, `c_N ≠ 0` and the oscillation amplitude decays like `e^{−πt/4}`. Near the crossover height `T_N` where the amplitude equals `|c_N|`, the real function `c_N + A(t) cos φ(t)` loses its zeros in pairs, and these become **off-line zeros** (conjugate pairs in `t`). So `ξ_N` has zeros off the line for every `N`. **L98 as stated is FALSE.**
- **Refined conjecture L98′ (producer ladder).** For every `N`, all zeros of `ξ_N` with `|γ| ≤ (1 − ε) T_N` lie on the critical line. Here `T_N ≍ (4/π) log(1/c_N) → ∞`.
  - By Hurwitz and locally uniform convergence, L98′ for all large `N` implies RH.
  - Each `ξ_N` is an explicit finite combination of incomplete gamma functions, so each rung is a statement about one explicit entire function. `N = 1` is a Pólya-type object.
  - The truncation-induced off-line zeros are confined to the crossover window. That separates "defects produced by truncation", which are provably present, from the RH question below the window.
  - Status: L98′ contains RH up to height `(1−ε)T_N`. Uniform-in-`N` proof = RH. **Open core:** a Pólya-type real-rootedness proof below the crossover window for fixed small `N` (`N = 1, 2`), as the first rung.
- **L98 audit (crossover scale; the ladder is RH-equivalent).**
  - Decompose `ξ_N = [G P_N + G(1−s) P_N(1−s)] + R_N`, with `G(s) = (s(s−1)/2) π^{−s/2} Γ(s/2)` and `P_N = Σ_{n≤N} n^{−s}`.
  - The remainder `R_N` has the asymptotic expansion `c_N + O(C(N)/t)`, with `c_N = Σ_{n>N} (4πn² − 1) e^{−πn²}` exactly (from `Σ_n (4πn² − 1) e^{−πn²} = ½`, the derivative of the theta functional equation at `x = 1`). This expansion is valid only for `t ≫ N²`.
  - For `t ≲ 2πN²` the bracket *is* the Riemann–Siegel main term. By the approximate functional equation `R_N` is then exponentially small, and `ξ_N ≈ ξ`.
  - So the crossover height is `T_N ≍ 2πN²`: `ξ_N` is the FE-exact Riemann–Siegel approximant with `N` terms.
- **Verdict.** L98′ says that the zeros of the `N`-term FE-exact Riemann–Siegel approximant below its validity height are real, for every `N`.
  - It implies RH (Hurwitz), and RH plus simplicity/stability of zeros implies it rung by rung, since `ξ_N` is within `e^{−c N²}` of ξ below `T_N`.
  - So it is **RH-equivalent, not a producer**. The Platt–Trudgian verification settles rungs up to `N ≈ 7·10^5`.
  - The new facts here: exact FE, Hurwitz convergence, `c_N` in closed form, `T_N ≍ 2πN²`, and zero annihilation beyond `T_N` (off-line escape curve). They make the approximation ladder precise but add no positivity mechanism.

### L99 — Real-rootedness producers versus Weil-positivity producers: the gap is the low-frequency phase deficit [P]
- **Pólya–Hermite–Biehler producers [P].** Let `P = 1 + Σ_{2≤n≤N} a_n n^{−s}` be real with `Σ_{n≥2} |a_n| n^{−½} < 1`, so `P` is zero-free on `σ ≥ ½`. Let `ξ_P := G·P + G(1−s)·P(1−s)`, with `G = (s(s−1)/2) π^{−s/2} Γ(s/2)`.
  - Then `ξ_P(½+it) = −2|G P| cos(θ(t) + arg P(½+it))`.
  - For `t ≥ t₁(P)` the phase `θ + arg P` is monotone, because `θ' ≍ ½ log t` beats the bounded `|P'/P|`. So the real zeros up to `T` number `θ(T)/π + O_P(1)`.
  - The argument principle on `[−A, 1+A] × [0, T]`, where `P` dominates on the right, gives the same total count. Hence **all but `O_P(1)` zeros of `ξ_P` are on the critical line, unconditionally**.
  - This is a one-parameter family of conductor-1 real-rootedness producers carrying genuine prime structure; Pólya's theorem is the case `P = 1`. It is likely close to known Gonek–Montgomery or Hermite–Biehler results; it is not claimed as new.
- **Why these are not Weil producers [P].**
  - Weil positivity of a weight system `lam` with ζ's archimedean datum means the completed exponential `E_lam` is Hermite–Biehler: `Re E'/E ≥ 0` on `Re s > ½` (L83). For `lam = coefficients of −P'/P`, `E = G·P`.
  - Real-rootedness of the *symmetrization* `E + E^*` is strictly weaker. HB for `E` implies real zeros of `E + E^*`, not conversely.
  - `G·P` fails HB exactly at low frequency: at `s = ½` we have `Re(GP)'/(GP) = θ'(0) + Re P'/P(½) ≈ −2.69 + O(Σ|a_n| n^{−½} log n)`, so it fails.
- **The low-frequency phase deficit (structural law).** Let `𝒟 := ∫_{|t|<6.29} |θ'(t)| dt = 2|θ(6.29)| ≈ 7.06`. This is the total clockwise rotation of `e^{iθ}` below the first sign change of `θ'`.
  - A real-rootedness producer may tolerate this deficit: zeros survive a non-monotone phase.
  - A Weil producer must pay it pointwise with counterclockwise rotation of `arg ζ_lam`. By L88, only a pole at `s = 1` pinned by a functional equation pays it without large values elsewhere. For ζ the pole plus FE pays it exactly: `arg ζ(½+it) = −θ(t)`.
  - **This is precisely why Pólya-type producers, however far extended, can never yield Weil positivity: they never pay `𝒟`.**
- **Conjecture L100.** Among functional-equation-symmetric objects `E + E^*` with `E = G·Y` (`Y` a Dirichlet exponential), Weil positivity (HB of `E`) holds iff `Y` pays the deficit `𝒟` with a pole at 1 *and* `E = E^*`. That is, the functional equation turns real-rootedness into Weil positivity.
  - Evidence: ζ (true under RH); L88 (pole necessary); this entry (FE-free `Y` fails).

### L101 — The pole-point budget: Weil positivity evaluated at s = 1 squeezes the ε-core to ε ≤ λ₁/(1+γ). THEOREM [P]
- **Idea.** The Herglotz function `Φ_lam = G_∞ + β(1/s + 1/(s−1)) − D_lam` of a Weil-positive system has one E-free interior point, the pole `s = 1`, because every Möbius-type perturbation `E/ζ` vanishes there (`1/ζ(1) = 0`).
  - For Λ, `Φ_Λ(1) = ξ'/ξ(1) = Σ_ρ 1/ρ = λ₁ = ½(2 + γ − log 4π) = 0.0230957…`, which is Li's first coefficient. This is the slack of Weil positivity at the pole.
- **Theorem L101.1 (Mertens inequality for completions) [P].** Let `lam` be Weil-positive (polar tests, ζ's archimedean datum, all levels). Suppose:
  - smoothed mean density `β`: `Σ lam(n) n^{−½} R(log n − Y) = β e^{Y/2} ∫R(u)e^{u/2}du + o(e^{Y/2})` for continuous compactly supported `R`;
  - Mertens asymptotics `Σ_{n≤x} lam(n)/n = β log x + C + o(1)` and `Σ_{n≤x} lam(n) = βx + o(x)`.

  Then `C ≤ β + G_∞(1) = β − γ/2 − log 2 − ½ log π = β − 1.5541199…`.
- **Proof (test-function route, no Herglotz P-sketch needed).**
  1. *Non-polar positivity with the produced pole.* For any real compactly supported `ψ`, the polar test `f_Y = ψ − c_Y(ψ(·−Y) + ψ(·+Y))/2`, with `c_Y = 1/cosh(Y/2)`, has `Q_lam(f_Y) ≥ 0`. As `Y → ∞`:
     - the archimedean part tends to `arch(φ_ψ)`;
     - the small lags give `−primes_lam(φ_ψ)`;
     - the far lags `Y` and `2Y` give, by the mean density, `4β p² − 2β p² = 2β p² = β·pole(φ_ψ)`, where `p² = ψ̂(i/2) conj ψ̂(−i/2)`.
     - This is the L75/L77 computation with a general `ψ`. Hence `W_lam(φ) := arch(φ) + β·pole(φ) − primes_lam(φ) ≥ 0` for every autocorrelation `φ = ψ ⋆ ψ̃`.
  2. *The one-sided exponential window.* Take `g_X = e^{−x/2} 1_{[0,X]}`. Then:
     - `φ_X(u) = e^{−|u|/2} − e^{|u|/2 − X}` on `[−X, X]`;
     - `ĝ_X(i/2) = X`, `ĝ_X(−i/2) = 1 − e^{−X}`, so `pole(φ_X) = 2X(1 − e^{−X})`;
     - `primes_lam(φ_X) = 2Σ_{n≤e^X} lam(n)/n − 2e^{−X} Σ_{n≤e^X} lam(n) = 2βX + 2C − 2β + o(1)`;
     - `arch(φ_X) → (1/π)∫ Re G_∞(½+it)/(¼+t²) dt = 2G_∞(1)` (Poisson representation of `G_∞` at `s = 1`).
  3. So `W_lam(φ_X) = 2(G_∞(1) + β − C) + o(1) ≥ 0`. ∎
  - For Λ, `W_Λ(φ_X) = Σ_ρ |ĝ_X(γ_ρ)|²·… → Σ_ρ 1/(ρ(1−ρ)) = 2λ₁`. This is the Bombieri–Lagarias test-function realization of `λ₁`, here applied to an arbitrary completion.
- **Corollary L101.2 (ε-core squeeze) [P].** If `(1−ε)Λ + e⋆μ` is Weil-positive, with `e` finitely supported and `e(1) = 0`, then
  `ε ≤ λ₁/(1+γ) = 0.0230957/1.5772157 = 0.014643…`.
  - Proof: `β = 1 − ε` (PNT for Λ; `e⋆μ` has mean density 0 by PNT for μ). `C = −(1−ε)γ` (Mertens `ΣΛ(n)/n = log x − γ + o(1)`, and `Σ(e⋆μ)(n)/n → E(1)/ζ(1) = 0` by `Σμ(k)/k → 0`). The inequality reads `(1−ε)(1+γ) ≥ 1.5541199`. ∎
  - So every deficient-residue Möbius completion is within 1.47% of Λ in residue. Before this, L83–L89 excluded the ε-core only through zero statistics or per-`e` finite verification.
- **Corollary L101.3 (general perturbation budget) [P].** For a second completion `Λ + w`, where `D_w = β_w/(s−1) + C_w + O(s−1)`, positivity gives `C_w − β_w ≤ λ₁`.
  - A pole-free perturbation must have `D_w(1) ≤ 0.0231`.
- **Sharpness of the E-free method [P].** A positive measure `ν` compactly supported in `Re s > ½` that annihilates every `n^{−s}/ζ(s)`, `n ≥ 2`, is a multiple of `δ₁`.
  - Reason: `λ := ν/ζ` off `s = 1` has Laplace transform `∫e^{−zs}dλ(s)` of finite exponential type vanishing at every `log n`. That zero density (`e^x`) exceeds any finite type, so the transform vanishes and `ν` is carried by `{1}`.
  - Hence `λ₁/(1+γ)` is the optimal ε-squeeze obtainable from interior positivity without using the structure of `E`.
- **Carathéodory form (structural) [P].** In the Cayley coordinate `w = 1 − 1/s` (`s = 1 ↦ 0`), Weil positivity of `lam` ⟺ the Toeplitz matrices of the Taylor coefficients `c_k(lam)` of `Φ_lam(1/(1−w))` are PSD for every order (Carathéodory–Toeplitz). This is the generalized Li criterion for weight systems.
  - `c₀ = λ₁(lam)`, and `c_k` is linear in the generalized Stieltjes constants of `lam`.
  - For Λ the circle measure is concentrated near `w = 1` (zeros are high), so `T_k(ξ'/ξ)` is nearly rank one: `2c₀ − |c₁| = 3.7·10^{−5}`.
  - Consequence (tower): perturbations `E/ζ^k` vanishing to order `k` at `s = 1` are squeezed to `ε ≤ λ_min(T_k(ξ'/ξ))/‖T_k(G_∞)‖`. For `k = 2` this is `ε ≲ 10^{−5}`. (The `k ≥ 2` classes are already killed by the multiplicity/density argument; the tower illustrates the geometry only.)
  - For the Möbius class only `c₀` is E-free, since `E`'s Taylor data at 1 make every off-diagonal Toeplitz entry free. So finite-order Carathéodory conditions add nothing beyond L101.2.
- **Phase 4 verdict.**
  - Mechanism: **REDISCOVERED/BRIDGE**. `λ₁ = Σ1/ρ` and its Weil-test realization are Li / Bombieri–Lagarias.
  - Application: **SURVIVES**. The Mertens inequality for arbitrary completions, the ε-core squeeze and the sharpness statement are new in the second-completion framework (no hits for "second completion", "Weil cone", "ε-core" outside this programme).
  - Significance: modest. The ε-core becomes a tangent-cone problem at Λ (`ε ∈ (0, 0.0146]`), but it is not killed.
- **What remains of the ε-core.** For small ε every boundary (tangent) condition is ε-independent, `θ' − Re(E'/ζ) ≥ 0` with `E = εE'`, and the only ε-dependent condition is the pole budget.
  - So the ε-core is exactly the tangent cone of W at Λ in the Möbius directions `−Λ + e'⋆μ`, and killing it needs the realness count (zero statistics, L82/L89) or the off-line interpolation. The L86 barrier stands for `ε ≤ 0.0146`.
- **Lean plan (when Lean is available).**
  - Generalize `weilPositive_farPolar_inequality` from the corpus Fejér test to an arbitrary compactly supported `ψ`.
  - Compute the exponential window `g_X` in closed form.
  - Mertens with constant `−γ` for Λ (check PNTPlus) and `Σμ(n)/n → 0`.
  - `G_∞(1)` via `ψ(½) = −γ − 2 log 2`.

### L102 — Phase locking: in the ε-core the critical zeros carry none of the Landau mass. IDENTITY [P] + reduction; not a kill
- **Reformulation of realness (phase locking).** At a simple critical zero `γ` (the `n`-th ordinate), `θ(γ) = π(n − 3/2) − πS(γ)`.
  - So the ε-core realness `X_E(γ) = Re(e^{iθ(γ)}E(½+iγ)) = 0` is equivalent to `arg E(½+iγ) ≡ πS(γ) (mod π)`. Equivalently, `G_E(ρ) := E(1−ρ) + χ(1−ρ)E(ρ) = 0`.
  - At multiple critical zeros `E(ρ) = 0`, so `G_E(ρ) = 0` too.
  - So every critical zero must sit on the modified Gram grid `θ(t) + arg E(½+it) ∈ π/2 + πℤ`.
  - Equivalently (symmetrization): `R_E(s) := (E/ζ)(s) + (E/ζ)(1−s)` has no pole on the critical line.
- **Identity L102.1 [P].** For every Dirichlet polynomial `W`, unconditionally:
  `Σ_{0<γ≤T} G_E(ρ)W(ρ) = N(T)·⟨E,W⟩ + O_{E,W}(T)`, where `⟨E,W⟩ = Σ_n e(n)w(n)/n`.
  - Proof: the `E(1−ρ)W(ρ)` part is the Landau–Gonek sum `Σ_ρ (n/m)^ρ`, which is `N(T)` for `n = m` and `O(T)` otherwise.
  - The `χ(1−ρ)E(ρ)W(ρ)` part is the twisted `κ = 1` case of Arias de Reyna, *On the distribution (mod 1) of the normalized zeros* (JNT 2015; arXiv:1403.7126, Thm 3.1). By Gonek's stationary-phase lemma, `Σ_ρ χ(1−ρ)y^ρ = −Σ_{n ≤ yT/2π}Λ(n)(…)e(−n/y) + O(T^{½}log²T) = O_y(T)`, unconditionally.
  - The twist `y` changes only the stationary point. To check line by line before any formal use.
- **Consequence L102.2 (ε-core) [P].** Phase locking kills every critical term, so
  `Σ_{off-line ρ, γ≤T} G_E(ρ)W(ρ) = N(T)⟨E,W⟩ + O(T)` for all `W`: **the off-line zeros must carry the entire Landau main term.**
  - With `W = E`, `G_E(ρ) = χ(1−ρ)G̃_E(ρ)` and `|G̃_E| ≤ 2M_E N_e^{|β−½|}` (`M_E = Σ|e(n)|n^{−½}`), this gives `Σ_{off-line} (1 + (γ/2π)^{|β−½|})·N_e^{2|β−½|} ≥ (‖E‖²/(2M_E²))·N(T)(1 − o(1))`.
  - So the ε-core forces a χ-weighted *positive proportion* of off-line zeros (order `T log T`). L82's deficit law forced only order `T` defective zeros, and multiple critical zeros counted there. They contribute nothing here.
- **The kill threshold drops, but not below current knowledge.**
  - Before: all but `o(T)` zeros critical and simple (L82/L89).
  - Now: the ε-core is killed as soon as `Σ_{off-line, γ≤T}(γ/2π)^{|β−½|} = o(N(T))`, i.e. 100% of zeros critical in the χ-weighted sense. Multiplicity no longer matters.
  - With *ordinate* sums in place of analytic sums, the bounded weights would give, via `W ≈ E/(|E|²+η)`, the threshold "more than 50% of zeros critical". That would sit only 8.3% above Pratt–Robles–Zaharescu–Zeindler's 41.7%.
  - But the ordinate `κ = 1` equidistribution with twists is Odlyzko's Gram-equidistribution problem, open even under RH (Arias de Reyna). The analytic version carries the weight `(γ/2π)^{β−½}`, and Conrey-type density `N(σ,T) ≪ T^{1−(8/7)(σ−½)}log T` bounds its total only by `O(N)` with a constant, not `o(N)`.
- **Phase 4 verdict.**
  - As a kill: **FAILS**, blocked by the χ-weight of off-line zeros, which is exactly the Odlyzko/Arias de Reyna obstruction.
  - As a structural identity: **SURVIVES** and is new in this framework. Realness of the second-completion residues is a Gram-phase locking of the critical zeros, and it forces the off-line zeros to reproduce the Landau diagonal `N⟨E,W⟩` for every `W`.
  - Positive survivor: the ε-core threshold is now "100% critical (χ-weighted)" rather than "all but `o(T)` critical and simple". A proof that more than 50% of zeros are critical, combined with an ordinate version of the twisted `κ = 1` law, would kill all Möbius-type second completions.

### L103 — The ε-core is empty: a ζ′-weighted discrete moment over the zeros kills every Möbius-type second completion. THEOREM [P]
- **Conjecture (from L101/L102).** In the ε-core the off-line zeros are degenerate: at a simple right off-line zero `ρ`, the interpolation `E(ρ) = (1−ε)ζ'(ρ)` forces `|ζ'(ρ)| ≤ K := M_E/(1−ε)`, with `M_E = Σ|e(n)|n^{−½}`. Typical zeros have `|ζ'(ρ)| ≍ log T`.
  - A discrete moment weighted by `ζ'(ρ)` (main term of order `T log² T`) should therefore see the whole zero set with one more power of log than the degenerate off-line zeros can supply. L102's unweighted sum had main term of order `N(T)`, the same order as the off-line count.
- **Theorem L103.** Let `e` be real and finitely supported with `e(1) = 0` and `e ≠ 0`, and let `c ∈ ℝ`. Then `cΛ + e⋆μ` is not Weil-positive.
  - With L52 (scaling) and L77 (`c ≤ 0`), the whole two-parameter family `{cΛ + e⋆μ}` meets the Weil cone at most in Λ. The case `c = 1 − ε`, `0 < ε < 1`, is the ε-core, declared a barrier in L83–L86; `c = 1` is L82.
- **Proof.** Write `E(s) = Σ e(n)n^{−s}`, `G_E(s) = E(1−s) + χ(1−s)E(s)`, `N_e = max supp e`.
  1. *Constraints from positivity* (L82 step 1 and L83(iii)–(iv); `c = 1−ε`, `ε < 1`).
     - At every simple critical zero, `G_E(ρ) = 0` (realness of the residue `E(ρ)/ζ'(ρ)`).
     - At every simple zero with `β > ½`, `E(ρ) = (1−ε)ζ'(ρ)`, because `Φ_lam` has no interior pole.
     - Hence `|ζ'(ρ)| ≤ K` at simple right off-line zeros, and `|ζ'(1−ρ)| = |χ(1−ρ)||ζ'(ρ)| ≤ (γ/2π)^{β−½}K`.
  2. *The identity.* Since `χ(1−ρ)ζ'(ρ) = −ζ'(1−ρ)` at zeros, `ζ'(ρ)G_E(ρ) = ζ'(ρ)E(1−ρ) − ζ'(1−ρ)E(ρ)`. For a Dirichlet polynomial `W`, set
     `𝒮(T) := Σ_{0<γ≤T} ζ'(ρ)G_E(ρ)W(ρ) = 𝒮₁ − 𝒮₂`, where `𝒮₁ = Σ ζ'(ρ)E(1−ρ)W(ρ)` and `𝒮₂ = Σ ζ'(1−ρ)E(ρ)W(ρ)`.
  3. *Main terms (unconditional discrete moments).* For `X(s) = Σ_r x_r r^{−s}`, finitely many positive rational frequencies:
     - Rule A: `Σ_{0<γ≤T} ζ'(ρ)X(ρ) = (T/4π)log²(T/2π)·Σ_{q∈ℕ} x_{1/q} + O_X(T log T)`.
     - Rule B: `Σ_{0<γ≤T} ζ'(1−ρ)X(ρ) = (T/4π)log²(T/2π)·Σ_{n∈ℕ} x_n/n + O_X(T log T)`.
     - Proof of A: the rectangle contour for `(ζ'/ζ)ζ'X`. The right edge and the `χ'/χ` part are `O(T log T)`. On the left edge, `(ζ'/ζ)(1−s)·χ(s)[(χ'/χ)(s)ζ(1−s) − ζ'(1−s)]·X(s)` gives, by stationary phase (`(1/2πi)∫χ(s)y^s ds ≈ y e^{2πiy}`, `y ≤ T/2π`), the sum `Σ_{j,m}Λ(j)r^{−1}log(j/r)e^{2πijm/r}`. This is coherent exactly when `r = 1/q`, and then it equals `(T/4π)[log²(T/2π) − log²q]`. Other frequencies cancel to `O(T log T)`.
       - Check: for `X ≡ 1` this is Fujii's `Σζ'(ρ) = (T/4π)log²(T/2π) + …` (Shanks' conjecture). The heuristic "`ζ'(ρ) ≈ ½log T·Σ n^{−ρ}` under the Landau pairing" reproduces both rules.
     - Rule B follows from A by the zero symmetry `ρ ↦ 1−ρ̄`.
     - `𝒮₁` has `X = E(1−s)W(s)`, with frequency `1/q` iff `n = qm`. `𝒮₂` has `X = EW`. So
       `𝒮(T) = (T/4π)log²(T/2π)·B(E,W) + O(T log T)`, where `B(E,W) = Σ_m (w(m)/m)[Σ_q e(qm)/q − E(1)]`.
     - Cross-check under RH: `ζ'(ρ)G_E(ρ) = −2iZ'(γ)X_E(γ)`. For `E = W = n₀^{−s}` the two chirp pieces give `(T/4π)log²T·(1/n₀ − 1/n₀²)`, which equals `B`.
  4. *B is nondegenerate.* Take `W = m₀^{−s}`, so `B = (1/m₀)[Σ_q e(qm₀)/q − E(1)]`.
     - For `m₀ > N_e` this is `−E(1)/m₀`.
     - If `E(1) = 0`, take `m₀ = N_e`: `B = e(N_e)/N_e ≠ 0`.
     - In general, `B(E,·) ≡ 0` forces `E(1) = 0` and `Σ_{m|k} e(k)/k = 0` for all `m`, hence `e = 0` by Möbius inversion.
  5. *The critical zeros contribute nothing.* Simple critical zeros have `G_E(ρ) = 0`; multiple zeros have `ζ'(ρ) = 0`. So `𝒮(T) = Σ_{simple off-line} ζ'(ρ)G_E(ρ)W(ρ)`.
  6. *The off-line zeros contribute `O(T log T)`.* With `δ = |β−½|`:
     - a right zero gives `|ζ'G_E W| ≤ K·M_E(N_e^δ + (γ/2π)^δ)·m₀^{−½}`;
     - its left partner gives `≤ (γ/2π)^δ K·M_E(1 + N_e^δ)·m₀^{−½+δ}`;
     - so each term is `≤ C·T^{(1+η)δ}` for `T ≥ T₀(η)`.
     - A density estimate `N(σ,T) ≪ T^{1−A(σ−½)}log T` with some `A > 1+η` gives `Σ_{off-line} T^{(1+η)δ} ≤ e²N(T) + (1+η)log T·∫_{1/log T}^{½} T^{(1+η)u}N(½+u,T)du = O(T log T)`.
     - Such an `A` is known: Conrey 1989 (`8/7 − ε`), or any mollified mean square with length `T^θ`, `θ > ½`, by Selberg's method (`A = 2θ`); for example Bettin–Chandee–Radziwiłł, θ = ½ + 1/66.
  7. Comparing, `(T/4π)log²T·|B| ≤ O(T log T)`, which is false for large `T`. ∎
- **Why L86's barrier verdict was wrong.** The five ε-core constraints are local or averaged against fixed weights. They miss the unconditional *global* discrete moment `Σζ'(ρ)X(ρ)`, which weights each zero by `|ζ'(ρ)| ≍ log T`.
  - The interpolation constraint (iv) makes every off-line zero degenerate (`|ζ'| ≤ K`). The realness constraint (iii) kills every critical term. So the `log T` excess of the main term has nowhere to live.
  - CANNOT-479 (continuous twisted moments) stays true. The successful moment is *discrete*.
- **Inputs, and their status.**
  - (a) Realness at critical zeros: the tangent criterion, [P]; Lean for dilations (L80); the Möbius version is pending.
  - (b) No interior pole: Herglotz, L83 [P-sketch], equivalently Weil's classical off-line-zero detection applied to `D_lam`.
  - (c) Rules A/B: standard contour and stationary-phase computations (Fujii; Conrey–Ghosh–Gonek; the generalized Landau–Gonek formula for `Σχ(ρ)X^ρ` of arXiv:2601.18025). They are unconditional; the rational twists are my extension and should be checked against those sources line by line.
  - (d) Density with `A > 1`: literature (Conrey 1989 announced `8/7−ε`; BCR 2017 mollified mean square).
  - No zero statistic beyond (d) is used. Neither RH nor Alpöge–Furman is needed.
- **Scope and next.**
  - The method needs `E` to be an absolutely convergent Dirichlet series with `Σ|e(n)|n^{η} < ∞`, for the bound at far-off zeros and for the moment asymptotics. So all rapidly convergent Möbius-type perturbations are covered.
  - Open: mixtures `lam = cΛ + Λ⋆b + f⋆μ` (a degree-1 part as well).
    - Realness becomes `K(ρ) := [B(ρ)−B(1−ρ)]ζ'(ρ)ζ'(1−ρ) − [F(ρ)ζ'(1−ρ) − F(1−ρ)ζ'(ρ)] = 0` at critical zeros. Its discrete moment has main term `≍ T log⁴T·C(B,W)`.
    - The off-line terms stay bounded wherever `|c + B(ρ)| ≥ η`, since there `ζ'(ρ) = F(ρ)/(c+B(ρ))`.
    - The remaining case is off-line zeros near the zero set of `c + B`, of `O(T)` size per strip. That is the next conjecture (L104).
  - Lean: (a) with the L82 link; (c) and (d) are deep analytic inputs and would enter as named hypotheses. This theorem is a paper theorem with named literature inputs, not a Lean target yet.

### L104 — Finite-type uniqueness: every Weil-positive `Λ⋆a + f⋆μ + v` equals Λ. THEOREM [P]
- **Setting.** Let `a` and `f` be real and finitely supported, with `f(1) = 0`. Let `v` be a regular perturbation (the L78 class: `D_v` analytic across the line, no poles at zeros). Put `lam = Λ⋆a + f⋆μ + v`, `A(s) = Σa(m)m^{−s}`, `Ã(s) := A(1−s)`, `F(s) = Σf(n)n^{−s}`, `F̃(s) = F(1−s)`. Then `D_lam = −Aζ'/ζ + F/ζ + D_v`.
- **Theorem L104.** If `lam` is Weil-positive, then `a = δ₁`, `f = 0` and `v = 0`.
  - Hence every finite-type second completion is excluded, *unconditionally*. Within finite type, `W ≠ ∅ ⇔ Λ ∈ W ⇔ RH`.
- **Constraints.** `D_v` has no poles at zeros, so all three constraints are independent of `v`.
  - (i) Simple critical zero: the residue `−A(ρ) + F(ρ)/ζ'(ρ)` is real. Using `conj A(ρ) = Ã(ρ)` and `conj(F/ζ')(ρ) = −χ(ρ)F̃(ρ)/ζ'(ρ)` on the line, this is equivalent to
    `J(ρ) := ζ'(ρ)[A(ρ) − Ã(ρ)] − F(ρ) − χ(ρ)F̃(ρ) = 0`.
  - (ii) Multiple critical zero: no poles of order ≥ 2 on the boundary of a Herglotz function, so `F(ρ) = 0`. Hence `J(ρ) = −F(ρ) − χ(ρ)conj F(ρ) = 0` too.
  - (iii) Simple zero with `β > ½`: no interior pole, so `F(ρ) = A(ρ)ζ'(ρ)`. At multiple interior zeros `F(ρ) = 0 = ζ'(ρ)`.
- **Step 1: the twisted J-moment kills the dilation part.** Take `V := A·Ã·W₀`, with `W₀` a finite exponential polynomial with positive rational frequencies.
  - *Critical zeros* contribute 0, by (i) and (ii).
  - *Right off-line zero.* By (iii), `J(ρ)V(ρ) = −F(ρ)Ã(ρ)²W₀(ρ) − χ(ρ)F̃AÃW₀(ρ)`. The factor `A(ρ)` in `V` converts `ζ'(ρ)A(ρ)` into `F(ρ)`. This is bounded by `C N^{O(δ)}`, since `|χ(ρ)| ≤ 1` there.
  - *Left partner `ρ' = 1−ρ̄`.* `J(ρ')V(ρ') = conj[−χ(1−ρ)F(ρ)Ã(ρ)² − F̃ÃA(ρ)]·W₀(ρ')`, which is `≤ C(γ/2π)^{(1+η)δ}`.
  - Summing with a density estimate `A_dens > 1` (as in L103) gives `O(T log T)`. When `F ≡ 0`, the off-line terms vanish *identically*: (iii) gives `A(ρ) = 0`, and `V` carries the factor `A`.
  - *Main term.* `J·V = ζ'·P·W₀ − (F + χF̃)V`, with `P := (A − Ã)AÃ`.
    - Rule A (L103): `Σ_ρ ζ'(ρ)P(ρ)W₀(ρ) = (T/4π)log²(T/2π)·Σ_q [q^{s}-coefficient of PW₀] + O(T log T)`.
    - `Σ_ρ F(ρ)V(ρ)` is a Landau sum, `N(T)·const + O(T)`. `Σ_ρ χ(ρ)F̃V` is a twisted Arias de Reyna sum, `O(T)`.
  - *Nondegeneracy.* Let `r₀` be the smallest frequency in the support of `P = Σ_r p_r r^{−s}`, and take `W₀ = r₀^{s}`. Then the coefficient is `p_{r₀} ≠ 0` whenever `P ≢ 0`.
  - *Conclusion of Step 1.*
    - The contradiction `T log²T ≲ T log T` forces `P ≡ 0`.
    - The group ring `ℂ[ℚ_{>0}]` is a domain, so `A ≡ Ã` or `A ≡ 0`.
    - `A ≡ Ã` means `a(m)m^{−s} ≡ a(m)m^{−1}m^{s}`, which forces `A = c` constant.
    - `A ≡ 0` is handled by the same method with `V = F F̃ W₀` (right off-line `F(ρ) = 0` kills both partner terms; the main term is Rule A minus Rule B, nondegenerate by the top-frequency argument). The details are routine, but this case should be written out before formal use.
- **Step 2.** With `A = c ≠ 0`, L103 (whose constraints are unaffected by `v`) gives `f = 0`.
- **Step 3.** Now `lam = cΛ + v`. The L81 side result (`h₁ ≠ 1` impossible) and L78 (regular uniqueness) give `c = 1` and `v = 0`. ∎
- **Worked check (single dilation `lam = Λ + bΛ(n/2)`).**
  - `P = b(1 + b²/2)2^{−s} + b²4^{−s} − (b/2)(1 + b²/2)2^{s} − (b²/4)4^{s}`.
  - With `W₀ = 1` the coefficient is `−(b/2)(1 + b/2 + b²/2)`. This is nonzero for `b ≠ 0`, since `1 + b/2 + b²/2` has no real roots.
  - Positivity would force every critical ordinate into `(π/log 2)ℤ` (L80) and every off-line zero onto the zeros of `1 + b2^{−s}`. Then `Σ_ρ ζ'(ρ)(A−Ã)AÃ(ρ)` would vanish exactly, contradicting the Fujii-type asymptotic.
  - This holds even if the zeros were arbitrarily multiple, which is why counting alone needed Alpöge–Furman in L81. **This is an Alpöge–Furman-free, density-free proof of the dilation rigidity L81.**
- **What this means for the producer.**
  - The Minkowski split is now: *existence* = PBAP = W ≠ ∅; *uniqueness* holds on every finite-type class (L78, L81, L103, L104).
  - Any Weil-positive system that differs from Λ by a finite Dirichlet-polynomial singular part plus a regular part is Λ. So a finite-type producer of Weil positivity for ζ's archimedean datum exists iff RH holds, and then it is Λ.
  - If RH fails, every element of W (if any) must be of *infinite type*: `E_w = ζ·D_w` is not a bounded Dirichlet series near the off-line zeros.
  - Equivalently, the producer question is now exactly: *does Λ's own explicit formula carry positivity* (RH), or can some wild, infinite-type system do so while RH fails?
- **Open core (uniqueness).** Infinite-type perturbations: `E_w` with `Σ|e(n)|n^{η} = ∞`, or with no continuation across the line. The method needs `|E_w|` bounded at off-line zeros and a main-term asymptotic for `Σζ'(ρ)E_w(…)`.
- **Inputs.**
  - Rule A: Fujii/Gonek discrete moment with rational twists, derived in L103 and checked against the AFE heuristic.
  - Density `N(σ,T) ≪ T^{1−A(σ−½)}log T` with `A > 1`: Conrey 1989; BCR 2017 via Selberg. Needed only when `F ≢ 0`.
  - Tangent-criterion realness and Herglotz interior analyticity: L80/L83.
  - L78, L81 side result, L52.

### L105 — Producer identification: for finite type the functional equation is the only producer; the remaining existence/uniqueness core is a crystalline-weight problem on the zeros. THEOREM (reformulation of L104) [P] + CONJECTURE
- **Producer identification theorem [P, from L104].** PC-82 holds on the finite-type class. Let `lam = Λ⋆a + f⋆μ + v` (finite `a` and `f`, regular `v`) be Weil-positive. Then `lam = Λ`, so `Γℝζ_lam = Γℝζ` satisfies the Γℝ functional equation, and positivity is produced by the FE through the identity `Re(−ζ'/ζ)(½+it) = θ'(t)` together with real zeros.
  - No other finite-type mechanism (dilations, Möbius-type corrections, regular corrections, or any combination) produces Weil positivity for ζ's archimedean datum.
  - The existence problem restricted to finite type is therefore *exactly* RH.
- **Existence tests that fail for structural reasons.** Three existence-side attempts this cycle were each killed by an identifiable mechanism, recorded to avoid repetition.
  - (X1) *Curve producers.* Weil's theorem for `C/F_q` gives positive-definite atomic distributions `T_C = 2gδ₀ + Σ_k a_k(C)(δ_{k log q} + δ_{−k log q})`. Their atoms lie on `log ℕ` when `q` is a prime power.
    - But atoms on `log ℕ` are free parameters of `lam`, so modulo them `T_C ≡ 2gδ₀`. Any combination only *subtracts* `δ₀`-mass from the archimedean datum. **KILLED:** positive-definite pieces carried by atoms cannot produce positivity of the continuous kernel `c₀δ₀ − K(|u|)`.
  - (X2) *Aperture Gronwall.* RH ⟺ the ground energy `μ₀(A)` never reaches 0.
    - A Hadamard-type inequality `d log μ₀/dA ≥ −K(A)` would suffice, with `K(A) ≳ e^{2A}` (Landau–Widom).
    - At a genuine crossing (off-line pair first resolved), the boundary flux is finite and nonzero while `μ₀ → 0` linearly. So no structural Pohozaev bound `flux ≤ K·μ₀` can hold without RH. **CIRCULAR.**
  - (X3) *Discrete-moment producer for PBAP.* PBAP concerns fixed, absolutely convergent zero sums `Σ_ρ Φ̂(γ_ρ)`; discrete moments give asymptotics of *growing* sums. **NO LEVERAGE.** The L103 mechanism needs algebraic relations at zeros that grow with `T`.
- **Reformulation of the infinite-type core (crystalline weights) [P].** Let `lam ∈ W` and `w = lam − Λ`.
  - By Herglotz, `D_w = D_lam + ζ'/ζ` is meromorphic on `Re s > ½`, with:
    - interior poles exactly at off-line zeros, residue = multiplicity;
    - boundary poles at critical zeros, with real residues `r_ρ ≤ m_ρ` (the atom `m_ρ − r_ρ ≥ 0`);
    - `Re D_w ≤ 0` a.e. on the line, unconditionally, since `Re(−ζ'/ζ)(½+it) = θ'(t)` off zeros holds by the FE alone.
  - If every `r_ρ ≤ 0` (and RH holds), then `−D_w` is Herglotz with zero vertical means, hence `D_w ≡ 0`.
  - So uniqueness fails only through *partial zero removal*: weights `r_ρ ∈ (0, m_ρ]` such that `Σ_ρ r_ρ e^{iγ_ρ u}`, minus a negative-type Herglotz part, is a *crystalline* distribution whose singular support lies on `±log ℕ` (by Mellin inversion, the coefficients `w(n)` live on the integers).
  - The known crystalline weights are constants (killed by L52) and `r_ρ = E(ρ)/ζ'(ρ) + B(ρ)` with finite `E, B` (killed by L103/L104).
  - **Conjecture L106 (crystalline rigidity on the zeta zeros).** Every weight sequence `(r_ρ)` of polynomial growth whose weighted zero measure is crystalline in this sense is of the form `E(ρ)/ζ'(ρ) + B(ρ)·m_ρ`, with `E` and `B` Dirichlet series absolutely convergent on `σ ≥ ½ − η`.
    - L106 together with an infinite-`E` version of L104 gives full uniqueness, hence RH ⟺ PBAP unconditionally. PBAP is then a statement about Γℝ and `log ℕ` alone, and it would be the only form in which a producer can still be sought.
    - It is the analogue, for the pair (zeta zeros, `log ℕ`), of the Fourier-interpolation and crystalline-measure rigidity of Radchenko–Viazovska and Kurasov–Sarnak.
    - How it could fail: an "exotic" crystalline weight, e.g. from Dirichlet series with natural boundary on the line whose boundary values still have singular support on `log ℕ`.
- **Status.** Existence: RH-equivalent within finite type (theorem). Infinite type: L106 open, equivalent to the last uniqueness gap.
- **L105 self-audit (correction to L106).** Every crystalline weight is *automatically* of the form `r_ρ = E(ρ)/ζ'(ρ)` at simple zeros, with `E := ζ·D_w`. This is a Dirichlet series with coefficients `1⋆w`, analytic on `Re s > ½` once positivity holds. So L106 as stated is a regularity statement, not an algebraic one.
  - **Corrected conjecture L106′.** Weil positivity of `Λ + w`, with `w` in the box, forces `E = ζD_w` to satisfy what the L103/L104 machinery needs:
    - (a) `|E(ρ)| ≪ (log γ)^{O(1)}` at interior zeros, i.e. `|ζ'(ρ)|` polylogarithmic at off-line zeros, since `E(ρ) = ζ'(ρ)` there;
    - (b) a mean-value structure on the critical line strong enough for Rule A with `X = E·W`.
  - The obstruction is that the realness relation `G_E(ρ) = 0` uses `E(1−ρ)`, i.e. a continuation of `D_w` to the left of the line. Positivity supplies `D_w` only on `Re s ≥ ½`. An analytic encoding of realness using only right-half-plane data is the missing tool.

### L106 — Pole-free perturbations are rigid in full generality: Step 3 of L104 needs no regularity class. THEOREM [P]
- **Theorem L106.** Let `v` be any real weight system in the box whose Dirichlet series `D_v` has no pole at any zero of ζ in `Re s ≥ ½` (for example Selberg-type `v = k⋆log`, `D_v = −Kζ'`, which lies outside the L78 class). If `Λ + v` is Weil-positive, then `v = 0`.
  - Combined with L104 Steps 1–2: `Λ⋆a + f⋆μ + v` (finite `a`, `f`; arbitrary pole-free `v`) is Weil-positive only if it equals Λ.
- **Proof.**
  1. `D_{Λ+v} = −ζ'/ζ + D_v` must be analytic in `Re s > ½` (Herglotz). `D_v` has no poles at zeros, so ζ has no off-line zeros. **RH follows from positivity here.**
  2. Under RH, `D_v` is analytic on `Re s > ½`, with polynomial growth: `D_v = D_lam + ζ'/ζ`, where `D_lam` is controlled by the Herglotz function and `ζ'/ζ ≪ log²|t|/(σ−½)`.
  3. On the line, the Weil measure of `Λ + v` is `μ_Λ − Re D_v`, with no atoms from `D_v`. Its a.c. part `−Re D_v` is `≥ 0`. So `−D_v` is Herglotz: `Re(−D_v) = a(σ−½) + Poisson(ν)`, with `ν ≥ 0`.
  4. For `σ > 1` (absolute convergence at `σ > 3/2`, then analytic continuation of the mean), `D_v` has vertical mean 0 (no constant term). So `a(σ−½) + mean(ν) = 0`, whence `a = 0`, `ν = 0`, and `D_v ≡ 0`. ∎
- **Consequence.** The uniqueness core is now *only* singular parts of infinite type: perturbations whose Dirichlet series has poles at zeros of ζ with residues `r_ρ = E(ρ)/ζ'(ρ)`, where `E = ζ·D_w` is not a finite (or rapidly convergent) Dirichlet series. Everything pole-free and everything finite-type is rigid.
  - Among pole-free perturbations, positivity *alone* implies RH (step 1). So the classical Weil criterion is recovered as the special case `v = 0`, and every pole-free completion reduces to it.

### L107 — Spectral mass conversion law: a producer converts every off-line pair into 2π of continuous spectrum. THEOREM [P]
- **Setting.** Take any `lam ∈ W`, `w = lam − Λ`. By the FE, `Re(−ζ'/ζ)(½+it) = θ'(t)` off zeros, unconditionally. So the Weil measure is `μ_lam = Σ_{crit} π(m_ρ − r_ρ)δ_γ + ν_ac`, with `ν_ac = −Re D_w(½+·)_{a.c.} ≥ 0`, where `r_ρ` is the residue of `D_w` at the critical zero `ρ`.
- **Theorem L107.**
  `ν_ac([0,T]) = π·(2N_off⁺(T) + Σ_{crit, 0<γ≤T} r_ρ) + O(log T)`,
  where `N_off⁺(T)` counts zeros with `β > ½`, `0 < γ ≤ T`.
  - With the atoms this gives total spectral mass `πN(T)`, which is Riemann–von Mangoldt for `lam`.
- **Proof.** Set `Ψ := −D_w + Σ_{β>½}[1/(s−ρ) + 1/(s−ρ*)] + Σ_{crit} r_ρ/(s−ρ)`, with `ρ* = 1−ρ̄` and the usual convergence normalization.
  - The off-line pair terms cancel the interior poles of `−D_w`, which have residue `−1`, and have zero real part on the line.
  - The critical terms cancel the boundary atoms.
  - So `Ψ` is analytic on `Re s > ½` with boundary real part `ν_ac ≥ 0`: it is Herglotz, `Ψ = a(s−½) + ib + Poisson(ν_ac)`.
  - Take vertical means over `[0,T]` at fixed `σ > 1`. `D_w` has mean 0 (no constant term). Each pair term is a pair of Poisson kernels of mass π each, giving `2π/T`. Each critical term gives `πr_ρ/T`. The Poisson part gives `ν_ac([0,T])/T`, and `a = 0` by varying σ. Edge effects are `O(log T)`. ∎
- **Corollaries.**
  - (i) **Conservation.** If RH fails, every Weil-positive system with nonnegative critical residues carries continuous spectrum of mass at least `2πN_off⁺(T)`. Off-line zeros cannot be hidden by a completion; they reappear as a.c. spectrum.
  - (ii) **RH ⟺ there is a Weil-positive system with purely singular Weil measure and nonnegative critical residues.** (⇒: Λ. ⇐: `ν_ac = 0` forces `2N_off⁺ + Σr_ρ = O(log T)` with `r_ρ ≥ 0`, hence `N_off⁺ = 0`.)
    - This is the producer conjecture PC-82 in its sharp form. The *producer* of positivity is FE-plus-discrete-spectrum; RH is exactly the statement that positivity can be produced with pure point spectrum.
  - (iii) With L106: a pole-free `v` has `r ≡ 0` and, by positivity, `N_off⁺ = 0`. So `ν_ac` has zero mean mass, `ν_ac = 0`, `D_v = 0`. This is a second proof of L106.
- **Pole-free producers (E-107), partial [P-sketch].** A system with `D_lam` analytic on `Re s > ½` (full zero removal) has a purely a.c. Weil measure, and its positivity is ζ-independent.
  - For such `lam`, the Perron truncation `Σ_{n≤x} lam(n) n^{−s} − βx^{1−s}/(1−s)` approximates `D_lam(σ₀+it)` to within `e^{−A}·polylog T` at `σ₀ = ½ + O(loglog T/log T)`.
  - This works because the spectral integral over a *tame* a.c. measure is harmless. For Λ the atoms at zeros spoil it.
  - If `lam ≥ 0` on a multiplicatively rich set (e.g. `lam(n) ≥ c₀ > 0` on smooth numbers), the resonance method (nonnegative Fejér weights, so all off-diagonal terms are ≥ 0) gives `max Re D_lam ≥ exp(c√(log T/loglog T))`. This contradicts the Herglotz bound `Re D_lam ≤ ½log t + O(1)`, valid on all of `Re s > ½` for every `lam ∈ W`.
  - So such pole-free producers do not exist. Prime-supported pole-free systems (Λ-like, where resonance gains only `√(log T/loglog T)`) are *not* excluded. That is the precise remaining form of E-107.

### L108 — Prime-supported pole-free producers: construction attempt (gap weights) and the fluctuation obstruction. CONSTRUCTION [P] + KILL [heuristic] + precise gap
- **Goal (existence).** An unconditional producer: a weight system with `D_lam` analytic on `Re s > ½` except a simple pole at 1. It must avoid the resonance kill of L107 (so no nonnegative mass on multiplicatively rich sets). If it existed it would prove PBAP, and W ≠ ∅, unconditionally. By L107 it would carry purely continuous spectrum of mass `πN(T)`.
- **Construction (the natural candidate) [P].** Take gap weights on primes, `lam(p) := β·(p⁺ − p)`, with `p⁺` the next prime. Then:
  - `ψ_lam(x) = βx + O(max gap) = βx + O(x^{0.525})` (Baker–Harman–Pintz);
  - `D_lam(s) = β/(s−1) + β Σ_p ∫_p^{p⁺}(p^{−s} − x^{−s})dx`, and each correction term is `≪ |s|·gap_p²·p^{−σ−1}`;
  - with Heath-Brown's `Σ_{p≤x} gap_p² ≪ x^{23/18+ε}`, the correction converges absolutely for `σ > 5/18`.
  - **So `D_lam` is analytic on `Re s > 5/18` except for the pole at 1.** This is an unconditional, explicit, prime-supported, pole-free candidate. It is *ζ-independent*: its Herglotz function never sees a zero of ζ.
- **Why it fails (fluctuation obstruction) [heuristic].**
  - On the line the correction is `≈ β Σ_{p ≲ t log t} gap_p·p^{−½−it}`. Its mean square is `≈ β² Σ gap_p²/p ≈ β² log²t`, using `E gap² ≈ 2 log²p`.
  - So `Re D_lam(½+it)` fluctuates with standard deviation `≈ 0.7β log t`. Positivity needs `Re D_lam ≤ θ'(t) ≈ ½ log t` for *every* `t`.
  - A Gaussian-like fluctuation exceeds this for a positive proportion of `t` (≈ 24% at β = 1).
  - For *any* prime-supported pole-free `lam` with density β, Cauchy–Schwarz only gives std `≳ β log t/√(loglog t)`. But unless the boundary values are correlated like those of an FE-function, the fluctuations are of the same order as θ'.
  - **Structural reason.** For Λ the same prime sum fluctuates with std `≈ ½ log t`, and the explicit formula transfers the excess *exactly* into the atoms at the zeros (`Re(−ζ'/ζ) = θ'` a.c.). A pole-free system has no atoms to absorb it.
  - Hence the dichotomy: **positivity needs either an FE-type exact cancellation (atoms, discrete spectrum, L107(ii)) or a fluctuation-free prime sum, and prime sums are never fluctuation-free.**
- **Precise gap to a theorem (E-107′).** One needs a lower-tail CLT for `Re Σ_{n≤x} lam(n) n^{−σ₀−it}` with `σ₀ = ½ + C/log T`, at thresholds of *constant* standard-deviation size.
  - The truncation lemma makes the head `p ≤ T^{ε}` dominant, since the tail is damped by `e^{−Cε}`.
  - But the head's exact Gaussian moments reach only order `1/ε`, while its variance is `≈ ε²θ'²`. Certifying a tail event at `1/ε` standard deviations with `1/ε` moments fails by a square root.
  - This is the same obstruction as in extending Selberg's CLT to large deviations at the scale of the mean; Soundararajan-type large-deviation bounds for prime sums would close it.
- **Status.** Existence via a pole-free producer: **KILLED heuristically**, with an explicit missing large-deviation input. Existence via a discrete-spectrum producer = RH (L107(ii)). No third kind of producer exists (L104–L107).

### L109 — Third-moment positivity inequality: a CLT-free kill of high-density prime-supported pole-free producers. THEOREM [P, modulo diagonal mean values] + reduction of E-107′
- **Tool (exact, elementary).** For a nonnegative random variable `X`, Cauchy–Schwarz on `X^{1/2}·X^{3/2}` gives `(E X²)² ≤ E X · E X³`.
  - Apply it to `X(t) = Re Φ_lam(σ+it) ≥ 0` (positivity), with `t` uniform on `[T,2T]` and `σ = ½ + κ/log T`.
  - Write `X = U − Y`, where `U = Re G_∞ + βRe(1/s + 1/(s−1)) ≈ ½log T` is deterministic up to `O(1)` and `Y = Re D_lam(σ+it)`, with `E Y = 0`, `E Y² = V`, `E Y³ = S₃`.
  - Then `(U² + V)² ≤ U(U³ + 3UV − S₃)`, that is
    **`V ≤ U² − U·S₃/V`.**
- **Prime-supported systems.** If `D_lam` is (up to prime powers) a prime sum, the diagonal of the third moment is empty (`p₁p₂ = p₃` is impossible), so `S₃ = o(V^{3/2})`.
  - Then positivity forces `V ≤ U²(1 + o(1))`, i.e. `½Σ_p lam(p)² p^{−1−2κ/log T} ≤ ¼log²T·(1 + o(1))`.
  - With density β (`lam(p) ≈ β log p` on average, the variance-minimizing profile), the left side is `≥ β²log²T/(8κ²)`. Positivity fails for every `κ < β/√2`.
- **Where it is rigorous.** For a pole-free `lam` the truncation lemma (L107) gives `D_lam(σ+it) = Σ_n lam(n)n^{−s}e^{−n/x} + o(1)`.
  - The damping `n^{−κ/log T}` makes the mean-square share of `n > T^c` equal to `(1 + 2κc)e^{−2κc}`.
  - Montgomery–Vaughan diagonal mean values for `V`, and the empty diagonal for `S₃` (products below `T`, `c = ⅓`), are valid once `κ ≥ κ₀`, an absolute constant (about 6 to 9 by the tail factor).
  - So **every prime-supported pole-free system with density `β > √2·κ₀` is not Weil-positive.** This replaces the unavailable large-deviation CLT of L108 by a third-moment inequality. The gap to all β is the diagonal range `κ < κ₀`.
- **Contrast with Λ (consistency).** For Λ at `σ = ½ + κ/log T` the same inequality would fail for `κ < 1/√2`. But there the mean square is not diagonal: the poles at the zeros give `E|ζ'/ζ|² ≈ log²T/(2κ)`, not `log²T/(8κ²)`. The spikes make `X` non-Gaussian and satisfy the inequality.
  - **This is the quantitative form of the dichotomy:** positivity near the line requires the variance of the prime sum to be carried by spikes (atoms/zeros), which is L107(ii).
- **Application to the gap-weight candidate (L108).** Interior positivity at `s = ½` and at `s = 1` forces large density. `Φ(½) = −2.686 + β(2 − K(½)) ≥ 0` and `Φ(1) = −1.554 + β(1 − K(1)) ≥ 0`, with `K(s) = Σ_p ∫_p^{p⁺}(p^{−s} − x^{−s})dx > 0`. Rough hand estimates give `K(½) ≈ 1.7` and `K(1) ≈ 0.69`, hence `β ≳ 9` and `β ≳ 5`.
  - A certified value of `K(½)` (an enclosure, not a numerical experiment) together with an explicit `κ₀` would decide whether the gap weights are killed rigorously by L109. **Status: KILL pending two explicit constants.**
- **Existence verdict.** Unconditional producers of pole-free type are killed for high density (L109) and nonnegative-rich support (L107). The low-density prime-supported case needs diagonal mean values closer to the line, which is the same frontier as the mollified moments of the corpus (the Conrey θ = 4/7 barrier). The only producer that survives every test is Λ, which is RH.

### L110 — Reflection-free encoding of realness (the F² device) and the one-sided contour identity for infinite-type uniqueness. TOOL [P] + reduction
- **Problem (from L105/L106′).** For an infinite-type second completion `lam = Λ + w`, `E := ζ·D_w` is defined only on `Re s ≥ ½`. L103/L104 encoded realness through `G_E(ρ) = E(1−ρ) + χ(1−ρ)E(ρ)`, which needs `E` to the left of the line.
- **Device.** At a critical zero, `conj ζ'(ρ) = −χ(1−ρ)ζ'(ρ)` (FE differentiated at a zero, `|χ| = 1` on the line). So realness of `E(ρ)/ζ'(ρ)` is equivalent to
  **`F(ρ) ∈ ℝ`, with `F(s) := χ(1−s)ζ'(s)E(s)`,**
  and `F` is analytic on `Re s > ½` using right-half-plane data only.
  - Consequently `F(ρ)² ≥ 0` at every critical zero: *positivity at the zeros without reflection*.
  - At right off-line zeros, interpolation gives `F(ρ) = χ(1−ρ)ζ'(ρ)²`.
- **One-sided contour identity.** Let the rectangle have left edge *on* the critical line, indented at critical zeros. For any Dirichlet polynomial `W`,
  `Σ_{β>½} F(ρ)²W(ρ) + ½Σ_{crit} F(ρ)²W(ρ) = (1/2πi)∫_{c−iT}^{c+iT}(ζ'/ζ)F²W ds − (1/2πi)PV∫_{½−iT}^{½+iT}(ζ'/ζ)F²W ds + O(horizontal)`.
  - The right edge is a χ²-twisted Dirichlet integral, computable by Gonek's lemma once `E` converges absolutely at `σ = c`.
  - On the line, `ζ'/ζ = −θ' − iZ'/Z` and `F(½+it) = −ie^{iθ}Z'(t)E(½+it)` (up to `|χ| = 1`), so the line integral involves only boundary values of `E`.
- **Reduction.** Infinite-type uniqueness follows if, for some `W ≥ 0`-type family, one can show:
  - (a) the right-edge main term is *negative* of order `T log^k T`;
  - (b) the line integral is `o(T log^k T)`;
  - (c) the off-line contributions `χ(1−ρ)²ζ'(ρ)⁴W(ρ)` are controlled.
  - Then `½Σ_crit F² ≥ 0` gives the contradiction.
  - (c) is where the difficulty concentrates. In the finite-type case `|ζ'(ρ)|` was bounded at off-line zeros; in general it is not, because `F(ρ) = χ(1−ρ)ζ'(ρ)²` carries no information.
  - (b) requires mean values of `E` on the line. They follow from the tangent criterion `Re(E·conj ζ) ≤ 0` only in averaged (Herglotz) form.
- **Status.** The F² device removes the reflection obstruction identified in L106′. The remaining obstruction is (c): off-line zeros of an infinite-type completion are *not* forced to be degenerate. This is the same place where RH itself sits, so no further reduction is expected from this device alone.

### L111 — Pair-correlation blindness: Montgomery-range statistics cannot distinguish Λ from a continuous-spectrum completion; atomicity lives beyond α = 1. OBSERVATION [P] + CONJECTURE
- **Setting.** `lam = Λ + w ∈ W` with Weil measure `μ_lam = Σ_crit π(m_ρ − r_ρ)δ_γ + ν_ac` (L107). The form factor is `F_lam(α) = (T log T/2π)^{−1}Σ∬ T^{iα(t−t')}w(t−t')dμ_lam dμ_lam`.
  - Being the Fourier transform of the (positive) self-correlation of `μ_lam`, it is positive-definite.
- **Blindness [P, Montgomery's method].** For `|α| < 1`, `F_lam(α)` is determined by the prime side: the diagonal `Σ lam(n)²/n` at scale `T^{α}`, plus the polar term `T^{−2|α|}log T`.
  - If `w` is prime-side small at these scales (`Σ_{n≤T^{α}} (2Λ(n)w(n) + w(n)²)/n = o(log²T)`), then `F_lam(α) = F_Λ(α) = |α| + T^{−2|α|}log T + o(1)` on `|α| < 1`.
  - So *no* statistic in the Montgomery range separates a pure-point producer (Λ under RH) from a completion that has converted off-line zeros into continuous spectrum.
- **Where atomicity is visible.** By Wiener's lemma, `lim_{A→∞}(1/A)∫_0^A F_lam(α)dα` measures the atomic part: `≍ Σ_ρ(m_ρ − r_ρ)²/N(T)` after normalization, with `ν_ac` contributing 0.
  - Hence **L107(ii) in form-factor language: RH ⟺ some Weil-positive system has form factor with full atomic mean beyond α = 1.** Montgomery's conjecture `F_Λ(α) = 1` for `α ≥ 1` is precisely the statement that Λ's atomic mean is maximal.
- **Consequence for the producer.** Any producer that proves RH must control correlations at scales `α ≥ 1`, i.e. beyond the reach of the prime diagonal. That is Montgomery's pair-correlation frontier. No argument confined to `α < 1` (mean values of Dirichlet polynomials of length `< T`) can produce the required atomicity.
  - This explains *structurally* why every mean-value attempt in L85/L90/L103–L109 stops at the same wall. It is the Montgomery–Vaughan length barrier `n ≤ T`, which corresponds to `α < 1`.
- **Conjecture L112 (atomicity from positivity).** If `lam ∈ W` and `F_lam(α) = |α| + T^{−2|α|}log T + o(1)` on `|α| < 1`, then `ν_ac = 0`. Equivalently: positivity plus Λ's Montgomery-range statistics forces pure point spectrum.
  - True under RH (Λ). Its proof would give "W ≠ ∅ ⇒ RH" for every prime-side-small completion.
  - The obstruction is that a positive a.c. measure with smooth density has form factor supported near `α = 0`. A Weil-positive `ν_ac` would have to reproduce the linear `|α|` ramp on `(0,1)` with *continuous* spectrum. Whether a positive a.c. measure with `~ (log t)/2π` density can have form factor `|α|` on `(0,1)` is a concrete harmonic-analysis question (a "continuous GUE" at the level of 2-point statistics).
- **L112 self-audit.** As a statement about positive measures alone, L112 is false. Smoothing the zeros, e.g. `Re ξ'/ξ(½+ε+it)`, gives a positive a.c. measure with Λ's Montgomery-range statistics.
  - But its Fourier transform is `arch·e^{−ε|u|} + Σ Λ(n)n^{−ε−½}δ_{±log n}`. That is a *shifted archimedean datum* `G_∞(s+ε)` with weights `Λ(n)n^{−ε}`, not ζ's datum.
  - **Corrected content.** The *exact* archimedean datum is what forbids continuous spectrum. The shifted family gives the ladder: `Λ(n)n^{−ε}` is Weil-positive for `G_∞(s+ε)` ⟺ no zero has `β > ½ + ε`.
  - For `ε ≥ ½` this holds unconditionally (all `β < 1`). That is an unconditional producer for the shifted datum, and RH is its `ε → 0` limit. (Classical in substance: `Re ξ'/ξ > 0` to the right of all zeros.)
  - L112 should therefore be read as: *exactness of the Γℝ datum plus positivity forces `ν_ac = 0`*. The shifted examples show that any proof must use the exact Γ-factor, not only Montgomery-range statistics.

### L113 — Datum-shift ladder: slack in the continuous spectrum cannot absorb interior poles; existence at shifted data is exactly a zero-free strip. THEOREM [P] (short)
- **Setting.** `W_ε := W(G_∞(·+ε))`, the Weil cone for the shifted archimedean datum on the same critical line.
  - Restriction to `Re s > ½ + ε` maps `W_0 → W_ε` via `lam ↦ lam·n^{−ε}`, so `W_0 ≠ ∅ ⇒ W_ε ≠ ∅` for every ε > 0.
  - Conversely, by the box compactness of L68, `W_ε ≠ ∅` for a sequence `ε → 0` with uniform bounds gives `W_0 ≠ ∅`.
- **Slack.** For `Λn^{−ε}`, `Re Φ(½+it) = Re ξ'/ξ(½+ε+it) + (datum terms)`.
  - Away from the zeros with `β > ½+ε`, this is `≥ c(ε) > 0`, since zero gaps are bounded by Riemann–von Mangoldt: the shifted system has *uniform slack* on the boundary.
  - The zeros with `β > ½ + ε` are interior poles of `Φ`. A boundary-slack argument cannot remove an interior pole, because the Herglotz property is violated in a neighbourhood of the pole whatever the boundary measure is.
  - Removing them requires a Dirichlet series `D_w` with poles exactly at those zeros, i.e. partial zero removal (L106′) in the shifted setting.
- **Theorem L113.** `Λn^{−ε} ∈ W_ε ⟺ ζ(s) ≠ 0 for Re s > ½ + ε`. Every finite-type element of `W_ε` equals `Λn^{−ε}`: the L104 proof transfers verbatim, with the critical line of `ζ(s+ε)` at `Re s = ½ − ε`, strictly inside the left half, so realness constraints become vacuous and only interpolation remains.
  - Hence **within finite type, `W_ε ≠ ∅` iff `ζ` has no zeros with `β > ½ + ε`.**
  - For `ε ≥ ½` this holds unconditionally (all `β < 1`). The producer ladder has rungs exactly at the zero-free strips, and RH is the rung `ε = 0`.
  - *Check of the transfer.* In the shifted setting there are no critical zeros on `Re s = ½` for `ζ(s+ε)`. The L104 moment argument uses only interior interpolation `F = Aζ'` at the zeros with `β > ½ + ε`. The main term must then be carried by those sparse zeros, of count `N(½+ε, T) = o(T)`, against a `T log²T` main term. This gives an **unconditional** exclusion of finite-type perturbations of `Λn^{−ε}` in `W_ε`, *provided* the Rule A main term for the shifted sums does not vanish. The ε-shifted analogue of Rule A has main term `(T/4π)log²T` times the coefficient at `s+ε`; still to be verified.
- **Meaning.** Existence at every positive slack of the datum is *equivalent* to a zero-free strip of the matching width, with no finite-type loophole. The producer question at `ε = 0` is RH with no residual freedom.
- **L113 self-audit (correction).** The "transfer verbatim" claim is **wrong**.
  - In `W_ε` the zeros of `ζ(s+ε)` corresponding to critical zeros of ζ lie strictly left of the line. So there are *no* realness constraints, and the boundary has uniform slack `c(ε)`. That slack is exactly what makes the critical terms vanish in L104; without them the moment argument has no vanishing set.
  - Correct picture:
    - (a) If ζ has no zeros with `β > ½ + ε`, then `Λn^{−ε}` lies in the *interior* of `W_ε` (slack `c(ε)`), and uniqueness fails at shifted data: every small finite-type perturbation is also a producer.
    - (b) If ζ has finitely many zeros with `β > ½+ε`, a finite-type perturbation can cancel those interior poles by interpolation (finitely many conditions, solvable by Dirichlet polynomials). If the perturbation is small, the slack absorbs it, so `W_ε ≠ ∅` even though the strip fails.
    - (c) With infinitely many such zeros (still `o(T)` by density theorems), finite type cannot interpolate them all.
  - **Corrected theorem.** `W_ε ∩ (finite type) ≠ ∅ ⟺` only finitely many zeros with `β > ½ + ε`, and the interpolating perturbation fits within the slack.
  - **Meaning.**
    - At positive datum slack, existence is governed by *finiteness* of far-right zeros, not by their absence.
    - At `ε = 0` there is no slack (no-slack law, L74/L79), and realness constraints on the line replace it. That is why `ε = 0` is rigid (L104) while every `ε > 0` is flexible.
    - **RH is the unique slack-free point of the ladder, and rigidity appears exactly there.**

### L114 — Beurling-algebra uniqueness: the L103/L104 kill extends from finite type to all singular data in `𝒲_η = {Σ c_n n^{−s} : Σ|c_n| n^{η} < ∞}`. THEOREM [P]
- **Statement.** Let `η > 0`. Suppose `A = Σ a(m)m^{−s}` (with `a(1) = c`) and `F = Σ f(n)n^{−s}` (with `f(1) = 0`) lie in `𝒲_η`, and `v` is pole-free at the zeros of ζ. If `lam = Λ⋆a + f⋆μ + v` is Weil-positive, then `a = δ₁`, `f = 0`, `v = 0`.
- **What changes from L104.**
  1. *Rules A/B for `X ∈ 𝒲`-type products.* Truncate `X = X_{≤N} + X_{>N}` with `N = T^{o(1)}`.
    - `X_{≤N}` obeys Rule A with error `O_N(T log T)`: the Gonek-lemma errors are `≪ Σ_{r≤N}|x_r| r^{O(1)} T^{½}log³T`.
    - For `X_{>N}`, the same contour computation, term by term, gives `≪ Σ_{r>N}|x_r|·T log²T = o(T log²T)`.
    - The positive-power frequencies `n^{s}/n` coming from `E(1−s)` are controlled on the right edge by `Σ|e(n)|n^{η}`.
    - The main-term coefficient `Σ_q x_{1/q}` converges absolutely.
  2. *Off-line bounds.* `|A(ρ)|`, `|Ã(ρ)|`, `|F(ρ)|`, `|F̃(ρ)| ≤ Σ|c_n| n^{|β−½|+…} ≤ C·(γ/2π)^{η'|β−½|}` once `T` is large. So the off-line terms stay `≤ C(γ/2π)^{(1+η')|β−½|}`, and the density input `A_dens > 1` still gives `O(T log T)`.
  3. *Nondegeneracy without a lowest frequency.*
    - Vanishing of the main-term functional for every `W₀ = x^{−s}`, `x ∈ ℚ_{>0}`, reads `Σ_q p_{1/(qx)} = 0` for all `x`.
    - Möbius inversion over `ℚ_{>0}` (absolutely convergent, since `P ∈ 𝒲`) gives `p ≡ 0`.
    - `P = (A−Ã)AÃ` is analytic on a vertical strip where all three factors converge, so `P ≡ 0` forces a factor to vanish identically (identity theorem).
    - `A ≡ Ã` means `Σa(m)m^{−s} ≡ Σ a(m)m^{−1}m^{s}`, and uniqueness of generalized Dirichlet coefficients gives `a(m) = 0` for `m ≥ 2`. `A ≡ 0` is handled as in L104.
  4. *L103 step.* `B(F,·) ≢ 0` for `f ≠ 0`, by Möbius inversion of `Σ_{m|k} f(k)/k` (absolutely summable). Step 3 (L106) is unchanged. ∎
- **Meaning.**
  - Uniqueness now covers every second completion whose "Möbius-Dirichlet data" `E = ζ·D_w` lie in a Beurling algebra, i.e. `1⋆w ∈ ℓ¹(n^{η})`. This is a genuine infinite-dimensional class.
  - **The remaining uniqueness core** is singular data outside every Beurling algebra: `Σ|(1⋆w)(n)|n^{η} = ∞` for all `η > 0`. These are perturbations whose zero-residue weights `r_ρ = E(ρ)/ζ'(ρ)` come from a Dirichlet series that does *not* converge absolutely on the far side of the critical strip.
  - Such an `E` is necessarily "ζ-like" in size (the ε-core type `E ≈ εζ'` is the model). So the open core is now: *second completions whose deviation from Λ is itself of zeta size.*
- **For the producer.** Within the Beurling class, "a producer exists" ⟺ Λ ∈ W ⟺ RH. A non-Λ producer must deviate from Λ by a zeta-sized amount.
  - By L107 it would carry continuous spectrum. By L109 its prime part fluctuates at the scale of θ'.

### L115 — Robust Weil criterion (dual of L104/L114), and the producer ladders unified. COROLLARY [P] + synthesis
- **Robust Weil criterion [P].** Let `𝒱` be a finite-dimensional space of weight perturbations spanned by dilation directions `Λ⋆δ_m` and Möbius directions `δ_n⋆μ` (finitely many `m, n`). Then
  **RH ⟺ `Q_Λ(Φ) ≥ 0` for every PD polar test `Φ` with `⟨v, Φ⟩ := Σ_n v(n)n^{−½}(Φ(log n) + Φ(−log n)) = 0` for all `v ∈ 𝒱`.**
  - *Proof.* (⇒) is Weil's criterion.
  - For (⇐), suppose RH fails. Then `Λ ∉ W`, and by L104 no other point of `Λ + 𝒱` lies in `W`, so `W ∩ (Λ + 𝒱) = ∅`.
  - `W` is closed and convex; at each level it is compact in the box (L68). `Λ + 𝒱` is a finite-dimensional affine space.
  - Hahn–Banach separation at a finite level, as in L79, gives a PD polar `Φ` with `Q_Λ(Φ) < 0` whose functional vanishes on the direction space `𝒱`. ∎
  - *Why it is not automatic.* Positivity of a quadratic form on a finite-codimension subspace does not imply positivity. If RH failed with finitely many off-line pairs, `Q_Λ` would have finitely many negative directions per level, and finitely many linear constraints could in principle annihilate them. L104 shows the *arithmetic* constraints of dilation or Möbius type never do.
  - By L114 the same holds for Beurling-class constraint families.
- **The producer ladders, unified (synthesis).** Four one-parameter families of unconditional producers are known, each with RH at the boundary value:
  - conductor slack `c` (L88: `c ≥ c_fin` with finite weights);
  - archimedean shift `ε` (L113: `Λn^{−ε}` for `G_∞(s+ε)`, unconditional at `ε ≥ ½`);
  - de Bruijn–Newman time `t` (`H_t` real-rooted for `t ≥ 0.2`, Polymath 15; `Λ_DN ≥ 0`, Rodgers–Tao);
  - derivative order `n` (high derivatives of Ξ real-rooted: Pólya–Wiman type results; Griffin–Ono–Rolen–Zagier for Jensen polynomials at large shift).
  - In each ladder the positive-parameter producers have *slack*, so the producer set has interior and uniqueness fails. At the boundary (`c = ε = t = 0`, or `n = 0`) the slack vanishes: the no-slack law (L74/L79), Newman's conjecture (Rodgers–Tao), and our results.
  - **For the Weil-cone ladder this programme proved that rigidity appears exactly at the boundary.** Finite-type (L104), pole-free (L106) and Beurling-class (L114) uniqueness hold at `ε = 0`, while every `ε > 0` is flexible (L113 correction).
  - So the boundary is both **rigid** (unique candidate Λ) and **slack-free** (no margin). A producer at the boundary must be an exact identity (L85) singling out Λ. The only known such identity is the functional equation, whose efficacy is RH.
- **Status of the producer question after L101–L115.**
  - Identified: the producer is ζ's FE acting through Λ. It is the only candidate among all Beurling-class completions.
  - Its efficacy: exactly RH.
  - Excluded or reduced: curve distributions, aperture Gronwall, discrete moments for PBAP, pole-free producers (high density; nonnegative-rich), gap weights (pending constants), Montgomery-range arguments (L111 blindness).
  - Open cores:
    - (i) zeta-sized second completions (outside every Beurling algebra);
    - (ii) low-density prime-supported pole-free systems;
    - (iii) RH itself.

### L116 — Candidate exact producers at the slack-free boundary: ferromagnetic (Lee–Yang) positivity through the Jacobi triple product. CANDIDATE + literature audit
- **Why this class.** L115 showed the producer at `ε = 0` must be an *exact identity* singling out Λ, with no slack. The literature has one mechanism that produces zeros on a line *exactly and without slack*, for families at criticality: the **Lee–Yang theorem** (ferromagnetic Ising partition functions have zeros on the unit circle at every coupling, including critical ones).
- **Dictionary.**
  - RH ⟺ Riemann's measure `Φ(u)du` has the Lee–Yang property: `∫Φ(u)e^{zu}du = ξ(½+z)` vanishes only on `Re z = 0`.
  - Lee–Yang producers are laws of magnetizations of ferromagnetic systems. Newman ("Fourier transforms with only real zeros", PAMS 1976) and Newman–Wu (CMP 2019) develop the single-spin classes.
  - The theta function behind Φ has the Jacobi triple product `θ = Π(1−q^{2n})(1+q^{2n−1}z)(1+q^{2n−1}/z)`. This *is* a product of independent two-state spin partition functions whose zeros lie on circles. The FE of ζ (the Weil-cone producer, L105) is the modularity of that product.
- **Literature audit (this cycle).** Konstantopoulos–Patie–Sarkar (Ann. Inst. Fourier 2024) reformulate both Lee–Yang and RH as van Dantzig problems in the Laguerre–Pólya class, and ask whether ξ lies in their new solution class (open). Newman's programme has long sought such a link; the Rodgers–Tao theorem `Λ_DN ≥ 0` shows RH would be *critical* (zero slack), consistent with L74/L79/L115.
- **Conjecture L116 (bridge).** Weil positivity of Λ (equivalently PBAP, under L114-type uniqueness) is equivalent to the Lee–Yang property of a single-spin measure built from the triple-product factors, with the Mellin transform taking the circle of Lee–Yang zeros to the critical line.
  - A *ferromagnetic* representation, i.e. positive pair couplings between the triple-product spins such that the Mellin image is exactly Φ, would be an exact, slack-free producer.
  - **How it could fail.** The Mellin transform does not preserve Lee–Yang structure in general: the triple-product zeros sit on circles `|z| = q^{±(2n−1)}` for each fixed `q`, and integrating over `q` (Mellin in `x`) mixes them. The positivity needed is for the `q`-integrated object. That is exactly the step where every modularity-based attempt has stalled.
- **Status.** A candidate class of *exact* producers compatible with L115's rigidity-at-the-boundary. No proof, and the bridge step (Mellin integration preserving Lee–Yang) is the open core. Recorded so the next cycle can test the bridge on the `N = 1` Pólya case (L97), where positivity is *known*: Pólya's real-rootedness for the one-term kernel should correspond to a Lee–Yang statement for a single triple-product factor.
- **L116 test (same cycle).**
  - *Pólya's `N = 1` case is a Lee–Yang instance.* Pólya's kernel is `(2cosh(9u/2) + 3cosh(5u/2))·exp(−2π cosh 2u)`. The factor `exp(−V)` with `V = 2π cosh 2u` is even, entire, with all Taylor coefficients positive, which is the ferromagnetic single-spin class (Newman; the `φ⁴`-type classes are its polynomial truncations). Real-rootedness of `K_{iz}(a)` in the order is its Lee–Yang property. The positive cosh prefactor acts by averaging imaginary shifts, which Pólya handles directly. ✓
  - *The full kernel breaks the bridge at the first structural step.*
    - (a) `Φ = Σ_n(…)exp(−πn²e^{2u})` is a *sum* (mixture) of such kernels. The Lee–Yang class is closed under *convolution* of measures (products of Laplace transforms), not under mixtures.
    - (b) The Jacobi triple product turns θ into a product *of densities in `u`*. That corresponds to convolution of the *transforms*, which does not preserve real-rootedness.
    - (c) `−log Φ` is not entire (Φ has complex zeros), so `Φ` cannot be written as `exp(−V)` with `V` entire of the ferromagnetic type. The Newman single-spin sufficient conditions therefore do not apply. This is not a disproof of Lee–Yang for Φ, but it rules out the standard producers.
  - **Verdict: KILLED as stated.** The positive survivor is a precise statement of where Lee–Yang producers stop. They cover exactly the `N = 1` (Pólya) level, where positivity comes from a *single* entire potential. The multi-term (arithmetic) sum is where the prime information enters, and no ferromagnetic closure operation reaches it.
  - This mirrors L97 and L99: every positivity producer we have found works at `N = 1` or with slack. The arithmetic sum over `n` is precisely where positivity must come from the FE, i.e. modularity across all `n` at once.

### L117 — Petersson Gram producers: already closed in the corpus. Pole-free producers at the boundary: heuristically `β ≤ 1`. All open cores share one barrier: mean values beyond length `T` (α ≥ 1). AUDIT + REDUCTION
- **Petersson/Poincaré Gram representation (planned candidate): KILLED by corpus search.**
  - Unfolding `‖P_f‖²` produces `ζ(2s−1)/ζ(2s)`, whose zeros `ρ/2` sit on `Re s = ¼`. They are second-sheet resonances, never `L²` spectrum.
  - The corpus Route-HB audit (memories `hb-producer-burden-is-second-sheet-positivity`, `hb-general-fuchsian-barrier`) already proves that Maass–Selberg positivity is σ-blind on the strip. Second-sheet positivity exists but points the wrong way (an upper bound). The trace-formula reading gives only an upper bound on the Weil functional (Hejhal 1976).
  - Not re-derived.
- **Pole-free producers at the boundary (heuristic).** Apply L109's inequality `V ≤ U² − U·S₃/V` at the boundary (`κ → 0`).
  - If the boundary mean square of a prime-supported pole-free `D` were diagonal, `V ≈ ¼β²log²T`.
  - Against `U² = ¼log²T` this gives **`β ≤ 1`**. With L77 (`β ≥ θ*`), a pole-free producer would need `θ* ≤ β ≤ 1`, and the gap weights (which need `β ≳ 9` by interior constraints) would be dead.
  - **Why it is only heuristic.** At `κ ≲ κ₀ ≈ 3–5` the truncation lemma needs lengths `x = T^{A}` with `A ≳ 5/κ > 1`. At those lengths the Montgomery–Vaughan diagonal is no longer valid. At `σ = ½` exactly, the spectral correction `∫h(τ)x^{i(τ−t)}/(i(τ−t))dτ` is of the same size `O(log T)` as the fluctuation.
- **Unification of the open cores.**
  - (i) Zeta-sized second completions: the moment methods of L103/L104 need the off-line data to be Beurling-bounded, and zeta-sized data carry the full `log T` fluctuation of prime sums of length `≥ T`.
  - (ii) Low-density pole-free producers: the L109 inequality needs diagonal mean values at `κ < κ₀`, i.e. Dirichlet polynomials of length `> T`.
  - (iii) RH / atomicity: by L111, atomicity is visible only in the form factor at `α ≥ 1`, which again means lengths `> T`.
  - **All three are the same barrier: mean values on `[T, 2T]` of arithmetic Dirichlet polynomials of length beyond `T`**, equivalently pair correlation beyond `α = 1` (Montgomery's conjecture, the Bogomolny–Keating range).
  - This is the precise place a producer must act. No argument of mean-value type confined to `α < 1` can produce Weil positivity at the exact datum.
- **Status.** Producer = the FE through Λ, with efficacy RH. Every remaining core reduces to the `α ≥ 1` barrier. Next genuinely new direction: a positivity mechanism for arithmetic mean values beyond length `T`. Candidates are the Bogomolny–Keating ratio heuristics made rigorous for *one-sided* (sign) statements, or Weil positivity itself used as the input that controls `α ≥ 1`. The latter would be circular unless it comes from a different L-function family (averaging over twists supplies `α ≥ 1` information unconditionally in families).

### L118 — Family transfer (Dirichlet characters mod q): family positivity reaches ζ only with conductor slack `log q`, in the wrong direction. KILL [P] + exact slack law
- **Computation [P].** For PD polar `Φ` at level `A`, average the Weil forms of the primitive characters mod `q` (prime `q` for simplicity):
  `(1/(q−2))Σ_{χ≠χ₀} Q_χ(Φ) = arch(Φ) + (log q/2π)·Φ(0)·c − Σ_{n≡1 (q)} Λ(n)n^{−½}(Φ(log n) + Φ(−log n)) + O(Φ(0)/q)`,
  by character orthogonality.
  - For ζ on the *q-blind cone* (tests vanishing at `log n` for `n ≢ 1 mod q`) this gives the exact identity
    `Q_Λ(Φ) = (family average)(Φ) − c(log q/2π)Φ(0) + O(Φ(0)/q)`.
- **Transfer.**
  - Family positivity (known unconditionally for support `< log(q+1)`, and with Kuznetsov/large-sieve input up to about `2 log q` in the one-level-density sense) yields only `Q_Λ(Φ) ≥ −c(log q/2π)Φ(0)` on the q-blind cone.
  - The slack *grows* with the conductor. Family positivity never reaches the slack-free boundary: its positivity *is* conductor slack.
  - **Verdict: KILLED.** Families supply `α ≥ 1` information only in averaged form, and the averaging is paid for by `log q` slack, exactly the resource that vanishes at ζ's datum.
- **Positive survivor (exact slack law) [P].** On the q-blind cone, the discrepancy between ζ's Weil form and the family-averaged form is exactly the conductor term `c(log q/2π)Φ(0)`, up to `O(Φ(0)/q)`.
  - So "PBAP for ζ restricted to q-blind tests" ⟺ "family-averaged positivity with the conductor term removed". As `q → ∞` the q-blind cone increases to the full test cone.
  - This gives a *one-parameter family* of equivalent forms of Weil positivity, indexed by `q`. At each `q` the needed statement is "the family average dominates the conductor term", which is again RH-strength. Recorded as an equivalence, not a producer.
- **Programme status (for the record).** Theorems L103–L106, L114 and L107 make *finding a producer of Weil positivity for ζ's exact archimedean datum* equivalent to proving RH within every class analysed (Beurling-class completions). Outside that class a producer must be a zeta-sized completion with continuous spectrum, whose existence would contradict the heuristic L109/L117 bounds. Each further cycle can shrink the unexcluded region or find new equivalent forms. A producer at the exact datum, if found, *is* a proof of RH.

### L119 — Making L117's boundary bound rigorous: the missing off-diagonal is exactly the Hardy–Littlewood prime-pair correlation. REDUCTION [P, conditional theorem sketch]
- **Spectral side.** For a pole-free `lam ∈ W` the Weil measure is a.c. with density `h ≥ 0`. So `X = P_η⋆h` and `Var(X)` is the variance of `h` smoothed at scale `2η`.
  - By Plancherel over `[T,2T]`, `Var(X) = Σ_n lam(n)²n^{−1−2η}/2 + Σ_{n≠m}lam(n)lam(m)(nm)^{−½−η}⟨cos(t log n), cos(t log m)⟩_{[T,2T]}`. This is the diagonal plus the weighted pair correlation of the support of `lam` at scale `n/T`.
  - For `n, m ≤ T^{1−ε}` the off-diagonal vanishes (Montgomery–Vaughan). For lengths `> T` it is the pair correlation of `lam`'s atoms at relative distance `< 1/T`.
- **Atomicity from pair correlation.** In L111's language, the atomic mass of `μ_lam` is the large-α mean of the form factor `F_lam(α)`. For `α > 1` the form factor is governed by exactly this off-diagonal.
  - For prime-supported `lam` with weights `lam(p) = β log p·(1 + ε_p)`, where `ε_p` is a smooth or slowly varying profile, the off-diagonal is `β²·(weighted Hardy–Littlewood pair correlation of primes) + (ε-terms)`.
  - **Conditional theorem [P, assuming a uniform Hardy–Littlewood pair correlation for primes in the Goldston–Montgomery form].** Then `F_lam(α) → β²·c_HL > 0` as `α → ∞`, so `μ_lam` has atomic mass `≍ β²`. This contradicts pole-freeness.
    - So pole-free prime-supported producers with smooth weight profiles do not exist, under HL.
    - Only weight profiles `ε_p` that cancel the Hardy–Littlewood correlation at every scale `p/T` escape. Such profiles would have to encode the prime-pair singular series with the opposite sign.
- **Where this leaves the barrier.**
  - The rigorous version of L117 is equivalent in strength to Goldston–Montgomery-type pair correlation (primes in short intervals ⟺ Montgomery's `F(α)` for `α ≥ 1`).
  - For ζ alone nothing unconditional is known beyond `α = 1`. Families reach further (Goldston–Gonek–Özlük–Snyder type results for Dirichlet families), but only in averaged form with conductor slack (L118).
  - **Verdict.** The last non-RH lever (E-107) is conditional on the Hardy–Littlewood/pair-correlation input, the same `α ≥ 1` frontier as the other open cores.
- **Programme-level conclusion.** Each open core now has an identified *classical* equivalent or sufficient input:
  - (i) zeta-sized completions: RH-strength;
  - (ii) low-density pole-free producers: Hardy–Littlewood pair correlation;
  - (iii) atomicity: Montgomery's pair-correlation conjecture beyond `α = 1`.
  - The producer of positivity at ζ's exact datum is the FE acting through Λ, and making it produce positivity is RH. The programme has no remaining route that avoids these classical frontiers.

### L120 — Batch of five quick producer conjectures, each tested (conjecture → kill → survivor)
- **P1. Sign-only ratios at `α ≥ 1`.** A producer needs only a sign, so conjecture a one-sided Bogomolny–Keating statement: `Σ_{γ≤T}|A(½+iγ)|² ≥ 0`-type lower bounds for Dirichlet polynomials of length `x > T`, as analytic sums.
  - *Kill.* For `x ≤ T^{1−ε}` the analytic discrete mean `Σ_ρ A(ρ)A*(1−ρ)` has main-term quadratic form equal to Weil's form at level `log x`. Its positivity is PBAP at that level. For `x > T` the main terms are not known unconditionally. The sign statement is Weil positivity itself: **CIRCULAR.**
  - *Survivor.* The analytic discrete mean at length `x` *is* the level-`log x` Weil form. This dictionary lets Gonek-type discrete moments and Weil levels be traded one for one.
- **P2. Heat-trace / Gaussian positivity.** Conjecture: RH ⟺ `Σ_ρ e^{−tγ_ρ²} ≥ 0` for all `t > 0`, i.e. Weil positivity on centred Gaussians.
  - *Kill.* An off-line pair at height `γ₀` contributes `2e^{−t(γ₀²−δ²)}cos(2tγ₀δ)`. It is dominated by `e^{−tγ₁²}` from the first critical zero once `γ₀² − δ² > γ₁²`, which holds for all high zeros. So Gaussian positivity cannot detect high off-line zeros: **INSUFFICIENT** (strictly weaker than RH).
  - *Survivor.* Positivity on a one-parameter family of tests detects off-line zeros only below the height where the family's decay rate matches the first ordinate. A producer needs a family with *two* parameters (shift and width) or more, as in Weil's full cone.
- **P3. Sharpen Alpöge–Furman with ζ′-weights.** Alpöge–Furman get `≥ 2/3` simple critical zeros from the inertia of a compressed Weil form plus a rank–trace inequality. Conjecture: weighting the compression vectors by `ζ'(ρ)`, as in L103, raises the rank–trace ratio to 1.
  - *Kill.* L103's gain came from off-line zeros being *degenerate* (`|ζ'(ρ)| ≤ K`), which was forced by a hypothetical completion. For ζ itself nothing forces degeneracy of off-line zeros, and `ζ'`-weighting inflates the off-line contribution to `tr(M²)` as much as the critical one: **NO GAIN.**
  - *Survivor.* The rank–trace loss in Alpöge–Furman is exactly the variance of `|ζ'(ρ)|²`-type weights across zeros. Any sharpening needs a zero-weight whose second moment matches its first-moment square (a "flat" weight), which is again a pair-correlation statement.
- **P4. Γ-duplication producer.** `Γℝ(s)Γℝ(s+1) = Γℂ(s)`. Conjecture: Weil positivity for the Γℂ datum (Dedekind zeta of `ℚ(i)`, with conductor slack `log 4`) transfers to ζ by factoring `ζ_{ℚ(i)} = ζ·L(χ₋₄)`.
  - *Kill.* Positivity of a product's Weil form does not split into the factors' (L118: averaging costs slack). RH for `ζ_{ℚ(i)}` implies RH for ζ, but proving it is harder. **WRONG DIRECTION.**
- **P5. A producer from the sign changes of Z.** RH ⟺ `Z(t)` has `N(T)` sign changes counted with multiplicity. Conjecture: a positivity principle for the *ordering* of Gram points, via Gram's law with multiplicity, produces all sign changes.
  - *Kill.* Gram's law fails a positive proportion of the time (Trudgian), and zeros are equidistributed relative to Gram points only conjecturally (Odlyzko; Arias de Reyna, L102). **UNAVAILABLE.**
  - *Survivor.* The phase-locking identity of L102 turns "sign changes at every Gram-shifted point" into the analytic sum `Σ_ρ χ(1−ρ)(…)`, whose `κ = 1` mean vanishes unconditionally (Arias de Reyna). So Gram-type producers are exactly first-moment-free, and cannot carry sign information.
- **Batch verdict.** Five conjectures, five kills, each with a recorded survivor. All five kills fall into three classes:
  - circular (P1);
  - insufficient one-parameter families (P2);
  - dependent on pair-correlation or equidistribution inputs (P3, P5), which is the L117/L119 barrier.
  - P4 goes the wrong way: positivity for a product is not a producer for its factor.

### L121 — Beating Alpöge–Furman's 2/3: the rank–trace input is Montgomery's form factor on `(−1,1)`, so any improvement needs `α ≥ 1`. REDUCTION (corpus-checked)
- **Corpus facts.** `RiemannGaussian.HermitianRankTrace.rank_trace_ineq_two` states `‖P+Q‖_F² ≥ c·tr P − (c²/4)r + 2c·tr Q − c²b`, and `Zeta23SimpleCriticalDensity.two_thirds_le_liminf_xiSimpleCriticalRatio` is the unconditional theorem.
  - The compressed Weil form is `M = P + Q`. Here `P ⪰ 0` has rank `≤` the number of simple critical zeros in the window, and `n₊(Q) ≤` the number of off-line pairs (Sylvester).
  - `tr M` comes from the explicit formula. `‖M‖_F²` is a second moment of the compressed form, i.e. a pair-correlation quantity at the compression scale.
- **Diagnosis.** With tests of Fourier support in `(−1,1)` (Montgomery range), `‖M‖_F²` is computed from `F(α) = |α| + T^{−2|α|}log T` on `(−1,1)`. Optimizing `c` gives exactly Montgomery's `2/3`, previously known only under RH, now unconditional because Sylvester's inertia replaces RH.
  - A larger proportion needs `‖M‖_F²` for tests of support beyond 1, i.e. `F(α)` for `α ≥ 1`. Montgomery's pair-correlation conjecture `F = 1` there would give 100% by the same inequality.
- **Verdict.** The plan's target ("beat 2/3 via L102 + P1") reduces to the `α ≥ 1` barrier. Phase-locking (L102) only concerns hypothetical completions, and the P1 dictionary only reproduces Weil levels. Neither supplies form-factor information beyond α = 1. **REDUCED to L117/L119's barrier.**
- **Structural closure.** The programme's positivity producers (Weil form inertia, discrete moments, Herglotz structure) all consume exactly Montgomery-range information. Everything they produce is sharp at that range: Alpöge–Furman's 2/3, the L103/L104 uniqueness, the L107 mass law. The next genuine advance of *any* of these requires one new input — unconditional control of the pair-correlation form factor beyond `α = 1` for ζ alone.

### L122 — Finite-level Weil positivity cannot feed the `α ≥ 1` form factor: scale mismatch. KILL [P] + the only tools that pass the diagonal
- **Conjecture.** Known finite-level positivity (`Λ ∈ W_A` for `A ≤ ½(log 2 + 1/50)` in the corpus, `A ≤ 0.8` certified in arXiv:2608.24827) gives a lower bound on `F(α)` for `α ∈ [1, 1+δ]`.
- **Kill.**
  - `F(α)` at height `T` is the explicit-formula image of prime sums at scale `T^{α}`, i.e. tests of log-support `≈ α log T`.
  - Level-`A` positivity controls PD tests of support `≤ 2A`, which corresponds to `α ≤ 2A/log T → 0`.
  - Reaching `α ≥ 1` needs level `A ≳ ½log T`, and Weil positivity at that level is RH up to height `T^{O(1)}` (L85's transfer). **CIRCULAR at every height.**
- **Positive survivor (where the diagonal *is* passed today).** The only unconditional techniques that beat the Montgomery–Vaughan diagonal for ζ are:
  - Kloosterman/spectral inputs (Deshouillers–Iwaniec) behind Conrey's mollifier length `θ = 4/7`;
  - twisted fourth moments behind Bettin–Chandee–Radziwiłł's `θ = ½ + 1/66`.
  - Both pass the diagonal for *mollified second moments* (lengths up to `T^{4/7}` against ζ), not for *prime pair correlations* (lengths `> T` without ζ).
  - An analogue for prime sums of length `> T` over `[T,2T]` would be a short-interval analogue of level of distribution beyond ½ (Zhang–Maynard) for the variance of primes in short intervals. It is not known.
  - **This is the single technical frontier every open core of the programme reduces to.**
- **Status.** The programme's existence question is RH. Its last non-RH levers all need pair correlation beyond `α = 1`, whose only conceivable unconditional route is a Kloosterman-type bilinear input for prime sums of length `> T`. That input is a major open problem of analytic number theory and not a Weil-cone question.

### L123 — What `Λ ≥ 0` produces: on the prime-nonpositive cone the primes contribute exactly the pole. THEOREM [P] + refinement of the three-ingredient law
- **Corpus context.** The memory `deligne-amplification-obstruction` records kill-standard countermodels for every ingredient subset except FE ∧ Euler ∧ `Λ ≥ 0`, so a producer must use all three. This entry isolates what `Λ ≥ 0` alone contributes.
- **One-sided far-polar tests [P].** Take a real `ψ ≥ 0` with autocorrelation `R` supported in `(−log 2, log 2)`, and set `f = ψ − e^{−X/2}ψ(·−X)`.
  - Then `f̂(z) = ψ̂(z)(1 − e^{−X/2}e^{−iXz})` vanishes at `z = i/2`, so `Φ = f⋆f̃` is **polar** (`Φ̂(±i/2) = 0`).
  - `Φ(u) = (1+e^{−X})R(u) − e^{−X/2}[R(u−X) + R(u+X)]`. Every integer lag `log n` (`n ≥ 2`) lies outside `supp R`, so **`Φ(log n) = −e^{−X/2}R(log n − X) ≤ 0` for all `n ≥ 2`**.
  - This improves L75's two-sided correction, which left positive lobes at `±2X`.
- **Consequences.**
  - (a) *The prime-nonpositive cone `𝒞₋ = {PD polar Φ : Φ(log n) ≤ 0 ∀n}` is not archimedean-positive.* As `X → ∞`, `arch(Φ) → arch(ψ) < 0` for the corpus Fejér test (the shifted terms oscillate away).
  - (b) *On `𝒞₋`, nonnegative weights contribute exactly the pole.* For `lam ≥ 0` with smoothed density β, `Q_lam(Φ) = arch(Φ) + 2Σ lam(n)n^{−½}e^{−X/2}R(log n − X) → arch(ψ) + β·pole(ψ)`. For Λ (β = 1) this is small-support Weil positivity `W_Λ(ψ) ≥ 0` (Yoshida/Connes–Consani, corpus).
  - So **`Λ ≥ 0` produces positivity only through the PNT pole, and only up to the threshold β ≥ θ* (L77).** It contributes nothing at off-line zeros.
- **Refined three-ingredient law.**
  - `Λ ≥ 0` → the pole (low-frequency deficit payment, L99).
  - Euler product → the integer locations `log n`, hence uniqueness (L104/L114).
  - FE → boundary pinning `Re(−ζ'/ζ) = θ'` (L105).
  - Each is *used up* by its own role. A producer of RH must make them interact at the off-line zeros, and no mechanism in L101–L122 does. This matches the corpus's fibration obstruction: the missing object is a geometric structure in which the three roles are coupled, as Hodge index couples them for curves over `F_q`.

### L124 — F₁ intersection-form lifting: every analytic lifting reduces to the PBAP compression; a genuine producer needs a Riemann–Roch on the square. CONJECTURE → KILL + survivor
- **Conjecture I1.** There is an explicit linear lifting `f ↦ Θ_f` into a Hilbert space with `⟨Θ_f, Θ_f⟩ = arch(f⋆f̃)` on the prime-blind cone. This would be an exact SOS certificate (L85) for PBAP, hence a producer.
  - Motivation: the intersection form on `C × C`. Correspondences `D_Φ = Σ Φ̂(n)Γ_{F^n}` have `D_Φ·D_Ψ = W(Φ⋆Ψ̃)`, and polarity is orthogonality to the fibre classes (L96).
- **Kill.** Any lifting whose norm is computed by unfolding a lattice sum, whether Poisson on ℤ, Petersson on SL₂(ℤ) (L117), or Epstein on ℤ², produces integer-lag terms `Φ(log n)`. These vanish on the prime-blind cone, leaving the archimedean term alone.
  - Exactness then requires the multiplication operator by `A(t) = Re ψ(¼+it/2) − log π` to be positive on the lifted image of the prime-blind cone. That *is* PBAP.
  - Since `A < 0` near `t = 0`, no lifting into a space where `A` acts diagonally can be positive without the prime-blind constraint doing the work. **CIRCULAR: I1 ⟺ PBAP.**
- **Survivor (what the curve case has that liftings lack).** Hodge index for `C × C` is not proved by exhibiting a norm. It is proved by *Riemann–Roch on the surface*:
  - `D² > 0` and `D·H = 0` force `h⁰(nD)` or `h⁰(−nD)` to grow;
  - this contradicts primitivity.
  - The positivity comes from a *dimension count of sections*, not from a Gram representation.
  - For `Spec ℤ`, the one-dimensional Riemann–Roch *is* Poisson summation (Tate), which is the FE (L105). The missing object is a two-dimensional Riemann–Roch for the arithmetic square, with sections of "correspondence divisors" `D_Φ`. That is the Connes–Consani programme (Riemann–Roch for the ring ℤ; the arithmetic/scaling site).
  - Every analytic tool tested in L101–L123 is one-dimensional (FE = 1-D RR). This is the precise sense in which they cannot produce the positivity.
- **Programme-level statement.** The producer problem splits as follows:
  - *identified*: the functional equation (1-D Riemann–Roch) acting through Λ, with efficacy RH;
  - *missing*: a 2-D Riemann–Roch whose dimension count yields Hodge index for the scaling correspondences;
  - *excluded*: all 1-D analytic, spectral, statistical and physical producers examined in L85–L123.

### L125 — Finite-type uniqueness closed on paper; the density input was never needed in the strong form. THEOREM [P] (card → stage 2)
- **What changed.** The card `weil-cone-finite-type-uniqueness` is dependency-closed. It moved to `2-fully-proven/11-rh-zero-divisor-geometry/`.
- **(B) proved exactly.** A Weil-positive `T` is positive definite, hence tempered (Bochner–Schwartz). The one-sided Laplace transform of `χT` is holomorphic on `Re s > ½` and equals `Φ_lam + E` with `E` entire. So:
  - `Φ_lam` is holomorphic on `Re s > ½`;
  - boundary poles are simple with real residue `≥ 0` (a local analysis of `(x − i0)^{−k}` against a Radon measure `μ ≥ 0`);
  - the pole at `s = 1` pins `A(1) = β`.
  - The last point is new in this programme. It kills the `A ≡ 0` branch of L104 and gives `c = 1` with no appeal to L52/L77/L81.
- **(C) replaced by (C′).** The off-line terms need only `Σ_{β>½, γ≤T} T^{β−½} = o(T log²T)`. This follows from Jutila (`A = 1 − ε`, near the line, with `log T`) and Ingham (`4/3`, with `log⁵T`, beyond `12 loglog T/log T`), giving `O_ε(T log^{1+12ε}T loglog T)`.
  - The earlier claim "`A > 1` is necessary for this method" confused a uniform exponent with the weighted count. It is withdrawn (MUST-520).
- **Step 3 made direct.** RH follows from holomorphy of `ξ'/ξ − D_v`. Then `−Re D_v ≥ 0` on the line, and by Phragmén–Lindelöf on `Re s > ½`. A nonnegative almost-periodic function with mean `−v(1) = 0` vanishes, so `v = 0`.
- **Significance.** Unconditionally, the Weil cone of ζ's archimedean datum meets the finite-type affine space `Λ + {Λ⋆(a−δ₁) + f⋆μ + v}` in at most the single point Λ, which lies in the cone iff RH. Finite-type producers other than Λ do not exist, whether or not RH holds.

### L126 — Singular deficit law: a second completion must modify `≫ T` atoms, in proportion to its distance from Λ. THEOREM [P] (card at stage 2)
- **Conjecture (from L106 + L107).** L106's almost-periodicity argument ("pole-free ⇒ `v = 0`") should be quantitative. A completion modifying only a sparse set of singular points should be forced to equal Λ.
- **Theorem L126.** For Weil-positive `lam`, with `w = lam − Λ`: `liminf [2N_off⁺(T) + R⁺(T)]/T ≥ sup_{σ>1} M₁(w,σ)/2π ≥ sup_n |w(n)|/(4πn)`, where `R⁺` is the total critical-atom deficit of `lam` relative to Λ.
- **Mechanism.**
  - The exact Herglotz dictionary gives `Re Φ_lam = Poisson(μ/2)`.
  - Subtracting the off-line pairs and critical atoms turns `Ψ = −D_w + S` into a Herglotz function with boundary measure `ν ≥ 0`.
  - So the almost-periodic `Re(−D_w(σ+it))` has mean 0 and a lower envelope `−ε`, with `∫_0^T ε = π(2N_off⁺ + R⁺)`.
  - Its L¹ mean, which is at least any Bohr coefficient, is therefore paid for by singular modifications.
- **Verdict:** SURVIVES; proved. Complementary to finite-type uniqueness: structured-dense modifications are excluded there, sparse-arbitrary ones here. The remaining uniqueness core is infinite-type completions modifying `≫ T` atoms. The law is linear in `T`; `T log T` needs the weighted-mean (discrete moment) regime.
- **Producer reading.** Λ is isolated in the Weil cone in the norm `sup_n|w(n)|/n`, at cost measured by singular modifications. A second producer cannot be a small "repair" of Λ. It must reorganize a positive-density-in-`T` set of the critical atoms.
- Card: `2-fully-proven/11-rh-zero-divisor-geometry/weil-cone-singular-deficit-law.md`.

### L127 — Where every alternative completion must come from: the pole-free funnel and the length-`T` barrier. REDUCTION [P] + obstruction record
- **Positive-proportion deficit law.**
  - Conjectured: `3N_off⁺ + R⁺ ≫ T log T` whenever `w` has prime mass.
  - Proved ingredients:
    - the exact near-line identity `−D_w = Φ_lam − ξ'/ξ`;
    - `∫_0^T Re(−D_w)(σ_T+it)dt = 2πN(σ_T,T) + O(log T)`, from the mass lemma `(μ/2)([0,T]) = πN(T) + O(log T)` for every Weil-positive `lam`;
    - the near-line envelope.
  - Obstruction: L¹ ← L² needs an upper bound on the Weil measure of `lam` at scale `1/log T`, and positivity gives only lower bounds. **Conditional** on domination `μ_lam ≤ C(μ_Λ + log t dt)`. Recorded in the deficit-law card.
- **Funnel (all alternatives are pole-free-type).**
  - Under RH, a first-order perturbation `Λ + εw` needs atom deficits at `≫ T` zeros (L126).
  - Explicit zero-indexed constructions `D_w = Σ_ρ φ(γ)[ζ(1+s−ρ) − 1]` fail: summable `φ` gives `R⁺ = O(1)`, which is killed; non-summable `φ` regularizes to `(1−ε)Λ + ε·u` with `u` pole-free.
  - So every element of `W ∖ {Λ}`, whether or not RH holds, requires the existence of integer-supported `u` with average 1 and `H = D_u − 1/(s−1)` holomorphic on `Re s > ½`, such that `Re H(½+it) ≤ θ'(t) + ½/(¼+t²)`.
  - This is E-107 in ζ-free form. If such `u` exists, PBAP holds unconditionally and uniqueness fails. If none exists, and no infinite-type atom-reorganizer exists either, then RH ⟺ PBAP.
- **Where E-107 sits.**
  - Multiplicatively rich `u` are killed by resonance (L107).
  - For prime-supported `u` with balanced weights, the small primes are harmless: Kronecker alignment gives at most `≈ 2√(log t) ≪ ½log t`.
  - The decisive fluctuations come from primes `p ≍ t^{A}`, `A ≥ 1`. Their value distribution on `[T,2T]` is controlled by prime-pair correlations of length `≥ T`, i.e. Hardy–Littlewood.
  - The upper bound `θ' ∼ ½log t` and a Gaussian with standard deviation `≍ A log t/2` differ only by a constant factor. The E-107 question is therefore a *constant-level* large-deviation question for prime sums beyond length `T`. It is the same `α ≥ 1` barrier as L117, L119, L121 and L122, now seen from the existence side.
- **Exact finite-length consequence (kill tool).** For every Weil-positive `lam`, every `X`, and every Fejér-type kernel `k ≥ 0` with `supp k̂ ⊂ [−log X, log X]`:
  `Σ_{n≤X} lam(n)n^{−½}k̂(log n)cos(t log n) ≤ (θ'⋆k)(t) + (pole terms ⋆ k)(t)` for all `t`.
  - This is Weil positivity on the translates of one test, restated as a one-sided bound on a finite trigonometric polynomial. It is the test used by every resonance kill.
- **Verdict:** REDUCTION. Existence and uniqueness now meet at one analytic object: the upper tail, at level `½log t`, of prime sums of length `≥ T` near the critical line.

### L128 — The Montgomery-range cap constant: what `α < 1` information can and cannot force on a prime-supported completion. QUANTITATIVE BLINDNESS [P]
- **Setting.** `u` is Weil-positive and supported on prime powers, with `u(p) = c_p log p` and average weight 1. `P_X(t) = Σ_{n≤X}u(n)n^{−½}k̂(log n)cos(t log n)` with `k ≥ 0`, `supp k̂ ⊂ [−log X, log X]`, `X = T^{1−ε}`.
- **Exact inputs (unconditional).**
  - The cap `P_X ≤ θ'⋆k + O(1/t²) =: M ≈ ½log T` (L127 kill tool).
  - `E P_X = 0`.
  - `Var P_X = ½Σ_{n≤X}u(n)²k̂(log n)²/n·(1+o(1))` (mean-value theorem, length `< T`).
  - `E P_X³ = O(1)`. Frequency matching at length `< T` forces exact `n₁n₂ = n₃`, and on prime powers only `p^i·p^j = p^{i+j}` survives.
- **Cap inequality (L109 form).** `X ≤ M`, mean 0 and third moment `S₃` give `V ≤ M² − M·S₃/V`. Hence `½ mean(c²)·β_k·log²X ≤ ¼log²T(1+o(1))`, where `β_k = ∫_0^1 w·φ(w)²dw`, `φ = k̂(L·)` is positive definite on `[−1,1]`, and `φ(0) = 1`.
  - Fejér `φ = (1−|w|)⁺` gives `β = 1/12`, hence `mean(c²) ≤ 6`.
  - `β ≤ ½` always, since `|φ| ≤ 1`. So no compactly supported kernel can force more than `mean(c²) ≤ 1/(2β*)`, with `β* < ½` the Turán-type extremal constant.
- **With the Poisson kernel** (`k̂(v) = e^{−a|v|/log T}`, not compactly supported), the `α < 1` part of the variance is `≥ ¼ mean(c²)log²T(1 − O(a))`, using `F_u ≥ 0` for `α ≥ 1`.
  - So `V ≥ M²·mean(c²)` as `a → 0`. **Λ (`c ≡ 1`, the Cauchy–Schwarz equality case) is exactly critical.**
  - But `S₃` now involves near-solutions `p₁p₂ ≈ p₃` beyond length `T`. The naive prime expansion of `S₃` diverges, so it is the `α ≥ 1` triple correlation.
- **Reading.** Unconditionally, the `α < 1` range constrains prime weights only to a bounded constant (`mean(c²) ≤ 6`). The sharp constraint, forcing `c ≡ 1` (Λ) at `a → 0`, needs the third moment beyond length `T`. This quantifies L111: Λ is the variance-minimal prime-supported system, and Weil positivity is critical exactly at Λ, but the certificate of criticality lives at `α ≥ 1`.
- **Verdict:** BLINDNESS, with the exact constant. No kill of E-107 from the Montgomery range; the barrier is confirmed from both sides.
- **L127/L128 precision note (self-audit).** In the kill tool, "(pole terms ⋆ k)" means the continuation term `2π Re k(t ∓ i/2)`, not the boundary value of `Re(1/s + 1/(s−1))`, which is 0 on the line.
  - The finite polynomial `Σ_{n≤X}lam(n)n^{−s}k̂(log n)` equals `D_lam⋆k` only for `σ > 1`. Crossing `σ = 1` adds the pole residue. For Fejér `k` this is of size `X^{½}/(t² log X)`, dominant for `|t| ≲ X^{1/4}`.
  - L128 works at `t ≍ T` with `X = T^{1−ε}`, where the term is `O(T^{−3/2})`, so it is unaffected.
  - A tempting variant is also excluded by this term. Windows centred at `t = 0` (so `Ŵ ≥ 0`) would make every off-diagonal and triple term nonnegative for `u ≥ 0`, at any length. But there the pole term dominates the cap. Near `t = 0` the naive cap `θ' < 0` would even contradict `u ≥ 0`, which shows that the pole term is essential and not a small correction.

### L129 — Extremality of Λ in the Weil cone is exactly crystalline rigidity of the zeta zeros (pure-atomic case). EQUIVALENCE [P] (short)
- **Setting.** `W` (integer-supported, in the box) is convex and closed. Assume RH, so Λ ∈ W and `μ_Λ = 2πΣm_ρδ_γ` is purely atomic.
- **Theorem L129.** Λ is an extreme point of `W` iff there is no nonzero real integer-supported `w` (in the box) such that `D_w = Σ_{crit} r_ρ[1/(s−ρ) + 1/ρ] + b` with real `|r_ρ| ≤ m_ρ` and no absolutely continuous boundary part.
  - (⇒) If `Λ = ½(u₁+u₂)`, then `μ_{u_i} ≤ 2μ_Λ` is atomic on the zeros. So `Ψ_i = −D_{w_i} + Σ r/(s−ρ)` is Herglotz with boundary measure `ν = 0`, hence `Ψ_i = a(s−½) + ib`. Growth forces `a = 0`.
  - (⇐) `Λ ± w ∈ W`, since the atoms `m ± r ≥ 0` and the a.c. part vanishes.
- **Necessary structure of such `w`.**
  - (i) Deficit law (L126) applied to `±w`: `R⁺(T)` and `R⁻(T)` are both `≥ (sup|w(n)|/4πn)T`, so the reweighting must have both signs on `≫ T` zeros.
  - (ii) `Σ_γ r_γδ_γ` is a signed Fourier quasicrystal on the zero ordinates with spectrum in `±log ℕ_{≥2}`, hence a spectral gap `(−log 2, log 2)`. Its local mean vanishes: no Γ-drift, since `D_w` is a Dirichlet series decaying like `2^{−σ}`.
  - (iii) Multiplicative reweightings `r_γ = φ(γ)`, with `φ = Σ b_k k^{iγ}` a Dirichlet polynomial, are impossible. The archimedean part `θ'φ` would need Fourier support in `log ℕ`, which forces `φ ≡ 0`.
  - (iv) If all `r_ρ ∈ ℤ`, then `G = exp(−∫D_w)` is a Dirichlet series whose divisor lies on ζ's critical zeros and has zero density drift. This is a "partial zeta function"; Hamburger-type rigidity suggests none exists.
- **Reading.** Extremality of Λ under RH is the pure-atomic case of the L105 crystalline-rigidity conjecture. The deficit law shows any counterexample must be two-signed and dense (`≫ T`). L129 is an **equivalence, not progress on the core**. It records that "is Λ the only producer" and "do the zeta zeros carry a second crystalline structure over `log ℕ`" are the same question.

### L130 — Function-field control: there the Weil cone is all positive measures of mass `2g`, and P¹ is a pole-free producer. The number-field obstruction to the F₁-P¹ is exactly `θ' < 0` on `|t| < 2π`. STRUCTURAL CONTRAST [P]
- **Function fields.** `C/F_q` of genus `g`. A real weight sequence `N'_n` (`n ≥ 1`) replacing the point counts is Weil-positive iff `μ̂(0) = 2g`, `μ̂(±n) = (q^n + 1 − N'_n)q^{−n/2}` is a positive-definite sequence. By Herglotz, this means iff it is the Fourier sequence of a symmetric positive measure of mass `2g` on `ℝ/(2π/log q)ℤ`.
  - So `W_C` is the whole cone of such measures. Existence is trivial, and uniqueness fails.
  - The prime-blind cone on the lattice `ℤ log q` is `ℝδ₀`, so the PBAP analog is the tautology `2g ≥ 0`.
  - Even the **arithmetic** subclass (Euler products with integer place counts) is not a singleton. The counts of P¹, `N'_n = q^n + 1`, give the uniform measure. That is a positive, pole-free completion of *any* genus datum, and `(1−ε)Λ_C + ε·Λ_{P¹}` lies in `W_C` for all `ε ∈ [0,1]`: the function-field ε-core is nonempty.
- **Number fields: why the analog fails.** The F₁-analog of P¹ has `ζ_{P¹/F₁} = 1/(s(s−1))`, whose counting "sequence" is the continuous density `dx` (the pole term).
  - (i) It is not integer-supported. Integer-supported approximations (`u ≡ 1`) inherit the large values of `ζ(½+it)` and are killed by resonance (L107).
  - (ii) **Even allowed as a continuous system it is not Weil-positive.** Its Weil measure is `2θ'(t)dt`, and `θ'(t) = ½Re ψ(¼+it/2) − ½log π < 0` for `|t| < 2π` (`θ'(0) = −2.686`).
  - The archimedean "genus density" of Spec ℤ is negative at low frequency, unlike the constant `2g ≥ 0`. At low frequency the positivity must be *paid by the small primes*: `Re D_lam(½+it) ≤ θ'(t) < 0` for `|t| < 2π`. That is the Mertens-type budget of L50/L101.
- **Consequence for the programme.** Every rigidity phenomenon found for ζ's Weil cone (L78–L81, L103–L104, L126) is **number-field specific** and must use at least one of:
  - (a) the non-lattice positions `log ℕ` (almost periodicity instead of periodicity);
  - (b) the negative low-frequency archimedean density.
  - The finite-type theorem uses (a) through rational twists and Gonek's lemma, and the deficit law uses (a) through Bohr means. **(b) has not yet been exploited in a uniqueness proof.** It is the only structural difference from function fields where Λ could be pinned without the zeros.
- **Next conjecture (L131 target).** A *low-frequency pinning law*. Weil positivity with `θ' < 0` on `|t| < 2π` forces `Re D_lam(½+it) ≤ θ'(t) < 0` there. Together with integer support, this might force `lam(n) = Λ(n)` for small `n`, through an exact extremal (Beurling–Selberg-type) problem on `|t| < 2π` with frequencies `log n`.
- **L130 correction (self-audit, immediately).** Ingredient (b) *has* been exploited, in L50 and L101 (MUST-513: `C ≤ β − γ/2 − log 2 − ½log π`). It gives only an inequality with slack: Λ passes with margin `λ₁ = Σ1/ρ = 0.0231`, and `Φ_Λ(σ) = ξ'/ξ(σ) = Σ_ρ 2(σ−½)/((σ−½)²+γ²)` is small but strictly positive on `σ > ½`.
  - Low-frequency tests are long-support tests, and Λ is **not extremal** there. So no exact low-frequency pinning of `lam(n)` can hold. An open set of low-frequency perturbations survives, and exactness can only come from the atoms (high frequency).
  - The L131 target is **withdrawn**. The function-field contrast stands: rigidity needs (a), plus the *sign* in (b) to exclude P¹-type completions. The exact pinning must come from (a) at `α ≥ 1`, in agreement with L127/L128.

### L131 — An explicit producer: ζ's archimedean datum is Weil-realized, with a coercive form, by Lebesgue measure on (1,∞) minus one point mass. All RH content of existence is integrality. THEOREM [P] + dichotomy conjecture
- **Key identity (the `s = 0` cancellation).** `G_∞(s) + 1/s = ½ψ(s/2 + 1) − ½log π =: Γ̃(s)`, since `ψ(z+1) = ψ(z) + 1/z`. It is holomorphic on `Re s > −2`.
  - Hence for every system `lam`, `Φ_lam = Γ̃(s) − H_lam(s)` with `H_lam := D_lam − 1/(s−1)` (holomorphic at 1 exactly when the pole is matched). Weil positivity reads **`Re H_lam(½+it) ≤ h(t)`** as boundary distributions, where
    `h(t) := Re Γ̃(½+it) = ½Re ψ(5/4 + it/2) − ½log π = θ'(t) + ½/(¼+t²)`.
  - (i) `h(0) = ½ψ(5/4) − ½log π = −0.686092`, from the exact value `ψ(5/4) = 4 − γ − π/2 − 3log 2`.
  - (ii) `h` is strictly increasing on `t > 0`, since `h' = −¼Im ψ'(5/4 + it/2) > 0`. The `n = 0` term of `θ''` equals `d/dt[½/(¼+t²)]` exactly, which is the `s = 0` cancellation seen on the line.
  - (iii) From `Re ψ(x+iy) = ψ(x) + Σ_n y²/((n+x)((n+x)²+y²))` and integral comparison: `h(t) ≥ −0.686092 + ¼log(1 + 4t²/25)`. So `h ≥ 0` for `t ≥ 9.54`.
- **Theorem L131 (explicit producer).** Let `lam₀ := 1_{(1,∞)}(x)dx − e^{1/200}·δ_{e^{1/100}}`. Then `lam₀` is Weil-positive for ζ's archimedean datum (pole weight 1), with purely absolutely continuous Weil measure `μ = 2[h(t) + cos(t/100)]dt ≥ 0.618 dt`. Hence `W_{lam₀}(h⋆h̃*) ≥ 0.618·‖h‖²/(2π)·2π`, i.e. the form is **coercive**.
  - *Proof.* In log coordinates `T_{lam₀} = arch + e^{−|u|/2} + (δ_{1/100} + δ_{−1/100})`. The Lebesgue part cancels the growing half of the pole term exactly, and the negative atom enters with weight `e^{1/200}·e^{−1/200} = 1`. `T` is tempered, and `FT(T) = 2θ' + 1/(¼+t²) + 2cos(t/100) = 2[h + cos(t/100)]`.
  - On `[0, 9.54]`: `h ≥ −0.6861` and `cos(t/100) ≥ cos(0.0954) = 0.9955`, so the sum is `≥ 0.309`.
  - On `[9.54, 50π]`: `h ≥ 0` and `cos > 0`.
  - On `[50π, ∞)`: `h ≥ −0.6861 + ¼log(1 + 4(50π)²/25) = 1.384 > 1 ≥ |cos|`.
  - By Bochner–Schwartz, `T` is positive definite. ∎ (Only elementary constants are used: `γ`, `π`, `log 2`, `log π`, `e^{2.7444}`, `cos(0.0954)`.)
- **What it shows.**
  - Over signed measures on `(1,∞)` the Weil cone of ζ's archimedean datum has **nonempty interior**. Positivity is produced by just two things: the pole density (Lebesgue), and one negative correction near `x = 1` paying for the low-frequency deficit `h(0) = −0.686` of Γ_ℝ.
  - For Λ the same deficit is paid by the **gap `[1,2)`** (no primes below 2): a continuous deficit of mass `∫_0^{log 2} e^{u/2}du = 2(√2−1) = 0.83 > 0.686`. With nonnegative weights a gap of at least `x < 1.80` is forced (`2(√X₀−1) ≥ 0.686`).
  - So **the entire RH content of W ≠ ∅ (PBAP) is the integrality of the support, `log ℕ`, together with the sign `lam ≥ 0` (L123)**. Existence over ℝ is trivial and explicit.
- **Why integrality is the obstruction (dichotomy, heuristic + partial proofs).**
  - (a) *Lattice resonance.* Mean-1 weights on all integers give `H ≈ ζ(s) − 1/(s−1)` plus fluctuation. The Euler-product large values of `ζ(½+it)`, `≥ exp(c√(log t/loglog t))`, eventually exceed `h(t) ∼ ½log t` (resonance kill, L107).
  - (b) *Granularity threshold.* Mass density 1 carried by atoms of spacing `κ` with generic (non-resonant) positions has on the line a Gaussian-like fluctuation of variance `≍ κ log t`, and the sup over `[T,2T]` is `≈ √(2κ)·log T`. Staying below `h ∼ ½log T` requires **`κ < 1/8`**. Integers have `κ = 1`: eight times too coarse for "generic" positivity.
  - (c) *Logarithmic structure.* Prime-supported weights `≈ log p` avoid (a) through the Euler product, but their mean structure is `−ζ'/ζ`, with poles at the zeros. Removing the zeros on primes needs corrections `Σ_ρ p^{ρ−1}`, which diverge at the primes by Landau's formula. So no finite correction and no convergent limit exists; finite cutoffs remove only finitely many zeros. Second-order poles sit at `ρ+ρ'−1`, on `Re s = β+β'−1`.
  - **Conjecture L131′ (integrality dichotomy).** Every integer-supported, box-bounded `lam` is either resonant (`sup_{t≤T} Re H_lam(½+it) ≥ (½+c)log T` along a sequence) or carries a singular spectrum on the zeros of an L-function with Γ_ℝ-datum and conductor 1, i.e. on the zeros of ζ. Consequently `W ⊆ {Λ}`, and PBAP ⟺ RH.
- **Verdict:** THEOREM (explicit producer over ℝ, coercive). REDUCTION: the producer over ℤ is the integrality problem, quantified by the granularity threshold `κ < 1/8` versus the unit spacing of ℕ.
- **L82 installed in Lean (2026-09-29, after "restart lean").** Module `RHTower/CriticalPolynomialZetaSignRigidity`, wired into `RHTower.lean` after `ZetaConvexityBound`. Contents:
  - `tendsto_twisted_zeta_first_moment`: the Cesàro limit of `ζ(½+iy)e^{iκy}` for every real `κ`;
  - `critDirPoly_eq_zero_of_re_mul_conj_zeta_nonpos`: `Re(E·conj ζ) ≤ 0` on the critical line forces `E = 0`.
  - Axioms `[propext, Classical.choice, Quot.sound]`; `lake build` of the module passes.
  - Renamed to avoid collisions: `twistedZeta → expTwistedZeta`, and `continuous_riemannZeta_critical → continuous_riemannZeta_criticalLine`. The corpus's `ZetaTwistedFirstMomentContour` owns the quantitative rational-twist version.
- **L131 Lean (2026-09-29).** Module `RHTower/LebesgueAtomArchimedeanWeilDensity`, wired after `DigammaTwoSided`; axioms `[propext, Classical.choice, Quot.sound]`, and the module build passes.
  - `half_digamma_add_inv_criticalLine`: `½ψ(s/2) + 1/s = ½ψ(s/2+1)` on the critical line (the `s = 0` cancellation).
  - `lebesgueAtomWeilDensity_ge` / `thetaDeriv_add_pole_add_atom_ge`: `θ'(t) + Re(1/(½+it)) + cos(t/10⁴) ≥ 1/200` for all real `t`.
  - The Lean version uses the atom `e^{1/20000}δ_{e^{1/10000}}`. That leaves room for crude certified constants (`ψ(5/4) ≥ −3/5`, `log π < 23/20`, `log 2400 ≥ 4`); the paper version with `e^{1/100}` has margin `0.309`.
  - The step from positive density to positive definiteness of `T_{lam₀}` is Plancherel plus Bochner–Schwartz (paper). The Lean theorem is the density statement.
  - Correction to the L131 text: the coercivity reads `W_{lam₀}(h⋆h̃*) = (1/2π)∫|ĥ|²μ ≥ c·(1/2π)∫|ĥ|²`, with `c = 0.618` (paper) or `c = 1/100` (Lean constants).

### L132 — Can Λ's atoms be smeared into an integer-supported pole-free producer? The Landau–PD squeeze. CONJECTURE → obstruction (semi-rigorous) + two exact lemmas
- **Conjecture L132 (tested).** Under RH, a pole-free integer-supported producer exists: take Λ and smear each atom `πδ_γ` into a positive bump, using prime-supported corrections `w(p) = −log p·Σ_ρ p^{ρ−1}c_γ(log p)`, where `c_γ(ℓ)` is a taper rising from 0 to 1 in `ℓ = log p`. If true, uniqueness would fail under RH, and E-107 could never be refuted unconditionally.
- **Exact bookkeeping (first order, PNT part).** Zero `γ` is replaced, on the line, by the atom `πδ` minus the cosine transform `C_γ(v) = ∫_0^∞ (1−c_γ(ℓ))cos(vℓ)dℓ`, with `v = t−γ` and total mass `π`. So the absolutely continuous Weil density of `b = Λ − w` is `Σ_γ C_γ(t−γ)` plus higher-order terms. Mass conservation (L107) is automatic.
- **Lemma A (PD doubling, exact).** For `C_γ ≥ 0` the profile `f = 1 − c_γ` must be positive definite. A normalized positive-definite `f` satisfies `1 − f(2x) ≤ 4(1 − f(x))`. So a taper reaching `c(ℓ₀) ≈ 1` has `c_γ(ℓ) ≥ ¼(ℓ/ℓ₀)²` on `[0, ℓ₀]`.
  - A flat-top profile is impossible: a PD function equal to `f(0)` near 0 is constant.
  - Hence every positive smearing of zero `γ` corrects **all** primes `p ≤ e^{ℓ₀(γ)}`, by at least `(log p/ℓ₀(γ))²/4`.
- **Lemma B (Landau divergence, exact).** At a prime `p`, `Σ_{0<γ≤T} p^{iγ} = −(T/2π)log p/√p + O(log T)`. Partial summation gives `Σ_γ p^{iγ}(log p/ℓ₀(γ))² = −∞·sign` whenever `ℓ₀(γ) ≲ C log γ`, since `∫dT/log²T = ∞`. So **wide smearing** (bump width `≍ 1/ℓ₀ ≳` zero spacing) makes the corrections diverge at every prime: no integer-supported `b` exists.
- **Narrow smearing fails positivity.** For reach `ℓ₀(γ) ≫ √γ` (e.g. `c_γ = 1 − e^{−(ℓ/γ)²}`) the corrections converge absolutely: `|w(p)| ≲ log³p·p^{−½}Σ1/γ²`. But the bumps are Gaussians of width `1/γ`, far below the zero spacing `2π/log γ`.
  - Between zeros the density is then carried only by the remaining terms: the PNT-error part `≲ |t−γ|e^{−c√γ}`, and the conditionally convergent phase sum `Σ_γ ±1/|t−γ|` of size `O(√log t)`.
  - Mass conservation forces these to have mean 0, so they are **negative on a set of positive density**, and `b ∉ W`.
- **The squeeze.** Positive smearing wide enough to fill the gaps between zeros forces corrections at small primes that Landau's spikes make diverge. Smearing narrow enough to converge leaves mean-zero gaps. No intermediate reach escapes both: the fill condition needs width `≳ 2π/log γ`, i.e. `ℓ₀ ≲ (log γ)/2π`, which is inside the Landau-divergent regime.
- **Side result (exact, small).** The prime-gap system `λ_gap(p_n) = p_n − p_{n−1}` (L108) is integer-supported, nonnegative and pole-free **across** the critical line, unconditionally.
  - `H = 1 + s∫E x^{−s−1}` with `|E| ≤ 1 + g(x)`.
  - Heath-Brown's `Σ_{p_n≤x} g_n² ≪ x^{23/18+ε}` makes `∫|E|x^{−σ−1} < ∞` for `σ > 5/18`.
  - Its Weil positivity is decided by constant-level large deviations of `Σ_p (g_p − log p)p^{−½−it}` (variance `≈ ¼log²t`, since `Var g ≈ log²p`). That is the `α ≥ 1` barrier again; the fluctuation heuristic predicts failure.
- **Verdict:** the zero-smearing route to a second (pole-free) producer is **blocked** by the Landau–PD squeeze. Lemmas A and B are exact; the gap-negativity step is heuristic. This supports the integrality dichotomy L131′ even under RH. Λ's atoms cannot be smeared into integer-supported positive spectrum, because the primes "remember" every zero, and that memory is Landau's formula.

### L133 — The independence–amplification tradeoff: why integer supports sit exactly at Λ's boundary. STRUCTURAL LAW [P, with heuristic large-deviation inputs]
- **Setting.** Integer-supported producers are an infinite LP in real weights on fixed positions `log n` (integrality is of positions, not values). The constraint is `Re H_lam(½+it) ≤ h(t) ∼ ½log t` for all `t`. Two properties of the positions decide feasibility.
- **(a) Multiplicative dependence ⇒ amplification.** If `supp lam` carries a positive proportion of the mass on a multiplicatively closed or dense set (all integers, squarefree, `y`-rough numbers with `y(n) = n^{o(1)}`), the mean part of `D_lam` is `ζ(s)×`(Euler factors), and `log|ζ|` fluctuates on the line like a Gaussian of variance `½loglog t` (Selberg).
  - Removing small primes does not help. The variance is spread over **all** primes up to `t`: `Σ_{y<p≤t}1/(2p) = ½log(log t/log y)`.
  - Hence `max_{t≤T}|mean part| ≥ exp(c√(log T/loglog T))` (resonance, rigorous when `y ≤ log T`), eventually far above `½log T`.
- **(b) Multiplicative independence ⇒ variance at the cap.** A set with ℚ-linearly independent `log n` has at most `π(x)` elements up to `x` (dimension count). Density 1 then forces weights `≳ log n`, and diagonal (`α < 1`) variance `V ≥ ¼·mean(c²)·log²T`. That is a standard deviation `≥ ½log T`, **equal to the cap** (L128 with Poisson `a → 0`).
  - A variable `X ≤ M` with mean 0 and `Var ≥ M²` must be nearly two-point: pinned at the cap most of the time, with rare deep negative excursions. For the Weil density `Y = M − X ≥ 0` this means coefficient of variation `≥ 1` at scale `1/log T`.
  - Λ realizes the extreme exactly: `Y` is atomic (the zeros), and the FE pins the absolutely continuous part at the cap.
  - A pole-free prime-supported producer would need an absolutely continuous `Y` with `CV ≥ 1` at every scale `a/log T`, together with the one-sided cap. This is not contradictory at second order (two-point or exponential-type densities are allowed), so **no kill**. It is exactly the regime where only exact arithmetic (an FE) has been seen to work.
- **Law (statement).** For integer supports, either the positions are dependent (amplification by `exp(√log T)`-type large values, killed), or independent (standard deviation `≥` the cap, forcing maximal burstiness).
  - Λ is the unique known system at the boundary, and it sits there with equality.
  - Discrepancy-theoretic constructions do not apply: the weights are real, and partial-coloring bounds concern rounding, not the LP itself.
- **Verdict:** STRUCTURAL LAW. It unifies L107, L108, L109, L128 and L132: the integer-support producer problem is a **constant-level extremal problem**, and Λ is its only known exact solution.

### L134 — The fattening bridge from ℝ to ℤ: producers on `δ`-fattened integers, and why `δ → 0` is Poisson self-duality. CONSTRUCTION [P-sketch] + threshold law [heuristic constants]
- **Conjecture L134.** Between L131 (support ℝ, explicit producer) and ℤ (open) lies the family `S_δ = ∪_n [n−δ, n+δ]`. Producers on `S_δ` should exist for every `δ > 0`, and their `δ → 0` behaviour should locate the integrality obstruction exactly.
- **Mechanism (exact up to stationary-phase error terms).** Take `lam_δ = Σ_{n≥2} ρ_δ(x−n)dx`, with `ρ_δ` a smooth even unit bump on `[−δ,δ]`, together with L131's negative atom placed in `[1−δ, 1+δ]`.
  - Poisson summation gives `Σ_n ρ_δ(x−n) = 1 + Σ_{k≠0} ρ̂(δk)e^{2πikx}`.
  - The `k = 0` term is Lebesgue: exactly L131's pole-cancelling part.
  - The `k`-th term contributes `∫x^{−s}e^{2πikx}dx`. On the line this has a stationary point at `x = t/2πk` and size `≍ k^{−½}`. So `H_δ(½+it) = H_{lam₀} + Σ_{0<|k|≲1/δ} c_k(t)k^{−½}e^{iφ_k(t)}`, a **dual ζ-partial sum of length `≍ 1/δ`** (the approximate functional equation in disguise).
- **Consequences.**
  - (i) `|Re H_δ − Re H_{lam₀}| ≤ Σ_{k≲1/δ}k^{−½} ≍ 2δ^{−½}`, uniformly in `t`. Positivity is therefore automatic for `½log t ≥ C δ^{−½}`, i.e. above height `e^{2Cδ^{−½}}`.
  - (ii) Below that height, the dual sum's large values decide. Full Kronecker alignment of `k ≤ 1/δ` (value `2δ^{−½}`) happens only at heights `≥ e^{c/δ}`, where `h ≫ δ^{−½}`, so it is harmless. But resonance at heights `T = e^L` with `L ≲ 1/δ` gives `exp(c√(L/log L))`, which beats `½L` once `L ≥ L₀`.
  - Hence (heuristic threshold) **a fattening threshold `δ₀ ≍ 1/L₀ > 0`**: density-1 systems on `S_δ` are Weil-positive for `δ ≥ δ₀`, and fail by dual-sum resonance for `δ < δ₀`.
- **Reading: why the limit `δ → 0` is ζ.** Fattening in `x` is truncation in the Poisson-dual variable. As `δ → 0` the dual sum becomes ζ's own reflected sum, because **ℤ is Poisson self-dual**, the same fact that gives ζ its functional equation.
  - On integer support, a density system therefore sees ζ twice: directly (the lattice sum) and through its dual. Resonance on either side kills positivity.
  - Λ escapes resonance by passing to the logarithmic derivative (independent positions, L133). It pays with atoms at the zeros, and its positivity is RH.
- **Why the fattened producers do not converge to an integer producer.** They are uniformly bounded, but their margins degenerate like `−exp(c√(L/log L)) + ½L` in the window `L ≲ 1/δ`. Any weak limit is the `u ≡ 1` system, which is killed by resonance.
  - PBAP needs a **different** family, one whose dual sums have no resonance: prime-like weights, where the dual is `−ζ'/ζ`'s explicit formula, i.e. the zeros.
- **Verdict:** CONSTRUCTION + threshold law. There is a quantitative bridge `ℝ → ℤ`. The integrality obstruction is Poisson self-duality of ℤ (resonance on the dual side), and the only escape is the logarithmic (prime) family, which returns to the zeros. This consistently supports "producer over ℤ ⟺ RH".

### L135 — Nonnegative producers: the low-frequency LP rediscovers Λ(2), and tapered Λ is exactly "RH at scale 1/L". EXPLORATION [P-sketch] + exact identity
- **Question.** L131's producer is signed (one negative atom). Does a **nonnegative** real-supported producer exist? That would isolate integrality, not sign, as the obstruction.
- **Gap-only systems fail.** Let `lam = 1_{x>e^a}dx` with deficit `ν = e^{u/2}1_{[0,a]}du` in log coordinates, so `C(t) = F_a(t) = [½(e^{a/2}cos at − 1) + t e^{a/2}sin at]/(¼+t²)`. Positivity is `C ≥ −h`.
  - `a = 0.9`: margins `+0.36` (`t=1`) and `+0.10` (`t=2`), but deficits `−0.23, −0.44, −0.42, −0.21` at `t = 3, 4, 5, 6`.
  - `a = log 3`: deficits at `t = 2, 4, 5`. Consistent with L131 (X₀ = 2 fails near `t ≈ 3`).
- **The one-atom LP points at Λ(2).** For `a = 0.9`, the deficit window `t ∈ [3,6]` is best repaired by one positive atom whose cosine is `−1` at `t ≈ 4.5`, i.e. at `u₁ = π/4.5 = 0.698 ≈ log 2`.
  - The budget constraints (`t = 0`: `m ≤ 0.451`; `t = 3, 4`: `m ≥ 0.46, 0.47`) pin the atom weight to `w = m√2 ≈ 0.65–0.67`, against `Λ(2) = log 2 = 0.693`.
  - With the gap `[1,3)` and one atom, a second deficit at `t ≈ 9` forces more atoms. The LP is "asking for" the next primes.
  - **Observation:** the low-frequency Weil constraints on a nonnegative system with a gap below 2 select, to within about 5%, an atom of mass `log 2` at `x = 2`. The positivity constraints alone start to reconstruct Λ's first prime.
- **Tapered Λ plus Lebesgue complement (exact identity).** Let `τ(ℓ) = (1−ℓ/L)⁺` and `lam_L = Λ(n)τ(log n) + (1 − τ(log x))dx`. Then
  `μ_L/2 = [h − F_L⋆h](t) + Σ_ρ Re τ̂(s−ρ)|_{s=½+it} + (small)`,
  where `F_L` is the Fejér kernel and `τ̂(z) = ∫_0^L(1−ℓ/L)e^{−zℓ}dℓ`.
  - For critical `ρ`: `Re τ̂ = πF_L(t−γ) ≥ 0`, and the atoms are smeared positively.
  - For off-line `ρ`: the profile is `(1−ℓ/L)e^{(β−½)ℓ}`, which stays convex-decreasing (hence gives a positive kernel) iff `(β−½)L ≲ 1`. Otherwise its contribution is sign-indefinite and of size `e^{(β−½)L}`, **at every height**.
  - Low frequency: `h` is convex at 0 (`h''(0) = −⅛Re ψ''(5/4) ≈ 0.165`) and minimal there. So `h − F_L⋆h < 0` near `t = 0`, of size about `−0.85/L`. The zero part there is only `(4/πL)Σ1/γ² ≈ 0.03/L`, i.e. λ₁-sized slack. An `O(1/L)` nonnegative correction near `x = 1` is needed; this is a rescaled, `L`-independent LP.
- **Conclusion.** Nonnegative real producers of the form "tapered Λ plus complement" exist iff (i) the rescaled low-frequency LP is feasible (plausible: it is the gap-plus-small-primes problem above) and (ii) all zeros lie within `≍ 1/L` of the critical line at **all heights**, i.e. quasi-RH at scale `1/L`.
  - The integer-supported producer (`L → ∞`) therefore needs RH itself. The sign obstruction (nonnegativity) is **not** the hard part: the low-frequency LP pushes toward Λ's small primes.
- **Verdict:** EXPLORATION. The positivity constraints select Λ's first prime. The tapered family ties integer-supported existence to `(β−½)L ≲ 1`. This is consistent with the equivalence "producer over ℤ ⟺ RH", and with L131: over ℝ with signs, existence is free.

### L136 — Lean: algebraic core of finite-type uniqueness installed; a Bohr-recurrence constraint on "partial zeta functions" (L129 iv). [Lean] + LEMMA [P]
- **Lean.** Module `RHTower/FiniteTypeDiscreteMomentAlgebra`: the derivative functional equation `ζ'(1−ρ) = −A(ρ)ζ'(ρ)` at zeros, the L103 moment identity, and the maximal-support nondegeneracy of `B(E,·)`. Wired into `RHTower.lean`; standard axioms.
- **Lemma (partial zeta functions must be ζ-sized).** Suppose Λ is not extreme in `W` under RH (L129) and the residues are integers. Then there is a Dirichlet series `G = exp(−∫D_w)`, zero-free and pole-free on `σ > ½` and holomorphic and nonzero at `s = 1`, whose divisor in the strip lies on ζ's critical zeros. Two consequences:
  - `G` cannot be written as `ζ^k·H` (`k ≠ 0`) with `H` absolutely convergent on `σ > 1−δ`. `H` would need a zero of order `k` at `s = 1`. By Bohr's uniform almost periodicity on `σ ∈ [1−δ/2, 1+δ]` and Rouché, `H` then has zeros near `1 + it_j` for a relatively dense set of `t_j`, i.e. zeros in `σ > ½` off the critical line.
  - The same argument excludes `G = P·(anything absolutely convergent near σ = 1)` for any Dirichlet polynomial `P` with a zero in `σ > ½`. So every candidate `G` has `log G` **not** absolutely convergent near `σ = 1`: its prime coefficients are of PNT size, exactly like `log ζ`.
- **Reading.** A second crystalline structure on the zeta zeros, if it exists, is "ζ-sized" at the level of primes. It cannot be built from ζ by absolutely convergent factors. This is consistent with the deficit law (`≫ T` modifications) and with L133 (prime-level variance at the cap).

### L137 — Lean: the independence dimension bound behind L133(b). [Lean]
- Module `RHTower/IndependentLogSupportDimension`, wired; standard axioms.
  - `card_le_primesUpToFinset_of_linearIndependent_log`: integers in `[1,x]` with `ℚ`-independent logarithms number at most `π(x)`.
  - `sq_sum_le_card_primesUpToFinset_mul_sum_sq`: `(Σ_S λ)² ≤ π(x)·Σ_S λ²`.
- With the prime number theorem this gives square mass `≳ x log x` for density-one systems on independent supports. Hence diagonal variance `≳ ¼log²T`, whose square root equals the archimedean cap `½log T`. This is the rigorous half of the independence–amplification law. The amplification half (resonance for dependent supports) is Soundararajan's method, from the literature.

### L138 — PBAP as a statement about the values of ζ (not its zeros), and the resonance–orthogonality mechanism. REFORMULATION [P] + mechanism
- **Exact reformulation.** On the prime-blind cone (`Φ(±log n) = 0`, `2 ≤ n ≤ e^A`), every integer-supported system gives the same Weil form. Take `u ≡ 1` (`D_u = ζ − 1`, pole-free), whose Weil density is `μ_u/2 = θ'(t) + 1 − Re ζ(½+it)`. Then:
  **PBAP ⟺ for all `A` and all `h` supported in `[−A/2, A/2]` with `∫|ĥ(t)|² n^{it} dt = 0` (`2 ≤ n ≤ e^A`): `∫|ĥ(t)|² (θ'(t) + 1 − Re ζ(½+it)) dt ≥ 0`.**
  - This is a zeros-free statement about the **values** of ζ on the critical line, tested against nonnegative Paley–Wiener densities that are orthogonal to the first `e^A` integer characters.
  - `V(t) = θ' + 1 − Re ζ(½+it)` is negative at low height (`V(0) = θ'(0) + 1 − ζ(½) = −0.226`) and at the resonance points where `Re ζ(½+it) > θ'(t) + 1`.
- **Mechanism.** Resonance points of `ζ(½+it)` are where `n^{it} ≈ 1` for many small `n`. A density `|ĥ|²` orthogonal to `n^{±it}` cannot put its mass near such points, since `∫|ĥ|²n^{it} ≈ n^{it₀}∫|ĥ|² ≠ 0`. It cannot concentrate near `t = 0` either (the Nyquist spreading of L85).
  - So **the prime-blind constraint is precisely an anti-resonance constraint**: it forbids the test densities from seeing ζ's large values. PBAP asserts that this anti-resonance suffices.
- **Krein form of the finite levels.** `PBAP_A` ⟺ there is a Weil-positive system that is integer-supported (real weights) on `[1, e^A]` and **arbitrary** (real-supported, signed) on `(e^A, ∞)`. The level-`A` form does not see beyond `e^A`, and the Krein extension supplies the rest.
  - L131 gives the unconstrained version: Lebesgue minus one atom.
  - L134/L135 show the integer segment `[1, e^A]` must carry Λ-like weights. With `u ≡ 1` there, dual-sum resonance kills positivity once `e^A` is large. With tapered Λ there, positivity needs zeros within `≍ 1/A` of the line at all heights.
  - The corpus height reduction (`zeta_re_W_ge_of_depth_below_horizon`, `log H ≤ 7000e^a`) gives only the relaxed bound `W ≥ −2∫|f|²` from finite RH verification, not positivity.
- **Status.** PBAP is RH-strength under the uniqueness conjecture. It is now phrased as: *do the values of ζ on the critical line satisfy a weak positivity against integer-blind Paley–Wiener densities?* This formulation is new in this programme. It invites an anti-resonance proof (large-values and small-values estimates for ζ, restricted to measures orthogonal to integer characters) rather than a zero-location proof.
- **L138 follow-up: the AFE bandwidth lemma (anti-resonance at high heights) [P-sketch].** Use the smooth approximate functional equation `ζ(½+it) = Σ_n n^{−½−it}W(n/√(t/2π)) + χΣ_m m^{−½+it}W(m/√(t/2π))`. Against a prime-blind density `|ĥ|²` of type `A` (Fourier support in `[−A,A]`), with `X = e^A`:
  - Direct terms with `n ≤ X` are killed by orthogonality once `W ≡ 1`, i.e. at `t ≥ 2πC²X²`.
  - Direct terms with `n > X` have frequency `log n > A` and are killed by bandwidth.
  - Reflected terms have frequency `log(t/2πm) ≥ ½log(t/2π) > A` for `t > 2πX²`, and are killed by bandwidth.
  - Only the `n = 1` term survives, and it cancels the `+1`. **So above the Nyquist height `2πC²e^{2A}`, the tested density is `θ'(t) > 0`, up to stationary-phase edge terms.**
  - PBAP_A is therefore a statement about the heights `t ≲ 2πe^{2A}` only. There the weights `W` vary, the reflected terms become visible, and the zeros below the Nyquist height enter.
  - This rederives L85's Nyquist localization in the language of values. Anti-resonance settles every height above Nyquist for free; the part below Nyquist is exactly the RH content (L70/L79/L85: RH ⟺ PBAP under uniqueness).
- **L138 self-audit (next cycle, immediately).** Take `N = X` in the AFE. The term `X^{1−s}/(s−1)` is **not** bandwidth-killed: `1/(−½+it)` has one-sided exponential Fourier transform, and its pairing with `ν = |ĥ|²` equals `∫ν̂(x)e^{x/2}dx`, independent of `X`. That is exactly the pole term.
  - So the values formulation reduces, after anti-resonance kills the direct and reflected sums, to `∫νθ' + pole(ν) = arch + pole` on the prime-blind cone. This is **tautologically** the original PBAP.
  - The anti-resonance mechanism is real, but it removes exactly the non-archimedean parts and adds no leverage. The low-height/Nyquist content (arch + pole against prime-blind densities concentrated below `2πe^{2A}`) is PBAP itself.
  - **Verdict for L138: REFORMULATION, no new leverage (circular at the last step).** Recorded to prevent reuse as a proof route.

### L139 — Second crystalline structures satisfy a Γ-free multiplicative functional equation; one-prime rigidity; singular-inner near-misses. THEOREM [P] (reduction) + partial rigidity
- **Setting (from L129, under RH).** Λ is not extreme in `W` iff there is a nonzero integer-supported `w` whose Dirichlet series is pure-atomic: `D_w = Σ_crit r_ρ[1/(s−ρ) + 1/ρ] + b`, with `|r_ρ| ≤ m_ρ` and no absolutely continuous boundary part. For integer residues put `G := exp(−∫D_w)`, a Dirichlet series with `G → 1` as `σ → ∞`.
- **Theorem L139 (degree-0 multiplicative FE).** For such a `G` (normalized, `G* (s) := conj G(s̄)`), `G(s)·G*(1−s) ≡ C` (a constant).
  - *Proof.* Pure-atomic boundary means `Re(G'/G)(½+it) = 0` off the atoms. The function `H(s) = (G'/G)(s) + conj((G'/G)(1−s̄))` is meromorphic near the line. It has zero real part there… more precisely `H = (G'/G)(s) + (G*'/G*)(1−s)·(−1)` vanishes on `σ = ½`. By the identity theorem `H ≡ 0`, so `d/ds log(G(s)G*(1−s)) = 0`. ∎
  - Consequences:
    - `G` continues to `σ < ½` as `C/G*(1−s)`.
    - All zeros and poles of `G` lie on the line.
    - The net divisor count is `O(log T)` (argument principle with the FE), so there is no density drift, as in L129.
- **Bohr-lift reading.** In Bohr variables `z_p = p^{−s}` the FE says `|G| = √C` on the critical torus `|z_p| = p^{−½}`: `G` is an **inner function** of the polydisk with radii `p^{−½}`, and its divisor sits on the distinguished boundary.
- **One-prime rigidity (exact).** If `G` involves a single base `n₀` (a function of `z = n₀^{−s}`), then `G` is meromorphic in `z` and unimodular (up to `√C`) on `|z| = n₀^{−½}`. Its zeros and poles lie on that circle, since `σ = ½ ⟺ |z| = n₀^{−½}`.
  - A meromorphic unimodular function with divisor on the circle is a finite Blaschke quotient whose zeros and poles coincide pairwise, so it is constant.
  - Hence `G ≡ 1` and `w = 0`. Single-prime-power "partial zetas" do not exist.
- **Near-miss (why the simple-pole constraint matters).** Singular inner functions such as `G = exp(−(1+z/r)/(1−z/r))`, with `z = 2^{−s}` and `r = 2^{−½}`, are Dirichlet series satisfying `G(s)G*(1−s) = 1`, zero-free on `σ ≠ ½`. They have essential singularities at `s = ½ + 2πik/log 2`, not at zeta zeros, and `D_w = −G'/G` has **double** poles there. Input (B) (boundary poles simple, with real residue) excludes them.
  - So the Weil-positivity dictionary is what separates "partial zeta functions" from generic inner functions.
- **Open core (exact).** Many primes: is every inner function of the `p^{−½}`-polydisk that is a Dirichlet series, with divisor on the critical torus's diagonal slice at ζ's ordinates and only simple boundary singularities, constant? A positive answer is L105/L129 crystalline rigidity, i.e. extremality of Λ in `W` under RH.
- **Verdict:** REDUCTION to multivariable inner-function rigidity (new). Proved in the one-prime case. This is the first place where Weil positivity (via simplicity of boundary poles) is used as an inner-function condition.

### L140 — Λ is an extreme point of the Weil cone: two-sided perturbations are killed by Hamburger's theorem. THEOREM [P]
- **Correction to L139.** The identity-theorem step gives a **linear** relation, not a multiplicative one. From `Re D_w(½+it) = 0` (absolutely continuous part), `K(s) = D_w(s) + D_w(1−s)` has zero real part on the line and is real-symmetric, so `D_w(s) + D_w(1−s) ≡ κ` (a constant). `G = exp(−∫D_w)` then satisfies `G(s) = C·G*(1−s)`. The one-prime Blaschke discussion stands; the reduction below supersedes it.
- **Theorem L140.** Let `w` be real, supported on `n ≥ 2`, with `Σ|w(n)|n^{−σ} < ∞` for `σ > 1`. If `Λ + w` and `Λ − w` are both Weil-positive for ζ's archimedean datum, then `w = 0`. Hence Λ, whenever it lies in `W` (⟺ RH), is an **extreme point** of the Weil cone. This settles L129: the pure-atomic crystalline rigidity holds, for arbitrary real residues.
- **Proof.**
  1. Convexity gives `Λ ∈ W`, so RH holds. Then `μ_Λ/2 = πΣ m_ρ δ_γ` (atoms only), and `D_w = ±(Φ_Λ − Φ_{Λ±w})` is holomorphic on `σ > ½` (differences of Herglotz functions).
  2. `μ_{Λ±w}/2 = μ_Λ/2 ∓ Re D_w ≥ 0` for both signs. So the boundary measure of `Re D_w` is atomic, supported on the critical ordinates, with atoms `πr_ρ`, `|r_ρ| ≤ m_ρ`. By input (B) the boundary poles are simple with real residues.
  3. Mittag-Leffler plus reflection: `S(s) = Σ_ρ r_ρ[1/(s−ρ) + 1/ρ]` converges, and `E = D_w − S` is holomorphic on `σ > ½` with constant boundary real part. By Schwarz reflection (distributional boundary values, polynomial growth from Paley–Wiener–Schwartz bounds), `E` is entire and `D_w` is meromorphic on ℂ with poles only at critical zeros. The residues pair as `r_ρ = r_ρ̄` (w real), which gives `D_w(s) + D_w(1−s) = κ`.
  4. Put `F := ζ(s)·(D_w(s) − κ/2)`. This is a Dirichlet series (coefficients `1⋆w − (κ/2)δ₁`), absolutely convergent on `σ > 1`. `(s−1)F` is entire, since the poles of `D_w` at zeros of ζ are cancelled because `|r_ρ| ≤ m_ρ`. It has finite order. By `ζ(1−s) = χ(1−s)ζ(s)` and `D_w(1−s) − κ/2 = −(D_w(s) − κ/2)`:
     `Γ_ℝ(s)F(s) = Γ_ℝ(1−s)·(−F)(1−s)`.
  5. **Hamburger's theorem** (with `f = F`, `g = −F`) gives `F = g = cζ`, hence `F = −F`, `F ≡ 0`, and `D_w ≡ κ/2`. Since `w(1) = 0`, `κ = 0` and `w = 0`. ∎
- **What is new.** Weil positivity from both sides forces the perturbation's Dirichlet series to have zero absolutely continuous boundary part. That yields an *odd* Riemann-type functional equation for `ζ·(D_w − κ/2)`, and Hamburger kills odd solutions.
  - The poles on the line, which block the corpus's earlier "FE rigidity at `x^{½}`" (xi.md: it assumes `∫x^{−(½−δ)}d|ν| < ∞`), are absorbed by multiplying by ζ, whose zeros are exactly where the poles sit (`|r_ρ| ≤ m_ρ`).
- **Limits.** One-sided perturbations (`Λ + εw ∈ W` only for `ε > 0`) leave an absolutely continuous part `ν ≥ 0`, so there is no functional equation and Hamburger does not apply. Λ is extreme, but not yet known to be isolated or unique. The remaining uniqueness core: every `lam ∈ W ∖ {Λ}` must lie in a direction along which `W` extends only one-sidedly from Λ. By the deficit law such a direction has `R⁺ ≫ T`.
- **Producer reading.** Among Weil-positive systems, Λ admits no symmetric deformation. The "producer" is rigid in the strongest two-sided sense, and its rigidity is Hamburger's (FE + Dirichlet series).

### L141 — The one-sided uniqueness core is "Hamburger with a nonnegative defect". REDUCTION [P]
- **Setting.** Assume RH. Let `lam ∈ W` and `w = lam − Λ`. Then `[Λ, lam] ⊂ W`, and `μ_{Λ+εw} ≥ 0` for `ε ∈ [0,1]` gives the boundary measure
  `Re D_w = πΣ r_ρδ_γ − ν`, with `r_ρ ≤ m_ρ` and `ν ≥ 0` even (w real).
  - `ν` is the part of `μ_lam/2` off the zero set; by the deficit law its mass is `≍` the atom deficit.
  - With `S = Σ r_ρ[1/(s−ρ) + 1/ρ]` and `C_ν(s) = (1/π)∫dν(u)/(s−½−iu)` (Cauchy transform), `D_w = S − C_ν + const` on `σ > ½`.
- **Key identity (exact).** `C_ν(s) + C_ν(1−s) = (1/π)∫dν(u)[1/(s−½−iu) − 1/(s−½+iu)] = 0` for even `ν`. So `D̃ := S − C_ν` (defined on both sides of the line) satisfies `D̃(s) + D̃(1−s) = κ`: **the odd functional equation survives**. But `D̃` is only piecewise holomorphic, with jump `−2ν` across the critical line (Plemelj). It is the analytic continuation of `D_w` iff `ν = 0` locally.
- **Hamburger with defect.** `F := ζ·(D̃ − κ/2)` equals the Dirichlet series `ζ(D_w − κ/2)` (coefficients `1⋆w − (κ/2)δ₁`) on `σ > ½` and satisfies `Γ_ℝ(s)F(s) = −Γ_ℝ(1−s)F(1−s)` across the line. Its only non-analyticity is the jump `F(½+it+0) − F(½+it−0) = −2ζ(½+it)ν(t)`.
  - Running Hamburger's Mellin–theta argument, the contour shift across `σ = ½` picks up the jump. For `a_n = (1⋆w)(n) − (κ/2)δ_{n,1}`:
    `Σ_n a_n e^{−πn²x²} + x^{−1}Σ_n a_n e^{−πn²/x²} = P(x) + J_ν(x)`, with `J_ν(x) = 2x^{−½}∫_0^∞ R(t)ν(t)cos(t log x)dt`,
    where `R(t) = Γ_ℝ(½+it)ζ(½+it)` (real on the line, sign changes exactly at the zeros) and `P` collects the polar terms.
  - For `ν = 0` this is L140: odd Poisson symmetry with integer frequencies forces `a = 0`.
- **Exact uniqueness core.** Under RH, `W = {Λ}` iff the only nonnegative even measures `ν` (with the growth allowed by Herglotz) for which `J_ν + P` is an odd-symmetrized theta series with coefficients of the form `1⋆w`, `w` supported on `n ≥ 2`, are `ν = 0`.
  - The weight `R(t)` changes sign at every zero. The defect is therefore a **zero-modulated** positive measure, and the integrality of the theta frequencies must rule it out.
- **Why this is a genuine reformulation.** It moves the one-sided uniqueness problem from the Weil cone to a Poisson/theta identity with an explicit positive defect. Both Hamburger's rigidity (L140) and its failure mode are visible there: `ν` must "pay" for the odd symmetry through `R`.
- **Status.** OPEN. Next test: evaluate at `x = 1` (`Σ a_n e^{−πn²}·2 = P(1) + ∫R ν`) and at the fixed-point derivatives, looking for a sign contradiction from `ν ≥ 0` combined with the known signs of `R` at low height (`R(t) < 0` for `0 < t < 14.13`, since `ξ(½) < 0`… sign conventions to be fixed).

### L142 — Where Hamburger's periodicity argument breaks for one-sided defects. FAILURE ANALYSIS [P]
- **Test (conjecture).** Run Titchmarsh's proof of Hamburger's theorem (§2.13) on the defect identity of L141 and look for a sign contradiction from `ν ≥ 0`.
- **Laplace step.** Multiply the theta identity by `e^{−πt²x}` and integrate over `x > 0`. With `b_n = −a_n` (odd FE):
  `t·Σ_n a_n/(π(n²+t²)) + Σ_n a_n e^{−2πnt} = c + c'/t + t·L_ν(t)`,
  where `L_ν(t) = 2∫R(u)ν(u)Re[Γ(½+iu)(πt²)^{−½−iu}]du`, for `t > 0`.
  - For `ν = 0`, the right side is `i`-periodic (plus `c'/t`). So the poles of the left side at `t = ±in` must repeat periodically, which forces `a_n` constant. The odd sign then forces `a = 0` (L140).
- **Failure mode (exact).** `tL_ν(t)` does **not** continue to the imaginary axis, where those poles live.
  - At `t = iy`, `(πt²)^{−iu}` picks up `e^{±πu}`. With `|Γ(½+iu)| ≍ e^{−πu/2}` and `|R(u)| ≍ |ζ(½+iu)|·e^{−πu/4}·u^{−¼}`, the integrand grows like `e^{πu/4}ν(u)`.
  - `ν` has density `≍ log u` (mass conservation), so the integral diverges. The periodicity argument cannot compare residues.
  - **The positive defect lives exactly in the part of the identity that is invisible on the imaginary axis.**
- **Consequence.** One-sided uniqueness cannot follow from Hamburger's method alone. Any proof must use the decay of `ν`'s Mellin–Laplace transform, i.e. a quantitative constraint on how fast the absolutely continuous spectrum can be modulated. By L127/L133 this is again the `α ≥ 1` regime.
- **Verdict:** KILL of the direct extension. The survivor is L140 (two-sided extremality), which is exactly the case where `ν = 0` and the argument closes.
- **L142 Lean note.** The Hamburger formalization has started (card `hamburger-theorem-lean`). Its Laplace step, the `K_{1/2}` identity, is installed as `HTGeometry/LaplaceBesselHalfIntegral`.

## L143 (2026-09-29) — Hamburger's theorem formalized
- **Status.** Lean closure of the analytic input of L140.
  - The converse theorem for `ζ` (Hamburger 1921) and its odd-sign vanishing corollary are proved in Lean. Modules: `HTGeometry/{MellinGammaNegativeStrip, ConverseThetaRelation, DirichletCoefficientTheta, HamburgerLaplaceIdentity, HamburgerFunctionalEquation}`.
  - The contour step avoids residues by absorbing the poles into explicit functions (`e^{−πt}` on the right, `e^{−πt} − 1` on the left). The Mellin transform of `e^{−x} − 1` on `(−1, 0)` is `Γ`.
- **Producer status: unchanged.**
  - Integer-supported producers other than Λ must have their large boundary values carry negative real part, i.e. poles on the line with negative residue: "fake zeros".
  - Every candidate built from `ζ`'s values fails pointwise against the `½ log t` ceiling (large values of `ζ`).
- **Next target (Conjecture Ω, zero-atom case of Weil-cone uniqueness).** Let an integer Dirichlet series `A` have a simple pole at `s = 1` (residue 1) and continuous boundary values on `Re s = ½`. Then `ess sup_t [Re A(½+it) − ½ log(2+|t|)] = +∞`.
  - True heuristically for Euler products with `f(p) ≈ 1` (Selberg-type CLT on the line).
  - If true, every producer must carry atoms (fake zeros) on the critical line.

### L144 — The one-sided Hamburger defect does continue to the imaginary axis; L142's failure mechanism is corrected, and what remains is a tautology. CORRECTION [P] + KILL
- **Conjecture tested.** In the setting of L141 (RH, `lam = Λ + w ∈ W`, `F = ζ·D_w`, `a_F = 1⋆w`, `ν ≥ 0` the off-zero part of `−Re D_w^+`), Hamburger's residue comparison on the imaginary axis should force `ν = 0`.
- **Exact defect identity [P].** Shift the inverse Mellin contour of `Λ_F = Z·D_w` (with `Z = Γ_ℝζ`) to the critical line and add the reflected copy. The Hilbert-transform part of `D_w^+` cancels. The atoms at the zeros drop out because `Z(½+iγ) = 0`. This leaves
  `θ_F(x) + x^{−½}θ_F(1/x) = −(1/2π)∫Z(½+it)x^{−(½+it)/2}dν(t) + c₁(1 + x^{−½})`, with `c₁ = D_w(1)/2`.
- **Closed-form Laplace kernel [P].** Multiply by `e^{−πτ²x}` and integrate, using the Lean Laplace lemmas of L143. By the reflection formula `Γ(¼+it/2)Γ(¾−it/2) = π/sin(π(¼+it/2))`, all Γ-factors collapse:
  `L_F(τ) + E_F(τ) = J(τ) + c₁/(πτ) + c₁`, where `J(τ) = −(1/2π)∫ζ(½+it)τ^{−½+it}dν(t)/sin(π(¼+it/2))`.
  - Here `L_F` is the Hamburger series and `E_F(τ) = Σa_F(n)e^{−2πnτ}`.
  - Equivalently, `Γ_ℝ(s)Γ(1−s/2)π^{s/2−1} = 1/sin(πs/2)`.
- **Correction of L142.** On `τ = iy` we have `|τ^{it}| = e^{−πt/2}` and `|1/sin| ≍ 2e^{−π|t|/2}`. So the integrand of `J` is `≍ |ζ(½+it)|ν(t)` for `t < 0`, which is polynomial. It is **not** the exponential growth `e^{πu/4}ν(u)` that L142 used; L142 paired `Γ(½+iu)` with the wrong Laplace exponent.
  - `J` is holomorphic on `Re τ > 0`, and its boundary behaviour at `τ = in₀` is an Abel mean.
- **Defect mean-value law [P].** Compare the residues at `τ = in₀ + ε`, `ε → 0⁺`:
  - `L_F` has residue `a_F(n₀)/2π`;
  - `E_F` is `i`-periodic, so `E_F(in₀+ε) = E_F(ε) ~ D_w(1)/(2πε)`.
  - This gives, for every `n ≥ 1`:
  **`Abel-lim_{ε→0⁺} ε∫_0^∞ ζ(½+iT) n^{iT} e^{−εT} dν(T) = −((1⋆w)(n) + D_w(1))/(2√n)`.**
- **Kill: tautology.** Take `ν` equal to the absolutely continuous part of `−Re D_w^+` and use `∫_0^X ζ(½+iT)y^{iT}dT ~ X·[y∈ℕ]y^{−½}`. The law then holds identically.
  - Checked on Dirichlet polynomials: the two sides match term by term, `Σ_{m|n}w(m) + Σ_m w(m)/m`.
  - So Hamburger's machinery run with a defect reproduces the mean-value theorem for `ζ` against `ν`. It is consistent for every `ν` and carries no information beyond the definition of `ν`.
- **Verdict.** L142's KILL stands, with the corrected mechanism: the defect is not invisible on the axis; it is visible but vacuous. Survivors: the exact defect identity and the `1/sin` kernel.
- **Rediscovery audit.** The variance and skew mechanism I then re-derived (a one-sided ceiling caps the variance of a skew-free prime sum at `U²`; Λ is variance-critical) is L109/L111/L128. The backward-gap system `p_n − p_{n−1}` is L132's side result. Neither is new.

### L145 — Lean: L109's cap inequality. [Lean]
- `HTGeometry.mul_integral_sq_add_integral_cube_le`: if `f ≤ M` almost surely under a probability measure, then `M∫f² + ∫f³ ≤ M³ + M²∫f`. The proof is one line: integrate `(M−f)(M+f)² ≥ 0`.
- `HTGeometry.integral_sq_le_sq_of_skew_free`: a centred, skew-free `f ≤ M` has `∫f² ≤ M²`, with equality only for the law `±M`.
  - This is the exact inequality behind L109's `V ≤ U² − U·S₃/V`. Rearranged: `M·V ≤ M³ − S₃`, so `V ≤ M² − S₃/M`.
- Module `HTGeometry/SkewFreeVarianceCeiling`, wired. Axioms: propext, Classical.choice, Quot.sound.
- **Frontier (unchanged, re-confirmed).** Every open core (the existence of a pole-free producer, the one-sided uniqueness of L141, and Conjecture Ω of L143) needs mean values of prime sums at length `≳ T`, i.e. the `α ≥ 1` wall of L111/L117/L127.

### L146 — Bootstrap: can positivity of the full Weil measure control the off-diagonal terms of long prime sums? KILL [P] (circular; = L122)
- **Conjecture.** For `lam ∈ W`, `μ_lam ≥ 0` is a *full* positive measure, not only finite-level positivity. So `∫|P|²φ(t/T)dμ_lam ≥ 0` for Dirichlet polynomials `P` of length `N > T` should bound the off-diagonal prime-pair terms beyond `α = 1`.
- **Kill.** Expand `∫|P|²φ(·/T)dμ_lam = Σ_{m,n} a_m ā_n (μ̂_lam ⋆ Tφ̂(T·))(log m/n)`. This is exactly `W_lam(g⋆g̃*)` for the level-`log N` test `g = Σ a_n φ̌_T(·−log n)`.
  - So the inequality *is* Weil positivity at level `log N ≥ log T`, which is the membership hypothesis itself.
  - It yields no off-diagonal information beyond what `lam ∈ W` at that level already asserts. For Λ it is RH up to height `T^{O(1)}` (L85, L122).
  - There is no second positivity source. The Weil measure is the only positive object, and its positivity at level `A` is equivalent to its restriction to supports `≤ 2A`.
- **Side checks (also already in the log).**
  - Explicit left-shifted families `Λ(n)n^{−ε} + (1 − n^{−ε})` (the zeros moved left by `ε`, with the pole repaired by `ζ(s) − ζ(s+ε)`) are multiplicatively rich. The L107 resonance kill applies.
  - Stable-polynomial (Kurasov–Sarnak) crystalline measures with prime variables have spectrum in `±log ℕ` but constant density. They cannot carry the archimedean drift `½log t` or its negativity at `t = 0` (L1 note line 67, L10 line 689).
- **Verdict:** KILL (duplicate mechanism of L122). No new lever. Every route still meets the `α ≥ 1` wall.

### L147 — Lean: reflection-free odd Hamburger; L140's formal gap reduced to one boundary-regularity lemma. [Lean]
- New module `HTGeometry/HamburgerCriticalLine`, standard axioms, wired.
  - `critical_line_odd_theta_relation` shifts the theta series' inverse Mellin integral from `Re s = 3/2` onto the critical line. The two representations at `x` and `1/x` then only see `E(s) + E(1−s)`, which is the Mellin transform of the explicit `−β(t^{−½}(e^{−πt}−1) + (e^{−π/t}−1))`.
  - `coeff_eq_zero_of_critical_line_odd`: oddness across the line (a boundary condition) forces `f = 0`.
  - Also appended to `HamburgerFunctionalEquation`:
    - `coeff_eq_of_coeffTheta_relation` (all coefficients equal `−2α` from any theta relation);
    - `coeff_eq_zero_of_odd_coeffTheta_relation`.
- **Consequence.** The L140 chain in Lean needs no Schwarz reflection and no continuation of `D_w` left of the line. The only missing piece is the boundary regularity of two-sided perturbations: `Z·D_w` continuous up to the line with `Re D_w⁺` supported on the zeros (Herglotz sandwich plus atomic `ξ'/ξ` measure).
- **Producer status: unchanged.** This certifies the extremality side (uniqueness among two-sided directions). It does not touch existence (PBAP) or the `α ≥ 1` wall.

### L148 — Producer short-interval law: Weil positivity gives any producer RH-quality prime-number theory for its own weights. THEOREM [P] (card `2-fully-proven/11-rh-zero-divisor-geometry/weil-cone-producer-short-interval-law.md`)
- **Conjecture (tested and proved).** Any `lam ∈ W` behaves, on its own support, like Λ under RH:
  - smoothed PNT with error `x^{½+ε}`;
  - support in every interval `(x, x+x^{½+ε})` and in almost every interval `(y, y+y^ε)`;
  - polylogarithmic square mass.
  - Consequently a producer supported on the primes forces primes in short intervals.
- **Mechanism.** Borel–Carathéodory on the discs `B(2+it, 3/2)` gives `|Φ(σ+it)| ≤ (1 + 3/(σ−½))|Φ(2+it)|`. So `E = D − 1/(s−1)` has `|E(σ+it)| ≪ log|t|/(σ−½)` on the whole strip: RH-quality growth for free.
  - The pole part of `(1/2πi)∫Dφ̃x^s` is exactly `x∫φ` (Mellin inversion of `u^{−1}∫_u^∞φ`, no residue calculus).
  - The `E` part moves to `Re s = ½+η`.
- **Results [P].**
  - (S) every `(x, x+x^{½+ε})` meets `supp lam`;
  - (AA) almost every `(y, y+2X^ε)` does, by Plancherel in `log y`;
  - (Q) `Σ_{n≤X}lam²/n ≪ log³X(log log X)²`, by Montgomery–Vaughan and the Herglotz mean square;
  - (D) `#(supp ∩ (x,2x)) ≫ x/log^{3+o(1)}x`, improving L75's `θ < ½` to every support of dyadic density `≤ x/log^{3+δ}x`;
  - Corollary: prime-power support ⇒ `≫ x^{2ε}/log^{3+o(1)}x` primes in every `(x, x+x^{½+ε})`, and primes in almost every `(y, y+y^ε)`.
- **Phase-4 attack.**
  - *False?* No; every step is proved.
  - *Circular?* No; only `lam`'s own Herglotz positivity is used, never ζ's zeros.
  - *Rediscovered?* The mechanism is the classical "RH ⇒ short-interval PNT" (von Koch, Cramér, Selberg), transported to the free-weight cone. The new content: Weil positivity supplies the growth bound by Harnack, for every integer-supported system, and gives the resulting support and density laws. It is not in the log (L75 had only `θ < ½`; L119 was heuristic) and not in the literature (the free-weight cone is not studied).
  - *Insignificant?* It is a BRIDGE: it turns "unconditional prime-supported producer" into the open short-interval prime problems (`0.525` for all intervals, fixed exponents for almost all).
  - **Verdict: SURVIVES (bridge theorem).**
- **Producer consequence.** An unconditional producer cannot be prime-supported without proving short-interval prime theorems beyond the state of the art. It must use dense composite support (S, AA, D) with anti-resonant weights (L107/L133) of polylogarithmic square mass (Q).
  - Dense multiplicatively structured weights are killed by resonance, and prime-like weights are RH-hard (this entry).
  - The remaining design space is **dense, non-multiplicative, polylog-bounded weights on composites**.
- **Lean.** Target: Theorem S and the prime corollary (Borel–Carathéodory plus Mellin inversion plus one contour shift; no Montgomery–Vaughan).
- **L148 Lean (same day).** Theorem S, the prime corollary and the ζ-datum instance are formal, with standard axioms.
  - Modules: `HTGeometry/ShortBumpMellinSmoothedSums` and `RHTower/WeilPositiveShortIntervalSupport`, both wired.
  - Headline theorem: `RHTower.exists_prime_mem_Ioo_of_zetaWeilPositive`.
  - Every Weil-positive system has support in every `(x, x+x^{½+ε})`. Any **prime-supported producer for ζ's datum forces a prime in every such interval**, which is beyond the unconditional exponent `0.525`.

### L149 — Construction batch in the design space left by L148, and the almost-all law in Lean. KILLS [P] + THEOREM [L]
- **Constructions tested (dense composite support, as L148 requires).**
  - **Zero-freeness is free.** Every system has `F_lam = exp(Σ lam(n)/log n · n^{−s})`, which is automatically zero-free wherever `D_lam` is holomorphic. For example `lam ≡ 1` gives `F = exp(∫_s^∞(ζ−1))`, with a pole at 1 and no zeros.
    - So existence is **purely** the one-sided growth condition `Re(D − 1/(s−1)) ≤ Re Γ̃` on `σ > ½`. There is no zero problem.
  - **Periodic / finite-Ramanujan weights** `lam = Σ_{q≤Q} a_q c_q`. Then `D = ζ·Σ_q a_qΣ_{d|q}dμ(q/d)d^{−s}` is ζ times a Dirichlet polynomial. KILL (L82/L88.2 large values).
    - General lesson: integer-supported measures have a 1-periodic additive Fourier transform. The density pole is replicated at every integer frequency, which gives the ζ-dual. Only Ramanujan coefficients `μ(q)/φ(q)` (i.e. Λ) make the replicas incoherent, and then the dual is the explicit formula.
  - **Integer Beurling primes with real multiplicity.** This is the same as a general `lam`, so there is nothing new. The additive large-values heuristic (alignment of `q ≤ log T` gives only `2√log T`) is irrelevant: the damage comes from the long Dirichlet sums, aligned multiplicatively through smooth numbers.
  - **Half-pole repair** `lam = u − c(√n − √(n−1))`. The pole of `ζ(s+½)`-type at `s = ½` with negative residue adds a positive atom at `t = 0` to the Weil measure. It pays L131's low-frequency deficit `h(0) = −0.686` without a non-integer atom, but it leaves ζ's large values. KILL.
    - Survivor: the half-pole is the integer-supported replacement for L131's point mass near 1.
  - **Lebesgue-tail hybrid** (integer weights on `[2,N]`, Lebesgue beyond). Here `H = P_N − ∫_1^N y^{−s}dy` is entire, so Weil positivity is the **pointwise** inequality `Re H(½+it) ≤ h(t)`, via Phragmén–Lindelöf for `exp(−Φ)`.
    - This gives a zero-free, prime-free sufficient criterion: `∀N ∃w: Re[Σ_{n≤N}w_n n^{−½−it} − ∫_1^N y^{−½−it}dy] ≤ h(t)` implies `W ≠ ∅`, by L68.
    - With `w = Λ` this is Λ's level-`½log N` positivity (the sharp cutoff fails by Gibbs lobes even under RH; the Fejér taper works under RH). So the criterion does not escape RH for Λ-type `w`. Other `w` are untested.
  - **CLT correction (self-audit of L127/L133).** Prime sums of length `T^α` at height `T` have Gaussian moments only up to order `< 1/α`. At `α ≈ 1` only the variance is determined.
    - Tapered Λ at height `N^{1+δ}` is "at the cap except for dips" (zero windows contain 0 or 1 zero), with the same variance as the Gaussian model but bounded above.
    - So the Gaussian kills in L117/L127/L133(b) are heuristic in exactly the α ≥ 1 sense. This confirms that they are not proofs.
  - **L74 trace premise corrected.** On the near radical, `tr(P_V τ_{log n}) ≈ −tr(P_{zeros} τ_{log n})`, and this picks up Landau's `Σ_{γ≤T} n^{iγ} ≈ −(T/2π)Λ(n)/√n`. It is large at prime powers, not ≈ 0.
    - L74's conclusion (prime-blind near-radical PSD combinations exist, hence no slack) survives by a different route. For any `c`, the symbol `Σ c_n n^{−½}cos(τ log n)` has mean zero, so it is negative on some frequency window below the Nyquist height. The near radical contains vectors localized there, so no `Σ c_n M_n` is positive definite on `V`, and Gordan applies.
- **Theorem (Lean).** Almost all windows of length `X^ε` meet the support of any Weil-positive system. A prime-supported producer for ζ's datum forces primes in almost all such windows, for every `ε > 0` (`RHTower.volume_primeGapStarts_le_of_zetaWeilPositive`, module `RHTower/WeilPositiveAlmostAllShortIntervals`).
- **Verdict.** Every construction in the dense design space fails in one of two ways: through ζ's large values (coherent dual) or through Λ's zeros (incoherent dual). The producer's existence is the one-sided pointwise Dirichlet-polynomial problem above, for every `N`.

### L150 — Crystalline producers are Λ and force RH (no RH assumed). THEOREM [P] (card `2-fully-proven/11-rh-zero-divisor-geometry/weil-cone-crystalline-producer-rigidity.md`)
- **Conjecture.** A Weil-positive system whose Weil measure is purely atomic, with atoms at zeta ordinates, is Λ, even if RH is not assumed. Its existence then implies RH.
- **Proof idea.**
  - Atomic Herglotz form gives `Φ̃ = (2(s−½)/π)Σc_j/((s−½)²+t_j²)`, which is odd under `s ↦ 1−s`.
  - ζ's FE makes `ξ'/ξ` odd (unconditional). So `D_w = ξ'/ξ − Φ̃` is odd.
  - `F = ζD_w` is entire apart from `s = 1`: ζ's zeros absorb all of `D_w`'s poles, on or off the line.
  - Odd Hamburger gives `F ≡ 0`, hence `lam = Λ` and `ξ'/ξ = Φ̃`, which has poles only on the line: RH.
- **Phase-4 attack.**
  - *False?* No.
  - *Circular?* No: RH is the conclusion.
  - *Rediscovered?* L129/L140 have the same mechanism, but they assume `Λ ∈ W` (RH) and two-sidedness. Here a **single** crystalline system suffices, and off-line zeros are harmless because ζ cancels them.
  - *Insignificant?* It settles the crystalline case of L105/L106 (second crystalline structures on the zeros) unconditionally.
  - Verdict: **SURVIVES** (theorem).
- **Extension.** Finitely many fake atoms are excluded too: the Hamburger residue argument survives finitely many poles on the line. Infinitely many fake atoms is the L142/L144 obstruction.
- **Producer map after L148–L150.** A producer other than Λ must be:
  - non-crystalline on the zeta spectrum (an absolutely continuous part, or infinitely many fake atoms), by L150;
  - dense in composites, and not prime-supported without breaking short-interval records, by L148/L149;
  - free of ζ-type large values, by L107/L133.
  - The crystalline route to a second producer is closed.

### L150 Lean — closed
- `RHTower.crystalline_producer_rigidity` (module `RHTower/CrystallineProducerRigidity`, on top of `RHTower/ZetaSpectrumAtomicSeries`). Standard axioms only.
- Both cards moved to `3-formalized/11-rh-zero-divisor-geometry/`.
- Reusable pieces:
  - `eventually_eq_zero_of_deriv_eq_mul` (a zero of an analytic solution of `f' = fg` is not isolated);
  - `completedZetaXiLogDeriv` (`Λξ'/ξ`, odd, decaying);
  - `atomicZetaPart` (ζ-cancelled atomic Herglotz series, odd, holomorphic, decaying);
  - `coeffDirichlet_eq_LSeries`.
