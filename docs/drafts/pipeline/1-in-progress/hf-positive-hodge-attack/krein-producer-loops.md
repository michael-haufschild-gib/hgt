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
