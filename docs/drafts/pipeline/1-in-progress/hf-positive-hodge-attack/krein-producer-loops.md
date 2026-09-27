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
