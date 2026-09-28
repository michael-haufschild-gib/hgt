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
