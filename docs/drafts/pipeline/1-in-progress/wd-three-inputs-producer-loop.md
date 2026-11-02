# WD missing inputs: long-range depth pair correlation, long mollifiers, counting producer

- **ID:** wd-three-inputs-producer-loop
- **Stage:** 1-in-progress
- **Type:** CONJECTURE LOOP
- **Source:** wd-review-0111-closing-loop (rows 4–20); route-WD blocks 1, 3–6.
- **Statement:** Construct an unconditional input that makes the WD window energy `|𝒵(t)|²`
  grow sub-exponentially beyond `t = log T` on average over windows.

## Goal

Blocks 1 and 3–6 need information about `|𝒵_m(t)|²` for `t ≫ log m`, that is prime data of
length `T^α`, `α → ∞`, at the scale `1/log T` in depth. Block 3 (mean log-stage index
`o(log U)`) is the weakest open rung.

## The three inputs and the minimal input

Write `G(α) = N⁻¹ Σ_{ρ,ρ'} T^{α(ρ+ρ̄'−1)} w(γ−γ')` (depth-weighted Montgomery form, corpus
`averagedMontgomeryForm`), `δ = a/log T`.

1. **Long-range pair correlation.** Zeros deeper than `2a/log T` gain weight `e^{2aA}` in
   `∫_0^A e^{−2aα}(A−α)G(α)dα` against the damped on-line diagonal `A/(2a)`; tight deep pairs
   (ordinate gap `< C/(AL)`) can cancel at the end of the range and are `O(N/A)` by the
   Selberg–Fujii short-range count. But the long-range energy weights every zero by `e^{2αLδ}`, so
   a sub-exponential bound for all ranges `A` forces `N(½+η,T) ≤ T^{1−2Aη}N` for all `A`: quasi-RH.
   Long-range energy is the wrong currency for block 3.
2. **Long mollifiers.** Mollified mean squares at `σ₀ = ½ + b/log T` are depth-localized; with
   Littlewood and Jensen they bound `Σ(β−σ₀)₊`. The constant tends to `0` only as `θ → ∞`
   (corpus: `0.067V` at `θ = 21/50`; depth charge `O(log U)` for `c < ½`). For `θ > 1` even
   `∫_T^{2T}|M|²` is a sum of squares of Möbius sums over intervals of length `n/T`: the parity
   barrier. Kloosterman/Kuznetsov technology (in the corpus: Weil bound, DI large sieve for `Γ₀(Q)`)
   caps at `θ < 1`.
3. **Counting producer.** Over `𝔽_q` the window bound is `|𝒵(n log q)| ≤ 2g`, Stepanov's count.

**Minimal input for block 3.** By the corpus TFAE
(`dyadicMean_corridor_and_polynomialTheta_littleO_log_up_to_half_tfae`), the Selberg tail law
(`eventually_offLineTail_le_selberg`, rate `−log(1−e^{−2R/15}) → 0`) and Littlewood on the line
(`exists_zetaLine_logMean_sandwich`), block 3 is

  `∫_T^{2T} log|ζ(½+it)| dt = o(T)`, equivalently `Σ_{T<γ≤2T} m_ρ(β−½)₊ = o(T)`,

a logarithmic (not quadratic) functional of `ζ` on the line. Quadratic inputs reach it only
through mollifiers and Jensen.
## Ledger

| # | Conjecture | Verdict | Insight |
|---|---|---|---|
| 1 | Averaged Hardy–Littlewood (mean square over `h ≤ H`, Mikawa/Perelli–Pintz) gives `G(α) = e^{o(α)}` | refuted | the growth bound needs `Σ_{h≤H} φ̂(h/H)(S(h)−𝔖(h)x) ≪ x H^ε`, relative precision `H^{−1+ε}`; mean-square HL saves only `(log x)^{−A}` per shift |
| 2 | Upper-bound sieves (Selberg, `S(h) ≤ C𝔖(h)x`) bound `G(α)` | refuted | the main term `Σ 𝔖(h)x` cancels against the pole term; a factor `C` leaves `(C−1)H/log H = T^{α−1}`, the trivial bound |
| 3 | Height averaging localizes the long range to an accessible first moment | reduction | it becomes `Σ_n Λ(n)(ψ_φ(n;H) − H)` (Λ-weighted short-interval discrepancy), and the explicit formula returns it to `G(α)`: circular |
| 4 | Short-interval variance (Huxley range) bounds `G(α)` | refuted | Cauchy–Schwarz gives `G ≲ T^{(α−1)/2}`; still exponential in `α log T` |
| 5 | Tauberian `∫_b^{b+1} G ≪ 1` (Montgomery's RH argument, depth-damped so the form stays a square) | refuted | damping by the window's top depth makes the bound say `#top ≲ N`; `o(N)` needs `G_damped → 0`, which is the claim |
| 6 | Positive definite (Krein) extension of `G` from `[−1,1]` | refuted | depth weights destroy positive definiteness; under RH it gives `F(α) ≤ F(0) ~ log T` for free |
| 7 | Euler-product mollifier `∏_{p≤X}(1−p^{−s})` (mean of `log|P_X|` is exactly 0) | refuted | `E|ζ/P_X|² ≈ e^{−γ}log T/log X`; needs `X = T^θ`, a mollifier of length `e^{T^θ}` |
| 8 | Fractional moments / Jensen gap: `mean log|ζM| = ½ log E|ζM|² − J` | reduction | `J ≥ 0` is the log-variance of `ζM`; fourth moments improve constants only; `J = ½ log c − o(1)` is equivalent to the claim |
| 9 | Heat flow: Ki–Kim–Lee at `t > 0` transfers to ζ | refuted | KKL threshold `t ≍ 1/log T`; heat time `t` acts like depth `tL/8`; deep-zero persistence is proved only for `t ≤ δ²/L⁴` (corpus `exists_card_deep_le_mul_nonrealZeroCount`) |
| 10 | Turán power sums on `𝒵_m(t)`, `t ∈ [L, AL]` | refuted | loss `e^{−O(#zeros)} = T^{−c}`; detecting depth `a/L` needs `t ≳ L²/a` |
| 11 | Spectral families (GL(2)/GL(n) large sieve with Eisenstein slice) give long mollifiers | refuted | the large sieve loses the constant; dropping cusp forms costs the family size; Conrey's `4/7` is the limit of the Kuznetsov–Weil route |
| 12 | Parity-breaking inputs (Matomäki–Radziwiłł, log-Chowla) supply the off-diagonal | refuted | they give relative `o(1)` cancellation in short intervals; the growth bound needs square-root cancellation over shifts (variance asymptotics) |
| 13 | Linear combinations of L-functions as calibration | corrected | for `F = Σ c_j L_j` with a common functional equation, `log|L_1/L_2|` has variance `→ ∞` (Selberg), one term dominates almost everywhere, and Bombieri–Hejhal (GRH for the `L_j` plus a spacing hypothesis) give 100% of zeros simple and on the line; so block 3 holds for Davenport–Heilbronn-type `F` while RH fails (zeros with `σ > 1`). Block 3 does not need the function's own Euler product; the dominance mechanism needs two competing Euler products |
| 14 | AFE main sum `A_t = Σ_{n≤√(t/2π)} n^{−s}` governs depths | reduction | right of the line `ζ ≈ A_t` (`|χ| = e^{−uL}`); a zero of `A_t` at depth `D/L` creates an off-line zero of the first-order model once `D` exceeds a constant. RH forces `A_t` to be (typically) zero-free beyond `C log L/L`; transfer is not uniform because `max|A*| ~ T^{1/4}` |
| 15 | Fermat/LTE auxiliary integers `a^{lcm(1..x)}−1` as a Stepanov producer | refuted | multiplicity `1+v_p(lcm)` on all `p ≤ x`, but the size `e^{ψ(x)}log a` is exponential in the count |
| 16 | Deligne amplification over ℤ: k-fold zero sums (Kurokawa tensor powers) with a k-uniform weak bound | reduction | over `𝔽_q` the error `+1` comes from the Lefschetz pencil base curve; over ℤ mean values give only the cap `kλ ≤ 1` and the Kurokawa Euler region has error `k/2`; detecting depth `a/L` through `|𝒵|^{2k}` needs range `t ≈ L log L/(2a)`, length `T^{2kα}` |
| 17 | Unconditional Montgomery simple-zero argument with depths | corrected | termwise Fejér positivity fails at deep pairs, but the rank–trace (Frobenius) certificate is unconditional: `4 tr Â − ‖Â‖_F² − 2N + M_off ≤ s₁` (TTPC), giving simple critical proportion `2 − κ(λ)`, `κ(λ) = 1/λ + (2/λ²)∫_0^λ(λ−α)F(α)`; corpus has `HD(1) = 0.6725…` (Zeta23 Thm D) and `0.67250071` (`simple_critical_proportion_ge_67250071`). An off-line reflected pair is a double ordinate there, whatever its depth |
| 18 | Levinson structure through the AFE half: off-line zeros of `A+χA*` ≤ `2·#{zeros of A right of ½}` | reduction | this is Levinson's method with `G` the AFE half; the sharp half `1_{n≤√(t/2π)}` is badly mollifiable (truncation residues `≍ L`); smooth halves give Levinson–Conrey, `θ`-limited; Farmer's `θ = ∞` would give 100% |
| 19 | Micro-scale limits: subsequential limits `F` of `ζ(½+i(t₀+z/L))/√L` are real on ℝ with the CUE 2- and 4-point moments; block 3 ⟺ every limit has only real zeros | reduction | the known moments fix `E|F|²` and `E|F|⁴`, not `E log|F|`; real-rootedness needs the log-moment |
| 20 | Heat flow at time `τ/L²` (KKL threshold `e^{c/√t}`) | reduction | with dense real neighbours a pair at depth `a/L` dies by heat time `log(1+ca²)/(2cL²)`; KKL at time `τ/L²` would give the corridor (block 5), but at that time the effective series sits at depth `τ/(8L)`: the same critical problem |
| 21 | Jensen loss as the obstruction: `mean log|ζM| = ½ log E|ζM|² − J`, and `J` computable | reduction | for `Y = log|ζM(½+b/L+it)|`, `J ≈ Var Y ≈ ½E₁(2bθ)` from primes beyond `T^θ`; primes beyond `T` are dual to the zeros near `σ₀`, so `E Y` (not `Var Y`) is the depth sum; higher moments of `ζM` cannot improve the upper bound on `g'(0)` for the convex `g(k) = log E|ζM|^{2k}` |
| 22 | a-points as calibration | insight | `a`-points (`a ≠ 0`) have mean depth `≍ √(loglog T)/log T`; block 3 is the `o(1)` symmetry `E log⁺|ζ| − E log⁻|ζ| → 0` of the log-normal law of `|ζ(½+it)|`, invisible to Selberg's CLT (precision `o(√loglog T)`) |
| 23 | Family averaging (Conrey–Iwaniec–Soundararajan asymptotic large sieve) lengthens mollifiers | refuted for ζ | effective `θ > 1` exists only on average over a family of conductors; height averaging is one-dimensional and gives no extra room for a single `ζ` |
| 24 | A pair functional `Σ k(z+w̄−1)` with `k = ∫e^{tζ}dμ`, `μ ⊂ [−L,L]` (Montgomery range) that separates off-axis pairs | refuted | two such kernels agreeing on the imaginary axis coincide (identity theorem; the odd part of `μ` cancels by reflection); to first order an off-line reflected pair is a double ordinate (block sum 4 vs 2) and depth enters at second order `(tδ)²`; so the `α ≤ 1` constraints admit a positive proportion of off-line pairs (Montgomery's `1/3` double-ordinate ceiling) |
| 25 | Amplified zero detection / large sieve over zeros with detector length `X = T^θ`, `θ > 1` | refuted | the dual large sieve `Σ_{n≤X}|Σ_ρ c_ρ n^{iγ}|² ≈ X·N·F(log X/log T)` keeps the `X`-term even if `F ≡ 1`; slope `2θ` needs `θ ≤ 1` |
| 26 | Literal block-3 object (Zhukovsky index at the log stage) from clustering via corpus inputs | reduction | index `≤ 2Σ_{deep z} #near(z)`; Cauchy–Schwarz needs `Σ_z #near(z)² ≪ N` (Selberg–Fujii); the Montgomery–Gram route fails at near neighbours of very deep zeros (pointwise local count `≪ log T`), and the corpus almost-all corridor leaves `O(U/loglog U)` bad windows, too many by `log U/loglog U` |
| 27 | Stepanov through the reflection `ι(s) = 1 − s̄`: on-line zeros are the fixed points of `ι` among zeros, as rational points are the fixed points of Frobenius | refuted | Stepanov bounds fixed points from above and gets the lower bound from twists whose fixed-point counts sum to a known total; there is no family of twisted involutions of the zero set with a computable total, and auxiliaries vanishing at off-line zeros only (`ζ(s)ζ(1−s)` etc.) vanish at all zeros |
| 28 | Lee–Yang / Kurasov–Sarnak: real zeros from a stable Bohr lift `Q(z,w) = wÃ(z) + Ã*(z)`, `Ã(z) = Σ_{n≤N} n^{−½} z^{v(n)}` restricted to `z_p = p^{−it}` | refuted | the truncated half has zeros in the closed polydisc (generic for `N ≥ 3`), so `Q` is not stable; the factor `w = e^{2iθ(t)}` has phase `≈ (t/2)log(t/2πe)`, not a linear phase, so `t ↦ Q` is not a line in a torus; the full Euler product is stable on the polydisc but `ξ(½+it)` is not a function on the infinite torus |
| 29 | The moderate band: block 3 ⟺ `#{κ/L < δ ≤ R/L} = o(N)` for all `0 < κ < R`; attack it by the mollifier zero credit `Σ(β−σ₀)₊ = (T/2π)[E log|ζM| − E log|M|]` | refuted | shallow zeros cost `≤ κT/2π`, the tail beyond `R/L` costs `e^{−2θR}T/4π` (corpus tail law); the moderate band is the whole content. In the log-normal model `E log|M| ≈ −E log|ζ| ≈ 0`, so the credit does not cancel `½ log c`; the loss is the Jensen gap (log-variance of `ζM`), not a missing credit |
| 30 | Variance projection: certify the Jensen gap `J(Y) ≥ Var(prime part on (T^θ, T])` for `Y = log|ζM|`, doubling the effective mollifier length to `θ = 1` | refuted | `J ≥ Cov(Y,X)²/Var X` needs joint Gaussianity; the conditional-Jensen form `½log E e^{2Y} ≥ EY + ½log E e^{2X}` needs exponential moments of `X`, whose `k`-th moment has length `T^{k}`: the arithmetic cap `kλ ≤ 1` leaves only the variance |
| 31 | Long mollifiers through the contour form `M(s) = ∮ ζ(s+w)⁻¹ T^{θw}P̂(w)dw` | reduction | for `θ > 1` the zero residues `T^{θ(ρ−s)}/ζ'(ρ)` dominate; `∫|M|²` becomes a zero-pair sum weighted by `1/(ζ'(ρ)ζ̄'(ρ'))`: Gonek–Hejhal negative moments plus pair correlation, open even under RH |
| 32 | Holomorphic moments `E(ζM)^k = 1` plus `E|ζM|² = c` improve Jensen's `E log|ζM| ≤ ½ log c` | refuted, survivor formalized | the boundary law of `F(w) = r⁻¹(w+r)/(1+rw)`, `r = c^{−½}`, has every holomorphic moment `1`, constant modulus `√c`, log-mean exactly `½ log c`; the mollifier method's loss is intrinsic to its data (`exists_jensen_extremal`) |
| 33 | All absolute moments `E|ζM|^{2k}` (if known) determine `E log|ζM|` | refuted (structural), survivor formalized | at fixed `θ` the law of `log|ζM|` has positive variance; log-normal moment sequences are indeterminate (Heyde: densities `f(x)(1 + ε sin(2π log x))` share all moments), and the perturbation shifts `E log` by `ε·2π e^{−2π²}`; so no moment method at fixed mollifier length pins the log-mean, only `θ → ∞` (variance `→ 0`) or non-moment structure |
| 34 | Gaussian bookkeeping: `E log|ζM| = ½ log E|ζM|² − Var − (higher cumulants)` with the variance from primes and zeros | reduction | the `O(1)` term of the variance is the Goldston–Gonek–Montgomery constant `∫_1^∞ F(α)α^{−2}dα` (long-range pair correlation, weighted); at fixed `θ` the higher cumulants of `log|ζM|` are `O(1)` (log-singularities, few nearby zeros), so mean and variance do not determine each other |
| 35 | Szegő–Kolmogorov–Helson: the optimal mollified mean square `c_opt(θ) = inf_{a_1=1}(1/T)∫|ζM|²` over all mollifiers of length `T^θ` | equivalence (insight) | Jensen with the mollifier credit `E log|M| ≥ 0` gives `c_opt(θ) ≥ exp(2E log|ζ|)` for every `θ`; Helson–Lowdenslager on the Bohr torus `𝕋^∞` (dual ℚ₊ ordered) predicts `c_opt(θ) → exp(2E log|ζ|)`; so the long-mollifier input (optimal coefficients, `θ → ∞`) is equivalent to block 3, not merely sufficient. Transfer from `𝕋^∞` to `t ∈ [T,2T]` holds only below length `T` |
| 36 | Derivatives: on-line zeros of `ξ'` (Conrey-type proportions, corpus `eventually_deriv_xi_criticalLine_count_ge`) constrain `ξ` | refuted | a shallow off-line pair of `ξ` turns the Rolle interval of `Ξ` from one critical point into three (max–min–max), so on-line zeros of `ξ'` absorb off-line pairs; `ξ'` can be 100% on the line while `ξ` is not |
| 37 | Block 3 through the rank–trace census (row 17): 100% simple critical zeros ⟹ block 3 | reduction | `κ(λ) → 1` needs the form factor `F(α) ≈ 1` on `[1, λ]` for `λ → ∞`, the TTPC coalescent-surplus bound at every bandwidth (`3/4` already needs `S ≤ (1/18+o(1))N` at `λ = 4/3`); rank–trace counts distinct ordinates and cannot separate shallow from deep off-line pairs, so it cannot use the weakness of block 3 relative to 100% critical |
| 38 | Synthesis: which quadratic side sees depth | insight | Weil side (rank–trace, reflection pairing `w_ρ ⊗ w̄_{ρ̃}`): on a fine height grid `⟨w_{ρ̃}, w_ρ⟩ ≈ 2π∫φ²` for every depth, so an off-line pair is a double ordinate and certificates are depth-blind; 100% needs bandwidth `λ → ∞`. Collided side (`|ζM(σ₀)|²`, window energy, Hecke defect): sees depth but carries the Jensen gap, intrinsic for moment data (formal, rows 32–33); 100% needs `θ → ∞`. Block 3 sits between: depth-tolerant (Weil side cannot use it) and logarithmic (collided-side moments cannot reach it) |
| 39 | Hermite/Sturm counting: off-line ordinates of the window polynomial `P_m` are its non-real pairs, `#neg` of the power-sum Hankel matrix | reduction | the Hankel entries are linear statistics (explicit formula), the inertia is not; corpus `rootPowerSumHankel_posSemidef_iff`, `thetaArithmeticTraceHankelRequiredWindow_posSemidef` already make window RH a Hankel sign; bounding `#neg` from linear data needs a low-rank PSD correction, i.e. the sign itself |
| 40 | Modular-surface resonances: ζ-zeros are the resonances `ρ/2` of `PSL(2,ℤ)` (zeros of Mayer's `det(1 − L_s²)`); Dolgopyat-type spectral gaps for the Gauss-map transfer operator | refuted | spectral-gap methods give resonance-free regions near the top (`Re s` near `½`, i.e. `σ` near `1` for ζ), not concentration on `Re s = ¼`; the scattering phase `φ = ξ(2s−1)/ξ(2s)` that carries the resonances is ζ itself |
| 41 | Hamburger rigidity: the functional equation with conductor one plus being a Dirichlet series forces `ζ` (Euler product implied), so theta modularity alone must carry block 3 | insight | true but non-constructive: Davenport–Heilbronn functions (conductor `> 1`) show that the functional equation without uniqueness fails block 3; extracting the Euler product from modularity is Hecke's converse theorem, which gives coefficients, not depth control |
| 42 | Landau positivity: `(ψ(x)−x)²` and the window energy are positive, their Mellin/Laplace transforms have real singularities at `2δ_ρ` (conjugate pairs `ρ, ρ̄`) | reduction | positivity gives the abscissa (twice the maximal depth, already formal as the energy–index law), not proportions; a Tauberian reading of the residues at `2δ` is blocked by the complex singularities `z + w̄ − 1` of top-depth pairs on the abscissa line |
| 43 | Topological counting: sign changes of Hardy's `Z` as crossings of the phase `θ + arg A` | reduction | each zero of the AFE half right of the line reverses the phase by `π`; the count of off-line zeros is twice the count of right-zeros of the half (Levinson, row 18), which only Littlewood plus mean values bound |
| 44 | Pointwise window certificates: for most windows `|𝒵_m(t)| ≪ L^ε √t` on `t ≤ L` (mean square plus a maximal inequality over `t`) | refuted | depth `a/L` changes `𝒵_m` by `e^{a}` only, invisible below `t ≈ L/a`; extrapolating an `L`-term exponential sum beyond `[0, L]` costs Turán's `(Ct/L)^{O(L)}` |
| 45 | Hecke structure: WD translation by `2 log p` is the Hecke operator `T(p²)` on the weight-½ theta series, with exact eigenvalue `1 + 1/p` | insight | the eigen-relation is the Euler factor at `p` of `ζ(2s)`; Euler factors do not vanish on the strip, so zeros are Hecke-invariant and the relation carries no depth |
| 46 | Averaged linear statistics `E_T Σ_ρ g(γ − T − iδ_ρ)` | refuted | by the contour shift `∫ g(u − iδ)du = ∫ g(u)du` the height average is depth-blind for every entire `g`; depth enters linear statistics only pointwise, through `g''δ²` |
| 47 | Certify the Jensen gap from primes in `(T^θ, P]` by a truncated linear tilt `dQ/dP = 1 + λX·1_{|X|≤K}` (Donsker–Varadhan) | refuted | the tilt needs `|λX| ≤ 1`, and the lost mass `E[X²1_{|X|>K}]` needs the fourth moment of the prime polynomial `X`, whose square has length `P²`: the cap is `P ≤ T^{½}`, exactly the mollifier cap; a heavy lower tail of `log|ζM|` (near zeros) can make the Jensen gap `≪` the variance |
| 48 | Calibrations by structure (Beurling systems: Euler product, no functional equation; Davenport–Heilbronn: functional equation, no Euler product) | corrected | Davenport–Heilbronn satisfies block 3 (row 13) by dominance; for `ζ` the AFE ratio `R = χA*/A` has `|R| ≡ 1` on the line (maximal balance), so dominance is unavailable and block 3 is the scarcity of bubble curves `{|R| = 1, σ ≠ ½}` at depth `≥ a/L` |
| 49 | Total positivity (Pólya–Schoenberg): RH iff `ℱ[ξ(½)/ξ(½ + ·)]` on the real axis of `ξ` is a Pólya frequency function | reduction | non-moment and non-reflection, but local total positivity at scale `1/T` is Hankel/Turán positivity of the Taylor data, i.e. Jensen-polynomial hyperbolicity; Griffin–Ono–Rolen–Zagier give fixed degree with large shift, far from degree `≍ T²` at shift `0` |
| 50 | Block 3 through the AFE half at its natural height: (first-order model) block 3 ⟺ `E log|A_t(½ + a/L + it)| = o(1)`, `A_t = Σ_{n≤√(t/2π)} n^{−s}` | reduction | `A_t` is short (`√T`), so `E|A|²`, `E|A|⁴` are exact, but its inverse is not short (the cutoff destroys multiplicativity; truncation residues have mean square `≍ L`), and the Bohr–Jessen model predicts a positive Mahler measure (the Bohr lift vanishes in the polydisc); the self-dual regime `t ≈ 2πN²` is non-random, and the scarcity of right-zeros of `A_t` is itself the content of block 3 |

## Formalized

- `RHTower/WD/HolomorphicMomentsCannotBeatJensen.lean`: `integral_log_norm_le_half_log_integral_sq`
  (Jensen ceiling for any probability law), `exists_jensen_extremal` (sharpness: for every `c > 1`
  a law with all holomorphic moments `1`, mean square `c`, log-mean `½ log c`). Standard axioms only;
  wired into `RHTower.lean`.
- `RHTower/WD/MomentsDoNotDetermineTheLogMean.lean`: `logNormal_moments_do_not_determine_logMean`
  (Heyde's laws `φ(y)` and `φ(y)(1 + sin 2πy)` share `E e^{kY}` for every `k ∈ ℤ`; their means differ
  by `2π e^{−2π²}`). With the Jensen sharpness: at fixed mollifier length no moment data, finite or
  complete, fixes the critical-line log-mean. Standard axioms only; wired into `RHTower.lean`.

## Open core

An unconditional bound for the damped long-range energy, equivalently cancellation of size
`H^{1−ε}` in `Σ_{h≤H}(Λ(n)Λ(n+h) − 𝔖(h))` on average over `n`, or a ℤ-auxiliary with Frobenius-type
multiplicity. No mechanism above survives.

## Log
- 2026-11-02 — created; rows 1–50; rows 13 and 48 corrected (Bombieri–Hejhal); row 17 corrected after reading the rank–trace census; minimal input identified (critical-line log-mean).
