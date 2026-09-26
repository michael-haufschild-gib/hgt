# Route 1 producer: conjecture → proof-or-kill → pivot loop

- **ID:** R1-PRODUCER-LOOP
- **Stage:** 1-in-progress
- **Type:** CONJECTURE LOOP (log)
- **Source:** `docs/reports/route-proposals/route1.md`. Route 1 is formal up to its producer: `riemannHypothesis_iff_forall_xiRightDisc_adjointSeam_lt_one` [L].
- **Target:** a producer of `‖(1−P)U†P‖ < 1` for the `xi` boundary phase on every disc strictly right of the critical line. By HF-L10/L11 this is also the level-wise Krein-extendability producer.
- **Kill standard:** a countermodel satisfying all inputs of the named producer, or a disproof of an intermediate claim. Hamburger's theorem pins any Dirichlet series with ζ's functional equation to ζ, so route 1 itself admits no countermodel. Kills apply to producer *classes*.

## Cycles

| # | Conjecture | Verdict | Reason |
|-|-|-|-|
| 1 | Torus completion coupling primes through invisible composites (HF-L13) | FALSE | Product test vectors force `M_min(a) ≳ e^{a/2}`; phases are independent on the Bohr torus |
| 2 | Three-regime map; SP-L short-prime alignment bound (HF-L14) | DIAGNOSIS | Moderate heights are the Lindelöf regime `2a ≪ (log t)^{2/3}` |
| 3 | SP-L as stated | FALSE (heuristic + RH-conditional) | Random-phase extremes `≍ a√(log t)`; under RH, Montgomery's Ω-results for `S(t)` give negativity at `log t ≲ C a²`. Pointwise completions fail at moderate heights either way |
| 4 | Diophantine (Baker) alignment exclusion | INSUFFICIENT | Baker bounds exclude only precision `exp(−C(n)Π log p · log t)`, not `O(1)` alignment |
| 5 | σ-convexity of `log|ξ(σ+it)|` | FALSE near zeros | `∂²_σ log|ξ| = Σ_ρ (y²−x²)/|w|⁴` is negative when `|t−γ| < σ−½`; the monotonicity equivalence (Sondow–Dumitrescu) is classical |
| 6 | Hurwitz real-zero approximants (Taylor, Ising/Lee–Yang, determinants) | CORPUS-CLOSED | Consumers [L]: `riemannHypothesis_of_XiC_locally_uniform_real_zero_approximants`; Ising/GKS no-gos [L] |
| 7 | Derivative descent `Ξ^{(n+1)} ∈ LP ⇒ Ξ^{(n)} ∈ LP` | NO LEVER | Kim: `Ξ^{(n)}` has only real zeros in any fixed disc for large `n`, unconditionally. All RH content sits in the descent step |
| 8 | **Seam margin**: some producer gives `‖(1−P)U†P‖ ≤ 1−c` uniformly on right discs | **FALSE, with proof [paper]**; positive survivor below | Seam log-defect law |

### Cycle 8: seam log-defect law [paper; Lean pending]
Let `F` be holomorphic near a closed disc `D` and zero-free on it, with a simple zero at distance `ε` outside `∂D`. In disc coordinates write `F = (z − w₀)G`, `|w₀| = 1 + ε′`, `λ = 1/w̄₀`, and `a_λ = (1 − λ̄z)^{1/2}` (analytic, outer). Then:
- `ū = c · conj(a_λ)/a_λ · v̄` with `v = G/|G|` smooth and `|c| = 1`.
- Test vector `f = a_λ^{-1} = (1 − λ̄z)^{-1/2} ∈ H²`:
  - `P(conj(a_λ)/a_λ · f) = P(conj(a_λ) k_λ) = conj(a_λ(λ)) k_λ`, of norm exactly `(1−|λ|²)^{1/2}‖k_λ‖ = 1`.
  - `‖f‖² = Σ_n binom(−½,n)² |λ|^{2n} ≈ (1/π) log(1/(1−|λ|²)) → ∞`.
  - The smooth factor costs `O(1)`, since `|f|² ~ |z − ζ₀|^{-1}` and `v̄ − v̄(ζ₀) = O(|z−ζ₀|)`.
- Hence the lower bound of `T_ū` is `≤ C/√(log(1/ε))`, and `‖(1−P)U†P‖² ≥ 1 − C²/log(1/ε)`.

**Consequences.**
- (i) Take right discs approaching an on-line zero (Hardy's theorem [L] gives infinitely many). Then `sup_{right D} ‖(1−P)U†P‖ = 1` unconditionally.
- (ii) **Kill:** every producer claiming a uniform seam margin on right discs is false.
- (iii) **Survivor (seam log-defect law):** `(min_{∂D}|F|/max_{∂D}|F|)² ≤ 1 − ‖(1−P)U†P‖² ≤ C/log(1/dist(zeros, ∂D))`. Route 1's seam defect decays at the critical-Sobolev log rate. This is the corpus's one-log wall (MUST-440, critical Sobolev exponent) appearing in route 1's own carrier: a producer must be sharp at the log scale.

**Next.**
- (a) Formalize the test-vector bound in the `CCMCircleL2` model: `f = Σ binom(−½,n)(−λ̄)^n e_n` together with the projection identity.
- (b) Cycle 9: is `1 − σ² ≍ 1/log(1/d)` also a *lower* bound under RH, i.e. a logarithmic-capacity law for the seam? If so, the producer target becomes a capacity lower bound, a potential-theoretic statement that is new to the corpus.

| # | Conjecture | Verdict | Reason |
|-|-|-|-|
| 9 | Log-capacity law: `1 − σ(D)² ≍ 1/log(1/d)`, `d` = distance from `∂D` to the nearest zero | **TRUE up to the exponent [paper]** | Upper `C/log(1/ε)` from the cycle-8 test vector. Lower: `T_ū = T_{ā}T_{1/a}`, `T_ū^{-1} = T_a T_{1/ā}`, so `‖T_ū^{-1}‖ ≤ ‖P‖_{L²(w)}` with `w = |1−λ̄z|`. Then `[w]_{A₂} ≍ log(1/ε)` (borderline power weight `|z−ζ₀|¹`) and Petermichl's sharp A₂ bound give `1 − σ² ≥ c/log²(1/ε)`. The seam is a Helson–Szegő/A₂ quantity of the boundary weight |F|² |
| 10 | A₂ producer: control `[|ξ|²|_{∂D}]_{A₂}` arithmetically | NO LEVER | The weight `|ξ|²` on `∂D` does not see zeros inside `D`. They enter only through the Jensen defect `log|O(c)| − log|ξ(c)|` = route LA/Jensen (R1-L2; `U(t)<2` wall) |
| 11 | FE-free producers (Euler product + Λ ≥ 0 + Γ-completion, no FE) | CORPUS-KILLED | Beurling countermodels with off-line zeros [L] (`BeurlingRegularIntegersOffLineZeros`, `BeurlingRHSensitivityThreshold`) |

**Surviving producer class after cycles 1–11:** it must use (FE) ∧ (Euler product) ∧ (Λ ≥ 0) jointly (the Selberg-class axioms, where no countermodel is known). It must be sharp at the logarithmic scale (cycle 9). It cannot live on the Bohr torus (cycle 1), cannot be pointwise at moderate heights (cycle 3), and cannot be a finite-prime completion (HF-L12).
| 12 | Sum-of-squares factorization `W_a = B_a^* B_a` with `B_a` built from the Γ-factor alone (Sonin/prolate) | FALSE at large `a` | The archimedean symbol `Ω(t) = Re ψ(¼+it/2) − log π` is negative on `|t| < 6.3` (`Ω(0) ≈ −5.37`). Two polar constraints cannot absorb it for large `a`, so `B_a` must carry primes at low frequency, which is L2 again |
| 13 | Herglotz/Pick producer via `−Z′/Z` | CIRCULAR | Pick ⟺ real zeros (Hermite–Biehler / de Branges / Lagarias) |
| 14 | Index bundle over the space of right discs | TAUTOLOGICAL | Walls are exactly off-line zeros on disc boundaries; the right-disc space is contractible |
| 15 | Linear independence of ordinates (LI) as producer | STRONGER THAN RH | An off-line pair shares an ordinate, so LI over all zeros ⇒ RH + simplicity; LI is harder than RH |
| 16 | x-flow of the formation: `∂_x L_x(s) = −π L_x(s−2)` (shift-delay law, exact) | TAUTOLOGICAL TRANSPORT | Iterating moves the same zero terms `Γ((ρ−s+2)/2)(πx)^{(s−2−ρ)/2}` further left; no monotone quantity. The exact identity itself is new to the corpus as a formula |

**Pivot rule for the next batch.** Cycles 1–16 kill every mechanism that separates primes, localizes pointwise, avoids the FE, averages, or uses holomorphic readers. The next conjectures must be global on the line, FE ∧ Euler ∧ Λ ≥ 0, log-sharp, and exact. Candidates to test next:
- (α) Gaussian approximate functional equation (Riemann–Siegel with Gaussian cutoff) as an exact FE-built two-term decomposition `ζ = Z_x + χ Z̃_x + (Γ-residue)`. At the symmetric `x`, `Z(t) = 2Re(e^{iθ}Z_x) + small`. Test: can the phase of the "half-function" `e^{iθ}Z_x` be shown monotone (Gram-law rigidity)?
- (β) log-capacity law (cycle 9) plus the Selberg CLT for `log|ζ|` on circles. Is the typical seam defect at height `T` provably `≫ 1/(log log T)^c` on almost all right discs? This would be a density-type producer: new, but proportions only.
- (γ) exact FE-pairing inertia (Alpöge–Furman (1,1) blocks) combined with route 1's integer on thin symmetric rectangles. Test whether the local rank–trace inequality can individuate at the log scale.
| 17 | (α) Gram-law rigidity: `θ + arg D_N` monotone for the Riemann–Siegel half-function | FALSE | `d/dt arg(e^{iθ}D_N) = θ′ − Re(Σ log n · a_n / Σ a_n)` is borderline 0 at `N = √(t/2π)` and negative where `D_N` is small (Titchmarsh: Gram's law fails infinitely often) |
| 18 | (β) seam-defect density via the Selberg CLT | PROPORTIONS ONLY | Individual-zeros gate |
| 19 | (γ) local rank–trace individuation | FALSE | Local second moments fluctuate by `O(1)` relative; Alpöge–Furman §7.2: nothing distinguishes 2/3 from all |
| 20 | Interlacing families (Marcus–Spielman–Srivastava) for Ξ's Jensen polynomials, written as positive averages of one Laguerre-type polynomial at scaled arguments (corpus `jensenPolyEval_superposition`) | LARGE-`n` ONLY | A common interlacer exists iff the tilted measure's support ratio is `≤ min_j r_{j+1}/r_j ≈ 1 + O(d^{-2/3})`. The tilt `s^n dμ` concentrates at relative width `n^{-1/2}`, so this plausibly gives `J^{d,n}` real-rooted for `n ≳ d^{4/3}` (quantitative GORZ, a possible side result). RH needs `n = 0`, where the untilted `Φ`-measure has relative width `O(1)` and no interlacer exists |
| 21 | Hadamard + Euler positivity at FE-reflected points (de la Vallée Poussin with partners) | CLASSICAL LIMIT | The Euler side is evaluable only for `σ > 1`; the FE relates two strip points. Gives zero-free regions of width `~1/log t` only |
| 22 | Positivity of the dual explicit-formula distribution (Guinand) | EQUIVALENT | Same Weil positivity |
| 23 | Turing index identity on the right half-rectangle: sign changes of `Z` against the argument change on three sides | CLASSICAL | Three-side argument change is controlled only by `S(T)` bounds, giving `N₊ = O(log T)`, never `0` |

**Side result worth recording (cycle 20):** a quantitative GORZ bound `N(d) ≲ d^{4/3}` via common interlacers of tilted Laguerre mixtures, if the Gaussian tails of the tilted measure can be controlled. It is not RH but is a plausible improvement over explicit `N(d)` bounds in the literature. Not pursued: it is a proportion-type result, off-target.
| 24 | Bagchi strong recurrence (RH ⟺ ζ approximates itself on right compacts) via recurrence of the Kronecker flow on the prime torus | CORPUS (BAG) + gap located | The torus identity is recurrent, but ζ at the identity is the *renormalized* continuation, not the Euler product. Transfer needs continuity of the renormalized product at the identity, i.e. control of the zeros factor `Z_X` of the Gonek–Hughes–Keating hybrid, which is circular |
| 25 | Zero-free Weil identity of `Φ_x` (empty zero side) with limit `x → 0` | TAUTOLOGICAL | The contour at vertical infinity carries the zero terms `Σ_ρ Γ(·)(πx)^{·}` (R1-L5) |
| 26 | Positivity from complete monotonicity of the Gaussian formation in `x` | KILLED (R1-L11/13) | Landau's lever globalizes |
| 27 | Canonical (maximum-entropy/Burg) Krein completions with a monotone entropy functional | EQUIVALENT | The true completion is the atomic zero measure (entropy `−∞`, deterministic process). Level entropies decrease to `−∞` regardless; Szegő theory reads only positivity |

**State after 27 cycles:** no survivor. Every tested mechanism is either killed by a named corpus gate or reduces to one of the three terminal forms: (i) level-wise Weil positivity (exponent gate at `t≈0`); (ii) local mollification at moderate heights (the short-polynomial Lindelöf regime, cycles 2–3); (iii) sub-log-sharp estimates (cycle 9 log-capacity law). The loop continues from here.
| 28 | A₂ reformulation: RH ⟺ on every right disc the seam defect is `≥ c/[|ξ|_{∂D}]_{A₂}^2`, with weight `|ξ|¹` on `∂D` (the seam factors through `F^{1/2}`: `ū = ā/a`, `|a|² = |F|`) | EQUIVALENT (new to corpus) | Petermichl gives the bound exactly when `N(D)=0`; the A₂ constant is finite whenever `ξ≠0` on `∂D`. A zero-free producer is still required. Corpus search: no Muckenhoupt / Helson–Szegő / A₂ occurrence, so the formula is a corpus addition |

**Corpus-overlap note (cycle-hygiene rule from now on):**
- Cycle 19 and the sieve/Fejér observation (R1-L14) duplicate EOC-F12 and EOC-F15/F16 (`exact-ordinate-coincidence-facts.md`).
- EOC-F17 records Zhu's `λ_min(0.8) ≈ 10^{-17}` and the doubly-exponential plunge `−ln λ_min(L) ~ 2π²N(T*)/ln N(T*)`.
- Every new cycle starts with a corpus search, per memory `search-corpus-before-claiming-novelty`.
| 29 | FE real structure on discs centered on the line: `J f(z) = conj(f(−z̄))` is antiunitary, `J² = 1`, `JP = PJ`, `J M_u J = M_u` (from `u∘σ = ū`), so the Hardy pair is `J`-real | BLIND | An antilinear involution gives real forms, not ±1 eigenspaces. Fixed zeros and swapped off-line pairs both give real forms of equal dimension, so no signature separates them (corpus: RH is 2-torsion; ℝ-structures blind) |
| 30 | Height-averaged seam defect | BLIND | Displacement-mass/averaging blindness |
| 31 | Fredholm determinant of the seam: `det(1 − H*H) = det(T_u T_ū)` (since `T_ū*T_ū + H*H = 1`) | EQUIVALENT; exact identity | Widom: for a zero-free disc with `u = e^{iφ}`, `det(T_uT_ū) = exp(−Σ_{k≥1} k|φ̂_k|²) = exp(−‖arg ξ‖²_{Ḣ^{1/2}(∂D)})`. If `N(D) ≥ 1`, `det = 0`. As an outside zero approaches `∂D`, `‖arg‖²_{Ḣ^{1/2}} ~ ½ log(1/ε)`, so `det ~ ε^{1/2}`: polynomial, while the bottom eigenvalue is `~ 1/log(1/ε)`. This ties route 1's seam exactly to its original `H^{1/2}` Gagliardo carrier (MUST-442). The producer reduces to `H^{1/2}` bounds on `arg ξ` (R1-L8 energy quantum = route LA) |

**Loop status after 31 cycles.** No survivor. New to corpus: seam log-capacity/A₂ law (8, 9, 28); shift-delay identity `∂_x L_x(s) = −πL_x(s−2)` (16); seam-determinant = `exp(−Ḣ^{1/2} energy)` (31); interlacing large-`n` side result (20). Every producer reduces to one of three named barriers:
- (B1) the exponent gate at `t ≈ 0` (MUST-250);
- (B2) the short-polynomial Lindelöf regime `2a ≪ (log t)^{2/3}` at moderate heights. Moment/large-values methods lose to the trivial bound there; see the computation in cycle 3;
- (B3) the critical-Sobolev log (H^{1/2} ↛ L^∞).

A new route must attack one of B1–B3 with a genuinely new input.
| 32 | External SOTA scan (Sept 2026) for new producer mechanisms | NO NEW MECHANISM | Pearce-Crump arXiv 2609.15329 (optimized Selberg sign-change method, ≥ 7% on the line, PSD mollifier families); Wang arXiv 2609.07918 (short-interval simple/distinct zeros via Lamzouri + BGSTB short-interval pair correlation); Yakaboylu arXiv 2408.15135 (operator form of Weil–Bombieri positivity ⇔ RH, equivalent); arXiv 2606.24924 (conditional criteria). All are proportions or equivalences |
| 33 | Falsification probe: the prime-only random model for `Σ_{n≤e^{2a}} Λ(n)n^{−1/2−it}(1−log n/2a)` predicts upper deviations `a√(2 log T)`, which exceed `½ log T` at `log T ≲ (8/3)a²`. Level-`a` positivity (sinc test functions, pole-vanishing up to `O(1/t₀)`) forbids them, since `S_N * K_a ≥ 0` is necessary. Can the resonance method prove such a deviation (⇒ RH false)? | NO CONTRADICTION | Under RH, `S_N*K_a = 2πΣ_γ K_a(t−γ) ≥ 0` and `Re(−ζ′/ζ(σ+it)) ≤ ½ log t` (Hadamard positivity): a one-sided, non-Gaussian law. The prime-only model omits the zero sum `≈ ½ log t` at scale `1/log N`. The resonance method reaches only `≍ √(log t · log log t)` for log-weighted prime sums (alignment of `p ≲ log t log log t`), and strip Ω-results are `(log t)^{1−σ}`. A falsification needs Ω₊ of size `½ log t`, i.e. an off-line zero's footprint. **Insight:** at moderate heights, level-wise positivity is exactly the one-sided upper-tail law of smoothed `−ζ′/ζ` near the line, the B2 barrier stated probabilistically |
| 34 | Rouché-type dominance in the balanced (Gaussian/Riemann–Siegel) AFE `ζ = A + χB`: termwise `|χ b_n| ≤ |a_n|` for `n ≤ N = √(t/2π)` when `σ > ½` | FALSE as a producer; exact structure found | With symmetric weights, `χB = e^{−2iθ}Σ ρ_n conj(c_n)` where `c_n = n^{−½−δ−it}w(n/N)` and `ρ_n = (n/N)^{2δ} ≤ 1`. An off-line zero needs `|Σc_n| = |Σρ_n c_n|` plus a phase condition: two real equations in `(t,δ)`, so generically possible. The modulus defect `Σ c_m c̄_n (1−ρ_mρ_n)` has kernel `11ᵀ − ρρᵀ` of signature (1,1): the Alpöge–Furman block again. First order in `δ`: `log N = Re(Σ c_n log n / Σ c_n)`, i.e. `d/dt arg(e^{iθ}A) = 0`. Off-line pairs are born exactly at stationary points of the Riemann–Siegel phase (Lehmer-pair splitting, wrong-sign extrema of `Z`), which is the Laguerre criterion (corpus) |
| 35 | One-sided sieve (Brun–Titchmarsh/Selberg) upper bounds for `Re Σ Λ(n)n^{−1/2}w(n)cos(t log n)` (B2 is one-sided) | FALSE | The sieve bounds the positive-cosine part by `≈ (4/π)√N` against the needed `½ log t`. The cancellation between the `cos > 0` and `cos < 0` regions is exactly the `ψ(x) − x` fluctuation, which no sieve sees |

**Structural pattern (cycles 19, 29, 31, 34):** every exact mechanism reads an off-line pair as a signature-(1,1) block: Weil pairs, Alpöge–Furman blocks, the balanced-AFE modulus kernel, Pick matrices. A producer must exhibit an arithmetic Hermitian form in which an off-line pair would contribute a *definite negative* block while the form is manifestly `≥ 0`. The Weil form does this only on reflection-antisymmetric test functions localized at the pair, i.e. Weil positivity itself. No arithmetic form with a definite pair block has been found. This is the sharpest statement of the missing object so far.
| 36 | Arithmetic Hermitian form with a definite-negative off-line pair block, via zero weights `(ρ−½)^k` in `Σ_ρ (ρ−½)^k F(ρ)F^#(1−ρ)` | FALSE for holomorphic weights; reduces to corpus angular-energy core | `k=1`: the sum is purely imaginary (the pair gives `2i Im((ρ−½)X)`). `k=2`: the pair gives `2Re((γ²−δ²−2iδγ)X)`, which for `γ ≫ δ` is `γ²`× the Weil pair (1,1) block. A definite block needs non-holomorphic weights (`Re ρ − ½`) or sesquilinear pairings `Σ_ρ F(ρ) conj K(ρ)`, which explicit formulas cannot produce: they give only `Σ_ρ H(ρ)` with `H` holomorphic. Same as memory `angular-energy-quantization` ("missing object = non-holomorphic self-pairing of the divisor") |

**Loop state after 36 cycles.** No survivor. The missing object has now been stated from three sides that agree:
- (i) a definite pair block (cycle 34 pattern);
- (ii) a sesquilinear zero pairing (cycle 36, the corpus angular-energy core);
- (iii) a one-sided upper-tail law for smoothed `−ζ′/ζ` near the line (cycle 33).

All three are the statement "the divisor is fixed by the reflection", read through different carriers.

Next cycles will look for any *arithmetic source* of a sesquilinear pairing: an inner-product structure whose Gram entries are computable from primes (candidates: Hilbert spaces of Dirichlet series with arithmetic reproducing kernels; Bohr/Helson spaces — gate-limited; automorphic `L²(Γ\H)` inner products of Eisenstein series, where Maass–Selberg relations are sesquilinear in the spectral parameter and are exact).

### Cycle 8 kill is now [L]
Module `RHTower.CircleLinearPhaseSeamMargin`. Wired; `lake build --old` green; axioms `propext, Classical.choice, Quot.sound`; zero warnings.
- `LinearPhaseSeam.one_sub_le_norm_sq_adjointSeam`: for `q(z) = 1 − rz`, `0<r<1` (zero-free near the closed disc), `‖(1−P)U†P‖² ≥ 1 − 2π/log(1 + π/(1−r))`.
- `LinearPhaseSeam.exists_datum_adjointSeam_gt`: for every `ε>0` some zero-free `DiscArgumentDatum` has seam norm `> 1−ε`.
- **Mechanism:** test vector `g = q^{-1/2}` (Hardy by the Cauchy lemma). Cauchy's integral formula gives the nonnegative Fourier coefficients of `U†g = conj(a)/q` as exactly `r^j conj(a(r))`, so `‖P U† g‖ = 1`. The chord bound `|1−e^{iθ}| ≤ θ` gives `‖g‖² ≥ (1/2π)log(1+π/(1−r))`.
- **Reusable assets:** `norm_sq_eq_tsum_fourierCoeff` (Parseval), `norm_sq_hardy_eq_tsum`, `hardy_eq_self_of_fourierCoeff_neg`, `norm_sq_circleLiftLp`, `seam_sq_mul_ge` (seam from any Hardy test vector), `integral_e_cauchy`.
- **Kill (Lean-certified):** no producer that uses only holomorphy and zero-freeness of the boundary phase can bound route 1's seam away from 1.
