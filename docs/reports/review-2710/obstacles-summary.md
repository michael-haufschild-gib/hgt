# Research frontier summary: work, open mathematics, next questions, and a possible new field

Status: 2026-10-27, corpus `6046e5478` with working tree. This summary covers the 31 routes, 17 candidates, PW-B and the supporting programmes of the [complete report](route-obstacles.md). Companions: [walls ledger](walls-ledger.md), [route unification](route-unification-ledger.md). Evidence: corpus search and Lean statement reading, recorded in `logs/review-2710-v4-research-log.md`. Nothing was compiled. Labels `[L]`, `[S]`, `[P]`, `[R]` and notation as in the complete report.

## 0. The frontier in twenty statements

1. **`ζ` has a computed positive form and a computed equivariant form; RH says they are one form.** `W` is Hecke equivariant with finitely many negative directions at every aperture; the collided form `D` is positive, faithful, the logarithmic Sobolev norm, computed without zero indexing; `Re W = D − Δ`.
2. **The equivariance defect of `D` is a moment of inertia, and every uniform bound on it is a zero-free strip.** `4L²M_f ≤ E_f(L) ≤ 8(cosh L − 1)M_f` [L]; an all-test, all-scale cap `E_f(L) ≤ D(f)(2cosh(2ϑL) − 2)` is the strip of width `ϑ` [S]; dyadic amplification is soft, valid for every configuration [L].
3. **RH has exact electrostatic forms, all computed and quantized.** Zero transverse energy; energy below one quantum; every unit window below two quanta; every right zero feeling a field `≤ 1` or `< √(2c log γ)`; no right terminal [L/S]. The energy of one zero is unconditionally between `1` (off-line) and `16(C + log γ)` [L].
4. **What is missing on the zero side is a non-uniform upper bound.** Every off-line zero has a terminal, an outward reserve `≥ c·a·log γ` and a zero-free lens; a uniform ceiling on terminals is a strip [S].
5. **Short prime polynomials rarely align at zero ordinates, and counting never excludes a zero.** A detector of length `(log T)^C` reaches `η log T` at `T^{1 − 1/C + o(1)}` zero ordinates in `(T, 2T]` [L]; no implication "off-line ⇒ aligned" is proved inside the strip; outside it, a deep zero forces anti-alignment of the primes at its ordinate [L].
6. **Zero-ordinate moments are Rosati pairings.** `Σ m_ρ (QQ̃)^k(ρ)` is `|Q|^{2k}` on the line and `2 Re(Q(ρ) conj Q(ρ*))^k` off it; their positivity for all `Q`, `k` is a Weil-type Hodge index [L].
7. **The rank of a counterterm is a property of the regulator, and no regulator of the prime place alone keeps positivity.** Abel radius: identity counterterm, survival `{0}`; spacing radius: scalar, Hecke covariant up to tame ramification, indefinite limit; horizon (Weil's own regulator): polar and rank one on uniform log-scale profiles, identity on the `p`-valuation classes, unbounded rank [L/S].
8. **Coupling cannot lower the torsion counterterm.** A partner pays at most as many prime directions as the rank of its own counterterm; the archimedean place, coupled through constant modes, pays exactly the arithmetic point; pole-node completion relocates a full-rank divergence to infinite node height [L/S].
9. **Covariance and survival exclude each other for diagonal counterterms.** A diagonal renormalization of the prime form is Hecke covariant iff it is scalar; the covariant counterterm is `log N + O(1)`; keeping the self-intersection costs at least another `½ log N` [S].
10. **The archimedean place pays the prime place at atomic resolution.** For log-atom tests of width `≤ N^{−O(1)}`, `arch − prime ≥ 0`, and with a rank-one pole counterterm `Re W + 2S² ≥ 0`; `Re W ≥ 0` on `|S| ≤ |C|` [L/S]. The leading constants match: covariant prime counterterm `log N` against archimedean self-energy `log(1/w)` at `w ≍ 1/N`.
11. **Below the spacing the gauge cannot favour `ζ`.** The finite intersection of every sign twin is `ζ`'s in the gauge `x ↦ ωx`, and every twin satisfies the atomic stability law [L]. The twins' Weil forms differ only through the archimedean interaction of the charged and neutral parts of a test, `M_ω(f_x) = M(f_{ωx}) + A(f⁺ + f⁻) − A(f⁺ − f⁻)`; on nonnegative atomic tests `ζ` is the minimum of its gauge orbit, by `2Λ(p)/√p` per unit mass at a flipped prime [L]. Selectivity in `ζ`'s favour must come from the pole term and from the archimedean cross kernel where it stops being dominated, at and beyond the spacing.
12. **The gauge charge of the source never collapses.** At a flipped prime the renormalized source gap is `2 log² p`, fixed by the smallest flipped prime [L]; it is a coefficient margin, not a margin on signed tests. Cell-holonomy defects grow at least like `X^{1/4}` for every sign gauge flipping `2` [L].
13. **Over `ℤ` there is no base.** Over `𝔽_q` all places act on one Frobenius ladder; over `ℤ` the ladders of distinct primes never share a pair of orders, the successor is transverse to all of them, and additive information is visible only across ladders [S]. Summing local Hodge indices in absolute value costs the square root [L].
14. **Local Hodge index holds at every prime and the self-intersection dominates each tower.** Each tower form is two-sided bounded; the renormalized torsion form is negative definite above the second level of each ladder [L].
15. **Counting is the sign over `ℤ` and proves the sign over `𝔽_q`.** Every counting currency is RH; hyperelliptic RH is proved by counting [L].
16. **One currency carries every graded reading.** Escaped Möbius decay at power `θ`, receiver rate, `Θ ≤ 1 − θ`, Hecke strip caps, dyadic growth, `Re ξ′/ξ ≥ 0` on `Re s > 1 − θ` and prefix reading rates are equivalent; unconditionally only VK rates [L/S].
17. **Unconditional positivity of `ζ` separates it from the first sign twins, permanently.** At `181/500` and `23/40`; Liouville ground eigenvalue `< −3/10` at every larger aperture [L]; no form-margin law on growing windows.
18. **One-variable positivity and deformations are exhausted.** Pole order pays inserted zeros; positive deformations detect zero-free ordinates and are irreversible; independent-ordinate packets buy at most their pole share, every finite lattice cloud a finite multiple [L/S].
19. **Escape classifies and never excludes; statistics place most zeros near the line and exclude none.** `3/4` of copies within `4/log T`, `4/5` of ordinates critical [L].
20. **Every positive mechanism stops at a threshold, and the thresholds line up [R].** Conductor horizon, atomic width versus spacing, square-root threshold, half damping, certified apertures, VK rates: below each, positivity is proved and blind; at each, the open problem begins. The spacing scale `w ≍ 1/N` is where the archimedean and prime places match, where the gauge becomes visible and where tests start to see zeros up to height `≍ N`.

## 1. Just work

Known mathematics suffices; none crosses a wall. An item's outcome may be unknown; the method is known.

| ID | Task | Content | Completion criterion |
|---|---|---|---|
| **W1** | Selectivity battery | Test each mechanism against relaxations, the golden datum and complex fake, sign/Liouville/dominated twins, height-coupled and deformed members, theta fibres, square-class kernels, torsion energies at `r < 1`, the lattice germ off its hyperplane, periodic germs, Ramanujan twins, spacing-regulated and horizon-regulated forms, valuation-class profiles, atomic tests below and at the spacing, synthetic multi-pair configurations, independent and harmonic packets. Calibrations: `κ = 1`, `κ ≥ 3`, Weil for curves, hyperelliptic RH, budget slopes, `W = D − Δ`, `E_f ≍ M_f`, equilibrium, field threshold, tower bounds, torsion cone `{0}`, partner-rank law, atomic stability law. | Each mechanism records the model that defeats it, its regulator and counterterm rank, its gauge class, and whether its positivity is collided, Rosati, local, counterterm-carried, atomic or zero-side. |
| **W2** | Finite certificates | Gram, Hausdorff, Hankel, Jensen blocks; heat transforms; schedules; finite budgets. | Every finite term certified. |
| **W3** | Premise checks | Regularity, support, decay, domains for named tests and families. | Hypotheses discharged. |
| **W4** | Transport | Restate in route coordinates: averaged and zero-ordinate positivity, horizon, forcing gap, log-Sobolev norm, negative index, reserve, census, moment-of-inertia law, field threshold, quantization, VK-rate decay, Kloosterman dispersion, alignment counts, the width currency. | Each conclusion at its true strength. |
| **W5** | Certified constants | Full floor of `ζ` at `23/40`, then past `log 5/2`; odd and primitive windows; explicit constants of the horizon, log-Sobolev, outward and field-threshold laws. | Certified finite-aperture theorems. |
| **W6** | Selectivity tables | At `23/40` the margin of each `{2, 3}` sign pattern; the `{2, 3, 5}` window; successor- and cell-built separating tests. | A margin table per window. |
| **W7** | Short windows | Selberg's near-line density on `U^{1/2+ε}`; averaged and positive-proportion positivity on `Γ^{1/2+ε}`. | The theorems on `Γ^{1/2+ε} ≤ H ≤ Γ/8`. |
| **W8** | Quadrature of readings | Replace the `z`-integrals of the theta readings by finite quadrature with explicit error. | `D`, moments, `M_f` and the detector from finitely many integers. |
| **W9** | Atomic stability up to a logarithm of the spacing | Sharp archimedean self-energy `E_φ = ‖φ‖²(log(1/w) + O(1))` (the corpus uses `e^{−1/2}`), the covariant ceiling `P_N ≤ (log N + log 4 + 4)|x|²`, and a Schur bound `‖K_φ‖ ≲ 4wN(1 + log N)` on the archimedean cross kernel in tower coordinates [R]. | `Re W + 2S² ≥ 0` on atomic tests of width `δ_N/(C log N)`; first input of Q1. |
| **W10** | Interior reading of the reserve | Express the outward reserve on a terminal's ray through the explicit formula as a lower bound for a smoothed prime sum at the terminal ordinate. | "An off-line zero of depth `a` forces a smoothed prime sum `≥ c·a·log γ` within `C log γ` of its ordinate"; first input of Q3. |
| **W11** | Counterterm constants | Leading constant of the minimal torsion counterterm, now between `3/2` and `4` (continuum model `e/(e − 1)`); `O(1)` terms of the covariant counterterm and of the atom self-energy. | `κ_min = C log N + O(1)` with explicit `C`. |
| **W12** | Overlap bookkeeping | For width `w > δ_N`, write the prime sum of a log-atom test as the finite intersection plus non-ratio lag terms; compute twins' non-ratio terms; certify `Re W + 2S²` on atomic families at widths `cδ_N` for growing finite `N`. | Exact decomposition and a certified table; second input of Q1 and Q2. |
| **W13** | Electrostatic dictionary | `𝓔` versus `𝓔_copy`; field, window energy and `M_f` in PL, HF, ACS coordinates. | One dictionary theorem per receiver. |
| **W14** | Census assembly | Simple off-line core, TTPC surplus, near-line density, multiplicity exclusion; transport. | One census theorem in receiver coordinates. |
| **W15** | Depth homogeneity | Loss law for `k`-level forms and Følner coupling. | One theorem per class. |
| **W16** | Growth inputs | VK and VK-rate escaped decay as range instances of the growth-to-forcing law. | VK as an instance of `exclusion_iff`. |
| **W17** | Contraction calculus | Quartets at depth `1/4 < a < 1/2` at `Δκ = 1`; minimum-tax theorem. | Calibrations in Lean. |
| **W18** | Corollary assembly | Averaged WL energy; one rate dictionary; LA/WD residual region; MPG/SBWF collar; conservation for infinite corrections; one capacity law; ceilings as central nonvanishing; one collided-positivity theorem; `E_D = E_Δ`; the Mertens converse under RH and `J_{−1}(T) ≪ T` (Ng); Gårding as a finite-rank survival instance; import of the Polymath de Bruijn–Newman bound. | Each from existing theorems or the literature. |
| **W19** | Working sources | The `[S]` modules at their stated strength. | Each statement completed. |
| **W20** | Charged-cell density | Import Tao's logarithmically averaged two-point Chowla theorem (`λ(a)λ(2a + 1)`, `a₁b₂ − a₂b₁ = 1`) [R, literature]: `{a : λ(a) = λ(2a + 1)}` has logarithmic density `1/2`, so the Liouville cell defect is linear along a sequence; the analogous Elliott statement for non-pretentious sign gauges. | Positive logarithmic density of charged cells; input of Q2. |
| **W21** | Alignment accounting | Combine W10 with the power-saving alignment counts and zero-density estimates. | A density theorem for deep off-line zeros at aligned ordinates; second input of Q3. |

## 2. Open mathematical obstacles

### 2.1 Tier B1: RH-strength closing statements

| ID | Statement | Routes |
|---|---|---|
| **B1.1** | **Critical signed cancellation at every positive slack.** Bounded critical deficit; one-sided lag or Abel moments; history floor; regularized abscissa `1/2`; JAS half-power budget; Mertens at square root; one-sided count; Farey sum; typicality of the gauge point `0`. | WL, MC, FU, RP, PBM, JAS, SRT, DR |
| **B1.2** | **Signed small-damping energy.** Admission at every damping; positive gauge mass; signed long-modulus quadrature; Báez–Duarte residual `→ 0`. | PM, CTF, BVI, MC, PW-B |
| **B1.3** | **Positivity of the equivariant form.** `W ≥ 0` at all apertures; zero negative index; one shift; free budget sufficient; Rosati positivity; symmetric-square spectra; nodal inequality; Suzuki first variation; global allocation; tower-coordinate Hodge index for all log-atom cycles at all widths. | RW, SZ, CHMD, EWU, OWU, ACT, AIP, TT, HF, ACS, SRT |
| **B1.4** | **Selection** from averages and proportions to every height, test and aperture. | WL, SRT, ACS, APT |
| **B1.5** | **Critical-endpoint heat and moment sign.** | LA, WD, TH, HCF, GTA, XN, PA |
| **B1.6** | **Forcing and exhaustion for a realization**, with input outside every exhausted class (invariant, non-localizing, nonnegative-test, multiplicative, square-class, one-variable, collided, below-horizon, counting, deformation, counterterm-carried, local, atomic, zero-side). | TG, RN, WD, ACS, candidates, PW-B |
| **B1.7** | **Single-currency endpoints.** BSY equality; Li floor; Robin tail; recurrence near zeros; `D_idx < 2`. | FEL, LI, RB, BAG, HF |
| **B1.8** | **RH with simple zeros.** | ACS faithful branch, WL |
| **B1.9** | **Counting forms of the sign.** | HF, ACS, AOG, SRT, WL |
| **B1.10** | **Budget currencies.** | WL, MC |
| **B1.11** | **Equivariance of the positive form.** `D` Hecke invariant; `M_f = 0` ∀`f`; dyadic defects sub-doubly-exponential; subpolynomial integer-theta readings on the dyadic schedule. | HF, ACS, PM |
| **B1.12** | **Central ceilings and chirality** at every ordinate. | ACS, SBWF |
| **B1.13** | **Field and energy forms.** Right-zero field `≤ 1` or `< √(2c log γ)`; `𝓔 < 1`; unit windows `< 2`; no right terminal; `Re ξ′/ξ > 0` on `Re s > 1/2` (Lagarias). | HF, ACS, OWU, SRT |

### 2.2 Tier B2: classical open problems weaker than RH

| ID | Problem | Where it is the next rung |
|---|---|---|
| **B2.1** | Quasi-RH: a fixed zero-free strip (e.g. `Θ ≤ 7/8`). | Every graded receiver; the width currency. |
| **B2.2** | Finite off-line index (`𝓔 < ∞`). | HF/AOG index exit. |
| **B2.3** | Simplicity of the zeros. | Faithful realizations; budgets; `𝓔` vs `𝓔_copy`. |
| **B2.4** | Density hypothesis; large values beyond Guth–Maynard. | Averaged positivity; exceptional sets of B3.24. |
| **B2.5** | `3/4` of the zeros on the line. | Census; surplus `β ≤ 1/18`; Rosati products beyond the square root. |
| **B2.6** | Power-saving sign correlations of `μ`, `λ`; two-point Chowla in natural density. | MC; SSA; charged-cell density. |
| **B2.7** | Uniform Hardy–Littlewood prime-pair correlations near the square-root band. | TTPC. |
| **B2.8** | Subconvexity and growth near `Re s = 1`. | Growth input of multiplicative forcing. |
| **B2.9** | De Bruijn–Newman bounds beyond the literature. | Shrinks the B1.5 region. |
| **B2.10** | Near-line density on windows shorter than `T^{1/2}`. | Averaged positivity on `Γ^θ`, `θ < 1/2`. |

### 2.3 Tier B3: open problems isolated by this research

No solution is known, and none is proved RH-equivalent.

| ID | Question | Present boundary |
|---|---|---|
| **B3.1** | `polarRate = Δ` when off-line zeros cluster. | Equality without clustering. |
| **B3.2** | Exclusion of infinite-height escape. | Classification complete [L]. |
| **B3.3** | Quantitative coercivity of residual reconstruction. | Algebraic injectivity. |
| **B3.4** | Signed shell flux on the moving prime-threshold ladder. | Collar bound. |
| **B3.5** | Averaged positivity on windows `Γ^θ` below the classical range. | `θ = 99/100`. |
| **B3.6** | Shared-budget calculus with prime-weighted remainder; the pole-neutralized continuum form. | Raw towers negative `≍ e^A`; joint `2, 3` payment at `23/40`. |
| **B3.7** | Arithmetic input on the residual heat region. | Model geometry complete. |
| **B3.8** | Compatible oriented families. | Spline-orbit index `≤ 1` ⇔ RH. |
| **B3.9** | Sub-half-damping signed control. | `ε = 1/2` bounded. |
| **B3.10** | Order-uniform thresholds; rank decoupled from time. | Fixed-order thresholds. |
| **B3.11** | Sharp successor constants beyond conductor 3. | `1/3`, `1/4`. |
| **B3.12** | Is the paid ideal nonzero on escape? | Excludes white noise only. |
| **B3.13** | Equality case of collar capacity at even `κ`. | Odd `κ` sharp. |
| **B3.14** | Signed near-coincidence beyond aperture `½ log Γ`. | Single-height law. |
| **B3.15** | A gauge-charged estimate for `μ` or `Λ` at `0` beyond the square-root threshold. | Haar-typical twists meet every budget. |
| **B3.16** | **Gauge form-margin.** Positivity of `ζ` separating it from every sign twin on signed tests reading growing prime windows, with a margin bounded below. | Coefficient margin `2 log² p` permanent [L]; atomic prime forms conjugate, and on nonnegative atomic tests `ζ` is the minimum of its orbit [L]; cell defects `≥ X^{1/4}` [L]; Liouville separated from `23/40` on [L]. |
| **B3.17** | Form positivity of the renormalized Rankin–Selberg source beyond isotropy. | Coefficient positivity only. |
| **B3.18** | Lower bounds or arithmetic use of the successor defect. | Mean square exact. |
| **B3.19** | Stepanov auxiliaries over `ℤ`. | Need a lattice spectrum; the arithmetic point has no period. |
| **B3.20** | The odd-sector sign beyond the conductor horizon. | Forcing gap at every height [L]. |
| **B3.21** | **A non-uniform bound on the moment of inertia**: test-dependent or averaged beyond classical density. | Uniform and one-scale caps are strips [S]. |
| **B3.22** | The full coupled class at the centre. | Positive and rational subclasses settled. |
| **B3.23** | A selective counting polarization. | Soft polarizations; inflating majorants. |
| **B3.24** | **Alignment at zero ordinates.** An implication "off-line zero of depth `a` ⇒ a short prime polynomial `≥ c·a·log γ` near its ordinate" inside the strip, and extinction of the exceptional set. | Power-saving counts [L]; exterior law at `σ > 1` [L]; Kronecker dilution [L]. |
| **B3.25** | **The spacing-scale joint estimate.** At width `w = cδ_N`, `c` fixed: `Re W + (bounded-rank correction) ≥ 0` on atomic tests, uniformly in `N`. Needs a joint bound: the prime form is large on vectors spread across multiplicative scales, the archimedean cross kernel on vectors concentrated near scale `N`. | Proved at `w ≤ N^{−O(1)}` [L/S]; expected at `δ_N/(C log N)` (W9) [R]; implied by RH. |
| **B3.26** | **The overlap regime.** For widths `w = N^{−θ}`, `θ < 1`, where atoms overlap and non-ratio lags enter: is there a positivity statement weaker than RH, what is the critical exponent, and is it gauge selective? | Open beyond the spacing; at `θ → 0` the tests are general and positivity is RH. |
| **B3.27** | **Terminal or outward upper control off a sparse set.** | Uniform terminal ceiling = strip [S]; reserve and lens [L]. |
| **B3.28** | **A Hecke-covariant regulator of the prime place whose counterterm has a nontrivial null cone** (necessarily non-diagonal, not of Abel, spacing or horizon type). | Diagonal covariant ⇒ scalar [S]; spacing covariant up to tame, indefinite [L]. |
| **B3.29** | **The base.** A Hecke-covariant positive structure across the transverse prime ladders, built from charged successor couplings, on which the local tower forms sum with a non-scaling loss. | No common ladder over `ℤ` [S]; square-root price of separate towers [L]; cells fix the gauge [S]. |

### 2.4 Settled questions

- Computation and norm of `D`; the moment of inertia; uniform and one-scale defect caps are strips.
- Electrostatic forms of RH; energy of one zero `O(log γ)`; finite equilibrium ⇔ criticality.
- Visibility of off-line zeros at their height; rarity of alignment at zero ordinates; zero moments are Rosati pairings.
- Torsion-side renormalization (survival `{0}`); spacing regulator (covariant up to tame, indefinite); horizon divergence (polar, unbounded rank on torsion orbits); coupled survival law; periodic coupling pays only the arithmetic point; pole-node completion relocates the divergence; covariant diagonal counterterms are scalar; covariant counterterm `log N + O(1)`; anomaly cost `½ log N`.
- The archimedean place pays the prime place at atomic resolution, with a rank-one pole counterterm, for every sign twin; on nonnegative atomic tests `ζ` is the minimum of its gauge orbit.
- Local Hodge index sums only at the square-root price; no common ladder; self-intersection dominates each tower.
- Gauge-charged couplings; gauge margin of the source; first gauge windows; elliptic rotations of the circle are archimedean.
- Forcing gap; escape; deformations; statistics; counting over `𝔽_q`; the width currency.

## 3. The three questions to answer next

**Selection criteria.**

1. Weaker than RH, so it can be answered.
2. Either answer changes the frontier: a positive answer adds a mechanism, a negative one is a sharp no-go naming the missing input.
3. Together the questions cover the three walls.
4. The output is not a strip, a collided positivity, a counting reformulation, a gauge-orbit statement, a one-variable system, a deformation equivalence, a zero-side detection, a prime-only renormalization or an atomic-resolution (gauge-blind) positivity.
5. The question addresses the polarization problem where it now sits: at the scale where positivity, equivariance and gauge charge first meet.

**Why these three.** The diagonal question is answered for the prime place: no regulator of it keeps positivity, coupling pays at most the partner's rank, and covariance forces a scalar. The archimedean place does pay — at atomic resolution, with matched leading constants — and the remaining renormalization question has moved to one scale, the spacing of the atoms (Q1). The same scale is where the gauge first becomes visible to Weil forms, while the source's coefficient margin is already permanent (Q2). On the zero side the counts are done and the missing link is the interior implication from an off-line zero to an aligned prime polynomial (Q3).

### Q1. The spacing scale: how far does the archimedean place pay the prime place?

> *Atomic Weil positivity holds below width `N^{−O(1)}`. Push it to the spacing: prove `Re W + (rank ≤ r correction) ≥ 0` on atomic tests of width `cδ_N` uniformly in `N` (B3.25), and determine what happens when atoms overlap: for widths `N^{−θ}`, `θ < 1`, is there a positivity statement weaker than RH, and what is the critical exponent (B3.26)?*

- **Why.**
  - The covariant counterterm of the prime place is `log N + O(1)` and the archimedean self-energy of an atom is `log(1/w) + O(1)`: the constants match exactly at `w ≍ 1/N` [S/R].
  - In tower coordinates every term is explicit: self-energy `E_φ`, polar pairing, archimedean cross kernel `K_φ(log(n/m))`, the finite intersection `Σ_p Q_p` [L]. The cross kernel at width `cδ_N` behaves like the positive Hilbert kernel `c/|n − m|` near scale `N` [R].
  - The spacing scale is the Montgomery–Vaughan regime `T ≍ N` for Dirichlet polynomials of length `N`, where large-sieve and Hilbert inequalities are sharp tools.
  - A heuristic suggests a single off-line pair loses by a factor `log T` against the mean value at `T ≍ N` [R]: the spacing-scale statement may be provable unconditionally.
- **Route.** W9 (norm estimate to `δ_N/(C log N)`); W11 (sharp `O(1)` terms); W12 (overlap decomposition and certified finite-`N` tables); then a joint estimate separating the spread (prime) and concentrated (archimedean) regimes, e.g. by a dyadic decomposition in `n` with the Schur rows of RAPT.
- **Weaker-than-RH content.** Each statement concerns a restricted `N`-dimensional family; RH implies it, no implication back is known.
- **Outcomes.**
  - *Yes at the spacing:* the first coupled renormalization at the scale where tests see zeros up to height `≍ N`; the obstruction then lies entirely in the overlap regime.
  - *Yes in the overlap regime at some `θ < 1`:* a positivity that is not atomic and may be gauge selective; the critical exponent becomes the new graded currency.
  - *No at the spacing:* the archimedean place cannot pay the prime place at its own resolution; a structure beyond the two places (a base, B3.29) is necessary, and the failing vectors name it.

### Q2. Gauge selectivity at the spacing and beyond: does the source's margin become a form margin?

> *The renormalized source of every sign twin differs from `ζ`'s by `2 log² p` at its smallest flipped prime, permanently. At atomic resolution the twins' prime forms are `ζ`'s in the gauge `x ↦ ωx`, every twin satisfies the stability law, and the Weil forms differ only by the archimedean interaction `A(f⁺ + f⁻) − A(f⁺ − f⁻)` of the charged and neutral parts — on nonnegative tests in the twin's favour. At the spacing this interaction is no longer dominated by the self-energy, and beyond it the prime sum reads non-ratio lags `log k`. Is there, for every sign gauge flipping a prime `≤ p_N`, a signed test at or beyond the spacing on which `ζ`'s form is positive and the twin's negative, with a margin bounded below as `N` grows — and can it be built from charged data (successor couplings, cells) rather than certified numerics?*

- **Why.**
  - Selectivity must come from the pole term and the archimedean place (the finite intersection is gauge blind) [L]; the archimedean cross term between charged and neutral atoms is the term that carries the gauge, and it is the same cross kernel that decides Q1 [L/R].
  - The coefficient margin exists and does not collapse [L]; the atomic margin on nonnegative tests is on the wrong side: `ζ` is the orbit minimum there [L]; signed tests are required.
  - The cell defect is unbounded for every gauge flipping `2` [L], and logarithmic density of charged cells follows from Tao's theorem [R].
  - Separation exists and persists on certified windows: Liouville fails at every aperture `≥ 23/40` [L].
- **Route.** W5, W6 (the `23/40` floor and margin tables); W12 (the archimedean charged–neutral cross term at widths `cδ_N` and the twins' non-ratio lag terms beyond); W20 (charged-cell density); compare the twin's form with `ζ`'s through the gauge-moved terms only, on signed tests whose charged part is supported on cells.
- **Outcomes.**
  - *Margin survives:* the first unconditional positivity reading non-archimedean arithmetic at every scale.
  - *Margin collapses at a measured rate:* a threshold where positivity stops seeing arithmetic.
  - *No separation at overlap widths:* gauge charge must be carried inside the form by a new structure (a base), not by widths.

### Q3. The interior anti-alignment law: does an off-line zero force alignment inside the strip?

> *Outside the strip a zero of real part `β` forces `Σ Λ(n) n^{−σ} cos(γ log n) ≤ Re(Γ-part)′ − m/(σ − β)`; inside, every off-line zero has a terminal whose outward ray carries a reserve `≥ c·a·log γ`. Does the reserve force a smoothed prime polynomial of length `(log γ)^{O(1)}` to be `≥ c′·a·log γ` at an ordinate within `C log γ` of the zero — and since such alignments occur at only `T^{1 − 1/C + o(1)}` zero ordinates, can the exceptional set be emptied by a structural argument (non-isolation, quantization, Kronecker dilution)?*

- **Why.**
  - The counting half is proved: power-saving alignment counts at zero ordinates [L].
  - The exterior half is proved: anti-alignment at `σ > 1` [L].
  - The missing link is the interior implication (W10) and then the step from counts to an individual zero, which counts alone cannot take.
  - Uniform terminal ceilings are strips [S]; only a sparse-set version is non-graded.
- **Route.** W10 (explicit-formula reading of the reserve on the outward ray, using Harnack to move it to discs); W21 (density theorem); then combine with window quantization (energy `≥ 2` in a window with an off-line zero) and with the forcing half to obtain a non-isolation law at non-exceptional ordinates.
- **Outcomes.**
  - *Implication holds and the exceptional set empties:* exclusion of isolated deep zeros at non-exceptional ordinates; a non-graded zero-side theorem.
  - *Implication holds, exceptional set persists:* a density estimate of classical type plus a sharp description of what an exceptional zero must look like.
  - *Implication fails:* off-line zeros need not align any short prime polynomial; zero-side detection cannot become exclusion by Diophantine means.

The three questions are the forcing problem in each wall's currency: Q1 at the diagonal (Wall 14, faces 14.27–14.29; Wall 3, faces 3.23–3.25), Q2 at the gauge point (Wall 1, face 1.18; Wall 3, face 3.18), Q3 at the zero side (Wall 1, face 1.21; Wall 3, face 3.19).

**Considered and not chosen.**
- **A covariant regulator with a nontrivial null cone (B3.28).** The horizon divergence is the identity on torsion orbits times `log N`, which is the shape of the archimedean self-energy: the archimedean place is the covariant counterterm, so the question reduces to Q1.
- **The base (B3.29).** The natural candidate structure is what a negative answer to Q1 would have to construct; posing it first has no computation attached.
- **A bound on `M_f` (B3.21).** Uniform versions are strips; averaged versions are density estimates.
- **The field threshold, window energy, terminal exclusion (B1.13).** RH itself.
- **The full coupled class (B3.22), `3/4` (B2.5), a selective polarization (B3.23), infinite-height escape (B3.2), Stepanov over `ℤ` (B3.19).** No candidate object, classical with a sharp reduction, or blocked by the missing period.

## 4. Would the B-tier obstacles require a new field of mathematics?

### 4.1 Assessment

No theorem shows a new field is necessary. The previous proposal — a renormalized potential theory of the characteristic circle — now exists as a programme (RAPT, with AES, AIT and RBG), and its first theorems changed the shape of what is missing:

| Ingredient over `𝔽_q` | Over `ℤ` | Status |
|---|---|---|
| Positive Hermitian structure; Frobenius a similitude | Abel torsion energies PSD, power maps similitudes up to `r ↦ r^t`; `D` positive with defect `≍ M_f` | exists, regularized [L] |
| Local Hodge index at a place | each tower form two-sided bounded; self-intersection dominates each tower | exists [L] |
| Finite self-intersection of the diagonal | regulator-dependent: Abel `{0}`, spacing scalar and indefinite, horizon unbounded rank; no prime-only regulator keeps positivity | missing on the prime side [L/S] |
| Global index = local + archimedean | archimedean self-energy pays the prime form at atomic resolution, constants matched | exists below the spacing [L/S]; open at and beyond it |
| One Frobenius ladder (base) | transverse ladders, successor transverse to all | missing [S] |
| Tensor amplification with non-scaling loss | dyadic amplification, loss `D(f)`, soft | exists, converts rates only [L] |
| Frobenius spectrum on a lattice | none at the arithmetic point | missing [L] |
| Frobenius fixes the base point | cells fix the gauge; source margin `2 log² p`; below the spacing prime forms are conjugate and `ζ` is the orbit minimum on nonnegative tests | exists structurally and on coefficients, not on forms |

A new field is likely required [R]: an **arithmetic harmonic analysis at the spacing scale**, joining the renormalization theory of the explicit formula with the mean-value theory of Dirichlet polynomials at `T ≍ N`. Arakelov theory supplies the template (an archimedean Green function regularizing the diagonal at each point); the corpus shows that over `ℤ` the regularization must be resolved at the log-spacing of the integers, uniformly in `n` (widths proportional to `1/n` reproduce the anomalous torsion diagonal, which costs `½ log N` on the pole vector [R]), and that this is exactly where the arithmetic gauge becomes visible.

### 4.2 The field: arithmetic harmonic analysis at the spacing scale

**Thesis [R].** The prime place and the archimedean place of `ℚ` regularize the same diagonal. Below the spacing of the integers the archimedean self-energy pays the prime intersection and nothing arithmetic is seen; at the spacing the two divergences match to leading order; beyond it the atoms overlap, the gauge charge enters through non-ratio lags, and the tests see the zeros. RH is the statement that the matching persists through every overlap.

**Central conjecture [R]: Hodge index at the spacing scale.** For every `N`, Weil's form restricted to the `N`-dimensional atomic family at width `cδ_N` is nonnegative up to a correction of bounded rank, with constants independent of `N`; and in the overlap regime there is a critical width exponent `θ* < 1` above which the same holds and below which positivity must use zero information.

**What it would be like.**
- **Like Arakelov theory:** Green functions on the circle and the line, self-intersections as discriminants, adjunction along towers, local Hodge index at each place, a global index needing the archimedean place.
- **Like renormalization in quantum field theory:** regulators, counterterms whose rank is a property of the regulator, survival cones, anomalies, cancellation between sectors.
- **Like large-sieve theory:** mean values of Dirichlet polynomials at `T ≍ N`, Hilbert-type inequalities with sharp constants, duality between spread and concentrated vectors.
- **Like logarithmic potential theory:** zeros as charges, the explicit formula as an equilibrium equation, quantized energy.
- **Like Diophantine approximation:** alignment of `γ log p` at zero ordinates; repulsion from the Liouville vacuum.
- **Like gauge theory:** square-class (blind) and successor/cell (charged) couplings; the arithmetic point fixed by additive structure.

**Parts already in the corpus.** Electrostatics and conjugate-diagonal geometry (AES, CDG, PL); intersection theory of the circle and tower coordinates (AE, AIT); renormalization data (RBG, RAPT); atomic stability (AES); gauge geometry (ACG, BGG, RBG, SP); zero-ordinate mean values (AES).

### 4.3 Criteria the field must meet

| Criterion | Test against the corpus |
|---|---|
| **Computability** | Forms produced by identities (explicit formula, `ξ` current, log-orders, `Λ ⋆ Λ`), not posited; counting reformulations excluded. |
| **Regulator honesty** | States its regulator and the rank and survival cone of the counterterm; reproduces Abel `{0}`, spacing indefiniteness, horizon unbounded rank, the partner-rank law. |
| **Matched constants** | Reproduces the covariant counterterm `log N + O(1)` against the self-energy `log(1/w) + O(1)`, and the anomaly cost `½ log N`. |
| **Reaches the spacing** | A positivity theorem at width `cδ_N`, not only `N^{−O(1)}`. |
| **Selectivity** | Fails for sign twins somewhere in the overlap regime; passes the W1 battery; gauge blind exactly where the corpus proves blindness. |
| **Local to global** | Reproduces local Hodge index at each prime and the square-root price of summing in absolute value. |
| **From detection to bound** | Turns a zero-side reserve into a non-uniform bound beyond classical density. |
| **Calibration** | Weil for curves (`2 − 2g`, one Frobenius ladder); hyperelliptic RH; budget slopes; `κ = 1`; `κ ≥ 3`; conductor horizon; `W = D − Δ`; `E_f ≍ M_f`; equilibrium; quantization; Gauss's digamma theorem; Fekete stability; the census. |
| **Non-circularity and uniformity** | No premise contains the conclusion; width, aperture, height and rank controlled together. |
| **New partial results** | Outputs that are not strips: spacing-scale stability, a critical width exponent, a gauge form-margin, a non-isolation law. |

### 4.4 Questions it must answer

1. How far does the archimedean place pay the prime place: to the spacing, into the overlap regime, and with what critical exponent (Q1)?
2. What is the base over `ℤ`: which positive, Hecke-covariant structure joins the transverse ladders, and is the successor its connection (B3.29)?
3. When does a form see the gauge, and does the source's coefficient margin become a form margin (Q2)?
4. Does an off-line zero force alignment of the primes inside the strip, and can the exceptional set be emptied (Q3)?
5. Which covariant regulator has a nontrivial null cone, if any (B3.28)?
6. What is the Frobenius at infinity: which correspondence acts as conjugation on the zeros, as the power map `−1` does on torsion cycles?
7. What is the arithmetic point and its period?
8. What bounds the field at right zeros below `√log γ` off a sparse set?
9. How does a quantized statistic reach every window?
10. Is the coupled class bounded at the centre (B3.22)? What selects the fibre (B3.23)?

### 4.5 Tools

**Built:** capacity identity and Hecke law of `D`; log-Sobolev norm; `ξ` current and theta readings; moment of inertia, Stieltjes moments, dyadic amplification; terminals, rays, lens, Harnack; source field; virial laws, energy, quantization, field threshold, external field law; Selberg's source and its gauge margin; log-orders, self-intersection, tower forms, square-root price, self-intersection dominance; survival law, rank dichotomy, coupled survival law, covariance law, anomaly cost, horizon polarity and unbounded rank; spacing regulator; rotations; prime functional as finite intersection; polar pairing; tower-coordinate Hodge index; atomic stability law and coupled form; gauge invisibility; zero-ordinate mean values and higher moments; zero moments as Rosati pairings; width currency; counting and budget calculus; gauge torus, cells, cell defects.

**Not yet built:**
- **Spacing-scale inequalities:** a joint estimate for the prime form and the archimedean cross kernel at width `cδ_N`; sharp constants (W9, W11).
- **Overlap calculus:** the prime sum with non-ratio lags and its gauge dependence (W12).
- **Gauge margin transfer:** from coefficient margins to signed-test margins.
- **Interior anti-alignment:** the explicit-formula reading of reserves (W10) and exceptional-set extinction.
- **A base:** a covariant positive structure across ladders.

### 4.6 Objects, language and mechanisms

| Layer | Content |
|---|---|
| **Objects** | • Atoms `log n` with widths `w`, spacing `δ_N`; atomic and overlap tests; the atomic family as an `N`-dimensional space.<br>• The finite intersection `Σ_p Q_p` on `ℓ²(⊕_p ℕ)`; tower forms; the pole vector and its polar functional; `p`-valuation classes.<br>• The archimedean self-energy `E_φ` and cross kernel `K_φ`; the polar pairing.<br>• Regulators (Abel, spacing, horizon, width), counterterms, survival cones, anomalies.<br>• The characteristic circle: torsion orbits, power maps, rotations, the arithmetic point.<br>• The zero divisor: `log\|ξ\|`, field, energy, terminals, moment of inertia; Dirichlet polynomials at zero ordinates.<br>• Gauge data: sign twins, square-class and charged couplings, cells, the source `Λ₂`. |
| **Language** | It must distinguish: below, at and beyond the spacing; separated and overlapping atoms; ratio and non-ratio lags; regulator and pairing; scalar, rank-one, identity and unbounded counterterms; covariant and anomalous; survival and covariance; local, global and base; computed, bounded and posited; detected, counted and excluded; collided and Rosati; coefficient margin and form margin; gauge blind and gauge charged; uniform (strip) and non-uniform bounds. |
| **Mechanisms to discover** | • A **spacing-scale stability law** (joint estimate).<br>• A **critical-width law** for the overlap regime.<br>• A **gauge transfer law** from coefficients to forms.<br>• An **interior anti-alignment law** and an **extinction law** for exceptional zeros.<br>• A **base law**: covariant positivity across ladders. |
| **First milestones** | (1) W9, W11: atomic stability to `δ_N/(C log N)` with sharp constants.<br>(2) W12: overlap decomposition and certified finite-`N` tables at `cδ_N`.<br>(3) W5, W6, W20: the `23/40` floor, margin tables, charged-cell density.<br>(4) W10, W21: interior reading of the reserve and the density theorem.<br>(5) W8: quadrature of the readings.<br>(6) W13, W18: dictionaries and corollaries. |

Each milestone is a theorem of a kind the corpus lacks: a positivity at the scale where tests see zeros, a selective form margin, or an implication from a zero to an arithmetic large value — not a receiver, a strip, a blindness theorem, a detection or a counting reformulation. Programme standards: **RAPT / AIT / RBG** name the regulator, the counterterm rank, the survival cone and the width; **AES / CDG / PL** name whether a positivity is atomic, collided, Rosati or zero-side and whether a bound is uniform; **ACG / BGG / SP** name the gauge class and whether a margin is on coefficients or on forms; **AE / ACP** name the currency and show it is not a form of the sign.
