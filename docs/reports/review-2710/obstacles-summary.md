# Research frontier summary: work, open mathematics, next questions, and a possible new field

Status: 2026-10-27, corpus `0bd3153ba` (clean tree). This summary covers the 31 routes, 17 candidates, PW-B and the supporting programmes of the [complete report](route-obstacles.md). Companions: [walls ledger](walls-ledger.md), [route unification](route-unification-ledger.md). Evidence: corpus search and Lean statement reading, recorded in `logs/review-2710-refresh-research-log.md`. Nothing was compiled. `[L]`, `[S]`, `[P]`, `[R]` and the notation (`W`, `D`, `Δ`, `E_f(L)`, `σ_γ`, `ζ_γ`, `ν_N`, the field `E(ρ)`) as in the complete report.

## 0. The frontier in eighteen statements

1. **`ζ` has a computed positive form and a computed equivariant form, and RH says they are one form.** Weil's form `W` is Hecke equivariant for every zero configuration and has finitely many negative directions at every aperture; its positivity is RH. The collided form `D(f) = Σ_ρ m_ρ|f̂(ρ)|²` is positive, faithful, at each aperture equivalent to the logarithmic Sobolev norm `∫|f̂|² log(|σ| + 4)`, and computed without zero indexing by the current `Δ log|ξ|` and polynomially many integer theta values [L]. Its Hecke equivariance is RH. `Re W = D − Δ`.
2. **What is missing is an inequality, not a computation.** The computations evaluate the Hecke defect `E_f(L) = Σ m_ρ(2cosh(2δ_ρL) − 2)|f̂(ρ)|²` and detect zeros locally; nothing bounds `E_f` above by a quantity that vanishes. `E_D = E_Δ` [R].
3. **An off-line zero leaves a computable trace at its own height, and the trace detects without excluding.** Every off-line zero has, within `C log γ`, a locally rightmost terminal zero whose transverse field (the field of all other zeros) is positive and whose zero-free outward ray carries the reserve `Re(ζ′/ζ + Γ-part) ≥ m/h + m/(2a + h) + c·a·log γ` [L/S]. The Rankin–Selberg square `(ζ′/ζ)² = L(Λ ⋆ Λ)` computes that field as its simple Laurent coefficient; critical configurations are in transverse equilibrium [L].
4. **Every unconditional positivity found is invariant, averaged or statistical, non-localizing, on nonnegative tests, collided, twisted below the conductor horizon, a finite-window certificate, positive before a renormalization, or a zero-side reserve.**
5. **Multiplicative symmetry is hyperbolic exactly at off-line pairs; elliptic localization inside correspondence-closed carriers is resonance; the only reflection-compatible affine localizer is `σ_γ`; the spectrum of symmetric squares at one prime is the critical line.**
6. **The forcing gap is a theorem, and both zero-side detectors meet the same Diophantine question.** The companion certificate needs `e^{2δa} > 768A log(|γ| + 3)` and is disjoint from the conductor horizon at every height [L]. Beyond the horizon the detector's prime side is a polynomial of length `(log γ)^{O(1)}` at the zero's ordinate; the outward reserve is a large value of a short prime sum at the terminal's ordinate. Both ask whether `γ log p` can align modulo `2π` for small `p` at zero ordinates [R].
7. **Counting is the sign over `ℤ` and proves the sign over `𝔽_q`.** Over `ℤ` section counts, effectivity, naive and convex heights, one-sided counts, a fixed tensor loss, horizon torsion and the Farey sum are each RH; Stepanov auxiliaries need a lattice spectrum, which no sparse correspondence produces off the line. Over `𝔽_q` the corpus proves RH for odd-degree hyperelliptic curves, split or not, by counting [L].
8. **The prime-error budget is RH; with its Abel slope at the genus it is RH with simple zeros.** Both directions are proved [L]. A Mertens budget forces RH, simple zeros and summable residues; its converse is classical only under an additional residue-growth hypothesis. Over `𝔽_q` the slopes count the spectrum.
9. **`Λ` is an intersection number of torsion cycles; the prime kernel is a renormalized positive energy.** Positivity is lost exactly in the divergent diagonal self-energy [L].
10. **One diagonal, three appearances [R].** Weil's self-intersection `Δ·Δ = 2 − 2g`, the torsion self-energy `log(1/(1 − r))`, and the double pole `m²/(s − ρ)²` of `(ζ′/ζ)²` are self-terms; removing each leaves the content (the trace, the prime kernel, the field).
11. **Multiplicative data see orbits, not the point; positivity already sees the first two primes.** Unconditional positivity of `ζ` separates it from the Liouville twin at `181/500` and from the first non-archimedean twin at `23/40` [S]; gauge-charged boundaries normalize at weight `1/4`.
12. **Every amplification over `ℤ` tested loses linearly, and twists are rate neutral.**
13. **No graded receiver has a rung between Vinogradov–Korobov and a fixed strip.**
14. **One-variable positivity is exhausted, and its cone is classified.**
15. **Deformations detect, they do not force.** Positive rigidity, chirality and central ceilings at `γ` are each the absence of (off-line) zeros at `γ`; at zero-free ordinates the surplus residue of an arithmetic member is an even central drop `≤ 2 ord_{1/2+iγ} ξ` [L].
16. **Escape classifies and never excludes.** RH is positive gauge mass of every escape state.
17. **Statistics place most zeros near the line and exclude none.** Unconditionally `3/4` of the zero copies in `(T, 2T]` lie within `4/log T` of the line and `4/5` of the zero ordinates carry a critical zero; the `3/4`-on-the-line problem is a bound on simple off-line zeros near the line [L].
18. **Excluding an individual zero needs control below the zero spacing**: averages, proportions and almost-every statements do not reach it.

## 1. Just work

Known mathematics suffices for each item, and none crosses a wall. An item's outcome may be unknown; what is known is the method.

| ID | Task | Concrete content | Completion criterion |
|---|---|---|---|
| **W1** | Selectivity battery | Test every mechanism against:<br>• pole-order-2/3 relaxations, strip-pole quartets, over-regular Beurling systems, the Siegel family, twisted boundary systems;<br>• the golden datum and the complex fake;<br>• the Liouville, `{2,3}`-flipped, sign-flipped and dominated twins; Haar-typical and Kronecker twists; shifted pairs `ζ(s − a)ζ(s + a)`;<br>• height-coupled lifts, `W_β`-split members, Fejér-coupled systems, rational and positive deformations, arithmetic members with square-root deficit;<br>• theta-surface fibres at `a ≠ 0`; Jacobi–Hurwitz packets; polar configurations with incommensurable leading lines;<br>• torsion energies at `r < 1`; white noise, reset-origin mixtures, translated-zero eigenstates, Abel atoms;<br>• synthetic configurations with several off-line pairs of different depths (sign of the field off the deepest pair).<br><br>Calibrations to reproduce: κ = 1 collapse; `⌊k/2⌋` capacity; Fejér barrier; `κ ≥ 3`; Weil for curves with budget `2g`; hyperelliptic RH by counting; prime-error slope `Σ mult²` and Mertens slope = repulsion energy; `ℙ¹ × ℙ¹` effectivity; `W = D − Δ`; local Weyl law; transverse equilibrium of critical configurations. | Each mechanism records the model that defeats it, its local type, whether its positivity is collided, Rosati, pre-renormalization or zero-side, and whether its counting polarization is fibre-selective. |
| **W2** | Finite identities and certificates | Gram, Hausdorff, Hankel, Jensen blocks; finite heat transforms; schedules and histories; finite Robin, Li, JAS and Vaughan budgets. | Every finite term certified; no cofinal claim. |
| **W3** | Premise checks | Regularity, support, decay and domain membership for named tests and families (SZ limits, CHMD domains, candidate sources, twisted detectors). | Hypotheses of existing transfers discharged. |
| **W4** | Transport of proved inputs | Width functor; RW↔SZ↔CHMD; HF→AIP; Weil margin → heat window. Restate in RW, SZ, CHMD, EWU, OWU, ACT, AIP, HF coordinates: averaged and positive-proportion positivity, the off-line field, zero-ordinate positivity, the short-cycle split, the conductor horizon, the forcing half and gap, the log-Sobolev equivalence and local Weyl law, the finite negative index with its explicit bound, the outward reserve, the census. | Each conclusion stated at its true strength. |
| **W5** | Certified extensions and constants | Push the full floor of `ζ` beyond `181/500` (`23/40` is W13; then past `log 5/2`); odd and primitive windows. Make explicit `κ₀, C₀, Γ₀`, `sharpCollarConst κ`, the constant `C` of the conductor horizon, the log-Sobolev constants `c_A, C_A` and the outward constants `C, c`. | Certified finite-aperture theorems. |
| **W6** | Short windows to the classical range | Selberg's near-line density is formal on windows `≥ U^{99/100}`; extend it to `U^{1/2+ε}` (Selberg's classical range) and replace `Γ^{99/100}` by `Γ^{1/2+ε}` in the averaged, off-line-field, zero-ordinate, positive-proportion theorems and in WL's filtered deficit. | The theorems on `Γ^{1/2+ε} ≤ H ≤ Γ/8`. |
| **W7** | Corollary assembly | (i) An averaged bounded-energy statement for WL.<br>(ii) One rate dictionary for RW, SRT, ACS through `groundRate = polarRate`, including the non-clustering equality.<br>(iii) The explicit LA/WD residual region.<br>(v) Replace the imported `c/(log\|t\|)^9` collar by the MPG or SBWF calibration.<br>(vi) Conservation for infinite reflection-antisymmetric corrections.<br>(vii) One capacity law: boundary, collar, gauge, family, Abel–Gram line capacity, `ζ^d` boundary capacity.<br>(xi) The full-class ceiling at zero-free ordinates as central nonvanishing.<br>(xii) One collided-positivity theorem: kernel counts, coupled counts, escape Cauchy forms, `D`, depth profile, with the Hecke law.<br>(xiv) `E_D = E_Δ` and the `ξ`-current formula for `E_f(L)` in PL and HF coordinates.<br>(xv) The Mertens converse under RH, simple zeros and `J_{−1}(T) ≪ T` (Ng's method).<br>(xvi) Transverse equilibrium on the actual divisor: `Re E(ρ) = 0` at critical simple zeros, `Re E > 0` at a deepest off-line zero, from the finite-configuration law and the witness.<br>(xvii) The quantization law and ceiling transfer in ACS coordinates: the surplus residue as an even central drop. | Each statement proved from existing theorems. |
| **W9** | Depth homogeneity, remaining classes | The loss law for `k`-level forms and Følner coupling. | One theorem per class. |
| **W10** | Range-limited growth inputs | State the VK step as a `δ`-range instance of `exclusion_iff`. | VK as an instance of the growth-to-forcing law. |
| **W11** | Contraction calculus, last items | (i) Whether a complex quartet at depth `1/4 < a < 1/2` contracts at `Δκ = 1` with the boundary pole as anchor. (ii) A minimum-tax theorem for arbitrary finite rational multipliers. | Each statement in Lean as a calibration. |
| **W12** | Integration of working sources | SelectivePositivity (six modules); the terminal-field and witness modules of the outward field. | Each statement at its stated strength in an umbrella. |
| **W13** | The two-prime window | Certify the full-sector floor of `ζ` at `23/40` and compute `inf (W_ζ(F) − W_λ(F))/‖F‖²` over odd separating tests there; repeat for every sign pattern on `{2, 3}`. | `ζ` positive on the whole `23/40` window with an explicit floor, and the margin table of the four sign twins. |
| **W14** | Quadrature for the conjugate-diagonal readings | Replace the continuous source integrals of the polynomial theta metric and of the local detector by finite quadrature with explicit error, using the strip amplitude bounds and the fixed-strip cutoff. | `D`, its depth moments and the local detector from finitely many integer theta values. |
| **W15** | Moments of the odd detector over zero ordinates | Compute `Σ_{0<γ≤T} P_a(γ)^{2k}` for the detector's prime polynomial `P_a` with the formal smoothed Landau formula (`exists_smoothedLandau_le`); derive the exceptional-set bound for `P_a(γ) > (1 − η) log γ`. | Moment and exceptional-set theorems for `e^{2a} ≤ (log T)^{C}`; first input of Q1. |
| **W16** | Torsion counterterms on finite sets of orders | For finite `S ⊂ ℕ`, compute the minimal diagonal counterterm `C_r(S)` making `G∘T_r − C_r` positive and converging to the atomic Weil form; compare with the archimedean self-energy at scale `1 − r`. | A table of `C_r(S)` and its divergence rate; the input of Q2. |
| **W17** | The three-prime window | Extend the selectivity law to windows reading `{2, 3, 5}` (`2A > log 5`). | A certified three-prime selectivity battery. |
| **W18** | The prime reading of the outward reserve | Express the reserve at a terminal through the explicit formula on its zero-free ray: a lower bound `≥ c·a·log γ` for a smoothed prime sum `−Re Σ Λ(n) n^{−σ−iγ_p} k(log n)` at the terminal ordinate, with explicit length; compute its moments over terminal ordinates with W15's tools. | A theorem "an off-line zero of depth `a` forces a large smoothed prime sum within `C log γ` of its ordinate"; second input of Q1. |
| **W19** | Census assembly | Combine the simple off-line core with the TTPC surplus, Selberg's near-line density and the multiplicity exclusion: state the `3/4` problem as a bound on simple off-line zeros within `4/log T`, and transport the census to RW, WL, ACS receivers. | One census theorem in receiver coordinates. |

W8 (the edge eigenproblem at `181/500`) is settled by an explicit negative witness [S]. W7(xiii) (the lower log-Sobolev bound) is proved [L]; the prime-error half of the former W7(xv) is proved [L].

## 2. Open mathematical obstacles

### 2.1 Tier B1: RH-strength closing statements

Each is equivalent to RH or stronger. Solving one closes every route that uses it.

| ID | Statement | Routes |
|---|---|---|
| **B1.1** | **Critical signed cancellation at every positive slack.** Bounded critical deficit energy; one-sided lag or Abel moments; the history floor; the regularized abscissa `1/2`; the JAS half-power budget; Mertens at square root (`ν̂_N(1)`); the one-sided count; the Farey sum at `√N` precision; typicality of the gauge point `0`. | WL, MC, FU, RP, PBM, JAS, SRT, DR |
| **B1.2** | **Signed small-damping energy.** Admission at every damping; subpower receiver energy; positive gauge mass of every escape state; signed long-modulus quadrature; a Báez–Duarte residual `→ 0`. | PM, CTF, BVI, MC, PW-B |
| **B1.3** | **Positivity of the equivariant form.** `W ≥ 0` at all apertures; zero negative index at every aperture; the one-sided Weil inequality at one prime; one shift; sufficiency of the free budget; Rosati positivity; nonnegative symmetric-square spectra; the nodal inequality; positive Suzuki first variation; odd capacity; global allocation; Bézout on the exact source cone. | RW, SZ, CHMD, EWU, OWU, ACT, AIP, TT, HF, ACS, SRT |
| **B1.4** | **Selection.** From short-window averages, positive proportions and almost every zero ordinate to every height, signed test and aperture. | WL, SRT, ACS, APT |
| **B1.5** | **Critical-endpoint heat and moment sign.** Residual heat region; all-rank Hankel positivity at one time; both heat grids; rank-uniform Schur decay; the Newton margin; order-uniform passivity. | LA, WD, TH, HCF, GTA, XN, PA |
| **B1.6** | **Forcing and exhaustion for a realization.** Exhaust the maximal blind ideal with an input outside the exhausted classes (invariant, non-localizing, nonnegative-test, multiplicative, one-variable, collided, twisted-below-horizon, counting, deformation, pre-renormalization, zero-side reserve). | TG, RN, WD, ACS, all candidates, PW-B |
| **B1.7** | **Single-currency endpoints.** BSY contrast equality; the subexponential Li floor; the eventual Robin tail; recurrence near possible zeros; `D_idx < 2`. | FEL, LI, RB, BAG, HF |
| **B1.8** | **RH with simple zeros.** Faithful positive Meyer degree; RR for the Hilbert–Schmidt reserve; the Abel slope at the genus. | ACS/Meyer faithful branch, WL |
| **B1.9** | **Counting forms of the sign.** Effectivity function; no abundant class; naive heights; convex heights; fixed tensor loss; section count; horizon torsion; the Farey sum. | HF, ACS, AOG, SRT, WL |
| **B1.11** | **Equivariance of the positive form.** `D` Hecke invariant; one Hecke translation a similitude of `D`; `E_f ≡ 0`; `Δ ≡ 0`; `W = D`. | HF, ACS, PM |
| **B1.12** | **Central ceilings and chirality.** Rational or positive central ceilings, or positive chirality, at every `γ ≠ 0` (each RH, ordinate by ordinate [L]); the full-class ceiling at every `γ` (implies RH; converse open, see B3.34). | ACS, SBWF |
| **B1.13** | **Budget currencies.** A linear prime-error budget (⇔ RH); a Mertens budget (⇒ RH + simple + summable residues); the Abel slope at the genus (⇔ RH + simple). | WL, MC |
| **B1.14** | **The field form.** No zero feels an outward transverse field (`Re E(ρ) ≤ 0` at every zero; ⇔ RH, since every off-line zero has a terminal with positive field [S]); or an arithmetic upper bound for `Re(ζ′/ζ + Γ-part)` on every terminal's outward ray below its reserve. | HF, ACS, OWU, SRT |

### 2.2 Tier B2: classical open problems weaker than RH

| ID | Problem | Where it is the next rung |
|---|---|---|
| **B2.1** | Quasi-RH: a fixed zero-free strip. | Every graded receiver; admission at fixed damping; energy growth; one-sided Lefschetz bounds; escaped Möbius pairings at a fixed `θ`; large-sieve section supply. |
| **B2.2** | Finite off-line index. | HF/AOG index exit; WD collision masses. |
| **B2.3** | Simplicity of the zeros. | Operator-norm faithful realizations; Mertens budgets; the Abel slope. |
| **B2.4** | Density hypothesis; large values beyond Guth–Maynard. | Averaged positivity at larger aperture; filtered deficit; the computed Hecke defect (B3.33); exceptional sets of B3.36. |
| **B2.5** | At least `3/4` of the zeros on the line. | The census reduces it to a bound on simple off-line zeros within `4/log T` (TTPC, W19): surplus `β ≤ 1/18`; parity-breaking dispersion. |
| **B2.6** | Power-saving sign correlations of `μ`, `λ`. | MC anti-alignment; SSA constants. |
| **B2.7** | Uniform Hardy–Littlewood prime-pair correlations near the square-root band. | TTPC; near-incidence beyond the threshold. |
| **B2.8** | Subconvexity and growth near `Re s = 1`. | KKL horizon; growth input of multiplicative positivity. |
| **B2.9** | Better de Bruijn–Newman bounds. | Shrinks the B1.5 region. |
| **B2.10** | Near-line density on windows shorter than `T^{1/2}`. | Averaged positivity on windows `Γ^θ`, `θ < 1/2` (B3.7). |

### 2.3 Tier B3: open problems isolated by this research

No solution is known, and none is proved RH-equivalent.

| ID | Question | Present boundary |
|---|---|---|
| **B3.1** | Physical-`L²` rate equality `polarRate = Δ` when off-line zeros cluster. | Equality when off-line copies or depth mass are locally bounded [L]; form-norm rate `= Δ` unconditionally. |
| **B3.2** | **Exclusion of infinite-height escape for `ζ`**: tightness of the exterior spectral mass of the actual receiver. | Classification complete [L]. |
| **B3.3** | Quantitative coercivity of residual/trace reconstruction. | Algebraic injectivity; kernel `ℝ q_ε`. |
| **B3.6** | Signed shell flux along the moving prime-threshold ladder. | Birth jumps vanish; collar bound. |
| **B3.7** | Averaged positivity on windows `Γ^θ` below the classical range. | `θ = 99/100` proved; `θ > 1/2` is W6. |
| **B3.8** | A nonlocal shared-budget calculus with prime-weighted remainder. | Frustration and descent laws; polar-neutral collapse; raw continuum towers negative at order `e^A` [S]; joint `2, 3` payment at `23/40`. |
| **B3.9** | Arithmetic input on the residual heat region. | Model geometry complete. |
| **B3.10** | Compatible oriented families. | Spline-orbit index `≤ 1` ⇔ RH. |
| **B3.11** | Sub-half-damping signed control of the forward interior. | Exterior paid; `ε = 1/2` bounded. |
| **B3.12** | Order-uniform PA thresholds; decoupling rank from time. | Fixed-order thresholds. |
| **B3.13** | Sharp successor constants beyond conductor 3. | Odd shifts `1/3`, lag 2 `1/4`. |
| **B3.16** | Is the paid ideal nonzero on escape? | Would exclude white noise, not translated-zero states. |
| **B3.18** | Equality case of collar capacity at even `κ`. | Odd `κ` sharp. |
| **B3.20** | Signed near-coincidence cancellation at one height beyond aperture `½ log Γ`. | Single-height phase-selective law. |
| **B3.24** | An unconditional nontrivial estimate for a gauge-charged statistic of `μ` or `Λ` at the point `0` beyond the square-root threshold. | Haar-typical twists meet every budget; charged boundaries normalize at `1/4`. |
| **B3.26** | **The non-archimedean gauge charge**: positivity of `ζ` separating it from every sign twin on growing prime windows, with a margin that survives aperture growth. | First two windows separated [S]; multi-prime repulsion [L]; successor-square separator [S]. |
| **B3.28** | **Positivity of the Rankin–Selberg source `Λ ⋆ Λ` beyond isotropy.** | `(ζ′/ζ)² = L(Λ⋆Λ)` [L]; its simple Laurent coefficient is `2m` times the field of the other zeros; critical configurations are in equilibrium, the deepest off-line zero feels a positive field [L]; off the deepest pair the field has no sign. |
| **B3.29** | Lower bounds or arithmetic use of the successor defect `D_Λ` on vertical lines. | Pointwise `(\|s\| + 1)^{1−σ+η}`; mean square exact [L]. |
| **B3.30** | Stepanov auxiliaries over `ℤ` outside the one-prime Hecke algebra. | Hyperelliptic RH by Stepanov [L]; sparse annihilators need a lattice spectrum [L]; the integrality floor stops below PNT; the arithmetic point has no period. |
| **B3.32** | **The odd-sector sign beyond the conductor horizon** at the ordinate of a hypothetical off-line zero. | Forcing half [L]; horizon [L]; gap at every height [L]; reduces to B3.36 [R]. |
| **B3.33** | **An inequality for the computed collided form**: a prime-side or theta-side upper bound for `E_f(L)` that is not a classical density estimate. | `D` computed and detected locally [L]; `E_f(L) ≤ k(L, 1/2) D(f)` and the two-scale law only [L]; `E_D = E_Δ` [R]. |
| **B3.34** | **The full coupled class at the centre**: at zero-free ordinates, does every member of `HeightCoupledSystem 2 1 1 γ` satisfy the ceiling? | Positive and rational subclasses settled [L]; surplus residue = even central drop `≤ 2 ord ξ` for zero-residue arithmetic members [L]; ceiling transfers to factors [L]. |
| **B3.35** | **A selective counting polarization**: counts of rank growing with the class, fibre-dependent, equal to the Rosati form at the fibre of `ζ`. | Theta surface soft; lattice counts collapse; large-sieve majorants inflate [S]. |
| **B3.36** | **Kronecker alignment at zero ordinates.** Can `γ log p` (small `p`) align modulo `2π` at the ordinates of zeros so that a short prime polynomial reaches `(1 − η) log γ` (detector) or `c·a·log γ` (outward reserve), except on a set sparse enough for zero-density estimates? | Generic heights: large deviations of random phases [R]; zero ordinates: smoothed Landau formula [L], moments not computed (W15, W18); multi-prime repulsion bounds alignment with the Liouville vacuum [L]. |
| **B3.37** | **Positive renormalization of torsion energies.** A Hecke-compatible counterterm, paid by the archimedean and polar terms, under which the atomic Weil form is a limit of positive torsion forms? | `G∘T_r ≥ 0`; renormalized limit = minus prime kernel + log-discriminant [L]; finite-set counterterms are W16. |
| **B3.38** | **Outward upper control off a sparse set**: an arithmetic upper bound for `Re(ζ′/ζ + Γ-part)` on outward rays of terminals, below `c·a·log γ`, outside a set of ordinates sparse enough to exclude isolated deep zeros. | Reserve and terminals [L/S]; under RH `‖ζ′/ζ‖ ≤ C log γ/(σ − 1/2)` [L]; same Diophantine content as B3.36 [R]. |

### 2.4 Settled questions

- **What computes `D`, and which norm it is.** The `ξ` current and polynomially many integer theta values; the logarithmic Sobolev norm at each aperture; local zero detection by the same readings.
- **Whether an off-line zero is visible at its own height.** Yes: a terminal with positive field and an outward reserve.
- **Whether the prime-error budget is weaker than RH.** No: equivalent; at the genus with simple zeros.
- **The forcing gap.** Proved at every height; the certificate splice is dead.
- **The first gauge-charged windows.** Separated at `181/500` and `23/40` [S].
- **Escape.** Classified completely, including the infinite-height cases.
- **Positive and rational deformations of the coupled carrier.** Rigid exactly at zero-free ordinates; surplus residues quantized as even central drops.
- **How far statistics reach.** `3/4` of the zero copies within `4/log T`; `4/5` of the ordinates critical.
- **Counting over `𝔽_q`.** Hyperelliptic RH by Stepanov and Gauss sums, split case included.
- **Also settled:** kernel counts as heights (no: the complex fake); section counts, effectivity, naive heights, one-sided counts and tensor bases are the sign; elliptic localization in correspondence-closed carriers is resonance; symmetric-square spectra are the sign at one prime; contraction and collision calculus; positive polar-configuration cone; theta `h⁰` does not extend; multiplicative lattice forms blind; the first gauge charge is a twist; theorem of the square and budget free; positivity beyond isotropy only without localization; κ = 1 class; Lefschetz receivers at one and two primes; linear loss; twists rate neutral; averaged positivity at `Γ^{99/100}`; absolute pole-order budget false.

## 3. The three questions to answer next

**Selection criteria.**

1. The question is weaker than RH, so it can be answered.
2. Either answer changes the frontier: a positive answer adds a mechanism; a negative answer is a sharp no-go naming the missing input.
3. Together the questions cover the three walls.
4. The output is not a zero-free strip, a collided positivity, a counting reformulation, a gauge-orbit statement, a one-variable positive system, a deformation equivalence or a zero-side detection.
5. The question addresses the polarization problem in its present form: a form that is positive and equivariant at once, or an inequality that turns a detection into an exclusion.

**Why these three.** What computes `D` is answered and an off-line zero is now visible at its own height through two detectors; both detectors need the same Diophantine input, so alignment is the sharpest open question with a concrete toolkit (the smoothed Landau formula). Torsion energies are positive before a renormalization and equivariant after it, and the same diagonal renormalization produces the field in `Λ ⋆ Λ`; the adjunction is the concrete form of the polarization problem. The first two gauge-charged windows separate `ζ` from its twins; persistence decides whether positivity reads arithmetic at all scales.

### Q1. Alignment at zero ordinates: can either zero-side detector be turned into an exclusion off a sparse set?

> *At the ordinates of zeros, can a short prime polynomial be Kronecker-aligned — `P_a(γ₀) = Σ_{n ≤ e^{2a}} Λ(n) n^{−1/2} cos(γ₀ log n) k_a(log n)` reaching `(1 − η) log γ₀` for apertures between the conductor horizon and the forcing threshold, or the smoothed prime sum at a terminal ordinate reaching the outward reserve `c·a·log γ` — for every zero, or only on a set sparse enough that zero-density estimates exclude it?*

- **Why.**
  - The odd sector of `σ_γ` is the only localizing sector whose positivity forces; the gap between horizon and threshold is a theorem, so the remaining route through it is a sign beyond the horizon at zero ordinates.
  - The outward field gives a second, independent entrance: every off-line zero forces, within `C log γ`, a terminal whose outward ray carries a reserve of order `a log γ` [L]; through the explicit formula the reserve is a large value of a short prime sum at that ordinate (W18).
  - Both entrances ask whether `γ log p` can align modulo `2π` for small `p` at zero ordinates. Random phases give `≈ log X`; Landau's formula `Σ_{γ≤T} x^ρ = −TΛ(x)/(2π) + O_x(log T)` makes sums over zero ordinates explicit, and the corpus has its smoothed form [L].
  - Multi-prime repulsion bounds how closely `γ log p` can align with the Liouville vacuum [L] — the alignment the reserve requires.
- **Route.**
  1. W15: moments `Σ_{γ≤T} P_a(γ)^{2k}` and the exceptional set `E_T = {γ ≤ T : P_a(γ) > (1 − η) log γ}`.
  2. W18: the prime reading of the reserve and its moments over terminal ordinates.
  3. Compare `|E_T|` with `N(1/2 + δ, T)` and with the local count of the forcing half; iterate the forcing half outside `E_T`.
- **Weaker-than-RH content.** A non-isolation law: an off-line zero of depth `δ > 1/(2θ)` whose ordinate lies outside the exceptional set has an off-line companion within `(log γ)^θ`; from the outward side, deep off-line zeros at non-exceptional ordinates are excluded outright.
- **Outcomes.**
  - *Yes (all ordinates or outside a sparse set):* the first localizing mechanism that forces, and a theorem excluding isolated deep off-line zeros at non-exceptional ordinates.
  - *No:* zero ordinates can be aligned with the first primes; zero-side detection cannot be turned into exclusion by Diophantine means, and forcing must come from a renormalized or computed polarization (Q2).

### Q2. Arithmetic adjunction: does a positive renormalization of the diagonal produce Weil's form?

> *The torsion energies `G∘T_r` (`r < 1`) are positive semidefinite on finitely supported vectors over the orders; their limit is minus Weil's prime kernel plus the log-discriminant, with a divergent self-energy `log(1/(1 − r))`. Is there a counterterm — computed from the archimedean place and the pole, compatible with the Hecke law `I(m, mt) = φ(m)Λ(t)` — whose subtraction keeps the torsion forms positive and whose limit is Weil's atomic form?*

- **Why.**
  - Torsion energies are positive (`r < 1`) and Hecke equivariant (`r = 1`) in one family; the two properties separate only at the diagonal [L].
  - The same diagonal carries the content elsewhere [R]: the double pole of `(ζ′/ζ)² = L(Λ ⋆ Λ)` is the self-term whose removal leaves the field; Weil's self-intersection `2 − 2g` is the finite self-term over `𝔽_q`. A positivity-preserving renormalization of one is a candidate for the others.
  - Weil's archimedean kernel diverges like `log(1/ε)` at the diagonal, as the torsion self-energy diverges like `log(1/(1 − r))` [R]. The question is whether these divergences cancel in a positivity-preserving, Hecke-compatible way.
- **Route.**
  1. W16: minimal counterterms `C_r(S)` on finite sets of orders; their divergence rate.
  2. Compare `C_r(S)` with the archimedean self-energy of atomic tests at matched scale, and with the polar term.
  3. Test Hecke compatibility with the power maps `z ↦ z^t`; test the same counterterm on the Laurent self-terms of `Λ ⋆ Λ`.
- **Weaker-than-RH content.** Positivity of the renormalized form on vectors supported in a fixed finite set of orders is a finite statement; a counterterm on one Hecke orbit `{m, mp, mp², …}` is a one-prime statement to compare with the Lefschetz receivers.
- **Outcomes.**
  - *Yes:* a computed form that is positive and equivariant up to an explicit counterterm; the polarization problem becomes one inequality between arithmetic and archimedean self-energies.
  - *No:* every positivity-preserving counterterm breaks the Hecke law; positivity and equivariance cannot be joined through torsion cycles of the characteristic circle, and a two-variable carrier is necessary.

### Q3. Gauge persistence: does unconditional positivity of `ζ` keep separating it from its sign twins as primes enter?

> *For windows reading the first `N` primes, is there, for every real sign gauge `ω` differing from the Euler vacuum on `{p ≤ p_N}`, an explicit test on which `ζ`'s form is positive and the twin's form negative, with margin bounded below by an explicit function of `N` — and can the separating tests be built from successor data rather than certified numerics?*

- **Why.**
  - A `ζ`-specific sign must use gauge-charged data. The first two windows separate `ζ` from its twins [S]; from the second prime on the charge is not archimedean [L].
  - Archimedean twists approach the Liouville vacuum at most stretched-exponentially fast [L]; the off-line field costs `e^A` at aperture `A`. A margin law decides whether positivity reads the gauge point at all scales.
  - The successor connection reconstructs prime phases from consecutive integers; the successor-square form separates the Liouville twin from every scale twist without archimedean input [S].
- **Route.** W13, W17 (two- and three-prime windows with margins); the margin as a function of `N` and `A`; successor-built tests through Catalan links (`2 → 3 → 4`, `3 → 4 → 5`, `8 → 9`).
- **Outcomes.**
  - *Separation with a surviving margin:* the first unconditional positivity that reads non-archimedean arithmetic at every scale.
  - *Separation with a collapsing margin:* a measured threshold where positivity stops seeing arithmetic.
  - *No separation beyond some `N`:* a sign twin indistinguishable from `ζ` by unconditional positivity on every certified window; additive (successor) input is necessary.

The three questions are the forcing problem in each wall's currency:
- Q1: what a localized sign or a zero-side reserve at one height can force (Wall 3, faces 3.19 and 1.21; Wall 1, face 1.3).
- Q2: whether a positive form and an equivariant form become one form through renormalization of the diagonal (Wall 14, faces 14.18, 14.21, 14.24, 14.26; Wall 1, face 1.16).
- Q3: whether positivity carries non-archimedean gauge charge at every scale (Wall 1, face 1.18).

**Considered and not chosen.**
- **An upper bound for the computed Hecke defect (B3.33).** Uniform in `L` it is a graded rate; at `L ≍ log T` for every height it is RH-strength; averaged over heights it is a classical density estimate. A non-classical bound needs a structure the computation does not supply — the object of Q2.
- **The field form (B1.14) directly.** RH-strength; its weaker-than-RH content is exactly Q1's second entrance.
- **The full coupled class at the centre (B3.34).** Quantization settles the positive and zero-residue arithmetic members; the full class has no classification.
- **The `3/4` problem (B2.5).** Classical, with a sharp reduction (W19); its solution would not change any wall.
- **A selective counting polarization (B3.35); exclusion of infinite-height escape (B3.2); Stepanov auxiliaries over `ℤ` (B3.30).** No candidate object, RH-strength, or blocked by the missing period.

## 4. Would the B-tier obstacles require a new field of mathematics?

### 4.1 Assessment

No theorem shows that a new field is necessary. The corpus maps every forcing mechanism it has found, each with a sharp limit:

- **Invariant positivity is isotropic; elliptic localization is resonance or `σ_γ`, and `σ_γ`'s certificate stops at the conductor**, which is the local Weyl law of `D`.
- **One-variable positivity is Landau–Fejér positivity**, and its cone is classified.
- **Deformations detect**: positive and rational deformations of the coupled carrier are rigid exactly at zero-free ordinates; surplus residues are quantized central drops.
- **Counting is the sign over `ℤ`**; over `𝔽_q` it proves the sign through two cardinalities and a lattice spectrum.
- **Collided positivity is free, faithful, computed and blind.** `D` is the log-Sobolev norm computed from `ξ`; its equivariance is the content.
- **Zero-side reserves detect.** An off-line zero is visible at its own height through a positive field and an outward reserve; nothing bounds them from the arithmetic side.
- **Budgets are the sign**, with the spectral count as slope.
- **Multiplicative data see orbits**; finite windows separate the first twins, with no margin law.
- **Positivity before renormalization is lost at the diagonal.**
- **Statistics place most zeros near the line** and exclude none.

What is missing has a precise shape: **an inequality that turns the computed positive form, or the computed field, into a bound — or a renormalization that keeps a positive equivariant family positive at the diagonal.** Over `𝔽_q` both are supplied by a polarization of `C × C`: Riemann–Roch on the surface gives the positive trace, the Frobenius is a similitude, the self-intersection of the diagonal is the finite number `2 − 2g`, and the Frobenius spectrum lies on a lattice. Over `ℤ`:

- arithmetic intersection theory has a Hodge index theorem on arithmetic surfaces fibred over `Spec ℤ`, not on a square of `Spec ℤ`;
- the adele class space and the scaling site realize the zeros spectrally, and their positivity is RH;
- the Hilbert–Pólya picture posits `D` and asks for unitarity; the corpus computes `D` and finds the unitarity defect equal to the defect of `Δ`;
- potential theory computes `D` (the Laplacian of `log|ξ|`) and the field (the regularized gradient at the zeros, via `Λ ⋆ Λ`), but supplies no inequality for either;
- torsion intersection theory computes the prime kernel as intersections of torsion cycles, with positivity lost in the diagonal self-energy.

A new field is likely required [R]. Its parts are visible in the corpus: a conjugate-diagonal potential theory (energy and field of the zero divisor), a torsion intersection theory (renormalized self-energies), a deformation theory of positive systems, and a Diophantine theory of zero ordinates against `log p`. What none has is the adjunction that joins them.

### 4.2 The field: arithmetic electrostatics of the zero divisor

**Thesis [R].** RH is the coincidence on the zero divisor of two involutions — the functional-equation reflection `s ↦ 1 − s` (computed by the explicit formula) and complex conjugation `s ↦ s̄` (computed by potential theory of `log|ξ|`) — and, in electrostatic language, the statement that the zero divisor is in transverse equilibrium: no zero feels an outward field. Three quantities of one logarithmic potential are already computed by arithmetic:

| Quantity of the potential `log|ξ|` | Arithmetic computation | Positivity / content |
|---|---|---|
| Laplacian (Riesz measure; energy) | `D` from the `ξ` current and theta values | positive, a norm; equivariance is RH |
| Gradient at the charges (field) | simple Laurent coefficient of `(ζ′/ζ)² = L(Λ ⋆ Λ)` | equilibrium on critical configurations; outward at the deepest off-line zero |
| Diagonal self-interaction (self-energy) | torsion energies of roots of unity, renormalized | positive before renormalization; prime kernel after |
| Reflection pairing | Weil's form `W` from the explicit formula | equivariant; positivity is RH |

The field would study this potential on the characteristic circle `ℝ/ℤ` (torsion cycles as charges, cyclotomic resultants as intersections, `−log|1 − z w̄|` as Green function, the log-discriminant as self-intersection, the arithmetic point `z = 1` as distinguished fibre, the prime gauge torus acting on characters) and on the conjugate diagonal (zeros as charges, `D` as energy, `E` as field). Its central conjecture would be a **Hodge index theorem with adjunction**: on degree-zero cycles, the renormalized pairing plus the archimedean Γ-part is positive, and the renormalization is the one that turns the double pole of `Λ ⋆ Λ` into the field. RH is its specialization at the arithmetic point.

**What it would be like.**
- **Like Arakelov theory:** an archimedean Green function, regularized self-intersections, an adjunction formula, a Hodge index theorem for degree-zero cycles (Faltings–Hriljac), with the cyclotomic tower replacing an arithmetic surface.
- **Like Stieltjes electrostatics:** zeros of classical orthogonal polynomials are equilibrium positions of charges in an external field; here the external field is the Γ-factor and the pole, the charges are the zeros, and the equilibrium equation is the explicit formula. Equilibrium is computed; its stability is the sign.
- **Like logarithmic potential theory:** the energy is positive on signed measures of mass zero, free of charge; the potential at a point is not controlled by the energy. RH is a statement about the potential of the torsion measure at `z = 1` (Franel–Landau).
- **Like Hodge theory:** a Hermitian structure (`D`) and an intersection pairing (`W`), related by a polarization whose similitudes are the Hecke operators.
- **Like Diophantine approximation:** alignment of `γ log p` modulo `2π` at zero ordinates is the quantity both zero-side detectors need; Baker-type and Siegel-type repulsion already bound alignment with the Liouville vacuum.
- **Like gauge theory:** the prime gauge torus acts, multiplicative data are gauge invariant, and the arithmetic point is fixed by additive (successor) structure with holonomy.

**Parts already in the corpus.**
- **Conjugate-diagonal geometry** (CDG, PL): `D` from the `ξ` current and theta values; log-Sobolev norm; depth distributions; local Weyl law; local zero detection.
- **The field** (OF): terminals, outward rays, the transverse field, the Rankin–Selberg square.
- **Torsion intersection theory** (AE): `Λ` as an intersection number; the torsion measure's potential (`ψ`) and Fourier coefficient (`M`); renormalized positive energies.
- **Deformation theory of positive systems** (BGG): Landau–Wronskian principle, Abel–Gram law, conservation, quantization, strong multiplicity one.
- **Correspondence positivity and polarization** (ACP, PL): the layer map of Weil's argument, local types, symmetric-square spectra, elliptic localizers, two forms, budgets.
- **Gauge geometry and Diophantine repulsion** (ACG, BGG, SP): gauge torus, successor holonomy, repulsion, first separations.

### 4.3 Criteria the field must meet

| Criterion | Test against the corpus |
|---|---|
| **Computability** | The positive form, the field and the pairing are produced by identities (explicit formula, `ξ` current, resultants, `Λ ⋆ Λ`), not posited. Counting reformulations of the sign do not count. |
| **Renormalization** | A diagonal counterterm computed from the archimedean place and the pole, Hecke compatible, preserving positivity — the same on torsion self-energies and on the double pole of `Λ ⋆ Λ`. |
| **From detection to bound** | Turns a zero-side reserve (field, outward ray, local detector, Hecke defect) into an upper bound beyond classical density. |
| **Selectivity** | Distinguishes `ζ` from the W1 battery: relaxations, coupled-class deformations, golden datum and complex fake, sign and Liouville twins, theta fibres at `a ≠ 0`, polar configurations with incommensurable lines, multi-pair synthetic configurations. |
| **Gauge charge** | Sees the arithmetic point and non-archimedean charge beyond the first prime; reproduces the first separations. |
| **Local type** | Localizes by a non-multiplicative operation, or carries a polarization; controls the alignment of zero ordinates with small primes. |
| **Deformation calibration** | Reproduces positive rigidity at zero-free ordinates, chirality, quantization of surplus residues and critical conservation. |
| **Rank growth and fibre selectivity** | Section spaces of rank growing with the class; counting polarization depending on the fibre. |
| **Non-circularity** | No premise contains the conclusion; objects constructed before their sign. |
| **Uniformity** | Aperture, height, rank, damping and window controlled together; exceptional sets below the zero spacing. |
| **Calibration** | Weil for curves (`2g`, Hermitian `H¹`, Rosati transpose, lattice Frobenius spectrum); hyperelliptic RH by counting; budget slopes; `ℙ¹ × ℙ¹` effectivity; κ = 1 collapse; `κ ≥ 3`; conductor horizon; `W = D − Δ`; log-Sobolev norm; transverse equilibrium; Franel–Landau; the census. |
| **New partial results** | Outputs that are not zero-free strips: a non-isolation law (Q1), an adjunction inequality on finite sets of orders (Q2), a gauge margin law (Q3), central nonvanishing for coupled classes (B3.34). |

### 4.4 Questions it must answer

1. **What is the Frobenius at infinity as a correspondence?** Which algebraic involution acts on the zero spectrum as complex conjugation, and on torsion cycles as `z ↦ z̄`?
2. **What is the self-intersection of the diagonal?** Which renormalization of the torsion self-energy, and of the double pole of `Λ ⋆ Λ`, is Hecke compatible and positivity preserving (Q2)?
3. **What bounds the field?** Which arithmetic inequality caps the transverse field, or `ζ′/ζ` on outward rays, below the reserve (B1.14, B3.38)?
4. **What bounds the equivariance defect of the computed positive form?** (B3.33)
5. **What is the arithmetic point?** How does the theory distinguish `z = 1` (the gauge point `0`) from the rest of the circle, and what is its period?
6. **How does `σ_γ` localize beyond the conductor, and are zero ordinates aligned with small primes?** (Q1)
7. **What is the non-archimedean gauge charge?** (Q3)
8. **Is the coupled class bounded at the centre?** (B3.34)
9. **What selects the fibre?** (B3.35)
10. **What are the escape states of `ζ` at infinite height?** (B3.2)
11. **How does an average or a proportion become a point?** Which selection principle reaches below the zero spacing?
12. **What is the base?** Which structure has a tensor loss independent of the power?

### 4.5 Tools

**Built:** the capacity identity and the Hecke law of `D`; coercivity, log-Sobolev equivalence and the local Weyl law of `D`; the `ξ` current, finite and polynomial theta metrics and the local zero detector; depth distributions and the two-scale law; quadratic terminals, outward rays, the transverse field and the Laurent structure of `Λ ⋆ Λ`; the polarization law; local forms, boosts, resonance, symmetric-square spectra, sparse annihilators, `σ_γ`; twisted explicit formulas, conductor horizon, forcing half and gap; the smoothed Landau formula; effectivity calculus, Tate's law, naive and convex heights, theta surface, polar box, horizon torsion, Farey potential; torsion intersections and renormalized torsion energy; budget calculus over `ℤ` (both directions for the prime error) and `𝔽_q`; hyperelliptic RH by counting; completion, Burgess, least non-residue; the gauge torus, successor holonomy, Catalan and multi-prime repulsion; contraction and collision calculus; polar-configuration cone; deformation principle, Abel–Gram law, conservation, quantization, strong multiplicity one; phase kernels, Abel atoms; the census.

**Not yet built:**
- **Arithmetic adjunction:** a Hecke-compatible, positivity-preserving renormalization of diagonal self-terms.
- **Field and defect inequalities:** upper bounds for the transverse field, for `ζ′/ζ` on outward rays, and for the Hecke defect, that are not classical density estimates.
- **Diophantine control at zero ordinates:** alignment of `γ log p` at zero ordinates, with exceptional-set bounds.
- **Gauge margin laws:** positivity margins on growing prime windows, built from successor data.
- **Hermitian structures on correspondence spaces:** a Hilbert norm on zero transforms with the archimedean flow acting by computed similitudes.
- **Selective counting polarizations; ceilings for non-positive members of coupled classes; selection lemmas at the zero-spacing scale.**

### 4.6 Objects, language and mechanisms

| Layer | Content |
|---|---|
| **Objects** | • The characteristic circle `ℝ/ℤ` with torsion characteristics, Galois orbits, torsion measures `ν_N`, the arithmetic point `z = 1`, power maps (Hecke), the Green function `−log\|1 − z w̄\|`, log-discriminants, cyclotomic resultants, the horizon polynomial `P_N(q)`.<br>• The conjugate diagonal: `log\|ξ\|`, its Riesz measure, regularized potentials, the field `E` at the zeros, terminals and outward rays, depth distributions, theta prefixes.<br>• The Rankin–Selberg square `Λ ⋆ Λ` and its Laurent structure.<br>• The two forms `W`, `D`, the defect `Δ`, the Hecke defect `E_f(L)`.<br>• The biarithmetic semigroup `⟨+1, ×p⟩`: gauge torus, gauge points and twins, successor connection and holonomy.<br>• Counting objects; positive systems and their deformations; escape objects; zero ordinates as points of the prime torus. |
| **Language** | It must distinguish: positive and equivariant; computed, bounded and posited; detected and excluded; collided (conjugate) and Rosati (reflection) pairing; energy, field and self-energy; regularized and renormalized; equilibrium and stability; hyperbolic, elliptic and unipotent; even and odd sector; below and beyond the conductor; aligned and generic heights; gauge invariant and gauge charged; orbit and point; count and sign; soft and selective polarization; one-variable and two-variable; ceiling and rigidity; surplus and deficit; classification and exclusion; statistic and individual zero. |
| **Mechanisms to discover** | • An **adjunction law**: the diagonal self-term renormalized by the archimedean place, positivity preserving and Hecke compatible.<br>• A **stability law**: equilibrium of the zero divisor is stable for the renormalized pairing (Hodge index with adjunction).<br>• A **field law**: an arithmetic upper bound for the transverse field.<br>• An **alignment law**: Diophantine control of zero ordinates against small primes.<br>• A **gauge margin law**; a **conjugation law** (an algebraic correspondence acting as complex conjugation on the zeros); a **ceiling law** for coupled classes; a **base law**. |
| **First milestones** | (1) W15 and W18: moments and exceptional sets for both detectors; Q1.<br>(2) W16: finite-set counterterms; the divergence comparison of Q2, also on the self-terms of `Λ ⋆ Λ`.<br>(3) W13, W17: two- and three-prime selectivity with margins; Q3.<br>(4) W7(xvi): transverse equilibrium on the actual divisor.<br>(5) W14: the collided form and the local detector from finitely many theta values.<br>(6) W7(xi), W7(xvii): central nonvanishing and the quantization law in ACS coordinates. |

Each milestone is a theorem of a kind the corpus does not yet contain: a forcing law of elliptic type, a renormalized positivity, a gauge margin at every scale, or a computation on the conjugate diagonal with an inequality attached, rather than a receiver, a blindness theorem, a deformation equivalence, a detection or a counting reformulation of the sign. Programme standards add their own requirements:
- **APD:** name the positive side, the spectral side, the gap and the integer.
- **ACG / BGG / SP:** name the gauge charge, its holonomy and its margin.
- **ACP / PL / CDG / OF:** name the layer of Weil's argument, the local type, whether the carrier localizes, whether the positivity is collided, Rosati, pre-renormalization or zero-side, and what bounds the defect or the field.
- **AE:** name the currency, show the count is not one of the forms of the sign, and name the period it uses.
