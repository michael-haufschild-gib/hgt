# Research frontier summary: work, open mathematics, next questions, and a possible new field

Status: 2026-10-27, corpus `80f251476` with the working tree of that day. This summary covers the 31 routes, 17 candidates, PW-B and the supporting programmes of the [complete report](route-obstacles.md). Companions: [walls ledger](walls-ledger.md), [route unification](route-unification-ledger.md). Evidence: corpus search and Lean statement reading, recorded in `logs/review-2710-research-log.md`. Nothing was compiled. `[L]`, `[S]`, `[P]`, `[R]` as in the complete report; notation as there (`W`, `D`, `Δ`, `E_f(L)`, `σ_γ`, `ζ_γ`, `ν_N`).

## 0. The frontier in sixteen statements

1. **`ζ` has a computed positive form and a computed equivariant form, and RH says they are one form.** Weil's form `W` is Hecke equivariant for every zero configuration and has finitely many negative directions at every aperture; its positivity is RH. The collided form `D(f) = Σ_ρ m_ρ|f̂(ρ)|²` is positive, faithful and coercive at every aperture (the zeros are a sampling set for every Paley–Wiener space), and it is computed without zero indexing by the current `Δ log|ξ|` and by finite integer theta prefixes [L]. Its Hecke equivariance is RH; a single Hecke translation is a similitude of `D` iff RH [L]. `Re W = D − Δ`.
2. **What is missing is an inequality, not a computation.** The computations of `D` evaluate its Hecke defect `E_f(L) = Σ m_ρ(2cosh(2δ_ρL) − 2)|f̂(ρ)|²`; nothing bounds it above by a quantity that vanishes. Because `W` is equivariant, `E_D = E_Δ` [R]: the equivariance defect of the positive form is the equivariance defect of the off-line defect.
3. **Every unconditional positivity found is invariant, averaged, non-localizing, on nonnegative tests, collided, twisted below the conductor horizon, a finite-window certificate, or positive before a renormalization.** The new class: torsion energies `T_r` (`r < 1`) are positive semidefinite, and their renormalized limit is Weil's prime kernel; positivity is lost exactly in the divergent diagonal self-energy [L].
4. **Multiplicative symmetry is hyperbolic exactly at off-line pairs; elliptic localization inside correspondence-closed carriers is resonance; the only reflection-compatible affine localizer is `σ_γ`.**
5. **The forcing gap is a theorem.** The existing companion-forcing certificate needs `e^{2δa} > 768A log(|γ| + 3)` and is disjoint from the conductor horizon for every depth `δ ≤ 1/2`, at every height [L]. The conductor `log γ` is the local Weyl law of `D` (`D(e^{−iγu}f) ∼ ‖f‖² log|γ|`) [L/R]. Beyond the horizon the detector's prime side is a Dirichlet polynomial of length `(log γ)^{O(1)}` at the zero's ordinate: the open question is Kronecker alignment of zero ordinates with small primes [R].
6. **Counting is the sign over `ℤ` and proves the sign over `𝔽_q`.** Over `ℤ` a section count, an effectivity function, a naive or convex height, a one-sided count, a fixed tensor loss, horizon torsion and the Farey sum `Σ log(2 sin(πk/n))` at `√N` precision are each RH; large-sieve majorants inflate; subtracting the prime nodes destroys the Riemann inequality [L/S]. Over `𝔽_q` the corpus proves RH for odd-degree hyperelliptic curves by Stepanov's count and `|τ|² = q` [L]. Completion transports finite-level counts to incomplete sums only through a period; the arithmetic point has none.
7. **Budgets are RH or stronger, and over `𝔽_q` they count the spectrum.** A linear prime-error budget forces RH with slope at least the archimedean genus `2 + γ_E − log 4π`; a Mertens budget forces RH, simple zeros and summable residues `Σ|ρζ′(ρ)|^{−2}`; an Abel slope at the genus forces RH with simple zeros. Over `𝔽_q` the prime-error slope is `Σ mult(β)²` and the Mertens slope is the repulsion energy of the spectrum [L].
8. **`Λ` is an intersection number of torsion cycles.** `I(m, mt) = φ(m)Λ(t)` for Galois orbits of roots of unity (cyclotomic resultants), a Hecke-equivariant law computed by integers; `ψ(N)` is minus the potential of the torsion measure at the arithmetic point and `M(N)` its first Fourier coefficient [L].
9. **Hodge index splits into a local part that holds and a Lefschetz part that is RH.**
10. **Multiplicative data see orbits, not the point; positivity already sees the first two primes.** Finite multiplicative lattice forms are blind; the successor connection reads the prime phases from `2 → 3 → 4`. Unconditional positivity of `ζ` separates it from the Liouville twin at `181/500` and from the first non-archimedean twin at `23/40` on explicit witnesses [S]. An archimedean twist approaches the Liouville vacuum on `N` primes at most stretched-exponentially fast [L].
11. **Every amplification over `ℤ` tested loses linearly, and twists are rate neutral.**
12. **No graded receiver has a rung between Vinogradov–Korobov and a fixed strip.** The energy-rate law at the zero abscissa is exact in both directions [L].
13. **One-variable positivity is exhausted, and its cone is classified.** κ = 1 class `ℝ^× · ζ`; anchored quartets force `κ ≥ 3`; one vertical section decides positivity; the leading line is a nonnegative almost-periodic sum; positive commensurable lines are couplings [L].
14. **Deformations detect, they do not force.** Positive prime-mass deformations of `ζ_γ` keep the off-line divisor; positive rigidity at `γ` holds iff `ξ` has no zero at ordinate `γ`; positive chirality and the rational and positive central ceilings at `γ` each hold iff there is no off-line zero at ordinate `γ` [L]. A central excess of an arithmetic member costs a square-root prime deficit with Abel residue at least the excess [L].
15. **Escape classifies and never excludes.** Abel atoms of `ζ` are its dominant zeros with their residues; non-summable residues, an unattained abscissa or unbounded orders send the mass to infinite height [L]. RH is positive gauge mass of every escape state.
16. **Positivity holds on average and at almost every zero ordinate; excluding an individual zero needs exceptional sets below the zero spacing.**

## 1. Just work

Known mathematics suffices for each item, and none crosses a wall. An item's outcome may be unknown; what is known is the method.

| ID | Task | Concrete content | Completion criterion |
|---|---|---|---|
| **W1** | Selectivity battery | Test every mechanism against:<br>• pole-order-2/3 relaxations, strip-pole quartets, over-regular Beurling systems, the Siegel family, twisted boundary systems;<br>• the golden datum and the complex fake (including its kernel counts, all `≥ 0`);<br>• the Liouville, `{2,3}`-flipped, sign-flipped and dominated twins; Haar-typical and Kronecker twists; shifted pairs `ζ(s − a)ζ(s + a)`;<br>• height-coupled lifts, `W_β`-split members, Fejér-coupled systems, rational and positive deformations, arithmetic members with square-root deficit;<br>• theta-surface fibres at `a ≠ 0`; Jacobi–Hurwitz packets;<br>• polar configurations with incommensurable leading lines;<br>• torsion energies at `r < 1`;<br>• white noise, reset-origin mixtures, translated-zero eigenstates, Abel atoms.<br><br>Calibrations to reproduce: κ = 1 collapse; `⌊k/2⌋` capacity; Fejér barrier; `2 : 1` anchor law and `κ ≥ 3`; Weil for curves with budget `2g`; hyperelliptic RH by counting; prime-error slope `Σ mult²` and Mertens slope = repulsion energy; `ℙ¹ × ℙ¹` effectivity; `W = D − Δ`; local Weyl law. | Each mechanism records the model that defeats it, its local type, whether its positivity is collided, Rosati or pre-renormalization, and whether its counting polarization is fibre-selective. |
| **W2** | Finite identities and certificates | Gram, Hausdorff, Hankel, Jensen blocks; finite heat transforms; schedules and histories; finite Robin, Li, JAS and Vaughan budgets. | Every finite term certified; no cofinal claim. |
| **W3** | Premise checks | Regularity, support, decay and domain membership for named tests and families (SZ limits, CHMD domains, candidate sources, twisted detectors). | Hypotheses of existing transfers discharged. |
| **W4** | Transport of proved inputs | Width functor; RW↔SZ↔CHMD; HF→AIP; Weil margin → heat window. Restate in RW, SZ, CHMD, EWU, OWU, ACT, AIP, HF coordinates: averaged positivity, the off-line field, zero-ordinate positivity, the short-cycle split, the conductor horizon, the forcing half and gap, collided coercivity and the local Weyl law, the finite negative index. Restate the effectivity currencies in HF and ACS coordinates. | Each conclusion stated at its true strength. |
| **W5** | Certified extensions and constants | Push the full floor of `ζ` beyond `181/500` (`23/40` is W13; then past `log 5/2`); odd and primitive windows beyond `181/500`, `(log 2 + 1/50)/2`. Make explicit `κ₀, C₀, Γ₀`, `sharpCollarConst κ`, the constant `C` of the conductor horizon and an effective coercivity constant `c_A` for `D` (the proved constant is non-effective). | Certified finite-aperture theorems. |
| **W6** | Short windows to the classical range | Replace `Γ^{99/100}` by `Γ^{1/2+ε}` in the averaged, off-line-field, zero-ordinate and positive-measure theorems and in WL's filtered deficit, using Selberg's near-line density [R]. | The four theorems on `Γ^{1/2+ε} ≤ H ≤ Γ/8`. |
| **W7** | Corollary assembly | (i) An averaged bounded-energy statement for WL.<br>(ii) One rate dictionary for RW, SRT, ACS through `groundRate = polarRate`.<br>(iii) The explicit LA/WD residual region.<br>(v) Replace the imported `c/(log\|t\|)^9` collar by the MPG or SBWF calibration.<br>(vi) Conservation for infinite reflection-antisymmetric corrections.<br>(vii) One capacity law: boundary, collar, gauge, family, Abel–Gram line capacity, `ζ^d` boundary capacity `2Σ ≤ κ − d`.<br>(xi) The full-class ceiling at zero-free ordinates as central nonvanishing: if `ξ(1/2 ± iγ) ≠ 0`, the ceiling at `γ` ⇔ every member of `HeightCoupledSystem 2 1 1 γ` has `Λ(1/2) ≠ 0`.<br>(xii) One collided-positivity theorem: kernel counts, coupled counts, escape Cauchy forms, `D`, the depth profile, with the Hecke law.<br>(xiii) The lower log-Sobolev bound `c∫\|f̂\|² log(\|σ\| + 4) ≤ D(f)` from Gårding, coercivity and the explicit-formula density; then the declared equivalence.<br>(xiv) `E_D = E_Δ` and the `ξ`-current formula for `E_f(L)` in PL and HF coordinates.<br>(xv) Converse directions of the budgets: RH ⇒ linear prime-error budget (Cramér, from `CramerZeroSumMeanSquare` and the RH partial fractions [S]); RH + simple zeros + `Σ\|ρζ′(ρ)\|^{−2} < ∞` ⇒ Mertens budget. | Each statement proved from existing theorems. |
| **W9** | Depth homogeneity, remaining classes | The loss law for `k`-level forms and Følner coupling. | One theorem per class. |
| **W10** | Range-limited growth inputs | State the VK step as a `δ`-range instance of `exclusion_iff`. | VK as an instance of the growth-to-forcing law. |
| **W11** | Contraction calculus, last items | (i) Whether a complex quartet at depth `1/4 < a < 1/2` contracts at `Δκ = 1` with the boundary pole as anchor. (ii) A minimum-tax theorem for arbitrary finite rational multipliers, using the rational-deformation real-anchor classification and the line hierarchy law. | Each statement in Lean as a calibration. |
| **W12** | Integration of working sources | SelectivePositivity (six modules); `TheCriticalConservationLaw`; `StripSourceCutoff`; `QuadraticAscentReachesALocalMaximum`; `TheCollidedFormIsTheLogarithmicSobolevNorm`; `ThePrimeErrorSymbolSplitsAtTheZeros`; the Burgess modules. | Each statement at its stated strength in an umbrella. |
| **W13** | The two-prime window | Certify the full-sector floor of `ζ` at `23/40` and compute the best margin `inf (W_ζ(F) − W_λ(F))/‖F‖²` over odd separating tests there; repeat for every sign pattern on `{2, 3}`. | `ζ` positive on the whole `23/40` window with an explicit floor, and the margin table of the four sign twins. |
| **W14** | Quadrature for the conjugate-diagonal readings | Replace the continuous source integrals of the finite theta metric by finite quadrature with explicit error, starting from the fixed-strip cutoff [S]. | A polynomial-prefix metric theorem: `D` and its depth moments from finitely many integer theta values. |
| **W15** | Moments of the odd detector over zero ordinates | Compute `Σ_{0<γ≤T} P_a(γ)^{2k}` for the detector's prime polynomial `P_a` by the Landau–Gonek formula; derive the exceptional-set bound for `P_a(γ) > (1 − η) log γ`. | Explicit moment and exceptional-set theorems for `e^{2a} ≤ (log T)^{C}`; the input of Q1. |
| **W16** | Torsion counterterms on finite sets of orders | For finite `S ⊂ ℕ`, compute the minimal diagonal counterterm `C_r(S)` making `G∘T_r − C_r` positive and converging to the atomic Weil form; compare `C_r(S)` with the archimedean self-energy of atoms at scale `1 − r`. | A table of `C_r(S)` and its divergence rate for squarefree and prime-power `S`; the input of Q2. |
| **W17** | The three-prime window | Extend the selectivity law to windows reading `{2, 3, 5}` (`2A > log 5`): full floor of `ζ`, negative witnesses for every non-Euler sign pattern. | A certified three-prime selectivity battery. |

W8 (the edge eigenproblem at `181/500`) is settled by an explicit negative witness [S]; its integration is part of W12.

## 2. Open mathematical obstacles

### 2.1 Tier B1: RH-strength closing statements

Each is equivalent to RH or stronger. Solving one closes every route that uses it.

| ID | Statement | Routes |
|---|---|---|
| **B1.1** | **Critical signed cancellation at every positive slack.** Bounded critical deficit energy; one-sided lag or Abel moments; the history floor; the regularized abscissa `1/2`; the JAS half-power budget; Mertens at square root (`ν̂_N(1)`); the one-sided count `ψ(x) − x ≤ C√x log²x`; the Farey sum at `√N` precision; typicality of the gauge point `0`. | WL, MC, FU, RP, PBM, JAS, SRT, DR |
| **B1.2** | **Signed small-damping energy.** Admission at every damping; subpower receiver energy; positive gauge mass of every escape state; signed long-modulus quadrature; a Báez–Duarte residual `→ 0`. | PM, CTF, BVI, MC, PW-B |
| **B1.3** | **Positivity of the equivariant form.** `W ≥ 0` at all apertures; equivalently zero negative index at every aperture; the one-sided Weil inequality at one prime; one shift; sufficiency of the free budget; Rosati positivity; the nodal inequality; positive Suzuki first variation; odd capacity; global allocation; Bézout on the exact source cone. | RW, SZ, CHMD, EWU, OWU, ACT, AIP, TT, HF, ACS, SRT |
| **B1.4** | **Selection.** From short-window averages and almost every zero ordinate to every height, signed test and aperture. | WL, SRT, ACS, APT |
| **B1.5** | **Critical-endpoint heat and moment sign.** Residual heat region; all-rank Hankel positivity at one time; both heat grids; rank-uniform Schur decay; the Newton margin; order-uniform passivity. | LA, WD, TH, HCF, GTA, XN, PA |
| **B1.6** | **Forcing and exhaustion for a realization.** Exhaust the maximal blind ideal with an input outside the exhausted classes (invariant, non-localizing, nonnegative-test, multiplicative, one-variable, collided, twisted-below-horizon, counting, deformation, pre-renormalization). | TG, RN, WD, ACS, all candidates, PW-B |
| **B1.7** | **Single-currency endpoints.** BSY contrast equality; the subexponential Li floor; the eventual Robin tail; recurrence near possible zeros; `D_idx < 2`. | FEL, LI, RB, BAG, HF |
| **B1.8** | **RH with simple zeros.** Faithful positive Meyer degree; RR for the Hilbert–Schmidt reserve. | ACS/Meyer faithful branch |
| **B1.9** | **Counting forms of the sign.** Effectivity function; no abundant class; naive heights; convex heights; fixed tensor loss; section count; horizon torsion; the Farey sum. | HF, ACS, AOG, SRT, WL |
| **B1.11** | **Equivariance of the positive form.** `D` Hecke invariant; one Hecke translation a similitude of `D`; `E_f ≡ 0`; `Δ ≡ 0`; `W = D`. | HF, ACS, PM |
| **B1.12** | **Central ceilings and chirality.** Rational or positive central ceilings, or positive chirality, at every `γ ≠ 0` (each RH, ordinate by ordinate [L]); the full-class ceiling at every `γ` (implies RH; converse open, see B3.34). | ACS, SBWF |
| **B1.13** | **Budget currencies.** A linear prime-error budget (⇒ RH); a Mertens budget (⇒ RH + simple + summable residues); an Abel slope at the genus (⇒ RH + simple). | WL, MC |

### 2.2 Tier B2: classical open problems weaker than RH

| ID | Problem | Where it is the next rung |
|---|---|---|
| **B2.1** | Quasi-RH: a fixed zero-free strip. | Every graded receiver; admission at fixed damping; energy growth; one-sided Lefschetz bounds; escaped Möbius pairings at a fixed `θ`; large-sieve section supply. |
| **B2.2** | Finite off-line index. | HF/AOG index exit; WD collision masses. |
| **B2.3** | Simplicity of the zeros. | Operator-norm faithful realizations; Mertens budgets. |
| **B2.4** | Density hypothesis; large values beyond Guth–Maynard. | Averaged positivity at larger aperture; filtered deficit; the computed Hecke defect (B3.33); exceptional sets of B3.36. |
| **B2.5** | At least `3/4` of the zeros on the line. | TTPC: surplus `β ≤ 1/18`; parity-breaking dispersion. |
| **B2.6** | Power-saving sign correlations of `μ`, `λ`. | MC anti-alignment; SSA constants. |
| **B2.7** | Uniform Hardy–Littlewood prime-pair correlations near the square-root band. | TTPC; near-incidence beyond the threshold; successor-charged positivity. |
| **B2.8** | Subconvexity and growth near `Re s = 1`. | KKL horizon; growth input of multiplicative positivity. |
| **B2.9** | Better de Bruijn–Newman bounds. | Shrinks the B1.5 region. |
| **B2.10** | Near-line density on windows shorter than `T^{1/2}`. | Averaged positivity on windows `Γ^θ`, `θ < 1/2` (B3.7). |

### 2.3 Tier B3: open problems isolated by this research

No solution is known, and none is proved RH-equivalent.

| ID | Question | Present boundary |
|---|---|---|
| **B3.1** | Physical-`L²` rate equality `polarRate = Δ`. | `Δ ≤ polarRate = groundRate ≤ 1/2`. |
| **B3.2** | **Exclusion of infinite-height escape for `ζ`**: tightness of the exterior spectral mass of the actual receiver. | Classification complete [L]: finite-height atoms are the dominant zeros with their residues; non-summable residues, an unattained abscissa or unbounded visible orders send all mass to infinite height; capacity and endpoint laws. |
| **B3.3** | Quantitative coercivity of residual/trace reconstruction. | Algebraic injectivity; kernel `ℝ q_ε`. |
| **B3.6** | Signed shell flux along the moving prime-threshold ladder. | Birth jumps vanish; collar bound. |
| **B3.7** | Averaged positivity on windows `Γ^θ` below the classical range. | `θ = 99/100` proved; `θ > 1/2` is W6. |
| **B3.8** | A nonlocal shared-budget calculus with prime-weighted remainder. | Frustration and descent laws; polar-neutral collapse; log-cell remainder; raw continuum towers negative at order `e^A` [S]; joint `2, 3` payment at `23/40`. |
| **B3.9** | Arithmetic input on the residual heat region. | Model geometry complete. |
| **B3.10** | Compatible oriented families. | Spline-orbit index `≤ 1` ⇔ RH. |
| **B3.11** | Sub-half-damping signed control of the forward interior. | Exterior paid; `ε = 1/2` bounded. |
| **B3.12** | Order-uniform PA thresholds; decoupling rank from time. | Fixed-order thresholds. |
| **B3.13** | Sharp successor constants beyond conductor 3. | Odd shifts `1/3`, lag 2 `1/4`. |
| **B3.16** | Is the paid ideal nonzero on escape? | Would exclude white noise, not translated-zero states. |
| **B3.18** | Equality case of collar capacity at even `κ`. | Odd `κ` sharp. |
| **B3.20** | Signed near-coincidence cancellation at one height beyond aperture `½ log Γ`. | Single-height phase-selective law. |
| **B3.24** | An unconditional nontrivial estimate for a gauge-charged statistic of `μ` or `Λ` at the point `0` beyond the square-root threshold. | Haar-typical twists meet every budget; growing-endpoint escaped pairings are strips [S]. |
| **B3.26** | **The non-archimedean gauge charge**: a positivity of `ζ` that separates it from every sign twin on growing prime windows, with a margin that survives aperture growth. | First two windows separated [S]; multi-prime repulsion stretched exponential [L]; archimedean-free successor-square separator [S]; finite lattice forms blind. |
| **B3.28** | The Rankin–Selberg field for the actual source `Λ ⋆ Λ`. | Finite polar sources only. |
| **B3.29** | Lower bounds or arithmetic use of the successor defect `D_Λ` on vertical lines. | Pointwise `(\|s\| + 1)^{1−σ+η}`; mean square `2πΣΛ²/(n(n+1))` exactly [L]. |
| **B3.30** | Stepanov auxiliaries over `ℤ` outside the one-prime Hecke algebra. | Hyperelliptic RH by Stepanov [L]; the natural output over `ℤ` is RH; univariate integer polynomials stop below PNT [R]; the arithmetic point has no period. |
| **B3.32** | **The odd-sector sign beyond the conductor horizon** at the ordinate of a hypothetical off-line zero. | Forcing half [L]; horizon [L]; gap a theorem at every height [L]; reduces to B3.36 [R]. |
| **B3.33** | **An inequality for the computed collided form**: a prime-side or theta-side upper bound for the Hecke defect `E_f(L)` that is not a classical density estimate, or a prime-side computation of `D`. | `D` computed by the `ξ` current and theta prefixes [L]; depth distribution and two-scale variance law [L]; `E_D = E_Δ` [R]. |
| **B3.34** | **The full coupled class at the centre**: at zero-free ordinates, does every member of `HeightCoupledSystem 2 1 1 γ` satisfy the ceiling (two-sided rigidity, central nonvanishing)? | Positive and rational subclasses settled [L]; arithmetic members need a square-root prime deficit with residue `≥` excess [L]; critical conservation [S]. |
| **B3.35** | **A selective counting polarization**: counts of rank growing with the class, fibre-dependent, equal to the Rosati form at the fibre of `ζ`. | Theta surface soft; lattice counts collapse; large-sieve majorants inflate; Jacobi–Hurwitz dichotomy [S]. |
| **B3.36** | **Kronecker alignment at zero ordinates.** For `X = (log γ)^{2θ}`, `θ > 1`, does the twisted detector's prime polynomial `Σ_{n≤X} Λ(n)n^{−1/2}cos(γ log n)k(log n)` stay below `(1 − η) log γ` at the ordinates of the zeros, or outside a set sparse enough for zero-density estimates? | Generic heights: large deviations of random phases [R]; zero ordinates: Landau–Gonek moments (W15); multi-prime repulsion bounds alignment with the Liouville vacuum [L]. |
| **B3.37** | **Positive renormalization of torsion energies.** Is there a Hecke-compatible counterterm, paid by the archimedean and polar terms, under which the atomic Weil form is a limit of positive torsion forms? | `G∘T_r ≥ 0`; renormalized limit = minus prime kernel + log-discriminant [L]; intersection law `I(m, mt) = φ(m)Λ(t)` [L]; finite-set counterterms (W16). |

### 2.4 Settled questions

- **What computes `D`.** The current `Δ log|ξ|` and finite theta prefixes; `D` is faithful and coercive; a Hecke translation is a similitude of `D` iff RH.
- **The forcing gap.** Proved at every height; the certificate splice is dead.
- **The first gauge-charged windows.** Separated at `181/500` and `23/40` [S].
- **Escape.** Classified completely, including the infinite-height cases; the energy-rate law is exact.
- **Positive and rational deformations of the coupled carrier.** Rigid exactly at zero-free ordinates; their ceilings and chirality are RH ordinate by ordinate. Two-sided rigidity of the full class fails at every zero ordinate.
- **Budgets over `𝔽_q`.** Prime-error slope `Σ mult²`; Mertens slope = repulsion energy; genus one: strict Hasse.
- **Counting over `𝔽_q`.** Hyperelliptic RH by Stepanov and Gauss sums.
- **Kernel counts as heights.** No: the complex fake.
- **Also settled:** section counts, effectivity, naive heights, one-sided counts and tensor bases are the sign; elliptic localization in correspondence-closed carriers is resonance; contraction and collision calculus; positive polar-configuration cone; theta `h⁰` does not extend; multiplicative lattice forms blind; the first gauge charge is a twist; theorem of the square and budget free; positivity beyond isotropy only without localization; κ = 1 class; Lefschetz receivers at one prime; linear loss; twists rate neutral; averaged positivity at `Γ^{99/100}`; absolute pole-order budget false.

## 3. The three questions to answer next

**Selection criteria.**

1. The question is weaker than RH, so it can be answered.
2. Either answer changes the frontier: a positive answer adds a mechanism; a negative answer is a sharp no-go naming the missing input.
3. Together the questions cover the three walls.
4. The output is not a zero-free strip, a collided positivity, a counting reformulation, a gauge-orbit statement, a one-variable positive system or a deformation equivalence.
5. The question addresses the polarization problem in its present form: a form that is positive and equivariant at once.

**Why these three.** What computes `D` is answered, so the two-form problem is an inequality. The forcing gap is a theorem, so elliptic localization is a Diophantine question about zero ordinates. The first two gauge-charged windows separate `ζ` from its twins, so the gauge question is persistence. Torsion energies are positive before a renormalization and equivariant after it, so the polarization problem has a concrete renormalized form. The three questions below take the three live contents: alignment (Wall 3 with Wall 1), renormalization (Wall 14), gauge persistence (Wall 1).

### Q1. Kronecker alignment at zero ordinates: can the odd-sector sign be proved beyond the conductor horizon?

> *At the ordinate `γ₀` of a zero, is the twisted detector's prime polynomial `P_a(γ₀) = Σ_{n ≤ e^{2a}} Λ(n) n^{−1/2} cos(γ₀ log n) k_a(log n)` at most `(1 − η)` times the shifted digamma term `≈ log γ₀` for apertures `e^a` between the conductor horizon `log γ₀/4` and the forcing threshold `(768A log γ₀)^{1/(2δ)}` — for every zero, or for all zeros outside a set sparse enough that zero-density estimates exclude it?*

- **Why.**
  - The odd sector of `σ_γ` is the only localizing sector whose positivity forces, and the forcing half needs it on one test at one height [L]. The gap between horizon and threshold is a theorem [L], so the only remaining route through this mechanism is a sign beyond the horizon.
  - Below the horizon the trivial bound `|cos| ≤ 1` suffices; beyond it the polynomial has length `X = (log γ₀)^{2θ}`, `θ > 1`, and positivity needs a saving `X^{(θ−1)/(2θ)}` over the trivial bound at the specific point `γ₀` [R]. Random phases give `≈ log X ≪ log γ₀`; the obstruction is alignment of `γ₀ log p` (`p ≤ X`) modulo `2π`.
  - The Kronecker-peak obstruction concerns all tests at aligned heights, not this test at zero ordinates. Landau's formula `Σ_{0<γ≤T} x^ρ = −TΛ(x)/(2π) + O_x(log T)` and its uniform version (Gonek) make exponential sums over zero ordinates explicit, with a negative bias at prime powers, so moments of `P_a` over zero ordinates are computable (W15) [R].
  - The same Diophantine quantity governs Q3: multi-prime repulsion bounds how closely `γ log p` can align with the Liouville vacuum [L].
- **Route.**
  1. W15: moments `Σ_{γ≤T} P_a(γ)^{2k}` and the exceptional set `E_T = {γ ≤ T : P_a(γ) > (1 − η) log γ}`.
  2. Compare `|E_T|` with zero-density bounds `N(1/2 + δ, T)` and with the local count `A log T` of the forcing half.
  3. Iterate the forcing half outside `E_T` (companions of companions) to a cluster statement.
- **Weaker-than-RH content.** Proved at threshold `θ`, the forcing half gives a non-isolation law: an off-line zero of depth `δ > 1/(2θ)` whose ordinate is outside `E_T` has an off-line companion within ordinate distance `(log γ)^θ`. This is a structural statement about off-line zeros, not a zero-free strip.
- **Outcomes.**
  - *Yes (all ordinates or outside a sparse set):* the first localizing positivity of elliptic type that forces; with density bounds on clusters, a theorem excluding isolated deep off-line zeros.
  - *No:* zero ordinates can be Kronecker-aligned with the first `(log γ)^{2θ}` primes; elliptic localization through `σ_γ` is closed as a forcing mechanism, and forcing must come from a renormalized or computed polarization (Q2).

### Q2. Arithmetic adjunction: does a positive renormalization of torsion energies produce Weil's form?

> *The torsion energies `G∘T_r` (`r < 1`) are positive semidefinite on finitely supported vectors over the orders; their limit is minus Weil's prime kernel plus the log-discriminant diagonal, with a divergent self-energy `log(1/(1 − r))`. Is there a counterterm — computed from the archimedean place and the pole, compatible with the Hecke law `I(m, mt) = φ(m)Λ(t)` — whose subtraction keeps the torsion forms positive and whose limit is Weil's atomic form?*

- **Why.**
  - Torsion energies are the first object in the corpus that is positive (at `r < 1`) and Hecke equivariant (at `r = 1`, through the intersection law) in one family [L]. Positivity and equivariance separate only at the diagonal renormalization [L].
  - Weil's archimedean kernel has a logarithmic singularity at the diagonal; smeared at scale `ε` it diverges like `log(1/ε)`, as the torsion self-energy diverges like `log(1/(1 − r))` [R]. The question is whether these two divergences cancel in a positivity-preserving way: an adjunction formula on the characteristic circle, in the role the self-intersection of the diagonal plays in Weil's proof and the Arakelov Green function plays in arithmetic surfaces.
  - It is a construction question, not a counting reformulation: the forms are given; the counterterm is the unknown.
- **Route.**
  1. W16: minimal counterterms `C_r(S)` on finite sets of orders (primes, prime powers, squarefree sets); their divergence rate.
  2. Compare `C_r(S)` with the archimedean self-energy of atomic tests at matched scale, and with the polar term.
  3. Test Hecke compatibility: whether `C_r` commutes with the power maps `z ↦ z^t` on torsion orbits.
- **Weaker-than-RH content.** Positivity of the renormalized form on vectors supported in a fixed finite set of orders is a finite statement; a uniform counterterm on all finite sets would be a positivity theorem for atomic tests and is RH-strength [R]. Intermediate: a counterterm that works on one Hecke orbit `{m, mp, mp², …}` is a one-prime statement to compare with the Lefschetz receivers.
- **Outcomes.**
  - *Yes:* a computed form that is positive and equivariant up to an explicit counterterm; the polarization problem reduces to one inequality between the arithmetic and the archimedean self-energies.
  - *No:* a theorem that every positivity-preserving counterterm breaks the Hecke law; positivity and equivariance cannot be joined through torsion cycles of the characteristic circle, and a two-variable carrier is necessary.

### Q3. Gauge persistence: does unconditional positivity of `ζ` keep separating it from its sign twins as primes enter?

> *For windows reading the first `N` primes, is there, for every real sign gauge `ω` differing from the Euler vacuum on `{p ≤ p_N}`, an explicit test on which `ζ`'s form is positive and the twin's form negative, with margin bounded below by an explicit function of `N` — and can the separating tests be built from successor data (the `+1` links) rather than certified numerics?*

- **Why.**
  - A `ζ`-specific sign must use gauge-charged data. The first two windows separate `ζ` from its twins [S]; from the second prime on the charge is not archimedean [L].
  - Multi-prime repulsion shows archimedean twists approach the Liouville vacuum at most stretched-exponentially fast [L]; the off-line field costs `e^A` at aperture `A`. A margin law decides whether positivity can read the gauge point at all scales.
  - The successor connection reconstructs the prime phases from consecutive integers, and the successor-square form `w(2)w(4)` separates the Liouville twin from every scale twist without archimedean input [S].
- **Route.**
  1. W13, W17: two- and three-prime windows: full floor of `ζ`, margins for every sign pattern.
  2. The margin as a function of `N` and `A`, against the repulsion bound and the `e^A` off-line-field cost.
  3. Successor-built tests: express separating tests through Catalan links `n → n + 1` (`2 → 3 → 4`, `3 → 4 → 5`, `8 → 9`).
- **Outcomes.**
  - *Separation with a surviving margin:* the first unconditional positivity that reads non-archimedean arithmetic at every scale, an input for B1.6's gauge-charge condition.
  - *Separation with a collapsing margin:* a measured threshold where positivity stops seeing arithmetic.
  - *No separation beyond some `N`:* a sign twin indistinguishable from `ζ` by unconditional positivity on every certified window; positivity is gauge blind there, and additive (successor) input is necessary.

The three questions are the forcing problem in each wall's currency:
- Q1: what a localized sign at one height can force (Wall 3, faces 3.18–3.19; Wall 1, face 1.3).
- Q2: whether a positive form and an equivariant form can be one form through renormalization (Wall 14, faces 14.18, 14.21, 14.24; Wall 1, face 1.16).
- Q3: whether positivity carries non-archimedean gauge charge at every scale (Wall 1, face 1.18).

**Considered and not chosen.**
- **An upper bound for the computed Hecke defect (B3.33).** Uniform in `L` it is a graded rate (first-rung law: a fixed strip); at `L ≍ log T` for every height it is RH-strength; averaged over heights it is a classical density estimate. A non-classical bound needs a structure that the computation does not supply — the object of Q2.
- **The full coupled class at the centre (B3.34).** The positive and rational subclasses are settled; the full class has no classification, and arithmetic members already pay a square-root deficit.
- **A selective counting polarization (B3.35).** No candidate object beyond the soft theta surface; large-sieve constructions inflate.
- **Exclusion of infinite-height escape (B3.2).** Equivalent in strength to positive gauge mass (B1.2).
- **Stepanov auxiliaries over `ℤ` (B3.30).** The natural output is RH; the arithmetic point has no period.

## 4. Would the B-tier obstacles require a new field of mathematics?

### 4.1 Assessment

No theorem shows that a new field is necessary. The corpus maps every forcing mechanism it has found, each with a sharp limit:

- **Invariant positivity is isotropic; elliptic localization is resonance or `σ_γ`, and `σ_γ`'s certificate stops at the conductor**, which is the local Weyl law of `D`.
- **One-variable positivity is Landau–Fejér positivity** and its cone is classified.
- **Deformations detect.** Positive and rational deformations of the coupled carrier are rigid exactly at zero-free ordinates; their ceilings are RH ordinate by ordinate.
- **Counting is the sign over `ℤ`**, and it proves the sign over `𝔽_q` through two cardinalities; over `ℤ` the arithmetic point has no period.
- **Collided positivity is free, faithful and computed, and blind.** `D` is a norm computed from `ξ`; its equivariance is the content.
- **Budgets are the sign**, with the spectral count as slope.
- **Multiplicative data see orbits**; finite windows already separate the first twins, with no margin law.
- **Positivity before renormalization is lost at the diagonal.**

What is missing has a precise shape: **an inequality that makes the computed positive form equivariant, or a renormalization that keeps a positive equivariant family positive at the diagonal.** Over `𝔽_q` both are supplied by a polarization of `C × C`: Riemann–Roch on the surface gives the positive trace, the Frobenius is a similitude, and the self-intersection of the diagonal is the finite number `2 − 2g`. Over `ℤ`:

- arithmetic intersection theory has a Hodge index theorem on arithmetic surfaces fibred over `Spec ℤ`, not on a square of `Spec ℤ`;
- the adele class space and the scaling site realize the zeros spectrally, and their positivity is RH;
- the Hilbert–Pólya picture posits `D` and asks for unitarity; the corpus computes `D` and finds the unitarity defect equal to the defect of `Δ`;
- potential theory computes `D` from `log|ξ|` but supplies no inequality for its Hecke defect;
- torsion intersection theory computes the prime kernel as intersections of torsion cycles, with positivity lost in the diagonal self-energy.

A new field is likely required [R]. Its parts are visible in the corpus: a conjugate-diagonal potential theory, a torsion intersection theory and a deformation theory of positive systems. What none has is the adjunction that joins them.

### 4.2 The field: arithmetic potential theory on the characteristic circle and the conjugate diagonal

**Thesis [R].** RH is the coincidence on the zero divisor of two involutions: the functional-equation reflection `s ↦ 1 − s`, holomorphic, computed by the explicit formula; and complex conjugation `s ↦ s̄`, antiholomorphic, computed by potential theory of `log|ξ|`. Their composite is the Rosati reflection `s ↦ 1 − s̄`. On the arithmetic side the explicit formula's prime kernel is an intersection pairing of torsion cycles on the characteristic circle `ℝ/ℤ` (roots of unity), Hecke equivariant under the power maps; on the potential side the same pairing is the limit of positive logarithmic energies, which diverge at the diagonal. The field studies this circle as an arithmetic curve: torsion cycles as points, cyclotomic resultants as intersections, `−log|1 − z w̄|` as the Green function, the log-discriminant as the self-intersection, the arithmetic point `z = 1` as the distinguished fibre, the prime gauge torus acting on characters. Its central conjecture would be a Hodge index theorem: on degree-zero torsion cycles, the renormalized intersection pairing plus the archimedean Γ-part is positive. RH is its specialization at the arithmetic point.

**What it would be like.**
- **Like Arakelov theory:** an archimedean Green function, regularized self-intersections, an adjunction formula, a Hodge index theorem for degree-zero cycles (Faltings–Hriljac), with the cyclotomic tower replacing an arithmetic surface.
- **Like logarithmic potential theory:** the energy `−∫∫ log|z − w| dμ dμ` is positive on signed measures of total mass zero, free of charge; the potential at a point is not controlled by the energy. RH is a statement about the potential of the torsion measure at `z = 1` (Franel–Landau: equidistribution of Farey points at square-root rate).
- **Like Hodge theory:** a Hermitian structure (`D`) and an intersection pairing (`W`), related by a polarization whose similitudes are the Hecke operators.
- **Like Tate's theory of heights:** positivity from functions at bounded distance from quadratic forms.
- **Like gauge theory:** the prime gauge torus acts, multiplicative data are gauge invariant, and the arithmetic point is fixed by additive (successor) structure with holonomy.

**Parts already in the corpus.**
- **Positive duality and one-variable positivity** (APD, MPG, SBWF, the polar-configuration cone of PL): the exhausted one-variable shadow.
- **Conjugate-diagonal geometry** (CDG, PL): `D` from the `ξ` current and theta prefixes; depth distributions; local Weyl law; coercivity.
- **Torsion intersection theory** (AE): `Λ` as an intersection number; the torsion measure's potential (`ψ`) and Fourier coefficient (`M`); q-deformation; renormalized positive energies.
- **Deformation theory of positive systems** (BGG): Landau–Wronskian principle, Abel–Gram law, critical transfer and conservation, strong multiplicity one, the square-root deficit law.
- **Correspondence positivity and arithmetic polarization** (ACP, PL): the layer map of Weil's argument, local types, elliptic localizers, two forms, budgets.
- **Gauge geometry** (ACG, BGG, SP): gauge torus, successor holonomy, repulsion, first separations.

What none has is the adjunction: a positivity-preserving renormalization at the diagonal that keeps the Hecke law.

### 4.3 Criteria the field must meet

| Criterion | Test against the corpus |
|---|---|
| **Computability** | The positive form and its pairing are produced by identities (explicit formula, `ξ` current, resultants), not posited. Counting reformulations of the sign do not count. |
| **Renormalization** | A diagonal counterterm computed from the archimedean place and the pole, Hecke compatible, preserving positivity. |
| **Conjugate-diagonal reach** | Evaluates `Σ G(ρ, ρ̄)` for a class containing `\|f̂(ρ)\|²`, with an inequality for the Hecke defect beyond classical density. |
| **Selectivity** | Distinguishes `ζ` from the W1 battery: relaxations, coupled-class deformations, golden datum and complex fake, sign and Liouville twins, theta fibres at `a ≠ 0`, polar configurations with incommensurable lines. |
| **Gauge charge** | Sees the arithmetic point (`z = 1`, the gauge point `0`) and non-archimedean charge beyond the first prime; reproduces the first separations. |
| **Local type** | Localizes by a non-multiplicative operation, or carries a polarization; controls the alignment of zero ordinates with small primes. |
| **Deformation calibration** | Reproduces positive rigidity at zero-free ordinates, chirality, the square-root deficit law and critical conservation. |
| **Rank growth and fibre selectivity** | Section spaces of rank growing with the class; counting polarization depending on the fibre. |
| **Non-circularity** | No premise contains the conclusion; objects constructed before their sign. |
| **Uniformity** | Aperture, height, rank, damping and window controlled together; exceptional sets below the zero spacing. |
| **Calibration** | Weil for curves (`2g`, Hermitian `H¹`, Rosati transpose); hyperelliptic RH by counting; budget slopes `Σ mult²` and repulsion energy; exterior-count purity; `ℙ¹ × ℙ¹` effectivity; κ = 1 collapse; `κ ≥ 3`; conductor horizon; `W = D − Δ`; local Weyl law; Franel–Landau. |
| **New partial results** | Outputs that are not zero-free strips: a non-isolation law (Q1), an adjunction inequality on finite sets of orders (Q2), a gauge margin law (Q3), central nonvanishing for coupled classes (B3.34). |

### 4.4 Questions it must answer

1. **What is the Frobenius at infinity as a correspondence?** Which algebraic involution acts on the zero spectrum as complex conjugation, and on torsion cycles as `z ↦ z̄`?
2. **What is the self-intersection of the diagonal?** Which renormalization of the torsion self-energy is Hecke compatible and positivity preserving (Q2)?
3. **What bounds the equivariance defect of the computed positive form?** Which inequality controls `E_f(L)` (B3.33)?
4. **What is the arithmetic point?** How does the theory distinguish `z = 1` (the gauge point `0`) from the rest of the circle, and what is its period (completion law)?
5. **How does `σ_γ` localize beyond the conductor?** Are zero ordinates Kronecker aligned with small primes (Q1)?
6. **What is the non-archimedean gauge charge?** Does positivity keep separating the twins as primes enter (Q3)?
7. **What pays `ζ`'s own zeros?** Which structure bounds `Δ` by `D` uniformly in the depth?
8. **Is the coupled class bounded at the centre?** Do non-positive, non-rational members respect the ceiling (B3.34)?
9. **What selects the fibre?** Which count has a quadratic term depending on the characteristic and equal to the Rosati form at `a = 0` (B3.35)?
10. **What are the escape states of `ζ` at infinite height?** (B3.2)
11. **How does an average become a point?** Which selection principle reaches below the zero spacing?
12. **What is the base?** Which structure has a tensor loss independent of the power?

### 4.5 Tools

**Built:** the capacity identity and the Hecke law of `D`; coercivity, sampling and the local Weyl law of `D`; the `ξ` current and theta metrics; depth distributions and the two-scale variance law; the polarization law; local forms, boosts, resonance, `σ_γ`; twisted explicit formulas, conductor horizon, forcing half and gap; effectivity calculus, Tate's law, naive and convex heights, theta surface, polar box, horizon torsion, Farey potential; torsion intersections, the renormalized torsion energy, q-deformation; budget calculus over `ℤ` and `𝔽_q`; hyperelliptic RH by counting; completion law and Burgess at finite level; the gauge torus, finite lattice intertwiners, successor holonomy, Catalan and multi-prime repulsion; contraction and collision calculus; polar-configuration cone; deformation principle, Abel–Gram law, critical transfer, strong multiplicity one, square-root deficit law; phase kernels, Abel atoms, capacity, endpoint and shadow laws.

**Not yet built:**
- **Arithmetic adjunction:** a Hecke-compatible, positivity-preserving renormalization of torsion self-energies.
- **Defect inequalities:** upper bounds for the computed Hecke defect that are not classical density estimates.
- **Diophantine control at zero ordinates:** alignment of `γ log p` at the ordinates of zeros, with exceptional-set bounds.
- **Gauge margin laws:** positivity margins on growing prime windows, built from successor data.
- **Hermitian structures on correspondence spaces:** a Hilbert norm on zero transforms with the archimedean flow acting by computed similitudes.
- **Selective counting polarizations:** fibre-dependent counts with rank growing with the class.
- **Ceilings for non-positive members of coupled classes.**
- **Selection lemmas** at the zero-spacing scale.

### 4.6 Objects, language and mechanisms

| Layer | Content |
|---|---|
| **Objects** | • The characteristic circle `ℝ/ℤ` with its torsion characteristics `k/n`, Galois orbits `O_n`, torsion measures `ν_N`, the arithmetic point `z = 1`, power maps `z ↦ z^t` (Hecke), the Green function `−log\|1 − z w̄\|` and its Abel regularization `r`, log-discriminants, cyclotomic resultants, the horizon polynomial `P_N(q)`.<br>• The conjugate diagonal: `log\|ξ\|`, its Riesz measure, regularized potentials, depth distributions, theta prefixes.<br>• The two forms `W`, `D`, the defect `Δ`, the Hecke defect `E_f(L)`, the depth profile.<br>• The biarithmetic semigroup `⟨+1, ×p⟩`: gauge torus, gauge points and twins, successor connection and holonomy.<br>• Counting objects: polar surfaces, effectivity functions, naive and convex heights, theta surface, Jacobi–Hurwitz packets, horizon tori.<br>• Positive systems: completed, height-coupled and Fejér-coupled classes, polar configurations, deformations, anchors, ceilings, deficits.<br>• Escape objects: cofactor profiles, symbols, phase kernels, Abel atoms, gauge mass. |
| **Language** | It must distinguish: positive and equivariant; computed, bounded and posited; collided (conjugate) and Rosati (reflection) pairing; regularized and renormalized; energy and potential at a point; hyperbolic, elliptic and unipotent; resonant and localizing; even and odd sector; below and beyond the conductor; aligned and generic heights; gauge invariant and gauge charged; archimedean and non-archimedean charge; orbit and point; count and sign; soft and selective polarization; one-variable and two-variable; positive, rational and arbitrary deformation; ceiling and rigidity; surplus and deficit; classification and exclusion; average and individual zero. |
| **Mechanisms to discover** | • An **adjunction law**: the diagonal self-energy of torsion cycles renormalized by the archimedean place, positivity preserving and Hecke compatible.<br>• A **Hodge index law on the circle**: positivity of the renormalized pairing on degree-zero torsion cycles.<br>• A **defect law**: an inequality for the Hecke defect of `D`.<br>• An **alignment law**: Diophantine control of zero ordinates against small primes.<br>• A **gauge margin law**: positivity reading the sign gauge at every scale.<br>• A **conjugation law**: an algebraic correspondence acting as complex conjugation on the zeros.<br>• A **ceiling law** for coupled classes beyond positive deformations.<br>• A **base law**: a fixed tensor loss. |
| **First milestones** | (1) W15 and the exceptional-set version of Q1.<br>(2) W16: finite-set counterterms; the divergence comparison of Q2.<br>(3) W13, W17: two- and three-prime selectivity with margins; the margin law of Q3.<br>(4) W7(xiii)–(xiv): the log-Sobolev equivalence and `E_D = E_Δ` in Lean.<br>(5) W14: the collided form from finitely many theta values.<br>(6) W7(xi): the full-class ceiling at zero-free ordinates as central nonvanishing. |

Each milestone is a theorem of a kind the corpus does not yet contain: a forcing law of elliptic type, a renormalized positivity, a gauge margin at every scale, or a computation on the conjugate diagonal with an inequality attached, rather than a receiver, a blindness theorem, a deformation equivalence or a counting reformulation of the sign. Each programme standard adds its own requirements:
- **APD:** name the positive side, the spectral side, the gap and the integer.
- **ACG / BGG / SP:** name the gauge charge, its holonomy and its margin.
- **ACP / PL / CDG:** name the layer of Weil's argument, the local type, whether the carrier localizes, whether the positivity is collided, Rosati or pre-renormalization, and what bounds the defect.
- **AE:** name the currency, show the count is not one of the forms of the sign, and name the period it uses.
