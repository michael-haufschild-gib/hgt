# Research frontier summary: work, open mathematics, next questions, and a possible new field

Status: 2026-10-27, corpus `7eaf4d7ef` with working tree. This summary covers the 31 routes, 17 candidates, PW-B and the supporting programmes of the [complete report](route-obstacles.md). Companions: [walls ledger](walls-ledger.md), [route unification](route-unification-ledger.md). Evidence: corpus search and Lean statement reading, recorded in `logs/review-2710-v3-research-log.md`. Nothing was compiled. Labels `[L]`, `[S]`, `[P]`, `[R]` and the notation (`W`, `D`, `Δ`, `E_f(L)`, `M_f`, the field `E(ρ)`, the transverse energy `𝓔`, the torsion objects `I`, `c`, `β`, `P`, `K_q`, `G_r`, `Λ₂`) as in the complete report.

## 0. The frontier in twenty statements

1. **`ζ` has a computed positive form and a computed equivariant form, and RH says they are one form.** Weil's form `W` is Hecke equivariant and has finitely many negative directions at every aperture; the collided form `D` is positive, faithful, the logarithmic Sobolev norm, and computed without zero indexing; `Re W = D − Δ`.
2. **The equivariance defect of `D` is a moment of inertia.** `4L² M_f ≤ E_f(L) ≤ 8(cosh L − 1)M_f` with `M_f = Σ m δ²|f̂(ρ)|²` [L]; RH is `M_f = 0` for every test, equivalently sub-doubly-exponential dyadic growth of every Hecke defect [S].
3. **`D` amplifies like the genus in Weil's tensor-power argument, and the amplification only converts rates.** A positive Hecke defect doubles its angle under `L ↦ 2L` with the fixed loss `D(f)` [S]; a dyadic growth rate becomes a depth bound and nothing stronger [R].
4. **RH has exact electrostatic forms, all computed and quantized.** Zero transverse energy; energy below one quantum; every unit window below two quanta; every right zero feeling a transverse field at most `1`, or below `√(2c log γ)` [L]. Finite energy is finite off-line index. Equilibrium of finite reflection-closed configurations is criticality [L].
5. **What is missing on the zero side is an upper bound of size `√log γ`.** Every off-line zero has a terminal with field `≥ m/(2a) + c·a·log γ`, a zero-free outward ray with a reserve of the same size, and a zero-free lens [L/S]; the excluding inequality is an upper bound at right zeros below `√(2c log γ)`, not equilibrium.
6. **A deep zero forces the primes out of alignment at its own ordinate — outside the strip.** For `σ > 1`, `Σ Λ(n) n^{−σ} cos(γ log n) ≤ Re(Γ-part)′ − m/(σ − β)` [L]; no interior counterpart is proved.
7. **Every unconditional positivity found is invariant, averaged or statistical, non-localizing, on nonnegative tests, collided, twisted below the conductor horizon, a finite-window certificate, local at one prime, carried by a scalar or rank-one counterterm, coefficient positivity of a source, or a zero-side reserve.**
8. **Multiplicative symmetry is hyperbolic exactly at off-line pairs; elliptic localization in correspondence-closed carriers is resonance; `σ_γ` is the only reflection-compatible affine localizer; its odd-sector certificate and the conductor horizon are disjoint at every height.**
9. **Torsion-side renormalization cannot keep positivity.** The torsion germ's counterterm is the identity, so every renormalization has survival cone `{0}` [L/S]; the minimal counterterm on orders `≤ N` lies between `½ log(N/2)` and `4 log N + O(1)`, with its divergence at the arithmetic point; the Hecke cocycle `β(n, t) = log t − (tame different)` is not a bounded coboundary [L].
10. **The archimedean germ keeps positivity on a hyperplane, and the arithmetic point completes it.** Its counterterm is rank one; `−ψ(x_i + x_j)` is PSD on `Σ c_i = 0`; the node `{1}` cancels the archimedean divergence and gives a kernel PSD on all vectors [L/S]. Gauss's digamma theorem makes the torsion energy and the archimedean germ Fourier dual, with `log N` the anomaly of `[N]` [L].
11. **Local Hodge index holds at every prime and does not sum.** The prime kernel is a sum of transverse tower forms `log p (K_q − I)`, each two-sided bounded [L]; the global prime form has no `ℓ²` ceiling, already along the pole direction `x_n = n^{−1/2}` [S]. The global sign must be paid by the archimedean place.
12. **Counting is the sign over `ℤ` and proves the sign over `𝔽_q`.** Section counts, effectivity, heights, one-sided counts, a fixed tensor loss, horizon torsion and the Farey sum are each RH; over `𝔽_q` hyperelliptic RH is proved by counting [L].
13. **The prime-error budget is RH; with its Abel slope at the genus it is RH with simple zeros** [L].
14. **Gauge charge sits exactly in non-square couplings.** A coupling is blind under every real sign gauge iff `nab` is a square; successor couplings are charged; cell dilations fix the Euler gauge [S]; electrostatics is blind to the archimedean twist [L].
15. **Unconditional positivity of `ζ` separates it from the first sign twins, permanently.** At `181/500` and `23/40` the twins fail on witnesses where `ζ` is positive, and the Liouville ground eigenvalue stays below `−3/10` at every aperture `≥ 23/40` [L]. No margin law on growing windows exists.
16. **One-variable positivity is exhausted; collective packets amortize only through commensurability.** Positive packets on `ℚ`-independent ordinates buy at most their pole share [S].
17. **Deformations detect, they do not force, and they cannot be undone.** Positive rigidity, chirality and central ceilings at `γ` are the absence of (off-line) zeros at `γ`; surplus residues are even central drops; positive deformations form a monoid without nontrivial units [L/S].
18. **Escape classifies and never excludes.** RH is positive gauge mass of every escape state [L].
19. **Statistics place most zeros near the line and exclude none, but a quantized statistic would.** `3/4` of the zero copies lie within `4/log T`; `4/5` of the ordinates are critical [L]; a window energy below `2` excludes every off-line zero in the window [L].
20. **Over `𝔽_q` every ingredient of Weil's argument is now located over `ℤ` [R]:** the regularized Hermitian structure with Hecke similitudes, local Hodge index, and the non-scaling amplification loss exist; a finite self-intersection of the diagonal, archimedean payment of the local-to-global divergence, and a lattice spectrum at the arithmetic point do not.

## 1. Just work

Known mathematics suffices for each item, and none crosses a wall. An item's outcome may be unknown; what is known is the method.

| ID | Task | Concrete content | Completion criterion |
|---|---|---|---|
| **W1** | Selectivity battery | Test every mechanism against:<br>• pole-order-2/3 relaxations, strip-pole quartets, over-regular Beurling systems, the Siegel family, twisted boundary systems;<br>• the golden datum and the complex fake;<br>• the Liouville, `{2,3}`-flipped, sign-flipped and dominated twins; Haar-typical and Kronecker twists; shifted pairs;<br>• height-coupled lifts, `W_β`-split members, rational and positive deformations, arithmetic members with square-root deficit;<br>• theta-surface fibres; Jacobi–Hurwitz packets; square-class kernels; lattice versus cell dilations;<br>• torsion energies at `r < 1`; the lattice germ off the polar hyperplane; periodic germs with and without relations;<br>• white noise, reset-origin mixtures, Abel atoms; synthetic configurations with several off-line pairs of different depths; packets on independent and harmonic ordinates.<br><br>Calibrations to reproduce: `κ = 1` collapse; Fejér barrier; `κ ≥ 3`; Weil for curves with budget `2g`; hyperelliptic RH by counting; budget slopes over `𝔽_q`; `W = D − Δ`; local Weyl law; the moment-of-inertia law; transverse equilibrium; the field threshold; local tower bounds; torsion survival cone `{0}`; Fekete equilibrium of the torsion. | Each mechanism records the model that defeats it, its local type, whether its positivity is collided, Rosati, local, counterterm-carried or zero-side, whether its couplings are square class, and whether its counting polarization is fibre-selective. |
| **W2** | Finite identities and certificates | Gram, Hausdorff, Hankel, Jensen blocks; finite heat transforms; schedules and histories; finite Robin, Li, JAS and Vaughan budgets. | Every finite term certified; no cofinal claim. |
| **W3** | Premise checks | Regularity, support, decay and domain membership for named tests and families (SZ limits, CHMD domains, candidate sources, twisted detectors, the pole-neutralized continuum form, cofactor families). | Hypotheses of existing transfers discharged. |
| **W4** | Transport of proved inputs | Restate in RW, SZ, CHMD, EWU, OWU, ACT, AIP, HF, ACS, SRT coordinates: averaged and positive-proportion positivity, zero-ordinate positivity, the conductor horizon, the forcing half and gap, the log-Sobolev equivalence, the finite negative index, the outward reserve, the census, the moment-of-inertia law, the field threshold, window quantization, VK-rate escaped decay, Kloosterman dispersion. | Each conclusion stated at its true strength. |
| **W5** | Certified extensions and constants | The full floor of `ζ` beyond `181/500`, first at `23/40`, then past `log 5/2`; odd and primitive windows; explicit `κ₀, C₀, Γ₀`, `sharpCollarConst κ`, the conductor-horizon constant `C`, the log-Sobolev constants `c_A, C_A`, the outward constants `C, c`, the field-threshold constant `c`. | Certified finite-aperture theorems with explicit constants. |
| **W6** | Two- and three-prime selectivity tables | At `23/40`: `inf (W_ζ(F) − W_ω(F))/‖F‖²` over odd separating tests for each of the four sign patterns on `{2, 3}`; then the `{2, 3, 5}` window (`2A > log 5`); successor- and cell-built separating tests (Catalan links `2 → 3 → 4`, `8 → 9`). | A certified margin table per window; the margin as a function of the window. |
| **W7** | Short windows to the classical range | Selberg's near-line density is formal on windows `≥ U^{99/100}`; extend to `U^{1/2+ε}` and replace `Γ^{99/100}` by `Γ^{1/2+ε}` in the averaged, zero-ordinate, positive-proportion theorems and in WL's filtered deficit. | The theorems on `Γ^{1/2+ε} ≤ H ≤ Γ/8`. |
| **W8** | Quadrature for the conjugate-diagonal readings | Replace the continuous integrals of the polynomial theta metric and of the local detector by finite quadrature with explicit error, using the strip amplitude bounds and the fixed-strip cutoff. | `D`, its depth moments, `M_f` and the local detector from finitely many integer theta values. |
| **W9** | Moments over zero ordinates | `Σ_{0<γ≤T} P_a(γ)^{2k}` for the detector polynomial `P_a`, and for the smoothed prime sums of W10, by the smoothed Landau formula (`exists_smoothedLandau_le`); the exceptional set `{γ ≤ T : P_a(γ) > (1 − η) log γ}`. | Moment and exceptional-set theorems for lengths `≤ (log T)^C`; first input of Q1. |
| **W10** | The interior prime reading of the reserve | Express the outward reserve on a terminal's zero-free ray through the explicit formula: a lower bound `≥ c·a·log γ` for a smoothed prime sum `−Re Σ Λ(n) n^{−σ−iγ_p} k(log n)` at the terminal ordinate, with explicit length — the interior counterpart of the exterior anti-alignment law. | "An off-line zero of depth `a` forces a large smoothed prime sum within `C log γ` of its ordinate"; second input of Q1. |
| **W11** | Torsion counterterm constants | The exact leading constant of the minimal torsion counterterm `κ_min(N)` (now `½ log(N/2) ≤ κ_min ≤ 4 log N + O(1)`) and of the arithmetic-point bound; the archimedean self-energy of an atom at the matched regularization `ε ≍ 1/N` through Gauss's digamma formula. | `κ_min(N) = C log N + O(1)` with explicit `C`, and the matching archimedean constant; first input of Q2. |
| **W12** | Survival cones of coupled germs on finite order sets | For finite `S`, compute the counterterm, its rank and its survival cone for torsion ⊕ lattice ⊕ pole-node families, for Ramanujan twins and for periodic germs with repeated modes (Cesàro Gram, module of relations); compute the Hecke variation of the coupled finite part and compare it with `β(n, t)` and with the regulator anomaly `t log t` of pulled-back cycles. | A table of ranks, cones and variations; second input of Q2. |
| **W13** | Electrostatic dictionary | `𝓔 ≤ 𝓔_copy` and the converse comparison with multiplicities; the field threshold, window energy and moment of inertia in PL, HF and ACS coordinates; the sign of the field off the deepest pair on synthetic multi-pair configurations; Kronecker dilution calibrations. | One electrostatic dictionary theorem per receiver. |
| **W14** | Census assembly | Combine the simple off-line core with the TTPC surplus, Selberg's near-line density and the multiplicity exclusion; state the `3/4` problem as a bound on simple off-line zeros within `4/log T`; transport the census to RW, WL and ACS receivers. | One census theorem in receiver coordinates. |
| **W15** | Depth homogeneity, remaining classes | The loss law for `k`-level forms and Følner coupling. | One theorem per class. |
| **W16** | Range-limited growth inputs | State the VK step, and the VK-rate escaped Möbius decay, as `δ`-range instances of the growth-to-forcing law. | VK as an instance of `exclusion_iff`. |
| **W17** | Contraction calculus, last items | Whether a complex quartet at depth `1/4 < a < 1/2` contracts at `Δκ = 1` with the boundary pole as anchor; a minimum-tax theorem for finite rational multipliers. | Each statement in Lean as a calibration. |
| **W18** | Corollary assembly | (i) An averaged bounded-energy statement for WL. (ii) One rate dictionary for RW, SRT, ACS through `groundRate = polarRate`. (iii) The explicit LA/WD residual region. (iv) Replace the imported `c/(log\|t\|)^9` collar by the MPG or SBWF calibration. (v) Conservation for infinite reflection-antisymmetric corrections. (vi) One capacity law: boundary, collar, gauge, family, Abel–Gram and `ζ^d` capacities. (vii) The full-class ceiling at zero-free ordinates as central nonvanishing, and the quantization law in ACS coordinates. (viii) One collided-positivity theorem: kernel counts, coupled counts, escape Cauchy forms, `D`, with the Hecke law and the moment-of-inertia law. (ix) `E_D = E_Δ` and the `ξ`-current formula for `E_f(L)` in PL and HF coordinates. (x) The Mertens converse under RH, simple zeros and `J_{−1}(T) ≪ T` (Ng's method). (xi) Gårding's inequality as a finite-rank-counterterm instance of the survival law. | Each statement proved from existing theorems. |
| **W19** | Working sources | The modules marked `[S]` in the frontier map, completed at their stated strength. | Each statement at its stated strength. |

## 2. Open mathematical obstacles

### 2.1 Tier B1: RH-strength closing statements

Each is equivalent to RH or stronger. Solving one closes every route that uses it.

| ID | Statement | Routes |
|---|---|---|
| **B1.1** | **Critical signed cancellation at every positive slack.** Bounded critical deficit energy; one-sided lag or Abel moments; the history floor; the regularized abscissa `1/2`; the JAS half-power budget; Mertens at square root; the one-sided count; the Farey sum at `√N`; typicality of the gauge point `0`. | WL, MC, FU, RP, PBM, JAS, SRT, DR |
| **B1.2** | **Signed small-damping energy.** Admission at every damping; subpower receiver energy; positive gauge mass of every escape state; signed long-modulus quadrature; a Báez–Duarte residual `→ 0`. | PM, CTF, BVI, MC, PW-B |
| **B1.3** | **Positivity of the equivariant form.** `W ≥ 0` at all apertures; zero negative index; the one-sided Weil inequality at one prime; one shift; sufficiency of the free budget; Rosati positivity; nonnegative symmetric-square spectra; the nodal inequality; positive Suzuki first variation; odd capacity; global allocation; Bézout on the exact source cone. | RW, SZ, CHMD, EWU, OWU, ACT, AIP, TT, HF, ACS, SRT |
| **B1.4** | **Selection.** From short-window averages, positive proportions and almost every zero ordinate to every height, signed test and aperture. | WL, SRT, ACS, APT |
| **B1.5** | **Critical-endpoint heat and moment sign.** Residual heat region; all-rank Hankel positivity at one time; both heat grids; rank-uniform Schur decay; the Newton margin; order-uniform passivity. | LA, WD, TH, HCF, GTA, XN, PA |
| **B1.6** | **Forcing and exhaustion for a realization.** Exhaust the maximal blind ideal with an input outside the exhausted classes (invariant, non-localizing, nonnegative-test, multiplicative, square-class, one-variable, collided, twisted below the horizon, counting, deformation, counterterm-carried, local, zero-side reserve). | TG, RN, WD, ACS, all candidates, PW-B |
| **B1.7** | **Single-currency endpoints.** BSY contrast equality; the subexponential Li floor; the eventual Robin tail; recurrence near possible zeros; `D_idx < 2`. | FEL, LI, RB, BAG, HF |
| **B1.8** | **RH with simple zeros.** Faithful positive Meyer degree; RR for the Hilbert–Schmidt reserve; the Abel slope at the genus. | ACS/Meyer faithful branch, WL |
| **B1.9** | **Counting forms of the sign.** Effectivity function; no abundant class; naive heights; convex heights; fixed tensor loss; section count; horizon torsion; the Farey sum; a bounded-below asymptotic subquadratic height. | HF, ACS, AOG, SRT, WL |
| **B1.10** | **Budget currencies.** A linear prime-error budget (⇔ RH); a Mertens budget (⇒ RH + simple + summable residues); the Abel slope at the genus (⇔ RH + simple). | WL, MC |
| **B1.11** | **Equivariance of the positive form.** `D` Hecke invariant; one Hecke translation a similitude of `D`; `E_f ≡ 0`; `M_f = 0` for every test; dyadic Hecke defects sub-doubly-exponential; `Δ ≡ 0`; `W = D`. | HF, ACS, PM |
| **B1.12** | **Central ceilings and chirality.** Rational or positive central ceilings, or positive chirality, at every `γ ≠ 0` (each RH, ordinate by ordinate); the full-class ceiling at every `γ` (implies RH; converse open, B3.22). | ACS, SBWF |
| **B1.13** | **The field and energy forms.** Every right zero feels a transverse field `≤ 1`, or `< √(2c log(|γ| + 4))`; `𝓔 < 1`; every unit window has energy `< 2`; transverse force zero at every zero with `𝓔 < ∞`; an arithmetic upper bound for `Re(ζ′/ζ + Γ-part)` on every terminal's outward ray below its reserve. | HF, ACS, OWU, SRT |

### 2.2 Tier B2: classical open problems weaker than RH

| ID | Problem | Where it is the next rung |
|---|---|---|
| **B2.1** | Quasi-RH: a fixed zero-free strip. | Every graded receiver; admission at fixed damping; energy growth; dyadic Hecke growth at a fixed rate; one-sided Lefschetz bounds; escaped Möbius pairings at a fixed `θ`; large-sieve section supply. |
| **B2.2** | Finite off-line index. | Equivalent to finite transverse energy `𝓔 < ∞` [L]; HF/AOG index exit; WD collision masses. |
| **B2.3** | Simplicity of the zeros. | Operator-norm faithful realizations; Mertens budgets; the Abel slope; `𝓔` versus `𝓔_copy`. |
| **B2.4** | Density hypothesis; large values beyond Guth–Maynard. | Averaged positivity at larger aperture; filtered deficit; bounds on `M_f` (B3.21); exceptional sets of B3.24. |
| **B2.5** | At least `3/4` of the zeros on the line. | The census reduces it to a bound on simple off-line zeros within `4/log T`; surplus `β ≤ 1/18`; parity-breaking dispersion at `λ = 4/3`. |
| **B2.6** | Power-saving sign correlations of `μ`, `λ`. | MC anti-alignment; SSA constants. |
| **B2.7** | Uniform Hardy–Littlewood prime-pair correlations near the square-root band. | TTPC; the stabilizer discrepancy at `λ = 4/3`. |
| **B2.8** | Subconvexity and growth near `Re s = 1`. | KKL horizon; growth input of multiplicative positivity. |
| **B2.9** | Better de Bruijn–Newman bounds. | Shrinks the B1.5 region. |
| **B2.10** | Near-line density on windows shorter than `T^{1/2}`. | Averaged positivity on windows `Γ^θ`, `θ < 1/2` (B3.5). |

### 2.3 Tier B3: open problems isolated by this research

No solution is known, and none is proved RH-equivalent.

| ID | Question | Present boundary |
|---|---|---|
| **B3.1** | `polarRate = Δ` when off-line zeros cluster. | Equality when copies or depth mass are locally bounded; form-norm rate `= Δ` unconditionally. |
| **B3.2** | **Exclusion of infinite-height escape for `ζ`.** | Classification complete [L]. |
| **B3.3** | Quantitative coercivity of residual/trace reconstruction. | Algebraic injectivity; kernel `ℝ q_ε`. |
| **B3.4** | Signed shell flux along the moving prime-threshold ladder. | Birth jumps vanish; collar bound. |
| **B3.5** | Averaged positivity on windows `Γ^θ` below the classical range. | `θ = 99/100` proved; `θ > 1/2` is W7. |
| **B3.6** | A nonlocal shared-budget calculus with prime-weighted remainder; payment of the pole-neutralized continuum form; growing-packet signed compensation. | Frustration and descent laws; polar-neutral collapse; raw continuum towers negative at order `e^A`; joint `2, 3` payment at `23/40`; fixed-packet Kloosterman correction. |
| **B3.7** | Arithmetic input on the residual heat region. | Model geometry complete. |
| **B3.8** | Compatible oriented families. | Spline-orbit index `≤ 1` ⇔ RH. |
| **B3.9** | Sub-half-damping signed control of the forward interior. | Exterior paid; `ε = 1/2` bounded. |
| **B3.10** | Order-uniform PA thresholds; decoupling rank from time. | Fixed-order thresholds. |
| **B3.11** | Sharp successor constants beyond conductor 3. | Odd shifts `1/3`, lag 2 `1/4`. |
| **B3.12** | Is the paid ideal nonzero on escape? | Would exclude white noise, not translated-zero states. |
| **B3.13** | Equality case of collar capacity at even `κ`. | Odd `κ` sharp. |
| **B3.14** | Signed near-coincidence cancellation at one height beyond aperture `½ log Γ`. | Single-height phase-selective law. |
| **B3.15** | An unconditional nontrivial estimate for a gauge-charged statistic of `μ` or `Λ` at the point `0` beyond the square-root threshold. | Haar-typical twists meet every budget; charged boundaries normalize at `1/4`; coalescent surplus is pure gauge charge. |
| **B3.16** | **The non-archimedean gauge charge with a margin**: positivity of `ζ` separating it from every sign twin on growing prime windows, with a margin that survives aperture growth. | Square-class couplings blind, successor couplings and cell dilations charged [S]; first windows separated, Liouville separation permanent from `23/40` on [L]; full floor at `23/40` uncertified. |
| **B3.17** | **Form positivity of the renormalized Rankin–Selberg source beyond isotropy.** | `(ζ′/ζ)² = L(Λ ⋆ Λ)`; its simple Laurent coefficient is `2m` times the field; `Λ₂ = μ ⋆ log² ≥ 0` with `L(Λ₂) = ζ″/ζ` renormalizes the double pole to `m(m − 1)` [L]; coefficient positivity only. |
| **B3.18** | Lower bounds or arithmetic use of the successor defect `D_Λ` on vertical lines. | Pointwise `(\|s\| + 1)^{1−σ+η}`; mean square exact. |
| **B3.19** | Stepanov auxiliaries over `ℤ` outside the one-prime Hecke algebra. | Hyperelliptic RH by Stepanov; sparse annihilators need a lattice spectrum; the integrality floor stops below PNT; the arithmetic point has no period. |
| **B3.20** | **The odd-sector sign beyond the conductor horizon** at the ordinate of a hypothetical off-line zero. | Forcing half; horizon; gap at every height [L]; reduces to B3.24 [R]. |
| **B3.21** | **A non-classical upper bound for the moment of inertia** `M_f` (equivalently the computed Hecke defect) from the prime or theta side. | `D` computed; `E_f ≍ M_f`; dyadic amplification and Stieltjes moments [L/S]; uniform-in-`L` bounds are rates, height averages are density estimates [R]. |
| **B3.22** | **The full coupled class at the centre**: at zero-free ordinates, does every member of `HeightCoupledSystem 2 1 1 γ` satisfy the ceiling? | Positive and rational subclasses settled; surplus quantized; ceiling transfers to factors [L]. |
| **B3.23** | **A selective counting polarization**: counts of rank growing with the class, fibre-dependent, equal to the Rosati form at the fibre of `ζ`. | Theta surface soft; lattice counts collapse; large-sieve majorants inflate; Serre-dual box cohomology fails RR on the golden datum. |
| **B3.24** | **Alignment at zero ordinates.** Can `γ log p` (small `p`) align modulo `2π` at zero ordinates so that a short prime polynomial reaches `(1 − η) log γ` (detector), `c·a·log γ` (reserve) or the field threshold `√(2c log γ)`, except on a set sparse enough for density estimates? | Exterior anti-alignment at `σ > 1` [L]; smoothed Landau formula [L]; moments not computed (W9, W10); Kronecker dilution of independent ordinates [S]; multi-prime repulsion [L]. |
| **B3.25** | **Coupled renormalization of the two places.** A regularized family coupling the torsion germ (prime place), the archimedean lattice germ at the Fourier-dual rational nodes and the pole node, whose joint counterterm has rank below the number of orders, whose survival cone contains nonzero Weil test vectors, and whose renormalized limit is Weil's atomic form; equivalently, archimedean payment of the local-to-global divergence of the prime form. | Torsion cone `{0}`; archimedean polar hyperplane; pole node PSD; periodic-germ cone = module of relations; local tower bounds; no global `ℓ²` ceiling; `κ_min ≍ log N` [L/S]. |
| **B3.26** | **Anomaly cancellation.** The Hecke cocycle `β(n, t) = log t − Σ_{p∣t,p∤n} log p/(p − 1)` of the renormalized torsion pairing is the regulator anomaly of `[t]` (cutoff `r ↦ r^t`) minus the tame different. Is there a coupling to the archimedean germ and pole node whose finite part is Hecke covariant? | `β` nontrivial; covariance up to the degree character on saturated cycles; projection-formula anomaly `t log t`; Gauss digamma `log N` anomaly [L]. |
| **B3.27** | **Outward upper control off a sparse set**: an arithmetic upper bound for `Re(ζ′/ζ + Γ-part)` on outward rays of terminals, below `c·a·log γ`, outside a set of ordinates sparse enough to exclude isolated deep zeros. | Reserve, terminals and lens [L/S]; under RH `‖ζ′/ζ‖ ≤ C log γ/(σ − 1/2)`; the same Diophantine content as B3.24 [R]. |

### 2.4 Settled questions

- **What computes `D`, which norm it is, and what its defect measures.** The `ξ` current and polynomially many theta values; the log-Sobolev norm; the moment of inertia `M_f`.
- **The electrostatic forms of RH and their quantization.** Energy, unit windows, field threshold `1` and `√log`; finite energy ⇔ finite index; finite equilibrium ⇔ criticality.
- **Whether an off-line zero is visible at its own height.** Yes: terminal, field, outward reserve, lens; exterior anti-alignment of the primes.
- **Whether torsion-side renormalization keeps positivity.** No: identity counterterm, survival cone `{0}`, logarithmic counterterm, nontrivial cocycle.
- **Whether local positivity at each prime sums.** No.
- **Which couplings are gauge charged.** Exactly the non-square-class ones; cells fix the gauge.
- **The forcing gap.** Proved at every height.
- **The first gauge-charged windows.** Separated at `181/500` and `23/40`; Liouville separation permanent.
- **Escape.** Classified completely.
- **Deformations of the coupled carrier.** Rigid exactly at zero-free ordinates; surplus residues quantized; positive deformations irreversible.
- **How far statistics reach.** `3/4` of the copies within `4/log T`; `4/5` of the ordinates critical.
- **Counting over `𝔽_q`.** Hyperelliptic RH by Stepanov and Gauss sums, split case included.
- **Also settled:** kernel counts as heights (no); section counts, effectivity, naive heights, one-sided counts and tensor bases are the sign; elliptic localization is resonance; symmetric-square spectra are the sign at one prime; contraction and collision calculus; positive polar-configuration cone; theta `h⁰` does not extend; multiplicative lattice forms blind; the first gauge charge is a twist; theorem of the square and budget free; positivity beyond isotropy only without localization; `κ = 1` class; Lefschetz receivers at one and two primes; linear loss; twists rate neutral; averaged positivity at `Γ^{99/100}`; absolute pole-order budget false; the prime-error budget is RH; dyadic amplification converts only rates.

## 3. The three questions to answer next

**Selection criteria.**

1. The question is weaker than RH, so it can be answered.
2. Either answer changes the frontier: a positive answer adds a mechanism; a negative answer is a sharp no-go naming the missing input.
3. Together the questions cover the three walls.
4. The output is not a zero-free strip, a collided positivity, a counting reformulation, a gauge-orbit statement, a one-variable positive system, a deformation equivalence, a zero-side detection or a scalar-counterterm renormalization.
5. The question addresses the polarization problem in its present form: a form that is positive and equivariant at once, or an inequality that turns a detection into an exclusion.

**Why these three.** The zero side now has an exact target: an upper bound of size `√log γ` for the field at right zeros, and the exterior law shows that the primes do anti-align at a deep zero's ordinate outside the strip; whether this survives inside is a Diophantine question with a concrete toolkit (Q1). The diagonal question of the previous frontier is answered on the torsion side — renormalizing the prime place alone destroys positivity — and the corpus has located the exact survivor: the archimedean germ with the arithmetic-point node, Fourier dual to the torsion energy; the remaining adjunction question is whether coupling the two places lowers the counterterm rank and cancels the Hecke anomaly (Q2). Gauge charge has been located structurally in non-square couplings and cells; whether positivity reads it at every scale is still open (Q3).

### Q1. Alignment at zero ordinates: can the zero-side reserves be bounded above off a sparse set?

> *At the ordinates of zeros, can the short prime sums produced by the zero-side detectors be bounded above — the transverse field at right zeros below `√(2c log γ)`, the smoothed prime sum on a terminal's outward ray below `c·a·log γ`, the odd detector polynomial `P_a(γ₀) = Σ_{n ≤ e^{2a}} Λ(n) n^{−1/2} cos(γ₀ log n) k_a(log n)` below `(1 − η) log γ₀` beyond the conductor — for every zero, or outside a set sparse enough for zero-density estimates to exclude it?*

- **Why.**
  - The field threshold makes the target exact: RH ⇔ every right-zero field `< √(2c log(|γ| + 4))` [L]. The witness gives a lower bound `m/(2a) + c·a·log γ` at a terminal within `C log γ` of every off-line zero; the missing inequality is the matching upper bound.
  - Outside the strip the inequality exists: a zero of multiplicity `m` at `β + iγ` forces `Σ Λ(n) n^{−σ} cos(γ log n) ≤ Re(Γ-part)′ − m/(σ − β)` for `σ > 1` [L]. The interior counterpart (W10) is the reserve read through the explicit formula on the zero-free ray.
  - The `σ_γ`-odd detector is the only localizing sector whose positivity forces, and the gap between horizon and threshold is a theorem; the remaining route through it is a sign beyond the horizon at zero ordinates.
  - Landau's formula makes sums over zero ordinates explicit, and the corpus has its smoothed form [L]. Kronecker dilution [S] says a cloud of companions with independent ordinates cannot be amortized collectively, so a forcing argument must use arithmetic relations among ordinates or act zero by zero.
- **Route.** W9 (moments over zero ordinates, exceptional sets); W10 (interior reading of the reserve); compare `|E_T|` with `N(1/2 + δ, T)` and with the local count of the forcing half; iterate the forcing half outside `E_T`.
- **Weaker-than-RH content.** A non-isolation law (an off-line zero of depth `δ > 1/(2θ)` at a non-exceptional ordinate has a companion within `(log γ)^θ`), or exclusion of deep zeros at non-exceptional ordinates.
- **Outcomes.**
  - *Yes, outside a sparse set:* the first localizing mechanism that forces, and a theorem excluding isolated deep off-line zeros at non-exceptional ordinates.
  - *No:* zero ordinates can be aligned with the first primes; zero-side detection cannot be turned into exclusion by Diophantine means, and forcing must come from a renormalized polarization (Q2).

### Q2. Coupled renormalization: does coupling the two places lower the counterterm rank and cancel the Hecke anomaly?

> *The torsion germ (prime place) has identity counterterm and survival cone `{0}`; the archimedean lattice germ has counterterm `𝟙𝟙ᵀ` and survives on the polar hyperplane; the arithmetic point `{1}` is the node whose self-energy is the archimedean divergence; Gauss's digamma theorem makes the torsion energy on `μ_N` and the lattice germ at `k/N` Fourier dual, with anomaly `log N`. Is there a coupled regularized family — torsion orbits, lattice germ at the rational nodes, pole node — whose joint counterterm has rank below the number of orders, whose survival cone contains nonzero Weil test vectors, and whose finite part is Hecke covariant — the archimedean side absorbing the regulator anomaly of `[t]` and the tame different that make up the cocycle `β(n, t)`?*

- **Why.**
  - The previous form of this question is answered: no diagonal counterterm on the torsion side alone keeps positivity (survival cone `{0}`; minimal counterterm `≍ log N`; divergence at the arithmetic point; `β` not a bounded coboundary) [L/S].
  - Local Hodge index holds at every prime and the sum diverges [L/S]; in Weil's form the divergence is paid by the archimedean self-energy `log(1/ε)` of an atom of width `ε` — the same `log N` that appears as the anomaly in Gauss's formula and as the size of `κ_min(N)`.
  - On saturated cycles the Hecke variation is the pure degree character `−log t Σ x_n²`: the regulator anomaly of `[t]`, which moves the cutoff `r ↦ r^t` (the archimedean flow acting on the regularization); for pulled-back cycles the projection formula gives `−t log t` per unit mass [L]. Weil's form has a translation-invariant archimedean term and no anomaly. Both sides are explicit, and whether a coupled finite part is covariant is a computation.
  - The pole node already performs a matched cancellation between the archimedean divergence and the arithmetic point [S]; the periodic-germ law says positivity survives exactly on linear relations among modes [S], so the coupling must create relations among torsion modes.
- **Route.** W11 (the exact constant of `κ_min(N)` against the archimedean constant at matched regularization); W12 (ranks, survival cones and Hecke variations of coupled families on finite order sets); test the candidate coupling on the Laurent self-terms of `Λ ⋆ Λ`, where degree renormalization `m² → m(m − 1)` is already positive (`Λ₂ ≥ 0`).
- **Weaker-than-RH content.** On every finite set of orders the question is finite-dimensional linear algebra and an identity for the Hecke variation; a bounded residual counterterm, or Hecke covariance of the coupled finite part, is a theorem about computed objects, not a sign.
- **Outcomes.**
  - *Yes:* a computed renormalized pairing that is positive on a nontrivial survival cone and Hecke covariant — positivity and equivariance in one form; Weil's sign becomes the statement that the survival cone contains the test space.
  - *No:* coupling the two places at the diagonal cannot join positivity and equivariance; a carrier with a genuinely two-dimensional diagonal (a surface) is necessary, and the obstruction names its invariant (rank or anomaly).

### Q3. Gauge persistence: does unconditional positivity of `ζ` keep separating it from its sign twins as primes enter?

> *For windows reading the first `N` primes, is there, for every real sign gauge `ω` differing from the Euler vacuum on `{p ≤ p_N}`, an explicit test on which `ζ`'s form is positive and the twin's form negative, with margin bounded below by an explicit function of `N` — and can the separating tests be built from charged data (successor couplings, cell dilations) rather than certified numerics?*

- **Why.**
  - A `ζ`-specific sign must read gauge-charged data. Square-class couplings are blind and successor couplings charged; the dyadic cell dilation is covariant only at the Euler gauge, with explicit reach `2X + 1` [S]; electrostatics is blind to the archimedean twist [L], so the charge must enter through the arithmetic computation.
  - Separation exists and persists: the Liouville twin fails at `181/500` and at every aperture `≥ 23/40` on witnesses where `ζ` is positive [L]. What is missing is the full floor of `ζ` at `23/40`, the other sign patterns, and a margin law.
  - Archimedean twists approach the Liouville vacuum at most stretched-exponentially fast [L]; a margin law decides whether positivity reads the gauge point at all scales.
- **Route.** W5, W6 (the `23/40` floor, the margin table of the four `{2, 3}` twins, the `{2, 3, 5}` window); separating tests built from cell dilations and Catalan links; the margin as a function of `N` and of the aperture.
- **Outcomes.**
  - *Separation with a surviving margin:* the first unconditional positivity that reads non-archimedean arithmetic at every scale.
  - *Separation with a collapsing margin:* a measured threshold where positivity stops seeing arithmetic.
  - *No separation beyond some `N`:* a sign twin indistinguishable from `ζ` by unconditional positivity on every certified window; charged additive structure is necessary inside the form, not only in its gauge fixing.

The three questions are the forcing problem in each wall's currency:
- Q1: what a reserve at one height can force (Wall 1, face 1.21; Wall 3, face 3.19).
- Q2: whether positivity and equivariance become one form through coupled renormalization (Wall 14, faces 14.24, 14.26, 14.27; Wall 3, face 3.23; Wall 1, face 1.16).
- Q3: whether positivity carries non-archimedean gauge charge at every scale (Wall 1, face 1.18; Wall 3, face 3.18).

**Considered and not chosen.**
- **A bound for the moment of inertia (B3.21).** Uniform in `L` it is a graded rate (dyadic amplification turns it into a strip); averaged over heights it is a classical density estimate; a non-classical bound needs the structure Q2 asks for.
- **Window energy below two (B1.13).** For one window it is local RH there; for all windows it is RH. A quantized receiver, not a weaker target.
- **The full coupled class at the centre (B3.22); the `3/4` problem (B2.5); a selective counting polarization (B3.23); exclusion of infinite-height escape (B3.2); Stepanov auxiliaries over `ℤ` (B3.19).** No candidate object, classical with a sharp reduction, or blocked by the missing period.

## 4. Would the B-tier obstacles require a new field of mathematics?

### 4.1 Assessment

No theorem shows that a new field is necessary. What has changed is that the corpus has built the first chapters of the field the previous assessment proposed — an electrostatics of the zero divisor (AES), an intersection theory of the characteristic circle (AIT), and a renormalization theory of its self-energies (RBG) — and these chapters locate, ingredient by ingredient, what of Weil's proof over `𝔽_q` exists over `ℤ`:

| Ingredient over `𝔽_q` | Over `ℤ` | Status |
|---|---|---|
| Positive Hermitian structure on `H¹`; Frobenius a similitude | Abel torsion energies PSD, power maps similitudes up to `r ↦ r^t`; `D` positive with defect `≍ M_f` | exists, regularized [L] |
| Local Hodge index at a place | each prime's tower form `log p (K_q − I)` two-sided bounded | exists [L] |
| Finite self-intersection of the diagonal, `2 − 2g` | torsion counterterm the identity; survival cone `{0}`; `κ_min ≍ log N`; cocycle `β` nontrivial | missing [L/S] |
| Global index = local + archimedean | local forms do not sum; the archimedean self-energy must pay | missing [S] |
| Tensor-power amplification with non-scaling loss `g` | dyadic amplification with loss `D(f)` | exists, converts rates only [S] |
| Frobenius spectrum on a lattice (Stepanov) | none at the arithmetic point; no period | missing [L] |
| Frobenius fixes the base point | cells fix the gauge; square-class couplings blind | exists structurally, not as positivity [S] |
| Equilibrium and its stability | equilibrium computed and quantized; field threshold `√log γ` | stability missing [L] |

A new field is likely required [R], and its shape is now sharper than before: an Arakelov-type theory of the characteristic circle in which the archimedean place enters the renormalization of the diagonal. Arakelov's admissible metrics make the self-intersection of the diagonal finite and the adjunction formula hold on arithmetic surfaces; the corpus shows that the prime place alone has an identity counterterm, that the archimedean place has a rank-one counterterm, and that the arithmetic point is the node joining them. The missing object is the admissible coupling.

### 4.2 The field: renormalized arithmetic potential theory of the characteristic circle

**Thesis [R].** RH is the stability of an equilibrium that arithmetic already computes. The zero divisor is in transverse equilibrium exactly when it is critical; its Laplacian (`D`), gradient (the field, read off `Λ ⋆ Λ`), moment of inertia (`M_f`, the Hecke defect) and energy (`𝓔`, quantized) are computed; its reflection pairing is `W`. On the characteristic circle the same potential theory has positive, Hecke-similar energies before renormalization and the prime kernel after it. The field would be the theory of the **coupled renormalization** that keeps positivity through the limit: torsion orbits (prime place), the lattice germ at rational nodes (archimedean place, Fourier dual through Gauss's digamma theorem) and the arithmetic point (the pole), with one counterterm of low rank and an anomaly that cancels.

**Central conjecture [R]: Hodge index with archimedean adjunction.** There is an admissible renormalization of the torsion pairing, coupling it to the archimedean germ and the arithmetic-point node, such that (i) the counterterm has bounded rank on every Hecke orbit; (ii) the coupled finite part is Hecke covariant, the archimedean side absorbing the regulator anomaly and the tame different that make up `β(n, t)`; (iii) the renormalized pairing is positive on its survival cone, and the survival cone contains the degree-zero cycles. RH would be its specialization at the arithmetic point.

**What it would be like.**
- **Like Arakelov theory:** a Green function on the circle (`−log|1 − z w̄|`), regularized self-intersections (log-discriminants, the different), an adjunction formula (`c(n)` grows by `log p` along the tower of `p`), a local Hodge index at each place (tower forms), and a global Hodge index that needs the archimedean place.
- **Like renormalization in quantum field theory:** regularized families, counterterms whose null cone is scheme independent (the survival cone), rank of the counterterm as the invariant that decides what positivity survives, anomalies (the cocycle `β`, the regulator anomaly `t log t`) and the question of anomaly cancellation between sectors.
- **Like Stieltjes electrostatics and logarithmic potential theory:** zeros as charges, the explicit formula as the equilibrium equation, virial laws, Fekete configurations (the torsion is the stable equilibrium of the circle); equilibrium computed, stability the sign.
- **Like Hodge theory:** a Hermitian structure (`D`) and an intersection pairing (`W`) related by a polarization whose similitudes are the Hecke operators.
- **Like Diophantine approximation:** alignment of `γ log p` at zero ordinates; Baker-type repulsion bounds alignment with the Liouville vacuum.
- **Like gauge theory:** gauge-invariant (square-class) couplings and charged (successor, cell) couplings; the arithmetic point fixed by additive structure with holonomy.

**Parts already in the corpus.**
- **Conjugate-diagonal geometry and electrostatics** (CDG, PL, AES): `D` from the `ξ` current; the moment-of-inertia law; the field and its threshold; energy and quantization; virial laws; terminals, rays and lenses.
- **Intersection theory of the circle** (AE, AIT): `Λ` as log-order; self-intersection and different; tower forms and local Hodge index; projection formula; Hecke cocycle; Gauss digamma duality.
- **Renormalization** (RBG, AES): survival law; rank dichotomy; polar hyperplane; pole node; periodic germs; logarithmic counterterm and the arithmetic point; dyadic amplification.
- **Deformation theory of positive systems** (BGG, RBG): Landau–Wronskian principle, Abel–Gram law, conservation, quantization, irreversibility.
- **Gauge geometry** (ACG, BGG, RBG, SP): gauge torus, successor holonomy, square-class blindness, cells, repulsion, first separations.

### 4.3 Criteria the field must meet

| Criterion | Test against the corpus |
|---|---|
| **Computability** | Positive form, field, energy and pairing produced by identities (explicit formula, `ξ` current, resultants and log-orders, `Λ ⋆ Λ`), not posited. Counting reformulations of the sign do not count. |
| **Low-rank renormalization** | A coupled counterterm of rank below the number of modes, with a survival cone that contains degree-zero cycles; scalar counterterms (survival cone `{0}`) do not count. |
| **Anomaly cancellation** | The Hecke cocycle of the prime place (regulator anomaly minus tame different) absorbed by the coupling, so that the renormalized pairing is Hecke covariant. |
| **Local to global** | The archimedean place pays the divergence of the sum of local prime forms; local Hodge index at each prime is reproduced. |
| **From detection to bound** | A zero-side reserve (field, outward ray, local detector, moment of inertia) turned into an upper bound beyond classical density; the field below `√log γ` at right zeros. |
| **Selectivity** | Distinguishes `ζ` from the W1 battery; fails on square-class kernels, torsion energies at `r < 1`, the lattice germ off its hyperplane. |
| **Gauge charge** | Uses non-square couplings or cells; reproduces the first separations. |
| **Local type** | Localizes by a non-multiplicative operation, or carries a polarization; controls alignment of zero ordinates with small primes. |
| **Calibration** | Weil for curves (`2 − 2g`, Hermitian `H¹`, Rosati transpose, lattice Frobenius spectrum); hyperelliptic RH by counting; budget slopes; `κ = 1` collapse; `κ ≥ 3`; conductor horizon; `W = D − Δ`; log-Sobolev norm; `E_f ≍ M_f`; transverse equilibrium and quantization; the field threshold; Gauss's digamma theorem; Fekete stability of the torsion; Gårding as a finite-rank counterterm; the census. |
| **Non-circularity and uniformity** | No premise contains the conclusion; aperture, height, rank, damping and window controlled together; exceptional sets below the zero spacing. |
| **New partial results** | Outputs that are not zero-free strips: a non-isolation law (Q1), Hecke covariance or a bounded residual counterterm of a coupled germ (Q2), a gauge margin law (Q3), central nonvanishing for coupled classes (B3.22). |

### 4.4 Questions it must answer

1. **What is the admissible metric of the characteristic circle?** Which coupling of the torsion germ to the archimedean germ and the arithmetic-point node makes the diagonal self-intersection finite (Q2, B3.25)?
2. **Does the anomaly cancel?** Can a coupling to the archimedean germ absorb the cocycle `β(n, t)` — the regulator anomaly of `[t]` and the tame different — so that the finite part is Hecke covariant (B3.26)?
3. **What bounds the field?** Which arithmetic inequality caps the transverse field at right zeros below `√(2c log γ)`, or `ζ′/ζ` on outward rays below the reserve (B1.13, B3.24, B3.27)?
4. **What bounds the moment of inertia?** (B3.21)
5. **What is the Frobenius at infinity?** On torsion cycles complex conjugation is the power map of degree `−1`, so the collided and reflection pairings coincide there; which correspondence acts as conjugation on the zeros?
6. **What is the arithmetic point?** How does the theory distinguish `z = 1`, the node carrying both the torsion divergence and the archimedean one, and what is its period?
7. **How does `σ_γ` localize beyond the conductor, and are zero ordinates aligned with small primes?** (Q1)
8. **What is the non-archimedean gauge charge of a positive form?** (Q3)
9. **How does a quantized statistic reach every window?** Which computation bounds a window energy below two?
10. **Is the coupled class bounded at the centre?** (B3.22)
11. **What selects the fibre?** (B3.23)
12. **What are the escape states of `ζ` at infinite height?** (B3.2)

### 4.5 Tools

**Built:** the capacity identity and Hecke law of `D`; log-Sobolev equivalence and local Weyl law; the `ξ` current, theta metrics and the local zero detector; depth distributions, two-scale rigidity, the Hecke moment problem, dyadic amplification and the moment-of-inertia law; quadratic terminals, outward rays, critical discs and the terminal lens; the source field at every zero; virial laws, equilibrium, divisor energy, window quantization, the field threshold, the external field law; Selberg's renormalized source; torsion log-orders, self-intersection, different, tower forms, local Hodge index, projection formula, Hecke cocycle, Gauss digamma duality; the survival law, rank dichotomy, polar hyperplane, pole node, periodic germs, the logarithmic counterterm; effectivity calculus, Tate's law, heights, polar box, horizon torsion, Farey potential; budget calculus over `ℤ` and `𝔽_q`; hyperelliptic RH by counting; completion, Burgess, least non-residue; gauge torus, successor holonomy, square-class classification, cells, repulsion; contraction and collision calculus; deformation principle, quantization, irreversibility; Abel atoms; the census; the smoothed Landau formula.

**Not yet built:**
- **Coupled renormalization:** a regularized family joining the two places and the pole with a low-rank counterterm (B3.25), and anomaly cancellation (B3.26).
- **Field and defect inequalities:** upper bounds for the field, for `ζ′/ζ` on outward rays, and for `M_f`, that are not classical density estimates.
- **Diophantine control at zero ordinates:** moments and exceptional sets of short prime sums over zero ordinates; the interior anti-alignment law.
- **Gauge margin laws:** positivity margins on growing prime windows, from charged data.
- **Hermitian structures on correspondence spaces** with the archimedean flow acting by computed similitudes; **selective counting polarizations**; **ceilings for non-positive members of coupled classes**; **selection lemmas at the zero-spacing scale.**

### 4.6 Objects, language and mechanisms

| Layer | Content |
|---|---|
| **Objects** | • The characteristic circle `ℝ/ℤ`: torsion orbits `O_n`, torsion measures `ν_N`, the arithmetic point `z = 1`, power maps `[t]` (Hecke), the Green function `−log\|1 − z w̄\|`, log-orders `log #(𝒪/(Φ_m(ζ_n)))`, self-intersections and differents, tower forms `K_q`.<br>• Regularized families: torsion germs, lattice germs `G_r`, pole nodes, periodic germs; counterterms, survival cones, anomalies.<br>• The conjugate diagonal: `log\|ξ\|`, its Riesz measure, the field, the transverse energy, moments of inertia, depth distributions, terminals, rays, lenses, theta prefixes.<br>• The Rankin–Selberg square `Λ ⋆ Λ`, Selberg's source `Λ₂`.<br>• The two forms `W`, `D`, the defect `Δ`, the Hecke defect.<br>• The biarithmetic semigroup `⟨+1, ×p⟩`: gauge torus, square-class and charged couplings, cells, successor holonomy.<br>• Counting objects; positive systems and deformations; escape objects; zero ordinates as points of the prime torus. |
| **Language** | It must distinguish: positive and equivariant; computed, bounded and posited; detected and excluded; collided and Rosati pairing; energy, field, moment of inertia and self-energy; regularized and renormalized; scalar, rank-one and admissible counterterms; local and global index; anomaly and cocycle; equilibrium and stability; hyperbolic, elliptic and unipotent; even and odd sector; below and beyond the conductor; exterior and interior; aligned and generic heights; square-class and charged; orbit and point; count and sign; soft and selective polarization; ceiling and rigidity; classification and exclusion; statistic and individual zero; quantized and averaged. |
| **Mechanisms to discover** | • An **admissibility law**: a coupled counterterm of bounded rank on Hecke orbits.<br>• An **anomaly-cancellation law**: the prime-place cocycle absorbed by the archimedean coupling.<br>• A **stability law**: equilibrium of the zero divisor is stable for the renormalized pairing (Hodge index with archimedean adjunction).<br>• A **field law**: an arithmetic upper bound for the field at right zeros of size `o(√log γ)` off a sparse set.<br>• An **alignment law** at zero ordinates; a **gauge margin law**; a **conjugation law**; a **ceiling law** for coupled classes. |
| **First milestones** | (1) W11, W12: the exact counterterm constant, coupled survival cones and the Hecke variation of coupled finite parts — Q2.<br>(2) W9, W10: moments and exceptional sets; the interior reading of the reserve — Q1.<br>(3) W5, W6: the `23/40` floor and margin tables — Q3.<br>(4) W13: the electrostatic dictionary on the actual divisor.<br>(5) W8: the collided form, `M_f` and the local detector from finitely many theta values.<br>(6) W18(vii), (xi): central nonvanishing in ACS coordinates; Gårding as a survival-law instance. |

Each milestone is a theorem of a kind the corpus does not yet contain: a renormalized positivity with a nontrivial survival cone, a forcing law of elliptic type, a gauge margin at every scale, or an inequality attached to a computed electrostatic quantity — not a receiver, a blindness theorem, a deformation equivalence, a detection or a counting reformulation of the sign. Programme standards add their own requirements:
- **AES / AIT / RBG:** name the counterterm and its rank, the survival cone, the anomaly, and what bounds the field.
- **APD:** name the positive side, the spectral side, the gap and the integer.
- **ACG / BGG / SP:** name the gauge charge (square class or not), its holonomy and its margin.
- **ACP / PL / CDG:** name the layer of Weil's argument, the local type, whether the carrier localizes, and whether the positivity is collided, Rosati, local, counterterm-carried or zero-side.
- **AE:** name the currency, show the count is not one of the forms of the sign, and name the period it uses.
