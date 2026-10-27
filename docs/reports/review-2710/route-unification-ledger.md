# Route-unification ledger

**Status 2026-10-27, corpus `80f251476` with the working tree of that day.** The 31 live routes, 17 candidates and PW-B are faces of three construction problems:

- **U1 — critical arithmetic cancellation**: the *rate* reading.
- **U2 — complete signed positivity**: the *sign* reading.
- **U3 — faithful realization and forcing**: the *carrier* reading, with an *invariant and deformation* sub-reading, a *counting* sub-reading and a *renormalization* sub-reading.

All three ask one question in different currencies: **what forces the actual arithmetic source to be blind to off-line zeros?** The corpus states that question through three objects on the test space of `ζ`:

- **U2 is the positivity of the equivariant form.** Weil's form `W` is Hecke equivariant for every configuration and has finitely many negative directions at every aperture; its positivity is RH.
- **U3 asks for a form that is positive and equivariant at once.** The collided form `D = Σ m_ρ|f̂(ρ)|²` is positive, faithful, coercive and computed from `ξ`; it is Hecke equivariant iff RH; `Re W = D − Δ`, and the Hecke defect of `D` equals that of `Δ` [R]. Torsion energies on the characteristic circle are positive at `r < 1` and Hecke equivariant at `r = 1`; positivity is lost in the diagonal renormalization. Every counting reformulation of positivity is RH; every unconditional positivity found is invariant, averaged, non-localizing, dominated, collided, twisted below the conductor, a finite-window certificate or positive before renormalization.
- **U1 excludes by comparing a collided object with a Rosati one, or a budget with a spectral count.** Escape states are phase kernels with collided Cauchy forms; their Abel atoms are the dominant zeros; RH is positive gauge mass. A linear budget of the prime error or the Mertens function forces RH; over `𝔽_q` its slope is the spectrum counted with squared multiplicity, or its repulsion energy.

The readings are equivalent at their endpoints:

- **U1.** A generic orbit's growth rate equals the depth of the deepest zero it sees; one test's Lefschetz sequence grows like `p^{Δm}`; escape at `ε` is the presence of zeros right of `1/2 + ε`; the receiver energy grows exactly at the exponent `max(0, 2Θ − 2ε − 1)`; `(1/L) log D(T_L f) → 2a_f`.
- **U2.** Orbit Hodge positivity holds iff the orbit is blind; on spans `{g, T_{p^m} g}` of short tests it is Weil's Castelnuovo–Severi inequality, whose local part holds; zero negative index at every aperture.
- **U3.** The maximal sharp-stable positive Meyer ideal is the off-line-blind ideal; the κ = 1 completed class is `ℝ^× · ζ`; a section count with RR and Bézout is the Hodge index; positive rigidity, positive chirality and the rational and positive central ceilings at an ordinate are the absence of zeros there.

**Six readings cut across the families.**

- **The local type.** At an off-line reflection pair multiplicative correspondences act by boosts, the successor unipotently, the functional equation and `σ_γ` by the swap. U1 reads the boost as growth; U2 reads boost-invariant positivity as isotropy; U3 needs a non-multiplicative localizer — `σ_γ`, whose odd-sector certificate is separated from the conductor horizon at every height.
- **The gauge point.** Multiplicative data determine a source up to its gauge orbit; finite lattice forms are blind; the successor connection reconstructs the prime phases; unconditional positivity of `ζ` separates it from the first two twins [S]; archimedean twists approach the Liouville vacuum at most stretched-exponentially fast.
- **The pairing.** Collided objects pair `ρ` with `ρ̄` (determinants, coupled counts, escape forms, `D`); Rosati objects pair `ρ` with `1 − ρ̄` (`W`). Collided positivity is free and computed; Rosati positivity is RH.
- **The renormalization.** Torsion energies join positivity and equivariance in one family and separate them only at the diagonal; Weil's archimedean kernel has its own diagonal divergence [R]. All three families meet at the question of a positivity-preserving counterterm.
- **The central order.** Deformations of positive systems keep the off-line divisor; the central vanishing order is the one invariant they move, and moving it costs a square-root prime deficit for arithmetic members.
- **The spectral count.** Budgets of signed rows have slopes that count the spectrum: `Σ mult²` (prime error), repulsion energy (Mertens), the archimedean genus as the regularized count over `ℤ`.

The invariant and deformation sub-reading of U3 is closed: pole order pays inserted zeros; contraction and collision are classified; the positive polar-configuration cone is classified; positive and rational deformations detect zero-free ordinates and force nothing. The counting sub-reading is closed as a reduction: every count is the sign, and large-sieve counts inflate. The renormalization sub-reading is open (Q2 of the summary). Identical receivers do not mean identical producers: each family keeps its own missing construction.

Companions: [complete report](route-obstacles.md), [summary](obstacles-summary.md), [walls ledger](walls-ledger.md). Evidence: corpus search and Lean statement reading (`logs/review-2710-research-log.md`). `[S]`, `[R]` as in the walls ledger.

## 1. Levels of unification

| Level | What it justifies | What it does not |
|---|---|---|
| **Exact identity** | Two expressions are equal on a stated source and normalization (`Re W = D − Δ`; `W_λ = W_ζ` twisted at `π/log 2` plus corrections; prime kernel = −renormalized torsion energy + log-discriminant). | Extension to another completion or norm. |
| **Computation** | A quantity is produced by an identity from source data (`D` from the `ξ` current; `Λ` from cyclotomic resultants). | Any inequality for it. |
| **Receiver isomorphism** | Same threshold at every rate `σ` (width functor). | Equal finite tests, rates or difficulty. |
| **Currency equivalence** | Two statements are proved equivalent to each other (six effectivity currencies). | That either is easier. |
| **Per-ordinate equivalence** | A statement at ordinate `γ` is the absence of zeros at `γ` (positive rigidity, chirality, rational and positive ceilings). | Anything at another ordinate; any mechanism. |
| **First-rung coincidence** | The weakest nontrivial conclusions coincide (quasi-RH). | Equality of later rungs or of producers. |
| **Gauge equivalence** | Sources with the same multiplicative data differ by a gauge twist. | Any statement at a chosen point of the orbit. |
| **Local-type equivalence** | Mechanisms invariant under the same hyperbolic symmetry force the same isotropy. | That either sees the sign. |
| **Pairing equivalence** | Two positivities are collided forms of the same conjugate pairing. | That either is Rosati positivity. |
| **Calibration equivalence** | A `ℤ` statement and its `𝔽_q` analogue have the same shape (budget slopes, effectivity, naive heights). | That the `𝔽_q` proof transfers. |
| **Layer equivalence** | Two mechanisms realize the same layer of Weil's argument. | That a lower layer forces a higher one. |
| **Maximality / isotropy** | Every member of a class lies in one extremal object, or has isotropic fibres. | That the actual source reaches it. |
| **Rigidity / ceiling** | A set of invariants has exactly one solution, or bounds an invariant. | That the solution's zeros are located; a ceiling is not rigidity. |
| **Classical reduction** | A mechanism's strongest output is a classical estimate (coupled budget = Hadamard count; boundary forcing = dlVP; conductor horizon = `\|Λ\|` bound = local Weyl law). | That a refinement stays classical. |
| **Conservation** | An exact balance on a deformation class (index–pole, critical conservation). | An absolute bound for the base point. |
| **Directional transfer** | A proved bound implies another under hypotheses. | The converse. |
| **Shared construction problem** | The same missing estimate, sign, counterterm or object. | That one producer yields the others. |
| **Analogy** | A model suggests a mechanism. | Validity for `ζ`. |

## 2. The three families

### U1 — Critical arithmetic cancellation (rate reading)

**Primary data:** prime or Möbius coefficients. Observables: lag, spline, deficit, Abel moment, history, regularized series, pronic energy, Vaughan Gram, cofactor module and symbol, divisor sums, Lefschetz sequences, one-sided counts, horizon torsion, Farey potential, budgets.

**Missing input:** a signed estimate at every positive slack, at the gauge point `0`.

**Proved unifications:**

- The width functor makes the spectral, abscissa, damped Möbius and Liouville, ξ half-plane and Suzuki receivers isomorphic.
- First-rung coincidence: every graded gain beyond VK is a fixed strip (including escaped Möbius pairings at fixed `θ` and large-sieve section supply [S]).
- **Escape.** Located (alternative), exact energy-rate law, classified: phase kernels, collided Cauchy forms; Abel atoms of `ζ` are the dominant zeros with residues `ζ(ρ − ε)/(ζ′(ρ)(ρ − ε))`; capacity, endpoint and shadow laws; infinite-height escape for non-summable residues, unattained abscissa or unbounded orders. RH ⇔ positive gauge mass.
- **Counting forms.** RH ⇔ the one-sided count; ⇔ horizon torsion; ⇔ the Farey potential at `√N`; `M(N)` is the first Fourier coefficient of the torsion measure.
- **Budgets.** Prime-error budget ⇒ RH with slope `≥` genus; Abel slope at the genus ⇒ RH + simple; Mertens budget ⇒ RH + simple + summable residues; `𝔽_q` slopes count the spectrum.
- **Gauge form.** The Möbius half-power law at `0` is RH, holds a.e., fails at the Liouville twin.
- **Loss law.** Moments, family averages, products and relative powers lose linearly; twists are rate neutral.

**Subfamilies:** width readings (WL, SRT, PBM, MC, JAS, FU, RP, DR); critical energy (PM, CTF with BVI, ACCE, ADR, SAEI, SSA, THIM); budgets (WL, MC); oscillatory payment (the capacity `Δ`).

**Separate currencies:** LI (reciprocal depth), RB (extremal inequality), BAG (local recurrence).

### U2 — Complete signed positivity (sign reading)

**Primary object:** the complete prime–Gamma–polar Weil form, Hecke equivariant; equivalently the spectral side of the explicit formula; equivalently the Rosati trace of the correspondence ring.

- Direct attacks on its sign: RW, SZ, CHMD, OWU, EWU, ACT, AIP, HF, TT.
- Identification with Hodge index, Castelnuovo–Severi on Lefschetz spans and Rosati positivity: ACS, HF, SRT.
- Sign under other quantifiers: LA, TH, HCF, GTA, XN, PA.

**Proved unifications:**

- RW ⇔ SZ ⇔ CHMD at fixed aperture; HF ceiling ⇒ AIP allocation ⇔ ACS strict-cone RR; one-shift variation, odd capacity and blind minima are parity components.
- Gårding inequality and finite negative index at every aperture.
- Short-window averaged positivity at `Γ^{99/100}`; the off-line field; zero-ordinate positivity for nonnegative tests.
- Lefschetz form and local–global split: one prime, short cycles, one shift.
- Correspondence form: RH ⇔ every normalized Hecke graph effective ⇔ budget sufficient ⇔ Rosati positivity.
- **Two forms:** `Re W = D − Δ`; RH ⇔ `W = D` ⇔ `D` Hecke invariant ⇔ one Hecke translation a similitude of `D`.
- **Elliptic sectors:** below the conductor horizon twisted positivity holds for every test; the odd sector forces companions; the certificate and the horizon are disjoint at every height.
- **First gauge windows:** the Liouville twin is `ζ` twisted at `π/log 2` on windows below `log 3`; unconditional positivity of `ζ` separates it from the twins at `181/500` and `23/40` [S].
- Worst twin on nonnegative tests; ground rate = polar rate.

**Common localization:** at each aperture a finite low-frequency sector (Gårding); in the incidence picture prime-sum edges; across heights selection below the zero spacing; on Lefschetz spans the Lefschetz part; in correspondence form the sufficiency of the budget; in the two-form picture the defect `Δ`.

### U3 — Faithful realization and forcing (carrier, invariant/deformation, counting and renormalization readings)

**Carriers:** geometric (ACS, Meyer surface, AOG, correspondence surface, theta surface, polar surfaces of AE, Serre-dual polar boxes); potential-theoretic (CDG: the `ξ` current; AE: the characteristic circle and torsion cycles); operator-theoretic (RN, GTA, PCS, IRK); probabilistic (W1C, FEL); photonic (PTR); categorical (CDC, SC, WBF, RFHM); divisor-diagnostic (HJ, SEC, BSH, APF, EWJ, EGC, PW-B); topological (TG); heat and divisor (WD, ALDG); gauge-geometric (BGG).

**Proved unifications:**

- **Maximality and isotropy, explained by local type.** Sharp-stable positive ideals lie in the blind ideal; positive ideals without sharp stability are half-blind; coupled point-stable carriers are isotropic. All three are the boost law.
- **Resonance and elliptic localizers.** Correspondence-closed carriers are elliptic only at resonant scales; `σ_γ` is the unique reflection-compatible affine localizer.
- **Non-localizing positivity** holds for every prime weight.
- **Detectors** (HJ, SEC, CDC, BSH, IRK, W1C) read whether a Hecke symbol is elliptic; zero-indexed depth functionals of this kind are computable from `ξ`.
- **Faithful branch:** operator-norm faithful positivity is RH plus simple zeros.
- **Invariant rigidity and the positive cone:** κ = 1 class `ℝ^× · ζ`; one section decides positivity of a polar configuration; leading line and line hierarchy laws; commensurable positive lines are couplings.
- **Contraction and collision:** real pairs free; quartets against a real anchor; anchored quartet ⇒ `κ ≥ 3`; couplings have even real orders; Fejér barrier; no analytic global collision.
- **Deformations:** Landau–Wronskian principle; Abel–Gram law; positive and rational deformations of `ζ_γ` rigid exactly at zero-free ordinates; their ceilings and positive chirality ⇔ no off-line zero at the ordinate; critical transfer law; strong multiplicity one below the square-root deficit; central excess ⇒ square-root deficit with residue `≥` excess; `ζ^d` rigidity and boundary capacity; critical conservation [S].
- **Counting:** six currencies; node twist destroys RI; theta surface fibre-independent; lattice counts collapse; naive heights are traces; Jacobi–Hurwitz dichotomy and large-sieve inflation [S].
- **Renormalization:** `Λ` is an intersection number of torsion cycles with a Hecke law; the prime kernel is minus the renormalized limit of positive torsion energies.
- **Weil's layers:** identities, theorem of the square, budget and involution free; kernel and coupled counts collided; over `𝔽_q` counting proves purity.
- **Successor:** affine positivity induced from dilations; Weil's extensions a box over critical zeros; successor connection reconstructs prime phases; successor defect in `H²`.

**Common missing object:** a pre-divisor source with a **forcing law** placing it in the maximal blind ideal, with input that is computed (not a counting reformulation), gauge charged beyond the archimedean line, localized by a non-multiplicative operation or polarized, not scaling with amplification, anchored at no pole or conductor cost, and positive and equivariant at once — through an inequality for the computed defect of `D` or a positivity-preserving Hecke counterterm for torsion energies.

### The forcing currency: where the families meet

| Mechanism | Family of origin | What it forces | Where it stops |
|---|---|---|---|
| Multiplicative positivity (boundary) | U3 | `ζ(1 + it) ≠ 0`; capacity `⌊k/2⌋`; with growth input dlVP, Littlewood, VK | Interior gain only from growth; next rung a fixed strip (U1). |
| Coupled height positivity in completed systems | U3 | `⌊κ/2⌋` collars; κ = 1 class; `5d < 9κ` | Collar width `1/log T`. |
| Invariant carrier positivity | U2/U3 | Blindness, half-blindness, isotropy | Boost invariance. |
| Non-localizing positivity | U2/U3 | Coercivity at bounded aperture | Every prime weight. |
| Elliptic localization by `σ_γ` | U2/U3 | Twisted positivity below the horizon; companion forcing from one odd-sector sign | Source-blind below the horizon; certificate disjoint from it at every height. |
| Positivity on nonnegative tests | U2 | Upper bounds on the source | Shared by dominated twins. |
| Linear rigidity | U3 | The coefficient measure is `ζ`'s | Zeros are nonlinear in the measure. |
| Pole order; positive contraction | U3 | Index = pole increment + critical traffic; real pairs free; anchored quartets | Pays inserted zeros; `κ ≥ 3`. |
| Collision by coupling | U3/U1 | Zero-tax contraction at one ordinate | Even real orders; Fejér barrier; conductor `log γ`. |
| Positive and rational deformations | U3 | Divisor rigidity off the line; central order bounded by deficit | Rigid exactly at zero-free ordinates; detect, do not force. |
| Successor prescription | U2/U3 | Hecke weight; threshold `s ≥ 1/2`; Kronecker-null spectrum | Never reaches atoms. |
| Multiplicative data | U1/U3 | Statements true on the whole orbit | The gauge point. |
| Finite-window certificates | U2 | First twins separated [S] | No margin law at growing windows. |
| Correspondence identities | U3 | Normalized graphs; similitude; involution | Hold on the golden datum. |
| Collided positivity (computed) | U1/U3 | Automatic, faithful, coercive positivity | Sees no sign; its equivariance is RH. |
| Torsion energies | U3/U1 | Positivity at `r < 1`; Hecke law at `r = 1` | Diagonal renormalization. |
| Counting (sections, effectivity, heights, one-sided counts, base, torsion, Farey, budgets) | U3/U1 | Exact receivers | Each is RH or stronger. |

The invariants run in parallel on the boundary and in the interior:

| Boundary line `Re s = 1` | Interior (degree one) |
|---|---|
| Nonnegative weights (N) | Coefficient positivity (N) |
| Integer divisor (Z) | Riemann's FE |
| Simple pole (S) | Simple pole (S) |
| Pole isolation (I) | Strip holomorphy (H) |
| N + Z + S + I ⇒ no boundary zeros; each necessary | N + FE + S + finite order ⇒ `ζ`; dropping S or H admits off-line zeros |
| Pole of order `k` carries `≤ ⌊k/2⌋` boundary zeros; `ζ^d` deformations `2Σ ≤ κ − d` | `≤ ⌊κ/2⌋` collar zeros; κ = 1 class; anchored quartet ⇒ `κ ≥ 3` |
| Families: only the two-torsion exception | Positive deformations rigid at zero-free ordinates; central excess costs a square-root deficit |

## 3. Every route and candidate

Abbreviations in the last column: *Rate* = graded rate (first rung quasi-RH). *Aperture* = pointwise or averaged window. *Carrier* = carrier, height, heat or order exhaustion. *Escape* = exterior mass at infinite height. *Lefschetz* = the Lefschetz part at one prime. *Gauge* = gauge-charged positivity with a margin. *Elliptic* = odd-sector sign beyond the conductor (alignment at zero ordinates). *Two-form* = an inequality for the computed defect of `D`. *Renorm* = a positivity-preserving Hecke counterterm. *Count* = a count that is not a reformulation of the sign. *Budget* = a linear log-energy budget.

### Live routes

| Route | Family | Common receiver or invariant | Distinct missing producer | Partial-progress axis |
|---|---|---|---|---|
| **WL** | U1 | Width via spline, deficit, critical energy; one-sided count; horizon torsion; Farey potential; prime-error budget | Signed lag/energy at every slack; an actual budget | Rate; filtered averages; budget |
| **RW** | U2 | Ground energy `μ`, shell flux, prime ladder; finite negative index | Sign at every aperture; collar estimate | Aperture; Lefschetz |
| **FU** | U1 | Completed Abel moment | Complete history covariance | Rate |
| **RP** | U1 | Matched-quantile history floor | High-LCM and moving-core payment | Rate |
| **PA** | U1/U2 | Prime–archimedean current; Hausdorff moments | Low shifts across unbounded orders | Carrier (order) |
| **MC** | U1 | Mertens; `ν̂_N(1)`; bands ⇔ `Θ < 1`; gauge point `0`; Mertens budget; escaped pairings | Interior anti-alignment; an actual budget | Rate; gauge; budget |
| **TT** | U1/U2 | Directed Wold covariance; odd form | Covariance sign | Aperture |
| **LA** | U2 | Finite-head coefficients; heat | Zero heat on the residual region | Carrier (heat × height) |
| **TG** | U3/U2 | Winding, sub-unit trace | Residual sign, sub-unit bound | Carrier |
| **HF** | U2/U3 | Full cone; index `D_idx`; one-prime tower; normalized graphs; effectivity; naive and convex heights; `W = D − Δ`; computed `D` | Lefschetz part, `D_idx < 2`, a naive height, an inequality for the computed defect, or a torsion counterterm | Aperture; Lefschetz; two-form; renorm; count |
| **CHMD** | U2 | Odd bound states; nodal quotient | Nodal / reflected-prime sign | Aperture |
| **TH** | U2 | All-rank heat-Hankel sign | Signed vectors at one time | Carrier (rank) |
| **RN** | U3 | `det₂` resonances | Boundary orientation | Carrier |
| **WD** | U3/U2 | Ward cap; collisions; heated head | Cap vanishing; residual heat region | Carrier |
| **LI** | U1 | Reciprocal-depth clock | Subexponential floor | Rate (separate currency) |
| **SZ** | U2 | First variation = Weil energy | Same sign as RW | Aperture |
| **PM** | U1 | Admission at every damping; cofactor module; Abel atoms; gauge mass | Signed small-damping energy; positive gauge mass; exterior tightness | Rate (damping); escape |
| **JAS** | U1 | Level-one budget ⇔ strip | Half-power budget | Rate |
| **CTF** | U1/U3 | Báez–Duarte residual | Readout → 1 and energy → 0 together | Rate (damping) |
| **HCF** | U2 | Two literal heat grids | Both grids at all degrees | Carrier (degree) |
| **XN** | U2/U3 | Newton interior margin | Covering discs with margin | Carrier |
| **BAG** | U1/U3 | Strong recurrence ⇔ local nonvanishing | Returns near possible zeros | Carrier |
| **EWU** | U2 | Even blind minimum; finite-level weights; `181/500` floor [S] | Low and mixed modes | Aperture |
| **GTA** | U2/U3 | Quartic Schur decay | Rank-uniform decay | Carrier (rank) |
| **OWU** | U2 | Odd capacity; first windows separated [S] | Reflected-prime and polar payment; non-archimedean charge with a margin | Aperture; gauge; elliptic |
| **PBM** | U1 | Graded regularized abscissa | Convergence to `1/2` | Rate |
| **RB** | U1 | Robin on colossally abundant numbers | Extremal tail | Rate (separate currency) |
| **SRT** | U1/U2 | Lag family; detector = odd sector of `σ_γ`; one-prime Lefschetz sequence | Lag sign; selection; Lefschetz part; odd-sector sign beyond the conductor | Aperture; selection; elliptic |
| **ACT** | U2 | One-shift variation | All-profile reflected collar | Aperture |
| **AIP** | U2 | Shared incidence allocation; polar-neutral collapse; continuum towers [S] | One shared budget with prime-weighted remainder for the pole-neutralized form | Aperture |
| **ACS** | U2/U3 | Hodge index; RR; blind ideal; counting; contraction, collision and deformations; two forms | A form positive and equivariant at once; a selective count; the full-class ceiling | Carrier; aperture; Lefschetz; gauge; two-form; renorm; count |

### Candidates and PW-B

All are U3 unless noted. Each lacks the forcing law of §2; the constraints of the [complete report](route-obstacles.md#3-the-17-candidates-and-pw-b) apply to all.

| Candidate | Family | Common face | Missing construction |
|---|---|---|---|
| **APF** | U3 | Cycle-trace reconstruction | Annihilation of the off-line component |
| **BSH** | U3 | Mate curvature | Pre-divisor section |
| **CDC** | U3 | Calibrated confluence | Descending source potential |
| **DR** | U1/U3 | Dyadic roots; PBM abscissa | Global monodromy |
| **EGC** | U1/U3 | Enclosed-pole cancellation | Exterior contour sign |
| **EWJ** | U3 | Finite jets | Norm exhaustion |
| **FEL** | U1/U3 | BSY contrast, a depth capacity like `Δ` | Arithmetic upper bound forcing it to zero |
| **HJ** | U3/U2 | Residual = SEC charge = HCF grids | Stabilization weld |
| **IRK** | U3 | Completed relation | Arithmetic lift (an integral count is the sign) |
| **MSC** | U3/U2 | Squarefree source | Positive Sonin landing |
| **PCS** | U3 | Shift plus defect | Wall annihilation |
| **PTR** | U3 | Lossless product limit | Pre-divisor nonlocal port |
| **RFHM** | U3 | Full-support admission | Phase-sensitive law |
| **SC** | U3 | Wall-singular fibres | Cross-fibre index |
| **SEC** | U3 | Seam compactness | Pre-divisor compactness |
| **W1C** | U3 | Centred Lee–Yang limit | Arithmetic couplings |
| **WBF** | U3 | Genealogy completion | Arithmetic stream |
| **PW-B** | U3/U1 | Positive-damping action | Pre-divisor form; zero-damping landing |

## 4. Exact common currencies

### 4.1 Width (U1 and multiplicative forcing)

For `σ ≥ 0`, `Δ ≤ σ` is equivalent to each of: graded lag, spline, deficit, band and regularized-series bounds; admission of every damping above `σ`; the ξ half-plane bound; the Suzuki exponent `1 + 2σ`; the JAS budget; balanced, centred-prime and short-window savings; Vaughan empty-leg and tail-rate statements; one test's Lefschetz growth `O(p^{σm})`; all-test one-sided Lefschetz bounds at one prime; linear tensor loss `L_k = kσ`; growing-endpoint escaped Möbius pairings at `θ = 1/2 − σ` [S]; section supply beyond the large-sieve diagonal [S]. The receiver energy grows exactly at exponent `max(0, 2Θ − 2ε − 1)`; escape occurs at every `ε < Δ` outside a countable set. VK is the strongest unconditional point.

### 4.2 The common Weil form (U2)

| Statement | Relation | Qualification |
|---|---|---|
| Exact form | `Q = (γ₀ − 2)‖F‖² + Lévy + 4·horizon + 2∫incoming·G²` | Every compact `C²` test. |
| Two forms | `Re W = D − Δ`; RH ⇔ `W = D` | Every compact `C²` test for `ζ`. |
| Equivariance | `W(T_L f, T_L g) = W(f, g)`; RH ⇔ `D` equivariant ⇔ `T_L` a similitude of `D` | `E_D = E_Δ` [R]. |
| Gårding; index | `Re W ≥ 2π‖f‖² − K·lowMass`; finitely many negative directions | Every aperture; index zero is RH. |
| Ground | `μ(A) ≥ 0 ⇔ W_{A′} ≥ 0` for `A′ < A` | RH ⇔ `μ > 0` at every `A`. |
| Prime ladder | RH ⇔ cumulative frozen relaxation `≤ μ(3/10)` | Birth jumps vanish. |
| Finite level | RH ⇔ every aperture admits a positive weight system | No sign premise. |
| Lefschetz | RH ⇔ `\|c_m^{(p)}\| ≤ c_0^{(p)}`; one-sided at one prime; short cycles; one shift | Local part positive for `η ≤ 3/10`. |
| Normalized graphs | RH ⇔ every normalized Hecke graph effective | Square theorem and budget free. |
| Elliptic sectors | `W` on `e^{−iγu}r` = `W` of `Z − iγ`; even `+m\|tr\|²`, odd `−m\|tr\|²` | Twisted positivity below the horizon. |
| Forcing half and gap | One odd-sector sign + local count + depth dominance ⇒ companion | Needs `e^{2δa} > 768A log(\|γ\| + 3)`, disjoint from the horizon. |
| First prime windows | `W_λ = W_ζ(e^{−iγ₂u}·) + Δ_arch + Δ_pole`; twins negative on witnesses at `181/500`, `23/40` [S] | Full floor `1/5000` through `181/500` [S]. |
| Averaged | Positive at `A ≤ κ₀ log Γ` on `Γ^{99/100} ≤ H ≤ Γ/8` | Frequency average only. |
| Pointwise floor | `Q_γ ≥ −4(A + 1)²e^A N²Φ(γ)`; nonnegative tests positive at almost every zero ordinate | Signed tests: floor only. |
| Transfers | RW ⇔ SZ ⇔ CHMD; HF ceiling ⇒ AIP allocation ⇔ ACS strict-cone RR; one ACT shift decides RH; RW margin ⇒ TH/HCF heat window | Fixed aperture; directional. |

### 4.3 Geometric and counting currency (U2 ↔ U3)

- **Scaling and correspondence surfaces.** Pairing = pole plane − Weil form; Hodge index, RR plus ample effectivity, and zero sector defect are each RH. Normalized graphs with quadratic graph map and similitude budget.
- **Counting.** On every polar surface: section count ⇔ Hodge; effectivity function ⇔ Hodge; abundance ⇔ positive self-intersection in degree zero; Tate: a degree-two form is nonnegative iff it has a naive height, or a convex height. For `ζ`: each ⇔ RH; six currencies one statement; the polar box count ⇔ Hodge, its node twist violates RI; large-sieve majorants inflate [S].
- **Over `𝔽_q`.** Effectivity and naive heights hold on hyperelliptic curves; purity by Stepanov and `|τ|² = q`; kernel counts do not supply heights (complex fake).
- **Meyer surface; maximal blind ideal; Lefschetz spans; function-field calibration.**

The Weil sign, ACS RR + Bézout, the Meyer Hodge index, exhaustion of the maximal blind ideal, Castelnuovo–Severi on Lefschetz spans, effectivity of normalized graphs, sufficiency of the budget, Rosati positivity, a section count, an effectivity function, naive and convex heights, a fixed tensor loss, horizon torsion, the Farey potential, the one-sided count, the equivariance of `D`, the vanishing of `Δ`, positive chirality at every ordinate and the rational and positive central ceilings at every ordinate are the same statement. A form positive and equivariant at once, an elliptic forcing law beyond the conductor, a gauge margin law, a selective count, a positivity-preserving torsion counterterm and an oscillatory capacity bound would each be a proof of it, or a piece of one.

### 4.4 Ground rate and clustering

`Δ ≤ polarRate = groundRate ≤ 1/2`, `RH ⇔ groundRate = 0`; form-norm rates equal `Δ`; depth-profile rates equal twice the deepest seen depth. RW, SRT, ACS, EWU and AIP share this currency.

### 4.5 Depth on the divisor (U3)

The seam charge, the mate gain and the other zero-indexed diagnostics have exact depth laws; the BSY functional and the defect `Δ` vanish exactly on critical zeros; the Hecke defect of `D` is `Σ m(2cosh(2δL) − 2)|f̂(ρ)|²`, computed from `ξ`; two scales determine the depth dispersion; the symmetric-square spectrum is nonnegative iff the symbol is elliptic. **Diagnostics and capacities read depth, and the corpus computes them; none forces depth to vanish.**

### 4.6 Invariants, capacity, contraction, collision and deformation (U3 selectivity)

- **Rigidity.** N + FE + S + finite order ⇒ `ζ`; `CompletedPositiveSystem 1 d = ℝ^× · ζ`; `ζ^d` deformations rigid without pole budget.
- **Relaxations.** Pole order 2 or 3, strip poles, no FE, no positivity, boundary invariants alone.
- **Capacity.** Boundary `2Σm ≤ k`; collar `2Σ ord ≤ κ`; gauge `2Σm ≤ κ`; family `Σm ≤ k`; line capacity half the real jump (Abel–Gram); `ζ^d` boundary `2Σ ≤ κ − d`.
- **Positive cone.** One section decides; leading line; line hierarchy; commensurable lines are couplings.
- **Contraction.** Real pairs at `Δκ = 0`; quartets against a real anchor; anchored quartet ⇒ `κ ≥ 3`; planting `Δκ ≥ 2`.
- **Collision.** Height coupling; absorption of shifted poles; Fejér coupling; even real orders; Fejér barrier; no analytic global carrier.
- **Coupled class and deformations.** Not rigid at zero ordinates; positive prime-mass rigidity ⇔ zero-free ordinate; positive chirality and positive/rational ceilings ⇔ no off-line zero at the ordinate; critical transfer; central excess ⇒ square-root deficit with residue `≥` excess; critical conservation [S].

### 4.7 The gauge currency (U1 ↔ U2 ↔ U3)

| Statistic | Gauge behaviour | Consequence |
|---|---|---|
| Moduli, coincidences of products, multiplicative moments, family averages | Invariant | Determine the source up to its orbit. |
| Finite diagonal + ratio + product lattice forms | Unitarily equivalent under real sign gauges | Cannot separate `ζ` from `λ`. |
| Successor connection `conj χ(n) χ(n + 1)` | Charged; flat iff Euler vacuum on `[1, N + 1]` | Reconstructs `ω(2), ω(3)` on `2 → 3 → 4`. |
| Successor-square form `w(2)w(4)` | Negative at `λΛ`, positive on scale twists [S] | Archimedean-free separator. |
| Successor, affine and near-incidence correlations | Charged: mean zero, diagonal variance | A bound must be proved at `0`. |
| Möbius partial sums; torsion Fourier coefficient | Square-root law a.e.; exceptions comeager and null | RH is a property of the point `0`. |
| Chebyshev sums; torsion potential | Square-root law a.e.; at `0` a linear pole | RH is typicality of `0` modulo the pole. |
| Windowed moments on the archimedean line | Gauge moment below `2rX^k ≤ 1` | The threshold where the line starts to see the point. |
| Weil form on prime-free windows; on nonnegative tests | Weight blind; antitone | Positivity holds for every (dominated) twin. |
| Weil form on windows below `log 3` | Reads atom `2`; Liouville twin is `ζ` at height `π/log 2` | First gauge charge archimedean; twin negative on a witness [S]. |
| Weil form at `23/40` | Reads atoms `2, 3`; `{2,3}` twin is not a height twist | Twin negative on a witness on which `ζ` is positive [S]. |
| Atoms at `N` primes | Archimedean twists approach the Liouville vacuum at most stretched-exponentially | Second and later charges not archimedean. |
| Ramanujan torsion sums | Invariant under coprime dilation; contrasts kill the pole mode | `+`/`×` coupling at finite level. |
| Möbius boundary of affine maps | Separates `μ` from its twin (PNT) | Finite presentations are gauge charged. |

### 4.8 The local-type currency (U1 ↔ U2 ↔ U3)

| Correspondence | Local type at an off-line pair | On the line | What invariant positivity forces |
|---|---|---|---|
| Hecke `T_p`, archimedean flow, gauge twist | Boost | Rotation | Isotropy |
| Symmetric dilation by `a` | Boost unless `γ log a ∈ πℤ` | Rotation | Fibre zero at a non-resonant scale |
| Functional equation; `σ_γ` | Swap | Swap | Even sector: nothing; odd sector: vanishing |
| `σ_γ` with one Hecke operator | Dihedral | — | Blindness |
| Successor | Unipotent | Unipotent | Nothing |
| Affine maps of `ℤ` | Genus zero | — | Nothing beyond weighted counts |

U1 reads the boost as growth; U2 reads boost-invariant positivity as RH; U3 needs a non-multiplicative localizer or a polarization.

### 4.9 The pairing currency (U1 ↔ U2 ↔ U3)

| Object | Pairing | Positivity |
|---|---|---|
| Determinant (kernel) counts | `ρ ↔ ρ̄` | Automatic without real eigenvalues |
| Coupled counts | `ρ ↔ ρ̄` | Modulus squares for every datum |
| Escape forms | `z_k ↔ z̄_l` (Cauchy/Pick) | Automatic |
| Collided form `D` (computed from `ξ`) | `ρ ↔ ρ̄` | Automatic, faithful, coercive; equivariance ⇔ RH |
| Weil form `W`; Rosati trace | `ρ ↔ 1 − ρ̄` | ⇔ RH |
| Torsion energies `G∘T_r` | Torsion orbits `O_m ↔ O_n` | Automatic at `r < 1`; lost at the renormalized diagonal |
| Exterior counts over `𝔽_q` | `Λ²` collision | Force unitarity |

### 4.10 The budget currency (U1 ↔ U3)

| Row | `ℤ` | `𝔽_q` |
|---|---|---|
| Prime error | budget ⇒ RH; slope `≥ 2 + γ_E − log 4π`; log-slope `≥ Σ_{critical} m²/\|ρ\|²` unconditionally | slope `Σ mult(β)²`; `= 2g` iff simple |
| Mertens | budget ⇒ RH + simple + `Σ\|ρζ′(ρ)\|^{−2} ≤ S` | slope = repulsion energy; genus one strict Hasse |
| Abel slope | at the genus ⇒ RH + simple | — |

Budgets read multiplicity as `m²` (prime error) or as divergence (Mertens): the spectral count of Weil's budget `2g`, regularized over `ℤ` by the archimedean genus.

### 4.11 The torsion currency (U1 ↔ U3)

| Statement | Content |
|---|---|
| Product formula | `Λ(n) = Σ_{μ primitive} log\|1 − μ\|` |
| Intersection law | `I(m, mt) = φ(m)Λ(t)`; log-energy `gcd(a, b) log lcm(a, b)` |
| Torsion measure | potential at `0` = `−ψ(N)`; first Fourier coefficient `M(N)`; RH ⇔ either at `√N` precision |
| q-deformation | `log P_N(q) = Σ M(⌊N/d⌋) log[d]_q` |
| Renormalized energy | prime kernel + log-discriminant = −lim (positive torsion energies) after removing `log(1/(1 − r))` |

### 4.12 Currencies that stay separate

| Currency | Exact result | Not identified with |
|---|---|---|
| Li reciprocal depth | Off-line rates `≤ 1/431` | `Δ` |
| Heat constant `Λ₊` | `0 ≤ Λ₊ < 1/8` | `Δ` |
| HF ceiling exponent | `Δ ≤ θ* ≤ Δ/2 + 1/4` | `Δ` |
| Packet vs Weil energy | `m²` vs `m` | Each other without simplicity |
| Trace-bounded vs operator-norm faithful positivity | RH vs RH + simple | Each other |
| Pole order on deformations | Inserted minus removed critical traffic | `Δ` |
| Quantum budget | `b(η) = (√A + √(Gη))²/B` | A zero count at the line |
| Coalescent surplus | `3/4` at `β ≤ 1/18` | RH |
| Determinant degree; collided form | Conjugate pairing | Rosati degree |
| Conductor horizon | `e^a ≲ log γ/4` | The forcing threshold `(768A log γ)^{1/(2δ)}` |
| Central order of the coupled class | Rational/positive ceilings ⇔ zero-free ordinates | Full-class rigidity |
| Mertens budget | RH + simple + summable residues | RH |
| Torsion energy at `r < 1` | Positive | Weil positivity |

## 5. Interfaces

| Interface | Proved | Missing |
|---|---|---|
| WL ↔ PA | Exact trace identity | Source sign |
| WL ↔ AE ↔ ACP (counting, budgets) | One-sided count, horizon torsion, Farey potential ⇔ RH; prime-error budget ⇒ RH; Nair floor | A signed count beyond integrality; an actual budget |
| MC ↔ AE ↔ ACP (Mertens) | `ν̂_N(1) = M(N)`; Mertens budget ⇒ RH + simple; curve repulsion energy | An actual Mertens budget |
| MC ↔ PM ↔ BVI | Energy = interior bracket `+ O(1)`; bands ⇔ `Θ < 1`; long-modulus decomposition | Signed long-modulus quadrature |
| PM ↔ ADR ↔ ACP ↔ ACG ↔ PL | Escape alternative; energy-rate law; Abel atoms; capacity, endpoint, shadow, infinite-height laws; escape forms collided; gauge-mass criterion | Exterior tightness (B3.2); positive gauge mass (B1.2) |
| PM ↔ SSA ↔ THIM | Half-damping endpoint bounded; integer local exponents below half | Sub-half signed interior |
| PM ↔ CTF | Residual = readout² + energy | One row family doing both |
| RW ↔ SZ ↔ CHMD | Sign transfer; first variation; domains | Sign |
| RW ↔ SRT ↔ ACS | One rate currency | `polarRate = Δ` |
| HF → AIP ↔ ACS | Ceiling ⇒ allocation ⇔ strict RR | The inequality |
| HF ↔ SRT ↔ ACS (Lefschetz) | One prime; short cycles; one shift | The Lefschetz part (B1.3) |
| HF ↔ ACS ↔ AE (counting) | Six currencies; polar box; naive heights are traces; Jacobi–Hurwitz [S] | A selective count (B3.35) |
| HF ↔ ACS ↔ PL ↔ CDG (two forms) | `Re W = D − Δ`; RH ⇔ `D` equivariant; `D` computed, faithful, coercive; local Weyl law; depth laws | An inequality for the computed defect (B3.33) |
| HF ↔ ACS ↔ AE (torsion) | `Λ` as torsion intersection; prime kernel as renormalized positive energy | A positivity-preserving Hecke counterterm (B3.37) |
| SRT ↔ PL ↔ CDG ↔ APT (elliptic) | Detector = odd sector of `σ_γ`; conductor horizon; forcing half; gap at every height | Kronecker alignment at zero ordinates (B3.36) |
| OWU ↔ PL ↔ ACP ↔ BGG ↔ SP (gauge windows) | First charge a twist; twins separated at `181/500`, `23/40` [S]; multi-prime repulsion | A margin law on growing windows (B3.26) |
| ACS ↔ MPG ↔ SBWF ↔ U1 | Boundary forced; `⌊κ/2⌋` collar; κ = 1 class; growth gives dlVP/VK | Better growth input or a non-multiplicative mechanism |
| ACS ↔ ACP ↔ PL ↔ BGG (one variable, deformations) | Contraction and collision calculus; polar-configuration cone; deformation principle; per-ordinate equivalences; square-root deficit law | The full-class ceiling (B3.34) |
| ACS ↔ APD ↔ ACP (carriers) | Isotropy; half-blind and left-blind ideals; boost law; resonance law; visible affine extensions | A non-multiplicative localizer |
| ACG ↔ MC ↔ TTPC ↔ SSA ↔ BGG | Gauge invariance; a.e. laws; gauge-charged pair statistics; finite lattice blindness | A gauge-charged estimate at `0` (B3.24) |
| ACG ↔ AKT ↔ AOG ↔ ACP ↔ PL | Linear loss; total-length law; Künneth collapse; tensor-loss receiver; twists rate neutral | Fixed tensor loss (B1.9) |
| AIP ↔ BGG ↔ SP | Polar-neutral collapse; log-cell remainder; continuum towers [S] | Prime-weighted remainder payment (B3.8) |
| AE ↔ RHTower (`𝔽_q`) | Hyperelliptic RH by counting; completion law; Burgess at finite level [S] | A period at the arithmetic point (B3.30) |
| WL ↔ ACS (windows) | Filtered deficit → averaged positivity; off-line field | Selection below the zero spacing (B1.4) |
| LA ↔ WD ↔ ALDG | Large-height repair; collision–index bridge | Residual heat region |
| HJ ↔ HCF ↔ SEC | Residual = two-grid sign = seam vanishing | Pre-divisor forcing |
| BAG ↔ SRT/WL | Recurrence right of `1/2 + σ` ⇔ lag floor at `σ` | Returns near zeros |
| APT → RW/EWU/ACT/AIP | Positive restricted families; source selection | Transfer to an RH-complete cone |
| AOG → HF/ACS/SRT | Orbit Hodge ⇔ blindness; index exit; theta `h⁰` | Forcing; a selective surface count |
| PTR ↔ W1C | Real-rooted finite producers | Arithmetic producers |

## 6. Consequences

1. **Count each producer once.**
   - a small-damping signed budget, equivalently positive gauge mass or exterior tightness: PM, CTF, BVI, MC;
   - the positivity of the equivariant form (zero negative index): RW, SZ, CHMD, OWU, EWU, ACT, AIP, HF, TT, ACS, SRT;
   - a residual heat-region sign: LA, WD, TH, HCF;
   - a forcing law into the maximal blind ideal, with a form positive and equivariant at once: TG, RN, ACS, HF and all candidates;
   - a gauge-charged estimate or positivity at the point `0`, with a margin at every scale: MC, PM, BVI, TTPC, SSA, OWU, EWU, ACS;
   - an odd-sector sign beyond the conductor (alignment at zero ordinates): SRT, OWU, ACT, ACS;
   - an actual linear budget: WL, MC.
2. **Finished below RH strength:** reformulation; carrier maximality and isotropy; local-type classification including resonance and `σ_γ`; the forcing gap; invariant completeness; the positive polar-configuration cone; the relative budget; contraction and collision calculus; the deformation principle and the per-ordinate equivalences of the coupled class; successor coupling; escape location and classification including infinite height; the correspondence layers below the sign; every counting currency; the budget calibrations over `𝔽_q`; the computation and norm of `D`. New equivalent endpoints, new invariant carriers, new non-localizing carriers, new multiplicative certificates, new one-variable contractions or couplings, new positive or rational deformations, new collided positivities (computed or not), new counting reformulations, new budgets, new statements from multiplicative data alone, and twisted positivity below the horizon add nothing.
3. **The three families reduce to three constructions and one law.**
   - **U1 — positive gauge mass or an actual budget**, a comparison of collided escape forms with a Rosati quantity, or of a budget slope with the spectral count; or a non-graded output (a non-isolation law).
   - **U2 — the positivity of `W`**, or its gauge-charged and elliptic approximations: separating windows with a margin law, the odd-sector sign beyond the conductor.
   - **U3 — a form positive and equivariant at once**: an inequality for the computed defect of `D`, or a positivity-preserving Hecke counterterm for torsion energies; with gauge-charged input and a non-multiplicative localizer.
   - **The common law:** arithmetic forces the zero spectrum to be elliptic — complex conjugation and the functional-equation reflection agree on the zeros. It appears as rate zero in U1, as positivity of `W` in U2, as equivariance of `D` or exhaustion of the blind ideal in U3, as `Δ = 0`, as typicality of the gauge point `0`, and as the absence of zeros at every ordinate in the deformation reading.
4. **Where the families meet.**
   - **U1 and U2** meet at the square-root threshold, at selection, at the Lefschetz sequence, at the one-sided count, and at zero ordinates (the detector's prime polynomial).
   - **U2 and U3** meet at one inequality, `Δ ≤ D` with equality: the Weil sign, the Hodge index, effectivity, naive heights, budget sufficiency, the equivariance of `D`, the per-ordinate ceilings.
   - **U1 and U3** meet at the cofactor module (escape forms are collided), at multiplicative forcing, at the base, at the counting and budget currencies, at the torsion measure (`ψ` its potential, `M` its Fourier coefficient) and at the gauge point.
5. **Partial progress is family-specific.**
   - U1's rate axis is blocked at quasi-RH; its non-graded outputs (escape location and classification, Abel atoms, budget calibrations) classify without excluding.
   - U2 has aperture windows, the local part on short cycles, the finite negative index, short-window averages, zero-ordinate positivity, twisted positivity below the horizon, the forcing half and the first separating windows.
   - U3 has blind, half-blind and isotropic sub-carriers, non-localizing positivity, boundary forcing, collars, the κ = 1 class, the closed contraction, collision and deformation calculus, a computed positive form `D`, torsion energies positive before renormalization, and the exact counting currencies.

   A result that converts one family's partial progress into another's would itself be a new mechanism: an odd-sector sign beyond the conductor (U2) from moments over zero ordinates (U1); a renormalized positivity of torsion energies (U3) that yields Weil positivity on atomic tests (U2); a gauge margin (U2) carried by successor links (U3).
6. **Seven obstructions are common to every amplification, multiplicative argument, invariant carrier, one-variable positive object, deformation, count and renormalized limit.** Depth homogeneity; gauge invariance; hyperbolicity (resonance its only exception); Landau–Fejér positivity; deformation rigidity (positive deformations detect zero-free ordinates); the counting law (every count is the sign); and the renormalization law (positivity is lost at the diagonal). Collided positivity escapes all seven and sees nothing; Rosati positivity sees everything and is RH; torsion energies come closest, positive and equivariant except at the diagonal. Over `𝔽_q` a polarization of `C × C` makes positivity and equivariance one, with a finite diagonal self-intersection; over `ℤ` none is known. The [summary](obstacles-summary.md#4-would-the-b-tier-obstacles-require-a-new-field-of-mathematics) describes what a structure making them one must satisfy.
