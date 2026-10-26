# Route-unification ledger

**Status 2026-10-26, corpus `19b8caad1` with the working tree of that day.** The 31 live routes, 17 candidates and PW-B are faces of three construction problems:

- **U1 — critical arithmetic cancellation**: the *rate* reading.
- **U2 — complete signed positivity**: the *sign* reading.
- **U3 — faithful realization and forcing**: the *carrier* reading, with an *invariant* sub-reading and a *counting* sub-reading.

All three ask one question in different currencies: **what forces the actual arithmetic source to be blind to off-line zeros?** The corpus now states that question as one about two forms on the test space of `ζ`:

- **U2 is the positivity of the equivariant form.** Weil's form `W` is Hecke equivariant for every zero configuration; its positivity is RH (Lefschetz part at one prime, budget sufficiency, Rosati positivity).
- **U3 asks for a computed form that is positive and equivariant.** The collided form `D = Σ m_ρ|f̂(ρ)|²` is positive unconditionally and Hecke equivariant iff RH [S]; `Re W = D − Δ`. Every counting reformulation of positivity (section counts, effectivity, naive heights, one-sided counts, a tensor base, horizon torsion) is RH; every unconditional positivity found is collided, isotropic, non-localizing, averaged, dominated or below the conductor horizon.
- **U1 excludes by comparing a collided object with a Rosati one.** Escape states are phase kernels whose forms are collided Cauchy forms, positive automatically; RH is positive gauge mass of every escape state, and the one-sided count `ψ(x) − x ≤ C√x log²x` is RH.

The readings are equivalent at their endpoints:

- **U1.** A generic orbit's growth rate equals the depth of the deepest zero it sees; one test's Lefschetz sequence grows like `p^{Δm}`; escape at `ε` is the presence of zeros right of `1/2 + ε`; power growth of the damped energy translates zeros.
- **U2.** Orbit Hodge positivity holds iff the orbit is blind; on spans `{g, T_{p^m} g}` of short tests it is Weil's Castelnuovo–Severi inequality, whose local part holds.
- **U3.** The maximal sharp-stable positive Meyer ideal is the off-line-blind ideal; the κ = 1 completed class is `ℝ^× · ζ`; a section count with RR and Bézout is the Hodge index; an effectivity function exists iff RH.

**Three readings cut across the families.**

- **The local type.** At an off-line reflection pair multiplicative correspondences act by boosts, the successor unipotently, the functional equation and its flow-conjugates `σ_γ` by the swap. Elliptic localization within correspondence-closed carriers is resonance (at most one prime). U1 reads the boost as growth; U2 reads boost-invariant positivity as isotropy; U3 needs a non-multiplicative localizer — `σ_γ`, whose odd sector forces and whose unconditional positivity stops at the conductor horizon.
- **The gauge point.** Multiplicative data determine a source up to its gauge orbit; finite multiplicative lattice forms are blind to real sign gauges [S]. The successor connection is the gauge-charged datum and reconstructs the prime phases on `2 → 3 → 4` [S]. The first gauge charge of positivity is a height twist; from the second prime on it is not archimedean.
- **The pairing.** Collided objects pair `ρ` with `ρ̄` (determinants, coupled counts, escape forms, `D`); Rosati objects pair `ρ` with `1 − ρ̄` (`W`, the trace of a polarization). Collided positivity is free; Rosati positivity is RH. The three families meet where a collided quantity must be compared with a Rosati one.

The invariant sub-reading of U3 is closed: pole order pays inserted zeros; contraction and collision are classified (anchored quartets force `κ ≥ 3`; couplings anchor and never count; the global collision has no analytic carrier); the coupled class is not rigid, and a one-sided central ceiling survives [S]. The counting sub-reading is closed as a reduction: every count is the sign. Identical receivers still do not mean identical producers: each family keeps its own missing construction.

Companions: [complete report](hard-obstacles.md), [summary](hard-obstacles-summary.md), [walls ledger](walls-ledger.md). Evidence: corpus search and Lean statement reading (`logs/review-2610/working-log-v3.md`). `[S]`, `[R]` as in the walls ledger.

## 1. Levels of unification

| Level | What it justifies | What it does not |
|---|---|---|
| **Exact identity** | Two expressions are equal on a stated source and normalization (`Re W = D − Δ`; `W_λ = W_ζ` twisted at `π/log 2` plus corrections). | Extension to another completion or norm. |
| **Receiver isomorphism** | Same threshold at every rate `σ` (width functor). | Equal finite tests, rates or difficulty. |
| **Currency equivalence** | Two statements are proved equivalent to each other, not only to RH (the five effectivity currencies [S]). | That either is easier. |
| **First-rung coincidence** | The weakest nontrivial conclusions coincide (quasi-RH). | Equality of later rungs or of producers. |
| **Gauge equivalence** | Sources with the same multiplicative data differ by a gauge twist. | Any statement at a chosen point of the orbit. |
| **Local-type equivalence** | Mechanisms invariant under the same hyperbolic symmetry force the same isotropy. | That either sees the sign. |
| **Pairing equivalence** | Two positivities are collided forms of the same conjugate pairing. | That either is Rosati positivity. |
| **Layer equivalence** | Two mechanisms realize the same layer of Weil's argument. | That a lower layer forces a higher one. |
| **Maximality / isotropy** | Every member of a class lies in one extremal object, or has isotropic fibres. | That the actual source reaches it. |
| **Rigidity / ceiling** | A set of invariants has exactly one solution, or bounds an invariant. | That the solution's zeros are located; a ceiling is not rigidity. |
| **Classical reduction** | A mechanism's strongest output is a classical estimate (coupled budget = Hadamard count; boundary forcing = dlVP; conductor horizon = `\|Λ\|` bound). | That a refinement stays classical. |
| **Conservation** | An exact balance on a deformation class. | An absolute bound for the base point. |
| **Directional transfer** | A proved bound implies another under hypotheses. | The converse. |
| **Shared construction problem** | The same missing estimate, sign or object. | That one producer yields the others. |
| **Analogy** | A model suggests a mechanism. | Validity for `ζ`. |

## 2. The three families

### U1 — Critical arithmetic cancellation (rate reading)

**Primary data:** prime or Möbius coefficients. Observables: lag, spline, deficit, Abel moment, history, regularized series, pronic energy, Vaughan Gram, cofactor module and profile, divisor sums, Lefschetz sequences, one-sided counts, horizon torsion.

**Missing input:** a signed estimate at every positive slack, at the gauge point `0`.

**Proved unifications:**

- The width functor makes the spectral, abscissa, damped Möbius and Liouville, ξ half-plane and Suzuki receivers isomorphic.
- First-rung coincidence: every graded gain beyond VK is a fixed strip.
- Vaughan transition at half damping; below it the signed long-modulus quadrature.
- **Escape.** Escape at `ε` ⇔ zeros right of `1/2 + ε` up to countably many `ε`; RH ⇔ admission at every damping. Escape states of finite, power-row and summable dominant configurations are phase kernels of rank the number of dominant zeros; a dominant split yields them, with zero gauge spectrum; their forms are collided Cauchy forms. Abel escape states read the poles of the symbol on the abscissa line [S]. RH ⇔ positive gauge mass.
- **Counting forms.** RH ⇔ `ψ(x) − x ≤ C√x log²x` eventually; RH ⇔ `ψ(N) = N + O(√N log²N)`, the horizon torsion of `ℤ/lcm(1,…,N)ℤ` against the Euler characteristic of the box class; integrality gives Nair's floor.
- **Gauge form.** The Möbius half-power law at `0` is RH, holds a.e., fails at the Liouville twin; the prime source is typical at `0` modulo its pole.
- **Loss law.** Moments, family averages, products and relative powers lose linearly; twists are rate neutral.

**Subfamilies:** width readings (WL, SRT, PBM, MC, JAS, FU, RP, DR); critical energy (PM, CTF with BVI, ACCE, ADR, SAEI, SSA, THIM); oscillatory payment (the capacity `Δ`).

**Separate currencies:** LI (reciprocal depth), RB (extremal inequality), BAG (local recurrence).

### U2 — Complete signed positivity (sign reading)

**Primary object:** the complete prime–Gamma–polar Weil form, Hecke equivariant; equivalently the spectral side of the explicit formula; equivalently the Rosati trace of the correspondence ring.

- Direct attacks on its sign: RW, SZ, CHMD, OWU, EWU, ACT, AIP, HF, TT.
- Identification with Hodge index, Castelnuovo–Severi on Lefschetz spans and Rosati positivity: ACS, HF, SRT.
- Sign under other quantifiers: LA, TH, HCF, GTA, XN, PA.

**Proved unifications:**

- RW ⇔ SZ ⇔ CHMD at fixed aperture; HF ceiling ⇒ AIP allocation ⇔ ACS strict-cone RR; one-shift variation, odd capacity and blind minima are parity components.
- Short-window averaged positivity at `Γ^{99/100}`; the off-line field; zero-ordinate positivity for nonnegative tests.
- Lefschetz form and local–global split: one prime, short cycles, one shift.
- Correspondence form: RH ⇔ every normalized Hecke graph of the spline effective ⇔ budget sufficient ⇔ Rosati positivity.
- **Two-form identity:** `Re W = D − Δ`; RH ⇔ `W = D`; `W` equivariant, `D` positive; RH ⇔ `D` equivariant [S].
- **Elliptic sectors:** on `σ_γ`-twisted tests `W` is `W` of the shifted configuration; below the conductor horizon it is nonnegative for every test; the odd sector forces companions.
- **First gauge window:** on windows below `log 3` the Liouville twin's form is `ζ`'s form at height `π/log 2` plus explicit corrections; the twin is positive on tests with small edge mass.
- Worst twin on nonnegative tests; ground rate = polar rate.

**Common localization:** at each aperture a finite low-frequency sector; in the incidence picture prime-sum edges; across heights selection below the zero spacing; on Lefschetz spans the Lefschetz part; in correspondence form the sufficiency of the budget; in the two-form picture the defect `Δ`.

### U3 — Faithful realization and forcing (carrier, invariant and counting readings)

**Carriers:** geometric (ACS, Meyer surface, AOG, correspondence surface, theta surface, polar surfaces of AE); operator-theoretic (RN, GTA, PCS, IRK); probabilistic (W1C, FEL); photonic (PTR); categorical (CDC, SC, WBF, RFHM); divisor-diagnostic (HJ, SEC, BSH, APF, EWJ, EGC, PW-B); topological (TG); heat and divisor (WD cap, ALDG); gauge-geometric (BGG).

**Proved unifications:**

- **Maximality and isotropy, explained by local type.** Sharp-stable positive ideals lie in the blind ideal; positive ideals without sharp stability are half-blind; coupled point-stable carriers are isotropic. All three are the boost law.
- **Resonance and elliptic localizers.** Correspondence-closed carriers are elliptic only at resonant scales; `σ_γ` is the unique reflection-compatible affine localizer; Hecke + `σ_γ` stability is blindness.
- **Non-localizing positivity** holds for every prime weight.
- **Detectors** (HJ, SEC, CDC, BSH, IRK, W1C) read whether a Hecke symbol is elliptic.
- **Faithful branch:** operator-norm faithful positivity is RH plus simple zeros.
- **Invariant rigidity:** the κ = 1 completed class is `ℝ^× · ζ`.
- **Contraction and collision:** real pairs free; quartets against a real anchor of twice the weight; anchored quartet ⇒ `κ ≥ 3`; planting costs `Δκ ≥ 2`; couplings have even real orders and cannot empty the deepest line; the global collision has no analytic carrier.
- **Coupled class:** not rigid at critical-zero ordinates; chiral (outward splitting positive, inward collapse not); central ceiling ⇒ RH [S].
- **Counting:** section count (RR + Bézout) ⇔ Hodge; effectivity function ⇔ Hodge; naive heights ⇔ Rosati positivity; base `h⁰` does not extend; the theta surface's counting polarization is fibre-independent; lattice counts on the square collapse; five currencies one statement [S].
- **Weil's layers:** identities, theorem of the square, budget and involution free; kernel and coupled counts collided.
- **Successor:** affine positivity induced from dilations; Weil's extensions a box over critical zeros; the successor connection reconstructs prime phases [S].

**Common missing object:** a pre-divisor source with a **forcing law** placing it in the maximal blind ideal, with input that is computed (not a counting reformulation of the sign), gauge charged beyond the archimedean line, localized by a non-multiplicative operation (or polarized), not scaling with amplification, and, for complex quartets, anchored at no pole or conductor cost.

### The forcing currency: where the families meet

| Mechanism | Family of origin | What it forces | Where it stops |
|---|---|---|---|
| Multiplicative positivity (boundary) | U3 | `ζ(1+it) ≠ 0`; capacity `⌊k/2⌋`; with growth input dlVP, Littlewood, VK | Interior gain only from growth; next rung a fixed strip (U1). |
| Coupled height positivity in completed systems | U3 | `⌊κ/2⌋` collars; κ = 1 collar zero-free; `5d < 9κ`; κ = 1 class | Collar width `1/log T`. |
| Invariant carrier positivity | U2/U3 | Blindness, half-blindness, isotropy | Boost invariance. |
| Non-localizing positivity | U2/U3 | Coercivity at bounded aperture | Every prime weight. |
| Elliptic localization by `σ_γ` | U2/U3 | Twisted positivity below the conductor horizon; companion forcing from one odd-sector sign | Source-blind below the horizon; the forcing threshold lies above it for every `δ < 1/2` [R]. |
| Positivity on nonnegative tests | U2 | Upper bounds on the source | Shared by dominated twins. |
| Linear rigidity | U3 | The coefficient measure is `ζ`'s | Zeros are nonlinear in the measure. |
| Pole order; positive contraction | U3 | Index = pole increment + critical traffic; real pairs free; anchored quartets | Pays inserted zeros; `κ ≥ 3` for anchored quartets. |
| Collision by coupling | U3/U1 | Zero-tax contraction at one ordinate; classical local count | Even real orders; Fejér barrier; conductor `log γ`; coupled class not rigid, central ceiling [S]. |
| Successor prescription | U2/U3 | Hecke weight; threshold `s ≥ 1/2`; Kronecker-null spectrum | Never reaches atoms. |
| Multiplicative data | U1/U3 | Statements true on the whole orbit | The gauge point. |
| Correspondence identities | U3 | Normalized graphs; similitude; involution | Hold on the golden datum. |
| Collided positivity (determinants, coupled counts, escape forms, `D`) | U1/U3 | Automatic positivity | Sees no sign; its equivariance is RH. |
| Counting (sections, effectivity, heights, one-sided counts, base, torsion) | U3/U1 | Exact receivers | Each is RH. |

The invariants run in parallel on the boundary and in the interior:

| Boundary line `Re s = 1` | Interior (degree one) |
|---|---|
| Nonnegative weights (N) | Coefficient positivity (N) |
| Integer divisor (Z) | Riemann's FE |
| Simple pole (S) | Simple pole (S) |
| Pole isolation (I) | Strip holomorphy (H) |
| N + Z + S + I ⇒ no boundary zeros; each necessary | N + FE + S + finite order ⇒ `ζ`; dropping S or H admits off-line zeros |
| Pole of order `k` carries `≤ ⌊k/2⌋` boundary zeros | `≤ ⌊κ/2⌋` collar zeros; κ = 1 class `ℝ^× · ζ`; anchored quartet ⇒ `κ ≥ 3` |
| Families: only the two-torsion exception | Real pairs free; quartets need anchors; coupled class not rigid, ceiling [S] |

## 3. Every route and candidate

Abbreviations in the last column: *Rate* = graded rate (first rung quasi-RH). *Aperture* = pointwise or averaged window. *Carrier* = carrier, height, heat or order exhaustion. *Escape* = residues and infinite-height mass. *Lefschetz* = the Lefschetz part at one prime. *Gauge* = gauge-charged positivity. *Elliptic* = odd-sector sign beyond the conductor horizon. *Two-form* = equivariance of `D` or a computed positive equivariant form. *Count* = a count that is not a reformulation of the sign.

### Live routes

| Route | Family | Common receiver or invariant | Distinct missing producer | Partial-progress axis |
|---|---|---|---|---|
| **WL** | U1 | Width via spline, deficit, critical energy; one-sided count; horizon torsion | Signed lag/energy at every slack | Rate; filtered averages |
| **RW** | U2 | Ground energy `μ`, shell flux, prime ladder | Sign at every aperture; collar estimate | Aperture; Lefschetz |
| **FU** | U1 | Completed Abel moment | Complete history covariance | Rate |
| **RP** | U1 | Matched-quantile history floor | High-LCM and moving-core payment | Rate |
| **PA** | U1/U2 | Prime–archimedean current; Hausdorff moments | Low shifts across unbounded orders | Carrier (order) |
| **MC** | U1 | Mertens; bands ⇔ `Θ<1`; gauge point `0` | Interior anti-alignment | Rate; gauge |
| **TT** | U1/U2 | Directed Wold covariance; odd form | Covariance sign | Aperture |
| **LA** | U2 | Finite-head coefficients; heat | Zero heat on the residual region | Carrier (heat × height) |
| **TG** | U3/U2 | Winding, sub-unit trace | Residual sign, sub-unit bound | Carrier |
| **HF** | U2/U3 | Full cone; index `D`; one-prime tower; normalized graphs; effectivity; naive heights; `W = D − Δ` | Lefschetz part, `D < 2`, a naive height, or equivariance of the collided form | Aperture; Lefschetz; two-form; count |
| **CHMD** | U2 | Odd bound states; nodal quotient | Nodal / reflected-prime sign | Aperture |
| **TH** | U2 | All-rank heat-Hankel sign | Signed vectors at one time | Carrier (rank) |
| **RN** | U3 | `det₂` resonances | Boundary orientation | Carrier |
| **WD** | U3/U2 | Ward cap; collisions; heated head | Cap vanishing; residual heat region | Carrier |
| **LI** | U1 | Reciprocal-depth clock | Subexponential floor | Rate (separate currency) |
| **SZ** | U2 | First variation = Weil energy | Same sign as RW | Aperture |
| **PM** | U1 | Admission at every damping; cofactor module; phase kernels; Abel boundary measure; gauge mass | Signed small-damping energy; positive gauge mass; residues and infinite-height mass | Rate (damping); escape |
| **JAS** | U1 | Level-one budget ⇔ strip | Half-power budget | Rate |
| **CTF** | U1/U3 | Báez–Duarte residual | Readout → 1 and energy → 0 together | Rate (damping) |
| **HCF** | U2 | Two literal heat grids | Both grids at all degrees | Carrier (degree) |
| **XN** | U2/U3 | Newton interior margin | Covering discs with margin | Carrier |
| **BAG** | U1/U3 | Strong recurrence ⇔ local nonvanishing | Returns near possible zeros | Carrier |
| **EWU** | U2 | Even blind minimum; finite-level weights | Low and mixed modes | Aperture |
| **GTA** | U2/U3 | Quartic Schur decay | Rank-uniform decay | Carrier (rank) |
| **OWU** | U2 | Odd capacity; first window through a prime (a height twist of `ζ`) | Reflected-prime and polar payment; non-archimedean charge | Aperture; gauge |
| **PBM** | U1 | Graded regularized abscissa | Convergence to `1/2` | Rate |
| **RB** | U1 | Robin on colossally abundant numbers | Extremal tail | Rate (separate currency) |
| **SRT** | U1/U2 | Lag family; detector = odd sector of `σ_γ`; one-prime Lefschetz sequence | Lag sign; selection; Lefschetz part; odd-sector sign beyond the horizon | Aperture; selection; elliptic |
| **ACT** | U2 | One-shift variation | All-profile reflected collar | Aperture |
| **AIP** | U2 | Shared incidence allocation; polar-neutral collapse [S] | One shared budget with prime-weighted remainder | Aperture |
| **ACS** | U2/U3 | Hodge index; RR; blind ideal; counting; contraction and collision; coupled class; two forms | A computed positive equivariant form, a selective count, or the central ceiling | Carrier; aperture; Lefschetz; gauge; two-form; count |

### Candidates and PW-B

All are U3 unless noted. Each lacks the forcing law of §2; the constraints of the [complete report](hard-obstacles.md#3-the-17-candidates-and-pw-b) apply to all.

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

For `σ ≥ 0`, `Δ ≤ σ` is equivalent to each of: graded lag, spline, deficit, band and regularized-series bounds; admission of every damping above `σ`; the ξ half-plane bound; the Suzuki exponent `1+2σ`; the JAS budget; balanced, centred-prime and short-window savings; Vaughan empty-leg and tail-rate statements; one test's Lefschetz growth `O(p^{σm})`; all-test one-sided Lefschetz bounds at one prime; linear tensor loss `L_k = kσ`. Escape at damping `ε` reads the width: escape occurs at every `ε < Δ` outside a countable set. VK is the strongest unconditional point.

### 4.2 The common Weil form (U2)

| Statement | Relation | Qualification |
|---|---|---|
| Exact form | `Q = (γ₀−2)‖F‖² + Lévy + 4·horizon + 2∫incoming·G²` | Every compact `C²` test. |
| Two forms | `Re W = D − Δ`; RH ⇔ `W = D` | Every compact `C²` test for `ζ`. |
| Equivariance | `W(T_L f, T_L g) = W(f, g)`; RH ⇔ `D` equivariant | [S] |
| Ground | `μ(A) ≥ 0 ⇔ W_{A′} ≥ 0` for `A′ < A` | RH ⇔ `μ > 0` at every `A`. |
| Prime ladder | RH ⇔ cumulative frozen relaxation `≤ μ(3/10)` | Birth jumps vanish. |
| Finite level | RH ⇔ every aperture admits a positive weight system | No sign premise. |
| Lefschetz | RH ⇔ `\|c_m^{(p)}\| ≤ c_0^{(p)}`; ⇔ one-sided at one prime; short cycles; one shift | Local part positive for `η ≤ 3/10`. |
| Normalized graphs | RH ⇔ every normalized Hecke graph of the spline effective | Square theorem and budget free. |
| Elliptic sectors | `W` on `e^{−iγu}r` = `W` of `Z − iγ`; even sector `+m\|tr\|²`, odd `−m\|tr\|²` at ordinate `γ` | Twisted positivity below the conductor horizon. |
| Forcing half | One odd-sector sign + local count + depth dominance ⇒ off-line companion within `R` | Needs `e^a ≳ (log γ)^{1/(2δ)}` [R]. |
| First prime window | `W_λ = W_ζ(e^{−iγ₂u}·) + Δ_arch + Δ_pole`; twin positive on tests with edge mass `≤ 1/1961` | Odd window `181/500`. |
| Averaged | Positive at `A ≤ κ₀ log Γ` on `Γ^{99/100} ≤ H ≤ Γ/8` | Frequency average only. |
| Pointwise floor | `Q_γ ≥ −4(A+1)²e^A N²Φ(γ)`; nonnegative tests positive at almost every zero ordinate | Signed tests: floor only. |
| Transfers | RW ⇔ SZ ⇔ CHMD sign transfer; HF ceiling ⇒ AIP allocation ⇔ ACS strict-cone RR; one ACT shift decides RH; RW margin ⇒ TH/HCF heat window | Fixed aperture; directional; rank and time coupled. |

### 4.3 Geometric and counting currency (U2 ↔ U3)

- **Scaling and correspondence surfaces.** Pairing = pole plane − Weil form; Hodge index, RR plus ample effectivity, and zero sector defect are each RH. Normalized graphs with `deg N(y) = δ(y,y)/2`, quadratic graph map, similitude budget.
- **Counting.** On every polar surface: a section count with RR and Bézout ⇔ Hodge; an effectivity function (Riemann inequality, subquadratic growth in degree zero) ⇔ Hodge; abundance ⇔ positive self-intersection in degree zero; Tate: a degree-two form is nonnegative iff it has a naive height. For `ζ`: each ⇔ RH; RH ⇔ every integral Rosati form has a naive height; RH ⇔ horizon torsion at `√N` precision; the five currencies are one statement [S].
- **What counts give.** The theta `h⁰` has linear RR and no quadratic Riemann inequality; the theta surface has a counting polarization `πJ²/t`, the same on every fibre; lattice counts on the square give `ζ(s₁ + s₂)` or `ζ(s₁)ζ(s₂)`, i.e. boundary or determinant positivity.
- **Meyer surface; maximal blind ideal; Lefschetz spans; function-field calibration** (Rosati cones, genus-one Hodge, exterior counts, `ℙ¹ × ℙ¹` effectivity).

The Weil sign, ACS RR + Bézout, the Meyer Hodge index, exhaustion of the maximal blind ideal, the Castelnuovo–Severi inequality on Lefschetz spans, effectivity of normalized graphs, sufficiency of the budget, Rosati positivity, a section count, an effectivity function, naive heights, a fixed tensor loss, horizon torsion at `√N`, the one-sided count, the equivariance of `D` and the vanishing of `Δ` are the same statement. A computed positive equivariant form, an elliptic forcing law beyond the horizon, a non-archimedean gauge-charged positivity, a selective count and an oscillatory capacity bound would each be a proof of it, or a piece of one.

### 4.4 Ground rate and clustering

`Δ ≤ polarRate = groundRate ≤ 1/2`, `RH ⇔ groundRate = 0`; form-norm rates equal `Δ`. RW, SRT, ACS, EWU and AIP share this currency.

### 4.5 Depth on the divisor (U3)

The seam charge, the mate gain and the other zero-indexed diagnostics have exact depth laws; the BSY functional and the defect `Δ` are nonnegative and vanish exactly on critical zeros; the Hecke defect of `D` is `Σ m(2cosh(2δL) − 2)|f̂(ρ)|²`; the symmetric-square spectrum is nonnegative iff the symbol is elliptic. **Diagnostics and capacities read depth; none forces it to vanish.**

### 4.6 Invariants, capacity, contraction and collision (U3 selectivity)

- **Rigidity.** N + FE + S + finite order ⇒ `ζ`; `CompletedPositiveSystem 1 d = ℝ^× · ζ`.
- **Relaxations.** Pole order 2 or 3, strip poles, no FE, no positivity, boundary invariants alone.
- **Capacity.** Boundary `2Σm ≤ k`; collar `2Σ ord ≤ κ`; gauge `2Σm ≤ κ`; family `Σm ≤ k`.
- **Contraction.** Real pairs at `Δκ = 0`; quartets at `Δκ = 1` (`a ≤ 1/4`) or `2` (`a < 1/2`) with the boundary pole, or against a real anchor; anchored quartet ⇒ `κ ≥ 3`; planting `Δκ ≥ 2`.
- **Collision.** Height coupling at one ordinate; absorption of shifted poles at `κ₀ + 2κ_γ`; Fejér coupling at `9(K+1)/(2K)`; even real orders; Fejér barrier; no analytic global carrier.
- **Coupled class.** Not rigid at critical-zero ordinates; outward splitting positive, inward collapse not; central ceiling ⇒ RH [S]; at zero-free ordinates the ceiling is central nonvanishing [R].

### 4.7 The gauge currency (U1 ↔ U2 ↔ U3)

| Statistic | Gauge behaviour | Consequence |
|---|---|---|
| Moduli, coincidences of products, multiplicative moments, family averages | Invariant | Determine the source up to its orbit. |
| Finite diagonal + ratio + product lattice forms | Unitarily equivalent under real sign gauges [S] | Cannot separate `ζ` from `λ`. |
| Successor connection `conj χ(n) χ(n+1)` | Charged; flat iff Euler vacuum on `[1, N+1]` [S] | Reconstructs `ω(2), ω(3)` on `2 → 3 → 4`. |
| Successor, affine and near-incidence correlations | Charged: mean zero, diagonal variance | A bound must be proved at `0`. |
| Möbius partial sums | Square-root law a.e.; exceptions comeager and null | RH is a property of the point `0`. |
| Chebyshev sums | Square-root law a.e.; at `0` a linear pole | RH is typicality of `0` modulo the pole. |
| Windowed moments on the archimedean line | Gauge moment below `2rX^k ≤ 1` | The threshold is where the line starts to see the point. |
| Weil form on prime-free windows; on nonnegative tests | Weight blind; antitone | Positivity holds for every (dominated) twin. |
| Weil form on windows below `log 3` | Reads the atom `2`; the Liouville twin is `ζ` at height `π/log 2` | First gauge charge is archimedean. |
| Atoms at `2` and `3` | No height flips both; Catalan repulsion `e^{−\|γ\|}/50` [S] | Second gauge charge is not archimedean. |
| Ramanujan torsion sums `c_q` | Invariant under coprime dilation; contrasts kill the pole mode [S] | Torsion characteristics carry `+`/`×` coupling at finite level. |
| Möbius boundary of affine maps | Separates `μ` from its twin (PNT) | Finite presentations are gauge charged. |

### 4.8 The local-type currency (U1 ↔ U2 ↔ U3)

| Correspondence | Local type at an off-line pair | On the line | What invariant positivity forces |
|---|---|---|---|
| Hecke `T_p`, archimedean flow, gauge twist | Boost | Rotation | Isotropy |
| Symmetric dilation by `a` | Boost unless `γ log a ∈ πℤ` (resonant) | Rotation | Fibre zero at a non-resonant scale; elliptic survivor at resonant scales |
| Functional equation; `σ_γ` (at ordinate `γ`) | Swap | Swap | Even sector: nothing; odd sector: vanishing |
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
| Collided form `D` | `ρ ↔ ρ̄` | Automatic; equivariance ⇔ RH [S] |
| Weil form `W`; Rosati trace | `ρ ↔ 1 − ρ̄` | ⇔ RH |
| Exterior counts over `𝔽_q` | `Λ²` collision | Force unitarity |

### 4.10 Currencies that stay separate

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
| Conductor horizon | `e^a ≲ log γ/4` | The forcing threshold `(log γ)^{1/(2δ)}` |
| Central vanishing order of the coupled class | Ceiling ⇒ RH [S] | Rigidity |

## 5. Interfaces

| Interface | Proved | Missing |
|---|---|---|
| WL ↔ PA | Exact trace identity | Source sign |
| WL ↔ AE ↔ ACP (counting) | One-sided count ⇔ RH; horizon torsion ⇔ RH; Nair floor | A signed count beyond integrality |
| MC ↔ PM ↔ BVI | Energy = interior bracket `+ O(1)`; bands ⇔ `Θ<1`; long-modulus decomposition | Signed long-modulus quadrature |
| PM ↔ ADR ↔ ACP ↔ ACG ↔ PL | Escape alternative; translation Gram and Laplace form; phase kernels; dominant-split criterion; escape forms collided; Abel boundary measure [S]; gauge-mass criterion | Residues and infinite-height mass (B3.2); positive gauge mass (B1.2) |
| PM ↔ SSA ↔ THIM | Half-damping endpoint bounded; integer local exponents below half | Sub-half signed interior |
| PM ↔ CTF | Residual = readout² + energy | One row family doing both |
| RW ↔ SZ ↔ CHMD | Sign transfer; first variation; domains | Sign |
| RW ↔ SRT ↔ ACS | One rate currency | `polarRate = Δ` |
| HF → AIP ↔ ACS | Ceiling ⇒ allocation ⇔ strict RR | The inequality |
| HF ↔ SRT ↔ ACS (Lefschetz) | One prime; short cycles; one shift | The Lefschetz part (B1.3) |
| HF ↔ ACS ↔ AE (counting) | Section count, effectivity function, naive heights each ⇔ RH; base `h⁰` does not extend; theta surface soft; five currencies [S] | A selective count (B3.35) |
| HF ↔ ACS ↔ PL (two forms) | `Re W = D − Δ`; RH ⇔ `W = D`; RH ⇔ `D` equivariant [S] | A computation of `D` or its Hecke defect (B3.33) |
| SRT ↔ PL ↔ APT (elliptic) | Detector = odd sector of `σ_γ`; twisted explicit formula; conductor horizon; forcing half; single-height Kronecker laws | Odd-sector sign beyond the horizon (B3.32) |
| OWU ↔ PL ↔ ACP ↔ BGG (gauge window) | First charge a twist; edge reduction; second charge not archimedean; Catalan repulsion [S]; successor holonomy [S] | Edge problem (W8); `{2,3}` twin (W13); non-archimedean charge (B3.26) |
| ACS ↔ MPG ↔ SBWF ↔ U1 | Boundary forced; `⌊κ/2⌋` collar; κ = 1 class; growth gives dlVP/VK; coupled budget = Hadamard count | Better growth input or a non-multiplicative mechanism |
| ACS ↔ ACP ↔ PL ↔ BGG (one variable) | Contraction calculus with `κ ≥ 3`; collision calculus with Fejér barrier and parity; coupled class not rigid, chiral, central ceiling [S] | The ceiling (B1.12); central nonvanishing (B3.34) |
| ACS ↔ APD ↔ ACP (carriers) | Isotropy; half-blind and left-blind ideals; boost law; resonance law; non-localizing positivity | A non-multiplicative localizer |
| ACG ↔ MC ↔ TTPC ↔ SSA ↔ BGG | Gauge invariance; a.e. laws; gauge-charged pair statistics; finite lattice blindness [S] | A gauge-charged estimate at `0` (B3.24) |
| ACG ↔ AKT ↔ AOG ↔ ACP ↔ PL | Linear loss; total-length law; Künneth collapse; tensor-loss receiver; twists rate neutral | Fixed tensor loss (B1.9) |
| AIP ↔ BGG | Polar-neutral collapse of the diagonal reserve; log-cell remainder bound [S] | Prime-weighted remainder payment (B3.8) |
| WL ↔ ACS (windows) | Filtered deficit → averaged positivity; off-line field; witness persistence | Selection below the zero spacing (B1.4) |
| LA ↔ WD ↔ ALDG | Large-height repair; collision–index bridge | Residual heat region |
| HJ ↔ HCF ↔ SEC | Residual = two-grid sign = seam vanishing | Pre-divisor forcing |
| BAG ↔ SRT/WL | Recurrence right of `1/2+σ` ⇔ lag floor at `σ` | Returns near zeros |
| APT → RW/EWU/ACT/AIP | Positive restricted families; source selection | Transfer to an RH-complete cone |
| AOG → HF/ACS/SRT | Orbit Hodge ⇔ blindness; index exit; theta `h⁰` | Forcing; a selective surface count |
| PTR ↔ W1C | Real-rooted finite producers | Arithmetic producers |

## 6. Consequences

1. **Count each producer once.**
   - a small-damping signed budget, equivalently positive gauge mass: PM, CTF, BVI, MC;
   - the positivity of the equivariant form (the Lefschetz part): RW, SZ, CHMD, OWU, EWU, ACT, AIP, HF, TT, ACS, SRT;
   - a residual heat-region sign: LA, WD, TH, HCF;
   - a forcing law into the maximal blind ideal, with a computed positive equivariant form: TG, RN, ACS, HF and all candidates;
   - a gauge-charged estimate or positivity at the point `0`: MC, PM, BVI, TTPC, SSA, OWU, EWU, ACS;
   - an odd-sector sign beyond the conductor horizon: SRT, OWU, ACT, ACS.
2. **Finished below RH strength:** reformulation; carrier maximality and isotropy; local-type classification including resonance and `σ_γ`; invariant completeness; the relative budget; the contraction and collision calculus; coupled-class rigidity (false); successor coupling; escape in model configurations and its location; the correspondence layers below the sign; every counting currency. New equivalent endpoints, new invariant carriers, new non-localizing carriers, new multiplicative certificates, new one-variable contractions or couplings, new collided positivities, new counting reformulations, new statements from multiplicative data alone, and twisted positivity below the horizon add nothing.
3. **The three families reduce to three constructions and one law.**
   - **U1 — positive gauge mass**, a comparison of collided escape forms with a Rosati quantity; or a non-graded output (a non-isolation law).
   - **U2 — the positivity of `W`**, or its gauge-charged and elliptic approximations: the first windows through primes, the odd-sector sign beyond the horizon.
   - **U3 — a computed form that is both positive and equivariant**: the equivariance of `D`, or a selective count of growing rank, with gauge-charged input and a non-multiplicative localizer.
   - **The common law:** arithmetic forces the zero spectrum to be elliptic — complex conjugation and the functional-equation reflection agree on the zeros. It appears as rate zero in U1, as positivity of `W` in U2, as equivariance of `D` or exhaustion of the blind ideal in U3, as `Δ = 0`, and as typicality of the gauge point `0`.
4. **Where the families meet.**
   - **U1 and U2** meet at the square-root threshold, at selection, at the Lefschetz sequence, and at the one-sided count.
   - **U2 and U3** meet at one inequality, `Δ ≤ D` with equality: the Weil sign, the Meyer and scaling Hodge index, effectivity, naive heights, budget sufficiency and the equivariance of `D`.
   - **U1 and U3** meet at the cofactor module (escape forms are collided), at multiplicative forcing, at the base (fixed tensor loss), at the counting currencies (one-sided count, horizon torsion) and at the gauge point.
5. **Partial progress is family-specific.**
   - U1's rate axis is blocked at quasi-RH; its non-graded outputs (escape location, classification, Abel boundary measures) classify without excluding.
   - U2 has aperture windows, the local part on short cycles, short-window averages, zero-ordinate positivity, twisted positivity below the horizon, the forcing half and the first prime window.
   - U3 has blind, half-blind and isotropic sub-carriers, non-localizing positivity, boundary forcing, collars, the κ = 1 class, the closed contraction and collision calculus, the central-ceiling survivor, the exact counting currencies and a positive form `D`.

   A result that converts one family's partial progress into another's would itself be a new mechanism: an odd-sector sign beyond the horizon (U2) obtained from a source estimate at zero ordinates (U1); a computation of `D` (U3) whose Hecke defect bound is a density theorem (U1); a gauge-charged window margin (U2) carried by successor holonomy (U3).
6. **Five obstructions are common to every amplification, every multiplicative argument, every invariant carrier, every one-variable positive object and every count.** Depth homogeneity; gauge invariance; hyperbolicity (with resonance as its only exception); Landau–Fejér positivity (anchors, even collisions, no analytic global collision); and the counting law (every count is the sign). Collided positivity escapes all five and sees nothing; Rosati positivity sees everything and is RH. Over `𝔽_q` a polarization of `C × C` makes the two one; over `ℤ` none is known. The [summary](hard-obstacles-summary.md#4-would-the-b-tier-obstacles-require-a-new-field-of-mathematics) describes what a structure making them one must satisfy.
