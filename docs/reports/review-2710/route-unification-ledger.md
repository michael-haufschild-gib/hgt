# Route-unification ledger

**Status 2026-10-27, corpus `7eaf4d7ef` with working tree.** The 31 live routes, 17 candidates and PW-B are faces of three construction problems:

- **U1 — critical arithmetic cancellation**: the *rate* reading, and its pointwise form, *alignment* of `γ log p` at zero ordinates.
- **U2 — complete signed positivity**: the *sign* reading.
- **U3 — faithful realization and forcing**: the *carrier* reading, with *invariant and deformation*, *counting*, *renormalization*, *field* and *gauge* sub-readings.

All three ask one question in different currencies: **what forces the actual arithmetic source to be blind to off-line zeros?** The corpus now states that question through quantities of one logarithmic potential `log|ξ|` and of its counterpart on the characteristic circle:

- **U2 is the positivity of the equivariant form.** Weil's form `W` is Hecke equivariant for every configuration and has finitely many negative directions at every aperture; its positivity is RH.
- **U3 asks for a form positive and equivariant at once, or for a bound on the field.** The collided form `D` is positive, faithful, the logarithmic Sobolev norm, computed from `ξ`; its Hecke defect is the moment of inertia `M_f`; it is equivariant iff RH; `Re W = D − Δ`. The field of the zero divisor is computed by `(ζ′/ζ)² = L(Λ ⋆ Λ)`; the transverse energy is quantized; RH iff every right-zero field `≤ 1`. On the circle, torsion energies are positive at `r < 1` and Hecke similar up to the cutoff; their counterterm is the identity, so their renormalized limit (minus the prime kernel) keeps no positivity; the archimedean germ keeps it on a hyperplane; local Hodge index holds at each prime and does not sum. Every counting reformulation of positivity is RH.
- **U1 excludes by comparing a collided object with a Rosati one, a budget with a spectral count, or a short prime sum with a zero-side reserve.** Escape states have collided Cauchy forms; RH is positive gauge mass. A linear prime-error budget is RH. At zero ordinates the `σ_γ`-odd detector, the outward reserve and the field threshold become upper bounds for short prime sums; outside the strip the primes anti-align at a deep zero's ordinate by a theorem.

The readings are equivalent at their endpoints:

- **U1.** A generic orbit's growth rate equals the depth of the deepest zero it sees; one test's Lefschetz sequence grows like `p^{Δm}`; escape at `ε` is the presence of zeros right of `1/2 + ε`; `(1/L) log D(T_L f) → 2a_f`; dyadic Hecke defects grow sub-doubly-exponentially iff RH; the prime-error budget exists iff `Δ = 0`.
- **U2.** Orbit Hodge positivity holds iff the orbit is blind; on Lefschetz spans it is Weil's Castelnuovo–Severi inequality, whose local part holds at every prime; zero negative index at every aperture; nonnegative symmetric-square spectra at one prime.
- **U3.** The maximal sharp-stable positive Meyer ideal is the off-line-blind ideal; the `κ = 1` completed class is `ℝ^× · ζ`; a section count with RR and Bézout is the Hodge index; positive rigidity, chirality and central ceilings at an ordinate are the absence of zeros there; `M_f = 0` for every test; the transverse energy is zero; no right zero feels a field above `1`.

**Ten readings cut across the families.**

- **The local type.** At an off-line reflection pair multiplicative correspondences act by boosts, the successor unipotently, the functional equation and `σ_γ` by the swap. U1 reads the boost as growth; U2 reads boost-invariant positivity as isotropy; U3 needs a non-multiplicative localizer.
- **The gauge point.** Multiplicative data determine a source up to its gauge orbit; a coupling is blind under every real sign gauge iff it is of square class; successor couplings and cell dilations are charged and fix the Euler gauge; positivity of `ζ` separates it from the first twins and keeps separating it from Liouville at every aperture `≥ 23/40`.
- **The pairing.** Collided objects pair `ρ` with `ρ̄`; Rosati objects pair `ρ` with `1 − ρ̄`. Collided positivity is free and computed; Rosati positivity is RH. On torsion cycles complex conjugation is the power map of degree `−1`, so the two pairings coincide there.
- **The counterterm.** Positivity passes a scale limit exactly on the survival cone of the counterterm. The torsion germ has identity counterterm (cone `{0}`), the archimedean germ rank one (polar hyperplane), periodic germs the Cesàro Gram (cone = relations among modes); Gårding's inequality says Weil's form is positive off a finite-rank correction at each aperture [R]; RH is a zero correction.
- **The local–global passage.** Weil's prime kernel is the sum over primes of transverse tower forms, each with a local Hodge index; the sum has no `ℓ²` ceiling; the archimedean place, whose atom self-energy is `log(1/ε)`, must pay it.
- **The field and the energy.** The field of the zeros is computed (U3), vanishes on critical configurations and is outward at terminals (U2's sign in electrostatic form), and its excluding bound — of size `√log γ` at right zeros — is a large-value statement for a short prime sum (U1). The energy is quantized: `0` or at least one per off-line pair.
- **The moment of inertia.** The Hecke defect of `D` is the second depth moment `M_f` up to explicit factors; it amplifies dyadically with the fixed loss `D(f)`, as the genus does in Weil's tensor-power argument, and the amplification converts only rates.
- **The alignment.** Beyond the conductor horizon, at terminals, and at the field threshold, an off-line zero is a large value of a short prime polynomial at a zero ordinate; outside the strip the matching inequality is proved; inside it is a Diophantine statement about `γ log p` [R].
- **The central order.** Deformations of positive systems keep the off-line divisor and cannot be reversed; the central vanishing order is the one invariant they move; the surplus residue is an even central drop.
- **The statistic.** Averages, proportions, almost-every-ordinate positivity and the census place most zeros near the line; none reaches one zero; a quantized statistic below one quantum would.

The invariant and deformation sub-reading of U3 is closed: pole order pays inserted zeros; contraction, collision and the positive polar-configuration cone are classified; deformations detect zero-free ordinates, force nothing and are irreversible; surplus residues are quantized. The counting sub-reading is closed as a reduction. The renormalization sub-reading is closed on the torsion side and open as a coupling of the two places (Q2). The field sub-reading has an exact threshold and no bound (Q1). The gauge sub-reading is closed structurally (square class versus charged) and open as positivity with a margin (Q3). Identical receivers do not mean identical producers: each family keeps its own missing construction.

Companions: [complete report](route-obstacles.md), [summary](obstacles-summary.md), [walls ledger](walls-ledger.md). Evidence: corpus search and Lean statement reading (`logs/review-2710-v3-research-log.md`). `[S]`, `[R]` as in the walls ledger.

## 1. Levels of unification

| Level | What it justifies | What it does not |
|---|---|---|
| **Exact identity** | Two expressions are equal on a stated source and normalization (`Re W = D − Δ`; `L(Λ ⋆ Λ) = (ζ′/ζ)²`; prime kernel = −renormalized torsion energy + log-discriminant; `P = Σ_p L_p`; Gauss's digamma formula). | Extension to another completion or norm. |
| **Computation** | A quantity is produced by an identity from source data (`D` from the `ξ` current; the field from `Λ ⋆ Λ`; `Λ` from log-orders of cyclotomic rings). | Any inequality for it. |
| **Comparison** | Two quantities bound each other with explicit constants (`4L² M_f ≤ E_f(L) ≤ 8(cosh L − 1)M_f`; `D ≍` log-Sobolev norm). | That either is bounded. |
| **Detection** | An object sees each off-line zero at its own height (local theta detector; terminal field, reserve, lens). | Exclusion of that zero. |
| **Quantization** | A quantity is integral or jumps by a quantum at off-line zeros (energy `0` or `≥ 1`; window energy `≥ 2`; surplus residue an even central drop). | That the quantity is computed below the quantum. |
| **Survival** | Positivity of a regularized family passes to its limit exactly on the null cone of the counterterm; the cone is scheme independent. | Positivity off the cone; a coupling that enlarges the cone. |
| **Receiver isomorphism** | Same threshold at every rate `σ` (width functor). | Equal finite tests, rates or difficulty. |
| **Currency equivalence** | Two statements are proved equivalent to each other (six effectivity currencies; prime-error budget and RH; electrostatic forms of RH). | That either is easier. |
| **Per-ordinate equivalence** | A statement at ordinate `γ` is the absence of zeros at `γ`. | Anything at another ordinate; any mechanism. |
| **First-rung coincidence** | The weakest nontrivial conclusions coincide (quasi-RH). | Equality of later rungs or of producers. |
| **Gauge equivalence** | Sources with the same multiplicative data differ by a gauge twist; square-class kernels cannot tell them apart. | Any statement at a chosen point of the orbit. |
| **Local-type equivalence** | Mechanisms invariant under the same hyperbolic symmetry force the same isotropy. | That either sees the sign. |
| **Pairing equivalence** | Two positivities are collided forms of the same conjugate pairing. | That either is Rosati positivity. |
| **Local–global equivalence** | A global form is the sum of local forms over places. | That local bounds sum. |
| **Diophantine equivalence** | Two detectors reduce to the same alignment of `γ log p` at zero ordinates [R]. | That the alignment can be excluded. |
| **Calibration equivalence** | A `ℤ` statement and its `𝔽_q` analogue have the same shape. | That the `𝔽_q` proof transfers. |
| **Layer equivalence** | Two mechanisms realize the same layer of Weil's argument. | That a lower layer forces a higher one. |
| **Maximality / isotropy** | Every member of a class lies in one extremal object, or has isotropic fibres. | That the actual source reaches it. |
| **Rigidity / ceiling** | A set of invariants has one solution or bounds an invariant. | That the solution's zeros are located; a ceiling is not rigidity. |
| **Statistical reduction** | A proportion statement is a bound on a named class of zeros. | Control of any single zero. |
| **Classical reduction** | A mechanism's strongest output is a classical estimate. | That a refinement stays classical. |
| **Directional transfer** | A proved bound implies another under hypotheses. | The converse. |
| **Shared construction problem** | The same missing estimate, sign, counterterm, bound or object. | That one producer yields the others. |
| **Analogy** | A model suggests a mechanism. | Validity for `ζ`. |

## 2. The three families

### U1 — Critical arithmetic cancellation (rate and alignment reading)

**Primary data:** prime or Möbius coefficients. Observables: lag, spline, deficit, Abel moment, history, regularized series, pronic energy, Vaughan Gram, cofactor module and symbol, divisor sums, Lefschetz sequences, one-sided counts, horizon torsion, Farey potential, budgets, escaped Möbius pairings, short prime polynomials at zero ordinates, the prime field at `σ > 1`.

**Missing input:** a signed estimate at every positive slack, at the gauge point `0`; pointwise, a non-alignment law for `γ log p` at zero ordinates inside the strip.

**Proved unifications:**

- The width functor makes the spectral, abscissa, damped Möbius and Liouville, ξ half-plane and Suzuki receivers isomorphic; seven quasi-RH criteria are equivalent pointwise in `θ`.
- First-rung coincidence: every graded gain beyond VK is a fixed strip; dyadic Hecke growth at a fixed rate is a strip.
- **Escape.** Located, exact energy-rate law, classified; RH ⇔ positive gauge mass.
- **Counting forms.** RH ⇔ the one-sided count ⇔ horizon torsion ⇔ the Farey potential at `√N`; `M(N)` is the first Fourier coefficient of the torsion measure.
- **Budgets.** Prime-error budget ⇔ RH; Abel slope at the genus ⇔ RH + simple; Mertens budget ⇒ RH + simple + summable residues; `𝔽_q` slopes count the spectrum.
- **Gauge form.** The Möbius half-power law at `0` is RH, holds a.e., fails at the Liouville twin; charged boundaries at `1/4`; escaped Möbius pairings decay at the VK rate uniformly in the multiplier.
- **Loss law.** Moments, family averages, products and relative powers lose linearly; twists are rate neutral.
- **Alignment.** Exterior: `Σ Λ(n) n^{−σ} cos(γ log n) ≤ Re(Γ-part)′ − m/(σ − β)` at a zero's ordinate for `σ > 1` [L]. Interior [R]: the `σ_γ`-odd detector beyond the horizon, the outward reserve at a terminal and the field threshold are large values of short prime sums at zero ordinates.

**Subfamilies:** width readings (WL, SRT, PBM, MC, JAS, FU, RP, DR); critical energy (PM, CTF with BVI, ACCE, ADR, SAEI, SSA, THIM); budgets (WL, MC); oscillatory payment (`Δ`, `M_f`); alignment (SRT, OWU through Q1).

**Separate currencies:** LI (reciprocal depth), RB (extremal inequality), BAG (local recurrence).

### U2 — Complete signed positivity (sign reading)

**Primary object:** the complete prime–Gamma–polar Weil form, Hecke equivariant; equivalently the spectral side of the explicit formula; equivalently the Rosati trace of the correspondence ring; equivalently the sum over primes of local tower forms paid by the archimedean and polar terms.

- Direct attacks on its sign: RW, SZ, CHMD, OWU, EWU, ACT, AIP, HF, TT.
- Identification with Hodge index, Castelnuovo–Severi on Lefschetz spans, Rosati positivity and symmetric-square spectra: ACS, HF, SRT.
- Sign under other quantifiers: LA, TH, HCF, GTA, XN, PA.

**Proved unifications:**

- RW ⇔ SZ ⇔ CHMD at fixed aperture; HF ceiling ⇒ AIP allocation ⇔ ACS strict-cone RR; one-shift variation, odd capacity and blind minima are parity components.
- Gårding inequality and fewer than `2AT₀K/π` negative directions at aperture `A`.
- Short-window averaged positivity at `Γ^{99/100}`; zero-ordinate positivity; a positive proportion of Weil-positive heights; the census.
- Lefschetz form and local–global split: one or two primes, short cycles, one shift; symmetric-square spectra at one prime; local Hodge index of each prime's tower form; no global ceiling for their sum.
- Correspondence form: RH ⇔ every normalized Hecke graph effective ⇔ budget sufficient ⇔ Rosati positivity.
- **Two forms:** `Re W = D − Δ`; RH ⇔ `W = D` ⇔ `D` Hecke invariant ⇔ `M_f = 0` for every test.
- **Elliptic sectors:** below the conductor horizon twisted positivity holds for every test; the odd sector forces companions; the certificate and the horizon are disjoint at every height.
- **Gauge windows:** positivity of `ζ` separates it from the twins at `181/500` and `23/40`, and from Liouville at every larger aperture.
- Worst twin on nonnegative tests; ground rate = polar rate, = width without clustering.

**Common localization:** at each aperture a finite low-frequency sector (Gårding); in the incidence picture prime-sum edges; across primes the divergence of the sum of local forms along the pole direction; across heights selection below the zero spacing; on Lefschetz spans the Lefschetz part; in correspondence form the sufficiency of the budget; in the two-form picture `M_f`; in the field picture the outward field at terminals.

### U3 — Faithful realization and forcing (carrier, invariant/deformation, counting, renormalization, field and gauge readings)

**Carriers:** geometric (ACS, Meyer surface, AOG, correspondence surface, theta surface, polar surfaces, Serre-dual polar boxes); potential-theoretic (CDG: the `ξ` current; AES: the field, the energy, terminals and lenses; AE/AIT: the characteristic circle and torsion cycles; RBG: regularized germs); operator-theoretic (RN, GTA, PCS, IRK); probabilistic (W1C, FEL); photonic (PTR); categorical (CDC, SC, WBF, RFHM); divisor-diagnostic (HJ, SEC, BSH, APF, EWJ, EGC, PW-B); topological (TG); heat and divisor (WD, ALDG); gauge-geometric (BGG, RBG).

**Proved unifications:**

- **Maximality and isotropy, explained by local type.** Sharp-stable positive ideals lie in the blind ideal; coupled point-stable carriers are isotropic. Both are the boost law.
- **Resonance and elliptic localizers.** Correspondence-closed carriers are elliptic only at resonant scales; `σ_γ` is the unique reflection-compatible affine localizer.
- **Non-localizing positivity** holds for every prime weight.
- **Detectors** read whether a zero is off the line; zero-indexed depth functionals, the field and local detection are computable.
- **Faithful branch:** operator-norm faithful positivity is RH plus simple zeros.
- **Invariant rigidity and the positive cone:** `κ = 1` class `ℝ^× · ζ`; one section decides positivity; independent-ordinate packets dilute.
- **Contraction and collision:** real pairs free; quartets against a real anchor; anchored quartet ⇒ `κ ≥ 3`; Fejér barrier; no analytic global collision.
- **Deformations:** Landau–Wronskian principle; Abel–Gram law; per-ordinate equivalences; conservation; quantization of the surplus residue; ceiling transfer; irreversibility.
- **Counting:** six currencies; node twist destroys RI; theta surface fibre-independent; naive heights are traces; Jacobi–Hurwitz dichotomy; RH ⇔ an asymptotic subquadratic height.
- **Renormalization:** `Λ` is a log-order; torsion energies positive and Hecke similar up to the cutoff; survival law; counterterm rank dichotomy; logarithmic minimal counterterm with divergence at the arithmetic point; nontrivial Hecke cocycle; archimedean germ on the polar hyperplane; pole node; periodic germs; Gauss digamma duality.
- **Field and energy:** `L(Λ ⋆ Λ) = (ζ′/ζ)²`; source field at every zero; virial laws; finite equilibrium ⇔ criticality; energy forms of RH; work exhaustion; Selberg's source `Λ₂ ≥ 0`.
- **Gauge:** blind ⇔ square class; successor couplings charged; cells fix the gauge.
- **Weil's layers:** identities, theorem of the square, budget and involution free; kernel and coupled counts collided; over `𝔽_q` counting proves purity.
- **Successor:** affine positivity induced from dilations; Hecke states positive definite iff `s ≥ 1/2`; Weil's extensions a box over critical zeros; successor defect in `H²`.

**Common missing object:** a pre-divisor source with a **forcing law** placing it in the maximal blind ideal, with input that is computed (not a counting reformulation), uses charged (non-square-class) couplings, is localized by a non-multiplicative operation or polarized, does not scale with amplification, is anchored at no pole or conductor cost, and is positive and equivariant at once — through a coupled renormalization of the two places with a low-rank counterterm and a Hecke-covariant finite part, an inequality for `M_f`, or a bound on the field.

### The forcing currency: where the families meet

| Mechanism | Family of origin | What it forces | Where it stops |
|---|---|---|---|
| Multiplicative positivity (boundary) | U3 | `ζ(1 + it) ≠ 0`; capacity `⌊k/2⌋`; with growth input dlVP, Littlewood, VK | Interior gain only from growth; next rung a fixed strip (U1). |
| Coupled height positivity in completed systems | U3 | `⌊κ/2⌋` collars; `κ = 1` class; `5d < 9κ` | Collar width `1/log T`. |
| Invariant carrier positivity | U2/U3 | Blindness, half-blindness, isotropy | Boost invariance. |
| Non-localizing positivity | U2/U3 | Coercivity at bounded aperture | Every prime weight. |
| Elliptic localization by `σ_γ` | U2/U3 | Twisted positivity below the horizon; companion forcing from one odd-sector sign | Source-blind below the horizon; certificate disjoint from it at every height. |
| Zero-side reserves (field, outward ray, lens) | U3/U1 | A positive field and reserve `≥ c·a·log γ` at each off-line zero's height | Detects; exclusion needs a bound below `√log γ` (Q1). |
| Exterior prime field | U1 | Anti-alignment of `Λ(n) cos(γ log n)` at a zero's ordinate for `σ > 1` | Does not continue into the strip. |
| Positivity on nonnegative tests | U2 | Upper bounds on the source | Shared by dominated twins. |
| Square-class kernels | U1/U3 | Statements true for `Λ` and `λΛ` alike | Gauge blind. |
| Successor couplings; cell dilations | U3 | Gauge fixing at the Euler point | Gauge fixing is not positivity. |
| Linear rigidity | U3 | The coefficient measure is `ζ`'s | Zeros are nonlinear in the measure. |
| Pole order; positive contraction | U3 | Index = pole increment + critical traffic | Pays inserted zeros; `κ ≥ 3`. |
| Positive and rational deformations | U3 | Divisor rigidity off the line; quantized central drop | Rigid exactly at zero-free ordinates; irreversible; detect, do not force. |
| Successor prescription | U2/U3 | Hecke weight; threshold `s ≥ 1/2` | Never reaches atoms. |
| Finite-window certificates | U2 | First twins separated; Liouville permanently | No margin law at growing windows. |
| Correspondence identities | U3 | Normalized graphs; similitude; involution | Hold on the golden datum. |
| Collided positivity (computed) | U1/U3 | Automatic, faithful, log-Sobolev positivity; local detection; `E_f ≍ M_f` | Sees no sign; its equivariance is RH. |
| Torsion energies (renormalized) | U3/U1 | Positivity at `r < 1`; Hecke similitude up to the cutoff | Identity counterterm: survival cone `{0}`. |
| Archimedean germ with pole node | U3 | Positivity on the polar hyperplane; with the node, everywhere | Not the original germ or the full Weil kernel. |
| Local tower forms | U2/U3 | Local Hodge index at each prime | The sum has no ceiling. |
| Electrostatic energy and field | U3/U2 | Quantized energy; exact thresholds | Computed and detected, not bounded. |
| Statistics (averages, proportions, census) | U2 | `3/4` of zeros within `4/log T`; `4/5` of ordinates critical | No individual zero. |
| Counting (sections, effectivity, heights, one-sided counts, base, torsion, Farey, budgets) | U3/U1 | Exact receivers | Each is RH or stronger. |

The invariants run in parallel on the boundary and in the interior:

| Boundary line `Re s = 1` | Interior (degree one) |
|---|---|
| Nonnegative weights (N) | Coefficient positivity (N); `Λ₂ ≥ 0` |
| Integer divisor (Z) | Riemann's FE |
| Simple pole (S) | Simple pole (S) |
| Pole isolation (I) | Strip holomorphy (H) |
| N + Z + S + I ⇒ no boundary zeros; each necessary | N + FE + S + finite order ⇒ `ζ`; dropping S or H admits off-line zeros |
| Pole of order `k` carries `≤ ⌊k/2⌋` boundary zeros; `ζ^d` deformations `2Σ ≤ κ − d` | `≤ ⌊κ/2⌋` collar zeros; `κ = 1` class; anchored quartet ⇒ `κ ≥ 3` |
| dlVP: `3 + 4cos + cos 2 ≥ 0` bounds `ζ′/ζ` from the prime side; at `σ > 1` a zero forces anti-alignment at its ordinate | Outward reserve and field bound `ζ′/ζ` from the zero side; no prime-side bound inside the strip |
| Families: only the two-torsion exception | Positive deformations rigid at zero-free ordinates; surplus residue quantized |

## 3. Every route and candidate

Abbreviations in the last column: *Rate* = graded rate (first rung quasi-RH). *Aperture* = pointwise or averaged window. *Carrier* = carrier, height, heat or order exhaustion. *Escape* = exterior mass at infinite height. *Lefschetz* = the Lefschetz part at one prime. *Gauge* = gauge-charged positivity with a margin. *Alignment* = non-alignment of `γ log p` at zero ordinates. *Inertia* = a bound on `M_f`. *Field* = a bound on the field or energy. *Renorm* = coupled renormalization with a low-rank counterterm and covariant finite part. *Local–global* = archimedean payment of the sum of local prime forms. *Count* = a count that is not a reformulation of the sign. *Budget* = a linear log-energy budget.

### Live routes

| Route | Family | Common receiver or invariant | Distinct missing producer | Partial-progress axis |
|---|---|---|---|---|
| **WL** | U1 | Width via spline, deficit, critical energy; one-sided count; horizon torsion; Farey potential; prime-error budget | Signed lag/energy at every slack; an actual budget | Rate; filtered averages; budget |
| **RW** | U2 | Ground energy `μ`, shell flux, prime ladder; finite negative index | Sign at every aperture; collar estimate | Aperture; Lefschetz |
| **FU** | U1 | Completed Abel moment | Complete history covariance | Rate |
| **RP** | U1 | Matched-quantile history floor | High-LCM and moving-core payment | Rate |
| **PA** | U1/U2 | Prime–archimedean current; Hausdorff moments | Low shifts across unbounded orders | Carrier (order) |
| **MC** | U1 | Mertens; `ν̂_N(1)`; bands ⇔ `Θ < 1`; gauge point `0`; Mertens budget; escaped pairings; Kloosterman packets | Interior anti-alignment; an actual budget; growing-packet compensation | Rate; gauge; budget |
| **TT** | U1/U2 | Directed Wold covariance; odd form | Covariance sign | Aperture |
| **LA** | U2 | Finite-head coefficients; heat | Zero heat on the residual region | Carrier (heat × height) |
| **TG** | U3/U2 | Winding, sub-unit trace | Residual sign, sub-unit bound | Carrier |
| **HF** | U2/U3 | Full cone; index `D_idx`; one-prime tower; symmetric squares; effectivity; `W = D − Δ`; `M_f`; field threshold; divisor energy; torsion intersection | Lefschetz part, `D_idx < 2`, a naive height, a bound on `M_f`, a field bound, or a coupled renormalization | Aperture; Lefschetz; inertia; field; renorm; local–global; count |
| **CHMD** | U2 | Odd bound states; nodal quotient | Nodal / reflected-prime sign | Aperture |
| **TH** | U2 | All-rank heat-Hankel sign | Signed vectors at one time | Carrier (rank) |
| **RN** | U3 | `det₂` resonances | Boundary orientation | Carrier |
| **WD** | U3/U2 | Ward cap; collisions; heated head | Cap vanishing; residual heat region | Carrier |
| **LI** | U1 | Reciprocal-depth clock | Subexponential floor | Rate (separate currency) |
| **SZ** | U2 | First variation = Weil energy | Same sign as RW | Aperture |
| **PM** | U1 | Admission at every damping; cofactor module; Abel atoms; gauge mass; long-modulus quadrature | Signed small-damping energy; positive gauge mass; exterior tightness | Rate (damping); escape |
| **JAS** | U1 | Level-one budget ⇔ strip | Half-power budget | Rate |
| **CTF** | U1/U3 | Báez–Duarte residual | Readout → 1 and energy → 0 together | Rate (damping) |
| **HCF** | U2 | Two literal heat grids | Both grids at all degrees | Carrier (degree) |
| **XN** | U2/U3 | Newton interior margin | Covering discs with margin | Carrier |
| **BAG** | U1/U3 | Strong recurrence ⇔ local nonvanishing | Returns near possible zeros | Carrier |
| **EWU** | U2 | Even blind minimum; finite-level weights; `181/500` floor | Low and mixed modes | Aperture; gauge |
| **GTA** | U2/U3 | Quartic Schur decay | Rank-uniform decay | Carrier (rank) |
| **OWU** | U2 | Odd capacity; first windows separated, Liouville permanently; reserve and exterior law at the same ordinates | Reflected-prime and polar payment; non-archimedean charge with a margin; non-alignment | Aperture; gauge; alignment |
| **PBM** | U1 | Graded regularized abscissa | Convergence to `1/2` | Rate |
| **RB** | U1 | Robin on colossally abundant numbers | Extremal tail | Rate (separate currency) |
| **SRT** | U1/U2 | Lag family; detector = odd sector of `σ_γ`; Lefschetz sequences; exterior prime field; terminal lens | Lag sign; selection; Lefschetz part; non-alignment at zero ordinates | Aperture; selection; alignment |
| **ACT** | U2 | One-shift variation | All-profile reflected collar | Aperture |
| **AIP** | U2 | Shared incidence allocation; polar-neutral collapse; continuum towers; local tower forms; nine-modulus ledger | One shared budget with prime-weighted remainder; archimedean payment of the sum over primes | Aperture; local–global; gauge |
| **ACS** | U2/U3 | Hodge index; RR; blind ideal; counting; contraction, collision, deformations and quantization; two forms; field and energy; renormalization; census | A form positive and equivariant at once; a selective count; the full-class ceiling; a field bound; a coupled renormalization | Carrier; aperture; Lefschetz; gauge; inertia; field; renorm; local–global; count |

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
| **FEL** | U1/U3 | BSY contrast, a depth capacity like `Δ`, `M_f`, `𝓔` | Arithmetic upper bound forcing it to zero |
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

For `σ ≥ 0`, `Δ ≤ σ` is equivalent to each of: graded lag, spline, deficit, band and regularized-series bounds; admission of every damping above `σ`; the ξ half-plane bound; the Suzuki exponent `1 + 2σ`; the JAS budget; balanced, centred-prime and short-window savings; Vaughan empty-leg and tail-rate statements; one test's Lefschetz growth `O(p^{σm})`; all-test one-sided Lefschetz bounds at one or two primes; linear tensor loss `L_k = kσ`; growing-endpoint escaped Möbius pairings at `θ = 1/2 − σ`; section supply beyond the large-sieve diagonal; dyadic Hecke growth `E_f(2^k) = O(e^{(2σ+ε)2^k})` for every test [R]. The receiver energy grows exactly at exponent `max(0, 2Θ − 2ε − 1)`. VK is the strongest unconditional point.

### 4.2 The common Weil form (U2)

| Statement | Relation | Qualification |
|---|---|---|
| Exact form | `Q = (γ₀ − 2)‖F‖² + Lévy + 4·horizon + 2∫incoming·G²` | Every compact `C²` test. |
| Two forms | `Re W = D − Δ`; RH ⇔ `W = D` | Every compact `C²` test for `ζ`. |
| Equivariance | `W(T_L f, T_L g) = W(f, g)`; RH ⇔ `D` equivariant ⇔ `M_f = 0` ∀ `f` | `4L² M_f ≤ E_f(L) ≤ 8(cosh L − 1)M_f`. |
| Gårding; index | `Re W ≥ 2π‖f‖² − K·lowMass`; fewer than `2AT₀K/π` negative directions | Every aperture; index zero is RH. |
| Ground | `μ(A) ≥ 0 ⇔ W_{A′} ≥ 0` for `A′ < A` | RH ⇔ `μ > 0` at every `A`. |
| Prime ladder | RH ⇔ cumulative frozen relaxation `≤ μ(3/10)` | Birth jumps vanish. |
| Finite level | RH ⇔ every aperture admits a positive weight system | No sign premise. |
| Lefschetz | RH ⇔ `\|c_m^{(p)}\| ≤ c_0^{(p)}`; one-sided at one or two primes; short cycles; one shift; symmetric-square spectra | Local part positive for `η ≤ 3/10`. |
| Local–global | `P = Σ_p L_p`, each `L_p` two-sided bounded | No `ℓ²` ceiling for the sum. |
| Normalized graphs | RH ⇔ every normalized Hecke graph effective | Square theorem and budget free. |
| Elliptic sectors | even `+m\|tr\|²`, odd `−m\|tr\|²` | Twisted positivity below the horizon. |
| Forcing half and gap | One odd-sector sign + local count + depth dominance ⇒ companion | Needs `e^{2δa} > 768A log(\|γ\| + 3)`, disjoint from the horizon. |
| Gauge windows | Twins negative at `181/500`, `23/40` and, for Liouville, every larger aperture | Full floor `1/5000` through `181/500`; uncertified at `23/40`. |
| Averaged and statistical | Positive at `A ≤ κ₀ log Γ` on `Γ^{99/100} ≤ H ≤ Γ/8`; positive proportion of heights; census | Frequency average or proportion only. |
| Transfers | RW ⇔ SZ ⇔ CHMD; HF ceiling ⇒ AIP allocation ⇔ ACS strict-cone RR; one ACT shift decides RH | Fixed aperture; directional. |

### 4.3 Geometric and counting currency (U2 ↔ U3)

- **Scaling and correspondence surfaces.** Pairing = pole plane − Weil form; Hodge index, RR plus ample effectivity, and zero sector defect are each RH.
- **Counting.** On every polar surface: section count ⇔ Hodge; effectivity function ⇔ Hodge; a degree-two form is nonnegative iff it has a naive height or a convex height. For `ζ`: each ⇔ RH; the polar box count ⇔ Hodge, its node twist violates RI; large-sieve majorants inflate; Stepanov auxiliaries need a lattice spectrum; an asymptotic subquadratic height ⇔ RH.
- **Over `𝔽_q`.** Effectivity and naive heights hold on hyperelliptic curves; purity by Stepanov and `|τ|² = q`; kernel counts do not supply heights (complex fake).

The Weil sign, ACS RR + Bézout, the Meyer Hodge index, exhaustion of the maximal blind ideal, Castelnuovo–Severi on Lefschetz spans, nonnegative symmetric-square spectra, effectivity of normalized graphs, sufficiency of the budget, Rosati positivity, a section count, an effectivity function, naive and convex heights, a fixed tensor loss, horizon torsion, the Farey potential, the one-sided count, a prime-error budget, the equivariance of `D`, `M_f ≡ 0`, the vanishing of `Δ`, zero transverse energy, every right-zero field `≤ 1`, every unit window below two quanta, positive chirality at every ordinate and the rational and positive central ceilings at every ordinate are the same statement. A coupled renormalization with a low-rank counterterm and a covariant finite part, an alignment law at zero ordinates, a field bound, a bound on `M_f`, a gauge margin law, a selective count and an oscillatory capacity bound would each be a proof of it, or a piece of one.

### 4.4 Ground rate and clustering

`Δ ≤ polarRate = groundRate ≤ 1/2`, with `polarRate = Δ` when off-line copies or depth mass are locally bounded; `RH ⇔ groundRate = 0`; form-norm rates equal `Δ`; depth-profile rates equal twice the deepest seen depth. RW, SRT, ACS, EWU and AIP share this currency.

### 4.5 Depth on the divisor (U3)

The seam charge, the mate gain and the other zero-indexed diagnostics have exact depth laws; the BSY functional, the defect `Δ`, the moment of inertia `M_f` and the transverse energy `𝓔` vanish exactly on critical zeros; the Hecke defect of `D` is `Σ m(2cosh(2δL) − 2)|f̂(ρ)|² ≍ M_f`, computed from `ξ`; two scales determine the depth dispersion; the depth moments solve a Stieltjes problem whose null vectors are the polynomials vanishing on the seen depths. **Diagnostics and capacities read depth, and the corpus computes them; none forces depth to vanish.**

### 4.6 Invariants, capacity, contraction, collision and deformation (U3 selectivity)

- **Rigidity.** N + FE + S + finite order ⇒ `ζ`; `CompletedPositiveSystem 1 d = ℝ^× · ζ`; `ζ^d` deformations rigid without pole budget.
- **Relaxations.** Pole order 2 or 3, strip poles, no FE, no positivity, boundary invariants alone.
- **Capacity.** Boundary `2Σm ≤ k`; collar `2Σ ord ≤ κ`; gauge `2Σm ≤ κ`; family `Σm ≤ k`; line capacity half the real jump; `ζ^d` boundary `2Σ ≤ κ − d`; packets on independent ordinates `Σ|a_j| ≤ a₀`.
- **Positive cone.** One section decides; leading line; line hierarchy; commensurable lines are couplings.
- **Contraction and collision.** Real pairs at `Δκ = 0`; quartets against a real anchor; `κ ≥ 3`; Fejér barrier; no analytic global carrier.
- **Coupled class and deformations.** Not rigid at zero ordinates; per-ordinate equivalences; critical transfer and conservation; central excess ⇒ square-root deficit; surplus residue = even central drop `≤ 2 ord ξ`; ceiling transfers to factors; positive deformations irreversible.

### 4.7 The gauge currency (U1 ↔ U2 ↔ U3)

| Statistic | Gauge behaviour | Consequence |
|---|---|---|
| Moduli, coincidences of products, multiplicative moments, family averages | Invariant | Determine the source up to its orbit. |
| Couplings `(n; a, b)` with `nab` a square (diagonal, ratio, product) | Blind under every real sign gauge | Cannot separate `ζ` from `λ`. |
| Successor couplings `a(a + 1)`; successor connection | Charged; flat iff Euler vacuum on `[1, N + 1]` | Reconstruct `ω(2), ω(3)` on `2 → 3 → 4`. |
| Cell dilations on `[log n, log(n + 1))` | Covariant only at the Euler gauge; reach `2X + 1` | Gauge fixing, not positivity. |
| Catalan forms `w(2)w(4)`, `w(8)w(9)` | Negative at `λΛ`, positive on every real scale twist | Archimedean-free separators. |
| Electrostatic energy and field | Invariant under the archimedean twist | The first charge is invisible to electrostatics. |
| Twisted Selberg source `ωΛ₂` | Nonnegative at a prime iff `ω(p) = 1` (sign gauges) | Coefficient positivity is charged. |
| Escaped boundaries of affine maps | Unsigned at weight `1/2`; charged at weight `1/4` | The Möbius boundary at `0` is RH. |
| Möbius partial sums; torsion Fourier coefficient | Square-root law a.e.; exceptions comeager and null | RH is a property of the point `0`. |
| Windowed moments on the archimedean line | Gauge moment below `2rX^k ≤ 1` | The threshold where the line sees the point. |
| Weil form on prime-free windows; on nonnegative tests | Weight blind; antitone | Positivity holds for every (dominated) twin. |
| Weil form at `181/500`, `23/40`, `2 log 2` | Reads atom `2`, then `2, 3`, then the nine-modulus collar | Twins negative where `ζ` is positive; Liouville permanently. |
| Atoms at `N` primes | Archimedean twists approach the Liouville vacuum at most stretched-exponentially | Second and later charges are not archimedean. |

### 4.8 The local-type currency (U1 ↔ U2 ↔ U3)

| Correspondence | Local type at an off-line pair | On the line | What invariant positivity forces |
|---|---|---|---|
| Hecke `T_p`, archimedean flow, gauge twist | Boost | Rotation | Isotropy |
| Symmetric dilation by `a` | Boost unless `γ log a ∈ πℤ` | Rotation | Fibre zero at a non-resonant scale |
| Symmetric square `(T_p − c)(T_p − c)′` | Non-real or negative spectrum | Nonnegative spectrum | `Re ρ = 1/2` at one prime |
| Sparse correspondence `1 − T_p^N` | Never annihilates | Annihilates on a lattice of heights | Nothing off the line |
| Functional equation; `σ_γ` | Swap | Swap | Even sector: nothing; odd sector: vanishing |
| `σ_γ` with one Hecke operator | Dihedral | — | Blindness |
| Successor | Unipotent | Unipotent | Nothing |
| Affine maps of `ℤ` | Genus zero | — | Nothing beyond weighted counts |

### 4.9 The pairing currency (U1 ↔ U2 ↔ U3)

| Object | Pairing | Positivity |
|---|---|---|
| Determinant (kernel) counts | `ρ ↔ ρ̄` | Automatic without real eigenvalues |
| Coupled counts | `ρ ↔ ρ̄` | Modulus squares for every datum |
| Escape forms | `z_k ↔ z̄_l` (Cauchy/Pick) | Automatic |
| Collided form `D` | `ρ ↔ ρ̄` | Automatic, faithful, log-Sobolev; equivariance ⇔ RH |
| Weil form `W`; Rosati trace | `ρ ↔ 1 − ρ̄` | ⇔ RH |
| Torsion energies `G∘T_r` | Torsion orbits; conjugation = power map `−1`, so collided = reflection | Automatic at `r < 1`; lost in the renormalized limit |
| Field of `Λ ⋆ Λ`; transverse energy | `ρ ↔` all other zeros (Cauchy kernel) | Zero on critical configurations; quantized; outward at terminals |
| Exterior counts over `𝔽_q` | `Λ²` collision | Force unitarity |

### 4.10 The budget currency (U1 ↔ U3)

| Row | `ℤ` | `𝔽_q` |
|---|---|---|
| Prime error | budget ⇔ RH; slope `≥ 2 + γ_E − log 4π`; Abel slope at the genus ⇔ RH + simple | slope `Σ mult(β)²`; `= 2g` iff simple |
| Mertens | budget ⇒ RH + simple + `Σ\|ρζ′(ρ)\|^{−2} ≤ S`; converse needs a residue-growth hypothesis | slope = repulsion energy; genus one strict Hasse |

### 4.11 The renormalization currency (U1 ↔ U3)

| Statement | Content |
|---|---|
| Log-orders | `I(n, m) = log #(𝒪_{ℚ(ζ_n)}/(Φ_m(ζ_n)))`; `Λ(n) = log #(𝒪/(ζ_n − 1))`; `I(m, mt) = φ(m)Λ(t)` |
| Self-intersection | `c(n) = I(n, n)/φ(n) = Σ_{p^a∥n}(a − 1/(p − 1)) log p` (the different); grows by `log p` along the tower of `p` |
| Positive regularization | `T_r(A, B) = gcd(A, B) log(1/(1 − r^{lcm}))` PSD; `T_r(At, Bt) = t T_{r^t}(A, B)` |
| Renormalized limit | prime kernel + log-discriminant = −lim(positive torsion energies − `log(1/(1 − r))` per point) |
| Survival law | limit `≥ 0` exactly on the null cone of the counterterm; scheme independent |
| Rank dichotomy | torsion: identity counterterm, cone `{0}`; archimedean: `𝟙𝟙ᵀ`, cone `Σ c_i = 0`; pole node: cone everything; periodic germs: cone = relations |
| Minimal counterterm | `½ log(N/2) ≤ κ_min(N) ≤ 4 log N + O(1)`; `c(1) ≥ Σ Λ(n)²/(c(n)φ(n))` |
| Anomaly | `β(n, t) = log t − Σ_{p∣t,p∤n} log p/(p − 1)`; not a bounded coboundary; pure degree character on saturated cycles |
| Duality | Gauss's digamma theorem: torsion energy on `μ_N` ↔ lattice germ at `k/N`, anomaly `log N` |
| Rankin–Selberg square | `(ζ′/ζ)² = Σ m²/(s − ρ)² + Σ 2mE(ρ)/(s − ρ)` near the zeros; degree renormalization `m² → m(m − 1)`, `Λ₂ = μ ⋆ log² ≥ 0` |
| Over `𝔽_q` | self-intersection of the diagonal `2 − 2g`, finite |

### 4.12 The electrostatic currency (U2 ↔ U3)

| Quantity of `log\|ξ\|` | Computed by | RH form | Unconditional |
|---|---|---|---|
| Laplacian | `D` from the `ξ` current and theta prefixes | `D` Hecke invariant | positive, log-Sobolev |
| Moment of inertia | `E_f(L) ≍ M_f` | `M_f = 0` ∀ `f` | Stieltjes moments; dyadic amplification |
| Field at the charges | Laurent coefficient of `(ζ′/ζ)²` | right-zero field `≤ 1`, or `< √(2c log γ)` | outward at terminals; virial laws |
| Transverse energy | damped source work of `Λ ⋆ Λ` residues | `𝓔 = 0` ⇔ `𝓔 < 1`; unit windows `< 2` | `𝓔 < ∞` ⇔ finite index; quantized |
| Reflection pairing | explicit formula | `W ≥ 0` | finite negative index |

### 4.13 The alignment currency (U1 ↔ U2)

| Entrance | What an off-line zero forces | Missing exclusion |
|---|---|---|
| `σ_γ`-odd detector beyond the conductor | A sign condition on a prime polynomial of length `(log γ)^{O(1)}` at the zero's ordinate | Non-alignment of `γ log p` (Q1, W9) |
| Outward reserve at a terminal | `Re(ζ′/ζ + Γ-part) ≥ c·a·log γ` on a zero-free ray within `C log γ` | An upper bound for the smoothed prime sum there (Q1, W10) |
| Field threshold | A field `≥ √(2c log γ)` at some right zero | An upper bound of that size |
| Exterior field (`σ > 1`) | `Σ Λ(n) n^{−σ} cos(γ log n) ≤ Re(Γ-part)′ − m/(σ − β)` [L] | Its continuation into the strip |
| Multi-prime repulsion | Bounds alignment with the Liouville vacuum, stretched-exponentially | A bound at the scale the entrances need |
| Collective packets | Independent ordinates buy at most the pole share | Commensurability of companion ordinates |

### 4.14 Currencies that stay separate

| Currency | Exact result | Not identified with |
|---|---|---|
| Li reciprocal depth | Off-line rates `≤ 1/431` | `Δ` |
| Heat constant `Λ₊` | `0 ≤ Λ₊ < 1/8` | `Δ` |
| HF ceiling exponent | `Δ ≤ θ* ≤ Δ/2 + 1/4` | `Δ` |
| Packet vs Weil energy | `m²` vs `m` | Each other without simplicity |
| Distinct-point vs copy energy | `𝓔` vs `𝓔_copy` | Each other without simplicity |
| Trace-bounded vs operator-norm faithful positivity | RH vs RH + simple | Each other |
| Pole order on deformations | Inserted minus removed critical traffic | `Δ` |
| Coalescent surplus; census | `3/4` at `β ≤ 1/18`; `3/4` within `4/log T` | RH |
| Determinant degree; collided form | Conjugate pairing | Rosati degree |
| Conductor horizon | `e^a ≲ log γ/4` | The forcing threshold `(768A log γ)^{1/(2δ)}` |
| Central order of the coupled class | Ceilings ⇔ zero-free ordinates; quantized surplus | Full-class rigidity |
| Mertens budget | RH + simple + summable residues | RH |
| Torsion energy at `r < 1` | Positive | Weil positivity |
| Local tower form at one prime | Two-sided bounded | The global prime form |
| Outward reserve; local detector; exterior field | Detection at each off-line zero | Exclusion |

## 5. Interfaces

| Interface | Proved | Missing |
|---|---|---|
| WL ↔ PA | Exact trace identity | Source sign |
| WL ↔ AE ↔ ACP (counting, budgets) | One-sided count, horizon torsion, Farey potential ⇔ RH; prime-error budget ⇔ RH; Abel–Cramér law; Nair and Stepanov floors | A signed count beyond integrality; an actual budget |
| MC ↔ AE ↔ ACP (Mertens) | `ν̂_N(1) = M(N)`; Mertens budget ⇒ RH + simple; curve repulsion energy | An actual Mertens budget |
| MC ↔ PM ↔ BVI ↔ ACCE | Energy = interior bracket `+ O(1)`; bands ⇔ `Θ < 1`; long-modulus decomposition; VK-rate escaped decay; Kloosterman dispersion | Signed long-modulus quadrature; growing-packet compensation |
| PM ↔ ADR ↔ ACP ↔ ACG ↔ PL | Escape alternative; energy-rate law; Abel atoms; infinite-height laws; escape forms collided; gauge-mass criterion | Exterior tightness (B3.2); positive gauge mass (B1.2) |
| PM ↔ SSA ↔ THIM | Half-damping endpoint bounded; integer local exponents below half | Sub-half signed interior |
| PM ↔ CTF | Residual = readout² + energy | One row family doing both |
| RW ↔ SZ ↔ CHMD | Sign transfer; first variation; domains | Sign |
| RW ↔ SRT ↔ ACS | One rate currency; equality without clustering | `polarRate = Δ` for clustering configurations |
| HF → AIP ↔ ACS | Ceiling ⇒ allocation ⇔ strict RR | The inequality |
| HF ↔ SRT ↔ ACS (Lefschetz) | One or two primes; short cycles; one shift; symmetric squares | The Lefschetz part (B1.3) |
| HF ↔ ACS ↔ AE (counting) | Six currencies; polar box; naive heights are traces; Jacobi–Hurwitz; sparse annihilators | A selective count (B3.23) |
| HF ↔ ACS ↔ PL ↔ CDG ↔ AES (two forms) | `Re W = D − Δ`; RH ⇔ `D` equivariant; `D` computed, log-Sobolev; `E_f ≍ M_f`; local detection; depth laws; dyadic amplification | A bound on `M_f` (B3.21) |
| HF ↔ ACS ↔ AES ↔ ACP (field) | `L(Λ ⋆ Λ) = (ζ′/ζ)²`; source field; virial laws; energy forms; field threshold; terminals, rays and lens; Selberg's source | A field bound (B1.13, B3.17, B3.27) |
| HF ↔ ACS ↔ AE ↔ AIT ↔ RBG (renormalization) | Log-orders; tower forms; survival law; rank dichotomy; logarithmic counterterm; Hecke cocycle; pole node; Gauss digamma duality | Coupled renormalization (B3.25); anomaly cancellation (B3.26) |
| AIP ↔ AIT (local–global) | `P = Σ_p L_p`; local Hodge index; no global ceiling; nine-modulus ledger | Archimedean payment of the sum (B3.25) |
| SRT ↔ OWU ↔ PL ↔ CDG ↔ AES (alignment) | Detector = odd sector of `σ_γ`; conductor horizon; forcing gap; outward reserve; exterior field; smoothed Landau formula; Kronecker dilution | Non-alignment at zero ordinates (B3.24, Q1) |
| OWU ↔ PL ↔ ACP ↔ BGG ↔ SP ↔ RBG (gauge windows) | First charge a twist; twins separated at `181/500`, `23/40`; Liouville permanently; square-class blindness; cells; Catalan separators; multi-prime repulsion | A margin law on growing windows (B3.16, Q3) |
| ACS ↔ MPG ↔ SBWF ↔ U1 | Boundary forced; `⌊κ/2⌋` collar; `κ = 1` class; growth gives dlVP/VK | Better growth input or a non-multiplicative mechanism |
| ACS ↔ ACP ↔ PL ↔ BGG ↔ RBG (one variable, deformations) | Contraction and collision calculus; polar-configuration cone; packets; deformation principle; per-ordinate equivalences; quantization; irreversibility | The full-class ceiling (B3.22) |
| ACS ↔ APD ↔ ACP (carriers) | Isotropy; half-blind and left-blind ideals; boost law; resonance law; Hecke states; visible affine extensions | A non-multiplicative localizer |
| ACG ↔ MC ↔ TTPC ↔ SSA ↔ BGG | Gauge invariance; a.e. laws; charged boundaries at `1/4`; coalescent surplus as gauge charge | A gauge-charged estimate at `0` (B3.15) |
| ACG ↔ AKT ↔ AOG ↔ ACP ↔ PL | Linear loss; total-length law; Künneth collapse; twists rate neutral | Fixed tensor loss (B1.9) |
| AIP ↔ BGG ↔ SP | Polar-neutral collapse; log-cell remainder; continuum towers | Prime-weighted remainder payment (B3.6) |
| AE ↔ RHTower (`𝔽_q`) | Hyperelliptic RH by counting; completion; Burgess; least non-residue | A period at the arithmetic point (B3.19) |
| WL ↔ ACS ↔ TTPC ↔ AES (windows, census) | Filtered deficit → averaged positivity; positive proportion; census; window quantization | Selection below the zero spacing (B1.4); `3/4` (B2.5) |
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
   - a non-alignment law at zero ordinates (odd-sector sign, outward bound, field threshold): SRT, OWU, ACT, ACS, HF;
   - a coupled renormalization of the two places, or archimedean payment of the sum of local prime forms: HF, ACS, AIP;
   - a bound on the moment of inertia or the field: HF, ACS;
   - an actual linear budget: WL, MC.
2. **Finished below RH strength:** reformulation; carrier maximality and isotropy; local-type classification including resonance, `σ_γ`, symmetric squares and sparse annihilators; the forcing gap; invariant completeness; the positive polar-configuration cone and packet dilution; the relative budget and the prime-error budget in both directions; contraction and collision calculus; the deformation principle, per-ordinate equivalences, quantization and irreversibility; successor coupling; escape location and classification; the correspondence layers below the sign; every counting currency; the budget calibrations over `𝔽_q`; the computation and norm of `D` and the moment-of-inertia law; local zero detection; the electrostatic forms of RH, finite equilibrium and quantization; the existence of the outward field and the exterior law; torsion-side renormalization (negative); the archimedean germ on its hyperplane; local Hodge index at each prime and the failure of its sum; the classification of gauge-charged couplings; the census. New equivalent endpoints, invariant carriers, non-localizing carriers, multiplicative certificates, one-variable contractions or couplings, positive or rational deformations, collided positivities, zero-side detectors, counting reformulations, budgets, statistics, square-class kernels, scalar-counterterm renormalizations, local-at-one-prime bounds, statements from multiplicative data alone, and twisted positivity below the horizon add nothing.
3. **The three families reduce to three constructions and one law.**
   - **U1 — positive gauge mass, an actual budget, or a non-alignment law at zero ordinates inside the strip**; non-graded outputs (a non-isolation law, exclusion of deep zeros at non-exceptional ordinates).
   - **U2 — the positivity of `W`**, or its gauge-charged and elliptic approximations: separating windows with a margin law, the odd-sector sign beyond the conductor, archimedean payment of the sum over primes.
   - **U3 — a form positive and equivariant at once, or a field bound**: a coupled renormalization of the two places with low-rank counterterm and covariant finite part, an inequality for `M_f`, with charged input and a non-multiplicative localizer.
   - **The common law:** arithmetic forces the zero spectrum to be elliptic — complex conjugation and the functional-equation reflection agree on the zeros. It appears as rate zero in U1, as positivity of `W` in U2, as equivariance of `D` (`M_f = 0`) or exhaustion of the blind ideal in U3, as `Δ = 0`, as zero transverse energy, as typicality of the gauge point `0`, as the absence of outward fields, and as the absence of zeros at every ordinate in the deformation reading. On torsion cycles conjugation is already algebraic (the power map `−1`); the law asks for the same on the zeros.
4. **Where the families meet.**
   - **U1 and U2** meet at the square-root threshold, at selection, at the Lefschetz sequence, at the one-sided count, and at zero ordinates (the detector's polynomial, the reserve, the field threshold, the exterior law).
   - **U2 and U3** meet at one inequality, `Δ ≤ D` with equality: the Weil sign, the Hodge index, effectivity, naive heights, budget sufficiency, `M_f = 0`, zero energy, the per-ordinate ceilings, the absence of outward fields; and at the local–global passage, where local Hodge index holds and the sum must be paid.
   - **U1 and U3** meet at the cofactor module, at multiplicative forcing, at the base, at the counting and budget currencies, at the torsion measure and its renormalization, at the field (computed by `Λ ⋆ Λ`, bounded by a prime sum), and at the gauge point (square class versus charged).
5. **Partial progress is family-specific.**
   - U1's rate axis is blocked at quasi-RH; its non-graded outputs (escape classification, Abel atoms, budget equivalences, the exterior law) classify or detect without excluding.
   - U2 has aperture windows, the local part on short cycles and at each prime, the finite negative index, short-window averages, positive proportions and the census, twisted positivity below the horizon, the forcing half and permanent separation from the Liouville twin.
   - U3 has blind, half-blind and isotropic sub-carriers, non-localizing positivity, boundary forcing, collars, the `κ = 1` class, the closed contraction, collision and deformation calculus, a computed positive form `D` with its moment-of-inertia law, a computed and quantized electrostatics, torsion energies positive before renormalization, the archimedean germ on its hyperplane with the pole node, the classification of charged couplings, and the exact counting currencies.

   A result that converts one family's partial progress into another's would itself be a new mechanism: a non-alignment law (U1) from moments over zero ordinates that turns the field threshold (U3) into an exclusion; a coupled renormalization (U3) whose survival cone contains Weil test vectors (U2); a gauge margin (U2) carried by cell or successor couplings (U3).
6. **Eleven obstructions are common to every amplification, multiplicative argument, invariant carrier, one-variable positive object, deformation, count, renormalized limit, local bound, detector and statistic.** Depth homogeneity; gauge invariance (square class); hyperbolicity (resonance its only exception); Landau–Fejér positivity and dilution; deformation rigidity and irreversibility; the counting law; the survival law (scalar counterterms keep nothing); the local–global law (local bounds do not sum); the detection law (zero-side objects see each zero and bound nothing); the exterior law (the anti-alignment proved at `σ > 1` does not continue); and the statistics law (proportions exclude no zero; only quantized ones would). Collided positivity escapes the first seven and sees nothing; Rosati positivity sees everything and is RH; torsion energies, the archimedean germ and the field come closest — positive and Hecke similar except at the diagonal, positive on a hyperplane, or computed and quantized except where a bound is needed. Over `𝔽_q` a polarization of `C × C` makes positivity and equivariance one, with a finite diagonal self-intersection; over `ℤ` none is known. The [summary](obstacles-summary.md#4-would-the-b-tier-obstacles-require-a-new-field-of-mathematics) describes what a structure making them one must satisfy.
