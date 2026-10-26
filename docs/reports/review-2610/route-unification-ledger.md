# Route-unification ledger

**Status 2026-10-26, corpus `e889b7985` with the working tree of that day.** The 31 live routes, 17 candidates and PW-B are faces of three construction problems:

- **U1 — critical arithmetic cancellation**: the *rate* reading of blindness.
- **U2 — complete signed positivity**: the *sign* reading of blindness.
- **U3 — faithful realization and forcing**: the *carrier* reading of blindness, with an *invariant* sub-reading.

All three ask one question in different currencies: **what forces the actual arithmetic source to be blind to off-line zeros?** The corpus proves the readings equivalent at their endpoints:

- **U1.** A generic orbit's growth rate equals the depth of the deepest zero it sees; one test's Lefschetz sequence at one prime grows exactly like `p^{Δm}`.
- **U2.** Orbit Hodge positivity holds iff the orbit is blind; Weil positivity is positivity of the spectral side of the explicit formula; on two-element spans `{g, T_{p^m} g}` it is Weil's Castelnuovo–Severi inequality `|c_m| ≤ c_0`.
- **U3.** The maximal sharp-stable positive Meyer ideal is the off-line-blind ideal and equals the whole source iff RH. The degree-one invariants determine ζ. Pole order accounts exactly for inserted zeros.

**A reading that cuts across the families: the gauge point.** Multiplicative data determine a source up to its orbit under the gauge torus `(ℝ/ℤ)^{primes}`. In U1 the actual source is the gauge point `0` of an orbit on which the Möbius half-power law holds almost surely and fails at the Liouville twin. In U2 the sign is carried by the archimedean place, which is gauge charged. In U3 every carrier and certificate built from multiplicative data is gauge invariant and cannot single out the source. The three construction problems are therefore three ways of breaking the gauge symmetry at the point `0`.

The invariant sub-reading of U3 is settled: pole order is a complete invariant for relative deformations and silent about ζ's own zeros; their payment is oscillation of the zero sum, a rate. **The budget question of U3 is a U1 question.** Identical receivers still do not mean identical producers: each family keeps its own missing construction.

Companions: [complete report](hard-obstacles.md), [summary](hard-obstacles-summary.md), [walls ledger](walls-ledger.md). Evidence: corpus search and Lean statement reading (`logs/review-2610/working-log.md`). `[S]`, `[R]` as in the walls ledger.

## 1. Levels of unification

| Level | What it justifies | What it does not |
|---|---|---|
| **Exact identity** | Two expressions are equal on a stated source and normalization. | Extension to another completion or norm. |
| **Receiver isomorphism** | Same threshold at every rate `σ` (width functor). | Equal finite tests, rates or difficulty. |
| **First-rung coincidence** | The weakest nontrivial conclusions coincide; for every U1 receiver, for one-sided Lefschetz bounds at two primes and for multiplicative forcing this is quasi-RH. | Equality of later rungs or of producers. |
| **Gauge equivalence** | Two sources with the same multiplicative data differ by a gauge twist; every gauge-invariant statement transfers along the orbit. | Any statement at a chosen point of the orbit. |
| **Maximality / isotropy** | Every member of a class lies in one extremal object, or has isotropic off-line fibres. | That the actual source reaches it. |
| **Rigidity** | A set of invariants has exactly one solution. | That the solution's zeros are located. |
| **Conservation** | An exact balance between two invariants on a whole deformation class. | An absolute bound for the base point of the class. |
| **Directional transfer** | A proved bound implies another under hypotheses. | The converse. |
| **Shared construction problem** | The same missing estimate, sign or object. | That one producer yields the others. |
| **Analogy** | A model suggests a mechanism. | Validity for ζ. |

## 2. The three families

### U1 — Critical arithmetic cancellation (rate reading)

**Primary data:** prime or Möbius coefficients. Observables: lag, spline, deficit, Abel moment, history, regularized series, probe, pronic energy, Vaughan Gram, cofactor module, divisor sums, Lefschetz sequences, and the oscillatory payment of ζ's own zeros.

**Missing input:** a signed estimate at every positive slack, at the gauge point `0`.

**Proved unifications:**

- The width functor makes the spectral, abscissa, damped Möbius and Liouville, ξ half-plane and Suzuki formation receivers isomorphic.
- **First-rung coincidence.** The first gain beyond Vinogradov–Korobov of each graded receiver is a fixed strip, including every Vaughan power improvement, admission at fixed damping and one-sided Lefschetz bounds at two primes [S].
- **Vaughan phase transition at half damping.** Admission at and above `ε = 1/2`; below, leading order classified and every power gain a strip.
- **Escape structure.** Record-minimum limits; singleton-or-continuum; contraction calculus; eigencharacter moduli. On finite exponent windows the escape eigenstates are exactly the translated zeros `ρ − ε` with multiplicity: U1's escape alternative is a rate statement on every finite window.
- **Gauge form.** The Möbius half-power law at the gauge point `0` is RH; it holds at Haar-almost every twist and fails at the Liouville twin [S].
- **Loss law.** Moments, tensor products and relative powers lose at least linearly; a rate needs `b_k = o(k)`.

**Subfamilies:**

- **Width readings:** WL, SRT, PBM, MC, JAS, FU, RP, DR.
- **Critical energy:** PM, CTF, with the BVI, ACCE, ADR, SAEI, SSA and THIM machinery.
- **Oscillatory payment:** the residue of the U3 budget reading.

**Separate currencies:** LI (reciprocal depth) and RB (extremal inequality); BAG through local recurrence. U1's non-graded handles are frequency averaging and the escape alternative, now reduced to escape completeness (Q1).

### U2 — Complete signed positivity (sign reading)

**Primary object:** the complete prime–Gamma–polar Weil form, equivalently the spectral side of the explicit formula as a Poisson pair.

- **Direct attacks on its sign:** RW, SZ, CHMD, OWU, EWU, ACT, AIP, HF, TT.
- **Identification with Hodge index and with Castelnuovo–Severi on Lefschetz spans:** ACS, HF, SRT.
- **Sign under other quantifiers:** LA, TH, HCF, GTA, XN, PA (degree, rank, heat time, order).

**Proved unifications:**

- Fixed-aperture sign transfer RW ⇔ SZ ⇔ CHMD; Suzuki first variation = Weil energy.
- HF ceiling ⇒ AIP allocation ⇔ ACS strict-cone RR.
- One-shift variation, odd capacity and blind minima are parity components of the form.
- Weil margin ⇒ heat-Hankel positivity in a coupled rank–time window.
- **Short-window averaged positivity** at logarithmic aperture on every window `Γ^{99/100} ≤ H ≤ Γ/8` for the whole family, through the exact all-parity identity.
- **The off-line field** reads the negative part of every member of the family at every height: `Q_γ ≥ −4(A+1)²e^A N² Φ(γ)`; nonnegative tests are positive at almost every zero ordinate.
- **Finite-level existence.** RH ⇔ some weight system is positive at every finite aperture.
- **Bochner form.** RH ⇔ every scale function is the characteristic function of a positive measure; for the two-prime spline orbit, ⇔ a positive measure on `T²`.
- **Lefschetz form.** RH ⇔ `|W(T_{p^m} g, g)| ≤ W(g, g)` for all `m`, for one test at one prime; ⇔ the one-sided inequalities at two primes [S].
- Ground rate = polar rate.

**Common localization:** at each aperture the obstruction is a finite low-frequency sector; in the incidence picture frustration comes only from prime-sum edges; across heights it is selection below the zero spacing; on Lefschetz spans it is a budget.

### U3 — Faithful realization and forcing (carrier and invariant readings)

**Carriers:**

- geometric: ACS effectivity, the Meyer surface, AOG orbits and families, correspondences on the scaling surface;
- operator-theoretic: RN, GTA, PCS, IRK;
- probabilistic: W1C, FEL;
- photonic: PTR;
- categorical: CDC, SC, WBF, RFHM;
- divisor-diagnostic: HJ, SEC, BSH, APF, EWJ, EGC, PW-B;
- topological: TG;
- heat and divisor: WD cap, ALDG.

**Proved unifications:**

- **Maximality and isotropy.** Every sharp-stable positive convolution ideal lies in the blind ideal; positive ideals without sharp stability are half-blind; coupled point-stable carriers have isotropic off-line fibres. Single-channel and point-stable positive carriers differ only in how much of the blind or isotropic class they see.
- **Synthesis.** The blind ideal is the closure of critical jets and the Poisson boundary exactly when off-line zeros are simple, and always of all allowed jets plus the boundary.
- **Detectors.** The HJ residual, SEC seam, CDC confluence, BSH mate gain, IRK noninvertibility and W1C Clifford energy all read `Re ρ = 1/2` with exact depth laws.
- **Faithful branch.** Operator-norm faithful positivity is RH plus simple zeros.
- **Invariant rigidity.** Coefficient positivity, the FE, the simple pole and finite order determine ζ, stably in an `L¹` FE defect. Every relaxation breaks this.
- **Pole capacity.** Boundary: `⌊k/2⌋` per pole of order `k`. Completed systems: `2Σ ord ≤ κ` on finite-height collars of width `≍ 1/(d log T)`, no separation; κ = 1 collar zero-free; `5d < 9κ`. Relative deformations: conservation identity; pole order one rigid; pole order two admits every off-line type.
- **Successor.** Affine positivity is induced from the dilations; prescribed arithmetic successors force Kronecker-null dilation spectra; Weil's atomic spectrum carries no successor.
- **Products and correspondences.** Künneth, Adams and symmetric-power count positivity is point-count positivity; the Hecke graphs of `ℤ` satisfy no theorem of the square.

**Common missing object:** a pre-divisor source with a **forcing law** that places it in the maximal blind ideal, with gauge-charged input outside every mapped class and a term that does not scale with amplification. Where it would act: ACS effectivity; a correspondence ring with a theorem of the square and a section count; the HJ/SEC weld; the TG sub-unit residual; the RN boundary orientation.

### The forcing currency: where the families meet

Seven mechanisms are mapped. Each sits between families and stops at a computed boundary.

| Mechanism | Family of origin | What it forces | Where it stops |
|---|---|---|---|
| Multiplicative positivity (boundary divisor positive definite) | U3 | `ζ(1+it) ≠ 0`; capacity `⌊k/2⌋`; with growth input the dlVP, Littlewood and VK regions | Interior gain only from growth input; no quantized inequality at the critical line; next rung a fixed strip (U1). |
| Coupled height positivity in completed systems | U3 | `2Σ ord ≤ κ` on finite-height collars; κ = 1 collar zero-free; `5d < 9κ` | Collar width `1/log T`; no interior rate (U1). |
| Carrier positivity (single-channel, coupled point-stable) | U2/U3 | Blindness, half-blindness, isotropy of off-line fibres | Never vanishing; exhaustion is RH. |
| Linear rigidity (Fejér-tent squeeze on the theta law) | U3 | The coefficient measure is ζ's, stably | Zeros are nonlinear in the measure. |
| Pole order on relative deformations | U3 | Index increment = pole increment `+ R_crit − I_crit`; `κ = 1` rigid | Pays inserted zeros only; ζ's own zeros are a rate (U1). |
| Successor prescription on `Aff(ℚ)` | U2/U3 | Hecke weight `(nd)^{−1/2}`; positivity threshold `s ≥ 1/2`; Kronecker-null spectrum | Mutually singular with archimedean (Weil) dilation spectra. |
| Multiplicative (gauge-invariant) data | U1/U3 | Statements true on the whole gauge orbit, e.g. the a.e. square-root law | The gauge point `0`: the Liouville twin shares all its multiplicative data. |

Their invariants run in parallel. Rows pair invariants with the same role where one exists.

| Boundary line `Re s = 1` | Interior (degree one) |
|---|---|
| Nonnegative weights (N) | Coefficient positivity on `[1, ∞)` (N) |
| Integer divisor (Z) | Riemann's functional equation (FE) |
| Simple pole (S) | Simple pole (S) |
| Pole isolation (I) | Holomorphy of the completion in the strip (H) |
| N + Z + S + I ⇒ no boundary zeros; each necessary | N + FE + S + finite order ⇒ the system is ζ; dropping S or H admits off-line zeros |
| A pole of order `k` carries `≤ ⌊k/2⌋` boundary zeros, every placement realized | Completed systems: `≤ ⌊κ/2⌋` collar zeros at finite height; relative deformations: conservation identity, `κ = 1` rigid, `κ = 2` admits every off-line type |
| Family over a finite group: only the two-torsion exception | Real axis: no real zeros at `κ = 1`; the Siegel datum keeps all boundary invariants |

On the boundary the invariants force the conclusion and compute the capacity. In the interior they force the identity of the source, the collar capacity and the exact accounting of inserted zeros; the zero conclusion for ζ itself is not a capacity statement.

## 3. Every route and candidate

Abbreviations in the last column: *Rate* = graded rate `σ` (first rung quasi-RH). *Aperture* = pointwise aperture or averaged window. *Carrier* = carrier, height, heat or order exhaustion. *Escape* = cofactor escape completeness. *Budget* = Lefschetz spans at one prime.

### Live routes

| Route | Family | Common receiver or invariant | Distinct missing producer | Partial-progress axis |
|---|---|---|---|---|
| **WL** | U1 | Width via spline, deficit, critical energy | Signed lag/energy at every slack | Rate; filtered averages |
| **RW** | U2 | Ground energy `μ`, shell flux, prime ladder | Sign at every aperture; collar estimate | Aperture; short windows |
| **FU** | U1 | Completed Abel moment | Complete history covariance | Rate |
| **RP** | U1 | Matched-quantile history floor | High-LCM and moving-core payment | Rate |
| **PA** | U1/U2 | Prime–archimedean current; Hausdorff moments | Low shifts across unbounded orders | Carrier (order) |
| **MC** | U1 | Mertens; `θ(ε,t)` gap; bands ⇔ `Θ<1`; gauge point `0` | Interior anti-alignment | Rate |
| **TT** | U1/U2 | Directed Wold covariance; odd form | Covariance sign | Aperture |
| **LA** | U2 | Finite-head coefficients; heat; Jensen | Zero heat on the residual region | Carrier (heat × height) |
| **TG** | U3/U2 | Winding, sub-unit trace | Residual sign, sub-unit bound | Carrier |
| **HF** | U2/U3 | Full cone `{Λ}`; ceiling; index `D`; one-prime tower; two-prime Bochner receiver | `O(L)` ceiling, `D < 2`, or a Lefschetz budget | Aperture; budget |
| **CHMD** | U2 | Odd bound states; nodal quotient | Nodal / reflected-prime sign | Aperture |
| **TH** | U2 | All-rank heat-Hankel sign | Signed vectors at one time | Carrier (rank) |
| **RN** | U3 | `det₂` resonances | Boundary orientation | Carrier |
| **WD** | U3/U2 | Ward cap; collisions; heated head | Cap vanishing; residual heat region | Carrier (heat × height) |
| **LI** | U1 | Reciprocal-depth clock | Subexponential floor | Rate (separate currency) |
| **SZ** | U2 | First variation = Weil energy | Same sign as RW | Aperture |
| **PM** | U1 | Admission; Vaughan Gram; cofactor module; translated-zero eigenstates | Signed small-damping energy; escape completeness | Rate (damping); escape |
| **JAS** | U1 | Level-one budget ⇔ strip | Half-power budget | Rate |
| **CTF** | U1/U3 | Báez–Duarte residual | Readout → 1 and energy → 0 together | Rate (damping) |
| **HCF** | U2 | Two literal heat grids | Both grids at all degrees | Carrier (degree) |
| **XN** | U2/U3 | Newton interior margin | Covering discs with margin | Carrier |
| **BAG** | U1/U3 | Strong recurrence ⇔ local nonvanishing | Returns near possible zeros | Carrier |
| **EWU** | U2 | Even blind minimum; finite-level weights | Low and mixed modes | Aperture |
| **GTA** | U2/U3 | Quartic Schur decay | Rank-uniform decay | Carrier (rank) |
| **OWU** | U2 | Odd capacity | Reflected-prime and polar payment | Aperture |
| **PBM** | U1 | Graded regularized abscissa | Convergence to `1/2` | Rate |
| **RB** | U1 | Robin on colossally abundant numbers | Extremal tail | Rate (separate currency) |
| **SRT** | U1/U2 | One-parameter lag family; detector; one-prime Lefschetz sequence | Lag sign; selection; Lefschetz budget | Aperture; selection; budget |
| **ACT** | U2 | One-shift variation | All-profile reflected collar | Aperture |
| **AIP** | U2 | Shared incidence allocation | One shared budget | Aperture |
| **ACS** | U2/U3 | Hodge index; RR; maximal blind ideal; isotropy; multiplicative forcing; rigidity; pole and collar capacity; Lefschetz spans | Forcing input outside the mapped classes; a correspondence ring with a budget | Carrier; aperture; budget |

### Candidates and PW-B

All are U3 unless noted. Each lacks the forcing law of §2. Single-channel positivity cannot supply it, coupled point-stable positivity gives only isotropy, coupled height positivity reaches only the boundary and the collar, every candidate must separate ζ from the relaxation models at pole order two, and a candidate fed only by multiplicative data cannot separate ζ from its gauge twins.

| Candidate | Family | Common face | Missing construction |
|---|---|---|---|
| **APF** | U3 | Cycle-trace reconstruction | Annihilation of the off-line component |
| **BSH** | U3 | Mate curvature | Pre-divisor section |
| **CDC** | U3 | Calibrated confluence | Descending source potential |
| **DR** | U1/U3 | Dyadic roots; PBM abscissa | Global monodromy |
| **EGC** | U1/U3 | Enclosed-pole cancellation | Exterior contour sign |
| **EWJ** | U3 | Finite jets | Norm exhaustion |
| **FEL** | U1/U3 | BSY contrast: nonnegative, zero on critical zeros | Arithmetic upper bound forcing it to zero |
| **HJ** | U3/U2 | Residual = SEC charge = HCF grids | Stabilization weld |
| **IRK** | U3 | Completed relation | Arithmetic lift |
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

For `σ ≥ 0`, `Δ ≤ σ` is equivalent to each of: graded lag, spline, deficit-primitive, band and regularized-series bounds; admission of every damping above `σ`; the ξ half-plane bound; the Suzuki formation exponent `1+2σ`; the JAS budget; balanced, centred-prime and short-window savings (for `σ < 1/2`); the Vaughan empty-leg and tail-rate statements; one test's Lefschetz growth `c_m^{(p)} = O(p^{σm})` at every prime; all-test one-sided Lefschetz bounds at two primes [S]. VK is the strongest unconditional point. Sources include `TheWidthFunctor`, `balancedStatisticPowerSaving_iff`, `centredPrimeBandPowerSaving_iff`, `xiZeroHalfPlaneBound_iff_logZetaRegCoeff_converges`, `TheVaughanEmptyLegReadsTheZeroAbscissa`, `zeta_exists_universal_lefschetz_growth`, `zeta_width_le_iff_oneSided`.

### 4.2 The common Weil form (U2)

| Statement | Relation | Qualification |
|---|---|---|
| Exact form | `Q = (γ₀−2)‖F‖² + Lévy + 4·horizon + 2∫incoming·G²` | Every compact `C²` test. |
| Ground | `μ(A) ≥ 0 ⇔ W_{A′} ≥ 0` for `A′ < A`; flow strictly decreasing | RH ⇔ `μ > 0` at every `A`. |
| Prime ladder | RH ⇔ cumulative frozen relaxation `≤ μ(3/10)` | Birth jumps vanish. |
| Finite level | RH ⇔ every aperture admits a positive weight system | No sign or growth premise. |
| Bochner | RH ⇔ positive spectral measures for every `C²` test | The prime measure is positive unconditionally. |
| Lefschetz | RH ⇔ `|c_m^{(p)}| ≤ c_0^{(p)}` for one test, one prime | Two primes: one-sided suffices [S]. |
| Suzuki | First variation = Weil energy | Compact `L²`; RH-complete tents. |
| CHMD | Completion = supported maximal graph | Fixed aperture. |
| AIP ↔ ACS | Allocation ⇔ strict-cone RR | All apertures ⇔ RH. |
| HF → AIP | Ceiling ⇒ allocation | Directional. |
| ACT | One fixed shift decides RH | All even profiles. |
| RW → TH/HCF | `μ₀(A) > 0`, `K < A²/4` ⇒ heat-Hankel positivity | Rank and time coupled. |
| Graded | `Δ ≤ σ` ⇔ `H¹` floors at every rate `> σ` | Endpoint attained. |
| Averaged | Positive at `A ≤ κ₀ log Γ` on every window `Γ^{99/100} ≤ H ≤ Γ/8` | Frequency average only. |
| Pointwise floor | `Q_γ ≥ −4(A+1)²e^A N² Φ(γ)`; nonnegative tests positive at almost every zero ordinate | Signed tests: floor only. |
| Blindness | Scale-shift-invariant positive spaces are blind | No producer. |

### 4.3 Geometric currency (U2 ↔ U3)

- **Scaling surface.** Pairing = pole plane − Weil form. Hodge index, RR plus ample effectivity, and zero sector defect are each equivalent to RH. Adjoining two polar fibres of budget `κ` to a local pairing `L` gives Hodge index ⇔ `L(x,x) ≤ 2κ ℓ_H(x)ℓ_V(x)`.
- **Meyer surface.** Trace RR unconditional; Bézout ⇔ ampleness ⇔ RH; numerical = principal ⇔ simple zeros.
- **Maximal blind ideal.** All axioms hold; greatest sharp-stable positive ideal; synthesized by jets and the Poisson boundary; equals the source ⇔ RH.
- **Lefschetz spans.** The two-element windows `{g, T_{p^m} g}` are Weil's spans `⟨Δ, Γ_m⟩`; Castelnuovo–Severi on them for all `m` is RH.
- **Function-field calibration.** Rosati cones have Bézout without unitarity; genus-one Hodge index ⇔ degree positivity of `ℤ[F]`; curve purity ⇔ positive definiteness of the trace sequence on `ℤ`; a fixed budget forces purity; Künneth positivity is point-count positivity; the Hecke graphs of `ℤ` have no theorem of the square.

The Weil sign, ACS RR + Bézout, the Meyer Hodge index, exhaustion of the maximal blind ideal, positivity of the spectral measure, the Castelnuovo–Severi inequality on Lefschetz spans and the Lefschetz–Hasse–Weil bound are the same statement. An analytic payment of the low sector, a geometric forcing law with a budget and an oscillatory capacity for ζ's own zeros would be three proofs of it.

### 4.4 Ground rate and clustering

`Δ ≤ polarRate = groundRate ≤ 1/2`, `RH ⇔ groundRate = 0`; form-norm rates equal `Δ`. RW, SRT, ACS, EWU and AIP share this currency.

### 4.5 Depth on the divisor (U3)

The first-prime seam charge `√2·log 2·sinh(δ log 2)`, the mate gain `2δ log n` and the other zero-indexed diagnostics have exact depth laws with supremum `Δ`. Positive Hermitian Meyer degrees see critical values only. The BSY functional is nonnegative and vanishes exactly on critical zeros. The off-line field `Φ` vanishes exactly under RH. **Diagnostics read depth; none forces it to vanish.**

### 4.6 Invariants and capacity (U3 selectivity)

- **Rigidity.** N + FE + S + finite order ⇒ ζ; discrete Beurling systems ⇒ rational primes; `L¹` FE defects give off-lattice and tent-mass bounds.
- **Relaxations.** Pole order 2 ⇒ real pair, or complex quartet with one critical refund, both completed positive systems; pole order 3 ⇒ quartet; strip poles ⇒ quartet; no FE ⇒ over-regular zeros; no positivity ⇒ non-uniqueness; boundary invariants alone ⇒ the Siegel datum.
- **Capacity.** One number throughout: boundary `2Σm ≤ k`; finite-height collar `2Σ ord ≤ κ`; gauge `2Σm ≤ κ`; family `Σm ≤ k` with self-conjugate points counted once. Relative interior: index increment = pole increment `+ R_crit − I_crit`; `κ = 1` rigid; `5d < 9κ`.

Every forcing proposal is tested here (summary W1): it must use all invariants, fail on the pole-order-2 models, and see more than pole order.

### 4.7 The gauge currency (U1 ↔ U3)

| Statistic | Gauge behaviour | Consequence |
|---|---|---|
| Moduli, coincidences of products, multiplicative moments | Invariant | Determine the source up to its orbit; cannot select the point `0`. |
| Successor, affine and near-incidence correlations | Charged: mean zero, diagonal variance | A bound must be proved at the point `0`. |
| Möbius partial sums | Square-root law a.e.; fails at the Liouville twin | RH is a property of the point `0`. |
| Coalescent prime-pair surplus (TTPC) | Charged; meets every budget a.e. | `β` is a property of the point `0`. |
| Windowed moments on the archimedean line | Gauge moment below `2rX^k ≤ 1`; near-incidence beyond | The threshold is where the line starts to see the point. |
| Möbius boundary of affine maps | Separates `μ` from its twin (PNT) | The boundary of finite presentations is gauge charged. |

### 4.8 Currencies that stay separate

| Currency | Exact result | Not identified with |
|---|---|---|
| Li reciprocal depth | Rate law; off-line rates `≤ 1/431`; `β < 1/300` | `Δ` |
| Heat constant `Λ₊` | `0 ≤ Λ₊ < 1/8`; `Λ₊ = 0 ⇔ RH`; `Λ₊ ≤ Δ²/2` | `Δ` |
| HF ceiling exponent | `Δ ≤ θ* ≤ Δ/2 + 1/4` | `Δ` |
| Packet vs Weil energy | `m²` vs `m` | Each other without simplicity |
| Trace-bounded vs operator-norm faithful positivity | RH vs RH + simple | Each other |
| Pole order on deformations | Inserted minus removed critical traffic, exactly | `ind₋(W_ζ)`, `Δ` |
| Quantum budget | `b(η) = (√A + √(Gη))²/B`; `b(½) ≥ 1` once `L ≥ 0.17` | A zero count at the critical line |
| Coalescent surplus | `3/4` proportion at `β ≤ 1/18` | RH |
| Hecke exponent of the integer successor | Positivity iff `s ≥ 1/2`; Haar-singular at `s ≤ 1/2` | The zero width of ζ |

## 5. Interfaces

| Interface | Proved | Missing |
|---|---|---|
| WL ↔ PA | Exact trace identity | Source sign |
| MC ↔ PM ↔ BVI | Energy = interior bracket `+ O(1)`; Möbius ≅ Liouville; bands ⇔ `Θ<1`; Vaughan transition | Arithmetic contraction of the residual |
| PM ↔ ADR ↔ AOT | Admission ⇔ faithful infinite module; escape ⇒ paid ideal ⊆ annihilator; record minima; contraction calculus; eigencharacter moduli; visible-pole index; ζ/η symbols; translated-zero eigenstates on finite windows | Escape completeness (Q1) |
| PM ↔ SSA ↔ THIM | Half-damping endpoint bounded for all squarefree `P`; integer local exponents below half | Sub-half signed interior |
| PM ↔ CTF | Residual = readout² + energy | One row family doing both |
| RW ↔ SZ ↔ CHMD | Sign transfer; first variation; domains | Sign |
| RW ↔ SRT ↔ ACS | One rate currency; cluster dichotomy | `polarRate = Δ` |
| HF → AIP ↔ ACS | Ceiling ⇒ allocation ⇔ strict RR | The inequality |
| HF ↔ SRT ↔ ACS (Lefschetz) | One test, one prime: growth `p^{Δm}`; ratios recover zeros; one-sided at two primes [S] | A budget for `c_m` (B1.9) |
| HF ↔ APD | Two-prime orbit ⇔ Bochner problem on `T²`; affine positivity induced; successors see only the Kronecker-null part | Construction of the torus measure; archimedean–null coupling (B3.23) |
| ACS ↔ Meyer ↔ curves | Meyer Hodge ⇔ RH; maximal blind ideal, topology, synthesis; Rosati and genus-one calibration | Forcing input; exhaustion |
| ACS ↔ APD (carriers) | Isotropy on point-stable carriers; half-blind and left-blind ideals | Non-point-stable carriers (Q2) |
| ACS ↔ MPG ↔ SBWF ↔ U1 | Boundary forced with capacity `⌊k/2⌋`; finite-height `⌊κ/2⌋` collar; κ = 1 collar zero-free; growth gives dlVP/VK; certificates capped | Better growth input or a non-multiplicative mechanism |
| ACS/HF ↔ APD ↔ RHTower deformations | Positive-measure rigidity and stability; relaxation models; conservation identity; `κ = 1` rigidity; `5d < 9κ` | — (budget reading closed; ζ's own zeros are U1) |
| ACG ↔ MC ↔ TTPC ↔ SSA | Gauge invariance; a.e. square-root law; Liouville twin; surplus and successor correlations are gauge charge | A gauge-charged estimate at the point `0` (B3.24) |
| ACG ↔ AKT ↔ AOG | Linear loss of moments; total-length law for products; Künneth collapse; golden datum without budget | A sublinear loss (B1.9), a theorem of the square (Q3) |
| WL ↔ ACS (filtered and short windows) | Filtered deficit → averaged positivity; short windows `Γ^{99/100}`; off-line field; witness persistence | Selection below the zero spacing (B1.4) |
| RW → TH/HCF | Weil margin ⇒ heat window | Fixed time |
| LA ↔ WD ↔ ALDG | Finite head ⇔ slice; large-height repair; collision–index bridge | Residual heat region |
| HJ ↔ HCF ↔ SEC | Residual vanishing = two-grid sign = seam vanishing on the divisor | Pre-divisor forcing |
| BAG ↔ SRT/WL | Recurrence right of `1/2+σ` ⇔ lag floor at `σ` | Returns near zeros |
| APT → RW/EWU/ACT/AIP | Positive restricted families; tents; source selection; finite-level existence | Transfer to an RH-complete cone |
| AOG → HF/ACS/SRT | Orbit Hodge ⇔ blindness; families ⇔ joint blindness; index exit | Forcing |
| AOT → all | Width functor; reading trichotomy; Wiener hulls; prescribed Wiener jets | Producers |
| PTR ↔ W1C | Real-rooted finite producers; faithful-limit receivers | Arithmetic producers |

## 6. Consequences

1. **Count each producer once.** Each of the following is a single producer, shared by the routes listed:
   - a small-damping signed budget: PM, CTF, BVI, MC;
   - a complete Weil sign: RW, SZ, CHMD, OWU, EWU, ACT, AIP, HF, TT, ACS, SRT (Lefschetz form);
   - a residual heat-region sign: LA, WD, TH, HCF;
   - a forcing law into the maximal blind ideal: TG, RN, ACS and all candidates;
   - a gauge-charged estimate at the point `0`: MC, PM, BVI, TTPC, SSA.
2. **Reformulation, carrier maximality and isotropy, invariant completeness, the relative budget and successor coupling are finished.** New equivalent endpoints add nothing; new single-channel or point-stable positive carriers add nothing; new finite or height-coupled multiplicative certificates add nothing; new countermodels with a proper subset of the invariants add nothing; new pole-order bookkeeping adds nothing; new statements from multiplicative data alone add nothing at the point `0`.
3. **The three families reduce to three bridges and one law.**
   - **U1 — escape completeness (Q1).** Finite-window eigenstates are the translated zeros; completeness decides whether U1 has any handle that is not a rate.
   - **U2 — a budget for Lefschetz spans (Q3).** The Weil sign is Castelnuovo–Severi on `{g, T_{p^m} g}` at one prime; over `𝔽_q` the budget comes from correspondences with a theorem of the square.
   - **U3 — positivity beyond isotropy (Q2), then forcing.** Positivity on gauge-charged carriers that are not point-stable, with a term that does not scale.
   - **The common law:** arithmetic forces blindness. It would appear as rate zero in U1, as a complete sign in U2, as exhaustion of the maximal blind ideal in U3, as zero oscillatory capacity for ζ's own zeros, and as typicality of the gauge point `0`.
4. **Where the families meet.**
   - **U1 and U2** meet at the square-root threshold and at selection. Averaged positivity crosses the threshold on windows `Γ^{99/100}`; individual zeros need exceptional sets below the zero spacing; the Lefschetz sequence is a U1 growth rate and a U2 sign at once.
   - **U2 and U3** meet at one inequality: the Weil sign is the Meyer and scaling Hodge index, the Castelnuovo–Severi inequality on Lefschetz spans, the exhaustion of the maximal blind ideal and the positivity of the spectral measure.
   - **U1 and U3** meet at the cofactor module (admission gives a faithful infinite module, escape a module whose finite-window eigenstates are translated zeros), at multiplicative forcing (whose graded continuation is the U1 width scale), at the budget (whose residue, ζ's own zeros, is a U1 rate), and at the gauge point (U1's Möbius law at `0` is RH; U3's multiplicative carriers are gauge invariant).
5. **Partial progress is family-specific.**
   - U1's rate axis is blocked at quasi-RH, and so are multiplicative forcing, its completed-system collar and one-sided Lefschetz bounds.
   - U2 has aperture windows, short-window averages, zero-ordinate positivity for nonnegative tests and finite-level feasibility.
   - U3 has blind, half-blind and isotropic sub-carriers, the boundary forcing law and capacity, the `⌊κ/2⌋` collar, rigidity and its stability, and the exact relative budget.

   A result that converts one family's partial progress into another's would itself be a new mechanism: for example, a budget on Lefschetz spans (U2) obtained from a gauge-charged estimate (U1).
6. **Two obstructions are common to every amplification and every multiplicative argument.** Depth homogeneity: every way of enlarging the data over `ℤ` tested gains on a zero's depth as fast as it pays; for moments and products this is a theorem. Gauge invariance: every argument from multiplicative data proves its conclusion for the whole orbit. Over `𝔽_q` the base and the correspondences on `C × C` escape both; over `ℤ` neither is known. The [summary](hard-obstacles-summary.md#4-would-the-b-tier-obstacles-require-a-new-field-of-mathematics) explains why the known mechanisms are exhausted below RH strength and what a further one must satisfy.
