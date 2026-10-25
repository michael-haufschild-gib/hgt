# Route-unification ledger

**Status 2026-10-25, corpus `e4965f55a` with the working tree of that day.** The 31 live routes, 17 candidates and PW-B are faces of three construction problems:

- **U1 — critical arithmetic cancellation**: the *rate* reading of blindness.
- **U2 — complete signed positivity**: the *sign* reading of blindness.
- **U3 — faithful realization and forcing**: the *carrier* reading of blindness, with an *invariant* sub-reading.

All three ask one question in different currencies: **what forces the actual arithmetic source to be blind to off-line zeros?** The corpus proves the readings equivalent at their endpoints:

- **U1.** A generic orbit's growth rate equals the depth of the deepest zero it sees.
- **U2.** Orbit Hodge positivity holds iff the orbit is blind; family positivity iff joint blindness; every scale-shift-invariant positive test space is blind. Weil positivity is positivity of the spectral side of the explicit formula, whose prime side is positive unconditionally.
- **U3.** The maximal sharp-stable positive Meyer ideal is the off-line-blind ideal and equals the whole source iff RH. The degree-one invariants determine ζ. Pole order accounts exactly for inserted zeros and for nothing else.

The invariant sub-reading of U3 is settled: pole order is a complete invariant for relative deformations (the index–pole conservation identity) and is silent about ζ's own zeros. What it leaves is the payment of ζ's own zeros by oscillation of the zero sum, a rate. **The budget question of U3 is therefore a U1 question.** Identical receivers still do not mean identical producers: each family keeps its own missing construction.

Companions: [complete report](hard-obstacles.md), [summary](hard-obstacles-summary.md), [walls ledger](walls-ledger.md). Evidence: corpus search and Lean statement reading (`logs/review-2510-update/working-log.md`). `[S]`, `[R]` as in the walls ledger.

## 1. Levels of unification

| Level | What it justifies | What it does not |
|---|---|---|
| **Exact identity** | Two expressions are equal on a stated source and normalization. | Extension to another completion or norm. |
| **Receiver isomorphism** | Same threshold at every rate `σ` (width functor). | Equal finite tests, rates or difficulty. |
| **First-rung coincidence** | The weakest nontrivial conclusions coincide; for every U1 receiver and for multiplicative forcing this is quasi-RH. | Equality of later rungs or of producers. |
| **Maximality** | Every member of a class lies in one extremal object. | That the actual source reaches it. |
| **Rigidity** | A set of invariants has exactly one solution. | That the solution's zeros are located. |
| **Conservation** | An exact balance between two invariants on a whole deformation class. | An absolute bound for the base point of the class. |
| **Directional transfer** | A proved bound implies another under hypotheses. | The converse. |
| **Shared construction problem** | The same missing estimate, sign or object. | That one producer yields the others. |
| **Analogy** | A model suggests a mechanism. | Validity for ζ. |

## 2. The three families

### U1 — Critical arithmetic cancellation (rate reading)

**Primary data:** prime or Möbius coefficients. Observables: lag, spline, deficit, Abel moment, history, regularized series, probe, pronic energy, Vaughan Gram, cofactor module, divisor sums, and the oscillatory payment of ζ's own zeros.

**Missing input:** a signed estimate at every positive slack.

**Proved unifications:**

- The width functor makes the spectral, abscissa, damped Möbius and Liouville, ξ half-plane and Suzuki formation receivers isomorphic.
- **First-rung coincidence.** The first gain beyond Vinogradov–Korobov of each graded receiver is a fixed strip: the balanced statistic, centred-prime band, short windows, Vaughan empty leg, JAS budget, PBM abscissa, WL rate `σ`, every Vaughan power improvement [S]; admission at a fixed damping, which uncancelled zeros right of `1/2 + ε` obstruct (visible-pole index).
- **Vaughan phase transition at half damping.** Admission at and above `ε = 1/2`; below it, leading order classified and every power gain a strip.
- **Escape structure.** Record-minimum limits with positive diagonals; singleton-or-continuum families; contraction calculus; eigencharacter moduli `p^{−s}`, `s ≥ 1/2`; finite hulls in the half-plane closure. On the spectral reading [R], escape states are translated zeros, so U1's escape alternative is itself a rate statement.

**Subfamilies:**

- **Width readings:** WL, SRT, PBM, MC, JAS, FU, RP, DR.
- **Critical energy:** PM, CTF, with the BVI, ACCE, ADR, SAEI, SSA and THIM machinery.
- **Oscillatory payment:** the residue of the U3 budget reading (walls 1.16).

**Separate currencies:** LI (reciprocal depth) and RB (extremal inequality); BAG through local recurrence. U1's non-graded handles are frequency averaging (filtered deficit) and the escape alternative.

### U2 — Complete signed positivity (sign reading)

**Primary object:** the complete prime–Gamma–polar Weil form, equivalently the spectral side of the explicit formula as a Poisson pair.

- **Direct attacks on its sign:** RW, SZ, CHMD, OWU, EWU, ACT, AIP, HF, TT.
- **Identification with Hodge index:** ACS.
- **Sign under other quantifiers:** LA, TH, HCF, GTA, XN, PA (degree, rank, heat time, order).

**Proved unifications:**

- Fixed-aperture sign transfer RW ⇔ SZ ⇔ CHMD with identified domains; Suzuki first variation = Weil energy, including on RH-complete tents.
- HF ceiling ⇒ AIP allocation ⇔ ACS strict-cone RR.
- One-shift variation, odd capacity and blind minima are parity components of the form.
- Weil margin ⇒ heat-Hankel positivity in a coupled rank–time window.
- **Averaged positivity** at logarithmic aperture on `[Γ, 2Γ]` for the whole family, through the exact all-parity identity; its main term is the local critical-zero weight.
- **Finite-level existence.** RH ⇔ some weight system is positive at every finite aperture.
- **Bochner form.** RH ⇔ every scale function `y ↦ W(τ_y(f ⋆ f̃))` is the characteristic function of a positive measure; for the two-prime spline orbit, ⇔ a positive measure on `T²`.
- Ground rate = polar rate, merging the rate currencies of RW, SRT and ACS.

**Common localization:** at each aperture the obstruction is a finite low-frequency sector; in the incidence picture frustration comes only from prime-sum edges; across heights it is selection.

### U3 — Faithful realization and forcing (carrier and invariant readings)

**Carriers:**

- geometric: ACS effectivity, the Meyer surface, AOG orbits and families;
- operator-theoretic: RN, GTA, PCS, IRK;
- probabilistic: W1C, FEL;
- photonic: PTR;
- categorical: CDC, SC, WBF, RFHM;
- divisor-diagnostic: HJ, SEC, BSH, APF, EWJ, EGC, PW-B;
- topological: TG;
- heat and divisor: WD cap, ALDG.

**Proved unifications:**

- **Maximality.** Every sharp-stable positive convolution ideal lies in `meyerTraceBoundedIdeal`, the off-line-blind ideal, which keeps every critical jet, carries the full restricted geometry, is closed in the natural topology and equals the source iff RH. Single-channel positive carriers differ only in how much of it they see.
- **Detectors.** The HJ residual, SEC seam, CDC confluence, BSH mate gain, IRK noninvertibility and W1C Clifford energy all read `Re ρ = 1/2` with exact depth laws.
- **Faithful branch.** Operator-norm faithful positivity is RH plus simple zeros.
- **Invariant rigidity.** Coefficient positivity on `[1, ∞)`, Riemann's functional equation, the simple pole and the growth premises determine ζ (APD). Every relaxation breaks this.
- **Pole capacity.** On the boundary a pole of order `k` carries at most `⌊k/2⌋` zeros; in completed positive systems the same threshold `κ < 2Σm` holds with a `1/log T` collar and `κ²` sparsity [S]; for relative deformations the index–pole conservation identity is exact, pole order one is rigid [S] and pole order two admits every off-line type.

**Common missing object:** a pre-divisor source with a **forcing law** that places it in the maximal blind ideal, with input outside every mapped class and a term that does not scale with amplification. Where it would act: ACS effectivity; the HJ/SEC weld; the TG sub-unit residual; the RN boundary orientation; a section count registering oscillatory payment.

### The forcing currency: where the families meet

Four forcing mechanisms are proved. Each sits between families and stops at a computed boundary.

| Mechanism | Family of origin | What it forces | Where it stops |
|---|---|---|---|
| Multiplicative positivity (boundary divisor positive definite) | U3 | `ζ(1+it) ≠ 0`; capacity `⌊k/2⌋`; with growth input the dlVP, Littlewood and VK regions | Interior gain only from growth input; coupled certificates split into rational fibres; no quantized inequality at the critical line; next rung a fixed strip (U1). |
| Coupled height positivity in completed systems [S] | U3 | Not all of `r` zeros with `2Σm > κ` on `Re s = 1`; `κ²` collar sparsity | Boundary scale only; depth enters through `1 − β` (U1). |
| Linear rigidity (Fejér-tent squeeze on the theta law) | U3 | The coefficient measure is ζ's | Zeros are nonlinear in the measure. |
| Pole order on relative deformations | U3 | Index increment = pole increment `+ R_crit − I_crit`; `κ = 1` rigid | Pays inserted zeros only; ζ's own zeros are a rate (U1). |

Their invariants run in parallel. Rows pair invariants with the same role where one exists.

| Boundary line `Re s = 1` | Interior (degree one) |
|---|---|
| Nonnegative weights (N) | Coefficient positivity on `[1, ∞)` (N) |
| Integer divisor (Z) | Riemann's functional equation (FE) |
| Simple pole (S) | Simple pole (S) |
| Pole isolation (I) | Holomorphy of the completion in the strip (H) |
| N + Z + S + I ⇒ no boundary zeros; each necessary | N + FE + S (+ growth) ⇒ the system is ζ; dropping S or H admits off-line zeros |
| A pole of order `k` carries `≤ ⌊k/2⌋` boundary zeros, every placement realized | Relative deformations: conservation identity; `κ = 1` rigid; `κ = 2` admits every off-line type |

On the boundary the invariants force the conclusion (no zeros) and compute the capacity. In the interior they force the identity of the source and the exact accounting of inserted zeros; the zero conclusion for ζ itself is not a capacity statement at all.

## 3. Every route and candidate

Abbreviations in the last column: *Rate* = graded rate `σ` (first rung quasi-RH). *Aperture* = pointwise aperture or averaged window. *Carrier* = carrier, height, heat or order exhaustion.

### Live routes

| Route | Family | Common receiver or invariant | Distinct missing producer | Partial-progress axis |
|---|---|---|---|---|
| **WL** | U1 | Width via spline, deficit, critical energy | Signed lag/energy at every slack | Rate; filtered averages |
| **RW** | U2 | Ground energy `μ`, shell flux, prime ladder | Sign at every aperture; collar estimate | Aperture |
| **FU** | U1 | Completed Abel moment | Complete history covariance | Rate |
| **RP** | U1 | Matched-quantile history floor | High-LCM and moving-core payment | Rate |
| **PA** | U1/U2 | Prime–archimedean current; Hausdorff moments | Low shifts across unbounded orders | Carrier (order) |
| **MC** | U1 | Mertens; `θ(ε,t)` gap; bands ⇔ `Θ<1` | Interior anti-alignment | Rate |
| **TT** | U1/U2 | Directed Wold covariance; odd form | Covariance sign | Aperture |
| **LA** | U2 | Finite-head coefficients; heat; Jensen | Zero heat on the residual region | Carrier (heat × height) |
| **TG** | U3/U2 | Winding, sub-unit trace | Residual sign, sub-unit bound | Carrier |
| **HF** | U2/U3 | Full cone `{Λ}`; ceiling; index `D`; two-prime Bochner receiver | `O(L)` ceiling or `D < 2` | Aperture |
| **CHMD** | U2 | Odd bound states; nodal quotient | Nodal / reflected-prime sign | Aperture |
| **TH** | U2 | All-rank heat-Hankel sign | Signed vectors at one time | Carrier (rank) |
| **RN** | U3 | `det₂` resonances | Boundary orientation | Carrier |
| **WD** | U3/U2 | Ward cap; collisions; heated head | Cap vanishing; residual heat region | Carrier (heat × height) |
| **LI** | U1 | Reciprocal-depth clock | Subexponential floor | Rate (separate currency) |
| **SZ** | U2 | First variation = Weil energy | Same sign as RW | Aperture |
| **PM** | U1 | Admission; Vaughan Gram; cofactor module | Signed small-damping energy; escape classification | Rate (damping); escape |
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
| **SRT** | U1/U2 | One-parameter lag family; detector | Lag sign; selection | Aperture; selection |
| **ACT** | U2 | One-shift variation | All-profile reflected collar | Aperture |
| **AIP** | U2 | Shared incidence allocation | One shared budget | Aperture |
| **ACS** | U2/U3 | Hodge index; RR; maximal blind ideal; multiplicative forcing; rigidity; pole capacity | Forcing input outside the mapped classes | Carrier; aperture |

### Candidates and PW-B

All are U3 unless noted. Each lacks the forcing law of §2. Single-channel sharp-stable positivity cannot supply it, coupled height positivity reaches only the boundary, and every candidate must separate ζ from the relaxation models at pole order two.

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
| **W1C** | U3 | Centered Lee–Yang limit | Arithmetic couplings |
| **WBF** | U3 | Genealogy completion | Arithmetic stream |
| **PW-B** | U3/U1 | Positive-damping action | Pre-divisor form; zero-damping landing |

## 4. Exact common currencies

### 4.1 Width (U1 and multiplicative forcing)

For `σ ≥ 0`, `Δ ≤ σ` is equivalent to each of: graded lag, spline, deficit-primitive, band and regularized-series bounds; admission of every damping above `σ`; the ξ half-plane bound; the Suzuki formation exponent `1+2σ`; the JAS budget; balanced, centred-prime and short-window savings (for `σ < 1/2`); the Vaughan empty-leg and tail-rate statements (rate supremum `1 − Θ` at every damping) [S]. VK is the strongest unconditional point. Sources include `TheWidthFunctor`, `balancedStatisticPowerSaving_iff`, `centredPrimeBandPowerSaving_iff`, `xiZeroHalfPlaneBound_iff_logZetaRegCoeff_converges`, `exists_halfPlane_lt_half_iff_exists_jasBudgetProductPositive`, `TheVaughanEmptyLegReadsTheZeroAbscissa`.

### 4.2 The common Weil form (U2)

| Statement | Relation | Qualification |
|---|---|---|
| Exact form | `Q = (γ₀−2)‖F‖² + Lévy + 4·horizon + 2∫incoming·G²` | Every compact `C²` test. |
| Ground | `μ(A) ≥ 0 ⇔ W_{A′} ≥ 0` for `A′ < A`; flow strictly decreasing | RH ⇔ `μ > 0` at every `A`. |
| Prime ladder | RH ⇔ cumulative frozen relaxation `≤ μ(3/10)` | Birth jumps vanish. |
| Finite level | RH ⇔ every aperture admits a positive weight system | No sign or growth premise. |
| Bochner | RH ⇔ positive spectral measures for every `C²` test | The prime measure is positive unconditionally. |
| Suzuki | First variation = Weil energy | Compact `L²`; RH-complete tents. |
| CHMD | Completion = supported maximal graph | Fixed aperture. |
| AIP ↔ ACS | Allocation ⇔ strict-cone RR | All apertures ⇔ RH. |
| HF → AIP | Ceiling ⇒ allocation | Directional. |
| ACT | One fixed shift decides RH | All even profiles. |
| RW → TH/HCF | `μ₀(A) > 0`, `K < A²/4` ⇒ heat-Hankel positivity, degree `≤ n`, time `≤ K/n` | Rank and time coupled. |
| Graded | `Δ ≤ σ` ⇔ `H¹` floors at every rate `> σ` | Endpoint attained. |
| Averaged | Positive at `A ≤ κ₀ log Γ` on `[Γ, 2Γ]` | Frequency average only. |
| Blindness | Scale-shift-invariant positive spaces are blind | No producer. |

### 4.3 Geometric currency (U2 ↔ U3)

- **Scaling surface.** Pairing = pole plane − Weil form. Hodge index, RR plus ample effectivity, and zero sector defect are each equivalent to RH. Adjoining two polar fibres of budget `κ` to a local pairing `L` gives Hodge index ⇔ `L(x,x) ≤ 2κ ℓ_H(x)ℓ_V(x)` [S].
- **Meyer surface.** Trace RR unconditional; Bézout ⇔ ampleness ⇔ RH; numerical = principal ⇔ simple zeros.
- **Maximal blind ideal.** All axioms hold; greatest sharp-stable positive ideal; equals the source ⇔ RH.
- **Function-field calibration.** Rosati cones have Bézout without unitarity; genus-one Hodge index ⇔ degree positivity of `ℤ[F]`; curve purity ⇔ positive definiteness of the trace sequence on `ℤ`; the Hecke graphs of `ℤ` have no theorem of the square.

The Weil sign, ACS RR + Bézout, the Meyer Hodge index, exhaustion of the maximal blind ideal, positivity of the spectral measure and the Lefschetz–Hasse–Weil bound are the same statement. An analytic payment of the low sector, a geometric forcing law and an oscillatory capacity for ζ's own zeros would be three proofs of it.

### 4.4 Ground rate and clustering

`Δ ≤ polarRate = groundRate ≤ 1/2`, `RH ⇔ groundRate = 0`; form-norm rates equal `Δ`. RW, SRT, ACS, EWU and AIP share this currency.

### 4.5 Depth on the divisor (U3)

The first-prime seam charge `√2·log 2·sinh(δ log 2)`, the mate gain `2δ log n` and the other zero-indexed diagnostics have exact depth laws with supremum `Δ`. Positive Hermitian Meyer degrees see critical values only. The BSY functional is nonnegative and vanishes exactly on critical zeros. **Diagnostics read depth; none forces it to vanish.**

### 4.6 Invariants and capacity (U3 selectivity)

- **Rigidity.** N + FE + S + growth ⇒ ζ; discrete Beurling systems ⇒ rational primes [S]; stability under sublinear critical-line defects.
- **Relaxations.** Pole order 2 ⇒ real stray, or complex quartet with one critical refund; pole order 3 ⇒ unrefunded quartet; strip poles ⇒ quartet; no FE ⇒ over-regular zeros; no positivity ⇒ non-uniqueness.
- **Capacity.** Boundary: `⌊k/2⌋` zeros per pole of order `k`. Completed systems: `κ < 2Σm` forces a zero off `Re s = 1` [S]. Relative interior: index increment = pole increment `+ R_crit − I_crit`; `κ = 1` rigid [S].

Every forcing proposal is tested here (summary W1): it must use all invariants, fail on the pole-order-2 models, and see more than pole order.

### 4.7 Currencies that stay separate

| Currency | Exact result | Not identified with |
|---|---|---|
| Li reciprocal depth | Rate law; off-line rates `≤ 1/431`; `β < 1/300` | `Δ` |
| Heat constant `Λ₊` | `0 ≤ Λ₊ < 1/8`; `Λ₊ = 0 ⇔ RH`; `Λ₊ ≤ Δ²/2` | `Δ` |
| HF ceiling exponent | `Δ ≤ θ* ≤ Δ/2 + 1/4` | `Δ` |
| Packet vs Weil energy | `m²` vs `m` | Each other without simplicity |
| Trace-bounded vs operator-norm faithful positivity | RH vs RH + simple | Each other |
| Pole order on deformations | Counts inserted minus removed critical traffic, exactly | `ind₋(W_ζ)` (only lower bounds), `Δ` |
| Quantum budget | `b(η) = (√A + √(Gη))²/B`; `b(½) ≥ 1` for Fejér certificates once `L ≥ 0.17` | A zero count at the critical line |
| Coalescent surplus | `3/4` proportion at `β ≤ 1/18` | RH |

## 5. Interfaces

| Interface | Proved | Missing |
|---|---|---|
| WL ↔ PA | Exact trace identity | Source sign |
| MC ↔ PM ↔ BVI | Energy = interior bracket `+ O(1)`; Möbius ≅ Liouville; bands ⇔ `Θ<1`; Vaughan transition at half damping | Arithmetic contraction of the residual |
| PM ↔ ADR ↔ AOT | Admission ⇔ faithful infinite module; escape ⇒ paid ideal ⊆ annihilator; record-minimum limits; singleton-or-continuum; contraction calculus; eigencharacter moduli; visible-pole index | Escape classification (Q3) |
| PM ↔ SSA ↔ THIM | Half-damping endpoint bounded for all squarefree `P`; integer local exponents below half | Sub-half signed interior |
| PM ↔ CTF | Residual = readout² + energy | One row family doing both |
| RW ↔ SZ ↔ CHMD | Sign transfer; first variation; domains | Sign |
| RW ↔ SRT ↔ ACS | One rate currency; cluster dichotomy | `polarRate = Δ` |
| HF → AIP ↔ ACS | Ceiling ⇒ allocation ⇔ strict RR | The inequality |
| HF ↔ APD | Two-prime spline orbit ⇔ Bochner problem on `T²`; affine positivity induced from dilations | Construction of the torus measure; prescribed successor coordinates |
| ACS ↔ Meyer ↔ curves | Meyer Hodge ⇔ RH; maximal blind ideal and its topology; Rosati and genus-one calibration | Forcing input; exhaustion |
| ACS ↔ MPG ↔ SBWF ↔ U1 | Boundary forced with capacity `⌊k/2⌋`; completed-system threshold and `κ²` collar [S]; growth gives dlVP/VK; finite certificates capped | Better growth input or a non-multiplicative mechanism |
| ACS/HF ↔ APD ↔ RHTower deformations | Positive-measure rigidity; relaxation models; conservation identity; `κ = 1` rigidity [S] | — (budget reading closed; ζ's own zeros are U1) |
| WL ↔ ACS (filtered) | Filtered deficit → averaged form positivity | Selection (Q1) |
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
   - a complete Weil sign: RW, SZ, CHMD, OWU, EWU, ACT, AIP, HF, TT, ACS;
   - a residual heat-region sign: LA, WD, TH, HCF;
   - a forcing law into the maximal blind ideal: TG, RN, ACS and all candidates.
2. **Reformulation, carrier maximality, invariant completeness and the relative budget are finished.** New equivalent endpoints add nothing; new single-channel positive carriers add nothing; new finite or height-coupled multiplicative certificates add nothing; new countermodels with a proper subset of the invariants add nothing; new pole-order bookkeeping adds nothing.
3. **The three families reduce to three bridges and one law.**
   - **U1 — escape classification (Q3).** Whether escape states are exactly translated zeros decides whether U1 has any handle that is not a rate.
   - **U2 — selection (Q1).** From averaged positivity, proved beyond Nyquist, to individual heights.
   - **U3 — scale-side coupled positivity (Q2), then forcing.** Positivity outside the single-channel class, with a term that does not scale.
   - **The common law:** arithmetic forces blindness. It would appear as rate zero in U1, as a complete sign in U2, as exhaustion of the maximal blind ideal in U3, and as zero oscillatory capacity for ζ's own zeros.
4. **Where the families meet.**
   - **U1 and U2** meet at the square-root threshold. Averaged positivity crosses it (up to `X ≤ Γ^{4/3}`), so the meeting point has moved from aperture to selection.
   - **U2 and U3** meet at one inequality: the Weil sign is the Meyer and scaling Hodge index, the exhaustion of the maximal blind ideal and the positivity of the spectral measure.
   - **U1 and U3** meet at three places: the cofactor module (admission gives a faithful infinite module, escape one annihilated by the paid ideal), multiplicative forcing, whose graded continuation is the U1 width scale, and the budget, whose relative part is complete and whose residue, ζ's own zeros, is a U1 rate.
5. **Partial progress is family-specific.**
   - U1's rate axis is blocked at quasi-RH, and so are multiplicative forcing and its completed-system form.
   - U2 has aperture windows, averages and finite-level feasibility.
   - U3 has blind sub-carriers inside one maximal ideal, the forcing law and capacity on `Re s = 1`, rigidity, and the exact relative budget.

   A result that converts one family's partial progress into another's would itself be a new mechanism. For example, short-window averaged positivity (U2) that controls zero ordinates would supply U1 selection data.
6. **Depth homogeneity is the common obstruction to every amplification [R].** Every way of enlarging the data over `ℤ` tested in the corpus (harmonic twists, Følner coupling, family averages, tensor powers) gains on a zero's depth as fast as it pays. Over `𝔽_q` the base supplies a fixed loss that roots remove; over `ℤ` no base is known. The [summary](hard-obstacles-summary.md#4-would-the-b-tier-obstacles-require-a-new-field-of-mathematics) explains why the known mechanisms are exhausted below RH strength and what a further one must satisfy.
