# Route-unification ledger

**Status 2026-10-27, corpus `6046e5478` with working tree.** The 31 live routes, 17 candidates and PW-B are faces of three construction problems:

- **U1 — critical arithmetic cancellation**: the *rate* reading, and its pointwise form, *alignment* of `γ log p` at zero ordinates.
- **U2 — complete signed positivity**: the *sign* reading.
- **U3 — faithful realization and forcing**: the *carrier* reading, with *invariant and deformation*, *counting*, *renormalization*, *field*, *gauge* and *base* sub-readings.

All three ask one question in different currencies: **what forces the actual arithmetic source to be blind to off-line zeros?** The corpus now states it through one potential `log|ξ|`, the characteristic circle, and the explicit formula read at atomic resolution:

- **U2 is the positivity of the equivariant form.** `W` is Hecke equivariant with finitely many negative directions at every aperture; on log-atom tests every term is explicit (self-energy, polar pairing, archimedean cross kernel, the finite intersection of torsion orbits), and RH is one inequality between these forms at every width.
- **U3 asks for a form positive and equivariant at once.** `D` is positive and computed; its equivariance defect is the moment of inertia; uniform caps on it are strips. Every regulator of the prime place alone kills positivity (Abel: survival `{0}`; spacing: covariant and indefinite; horizon: unbounded rank on torsion orbits); coupling pays at most the partner's rank; covariant diagonal counterterms are scalar. The archimedean place pays the prime place below the spacing of the atoms, with matched constants and no gauge charge.
- **U1 excludes by comparing a collided object with a Rosati one, a budget with a spectral count, or a short prime sum with a zero-side reserve.** Every graded reading is one width currency; alignments of short prime polynomials at zero ordinates are rare (power-saving counts); zero-ordinate moments are Rosati pairings; outside the strip the primes anti-align at a deep zero's ordinate.

The readings are equivalent at their endpoints:

- **U1.** Escaped Möbius `θ`-decay, receiver rate `1/2 − θ`, `Θ ≤ 1 − θ`, the Hecke strip cap, dyadic rate `1 − 2θ`, `Re ξ′/ξ ≥ 0` on `Re s > 1 − θ` and prefix reading rates are one statement at each `θ`; RH is `θ = 1/2`.
- **U2.** Orbit Hodge positivity iff the orbit is blind; Castelnuovo–Severi on Lefschetz spans; zero negative index; the tower-coordinate Hodge index for every log-atom cycle at every width.
- **U3.** The maximal blind ideal is everything; `M_f = 0` for every test; zero transverse energy; no right terminal; positive chirality at every ordinate.

**Twelve readings cut across the families.**

- **The local type.** Multiplicative correspondences boost, the successor is unipotent, `σ_γ` swaps, torsion rotations are elliptic in the additive dual.
- **The gauge point.** Square-class couplings and the finite intersection are gauge blind; at atomic resolution twins' Weil forms differ only by the archimedean charged–neutral cross term, and `ζ` is the orbit minimum on nonnegative tests; successor couplings and cells are charged; the source's margin `2 log² p` never collapses; Liouville is separated from `23/40` on.
- **The pairing.** Collided objects pair `ρ` with `ρ̄`, Rosati objects pair `ρ` with `1 − ρ̄`; zero-ordinate moments are Rosati.
- **The regulator.** The rank of a counterterm is a property of the regulator: identity (Abel), scalar (spacing), identity ⊗ polar (horizon), rank one (archimedean lattice germ, pole at atomic resolution).
- **The partner.** A coupled partner pays at most its own counterterm's rank; the archimedean place pays the arithmetic point.
- **The local–global passage.** The prime kernel is a sum of transverse tower forms; summing their bounds costs the square root; there is no common ladder; the archimedean self-energy pays the sum below the spacing.
- **The spacing scale.** At width `≍ 1/N` the covariant prime counterterm `log N` meets the archimedean self-energy `log(1/w)`; the archimedean cross term between charged and neutral atoms, the only term in which twins' Weil forms differ, stops being dominated; tests begin to see zeros up to height `≍ N`; Dirichlet polynomials of length `N` sit in the Montgomery–Vaughan regime `T ≍ N` [R].
- **The field and the energy.** Computed, quantized, outward at terminals; uniform ceilings are strips.
- **The moment of inertia.** The Hecke defect of `D`; dyadic amplification is soft.
- **The alignment.** Beyond the conductor, at terminals and at the field threshold an off-line zero is a large value of a short prime polynomial at a zero ordinate; such values are rare; the implication from zero to alignment is proved only at `σ > 1`.
- **The central order.** Deformations detect zero-free ordinates and are irreversible.
- **The statistic.** Averages, proportions and alignment counts exclude no zero; a quantized statistic below one quantum would.

Sub-readings of U3: invariant and deformation — closed; counting — closed as a reduction; renormalization — closed for the prime place under every tested regulator and for coupling of the torsion block, open as archimedean payment at and beyond the spacing (Q1); field — exact threshold, uniform ceilings are strips, non-uniform bound open (Q3); gauge — closed structurally and on coefficients, open on forms (Q2); base — open. Identical receivers do not mean identical producers.

Companions: [complete report](route-obstacles.md), [summary](obstacles-summary.md), [walls ledger](walls-ledger.md). Evidence: `logs/review-2710-v4-research-log.md`. `[S]`, `[R]` as in the walls ledger.

## 1. Levels of unification

| Level | What it justifies | What it does not |
|---|---|---|
| **Exact identity** | Equal on a stated source and normalization (`Re W = D − Δ`; `L(Λ ⋆ Λ) = (ζ′/ζ)²`; prime functional on log-atoms = finite intersection; `P = Σ_p L_p`; tower-coordinate decomposition; Gauss's digamma formula). | Extension to another width, regulator or norm. |
| **Computation** | Produced by an identity from source data. | Any inequality for it. |
| **Comparison** | Mutual bounds with explicit constants. | That either is bounded. |
| **Detection** | Sees each off-line zero at its own height. | Exclusion. |
| **Frequency** | Bounds how often a large value occurs at zero ordinates. | Any individual zero. |
| **Quantization** | Jumps by a quantum at off-line zeros. | Computation below the quantum. |
| **Survival** | Positivity passes a limit on the counterterm's null cone. | Positivity off it. |
| **Regulator equivalence** | Two pairings share a regulator and hence a counterterm rank. | That a different regulator behaves alike. |
| **Matched constants** | Two divergences agree at leading order (`log N` vs `log(1/w)` at `w ≍ 1/N`). | Agreement of the `O(1)` terms or of the cross terms. |
| **Receiver isomorphism** | Same threshold at every rate (width currency). | Equal difficulty. |
| **Currency equivalence** | Proved equivalent statements. | That either is easier. |
| **Per-ordinate equivalence** | A statement at `γ` is the absence of zeros at `γ`. | Anything elsewhere. |
| **First-rung coincidence** | The weakest nontrivial conclusions coincide (quasi-RH). | Later rungs or producers. |
| **Gauge equivalence** | Sources with the same multiplicative data, or forms conjugate under `x ↦ ωx`, cannot be told apart. | Any statement at a chosen point of the orbit. |
| **Local-type equivalence** | Same hyperbolic symmetry, same isotropy. | That either sees the sign. |
| **Pairing equivalence** | Collided forms of one conjugate pairing. | Rosati positivity. |
| **Local–global equivalence** | A global form is a sum of local forms. | That local bounds sum. |
| **Threshold coincidence** | Several mechanisms stop at the same scale (spacing, conductor, square root) [R]. | That one producer crosses all. |
| **Diophantine equivalence** | Detectors reduce to one alignment question [R]. | That it can be excluded. |
| **Calibration equivalence** | A `ℤ` statement and its `𝔽_q` analogue have the same shape. | That the proof transfers. |
| **Layer equivalence** | Same layer of Weil's argument. | That a lower layer forces a higher one. |
| **Maximality / isotropy** | One extremal object or isotropic fibres. | That the source reaches it. |
| **Rigidity / ceiling** | One solution or a bounded invariant. | Location of its zeros. |
| **Statistical reduction** | A proportion bounds a class of zeros. | A single zero. |
| **Classical reduction** | The strongest output is classical. | That a refinement stays classical. |
| **Directional transfer** | A bound implies another under hypotheses. | The converse. |
| **Shared construction problem** | Same missing estimate, sign, regulator, structure or bound. | That one producer yields the others. |
| **Analogy** | A model suggests a mechanism. | Validity for `ζ`. |

## 2. The three families

### U1 — Critical arithmetic cancellation (rate and alignment)

**Primary data:** prime or Möbius coefficients. Observables: lag, spline, deficit, Abel moment, history, regularized series, pronic energy, Vaughan Gram, cofactor module, divisor sums, Lefschetz sequences, one-sided counts, horizon torsion, Farey potential, budgets, escaped Möbius pairings, integer-theta prefix readings, short prime polynomials at zero ordinates, the prime field at `σ > 1`.

**Missing input:** a signed estimate at every slack at the gauge point `0`; pointwise, an interior implication from an off-line zero to an aligned prime polynomial, and extinction of the exceptional set.

**Proved unifications:**

- **Width currency** [L/S]: seven quasi-RH criteria equivalent; at each `θ` the escaped, receiver, abscissa, Hecke-cap, dyadic, Carathéodory and prefix readings coincide; VK decay uniform in `N, a, b`.
- **Escape**: located, classified; RH ⇔ positive gauge mass.
- **Counting forms**: one-sided count ⇔ horizon torsion ⇔ Farey potential ⇔ RH.
- **Budgets**: prime-error budget ⇔ RH; Abel slope ⇔ RH + simple.
- **Gauge form**: Möbius half-power law at `0` is RH, holds a.e.
- **Loss law**: linear loss; twists neutral; dyadic amplification soft.
- **Alignment**: exterior anti-alignment at `σ > 1` [L]; power-saving alignment counts at zero ordinates [L]; zero moments are Rosati pairings [L].

**Subfamilies:** width readings (WL, SRT, PBM, MC, JAS, FU, RP, DR); critical energy (PM, CTF with BVI, ACCE, ADR, SAEI, SSA, THIM); budgets (WL, MC); alignment (SRT, OWU). **Separate currencies:** LI, RB, BAG.

### U2 — Complete signed positivity (sign)

**Primary object:** the complete prime–Gamma–polar Weil form; equivalently the Rosati trace of the correspondence ring; equivalently, on log-atoms, the self-energy plus polar pairing minus archimedean cross kernel minus the finite intersection.

- Direct attacks on its sign: RW, SZ, CHMD, OWU, EWU, ACT, AIP, HF, TT.
- Identification with Hodge index, Castelnuovo–Severi, Rosati positivity, symmetric-square spectra: ACS, HF, SRT.
- Sign under other quantifiers: LA, TH, HCF, GTA, XN, PA.

**Proved unifications:**

- RW ⇔ SZ ⇔ CHMD at fixed aperture; HF ceiling ⇒ AIP allocation ⇔ ACS strict-cone RR; Gårding and finite negative index.
- Averaged positivity at `Γ^{99/100}`; zero-ordinate positivity; positive proportions; census.
- Lefschetz and local–global: one or two primes; symmetric squares; local Hodge index; no global ceiling; square-root price.
- Two forms: `Re W = D − Δ`; RH ⇔ `M_f ≡ 0`.
- Elliptic sectors: below the horizon positive; forcing gap.
- **Atomic resolution**: prime functional = finite intersection; tower-coordinate Hodge index; stability law; `Re W + 2S² ≥ 0`; shared by every sign twin.
- Gauge windows: twins separated at `181/500`, `23/40`, Liouville permanently.
- Short cycles: lag `log 2` positivity on even profiles.

**Common localization:** at each aperture a finite low-frequency sector; across primes the divergence along the pole direction and along torsion orbits; across widths the spacing scale; across heights selection below the zero spacing; in the field picture outward terminals.

### U3 — Faithful realization and forcing (carrier, invariants, counting, renormalization, field, gauge, base)

**Carriers:** geometric (ACS, Meyer surface, AOG, correspondence and theta surfaces, polar boxes); potential-theoretic (CDG, AES, AE/AIT circle, RBG germs, RAPT regulators); operator-theoretic (RN, GTA, PCS, IRK); probabilistic (W1C, FEL); photonic (PTR); categorical (CDC, SC, WBF, RFHM); divisor-diagnostic (HJ, SEC, BSH, APF, EWJ, EGC, PW-B); topological (TG); heat and divisor (WD, ALDG); gauge-geometric (BGG, RBG).

**Proved unifications:**

- Maximality and isotropy by local type; resonance; `σ_γ`; non-localizing positivity; rotations archimedean.
- Detectors computable; faithful branch is RH + simple.
- Invariants, contraction, collision, deformations, packets and lattice clouds: classified.
- Counting: six currencies; naive heights are traces.
- **Renormalization**: survival law; regulator table; partner-rank law; periodic coupling pays the arithmetic point; Ramanujan twins and pole-node relocation; covariance law; covariant counterterm `log N + O(1)`; anomaly cost `½ log N`; self-intersection dominates each tower.
- **Field and energy**: computed, quantized; energy of a zero logarithmic; uniform terminal ceilings are strips.
- **Gauge**: blind ⇔ square class; cells charged with growing defect; source margin `2 log² p`.
- **Base**: no common ladder over `ℤ`; successor transverse to all ladders.
- Weil's layers: identities, square theorem, budget free; over `𝔽_q` counting proves purity.

**Common missing object:** a pre-divisor source with a forcing law placing it in the maximal blind ideal, with input that is computed, uses charged couplings, is localized by a non-multiplicative operation, does not scale with amplification, and supplies a form positive and equivariant at once — by archimedean payment at and beyond the spacing scale, through a base joining the ladders, or through a non-uniform field bound.

### The forcing currency: where the families meet

| Mechanism | Family | What it forces | Where it stops |
|---|---|---|---|
| Multiplicative positivity | U3 | `ζ(1 + it) ≠ 0`; with growth, dlVP/VK | Interior gain only from growth. |
| Coupled height positivity | U3 | `⌊κ/2⌋` collars; `κ = 1` class | Collar width `1/log T`. |
| Invariant carriers | U2/U3 | Blindness, isotropy | Boost invariance. |
| Non-localizing positivity | U2/U3 | Coercivity | Every prime weight. |
| `σ_γ` localization | U2/U3 | Twisted positivity; companion forcing | Disjoint from the horizon. |
| Zero-side reserves | U3/U1 | Reserve `≥ c·a·log γ` at each off-line zero | Detect; uniform ceilings are strips. |
| Alignment counts | U1 | Few aligned zero ordinates | No individual zero. |
| Exterior prime field | U1 | Anti-alignment at `σ > 1` | Not inside the strip. |
| Nonnegative tests | U2 | Upper bounds on the source | Dominated twins. |
| Square-class kernels; finite intersection; atomic forms | U1/U2/U3 | Statements true for `Λ` and every twin | Gauge blind. |
| Successor couplings; cells; source margin | U3 | Gauge fixing; coefficient margin | Not a form margin. |
| Pole order; contraction | U3 | Index bookkeeping | Pays inserted zeros; `κ ≥ 3`. |
| Deformations | U3 | Rigidity off the line; quantized drop | Detect, do not force. |
| Finite-window certificates | U2 | Twins separated | No margin law. |
| Collided positivity | U1/U3 | Faithful positivity; `E_f ≍ M_f` | Equivariance is RH. |
| Torsion energies; spacing regulator; horizon | U3/U1 | Positivity before the limit; covariance up to tame | Survival `{0}`; indefinite; unbounded rank. |
| Coupled germs | U3 | The arithmetic point survives | Partner rank. |
| Archimedean self-energy at atomic resolution | U2/U3 | `arch − prime ≥ 0`; `Re W + 2S² ≥ 0` | Width `N^{−O(1)}`; shared by every twin. |
| Local tower forms | U2/U3 | Local Hodge index | No ceiling; no base. |
| Electrostatics | U3/U2 | Quantized energy; thresholds | Computed, not bounded. |
| Statistics | U2 | `3/4` within `4/log T` | No individual zero. |
| Counting and budgets | U3/U1 | Exact receivers | Each is RH. |

**Boundary versus interior.**

| Boundary line `Re s = 1` | Interior |
|---|---|
| Nonnegative weights; integer divisor; simple pole; isolation ⇒ no boundary zeros | Coefficient positivity, FE, simple pole, finite order ⇒ `ζ`; dropping S or H admits off-line zeros |
| `⌊k/2⌋` boundary zeros per pole of order `k` | `⌊κ/2⌋` collar zeros; `κ = 1` class; `κ ≥ 3` for anchored quartets |
| dlVP bounds `ζ′/ζ` from the prime side; at `σ > 1` a zero forces anti-alignment | Reserves bound `ζ′/ζ` from the zero side; no prime-side bound inside |
| Families: only two-torsion exception | Deformations rigid at zero-free ordinates |
| Below the spacing: archimedean self-energy pays the prime intersection | At and beyond the spacing: open |

## 3. Every route and candidate

Axes: *Rate* (first rung quasi-RH). *Aperture*. *Carrier*. *Escape*. *Lefschetz*. *Gauge* (form margin). *Alignment* (interior implication, extinction). *Inertia* (non-uniform `M_f` bound). *Field* (non-uniform field bound). *Spacing* (archimedean payment at `cδ_N`). *Overlap* (positivity with non-ratio lags). *Base* (covariant structure across ladders). *Count*. *Budget*.

### Live routes

| Route | Family | Common receiver or invariant | Distinct missing producer | Partial-progress axis |
|---|---|---|---|---|
| **WL** | U1 | Width; one-sided count; horizon torsion; prime-error budget | Signed lag at every slack; an actual budget | Rate; budget |
| **RW** | U2 | Ground energy; prime ladder; negative index | Sign at every aperture | Aperture; Lefschetz |
| **FU** | U1 | Completed Abel moment | Complete-history covariance | Rate |
| **RP** | U1 | History floor | High-LCM payment | Rate |
| **PA** | U1/U2 | Prime–archimedean current | Low shifts across orders | Carrier (order) |
| **MC** | U1 | Mertens; width currency; prefix readings; Kloosterman packets | Interior anti-alignment; budget; growing packets | Rate; gauge; budget |
| **TT** | U1/U2 | Wold covariance; odd form | Covariance sign | Aperture |
| **LA** | U2 | Finite heads; heat | Residual heat sign | Carrier (heat × height) |
| **TG** | U3/U2 | Winding | Residual sign | Carrier |
| **HF** | U2/U3 | Full cone; `D_idx`; two forms; `M_f`; field; torsion; regulators; atomic resolution; zero moments | Lefschetz part; a non-uniform bound; archimedean payment at the spacing; a base | Aperture; Lefschetz; inertia; field; spacing; overlap; base; count |
| **CHMD** | U2 | Odd bound states | Nodal sign | Aperture |
| **TH** | U2 | Heat-Hankel sign | Signed vectors at one time | Carrier (rank) |
| **RN** | U3 | `det₂` resonances | Boundary orientation | Carrier |
| **WD** | U3/U2 | Ward cap; collisions | Cap vanishing | Carrier |
| **LI** | U1 | Reciprocal depth | Subexponential floor | Rate (separate) |
| **SZ** | U2 | First variation | Same sign as RW | Aperture |
| **PM** | U1 | Admission; gauge mass; Abel atoms | Small-damping energy; exterior tightness | Rate; escape |
| **JAS** | U1 | Level-one budget | Half-power budget | Rate |
| **CTF** | U1/U3 | Báez–Duarte residual | Readout and energy together | Rate |
| **HCF** | U2 | Two heat grids | Both grids at all degrees | Carrier (degree) |
| **XN** | U2/U3 | Newton margin | Covering discs | Carrier |
| **BAG** | U1/U3 | Recurrence | Returns near zeros | Carrier |
| **EWU** | U2 | Even minimum; `181/500` floor | Low and mixed modes | Aperture; gauge |
| **GTA** | U2/U3 | Schur decay | Rank-uniform decay | Carrier (rank) |
| **OWU** | U2 | Odd capacity; twins separated; short cycles; alignment counts | Reflected-prime payment; form gauge margin; interior alignment | Aperture; gauge; alignment; overlap |
| **PBM** | U1 | Regularized abscissa | Convergence to `1/2` | Rate |
| **RB** | U1 | Robin on CA numbers | Extremal tail | Rate (separate) |
| **SRT** | U1/U2 | Lag family; `σ_γ` detector; exterior field; alignment counts | Lag sign; selection; interior alignment | Aperture; selection; alignment |
| **ACT** | U2 | One-shift variation | All-profile collar | Aperture |
| **AIP** | U2 | Incidence allocation; towers; atomic stability; horizon structure | Shared budget; archimedean payment at the spacing; base | Aperture; spacing; overlap; base; gauge |
| **ACS** | U2/U3 | Hodge index; counting; deformations; two forms; field; renormalization; atomic resolution | A form positive and equivariant; selective count; full ceiling; spacing; base | Carrier; aperture; Lefschetz; gauge; inertia; field; spacing; overlap; base; count |

### Candidates and PW-B

All are U3 unless noted. Each lacks the forcing law of §2.

| Candidate | Family | Common face | Missing construction |
|---|---|---|---|
| **APF** | U3 | Cycle-trace reconstruction | Annihilation of the off-line component |
| **BSH** | U3 | Mate curvature | Pre-divisor section |
| **CDC** | U3 | Confluence | Descending potential |
| **DR** | U1/U3 | Dyadic roots | Global monodromy |
| **EGC** | U1/U3 | Enclosed-pole cancellation | Exterior contour sign |
| **EWJ** | U3 | Finite jets | Norm exhaustion |
| **FEL** | U1/U3 | BSY contrast, a depth capacity | Upper bound forcing it to zero |
| **HJ** | U3/U2 | Residual = SEC charge = HCF grids | Stabilization weld |
| **IRK** | U3 | Completed relation | Arithmetic lift |
| **MSC** | U3/U2 | Squarefree source | Sonin landing |
| **PCS** | U3 | Shift plus defect | Wall annihilation |
| **PTR** | U3 | Lossless products | Nonlocal port |
| **RFHM** | U3 | Full-support admission | Phase-sensitive law |
| **SC** | U3 | Wall-singular fibres | Cross-fibre index |
| **SEC** | U3 | Seam compactness | Pre-divisor compactness |
| **W1C** | U3 | Centred Lee–Yang limit | Arithmetic couplings |
| **WBF** | U3 | Genealogy completion | Arithmetic stream |
| **PW-B** | U3/U1 | Positive-damping action | Pre-divisor form; zero-damping landing |

## 4. Exact common currencies

### 4.1 Width (U1 and multiplicative forcing)

For `0 < θ ≤ 1/2`, `Θ ≤ 1 − θ` is equivalent to each of [L/S]: escaped Möbius pairings `O(M^{−θ+ε})` uniformly in `N, a, b`; the dyadic pairing; receiver damping rate `≤ 1/2 − θ`; the all-test Hecke cap at depth `1/2 − θ`; dyadic Hecke growth at rate `1 − 2θ`; `Re ξ′/ξ ≥ 0` on `Re s > 1 − θ`; prefix readings `O(n_k^{2(1−2θ)+ε})` on the dyadic schedule; and to the graded lag, spline, deficit, band, series, half-plane, Suzuki, JAS, Vaughan, Lefschetz, tensor-loss and section-supply statements. The terminal ceiling of depth `a` is the strip of width `a`. VK is the strongest unconditional point; `θ(4/3) = 1/8` names the target `Θ ≤ 7/8`.

### 4.2 The common Weil form (U2)

| Statement | Relation | Qualification |
|---|---|---|
| Two forms | `Re W = D − Δ`; RH ⇔ `W = D` | Every compact `C²` test. |
| Equivariance | RH ⇔ `M_f = 0` ∀`f` | `E_f ≍ M_f`. |
| Gårding; index | Fewer than `2AT₀K/π` negative directions | Every aperture. |
| Ground | RH ⇔ `μ > 0` at every `A` | Relaxation on the prime ladder. |
| Lefschetz | One or two primes; one shift; symmetric squares | Local part positive. |
| Local–global | `P = Σ_p L_p`, each bounded | No ceiling; square-root price. |
| Tower coordinates | `Re W = E_φ\|x\|² + polar − ΣK_φ − ‖φ‖²Σ_pQ_p` | Log-atom tests below the spacing. |
| Atomic resolution | `arch − prime ≥ 0`; `Re W + 2S² ≥ 0` | Width `≤ N^{−O(1)}`; shared by every twin. |
| Elliptic sectors | Twisted positivity below the horizon | Forcing gap. |
| Gauge windows | Twins negative at `181/500`, `23/40` | Liouville permanently. |
| Short cycles | `Re W(g − T_{log 2}g) ≥ ‖·‖²/1000` | Even `g`, support `≤ 181/500 − (log 2)/2`. |
| Averaged and statistical | Positive on `Γ^{99/100}` windows; proportions; census | Averages only. |

### 4.3 Geometric and counting currency (U2 ↔ U3)

On every polar surface section count, effectivity, naive and convex heights are each the Hodge index; for `ζ` each is RH. Over `𝔽_q` effectivity and naive heights hold; purity by counting. The Weil sign, Hodge index, effectivity, heights, budget sufficiency, the equivariance of `D`, `M_f ≡ 0`, zero transverse energy, no right terminal, every right-zero field `≤ 1`, every unit window below two quanta, positive chirality and the central ceilings at every ordinate, and the tower-coordinate Hodge index at every width are the same statement.

### 4.4 Ground rate and clustering

`Δ ≤ polarRate = groundRate ≤ 1/2`, with equality without clustering; form-norm rates equal `Δ`.

### 4.5 Depth on the divisor

The BSY functional, `Δ`, `M_f` and `𝓔` vanish exactly on critical zeros; the Hecke defect is `≍ M_f`, computed from `ξ`; two scales determine the depth dispersion; uniform caps are strips. Diagnostics read depth; none forces it to vanish.

### 4.6 Invariants, capacity, contraction, collision, deformation

Rigidity `CompletedPositiveSystem 1 d = ℝ^× · ζ`; capacities (boundary, collar, gauge, family, `ζ^d`, packets, lattice clouds); one section decides; contraction and collision classified; deformations per-ordinate, quantized, irreversible.

### 4.7 The gauge currency

| Statistic | Gauge behaviour | Consequence |
|---|---|---|
| Multiplicative moments, family averages | Invariant | Source up to its orbit. |
| Square-class couplings | Blind | Cannot separate `ζ` from `λ`. |
| Finite intersection of torsion orbits | Unitarily conjugate under `x ↦ ωx` | Every local or global bound shared by twins. |
| Atomic-resolution Weil forms | Prime parts conjugate; forms differ by `A(f⁺ + f⁻) − A(f⁺ − f⁻)`; on nonnegative tests `ζ` is the orbit minimum (`2Λ(p)/√p` at a flipped prime) | Stability law holds for every twin; the margin is on the wrong side. |
| Successor couplings; successor connection | Charged | Reconstruct `ω(2), ω(3)`. |
| Cell dilations | Covariant only at Euler; defect `≥ 2·#charged cells`, `≥ X^{1/4}` | Gauge fixing, not positivity. |
| Renormalized source `ωΛ₂` | Gap `2 log² p` at the smallest flipped prime, on every window | Coefficient margin, not form margin. |
| Electrostatic energy and field | Invariant under the archimedean twist | First charge invisible. |
| Weil form at `181/500`, `23/40`, `2 log 2` | Reads atom `2`, then `2, 3`, then the nine-modulus collar | Twins negative where `ζ` is positive. |
| Overlap-width Weil forms | Read non-ratio lags `log k` | Where selectivity must enter (Q2). |

### 4.8 The local-type currency

| Correspondence | At an off-line pair | On the line | Invariant positivity forces |
|---|---|---|---|
| Hecke `T_p`, archimedean flow, gauge twist | Boost | Rotation | Isotropy |
| Symmetric dilation by `a` | Boost unless `γ log a ∈ πℤ` | Rotation | Fibre zero |
| Symmetric square | Non-real or negative spectrum | Nonnegative | `Re ρ = 1/2` at one prime |
| `1 − T_p^N` | Never annihilates | On a lattice of heights | Nothing off the line |
| `σ_γ` | Swap | Swap | Odd sector: vanishing |
| Rotation `R_ζ` of the circle | — (acts on `ℚ/ℤ`) | — | Archimedean spectrum only |
| Successor | Unipotent | Unipotent | Nothing |

### 4.9 The pairing currency

| Object | Pairing | Positivity |
|---|---|---|
| Kernel and coupled counts; escape forms; `D` | `ρ ↔ ρ̄` | Automatic |
| `W`; Rosati trace; zero-ordinate moments | `ρ ↔ 1 − ρ̄` | ⇔ RH (for all tests or polynomials) |
| Torsion energies | Conjugation = power map `−1` | Automatic at `r < 1`; lost in the limit |
| Field; transverse energy | Cauchy kernel | Quantized; outward at terminals |

### 4.10 The budget currency

| Row | `ℤ` | `𝔽_q` |
|---|---|---|
| Prime error | budget ⇔ RH; Abel slope ⇔ RH + simple | slope `Σ mult(β)²` |
| Mertens | budget ⇒ RH + simple + summable residues | repulsion energy; strict Hasse |

### 4.11 The renormalization currency

| Statement | Content |
|---|---|
| Log-orders | `I(m, mt) = φ(m)Λ(t)`; `Λ(n) = log #(𝒪/(ζ_n − 1))` |
| Self-intersection | `c(n) = Σ (a − 1/(p − 1)) log p`; dominates each tower above level two |
| Survival law | Limit `≥ 0` exactly on the counterterm's null cone |
| Regulators | Abel: identity, `{0}`; spacing: scalar, covariant up to tame, indefinite; horizon: polar on uniform profiles, identity on torsion orbits, unbounded rank; lattice germ: `𝟙𝟙ᵀ`, polar hyperplane |
| Partner rank | Prime survival `≤ rank` of the partner's counterterm; periodic coupling: `ℝe₁` |
| Twins and pole node | Per-order relations; `−φ(m)Λ(t)` at pole nodes; full-rank divergence relocated to infinite node height |
| Covariance | Diagonal covariant ⇔ scalar; covariant counterterm `log N + O(1)`; torsion counterterm `≥ (3/2) log N − C` |
| Anomaly | `β(n, t) = log t − Σ log p/(p − 1)`; Weil's prime sum drops the diagonal |
| Duality | Gauss's digamma theorem; rotations' spectrum archimedean |
| Archimedean payment | Self-energy `log(1/w) + O(1)` pays the finite intersection below the spacing |
| Over `𝔽_q` | Diagonal `2 − 2g`, finite; one Frobenius ladder |

### 4.12 The electrostatic currency

| Quantity of `log\|ξ\|` | Computed by | RH form | Unconditional |
|---|---|---|---|
| Laplacian | `D` | `D` Hecke invariant | log-Sobolev; uniform defect caps are strips |
| Moment of inertia | `E_f ≍ M_f` | `M_f = 0` ∀`f` | Stieltjes moments; soft amplification |
| Field | Laurent coefficient of `(ζ′/ζ)²` | right-zero field `≤ 1`; no right terminal | outward at terminals |
| Energy | source work of `Λ ⋆ Λ` | `𝓔 = 0` ⇔ `𝓔 < 1` | `𝓔 < ∞` ⇔ finite index; one zero `≤ 16(C + log γ)` |
| Reflection pairing | explicit formula | `W ≥ 0` | finite negative index |

### 4.13 The alignment currency

| Entrance | What an off-line zero forces | Missing exclusion |
|---|---|---|
| `σ_γ`-odd detector beyond the conductor | A sign of a prime polynomial of length `(log γ)^{O(1)}` | Interior alignment law |
| Outward reserve | `Re(ζ′/ζ + Γ) ≥ c·a·log γ` on a zero-free ray | Upper bound for the smoothed prime sum there (W10) |
| Field threshold | Field `≥ √(2c log γ)` at some right zero | A non-uniform upper bound |
| Exterior field | Anti-alignment at `σ > 1` [L] | Continuation inside |
| Alignment counts | — | They bound frequency only [L] |
| Collective packets | Independent ordinates buy the pole share | Commensurability |

### 4.14 The spacing-scale currency

| Quantity at width `w` with `N` atoms | Size | Status |
|---|---|---|
| Finite intersection `P_N` | `≤ (log N + log 4 + 4)\|x\|²`, `≥ (log N − log 8 − 4)` on the pole vector, `≥ (log N − C)` on valuation classes | [S] |
| Archimedean self-energy `E_φ` | `log(1/w) + O(1)` (corpus bound with constant `e^{−1/2}`) | [L]/[R] |
| Archimedean cross kernel `K_φ` | Positive, `≈ w·2√(mn)·n/((n − m)(n + m))`; Hilbert-type `c/\|n − m\|` near scale `N` at `w = cδ_N` | [R] |
| Polar pairing | Rank two, signature `(1, 1)` | [L] |
| Gauge dependence | None below `δ_N`; non-ratio lags above | [L]/[R] |
| Dirichlet polynomials | `T ≍ 1/w`; at `w ≍ 1/N`, the Montgomery–Vaughan regime `T ≍ N` | [R] |

### 4.15 Currencies that stay separate

| Currency | Exact result | Not identified with |
|---|---|---|
| Li reciprocal depth | `≤ 1/431` | `Δ` |
| De Bruijn–Newman constant | `0 ≤ Λ < 1/8` (corpus normalization) | `Δ` |
| HF ceiling exponent | `Δ ≤ θ* ≤ Δ/2 + 1/4` | `Δ` |
| Packet vs Weil energy; `𝓔` vs `𝓔_copy` | `m²` vs `m` | Each other without simplicity |
| Trace-bounded vs operator-norm positivity | RH vs RH + simple | Each other |
| Coalescent surplus; census | `3/4` problems | RH |
| Collided form | Conjugate pairing | Rosati degree |
| Conductor horizon | `e^a ≲ log γ/4` | Forcing threshold |
| Mertens budget | RH + simple + summable residues | RH |
| Torsion energy at `r < 1`; local tower form | Positive; bounded | Weil positivity; the global form |
| Atomic positivity | Below the spacing | Positivity at the spacing |
| Coefficient gauge margin | `2 log² p` | Form margin |
| Alignment counts; reserves | Frequency; detection | Exclusion |

## 5. Interfaces

| Interface | Proved | Missing |
|---|---|---|
| WL ↔ AE ↔ ACP (counting, budgets) | One-sided count, horizon torsion, Farey, prime-error budget ⇔ RH | A signed count; an actual budget |
| MC ↔ BVI ↔ RBG ↔ ACG (width) | Width currency; VK decay; prefix readings | A fixed power saving |
| MC ↔ PM ↔ BVI ↔ ACCE | Energy brackets; bands; Kloosterman dispersion | Signed long-modulus quadrature |
| PM ↔ ADR ↔ ACP ↔ ACG ↔ PL | Escape alternative; atoms; gauge mass | Exterior tightness; positive gauge mass |
| PM ↔ SSA ↔ THIM; PM ↔ CTF | Half damping bounded; residual identity | Sub-half signed interior |
| RW ↔ SZ ↔ CHMD | Sign transfer | Sign |
| RW ↔ SRT ↔ ACS | One rate currency | Clustering |
| HF → AIP ↔ ACS | Ceiling ⇒ allocation ⇔ strict RR | The inequality |
| HF ↔ SRT ↔ ACS (Lefschetz) | One or two primes; symmetric squares | The Lefschetz part |
| HF ↔ ACS ↔ AE (counting) | Six currencies | A selective count |
| HF ↔ ACS ↔ PL ↔ CDG ↔ AES (two forms) | `Re W = D − Δ`; `E_f ≍ M_f`; uniform caps are strips | A non-uniform bound on `M_f` |
| HF ↔ ACS ↔ AES ↔ ACP (field) | Field computed; thresholds; terminals; Harnack; energy of a zero | A non-uniform field bound |
| HF ↔ ACS ↔ AIT ↔ RBG ↔ RAPT (renormalization) | Regulator table; partner rank; covariance; anomaly cost; twins | A covariant regulator with a null cone; the base |
| AIP ↔ AIT ↔ AES ↔ RAPT (spacing scale) | Prime functional = finite intersection; tower coordinates; stability law; `Re W + 2S² ≥ 0`; matched constants | Joint estimate at `cδ_N`; the overlap regime (Q1) |
| SRT ↔ OWU ↔ PL ↔ CDG ↔ AES (alignment) | Detector = odd sector; horizon; forcing gap; reserve; exterior field; alignment counts; Rosati moments | Interior anti-alignment; extinction (Q3) |
| OWU ↔ PL ↔ ACP ↔ BGG ↔ SP ↔ RBG ↔ AES (gauge) | First windows; square-class blindness; cells; source margin; atomic invisibility | A form margin at overlap widths (Q2) |
| ACS ↔ MPG ↔ SBWF ↔ U1 | Boundary forcing; collars; `κ = 1` | Better growth or a non-multiplicative mechanism |
| ACS ↔ ACP ↔ PL ↔ BGG ↔ RBG (one variable, deformations) | Calculi classified | The full-class ceiling |
| ACS ↔ APD ↔ ACP (carriers) | Isotropy; boost and resonance laws | A non-multiplicative localizer |
| ACG ↔ MC ↔ TTPC ↔ SSA ↔ BGG | A.e. laws; charged boundaries; coalescent surplus as gauge charge | A gauge-charged estimate at `0` |
| AE ↔ RHTower (`𝔽_q`) | Hyperelliptic RH by counting; completion | A period at the arithmetic point |
| WL ↔ ACS ↔ TTPC ↔ AES (windows, census) | Averaged positivity; census; quantization; alignment counts | Selection; `3/4` |
| LA ↔ WD ↔ ALDG | Repair; collision–index bridge | Residual heat region |
| HJ ↔ HCF ↔ SEC; BAG ↔ SRT; APT → RW/EWU/ACT/AIP; AOG → HF/ACS/SRT; PTR ↔ W1C | As in the frontier map | Unchanged |

## 6. Consequences

1. **Count each producer once.**
   - a small-damping signed budget, equivalently positive gauge mass: PM, CTF, BVI, MC;
   - the positivity of the equivariant form: RW, SZ, CHMD, OWU, EWU, ACT, AIP, HF, TT, ACS, SRT;
   - a residual heat-region sign: LA, WD, TH, HCF;
   - a forcing law into the maximal blind ideal: TG, RN, ACS, HF and all candidates;
   - **archimedean payment at the spacing scale and into the overlap regime**: AIP, HF, ACS (and, through the tower-coordinate form, every U2 route);
   - a gauge form-margin at overlapping widths: OWU, EWU, AIP, ACS, MC, PM;
   - an interior anti-alignment law with exceptional-set extinction: SRT, OWU, HF, ACS;
   - a non-uniform bound on `M_f` or the field: HF, ACS;
   - an actual linear budget: WL, MC.
2. **Finished below RH strength:** reformulation; carrier maximality; local-type classification including rotations; the forcing gap; invariants; packets and lattice clouds; budgets; contraction, collision, deformations; escape; counting; the computation of `D` and `M_f` and the strip character of uniform caps; local detection; electrostatic forms and the energy of a zero; alignment frequencies; zero moments as Rosati pairings; renormalization of the prime place under every tested regulator; coupling of the torsion block; covariance of diagonal counterterms; archimedean payment below the spacing; local Hodge index and its failure to sum; gauge-charged couplings and the source margin; the width currency; the census. New equivalent endpoints, graded readings, prime-only renormalizations, couplings of the torsion block, atomic-resolution positivities, coefficient margins, alignment counts, detectors and counting reformulations add nothing.
3. **The three families reduce to three constructions and one law.**
   - **U1 — an interior anti-alignment law** with extinction of the exceptional set; non-graded outputs (non-isolation).
   - **U2 — the positivity of `W` at every width**, approached from below through the spacing scale and the overlap regime, with a gauge-selective margin.
   - **U3 — a form positive and equivariant at once**: archimedean payment beyond the spacing, a base across the ladders, or a non-uniform field bound.
   - **The common law:** arithmetic forces the zero spectrum to be elliptic — conjugation and the functional-equation reflection agree on the zeros. It appears as rate zero (U1), positivity of `W` (U2), `M_f = 0`, zero transverse energy, no right terminal (U3), and — in tower coordinates — as the archimedean place paying the prime place at every width.
4. **Where the families meet: one scale.** Below the spacing of the atoms the archimedean self-energy pays the finite intersection (U2/U3), the gauge cannot favour `ζ` (U1/U3), and tests see no zeros; at the spacing the leading constants match; beyond it the atoms overlap, non-ratio lags carry the gauge, and tests see zeros up to height `≍ N` — the regime of mean values of Dirichlet polynomials at `T ≍ N`, where the alignment counts of U1 also live [R]. The conductor horizon and the square-root threshold are the same phenomenon in the aperture and moment variables.
5. **Partial progress is family-specific.** U1 is blocked at quasi-RH and has frequency bounds at zero ordinates; U2 has windows, short cycles, local parts, averages, the census, twisted positivity, the forcing half, permanent separation from Liouville, and atomic positivity; U3 has computed positive forms, quantized electrostatics, the full regulator table and its no-gos, the source margin, and the classification of charged couplings. A result converting one family's progress into another's would be a mechanism: atomic positivity pushed through the spacing (U2 → U3), a gauge margin carried by an overlap form (U1 → U2), or alignment counts turned into exclusion by an interior law (U1 → U3).
6. **Fourteen obstructions are common to every mechanism tested.** Depth homogeneity; gauge invariance (square class, finite intersection, atomic positivity shared by every twin); hyperbolicity; Landau–Fejér positivity and dilution; deformation rigidity; the counting law; the survival law; the regulator law; the partner-rank law; the covariance law; the local–global law; the detection law; the strip law (uniform ceilings are strips); and the statistics law. Collided positivity escapes the first seven and sees nothing; Rosati positivity sees everything and is RH; the archimedean self-energy at atomic resolution comes closest — positive, covariant, coupled through a rank-one pole counterterm, and unselective only because it stops below the spacing. Over `𝔽_q` a polarization of `C × C` with one Frobenius ladder makes positivity and equivariance one; over `ℤ` none is known. The [summary](obstacles-summary.md#4-would-the-b-tier-obstacles-require-a-new-field-of-mathematics) describes what such a structure must satisfy.
