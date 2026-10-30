# Research routes and their mathematical obstacles

Status: 30 October 2026, corpus `4089dad808` plus working tree. **RH is open.**

Scope: the 32 live routes and 17 candidates of the [frontier map](../rh-current-frontier-map.md), the PW-B branch of PM, and the theory programmes that carry their own RH receivers without a map entry (§6).

Companions: [summary and next questions](obstacles-summary.md) · [walls ledger](walls-ledger.md) · [route unification](route-unification-ledger.md) · [scoped no-gos](../rh-killed-routes.md). Research record: [working log](../../../logs/review-3010-rev4-research-2026-10-30.md). No builds or axiom audits were run.

## The frontier in eight sentences

- **The classical layer is formalized unconditionally:** Guth–Maynard large values, Vinogradov–Korobov, ≥0.6725 of zeros simple and critical, 0 ≤ Λ_dBN < 1/8, and dichotomies "≥3/4 of zeros critical, or a positive proportion of simple off-line zeros within A/log T of the line".
- **Weil positivity is proved in two regimes beyond the literature:** at every fixed fraction of the atom spacing (for ζ and every sign twin), and for the complete prime/Gamma/polar atomic matrix at every fixed overlap c (selectively: the Liouville twin and every cofinite flip fail).
- **At fixed overlap the complete Weil matrix is a solved operator:** its low spectrum lives on Ramanujan conductor modes, with eigenvalues the completed conductor energies E_m(c), each an explicit nonnegative Fourier tail.
- **RH is that same positivity along c_N ≫ (log N)^{1/4}.** Proved positivity reaches fixed conductor packets up to (log N)^{1/48} uniformly, (log N)^{1/40} along schedules, (log N)^{1/19} unintegrated.
- **The receiver dictionary is saturated.** Every route ends at an exact RH equivalence; whole classes of certificates are proved to collapse onto the same targets.
- **Three properties are forced on any crossing input** (walls ledger): critical (valid at zero margin), square-root precise, and selective at the trivial gauge point.
- **The explicit formula computes one side only.** Every line-calibrated explicit statistic is Weil's reflection-paired form W; the same-point form S is read from additive (theta) data; RH is S = W.
- **No route has an input with all three properties.** About two thirds lack criticality, a quarter lack precision, the rest lack selection.

## How to read this report

Evidence labels follow the frontier map: **[L]** integrated, **[K]** individual Lean with standard axioms, **[S]** unintegrated Lean, **[P]** paper only. **(inference)** marks a conclusion of this review. Lean statements cited by name were read through the corpus search.

**Obstacle classes.**

- **A — just work.** The mechanism exists in the corpus and has succeeded on a smaller instance: a finite certificate, a formalization of a paper proof, the integration of [S] work, an assembly of proved theorems, or the quantification of a qualitative proof. An A item never promises a sign beyond its stated range.
- **B — open mathematics.** No known mechanism, in the corpus or the literature, produces the statement. Each B item carries its strength:

| Tag | Strength of the open statement |
|---|---|
| **[RH]** | Equivalent to RH. |
| **[FS]** | Finitely many off-line zeros; implies Lindelöf. |
| **[LH] / [QRH]** | Lindelöf; a zero-free strip Re s > Θ, Θ < 1. |
| **[C%]** | A critical-line proportion (70%, 75%), not RH. |
| **[Siegel]** | Exclusion of real exceptional Dirichlet zeros. |
| **[sub]** | Open estimate that implies no classical conjecture by itself. |

**The three properties** (walls ledger): **C** critical, **P** square-root precise, **S** selective. Each route lists the one it lacks.

## 1. Shared unconditional base

| Area | Result | Evidence |
|---|---|---|
| Zero density | Guth–Maynard large values; N(σ,T) ≪ T^{(30/13)(1−σ)+ε} on [1/2, 5/6]; density hypothesis on σ ≥ 5/6 | [L] |
| Zero-free region | Vinogradov–Korobov; uniform Dirichlet region except real exceptional zeros | [L] |
| Critical line | `simple_critical_proportion_ge_67250071`; `three_quarters_or_simple_offLine_near_line` | [L] |
| Heat flow | `newmanConstant_lt_eighth`; heated zeros real and simple beyond 2π exp((2/3+ε)/t) | [L] |
| Sub-spacing Hodge index | `weilQuad_atomicTest_nonneg` at width ≤ c★/N, every N; same for every completely multiplicative sign twin | [L] |
| Small support | Full Weil floor ≥ mass/5000 through radius 181/500, where prime 2 is visible | [L] |
| Complete matrix, fixed c | Positive definite, one horizon for all 0 < c ≤ K, bottom E₁(c), attained at the pole conductor | [K]/[L] |
| Conductor spectrum | E_m(c) = 2/(Mφ(m)) Σ_{(k,m)=1}(m/k)∫_{kc/m}^∞ abs(φ̂(2πt))² dt ≥ 0; low spectrum spanned by Ramanujan modes (`tiltedUnitSpline_lowSpace_near_ramanujan`) | [K]/[L] |
| Index | κ(K_ζ) = 2·#(sector zeros); finite κ ⟺ finite off-line support ⟺ bounded heat counts ⟺ all zeros above some height critical (`zetaKernel_finiteIndex_tfae`) | [L] |
| Selection | Simple-pole completed positive class is ζ; Hecke state on Aff(ℚ) is PD ⟺ s ≥ 1/2, absolutely continuous over torus Haar ⟺ s > 1/2 (`heckeState_kakutani_wall`) | [L] |
| Two readings | Collided (same-point) form is the limit of integer theta-prefix readings, uniformly in twists (`finiteThetaSource_uniform_moving_collided`); RH ⟺ Weil form = collided form (`riemannHypothesis_iff_W_eq_collided`) | [L] |
| 𝔽_q calibration | Stepanov; eventual Hasse–Weil is Hasse–Weil; unitary ⟺ collision charge < 2; golden impure datum has charge exactly 2 | [L] |

## 2. The shared object: the complete Weil matrix along the overlap axis

HF, SRT, AIP, ACS (atomic branch), SC and the AID/CACT/CAF/RAPT/SSH/TM programmes share one object: the complete atomic Weil matrix W(φ, c, N), atoms φ((u − log n)/w), w = c/N, with all prime powers, Gamma and both poles. Its state along the overlap c:

| Regime | Status | Evidence |
|---|---|---|
| c ≤ c★ (fixed fraction of spacing) | Positive; also for every sign twin, so **not selective** | [L] |
| Fixed c | Positive definite, selective against Liouville and cofinite flips; single prime flips need c₀(p) with (p/log p)^{1/7} ≲ c₀(p) ≲ p^{1/7} | [K]/[L] |
| c = (log N)^α, fixed conductor packets | Positive for α < 1/48 uniformly, α < 1/40 along schedules, α < 1/19 | [L], [L], [S] |
| Mass reserve | Gamma ≥ κc⁻⁷ log N − bc; W ≥ ac⁻⁷D − Cc⁹‖x‖²; negative vectors have D ≤ C′c¹⁶ | [L] |
| RH receiver | Positivity eventually in N ⟺ RH whenever c⁴/log N → ∞, for every C² profile on [0,1] with ∫φ ≠ 0 (`riemannHypothesis_iff_completeWeilEnergy_nonneg_of_growthTwo`) | [L] |

(inference) The 1/4 threshold is a synthesis threshold: the atomic family must approximate fixed tests with error log N/c⁴ → 0. Whether an off-line zero forces negativity at slower growth is unknown, so positivity on (log N)^{1/8} ≲ c ≲ (log N)^{1/4} has no known strength.

**Where the loss sits.** The reserve exponent 16 = 2 + 2·7: the archimedean part keeps a defect fraction δ ∝ c⁻⁷, and the non-ratio (shell) form and the pole moments are each paid by Young's inequality at cost ∝ c²/δ. A top-band witness shows that any separate one-sided payment of the shells costs ≥ κc²/ε, so c¹⁶ is intrinsic to paying the shells apart from the pole ([S], in progress: `TheShellsAloneCostTheSquareOfTheOverlap`). Defect-only conductor capture needs exponential cutoffs ([L]). On conductor modes the same shells cancel exactly with sign: the integrality of the shift h repays log(2πc) (lattice gain, [S]).

## 3. Complete-matrix, Hodge and index routes

Format: **Path** · **Proved** · **A** (just work) · **B** (open mathematics) · **Lacks**.

#### HF — Positive Hodge form on arithmetic cohomology
- **Path:** full-source sign, zero Hecke defect or subquantum arithmetic work → Hodge index → RH.
- **Proved:** §2 in full. RH ⟺ collided polarization Hecke invariant ⟺ Hecke similitude. Haar branch: W + G = D_X + P + ΣV_X(a)u_a², prime edges retain fraction 1 − log2/log3 of divisor energy, full-Weil prime-edge entries ≤ −(log3 − log2)M_b/√m [K]. Euler heads: cost(P) ≤ log A gives index(Γ − Euler_P) ≤ A [L].
- **A:**
  - Formalize the reciprocal-shell square budget c²(1 + log c) [P].
  - Integrate fixed packets below (log N)^{1/19} [S → L].
  - Assemble sieve spectral truncation, harmonic class weights and the effective Ramanujan approximation (`exists_sieveProfile_ramanujan_approximation`) into an effective conductor-confinement theorem for finite sieve profiles at fixed c.
  - Finish the separate-shell-payment floor [S].
  - Haar branch: first-prime, coarse and polar costs on finite cells.
- **B:**
  - [RH] positivity at c ≫ (log N)^{1/4}.
  - [sub] confinement of nonpositive vectors with defect O(log c) instead of c¹⁶. Separate payment is excluded, so this needs a signed joint payment of shells and pole off the conductor span.
  - [RH] Haar branch: joint payment of the non-arithmetic Gamma graph and the signed diagonal V_X together with roots and poles.
- **Lacks:** C.

#### SRT — Prime-side one-parameter lag localization
- **Path:** late-lag bound, complete atomic sign, all-generator one-prime sign or consecutive-ratio tower sign → RH.
- **Proved:** §2. Full-index exhaustion by explicit (loglog N)^α/N schedules, α > 1 [L]. A single Steklov profile is RH-complete at L(log L)² loglog L, L = loglog N [K]. No compact Gevrey profile of order ≤ 1 exists, and the receivers end at the quasi-analytic boundary [S].
- **A:** full-index exhaustion for the smaller Steklov schedule; effective detection horizons for the explicit schedules.
- **B:**
  - [RH] sign on an RH-complete family.
  - [FS] arithmetic index ceiling on prime towers.
  - Detection of unattained maximal depth.
- **Lacks:** C; P for the tower branch.

#### AIP — Arithmetic incidence positivity
- **Path:** prime incidence and plateau gauge → all-aperture GlobalIncidenceAllocation → odd positivity ⟺ RH.
- **Proved:** §2 and the Haar branch shared with HF. Signed incidence theory: frustration is the local–global gap, and the odd Weil ledger is frustrated only by primes.
- **A:** mixed Schur debit on fixed blocks from tail energy (positive-prefix Schur reduction, A ≥ I/20 [L]); Haar-branch first-prime and coarse costs.
- **B:** [RH] all-aperture allocation. Paying the prime frustration globally is the signed prime problem.
- **Lacks:** C.

#### ACS — Arithmetic Castelnuovo–Severi effectivity
- **Path:** full-source effectivity, bounded-error Rosati heights or all-ordinate chirality → Hodge index → RH.
- **Proved:** scaling-surface Hodge defect = #right zeros. Arithmetic sections of width ≤ c★/N have Markov energy ≥ square mass; the sinh-pole kernel is a source-defined subspace with Riemann–Roch and ampleness on the scaling subsurface [L]. Sharp Adams support 2^{qr}. Moment bounds certify zero location only through the depth product (`MomentBoundsCapTheOffLineDepth`). Elliptic base over 𝔽₃: adeles, Haar, local integrals [K].
- **A:**
  - Automorphic branch foundations: product formula, quotient measures, Iwasawa characters, Eisenstein unfolding for the 𝔽₃ elliptic base.
  - Atomic branch: as HF.
- **B:**
  - [RH] quadratic effectivity: subquadratic h⁰ growth on degree-zero classes, or Rosati heights. Over 𝔽_q the Castelnuovo constant is 2g; over ℤ there is no finite genus.
  - [C%] census: signed Gram moments near bandwidth 1, a prime surplus ≤ N/18 or E(1/9) ≤ 4 (70%), or a displacement-sensitive slack bound near λ = 1 (75%).
- **Lacks:** P.

#### SC (candidate) — Stokes/Witt–Krein cross-fibre index
- **Proved:** fine-tower and shrinking-family full-index exhaustion [L/S]; finite reflection-closed spectra carry full index on distinct-prime boxes [K]; under attained maximal depth, infinitely many positive prime towers ⟺ RH [L].
- **A:** height-filtered certificate costs; effective horizons.
- **B:** [FS] source-fixed cross-fibre index ceiling; detection at unattained depth.
- **Lacks:** P.

## 4. Ground-state, Markov and operator routes

#### RW — Restricted Weil ground energy
- **Proved:** μ strictly decreasing; RH ⟺ μ(A) > 0 at every aperture. μ(A) ≤ K exp((11/2)A − πe^{2(A−2)}), so any floor decays doubly exponentially. An off-line zero forces a zero crossing at an aperture bounded by its visibility lag (`groundEnergyCrossing_le_visibility`).
- **A:** further fixed-aperture floors (finite certificates).
- **B:** [RH] every aperture. Monotone continuation of positivity is excluded (extension no-go).
- **Lacks:** C.

#### EWU, OWU — Even and odd weight uniqueness
- **Proved:** even rigidity; attained blind minima; RH ⟺ at every aperture some real weights make the full Weil functional nonnegative. Odd witnesses separate Λ from Liouville and prime flips at radii 181/500 and 23/40. The companion-forcing certificate and the conductor horizon have no common aperture (`TheConductorForcingGap`).
- **A:** further fixed-radius witnesses.
- **B:** [RH] all-aperture sign with reflected-prime and polar payment; OWU needs a detector other than companion forcing.
- **Lacks:** C.

#### ACT — Arithmetic criticality / single-shift variation
- **Proved:** the Markov form of Riemann's kernel in Doob coordinates; the odd form is never subcritical; folded supersolutions would give RH, and no positive profile is one. The archimedean place is Z-type: every obstruction to the variation inequality is prime.
- **A:** effective shift thresholds for fixed-support reflected-prime collars.
- **B:** [RH] a positive supersolution of the full nonlocal prime-jump generator.
- **Lacks:** C. This route is the cleanest statement of criticality.

#### CHMD — Causal hyperbolic–modular duality
- **Proved:** wave, Doob and nodal receivers. Stopping heads obey Γ(head) + Γ(tail) ≤ (2 + 96e²)Γ(f); one cutoff makes complete even-power error ≤ δΓ(f) [K]. Literal prime-edge Gamma payment leaves fraction 1 − log2/log3 of divisor energy [K].
- **A:** first-prime, coarse and head payments on finite sources.
- **B:** [RH] full wave or odd/nodal sign; sign of the infinite retained orbits.
- **Lacks:** C.

#### SZ — Suzuki screw and shifted kernels
- **Proved:** Ward-defect receiver; ¬RH forces cofinal unboundedness below. Each finite prime-power packet satisfies reflected current + negative-light Gram = positive-light Gram, both PSD. Bare-source ℓ², uniform causal recovery and positive unital finite parts are excluded.
- **A:** none that approaches the receiver.
- **B:** [RH] a uniform lower bound after complete source assembly.
- **Lacks:** C.

#### FU, CFC, RP — CCM prime histories
- **Proved:**
  - CFC: RH ⟺ the published first-clock sine coefficient is bounded below on a tail.
  - RP: no sublinear history floor exists; RH ⟺ an eventual linear floor.
  - FU: narrow-window prime channel negative [L]; wide windows can be positive [S].
  - CCM: the archimedean distribution = Sonin part + square − anticommutator, as operator traces.
- **A:** low-LCM payments; narrow-window channel estimates.
- **B:** [RH] one complete-history linear floor, paying high-LCM pairs and the anticommutator term.
- **Lacks:** C.

#### PA — Prime–archimedean passivity
- **Proved:** exact trace receivers; each fixed Hausdorff order positive at large shift.
- **A:** further fixed orders.
- **B:** [RH] all orders and shifts at once.
- **Lacks:** C.

#### TG — Topological sub-unit gate
- **Proved:** winding, cubic transgression and central-gap receivers.
- **B:** [RH] matrix-complete decomposition with nonnegative residual and integer trace < 1 on every disc.
- **Lacks:** C. Integrality enters only after the sign.

#### RN — Theta renewal
- **Proved:** compact cone-positive renewal operator with exact regularized determinant; native unregularized synthesis has a topology obstruction.
- **B:** [RH] directed mixed prime + Gamma ≥ pole. Cone positivity does not give real spectrum.
- **Lacks:** C.

#### LI — Paired Li and prime–Gamma balances
- **Proved:** the guarded history-zero set is finite; RH ⟺ it is empty; under ¬RH the last guarded zero has odd order. Cayley–Li ladder primitive sign ⟺ RH [S].
- **B:** [RH] the outside budget at every possible guarded zero, or the ladder sign.
- **Lacks:** C.

## 5. Prime-error, cancellation and theta routes

These share the global law κ = 0 ⟺ ψ(x) − x ≤ C√x log²x [L], the deciding-input theorem (a Count-sufficient input must separate a from a + εn^{−η} for all η < 1/2) and producer blindness.

#### WL — Weil lag function
- **Proved:** critical-energy, linear prime-error and one-sided count criteria. Chebyshev inversion isolates two Möbius moments, a Mertens remainder and an O(n) sawtooth. Balanced factorial ratios cost (2log2 − ε)mn; full Adams multiplicity costs support 2^{qr}, sharply. Algebraic first vertical jets detect every partial.
- **A (tractable):** higher-order scalar-jet transfer for general prime families.
- **B:**
  - [RH] signed prime error at √x precision.
  - [RH] parity-selective integer auxiliaries of controlled height beyond the Landau-window class.
- **Lacks:** P.

#### MC — Möbius cancellation at half power
- **Proved:** gauge exponent θ_μ(0) = Θ = sup Re ρ; typical exponent 1/2; RH ⟺ the trivial point is typical; gauge-invariant majorants are ≥ 3/4 at 0. Quadratic Dirichlet-point twins have exponent ≤ (2 + Θ)/6. Normalized Chebyshev energy reduces to a nonnegative cyclotomic remainder [K].
- **A:** Siegel–Walfisz transfer for growing-modulus shells.
- **B:**
  - [RH] half-power cancellation at the trivial point.
  - [QRH] a fixed strip: the 5/6 strip is equivalent to the cyclotomic-remainder bound R = O(N^{5/3+ε}), the 3/4 strip to R = O(N^{3/2+ε}) [K].
  - [Siegel] real exceptional zeros.
- **Lacks:** S at the trivial point, and P.

#### PBM, RB — Regularized abscissa; Robin/Nicolas
- **Proved:** convergence of the pole-regularized prime or log-ζ series at every σ > 1/2 ⟺ RH; colossally abundant reduction; counterexamples need growing prime cores.
- **B:** [RH] coefficient cancellation to the critical abscissa; square-root remainders on growing extremizers.
- **Lacks:** P.

#### JAS, CTF — Joint ancestry; Báez-Duarte approximation
- **Proved:**
  - JAS: positivity at growing logarithmic prime budget.
  - CTF: exact dual completion (kernel 1/max(j,k)); Euler completion error ≤ (M + 1)²/(T + 1); fixed-probe terminal edge sharp.
- **A:** CTF terminal and Euler-completion bookkeeping.
- **B:** [RH] JAS square-root budget; CTF covariance upper cancellation along compatible cutoffs. Dual completion yields lower bounds only.
- **Lacks:** P.

#### PM with PW-B — Physical-model Haar approximation
- **Proved:** RH ⟺ every escape state is visible; compact effective-pole-order laws. PW-B: native two-response action and principal small-damping limits.
- **A:** PW-B: restate the native action on source data, removing `XiZeroCopy` indexing.
- **B:** [RH] positive gauge mass for every subcritical limit; exterior tightness against infinite-height escape.
- **Lacks:** S.

#### BAG — Deterministic self-return
- **Proved:** strong and local recurrence receivers; finite Euler returns retain zero exceptions.
- **B:** [RH] returns near every right-strip point, including possible zeros.
- **Lacks:** S.

#### TH — Theta moment positivity
- **Proved:** rank seven strict; rank eight PSD for every 0 < a < 1/2 [L]. Each finite native tail = twice its Gram-square mass minus twice its local flux [L]. Heated orthant signs at all ranks; all-rank signed-center positivity ⟺ RH.
- **A:** rank nine, ten, … by seam-split piece certificates.
- **B:** [RH] flux domination uniformly in rank. No rank-uniform fraction of the new diagonal survives [K].
- **Lacks:** C.

#### TT, LA, WD, HCF, GTA — Theta tails, line anchor, Ward collisions, heat trace, transverse charge
- **Proved:**
  - TT: theta tail and Wold receivers.
  - LA: ξ coefficients Turán; heated zeros real beyond 2π exp((2/3+ε)/t).
  - WD: localized dissipation through collisions and t = 0, with C log X times outer vertical energy [K]; collision mass → ∞ as t ↓ 0 ⟺ unbounded tower indices.
  - HCF: positivity on both log2 and log3 grids ⟺ RH.
  - GTA: exact transverse-charge decay criterion.
- **A:**
  - WD: absorb the outer vertical energy and sum the localized estimates at each fixed t > 0.
  - LA, HCF: further fixed degrees.
- **B:**
  - [FS] uniform N(t) as t ↓ 0. By `zetaKernel_finiteIndex_tfae` this is finite off-line support, hence LH.
  - [RH] Λ_dBN = 0; all-height low-degree signs; both grid signs at all degrees; rank-uniform transverse decay.
- **Lacks:** C.

#### XN — Newton discs
- **Proved:** coverage criterion; nonnegative Laplacian of the interior margin.
- **B:** [RH] cover every zero by line-centered discs with nonnegative margin.
- **Lacks:** S.

## 6. Candidates

All candidates have proved receivers and lack an independent source mechanism [map].

| Candidate | A | B | Lacks |
|---|---|---|---|
| **APF** paired Fredholm | — | Zero-independent divisor exhaustion [RH] | P |
| **BSH** mate curvature | — | Pre-divisor section and mate identity on actual Ξ zeros [RH] | S |
| **CDC** constitutive dagger | — | Source potential forcing confluence at actual zeros [RH] | S |
| **DR** dyadic roots | Capped-atlas extensions | Global strict-right roots and monodromy [RH] | C |
| **EGC** pole-safe contour | — | Outer contour sign beating the Gamma floor [RH] | C |
| **EWJ** Euler/Wold jets | — | Zero-independent norm exhaustion [RH] | P |
| **FEL** theta likelihood | — | Cofinal balance from a predeclared source [RH] | P |
| **HJ** Hurwitz reflection | — | Residual vanishing forced at actual zeros [RH] | S |
| **IRK** rotation trace | — | Arithmetic projective lift with integral count [RH] | S |
| **MSC** Möbius–Sonin | — | Source-faithful bridge to a nonnegative Sonin energy [RH] | C |
| **PCS** singular co-shift | — | Source-natural wall annihilation [RH] | S |
| **PTR** photonic source | — | Prime-faithful zero-loss nonlocal port [RH] | C |
| **RFHM** support grade | — | Symmetry-breaking wall law [RH] | S |
| **SC** Witt–Krein | Effective horizons | Cross-fibre index ceiling [FS] | P |
| **SEC** prime seam | — | Exact eventual compactness at actual zeros [RH] | S |
| **W1C** Lee–Yang | — | Source couplings converging to Riemann's measure [RH] | C |
| **WBF** source certificates | — | Arithmetic certificate stream with uniform completion [RH] | P |
| **PW-B** cusp forcing | Remove `XiZeroCopy` indexing | Complete-energy ceiling and all-divisor extinction [RH] | S |

## 7. Theory programmes that act as routes

| Programme | Decisive results | A | B | Lacks |
|---|---|---|---|---|
| **HKT/AKLT** Krein index | κ = 2·#sector zeros; finite-index TFAE (bounded heat counts, eventual criticality); finite ζ index forces every single-prime flip to infinite index; atomic pole indices of ζ and Liouville differ by exactly one square in an explicit window [L] | Effective horizons for full-index schedules | [FS] κ < ∞ | P |
| **HEF** same-point sums | Calibration rigidity: every line-calibrated explicit statistic is W; holomorphic clocks have excess 0 or ∞; collision charge O ∈ 2ℕ, RH ⟺ O < 2, N ≤ N₀ + O; resolvent formula (σ − 1/2)S = E + D, D ≥ 0, on finite configurations [L] | Resolvent formula on the full Ξ divisor (absolute convergence) | [RH] D(s) or O(T) from arithmetic; [C%] O ≤ cN, c < 1/4 | C (no source for S) |
| **SSH** successor shells | Non-ratio form = finite sum of shells on the top band; continuum shells = pole charge; lattice gain = log(2πc) − β/M + o(1) [S] | Finish the separate-payment floor; the reciprocal-shell budget | [sub] signed shell payment off the conductor span with log c loss | C |
| **APD** Aff(ℚ) positivity | Hecke state PD ⟺ s ≥ 1/2 (Kakutani wall); RH ⟺ a PD function on Aff(ℚ) restricts to Weil's correlation; extensions classified [L] | — | [RH] the extension | C |
| **APol/CDG** polarization | RH ⟺ W = collided ⟺ Hecke invariance; collided form and Hecke defect read from theta prefixes; Def_L ≥ 4L²·(depth second moment) [L] | Rates for the theta-prefix readings | [RH] Hecke-defect upper bound | C |
| **ALG** Lorentzian | Sub-spacing Hodge index for ζ and twins; Ramanujan and Lorentzian meet only at the Weil bound [S]; trickle-down = count | — | [RH] | P |
| **AOG/SSIC** visibility | Orbit correlation ≤ Ke^{σt} ⟺ zero width ≤ σ; refutation finite, confirmation not; depth is the complete dilation invariant [L] | — | [RH] any subexponential orbit bound | P |
| **AES/RBG** electrostatics | RH ⟺ ℰ < 1; W(R) ≤ 64R L_R(L_R + 1) [L]; annular increment ≤ 39/50 at every R ≥ 4 ⟺ RH [S] | — | [FS] finite ℰ; [RH] subquantum increment | C |
| **ART** resonances | Paper only: commutative vs free realization, unique factorization forbids additive concatenation, Pisot and Cunningham obstructions, Pollicott strip bridge, orthogonal families cancel their gain [P] | Formalize the realization obstructions and the rank law | [QRH] a Hölder mixing realization; [RH] a non-envelope amplifier | P |
| **CCM / Deninger / Hedenmalm** | Weil distribution is an operator trace; complete carriers have bounded generators; covariant aggregation cannot select the line [L] | — | [RH] anticommutator sign; a carrier with unbounded generator | C / S |

## 8. Cross-route verdict

| Missing property | Routes |
|---|---|
| **C** critical sign | HF, SRT, AIP, RW, EWU, OWU, ACT, CHMD, SZ, FU, CFC, RP, PA, TG, RN, LI, TH, TT, LA, WD, HCF, GTA, DR, EGC, MSC, PTR, W1C, HEF, SSH, APD, APol/CDG, AES/RBG, CCM, Deninger |
| **P** square-root precision | ACS, WL, MC, PBM, RB, JAS, CTF, SRT (towers), SC, APF, EWJ, FEL, WBF, HKT/AKLT, ALG, AOG/SSIC, ART |
| **S** selection | MC, PM/PW-B, BAG, XN, BSH, CDC, HJ, IRK, PCS, RFHM, SEC, Hedenmalm |

(inference) The C-routes already have selection, from the pole, the Gamma factor and the conductor spectrum, and they work at fixed resolution; their margin vanishes along the axis that makes them complete. The P-routes have the right counting form but no producer stronger than Chebyshev precision. The S-routes carry analytic objects that cannot tell ζ from a twin. HEF explains the shared root of the C-routes: every positive object they build reads the reflection-paired side, and the same-point side has no prime-side source.
