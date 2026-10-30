# Research routes and their mathematical obstacles

Status: 30 October 2026, corpus `12ba3d87c6` plus working tree. **RH is open.**

Scope: the 32 live routes and 17 candidates of the [frontier map](../rh-current-frontier-map.md), the PW-B branch of PM, and the theory programmes that carry their own RH receivers without a map entry (§7).

Companions: [summary and next questions](obstacles-summary.md) · [walls ledger](walls-ledger.md) · [route unification](route-unification-ledger.md) · [scoped no-gos](../rh-killed-routes.md). Research record: [working log](../../../logs/review-3010-rev5-facts-2026-10-30.md), whose §4 lists the proof-read declarations. No builds or axiom audits were run.

## The frontier in eight sentences

- **The classical layer is formalized unconditionally:** Guth–Maynard large values, Vinogradov–Korobov, ≥ 0.6725 of zeros simple and critical, 0 ≤ Λ_dBN < 1/8, and in every dyadic window either ≥ 3/4 of the zeros are critical or a positive proportion are simple off-line zeros within A/log T of the line.
- **Weil positivity is proved in three regimes beyond the literature:**
  - below a fixed fraction of the atom spacing, for ζ and every sign twin, on every C² test supported near the logarithms log n;
  - for the complete prime/Gamma/polar atomic matrix at every fixed overlap c, selectively (the Liouville twin and every cofinite flip fail);
  - on fixed conductor packets up to overlap (log N)^{1/19}.
- **At fixed overlap the complete Weil matrix is a solved operator:** its low spectrum lives on Ramanujan conductor modes, with eigenvalues the completed conductor energies E_m(c), each an explicit nonnegative Fourier tail.
- **RH is that same positivity on an RH-complete schedule:** c_N⁴/log N → ∞ for every C² profile, or every bounded multiple of c*_N ≍ L(log L)² (L = log log N) for a logarithmic Denjoy–Carleman profile. At c*_N the margin of the form equals its synthesis error.
- **The receiver dictionary is saturated.** Every route ends at an exact RH equivalence, and whole classes of certificates are proved to collapse onto the same targets.
- **Three properties are forced on any crossing input** (walls ledger): critical (valid at zero margin), square-root precise, and selective at the trivial gauge point.
- **Two structural facts locate the remaining work:**
  - The explicit formula computes only the reflection-paired form W, never the same-point form S.
  - Every quantitative obstruction inside the complete matrix sits at a cutoff edge (horizon, top band, Euler head) and is paid, where it is paid, by the pole.
- **No route has an input with all three properties.** About two thirds lack criticality, a quarter lack precision, the rest lack selection.

## How to read this report

Evidence labels:

- **[L]** integrated, **[K]** individual Lean with standard axioms, **[S]** unintegrated Lean, **[P]** paper only, following the frontier map.
- On recent modules, [S] means: statement and proof read in source, integration not checked.
- **(inference)** marks a conclusion of this review.

**Obstacle classes.**

- **A — just work.** The mechanism exists in the corpus and has succeeded on a smaller instance. Examples: a finite certificate, a formalization of a paper proof, finishing a module whose ingredients are proved, an assembly of proved theorems, the quantification of a qualitative proof. An A item never promises a sign beyond its stated range.
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
| Zero-free region | Vinogradov–Korobov; uniform Dirichlet region except real exceptional zeros; conductor-uniform log-derivative and Perron contours | [L]; [S] |
| Critical line | `simple_critical_proportion_ge_67250071`; `three_quarters_or_simple_offLine_near_line` | [L] |
| Heat flow | `newmanConstant_lt_eighth`; heated zeros real and simple beyond 2π exp((2/3+ε)/t) | [L] |
| Heat depth law | With D(y) = #zeros of depth > y: every t-uniform bound B on the zeros of H_t of height ≥ h has D(2h) ≤ B, and D(h/2)/(2h²) is such a bound; deep zeros in [X, 2X] number ≤ C log X·N(t) for t ≤ δ²/(C log⁴X) | [S] |
| Sub-spacing positivity | `weilQuad_atomicTest_nonneg` at width ≤ c★/N, every N, every completely multiplicative sign twin [L]; Weil ≥ 0 on every C² test supported in ⋃_{n≤N}[log n, log n + w], w ≤ K★δ_N (`eventually_weilQuad_nonneg_of_support`) [S] | [L]; [S] |
| Small support | Full Weil floor ≥ mass/5000 through radius 181/500, where prime 2 is visible | [L] |
| Complete matrix, fixed c | Positive definite, one horizon for all 0 < c ≤ K, bottom E₁(c), attained at the pole conductor; also for every C² profile without real Fourier zeros | [K]/[L] |
| Conductor spectrum | E_m(c) = 2/(Mφ(m)) Σ_{(k,m)=1}(m/k)∫_{kc/m}^∞ \|φ̂(2πt)\|² dt ≥ 0; low spectrum spanned by Ramanujan modes; residual on each mode = the upward prime defect | [K]/[L]; [S] |
| Index | κ(K_ζ) = 2·#(sector zeros); finite κ ⟺ finite off-line support ⟺ bounded heat counts ⟺ all zeros above some height critical; two primes carry the whole index | [K]/[S] |
| Selection | Simple-pole completed positive class is ζ; Hecke state on Aff(ℚ) is PD ⟺ s ≥ 1/2, absolutely continuous over torus Haar ⟺ s > 1/2; twin defect = successor-disagreement shells | [L]; [S] |
| Two readings | Collided (same-point) form = limit of integer theta-prefix readings; RH ⟺ Weil form = collided form; on Ξ, RH ⟺ the two resolvent orientations agree | [L]; [S] |
| 𝔽_q calibration | Stepanov; eventual Hasse–Weil is Hasse–Weil; unitary ⟺ collision charge < 2; golden impure datum has charge exactly 2; Frobenius conformal with factor q | [L]; [S] |

## 2. The shared object: the complete Weil matrix along the overlap axis

HF, SRT, AIP, ACS (atomic branch), SC and the AID/CACT/CAF/RAPT/SSH/TM programmes share one object: the complete atomic Weil matrix W(φ, c, N) on atoms φ((u − log n)/w), w = c/N, with all prime powers, Gamma and both poles. Its state along the overlap c:

| Regime | Status | Evidence |
|---|---|---|
| c ≤ c★ (fixed fraction of spacing) | Positive; also for every sign twin, so the one-positive-square structure is **not selective**; the Metzler sign is (Liouville fails it) | [L]; [S] |
| Fixed c | Positive definite, selective against Liouville and cofinite flips; single prime flips need c₀(p) with (p/log p)^{1/7} ≲ c₀(p) ≲ p^{1/7}, and each fixed c misses all large primes | [K]/[L]; [S] |
| c = (log N)^α, fixed conductor packets | Positive for α < 1/48 uniformly, α < 1/40 along schedules, α < 1/19 | [L] |
| Mass reserve | Gamma ≥ κc⁻⁷ log N − bc; W ≥ ac⁻⁷D − Cc⁹‖x‖²; negative vectors have D ≤ C′c¹⁶ | [L] |
| RH receivers | Positivity eventually in N ⟺ RH whenever c⁴/log N → ∞, for every C² profile on [0,1] with ∫φ ≠ 0 [L]; for a log-DC profile, at every Kc*_N, c*_N ≍ L(log L)² [S] | [L]; [S] |

(inference) The proved and the RH-complete regimes use different profiles. The tilted spline and the profiles without real Fourier zeros have proved fixed-c positivity. Their RH-complete overlap is (log N)^{1/4}. The Denjoy–Carleman profiles have the much smaller RH-complete overlap L(log L)², but real Fourier zeros, and no positivity at any overlap is proved for them.

**Where the loss sits.**

- **The reserve exponent.** 16 = 2 + 2·7: the archimedean part keeps a defect fraction δ ∝ c⁻⁷, and the non-ratio (shell) form and the pole moments are each paid by Young's inequality at cost ∝ c²/δ.
- **Separate shell payment.** A top-band witness shows that any separate one-sided payment of the shells costs ≥ A²/(2ε) (`TheShellsAloneCostTheSquareOfTheOverlap`) [L]. So c¹⁶ is intrinsic to paying the shells apart from the pole.
- **Joint payment on the witness.** On the same witness the two pole moments are computed exactly (`poleMoments_topWitnessVector`) [S]. The theorem that the c-linear shell and pole parts cancel to O(G(log N + c + 1)) is stated in the module's design and absent from source.
- **Defect-only capture** needs exponential cutoffs [L].
- **Conductor modes.** There the shells cancel exactly with sign: the integrality of the shift h repays log(2πc) [L].
- **Euler heads.** The sharp head edge couples details to far windows at strength √Y (`tendsto_headCoupling`) [S]. This is the mechanism by which Γ − head(p ≤ Y) acquires unbounded negative index; the capstone is absent from source.

## 3. Complete-matrix, Hodge and index routes

Format: **Path** · **Proved** · **A** (just work) · **B** (open mathematics) · **Lacks**.

#### HF — Positive Hodge form on arithmetic cohomology
- **Path:** full-source sign, zero Hecke defect or subquantum arithmetic work → Hodge index → RH.
- **Proved:**
  - §2 in full. RH ⟺ collided polarization Hecke invariant ⟺ Hecke similitude.
  - Haar branch: W + G = D_X + P + ΣV_X(a)u_a²; prime edges retain fraction 1 − log2/log3 of divisor energy; full-Weil prime-edge entries ≤ −(log3 − log2)M_b/√m [K].
  - Euler heads: cost(P) ≤ log A gives index(Γ − Euler_P) ≤ A [L]; the head edge couples at √Y [S].
  - At each prime, the matched class Hodge index: one positive square and a gap → p log p/(p − 1) (`eventually_isHyperbolic_classHodgeGram`) [S].
- **A:**
  - Finish the top-band joint shell–pole cancellation (`abs_poleRow_sub_le`, `exists_abs_jointWitnessCoefficient_le`); the pole moments and the cell-comparison lemmas are proved.
  - Finish the growing-Euler-head capstone (`eventually_eulerHead_negative_family`); the coupling limit, its negative diagonal and the triangular lower bound are proved.
  - Effective conductor confinement for finite sieve profiles at fixed c. Ingredients: the sieve spectral tail, harmonic class weights and `exists_sieveProfile_ramanujan_approximation` [L], plus the conductor-uniform Dirichlet contours [S].
  - Haar branch: first-prime, coarse and polar costs on fixed finite cells.
  - The matched class Hodge index on a finite sieve of primes. The one-prime mechanism and the exact sieve-class prime Grams exist. This is the first test of local-to-global assembly; failure is informative.
- **B:**
  - [RH] positivity at the RH-complete overlap.
  - [sub] signed joint payment of shells, Euler heads and pole off the conductor span, with defect O(log c) instead of c¹⁶.
  - [RH] Haar branch: joint payment of the non-arithmetic Gamma graph and the signed diagonal V_X together with roots and poles.
- **Lacks:** C.

#### SRT — Prime-side one-parameter lag localization
- **Path:** late-lag bound, complete atomic sign, all-generator one-prime sign or consecutive-ratio tower sign → RH.
- **Proved:**
  - §2.
  - Full-index exhaustion by explicit (log log N)^α/N schedules, α > 1 [L]; at each fixed width the integer windows reach κ(K_ζ) [S].
  - The Steklov profile is RH-complete at L(log L)² log log L [K]; a log-DC profile at every bounded multiple of L(log L)² [S].
  - No compact Gevrey profile of order ≤ 1 [S].
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
- **Proved:**
  - Scaling-surface Hodge defect = #right zeros.
  - Arithmetic sections of width ≤ c★/N have Markov energy ≥ square mass; Riemann–Roch and ampleness hold on the scaling subsurface [L].
  - Sharp Adams support 2^{qr}.
  - Moment bounds certify zero location only through the depth product [L].
  - Odd Hodge index past the first prime at radius ≤ 0.362 [L].
  - Elliptic base over 𝔽₃: adeles, Haar, local integrals [K].
- **A:**
  - Automorphic branch foundations: product formula, quotient measures, Iwasawa characters, Eisenstein unfolding for the 𝔽₃ elliptic base.
  - Atomic branch: as HF.
- **B:**
  - [RH] quadratic effectivity: subquadratic h⁰ growth on degree-zero classes, or Rosati heights. Over 𝔽_q the Castelnuovo constant is 2g; over ℤ there is no finite genus.
  - [C%] census: signed Gram moments near bandwidth 1, a prime surplus ≤ N/18 or E(1/9) ≤ 4 (70%).
- **Lacks:** P.

#### SC (candidate) — Stokes/Witt–Krein cross-fibre index
- **Proved:**
  - Fine-tower and shrinking-family full-index exhaustion [L/S].
  - Finite reflection-closed spectra carry full index on distinct-prime boxes [K]; two primes carry the full index of an arithmetic Krein–Langer kernel [S].
  - Under attained maximal depth, infinitely many positive prime towers ⟺ RH [L].
- **A:** height-filtered certificate costs; effective horizons.
- **B:** [FS] source-fixed cross-fibre index ceiling; detection at unattained depth.
- **Lacks:** P.

## 4. Ground-state, Markov and operator routes

#### RW — Restricted Weil ground energy
- **Proved:**
  - μ is strictly decreasing; RH ⟺ μ(A) > 0 at every aperture.
  - μ(A) ≤ K exp((11/2)A − πe^{2(A−2)}), so any floor decays doubly exponentially.
  - An off-line zero forces a zero crossing at an aperture bounded by its visibility lag.
- **A:** further fixed-aperture floors (finite certificates).
- **B:** [RH] every aperture. Monotone continuation of positivity is excluded (extension no-go).
- **Lacks:** C.

#### EWU, OWU — Even and odd weight uniqueness
- **Proved:**
  - Even rigidity; attained blind minima.
  - RH ⟺ at every aperture some real weights make the full Weil functional nonnegative.
  - Odd witnesses separate Λ from Liouville and prime flips at radii 181/500 and 23/40.
  - The companion-forcing certificate and the conductor horizon have no common aperture.
- **A:** further fixed-radius witnesses.
- **B:** [RH] all-aperture sign with reflected-prime and polar payment; OWU needs a detector other than companion forcing.
- **Lacks:** C.

#### ACT — Arithmetic criticality / single-shift variation
- **Proved:**
  - The Markov form of Riemann's kernel in Doob coordinates; the odd form is never subcritical.
  - A folded supersolution through which every odd test factors gives RH (`riemannHypothesis_of_foldedSupersolution`) [S].
  - The archimedean place is Z-type: every obstruction to the variation inequality is prime.
- **A:** effective shift thresholds for fixed-support reflected-prime collars.
- **B:** [RH] a positive supersolution of the full nonlocal prime-jump generator.
- **Lacks:** C. This route is the cleanest statement of criticality.

#### CHMD — Causal hyperbolic–modular duality
- **Proved:**
  - Wave, Doob and nodal receivers.
  - Stopping heads obey Γ(head) + Γ(tail) ≤ (2 + 96e²)Γ(f); one cutoff makes complete even-power error ≤ δΓ(f) [K].
  - Literal prime-edge Gamma payment leaves fraction 1 − log2/log3 of divisor energy [K].
  - Finite Euler heads have explicit index budgets [L]; the head edge couples at √Y [S].
- **A:** first-prime, coarse and head payments on finite sources; the growing-head capstone (as HF).
- **B:**
  - [RH] full wave or odd/nodal sign; sign of the infinite retained orbits.
  - [sub] signed payment of heads beyond depth (log A)², jointly with poles and tails.
- **Lacks:** C.

#### SZ — Suzuki screw and shifted kernels
- **Proved:**
  - Ward-defect receiver (`riemannHypothesis_of_suzukiRectangularWardDefect_eventually_bddBelow`); ¬RH forces cofinal unboundedness below.
  - Each finite prime-power packet satisfies reflected current + negative-light Gram = positive-light Gram, both PSD.
  - Excluded: bare-source ℓ², uniform causal recovery, positive unital finite parts, and fixed-scale dressed, bounded-Gamma-observer and matched-CCM transition cores.
- **A:** none that approaches the receiver.
- **B:** [RH] a uniform lower bound after complete source assembly.
- **Lacks:** C.

#### FU, CFC, RP — CCM prime histories
- **Proved:**
  - CFC: RH ⟺ the published first-clock sine coefficient is bounded below on a tail.
  - RP: no sublinear history floor exists; RH ⟺ an eventual linear floor.
  - FU: the narrow-window prime channel is negative [L]; wide windows can be positive [S].
  - CCM: the archimedean distribution = Sonin part + square − anticommutator, as operator traces.
- **A:** low-LCM payments; narrow-window channel estimates.
- **B:** [RH] one complete-history linear floor, paying high-LCM pairs and the anticommutator term.
- **Lacks:** C.

#### PA — Prime–archimedean passivity
- **Proved:** exact trace receivers; each fixed Hausdorff order is positive beyond an order-dependent shift threshold (`riemannHypothesis_iff_forall_lt_shiftThreshold_nonneg`).
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
- **Proved:**
  - The guarded history-zero set is finite; RH ⟺ it is empty; under ¬RH the last guarded zero has odd order.
  - Cayley–Li ladder primitive sign ⟺ RH; over curves, unitarity ⟺ the Cayley ladder sign.
- **B:** [RH] the outside budget at every possible guarded zero, or the ladder sign.
- **Lacks:** C.

## 5. Prime-error, cancellation, theta and heat routes

These share the global law κ = 0 ⟺ ψ(x) − x ≤ C√x log²x [L], the deciding-input theorem (a Count-sufficient input must separate a from a + εn^{−η} for all η < 1/2) and producer blindness.

#### WL — Weil lag function
- **Proved:**
  - Critical-energy, linear prime-error and one-sided count criteria.
  - Chebyshev inversion isolates two Möbius moments, a Mertens remainder and an O(n) sawtooth.
  - Balanced factorial ratios cost (2 log 2 − ε)mn; full Adams multiplicity costs support 2^{qr}, sharply.
  - Algebraic first vertical jets detect every partial.
  - Adams operations on the gauge torus form a Λ-ring with the trivial twist as the unique ψ²-fixed point [S].
- **A:** higher-order scalar-jet transfer for general prime families.
- **B:**
  - [RH] signed prime error at √x precision.
  - [RH] parity-selective integer auxiliaries of controlled height beyond the Landau-window class.
- **Lacks:** P.

#### MC — Möbius cancellation at half power
- **Proved:**
  - θ_μ(0) = Θ = sup Re ρ; the typical exponent is 1/2; RH ⟺ the trivial point is typical.
  - Gauge-invariant majorants are ≥ 3/4 at 0.
  - The Möbius escape state on the gauge torus has coefficient −(6/π²)/(p+1) at each prime: it leans to the Liouville point, and carries no trace of the zeros [S].
  - Quadratic Dirichlet-point twins have exponent ≤ (2 + Θ)/6.
  - Normalized Chebyshev energy reduces to a nonnegative cyclotomic remainder [K]; outside the first and last K roots the remainder is ≤ 288N(N+1)/K [L].
- **A:** Siegel–Walfisz transfer for growing-modulus shells, using the conductor-uniform log-derivative and Perron contours [S].
- **B:**
  - [RH] half-power cancellation at the trivial point.
  - [QRH] a fixed strip: the 3/4 strip ⟺ near-band cyclotomic energy O(N^{3/2+ε}) at K = ⌈√(N+1)⌉, where the near modes have primitive conductor ≥ (N+1)/K [L/K].
  - [Siegel] real exceptional zeros.
- **Lacks:** S at the trivial point, and P.

#### PBM, RB — Regularized abscissa; Robin/Nicolas
- **Proved:** convergence of the pole-regularized prime or log-ζ series at every σ > 1/2 ⟺ RH; colossally abundant reduction; counterexamples need growing prime cores.
- **B:** [RH] coefficient cancellation to the critical abscissa; square-root remainders on growing extremizers.
- **Lacks:** P.

#### JAS, CTF — Joint ancestry; Báez-Duarte approximation
- **Proved:**
  - JAS: positivity at growing logarithmic prime budget.
  - CTF: exact dual completion (kernel 1/max(j,k)); Euler completion error ≤ (M + 1)²/(T + 1); the fixed-probe terminal edge is sharp.
- **A:** CTF terminal and Euler-completion bookkeeping.
- **B:** [RH] the JAS square-root budget; CTF covariance upper cancellation along compatible cutoffs. Dual completion yields lower bounds only.
- **Lacks:** P.

#### PM with PW-B — Physical-model Haar approximation
- **Proved:** RH ⟺ every escape state has positive gauge mass; compact effective-pole-order laws. PW-B: native two-response action and principal small-damping limits.
- **A:** PW-B: restate the native action on source data, removing `XiZeroCopy` indexing.
- **B:** [RH] positive gauge mass for every subcritical limit; exterior tightness against infinite-height escape.
- **Lacks:** S.

#### BAG — Deterministic self-return
- **Proved:** strong and local recurrence receivers; finite Euler returns retain zero exceptions.
- **B:** [RH] returns near every right-strip point, including possible zeros.
- **Lacks:** S.

#### TH — Theta moment positivity
- **Proved:**
  - Rank seven strict; rank eight PSD for every 0 < a < 1/2 [L].
  - Each finite native tail = twice its Gram-square mass minus twice its local flux [L].
  - Rank-N PSD reduces to positivity of the native tail.
  - Heated orthant signs hold at all ranks; all-rank signed-center positivity ⟺ RH.
- **A:** rank nine, ten, … by seam-split piece certificates.
- **B:** [RH] flux domination uniformly in rank. No rank-uniform fraction of the new diagonal survives [K].
- **Lacks:** C.

#### TT, LA, WD, HCF, GTA — Theta tails, line anchor, Ward collisions, heat trace, transverse charge
- **Proved:**
  - TT: theta tail and Wold receivers.
  - LA: ξ coefficients Turán; heated zeros real beyond 2π exp((2/3+ε)/t).
  - WD: localized dissipation through collisions and t = 0, with C log X times outer vertical energy [K].
  - WD/LA heat depth law [S]:
    - t-uniform high counts at every height ⟺ the zeros approach the line ⇒ LH;
    - deep zeros ≤ C log X·N(t);
    - N(t) ≤ At^{−a} ⇒ O((log X)^{4a+1}) zeros of depth ≥ δ in [X, 2X].
  - On real polynomials the heat flow has no depth budget: a deep pair holds a shallow pair off the axis (`not_forall_nonrealRootCount_polyHeat_le_depth`) [S].
  - HCF: positivity on both log2 and log3 grids ⟺ RH.
  - GTA: exact transverse-charge decay criterion.
- **A:**
  - State the graded heat ladder as theorems. Each rung is a corollary of `exists_card_deep_le_mul_nonrealZeroCount`. Example: N(t) ≤ exp(Ct^{−α}) with α < 1/4 gives X^{o(1)} deep zeros in [X, 2X].
  - LA, HCF: further fixed degrees.
- **B:**
  - [FS] t-uniform N(t), which is finite off-line support.
  - [sub] polynomial growth of N(t), or N(t) ≤ exp(Ct^{−α}) with α < 1/4. Known: α = 1.
  - [RH] Λ_dBN = 0; all-height low-degree signs; both grid signs at all degrees; rank-uniform transverse decay.
  - The polynomial no-go shows that a bound on N(t) must use more of Ξ than depth counting.
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
| **HKT/AKLT** Krein index | κ = 2·#sector zeros; finite-index TFAE; finite ζ index forces every single-prime flip to infinite index; sup over tests of the flip-kernel index = ∞, of ζ's = κ(K_ζ); two primes decide; higher odd moments bound inertia; local towers assemble to index 0 or ∞ [L/S] | Effective horizons for full-index schedules | [FS] κ < ∞ | P |
| **HEF** same-point sums | Every line-calibrated explicit statistic is W; holomorphic clocks have excess 0 or ∞; O ∈ 2ℕ, RH ⟺ O < 2, N ≤ N₀ + O; finite resolvent formula (σ − 1/2)S = E + D, D ≥ 0 [L]. On Ξ: the line-reflection receiver and the collision-charge endpoint [S] | Transport the finite resolvent depth formula to the Ξ divisor | [RH] a source law for the same-point side; [C%] O ≤ cN, c < 1/4 | C |
| **SSH** successor shells | Non-ratio form = finite sum of shells; continuum shells = pole charge; lattice gain log(2πc) [L]; separate payment ≥ A²/(2ε) [L]; twin defect = disagreement shells [S]; top-band pole moments [S] | Finish the top-band joint cancellation | [sub] signed shell payment off the conductor span with log c loss | C |
| **AGT** gauge torus | Coherence ‖S(x)‖ ≤ S(0); divisor collapse maximal only at 0; Liouville antipode; escape state leans to Liouville; ≥ 3/4 for gauge-invariant bounds; Adams operations [L/S] | — | [RH] point-specific cancellation at 0 | S, P |
| **APD** Aff(ℚ) positivity | Hecke state PD ⟺ s ≥ 1/2; RH ⟺ a PD function on Aff(ℚ) restricts to Weil's correlation [L]; such extensions are successor-blind and indexed by the zeros; integer successor ⟂ archimedean; Mautner rigidity [S] | — | [RH] the extension; a successor-carrying carrier beyond Aff(ℚ) | C |
| **APol/CDG** polarization | RH ⟺ W = collided ⟺ Hecke invariance; collided form and Hecke defect read from theta prefixes; Def_L ≥ 4L²·(depth second moment) [L] | Rates for the theta-prefix readings | [RH] Hecke-defect upper bound | C |
| **ALG** Lorentzian | Sub-spacing Hodge index for ζ and twins; Weil ≥ 0 on all tests near the logarithms; a uniform margin cannot reach a fixed overlap ratio; ζ Metzler, Liouville not; Frobenius conformal, Hecke a boost [L/S] | — | [RH] a conformal correspondence over ℤ | C |
| **AOG/SSIC** visibility | Orbit correlation ≤ Ke^{σt} ⟺ zero width ≤ σ; refutation finite, confirmation not; depth is the complete dilation invariant [L] | — | [RH] any subexponential orbit bound | P |
| **AES/AID** electrostatics, source work | RH ⟺ 𝓔 < 1; W(R) ≤ 64R L_R(L_R + 1) [L]; annular increment ≤ 39/50 at every R ≥ 4 ⟺ RH [S] | — | [FS] finite 𝓔; [RH] subquantum increment | C |
| **ART** resonances | Commutative vs free realization; additive ⇒ commutative; finite even and virtual realizations impossible; Hölder ⇒ strip; orthogonal families cancel their gain [L] | — | [QRH] a Hölder mixing realization; [RH] a non-envelope amplifier | P |
| **Census** IGP/TTPC | 0.6725 simple critical; 0.8876 simple-or-critical; 3/4-or-near-line; coalescent surplus reduction to the centred stabilizer discrepancy [L] | — | [C%] signed coalescent prime pairs past bandwidth 1 | P |
| **CCM / Deninger / Hedenmalm** | Weil distribution is an operator trace; complete carriers have bounded generators; the Hedenmalm reciprocal operator is self-adjoint ⟺ RH [L] | — | [RH] anticommutator sign; a carrier with unbounded generator built without zeros | C / S |

## 8. Cross-route verdict

| Missing property | Routes |
|---|---|
| **C** critical sign | HF, SRT, AIP, RW, EWU, OWU, ACT, CHMD, SZ, FU, CFC, RP, PA, TG, RN, LI, TH, TT, LA, WD, HCF, GTA, DR, EGC, MSC, PTR, W1C, HEF, SSH, APD, APol/CDG, ALG, AES/AID, CCM, Deninger |
| **P** square-root precision | ACS, WL, MC, PBM, RB, JAS, CTF, SRT (towers), SC, APF, EWJ, FEL, WBF, HKT/AKLT, AOG/SSIC, ART, census |
| **S** selection | MC, AGT, PM/PW-B, BAG, XN, BSH, CDC, HJ, IRK, PCS, RFHM, SEC, Hedenmalm |

(inference)

- **The C-routes** already have selection, from the pole, the Gamma factor and the conductor spectrum, and they work at fixed resolution. Their margin vanishes along the axis that makes them complete. The losses concentrate at the cutoff edges, where only the pole pays.
- **The P-routes** have the right counting form but no producer stronger than Chebyshev precision.
- **The S-routes** carry analytic objects that cannot tell ζ from a twin. Size statements are equal at the trivial point and its antipode.
- **The common root.**
  - HEF: every positive object the C-routes build reads the reflection-paired side, and the same-point side has no prime-side source.
  - The local-assembly law: all coupling between primes passes through the archimedean place, a rank-one channel.
