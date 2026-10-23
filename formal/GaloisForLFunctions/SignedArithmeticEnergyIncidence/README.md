# Signed Arithmetic Energy and Incidence (`GaloisForLFunctions.SignedArithmeticEnergyIncidence`)

**One question.** How does exact multiplicative incidence constrain signed quadratic energies across
scale — and which of those constraints survive a change of coordinates, a regularization, or a
completion?

Signed arithmetic energy and incidence (SAEI) is the interface theory of the corpus's critical
energy programmes. It owns no critical form of its own. It studies four operations used in
arguments about these forms: **paying** a signed form out of local resources, **completing**
it in a new norm, **transporting** it along a parameter, and **decomposing** its adverse sequences.
The programme proves sharp laws in finite or Hilbert-space settings and develops their arithmetic
applications through: the prime lag charges of
`ArithmeticIncidencePositivity`, the damped Möbius source and its damping chain of
`BezoutValuationIncidence`, and the continuation criterion of
`ArithmeticContinuationAndCriticalEnergy`. Every statement is unconditional and names its source,
its domain, its norm and its parameter range.

---

## Place in the research

SAEI studies three transfers on the critical arithmetic form: signed incidence into a shared
budget, a source expansion into its receiver norm, and a parameter path into a continuation bound.
The finite and Hilbert-space theorems specify when those transfers preserve information. Applying
them to the whole arithmetic source still requires estimates uniform in the growing cutoff.

The central examples are concrete. A balanced finite sign pattern makes positivity equivalent to
local allocation; a frustrated pattern may require a global square. The damped Möbius source is
the orbit of `1/k` under the centred arithmetic chain, and admission means that this orbit lies in
`ℓ²`. Its residue modes have norm `≍ d^{−1/2}`, so their absolute triangle-inequality sum converges
exactly above half damping. Backward operator stability fails, leaving source-specific cancellation
as the continuation problem.

| Programme | Connection |
|---|---|
| [Arithmetic Positivity Theory](../arithmetic-positivity-theory/README.md) | Supplies full-source positivity and finite Schur reductions; SAEI checks the norm and polar terms preserved by those reductions. |
| [Bi-Scale Uncertainty](../BiScaleUncertainty/README.md) | Supplies tests and countermodels for claims that recovery or restricted positivity controls a complete source. |
| [Trans-Horizon Incidence Mechanics](../TransHorizonIncidenceMechanics/README.md) | Preserves finite arithmetic incidence and boundary terms before the horizon limit. |
| [Bézout–Valuation Incidence](../BezoutValuationIncidence/README.md) | Supplies the compact `c₀` damping chain, entrance law and dense residue modes; SAEI identifies the source orbit and the receiver norm. |
| [Arithmetic Criticality Theory](../ArithmeticCriticalityTheory/README.md) | Supplies continuum ground-state transforms. SAEI's finite signed transform separates a positive supersolution from a valid payment certificate. |
| [Square-Root Threshold](../SquareRootThreshold/README.md) | Supplies width and floor dictionaries; SAEI's polynomial companion model explores how signed sampling might improve an unsigned depth estimate. |
| [Arithmetic Incidence Positivity](../ArithmeticIncidencePositivity/README.md) | Supplies strips, prime charges and shared surplus; local allocations prevent double spending, while sine trains sharpen finite first-lag capacities. |
| [Arithmetic Continuation and Critical Energy](../ArithmeticContinuationAndCriticalEnergy/README.md) | Supplies admission and its exact signed averaged criterion; SAEI identifies the radial loss and the source orbit it measures. |
| [Scale-Signed Incidence Criticality](../ScaleSignedIncidenceCriticality/README.md) | Supplies the language of readings and their limits; each SAEI obstruction names the information a proposed estimate discarded. |
| [Arithmetic Compensation Theory](../ArithmeticCompensationTheory/README.md) | Keeps mixed source terms and recovery in the continuation budget; its comb laws explain why large quadratic majorants need not imply large signed charge. |
| [Arithmetic Castelnuovo–Severi](../ArithmeticCastelnuovoSeveri/README.md) | Supplies the hyperbolic pole plane and Cartesian prime incidence; SAEI computes payment costs and finite train capacities on related forms. |
| [Trans-Threshold Pair Correlation](../TransThresholdPairCorrelation/README.md) | Shares the Dirichlet-polynomial mean value theorem at its diagonal `X ≍ T`: the half-damping bound for the chain cuts the dilation symbol there, and TTPC's Frobenius analysis starts there. Below half damping SAEI's obstruction is `1/ζ` inside the strip, not a prime-pair sum. |
| [Arithmetic Orientation Theory](../ArithmeticOrientationTheory/README.md) | Attaches an integer frustration index and a frustration mass to the switching class of a signed form. The ground energy is bounded by the mass and vanishes on connected patterns exactly at balance. The prime triangle of mechanism 14 has index exactly `2`, and its frustration mass is bounded by the positive prime-sum couplings. |

**The shared target.** The programmes in the table work on RH as the sign of one critical
arithmetic form and on the critical cancellation of the actual source. SAEI is the interface layer
between them: it decides which transfers — payment, completion, transport, decomposition — preserve
the signed information an argument needs, and it supplies the nonlocal payment method (canonical
paths) and the receiver-norm operator theory of the damping chain on which the incidence and
continuation faces depend.

Start with signed incidence and comparison positivity, then chains and train capacities. For
continuation, read the receiver-orbit identity before residue modes and their summation threshold.
The profile and sampling theorems are abstract tools with separate arithmetic realization problems.
Every proposed application must name its source, domain, norm, observation, retained signed terms,
parameter range and order of limits.

---

## 1. Why: motivation

**A critical form is a signed incidence form.** Read conductance by conductance (AIP), the zero
form of `ζ` is a quadratic form whose off-diagonal charges sit on pairs of points coupled by
divisibility, by products of prime powers, by the archimedean density and by the pole. Read strip
by strip, the global incidence allocation is a family of overlapping local positive pieces that
must be paid from one surplus. Read along the damping, the critical energy is the norm of a source
that moves under an arithmetic Markov semigroup. In each reading a closing argument has to turn a
*signed* object into a *bound* without losing the sign structure, and each reading has its own way
of losing it.

**Signed is substantive.** Replacing a signed ledger by magnitudes is the most common loss, and its
price is now exact:

- in the damping reading, the coefficient-envelope triangle inequality over the residue modes admits the source
  above half damping and has no finite bound at or below it (`summable_signBlind_iff`, `admits_of_signBlind`), and the series with all
  Möbius signs replaced by `+1` has infinite receiver energy at every damping `0 < ε ≤ ½`
  (`not_summable_positiveTwin`). This twin replaces the coefficients, including Möbius zeros;
  it is a counterexample for the class `|a_d| ≤ 1`, not a proof about every conceivable reading
  of `|μ|`. The actual Möbius source is admitted at `ε=½` by the corpus's separate endpoint argument;
- in the incidence reading, replacing the sign pattern of the overlaps by its absolute values turns
  a frustrated pattern into a balanced one, and the theorems of §3 show that this is exactly where
  local payment stops being lossless.

**Incidence is substantive.** Whether a positive form can be paid locally depends on budgets, magnitudes and signs. The **uniform guarantee over all magnitudes**
has a sign-pattern classification: on a complete overlap pattern, local
payment is lossless for *every* positive form realizing the pattern exactly when every triangle of
the pattern is unfrustrated (`localPayment_lossless_iff`), and on an arbitrary pattern exactly when
every closed walk is aligned (`localPayment_lossless_iff_alignedCycles`). The holonomy of a cycle is
computed from the source before any profile or gauge is chosen. Density statistics of the overlaps do not
determine it.

**Across scale is substantive.** The damping is the time of the chain: the damped Möbius source is
the orbit `η ↦ C_η(1/k)` of the compact centered semigroup (`centeredOperator_orbit`). Continuation
to smaller damping is backward evolution, and the semigroup has no uniform backward stability estimate in either
`c₀` or `ℓ²` (`not_backward_stable_l2`, `not_backward_stable_c0`). Every continuation
estimate must therefore use the source vector and its arithmetic.

---

## 2. What: objects and language

| Object | Meaning | Lean |
|---|---|---|
| Signed incidence form | symmetric coupling `c : ι → ι → ℝ` on a finite set, energy `Σ c_ij f_i f_j` | `incidenceEnergy`, `IsSymmetricCoupling` |
| Budget, overlap charge | diagonal `c_ii`; off-diagonal `c_ij` | — |
| Local allocation | shares `a_ij ≥ 0` with `c_ij² ≤ a_ij a_ji` and `Σ_{j≠i} a_ij ≤ c_ii` | `PairAllocation`, `LocallyPayable` |
| Aligned pattern | every overlap charge `≤ 0` | `HasNonpositiveOverlaps` |
| Switching, balance | `c ↦ s_i s_j c_ij`, `s_i = ±1`; balanced if some switching aligns | `switchCoupling`, `IsBalanced` |
| Coupling action, ground-state transform | `(Cv)_i = Σ_j c_ij v_j`; `E(vg) = Σ v_i (Cv)_i g_i² − ½ Σ c_ij v_i v_j (g_i − g_j)²` | `couplingAction`, `incidenceEnergy_mul_eq` |
| Triangle holonomy | `c_ij c_jk c_ki`; switching invariant | `triangleHolonomy` |
| Walk, walk holonomy | points each distinct from and overlapping the previous; product of edge signs `−c_xy/\|c_xy\|` | `IsWalkFrom`, `edgeSign`, `walkHolonomy`, `HasAlignedCycles` |
| Compatible form | overlap charges are nonnegative multiples of a sign pattern `σ` | `SignCompatible` |
| Cycle witness | unit budgets, charge `t` along a cycle, oriented by `σ` | `cycleWitness` |
| Mirror ledger, even and odd folds | translation charges `−w(u − u')` at `±p_x`; the half-line forms seen by even and odd profiles | `mirrorCoupling`, `evenFold`, `oddFold` |
| Prime kernel | `Σ_n Λ(n) n^{−½} [e^{\|u\|} = n]` | `primeKernel` |
| Half-sine | `sin((2i+1)π/(2k))`: positive on the cycle, antiperiodic, the ground state of a frustrated cycle | `halfSine` |
| Sign pattern, realization | symmetric `σ_ij = ±1`; `c` realizes `σ` if `c_ij σ_ij > 0` | `SignPattern`, `Realizes` |
| Rank-one charge | `w_i w_j`, the square of `Σ w_i f_i` | `rankOneCoupling` |
| Comparison form | same budgets, overlap charges `−\|c_ij\|` | `comparisonCoupling` |
| Frustrated triangle | unit budgets, charge `κ` on three pairs | `triangleCoupling` |
| Chain | budgets `d_k`, overlap charges `e_k` between `k`, `k+1` | `chainCoupling`, `chainEntry` |
| Running sign | switching that aligns a chain | `chainSign` |
| Sine gauge of a train | `sin((k+1)π/(n+2))` | `trainSine` |
| Amplitude train | `Σ_{k ≤ M} f_k g(· + kL)` | `amplitudeTrain` |
| Grid train | amplitudes on `(M+1) × (N+1)`; row/column charges and mass | `gridRowCharge`, `gridColCharge`, `gridMass`, `productSine` |
| Cartesian product of forms | overlaps along one factor at fixed other coordinate | `cartesianCoupling` |
| Polar form | `E_c(f) − (Σ g_i f_i)²` | `polarForm` |
| Envelope class, residue series | `\|a_d\| ≤ d^{−ε}`; `Σ_d a_d v_d(n)` | `DampedCoefficients`, `residueSeries` |
| Polar defect form | `‖v‖² − Σ_j ⟪g_j, v⟫²` | `polarDefectForm` |
| Reciprocal observable | `1/k` on the positive states, as a `c₀` vector | `reciprocalObservable` |
| First state, dyadic difference | `e₁`; `D_η(m) = P_η(m) − 2^{−η} P_η(⌊m/2⌋)` | `firstState`, `dyadicDifference` |
| Centered damping chain | BVI's `C_η` on `c₀`, state `n + 1` at index `n` | `BezoutValuationIncidence.arithmeticDampingCenteredOperator` |
| Residue mode | `v_d(n) = ⌊(n+1)/d⌋/(n+1) − 1/d` | `BezoutValuationIncidence.normalizedResidueMode` |
| Residue term, positive twin | `μ(d) d^{−η} v_d(n)`; `Σ_d d^{−ε} v_d(n)` | `residueTerm`, `positiveTwin` |
| Signed energy on a Hilbert space | `⟪T u, u⟫`, `T` symmetric | `signedEnergy`, `IsSymmetricOp` |
| Weak convergence | `⟪u_n, v⟫ → ⟪u, v⟫` for every `v` | `WeakConv` |
| Compact negativity | `Q ≥ −(finite-rank charge) − ε‖·‖²` for every `ε > 0` | `CompactlyNegative`, `finiteRankCharge` |
| Relative loss | `−2⟪u, u'⟫/(1 + ‖u‖²)` | `radialLoss` |
| Local companion form, Lagrange price | `Σ_i p(γ_i)² − w p'(t)²`; `Σ_i ℓ_i'(t)²` | `companionForm`, `lagrangePrice` |

**Words.**

- **Pay locally**: every overlap is paid by the two shares its endpoints lend it, and no point lends
  more than its budget. Nothing is spent twice.
- **Aligned, balanced, frustrated**: an overlap is aligned when its charge is `≤ 0` (it rewards
  equal values at its ends); a pattern is balanced when switching aligns all of it; a cycle is
  frustrated when no switching aligns it. On every pattern frustration is read off the closed
  walks (mechanism 10); on complete patterns the triangles suffice.
- **Holonomy**: the product of the charges around a triangle. Negative holonomy is the aligned case.
- **Supersolution**: a gauge `v > 0` with `Cv ≥ 0`. For aligned forms it is a local allocation in
  disguise (mechanism 2), and coercive aligned forms always have one (mechanism 3); a frustrated
  positive form can have no local allocation at all (mechanism 6).
- **Polar charge**: the square of one linear functional — the shape of the pole in every face of the
  critical form.
- **Receiver norm of the chain**: `ℓ²` on the chain coordinate; it is the pronic energy of the
  prefix `P = n · C r`.
- **Orbit**: `η ↦ C_η r`, the damped Möbius source as a function of the damping.
- **Sign-blind bound here**: the triangle-inequality majorant `Σ d^{−η}‖v_d‖`, using `|μ(d)| ≤ 1`.
- **Adverse sequence**: unit-bounded profiles whose energy tends to a negative value.
- **Escape**: an adverse sequence whose weak limit has nonnegative energy.

---

## 3. How: mechanisms

### Local payment and its limits

1. **Local payment implies positivity.** The energy is the unspent budget plus, over unordered
   overlaps, the binary forms `a_ij f_i² + 2 c_ij f_i f_j + a_ji f_j²`, each nonnegative when the
   overlap is paid (`incidenceEnergy_nonneg_of_pairAllocation`, `binaryForm_nonneg`). Switching
   transports allocations and positivity (`locallyPayable_switch_iff`, `nonneg_switch_iff`).
2. **Ground-state transform.** For every gauge `v`,
   `E(vg) = Σ_i v_i (Cv)_i g_i² − ½ Σ_{i,j} c_ij v_i v_j (g_i − g_j)²` (`incidenceEnergy_mul_eq`).
   A positive gauge with weighted dominance `Σ_{j≠i} |c_ij| v_j ≤ c_ii v_i` is a local allocation
   with shares `|c_ij| v_j / v_i` (`locallyPayable_of_weightedDominance`); for aligned forms this
   is a positive supersolution (`locallyPayable_of_supersolution`).
3. **Inverse positivity.** A coercive aligned form has a strictly positive solution of `Cv = 1`
   (`exists_pos_solution_of_coercive`). The solution minimizes `E(f) − 2Σ f_i`; passing to `|v|`
   does not raise the energy of an aligned form (`incidenceEnergy_abs_le`), so strict convexity
   forces `|v| = v`, and the equation at a vanishing coordinate would read `0 = 1`.
4. **Balanced incidence is locally payable.** A nonnegative aligned form is locally payable
   (`locallyPayable_of_nonneg_of_nonpositiveOverlaps`): the regularized forms `c + δ/(n+1)` have
   allocations from step 3, these lie in one compact box, and a limit point pays `c`. With
   switching, for balanced forms positivity *is* local payability
   (`nonneg_iff_locallyPayable_of_isBalanced`).
5. **A rank-one charge cannot be localized.** `(Σ w_i f_i)²` with all `w_i ≠ 0` on three or more
   points is positive and not locally payable (`not_locallyPayable_rankOneCoupling`): normalized
   shares would need `b_ij + b_ji ≥ 2` on every overlap from unit budgets, i.e. `n(n − 1) ≤ n`.
6. **The frustrated triangle.** With unit budgets and charge `κ` on all three pairs: balanced iff
   `κ ≤ 0` (`triangle_isBalanced_iff`), positive iff `−½ ≤ κ ≤ 1` (`triangle_nonneg_iff`), locally
   payable iff `|κ| ≤ ½` (`triangle_locallyPayable_iff`). The window `½ < κ ≤ 1` is positive,
   frustrated and unpayable (`triangle_frustrated_gap`); frustration halves the capacity of local
   payment.
7. **Holonomy decides balance.** On a complete overlap pattern a form is balanced iff every
   triangle has negative holonomy (`isBalanced_iff_triangleHolonomy_neg`); holonomy is switching
   invariant (`triangleHolonomy_switch`), and two sign patterns are switching equivalent iff all
   their triangle holonomies agree (`switchingEquivalent_iff_triangleHolonomy_eq`): on complete
   patterns the holonomies are the complete gauge-invariant sign data.
8. **Signed local–global principle.** For a sign pattern `σ` on a complete overlap graph, every
   nonnegative form realizing `σ` is locally payable iff every triangle of `σ` has holonomy `−1`
   (`localPayment_lossless_iff`). The converse direction is constructive: the switched triangle of
   holonomy `+1` carries the rank-one charge `¾ (s_a f_a + s_b f_b + s_c f_c)²`, and with unit
   budgets and charges `σ/(4n)` elsewhere it is a positive form that keeps a quarter of each budget
   and inherits the unpayable triangle (`frustrationWitness_nonneg`,
   `frustrationWitness_not_locallyPayable`).
9. **Local payment is positivity of the comparison form.** An allocation sees only the sizes
   `|c_ij|`; the comparison form keeps the budgets and replaces every overlap charge by `−|c_ij|`.
   A form is locally payable iff its comparison form is nonnegative
   (`locallyPayable_iff_comparison_nonneg`), the comparison form is the worst sign pattern of the
   given sizes (`incidenceEnergy_comparison_abs_le`), and for a balanced form it is a switching of
   the form (`switchCoupling_eq_comparison`). Raising every budget by `t` makes a form locally
   payable iff `E_comp(f) ≥ −t Σ f_i²` (`locallyPayable_regularized_iff`): the exact cost of local
   payment is the gap between the ground energies of the form and of its comparison form. The
   duality is explicit: a form has no allocation iff a nonnegative profile overloads its budgets,
   `Σ c_ii f_i² < Σ_{i≠j} |c_ij| f_i f_j` (`not_locallyPayable_iff_exists_overload`).
10. **Cycle holonomy decides balance on every pattern.** A walk steps along nonzero overlaps
   between distinct points; its holonomy is the product of the edge signs `−c_xy/|c_xy|`
   (`IsWalkFrom`, `walkHolonomy`). Switching multiplies the holonomy of a walk from `u` to `v` by
   `s_u s_v` (`walkHolonomy_switch`), so balanced forms have holonomy `+1` on every closed walk;
   conversely the holonomies of chosen walks from a base point of each component are an aligning
   switching. A symmetric form is balanced iff every closed walk is aligned
   (`isBalanced_iff_alignedCycles`, Harary's criterion), iff walk holonomy depends only on the
   endpoints (`isBalanced_iff_walkHolonomy_eq`). The closed triangle walk has holonomy
   `−sign(c_ij c_jk c_ki)` (`walkHolonomy_triangle`), so mechanism 7 is the complete-pattern case.
11. **Frustrated cycles spoil local payment on every pattern.** On a cycle of length `k` with
   holonomy `−1`, `4 Σ h_i² ≤ k² Σ (h_i − e_i h_{i+1})²` (`frustratedCycle_poincare`): after the
   gauge `Π_{j<i} e_j` the profile changes sign once around the cycle, so each value is half a
   signed sum of the increments. The frustrated cycle form is therefore strictly positive at the
   local-payment threshold and stays nonnegative at the charge `½ + 1/k²`
   (`frustratedCycle_energy_nonneg`, `cycleWitness_nonneg`), while no allocation pays a charge
   above `½`: each edge needs `2t` from its two shares and each point lends at most `1` to its two
   edges (`cycleWitness_not_locallyPayable`). A shortest frustrated closed walk has no repeated
   point (`exists_nodup_frustrated`). Hence, for every symmetric sign pattern `σ`, every nonnegative
   form whose charges are nonnegative multiples of `σ` (`SignCompatible`) is locally payable iff
   `σ` is balanced (`localPayment_lossless_iff_isBalanced`), iff every closed walk of `σ` is
   aligned (`localPayment_lossless_iff_alignedCycles`).
12. **The frustrated cycle is paid along its path.** Positivity of a frustrated cycle has a
   *nonlocal* certificate. In the gauge `H = v g` each edge splits as
   `2 H_i H_{i+1} = (v_{i+1}/v_i) H_i² + (v_i/v_{i+1}) H_{i+1}² − v_i v_{i+1} (g_i − g_{i+1})²`; on an
   antiperiodic profile the frustrated edge contributes `−v_0 v_n (g_0 − g_n)²`, and Cauchy–Schwarz
   along the path absorbs it once `v_0 v_n Σ_{i<n} 1/(v_i v_{i+1}) ≤ 1`
   (`antiperiodic_le_of_certificate`). The half-sine `sin((2i+1)π/(2k))` solves the signed train
   equation and has path budget exactly `1`: `1/(v_i v_{i+1})` telescopes as a difference of
   cotangents (`halfSine_telescope`). Hence a frustrated `k`-cycle has capacity exactly
   `2 cos(π/k)`: `2 Σ e_i h_i h_{i+1} ≤ 2 cos(π/k) Σ h_i²`, attained at the gauged half-sine
   (`frustratedCycle_capacity`, `frustratedCycle_capacity_attained`), and the cycle form is
   nonnegative iff `2t cos(π/k) ≤ 1` (`frustratedCycle_nonneg_iff`). The cycle witness is locally
   payable iff `t ≤ ½` (`cycleWitness_locallyPayable_iff`) and nonnegative iff `2t cos(π/k) ≤ 1`
   (`cycleWitness_nonneg_iff`): frustration costs local payment exactly the factor `cos(π/k)`, and
   `½ < t ≤ 1/(2 cos(π/k))` is the local–global window of every frustrated cycle
   (`cycleWitness_window`). For `k = 3` this is the triangle window `½ < κ ≤ 1` of mechanism 6.
13. **Frustration is paid along canonical paths.** The single-cycle certificate is one instance of
   a signed canonical-path method for any symmetric form (`PathCertificate`): a positive signed
   supersolution `v`, for every anti-aligned overlap `a, b` a walk from `a` to `b` through aligned
   overlaps with shares `λ_ab(x, y) > 0` of the overlaps it uses, the path budget
   `c_ab v_a v_b Σ_steps 1/(λ_ab |c_xy| v_x v_y) ≤ 1`, and the packing `Σ_{a,b} λ_ab(x, y) ≤ 1` of
   every aligned overlap. Cauchy–Schwarz along the path bounds each anti-aligned Dirichlet term by
   its shares (`antiTerm_le_pathEnergy`), and the packing spends no aligned term twice, so the form
   is nonnegative (`incidenceEnergy_nonneg_of_pathCertificate`). Frustrated cycles sharing edges
   compete exactly through the packing: a shared aligned overlap splits its Dirichlet energy, which
   raises the path budget of every cycle through it.
14. **Odd folding is the source of frustration.** A translation ledger charges positions `u, u'`
   by `−w(u − u')` with `w ≥ 0` even: it is aligned. Sampled at mirror points `±p_x`
   (`mirrorCoupling`), even profiles fold with charges `−w(p_x − p_y) − w(p_x + p_y)` and odd
   profiles with `w(p_x + p_y) − w(p_x − p_y)` (`incidenceEnergy_mirror_even`,
   `incidenceEnergy_mirror_odd`). Even folding never frustrates, so positive even profiles pay
   locally (`evenFold_aligned`, `evenFold_lossless`); a folded odd overlap is anti-aligned exactly
   when `w(p_x + p_y) > w(p_x − p_y)` (`oddFold_pos_iff`), so a kernel nonincreasing in `|u|`
   folds to an aligned odd form (`oddFold_lossless_of_antitone`). The von Mangoldt kernel
   `Σ_n Λ(n) n^{−½} [e^{|u|} = n]` (`primeKernel`) is sparse: at the three positions with pairwise
   sums `log 2, log 3, log 5` the differences `log(5/3), log(5/2), log(3/2)` carry no charge, all
   three folded overlaps are anti-aligned (`oddFold_primeTriangle_pos`), and the odd prime ledger
   is unbalanced for every choice of budgets (`oddFold_primeTriangle_not_isBalanced`). It carries a
   positive compatible form that no allocation pays (`exists_unpayable_odd_primeTriangle`), while
   even profiles of the prime ledger pay locally at every sampling (`evenFold_prime_lossless`).
15. **The odd Weil ledger is frustrated only by primes.** The archimedean and polar parts of the
   Weil functional combine into the weight `K(u) = 2e^{−u/2}/(1 − e^{−2u}) − 4 cosh(u/2)` of
   `RHTower.ArchimedeanWeilKernelSign` (`weilKernel`). `K` changes sign once, but it is nonincreasing on `(0, ∞)`
   (`weilKernel_antitone`): the decreasing archimedean part and the increasing polar part push the
   same way. For the sampled ledger with kernel `α K(|u|) + β · prime(u)` (`weilLedgerKernel`,
   `α, β ≥ 0`), an anti-aligned odd overlap of `x, y` forces `e^{p_x + p_y}` to be a prime power
   (`oddFold_pos_imp_primeSum`). So every frustrated closed walk passes through two consecutive
   points whose positions sum to a prime-power logarithm (`frustrated_walk_has_primeSum`), and if
   no two sample positions do, positivity on odd profiles is local payment of the fold
   (`oddWeilLedger_lossless_of_no_primeSum`). Conversely the frustration is real: the folded overlaps are affine in
   `α` (`oddFold_weilLedgerKernel`), so the prime triangle stays frustrated in the full odd Weil
   ledger for every relative archimedean–polar weight `|α| < α₀`, whatever the budgets
   (`exists_weight_oddWeilLedger_primeTriangle_not_isBalanced`).
16. **Source-faithful calibration of the prime triangle.** On actual arithmetic samplings pairwise
   overlap completeness fails — at the positions `(log 2)/2, (log 3)/2` the prime kernel vanishes at
   both `log 6` and `log(3/2)` (`not_isCompleteOverlap_oddFold_arithLogGrid`) — and a coupling whose
   off-diagonal entries are all nonnegative, one of them positive, admits no path certificate
   (`isEmpty_pathCertificate_of_nonneg_offDiag`, `isEmpty_pathCertificate_primeTriangle_primeKernel`):
   the prime kernel alone frustrates with no aligned path to pay along. At the source-faithful
   calibration `α = β = 1` the archimedean–polar kernel has the closed form
   `K(log x) = −2(x³ − x − 1)/((x² − 1)√x)` (`weilKernel_log_eq`), positive below `u₀ ≈ 0.3046` and
   negative above it. On the prime triangle the edges `(0, 1)` and `(2, 0)` turn aligned while
   `(1, 2)` stays anti-aligned, so the triangle is unconditionally frustrated
   (`oddFold_primeTriangle_weilLedgerKernel_one_not_isBalanced`), and its two aligned edges pay the
   third along `1 → 0 → 2` in the gauge `(4, 1, 1)` (`primeTrianglePathCertificate`,
   `primeTriangleCanonicalPathCertificate`, `supersolution_primeTriangleCanonical`,
   `incidenceEnergy_oddFold_primeTriangleCanonical_nonneg`). Adding a fourth position
   with a second anti-aligned prime-sum overlap, both anti-aligned overlaps route through one shared
   aligned hub edge with packed shares `½ + ½` (`packedPrimePathCertificate`,
   `packedPrimeCanonicalPathCertificate`, `supersolution_packedPrimeCanonical`,
   `incidenceEnergy_oddFold_packedPrimeCanonical_nonneg`). In general, routing a set `S`
   of anti-aligned targets from `a` through a shared first step `a → u` forces
   `Σ_{b∈S} c_ab v_b ≤ |c_au| v_u` (`packed_shared_step_gauge_lower_bound`,
   `packedPrimeCanonical_shared_step_gauge_bound`): a shared hub inflates its
   gauge, and that is how overlapping payments compete for diagonal budget.

**Positivity is decided on the frustration terminals.** A harmonic frame on a terminal set `T`
(`HarmonicFrame`: `h_τ` is the indicator of `τ` on `T` and harmonic off `T`; it exists when the form
is coercive on profiles vanishing on `T`, `exists_harmonicFrame`) splits every energy without cross
term, `E(f) = R(f) + E(f − Σ_τ f_τ h_τ)`, with the symmetric reduced coupling `R_στ = (C h_τ)_σ`
(`incidenceEnergy_eq_reduced_add`, `reduced_symm`). So `E ≥ 0` iff `E ≥ 0` on profiles vanishing on
`T` and `R ≥ 0` (`nonneg_iff_interior_and_reduced`); when `T` contains both ends of every
anti-aligned overlap the interior is aligned and its positivity is local payment
(`nonneg_iff_interior_payable_and_reduced`): all frustration lives on `T`. For one frustrated
overlap `{a, b}` of charge `t`, `R` is binary with effective budgets `α = R_aa`, `γ = R_bb` and
off-diagonal `t − β`, where `β = −Σ_{i∉{a,b}} c_ai h_b(i)` is the effective conductance of the
interior (`reduced_offDiag_eq`): the form is nonnegative iff its interior is and `(t − β)² ≤ αγ`
(`nonneg_iff_two_terminal`). The exact nonlocal price of a frustrated overlap is the effective
conductance plus the geometric mean of the effective budgets; a canonical path replaces the
effective resistance by the resistance of one path. In the odd Weil ledger the terminals are
prime-sum endpoints (`oddWeilLedger_terminal_primeSum`).

### Chains and trains

17. **Chain lending duality.** Chains are balanced, whatever the signs of their overlaps
   (`chainCoupling_isBalanced`, by the running sign `chainSign`), so a chain is positive exactly
   when it has a lending ledger: each point splits its budget between its two overlaps
   (`chain_nonneg_iff_locallyPayable`).
18. **Capacity of a uniform train.** The sine gauge solves the train equation
    `2 cos θ · v_k = v_{k−1} + v_{k+1}` with zero boundary values
    (`couplingAction_uniformTrain_trainSine`); as a positive supersolution it certifies
    `2 Σ_{k<n} f_k f_{k+1} ≤ 2 cos(π/(n+2)) Σ_{k≤n} f_k²` (`uniformTrain_capacity`), attained at the
    sine (`uniformTrain_capacity_attained`) and sharp (`uniformTrain_capacity_sharp`).
19. **The first-lag law of a train.** For `M + 1` disjoint copies of a bump at spacing `L`,
    `A_S(L) = (Σ_{k<M} f_k f_{k+1}) A_g(0)` and `A_S(0) = (Σ f_k²) A_g(0)`
    (`autoCorr_amplitudeTrain_first`, `autoCorr_amplitudeTrain_zero`, from AIP's translate
    calculus). Hence `|A_S(L)| ≤ cos(π/(M+2)) A_S(0)` (`autoCorr_amplitudeTrain_first_le`,
    `..._ge`), attained by the sine train (`autoCorr_sineTrain_first`).
20. **The resonant train is not extremal for one prime.** The unit train carries `M/(M+1)` of its
    mass at the first lag, strictly less than `cos(π/(M+2))` from `M = 2` on
    (`resonant_ratio_lt_cos`). The extremal deficit is `1 − cos(π/(M+2)) ≍ π²/(2M²)`.
21. **Two aligned towers add.** On an `(M+1) × (N+1)` grid train, the joint first-power charge of
    two primes is at most `(w_p cos(π/(M+2)) + w_q cos(π/(N+2)))` times the mass
    (`grid_joint_capacity`), attained by the product sine (`grid_joint_capacity_attained`) and sharp
    (`grid_joint_capacity_sharp`): no cross-prime cancellation on multiplicatively aligned trains.
    More generally the energy of a Cartesian product of incidence forms splits along its factors
    (`incidenceEnergy_cartesian`), lower bounds add (`cartesian_lower_bound`) and products of
    ground states attain the sum (`cartesian_attained`); iterating over a finite family of aligned
    towers, their single-tower capacities add.

**On the simplex two towers do not add.** The smooth-number train `p^j q^k`, `j + k ≤ n`, lives on
the simplex `S_n` of the exponent lattice. For equal prime weights its joint first-power charge is
at most `cos θ + cos 2θ` times its mass, `θ = π/(n+3)` (`simplex_joint_capacity`), attained by
`ψ = sin x sin y (cos x + cos y)`, `x = (j+1)θ`, `y = (k+1)θ`, the antisymmetrization of the box sine
across the cut `j + k = n + 1` (`simplex_joint_capacity_attained`, `simplex_joint_capacity_sharp`).
Each tower alone keeps the box capacity `cos(π/(n+2))` on `S_n` (`simplex_row_capacity_attained`),
and for `n ≥ 1` the joint capacity is strictly below their sum (`simplex_capacities_do_not_add`):
the hyperbola forces a cross-prime saving, deficit `≈ 5π²/(2n²)` against `π²/n²` on the box.

**Two towers add exactly on boxes.** For a support `S ⊆ [0, M] × [0, N]` and positive weights, a
constant below `w_p cos(π/(M+2)) + w_q cos(π/(N+2))` bounds the joint charge of every amplitude
carried by `S` iff `S` misses a point of the box (`joint_capacity_lt_iff_not_box`). At equality
every row and column is an extremal train, a multiple of the zero-free sine
(`uniformTrain_eq_zero_of_capacity_eq`), so a zero at a missing point empties the box
(`grid_eq_zero_of_capacity_eq`); compactness makes the gap uniform. Each tower alone still attains
its box capacity on its axis (`axisRowSine_capacity`, `axisColSine_capacity`). The smooth-number
support `j log p + k log q ≤ X` misses the corner of its box once both towers have length `≥ 2`
(`slanted_corner_not_mem`), so with the weights `Λ(p)p^{−½}, Λ(q)q^{−½}` the towers never add there
(`slanted_capacities_do_not_add`).

### Poles and completion

22. **Polar defect law.** `‖v‖² − Σ_j ⟪g_j, v⟫² ≥ 0` for all `v` iff the synthesis of the polar
    vectors is a contraction, `‖Σ c_j g_j‖² ≤ Σ c_j²` (`polarDefect_nonneg_iff`). In rank one the
    ground ratio for `g ≠ 0` is exactly `1 − ‖g‖²`, attained on `g` (`polarDefect_ge`, `polarDefect_self`,
    `polarDefect_nonneg_iff_norm_le_one`).
23. **Completion keeps the sign exactly when it keeps the polar functional.** Positivity on a dense
    set transfers to the completion for a continuous polar functional
    (`polarDefect_nonneg_of_dense`); an unbounded polar functional leaves no floor at all
    (`exists_polarDefect_lt_of_unbounded`).

**When sign changes can help.** For `Q(f)=E_c(f)−(Σg_i f_i)²`, nonpositive overlaps and
nonnegative polar weights imply `Q(|f|)≤Q(f)` (`polarForm_abs_le`): testing nonnegative profiles
already tests positivity. If `c` is coercive, solve `Cv=g`; inverse positivity gives `v≥0`, and
`Q≥0` is equivalent to `Σg_i v_i≤1` (`polarForm_nonneg_iff_polarSolution`). This supplies a
specific global polar-payment tool. A positive overlap can make an alternating two-point profile
cheaper than its absolute value (`signChange_beats_abs`), but this is a statement about the
incidence energy alone. One positive edge does not imply a frustrated cycle, and it need not
outweigh the change in the polar charge. Switching the incidence also switches the polar weights.

### The damping chain in the receiver norm

24. **The receiver is the chain orbit of the reciprocal.** `(C_η r)(n) = P_η(n+1)/(n+1)`
    (`centeredOperator_reciprocal_apply`), `C_s C_t r = C_{s+t} r` (`centeredOperator_orbit`), and
    `E_η(T) = Σ_{m<T} (m+1)/(m+2) · (C_η r)(m)²` (`dampedMobiusEnergy_eq_orbitEnergy`). Admission is
    `ℓ²`-membership of the orbit (`admits_iff_summable_orbit`); the Riemann hypothesis is the orbit
    entering `ℓ²` at arbitrarily small times (`riemannHypothesis_iff_orbit_summable`).
25. **Truncations approximate the receiver.** At every horizon the partial orbit energies of the
    finite truncations of `r` converge to those of `r` (`tendsto_truncation_partialEnergy`):
    truncations converge in `c₀` and the chain is `c₀`-continuous. So admission is decided by the
    chain on finitely supported sequences; a uniform `ℓ²` bound there would admit `η`. No such
    bound is proved below half damping, and none is assumed in a statement.
26. **The chain is Hilbert–Schmidt above damping one.** For `η > 1` the source is bounded,
    `|P_η(m)| ≤ ζ(η) + 1` (`abs_centeredPrefix_le`); in floor coordinates it is
    `Σ_{d ≤ m} μ(d) d^{−η}(⌊m/d⌋ − m/d) − m Σ_{d > m} μ(d) d^{−1−η}`. Writing `A_η = ρx + P_η`, the
    centred entry from state `n + 1` to `k + 1` is at most `2(ρ + ζ(η) + 1)(k+1)^{1−η}/(n+1)` for
    `k ≤ n` and minus the entrance mass `≤ ρ(k+1)^{−η}` beyond (`abs_centeredRow_le`,
    `entrance_le`). Every column has `Σ_n C(n,k)² ≲ (k+1)^{1−2η}` (`sum_sq_centeredRow_le`), so on
    finitely supported sequences `Σ_{n<T}(C_η b)(n)² ≤ M_η Σ b_k²` with an explicit constant
    (`centeredOperator_l2_le`).
27. **Floor jumps and the threshold `1/√2`.** Below damping one the kernel is read finely: with
    `a = ⌊N/K⌋`, `J = a − ⌊N/(K+1)⌋`, it splits into a mean-value part, a fractional part and a
    short-interval part `P(a) − P(⌊N/(K+1)⌋)`. The source is sign-blindly bounded,
    `|P_η(q)| ≤ C q^{1−η}` (`abs_centeredPrefix_le_rpow`), and its jumps cost at most `J`
    (`abs_centeredPrefix_sub_le`). Above the square root `J ≤ 1` and the jumps are sparse, one per
    quotient (`sum_floorJump_le`); below it `min(J, 2C(N/K)^{1−η})` interpolates
    (`min_le_rpow_mul_rpow`). The resulting majorant (`sq_centeredRow_le_majorant`) is square
    summable for a suitable interpolation exponent exactly when `η² > ½` (`interpExp_bounds`,
    `sum_chainMajorant_le`), so `C_η` is Hilbert–Schmidt for `1/√2 < η < 1` as well
    (`centeredOperator_l2_le_of_inverseRootTwo`).
28. **Short-interval divisor sums and the golden threshold.** The divisor structure of `c_η`
    sharpens the jump: on `(a', a]` of length `J ≤ D ≤ a`, `2J ≤ a`,
    `|P(a) − P(a')| ≤ C(D^{1−η} + J D^{−η} + a D^{−1−η})` (`abs_centeredPrefix_sub_le_short`). Divisors
    `d ≤ D` pay `D^{1−η}`; a divisor `d > D` has at most one multiple in the interval and is located by
    its quotient `⌊a/d⌋`; the signs of `μ` are not used. With `D = max(J, √a)`, below the square root
    `|P(a) − P(a')| ≤ C(J^{1−η} + a^{(1−η)/2})` (`abs_jump_le_belowSqrt`). The first term is square
    summable for every `η > ½`; interpolating the second with `J` is square summable at both ends of
    `K ≤ √N` exactly when `η² + η > 1` (`goldenExp_bounds`, `sum_belowSqrt_rpow_le`), so `C_η` is
    Hilbert–Schmidt above the golden threshold `(√5 − 1)/2`
    (`centeredOperator_l2_le_of_goldenThreshold`). The method is sharp there: for `K = N^κ` the bound
    `J` covers `κ > 1/(1+2η)`, the bound `a^{(1−η)/2}` covers `κ < η/(2−η)`, and the two meet exactly at
    `η² + η = 1`. Pointwise majorants of the kernel stop there; the Mellin reading below reaches `½`.

**The chain is Hilbert–Schmidt exactly above half damping.** With `K = k + 1`, the `k`-th column is
`C_η(n,k) = (K/N) Δ_K(N)`, `Δ_K(x) = K^{−η}P(x/K) − (K+1)^{−η}P(x/(K+1))`
(`centeredRow_eq_columnProfile`), and costs at most `8K² ∫_0^∞ Δ_K(x)² x^{−2} dx + 4K^{−2η}`
(`sum_sq_centeredRow_le_integral`). The source is the fractional-part series
`P(x) = −Σ_d μ(d) d^{−η} {x/d}` (`sourceProfile_eq_tsum`), so on `Re s = −½` its Mellin transform is
`(Σ_d μ(d) d^{s−η}) ζ(−s)/s` and `M Δ_K = (K^{s−η} − (K+1)^{s−η}) M P` (`mellin_fractSeries`,
`mellin_columnProfile_eq`). Plancherel (`integral_sq_div_sq_eq_mellin`), the dilation-symbol bound
`|K^z − (K+1)^z| ≤ 2K^{Re z}(|z|/2K)^θ` (`norm_cpow_sub_cpow_le`, `θ = ¾ − η/2`) and the dyadic
critical-line mean square give column energy `≲ K^{−½−η} ∫ |ζ(½+it)|² (2+|t|)^{−½−η} dt`. Hence `C_η`
is Hilbert–Schmidt, so `ℓ²`-bounded, for every `½ < η < 1` (`sum_sum_sq_centeredRow_le_halfDamping`,
`centeredOperator_l2_le_of_halfDamping`). The threshold is exact: the diagonal is
`C_η(k,k) ≥ (1 − ρ_η)(k+1)^{−η}` (`centeredRow_diag_ge`), so no Hilbert–Schmidt bound holds for
`0 < η ≤ ½` (`not_bounded_sum_sum_sq_centeredRow_of_le_half`). Only `|μ| ≤ 1` and the mean square of
`ζ` on the critical line enter: `½` is the sign-blind threshold, as for the residue envelope
(mechanism 35).

**The chain is bounded at half damping.** For finitely supported `b`, `(C_η b)(n) = G(N)/N` with
`G = Σ_k K b_k Δ_K` (`centeredOperator_apply_eq_combinedProfile`), so
`‖C_η b‖² ≤ 8 ∫ G² x^{−2} + 32‖b‖²` (`sum_sq_centeredOperator_le_integral`), and on `Re s = −½`
`M G = B · M P` with the dilation symbol `B = Σ_k K b_k (K^{s−η} − (K+1)^{s−η})`
(`mellin_combinedProfile_eq`). The source transform is `M P(s) = −ζ(−s)/(s ζ(η − s))`
(`mellin_sourceProfile_eq`), so `|M P(−½+it)|² ≪ |t|^{3/4} log⁴|t| / t²` uniformly in `½ < η < 1`
(`exists_norm_mellin_sourceProfile_sq_le`: convexity for `ζ(½ − it)`, `1/ζ ≪ log²` on and right of
the `1`-line). On `T ≤ t ≤ 2T` the head `K ≤ T` of `B` is a Dirichlet polynomial and the tail a
Fourier transform of a step function in `log x`, so `∫_T^{2T} |B|² ≤ 200 T(1 + log 2T)‖b‖²`
(`integral_norm_sq_dilationSymbol_shell_le`). The dyadic shells sum, uniformly as `η ↓ ½`
(`exists_centeredOperator_l2_le_uniform`), and the entries are continuous in `η`: `C_{½}` is bounded
on `ℓ²` (`exists_centeredOperator_l2_le_half`) although it is not Hilbert–Schmidt. Here the signs
of `μ` enter, as the zero-free `1`-line through `1/ζ(η − s)`; below `½` the same route needs `1/ζ`
on `Re = η + ½`, inside the critical strip.

**The receiver is continuous at half damping.** With `u_η = C_η r`, `u_η(n) = P_η(n+1)/(n+1)`
(`centeredOperator_reciprocal_eq_orbitCoord`), `u_η → u_{½}` in `ℓ²` as `η ↓ ½`
(`orbit_l2_tendsto_half`, `centeredOperator_reciprocal_l2_tendsto_half`). The orbit difference is at
most `8 ∫ (P_η − P_{η'})² x^{−2} + 4(ρ_η − ρ_{η'})²` (`sum_sq_orbitCoord_sub_le`); Plancherel makes
the integral the mean square of `F_η − F_{η'}`, `F_η(t) = −ζ(½ + η − it)^{−1} ζ(½ − it)/(−½ + it)`
(`integral_sq_sourceProfile_sub`); and since `ζ(1 − it) ≠ 0`, dominated convergence under
`|F_η|² ≪ (1 + t²)^{−9/16}` (`exists_norm_sq_criticalSymbol_le`) gives `∫ |F_η − F_{½}|² → 0`
(`tendsto_integral_sq_criticalSymbol_sub`). The positive twin does the opposite: its horizon
energies exceed every bound as `ε ↓ ½` (`positiveTwin_energy_unbounded`). Damping-summation of the
residue expansion converges in the receiver norm at the threshold where its size-only reading
diverges.

29. **The centring is indispensable in receiver coordinates.** The uncentred transition sends the
    first state to a column converging to the positive entrance mass
    (`arithmeticDampingEntrance_one_pos`), so it is `ℓ²`-unbounded at every damping
    (`not_summable_transition_first_column`).
30. **The first column of the chain is the receiver.** On the first state the centred chain is the
    dyadic difference `D_η(m) = P_η(m) − 2^{−η} P_η(⌊m/2⌋)` of the source over `m`, up to a term of
    size `1/m` (`centeredOperator_firstState_apply_eq`). The dyadic difference loses nothing in the
    receiver norm — a two-to-one count one way, the geometric inversion
    `P(m) = Σ_j 2^{−jη} D(⌊m/2^j⌋)` with a weighted Cauchy–Schwarz inequality the other
    (`summable_dyadicDifference_iff`) — so the first column lies in `ℓ²` iff `η` is admitted
    (`admits_iff_summable_firstColumn`, `riemannHypothesis_iff_firstColumn_summable`). The first
    test of `ℓ²`-boundedness of the chain is already the receiver.
31. **Residue modes are eigenmodes, with squared receiver norm `≍ 1/d`.** `C_η v_d = d^{−η} v_d`
    (`centeredOperator_normalizedResidueMode`); `(d − 1)/d² ≤ ‖v_d‖²_{ℓ²} ≤ 2/d`
    (`tsum_sq_normalizedResidueProfile_ge`, `..._le`).
32. **Backward continuation is ill-posed.** No `‖b‖ ≤ K ‖C_t b‖` holds in `ℓ²` or in `c₀`, for any
    `t > 0` (`not_backward_stable_l2`, `not_backward_stable_c0`); on `v_d` the ratio is `d^t`.
33. **Damping is strongly continuous, with an unbounded generator.** Extended by the identity at
    zero damping (`dampingFlow`), the chain is strongly continuous on `c₀`: `C_η b → b` as `η ↓ 0`
    for every `b` (`tendsto_dampingFlow`), because it converges on the dense span of the residue
    modes (BVI's `normalizedResidueMode_dense_span`) and `‖C_η‖ ≤ 2` (`tendsto_of_dense_of_bounded`).
    It is not norm continuous: `‖C_η − I‖ ≥ 1` at every positive damping
    (`one_le_norm_dampingFlow_sub_id`). Its generator acts on `v_d` by `−log d`
    (`tendsto_generator_residueMode`), so no bounded operator is the derivative of the flow at
    zero damping (`not_exists_bounded_generator`). Compact smoothing at positive time comes with an
    unbounded logarithmic generator: continuation towards zero damping has no operator-norm
    shortcut.
34. **The source is the damped Möbius residue series.** For `η > 0`,
    `(C_η r)(n) = Σ_{d≥1} μ(d) d^{−η} v_d(n)` (`centeredOperator_reciprocal_eq_tsum`), absolutely
    at every fixed coordinate (`summable_residueTerm`). Indeed `v_d(n) ≤ 0` and
    `|d^{−η}v_d(n)| ≤ d^{−1−η}`. Coordinatewise convergence is not convergence in `ℓ²`;
    the latter is precisely the critical issue below the absolute-summation threshold.
35. **The sign-blind threshold.** `Σ_d d^{−ε} ‖v_d‖_{ℓ²}` converges iff `ε > ½`
    (`summable_signBlind_iff`); above half damping the triangle inequality bounds every horizon by
    its square (`orbit_partial_energy_le`) and admits the source above half damping (`admits_of_signBlind`);
    the positive twin `Σ_d d^{−ε} v_d` has infinite receiver energy for `0 < ε ≤ ½`
    (`not_summable_positiveTwin`, via `positiveTwin_le`). Thus a uniform bound for every coefficient
    sequence `|a_d| ≤ 1` is impossible there. This obstruction does not contradict admission of
    the actual signed source at `η=½`.

**Extremality of the coefficient envelope.** For `ε>0` and `|a_d|≤d^{−ε}`, every residue mode
is nonpositive, so `|Σ_d a_d v_d(n)|≤|Σ_d d^{−ε}v_d(n)|` at each coordinate
(`abs_residueSeries_le_abs_positiveTwin`). Thus the positive twin is the extremal sign pattern
of this envelope class. Every row in the class has finite receiver energy **iff `ε>½`**
(`signBlind_admission_iff`); above the threshold one common triangle-inequality bound controls
all finite horizons (`residueSeries_partial_energy_le`). The negative half quantifies over all
rows of the envelope class, not over just the Möbius row or rows with its exact zero pattern.

### Adverse sequences

36. **Energy splitting.** For a bounded symmetric form and `u_n ⇀ u`,
    `Q(u_n) − Q(u) − Q(u_n − u) → 0` (`tendsto_energy_splitting`).
37. **Adverse profiles cannot vanish under compact negativity.** If `Q` is compactly negative, it is
    weakly lower semicontinuous along bounded sequences (`energy_le_of_weakConv`); a unit-bounded
    adverse sequence with `Q(u_n) → μ < 0` and `u_n ⇀ u` has `u ≠ 0` and `Q(u) ≤ μ ‖u‖²`
    (`adverse_weakLimit`). A form bounded below by one finite-rank charge is compactly negative
    (`compactlyNegative_of_finiteRank`). The escaping remainder `u_n − u` has eventually energy at
    least `−ε` for every `ε > 0` (`eventually_energy_remainder_ge`), so eventually
    `Q(u_n) ≥ Q(u) − ε` (`eventually_energy_ge_weakLimit`): all negative energy of an adverse
    sequence is carried by its weak limit.
38. **Escape through a noncompact negative part.** For `Q = −‖·‖²` an orthonormal sequence is
    adverse with weak limit `0` (`adverse_escape_of_orthonormal`).
39. **The critical form is compactly negative at every aperture.** At aperture `a` the corpus
    writes the restricted Weil form as `‖u‖² + ⟪R(Ju), Ju⟫` on the archimedean form domain, with `R`
    the polar and prime remainder and `J` the compact physical embedding
    (`re_ccmRestrictedWeilForm_eq`). A compact operator maps bounded weakly convergent sequences to
    norm-convergent ones (`tendsto_of_weakConvC`), so such energies are weakly lower semicontinuous
    (`compactPerturbation_le_of_weakConvC`) and their adverse sequences cannot vanish
    (`compactPerturbation_adverse_weakLimit`). For the restricted Weil form of `ζ`: a unit-bounded
    sequence with energies tending to `μ < 0` and weak limit `u` has `u ≠ 0` and `W(u, u) ≤ μ ‖u‖²`
    (`ccmRestrictedWeilForm_adverse_weakLimit`).

### Signed sampling

40. **On-line companions pay off-line depth (local model).** Near a height `t` take the source to be
    a polynomial `p` of degree `< n` (its local degrees of freedom); on-line companions at heights
    `γ_i` contribute `p(γ_i)²` and an off-line cluster of squared-depth mass `w` contributes
    `−w p'(t)²` (`companionForm`). With at least `n` distinct companions the Lagrange identity
    `p'(t) = Σ_i p(γ_i) ℓ_i'(t)` (`derivative_eval_eq_sum`) gives `Q ≥ 0` whenever
    `w Σ_i ℓ_i'(t)² ≤ 1` (`companions_pay`, price `lagrangePrice`); with two degrees of freedom
    more than companions and `t ≠ γ_i` for all `i`, `(X − t) Π_i (X − γ_i)` defeats every positive depth mass
    (`few_companions_never_pay`). Count alone is not a payment criterion: the locations determine
    the Lagrange price, which must satisfy `w Λ(t) ≤ 1`. This is a polynomial model, not an exact
    truncation of a Paley–Wiener source or of the full off-line zero form. The law transfers to an
    arbitrary source `f` at half the price: for any polynomial `p` of degree `< n`, if
    `2 w Λ(t) ≤ 1` then `Σ f(γ_i)² − w f'(t)² ≥ −(2 Σ (f − p)(γ_i)² + 4 w (f'(t) − p'(t))²)`
    (`companions_pay_up_to_error`, `sampleForm`): the signed floor of a general source costs
    exactly its local polynomial approximation error at the companions and at `t`. For a smooth
    source the Taylor polynomial at `t` reproduces `f'(t)` (`taylorPoly_derivative_eval`) and the
    two-sided Taylor bound (`abs_sub_taylorSum_le`) prices the error: with `d ≥ 2` local degrees of
    freedom, at least `d` companions within `δ` of `t` and `|f^{(d)}| ≤ M` there,
    `Σ f(γ_i)² − w f'(t)² ≥ −2 #s (M δ^d/d!)²` (`companions_pay_up_to_taylor`). For a source of
    aperture `A` — a trigonometric sum `Σ_k (a_k cos(λ_k x) + b_k sin(λ_k x))` with `|λ_k| ≤ A`, the
    shape of a Dirichlet polynomial of length `e^A` in the height — every derivative obeys
    `|f^{(d)}| ≤ A^d m`, `m = Σ_k (|a_k| + |b_k|)` (`abs_trigSourceDeriv_le`), and the loss is
    `2 #s ((Aδ)^d m/d!)²` at every height (`companions_pay_aperture`). The price is explicit in
    the companion geometry: companions `γ_0, …, γ_k` spaced by `δ` within `r` of `t` have
    `Λ(t) ≤ (k + 1)(k r^{k−1}/δ^k)²` (`lagrangePrice_le_of_separated`), so
    `2 w (k+1)(k r^{k−1}/δ^k)² ≤ 1` gives `Σ f(γ_i)² − w f'(t)² ≥ −2(k+1)((Ar)^d m/d!)²`
    (`companions_pay_aperture_explicit`).

### Continuation

41. **The radial loss law.** The relative loss `−2⟪u, u'⟫/(1 + ‖u‖²)` is the derivative of
    `−log(1 + ‖u‖²)` (`hasDerivAt_log_one_add_energy`); tangential motion is free
    (`radialLoss_add_tangential`, `radialLoss_of_inner_eq_zero`, `log_energy_eq_of_tangential`);
    `|L| ‖u‖ ≤ |⟪u, u'⟫|` and `|L| ≤ ‖u'‖` (`abs_radialLoss_mul_norm_le`, `abs_radialLoss_le`),
    so a uniform tangent bound `‖u'‖ ≤ B` gives log-energy change at most `B(c−a)`
    (`abs_log_energy_sub_le`).

---

## 4. Foundational pillar theorems

**Pillar I — the signed local–global principle.** For balanced signed incidence forms, positivity
and local payability coincide (`nonneg_iff_locallyPayable_of_isBalanced`). For aligned forms, a
positive supersolution produces a local allocation (`locallyPayable_of_supersolution`); for a
balanced form this applies after switching to aligned coordinates. On complete overlap
patterns, local payment is lossless for every positive form realizing a sign pattern iff every
triangle of the pattern has negative holonomy (`localPayment_lossless_iff`); on every pattern it
is lossless for all positive compatible forms iff the pattern is balanced, iff every closed walk is
aligned (`localPayment_lossless_iff_isBalanced`, `isBalanced_iff_alignedCycles`), and a frustrated
cycle of length `k` is positive exactly up to charge `1/(2 cos(π/k))` while local payment stops at
`½` (`frustratedCycle_nonneg_iff`, `cycleWitness_window`). For every form, local
payability is positivity of its comparison form, and the exact cost of local payment is the gap
between the two ground energies (`locallyPayable_iff_comparison_nonneg`,
`locallyPayable_regularized_iff`). A rank-one charge on three points is never locally payable
(`not_locallyPayable_rankOneCoupling`). Beyond local payment, a frustrated form is paid along
canonical paths: a positive signed supersolution, aligned walks closing every anti-aligned overlap,
path budgets and a packing of shared edges certify nonnegativity
(`incidenceEnergy_nonneg_of_pathCertificate`); at the source-faithful calibration the prime triangle
is frustrated and paid this way (`incidenceEnergy_oddFold_primeTriangle_weilLedgerKernel_one_nonneg`).

**Pillar II — the polar defect law.** The sign of `‖·‖² − Σ (polar charges)` is the contraction
property of the polar synthesis map; a completion keeps the sign iff it keeps the polar functional
continuous (`polarDefect_nonneg_iff`, `polarDefect_nonneg_of_dense`,
`exists_polarDefect_lt_of_unbounded`).

**Pillar III — the receiver as a semigroup orbit.** The damped Möbius source is the `c₀` orbit of
`1/k` under the compact centered damping chain; the critical energy is its `ℓ²` energy; admission
is `ℓ²`-membership, already equivalent to `ℓ²`-membership of the chain's first column;
truncations approximate the receiver at every horizon, the flow is strongly but not uniformly
continuous at zero damping with an unbounded generator, backward stability is impossible, and
sign-blind summation stops exactly at half damping (`admits_iff_summable_orbit`,
`admits_iff_summable_firstColumn`, `tendsto_truncation_partialEnergy`, `not_backward_stable_l2`,
`summable_signBlind_iff`, `signBlind_admission_iff`, `not_summable_positiveTwin`). In the receiver
norm the centred chain is Hilbert–Schmidt above damping one, above `1/√2`, and — through
short-interval sums of the damped divisor coefficients — above the golden threshold `(√5 − 1)/2`,
sharply for that method (`centeredOperator_l2_le`, `centeredOperator_l2_le_of_inverseRootTwo`,
`centeredOperator_l2_le_of_goldenThreshold`); in Mellin coordinates it is Hilbert–Schmidt exactly for
`½ < η < 1` (`sum_sum_sq_centeredRow_le_halfDamping`, `not_bounded_sum_sum_sq_centeredRow_of_le_half`)
and bounded at `η = ½` itself (`exists_centeredOperator_l2_le_half`); the orbit is `ℓ²`-continuous
at `η = ½` while the positive twin's energy diverges there (`orbit_l2_tendsto_half`,
`positiveTwin_energy_unbounded`).

**Pillar IV — train capacities.** A single prime's first-lag charge on a train of length `M + 1` is
at most `cos(π/(M+2))` of the mass, attained by sine amplitudes; on aligned trains the
capacities of the towers add (`autoCorr_amplitudeTrain_first_le`, `autoCorr_sineTrain_first`,
`grid_joint_capacity_attained`, `cartesian_lower_bound`, `cartesian_attained`); on the
smooth-number simplex they do not add (`simplex_capacities_do_not_add`), and in general they add
exactly on boxes (`joint_capacity_lt_iff_not_box`, `slanted_capacities_do_not_add`).

**Pillar V — profile compactness.** Under compact negativity, a weak limit of a bounded adverse
sequence remains nonzero and adverse; without it escape can occur (`adverse_weakLimit`,
`adverse_escape_of_orthonormal`). The restricted Weil form of `ζ` is compactly negative at every
fixed aperture (`ccmRestrictedWeilForm_adverse_weakLimit`).

**Pillar VI — signed sampling.** In the local model, off-line depth is paid by on-line companions
at the Lagrange price when they are at least as many as the source's local degrees of freedom, and
never when the source has two degrees of freedom more (`companions_pay`,
`few_companions_never_pay`).

**Pillar VII — the radial loss law.** Signed continuation charges only the radial rate of the
source; the tangent norm is the orientation-blind majorant (`radialLoss_add_tangential`,
`abs_log_energy_sub_le`).

---

## 5. Traps

| Trap | What is true instead |
|---|---|
| "Each atom is paid by its own strip, so the form is paid." | Own-strip payments are a local allocation only if the shares are drawn once from each budget. Overlapping strips form a signed incidence pattern; a frustrated cycle in it can make a positive form unpayable (mechanism 8). |
| "Positivity of a form implies a positive gauge." | For balanced forms positivity implies local payment (mechanism 4). Frustrated forms can be positive with no local allocation, hence with no gauge satisfying weighted dominance (mechanisms 2, 5–6). |
| Treating the pole as a local charge. | A rank-one charge on three or more points is never locally payable (mechanism 5). The pole must be paid by a global dual-norm bound (mechanism 22). |
| Reading the frustrated triangle as an artefact of equal weights. | The converse construction of mechanism 8 realizes every frustrated pattern on every complete overlap graph, and the cycle witness of mechanism 11 on every sparse pattern; the window of a frustrated `k`-cycle is exactly `½ < t ≤ 1/(2 cos(π/k))` (mechanism 12). |
| "The resonant (unit) train is the extremal adverse direction." | For several lags at once long unit trains approach the Euler envelopes; for one lag at finite length the sine train is extremal and the unit train is strictly worse from `M = 2` on (mechanism 20). |
| Expecting cross-prime cancellation on aligned trains. | On box supports the single-prime capacities add exactly, for any finite family of towers (mechanism 21); a saving comes only from the support, and every non-box support produces one (`joint_capacity_lt_iff_not_box`). |
| Taking the pronic weight on the chain coordinate as the receiver. | The receiver is `ℓ²` on the chain coordinate (mechanism 24). In the pronic weight on the chain coordinate the centring functional is unbounded below half damping (BVI); in the receiver norm the transition is unbounded and the centring is what makes the receiver possible (mechanism 29). |
| "Compactness of the chain on `c₀` gives continuation." | Compactness makes the backward problem ill-posed: no backward stability estimate exists in `c₀` or `ℓ²` (mechanism 32). |
| "Dense residue modes give a stable expansion of the source." | The modes diagonalize the chain and span `c₀` densely, but the source is a signed series in them whose sign-blind majorant converges only above half damping (mechanism 35); at half damping the damping-summed signed series is still `ℓ²`-continuous and its twin is not. |
| Bounding the relative loss by the tangent norm and calling it the criterion. | The tangent norm is the orientation-blind majorant; tangential motion is free and only the signed radial rate enters (mechanism 41). |
| "An adverse sequence has an adverse limit." | Compact negativity preserves adversity in an existing weak limit; a noncompact negative part can allow a zero limit (mechanisms 37–38). |
| Treating a frustrated pattern as a failure for every realization. | Frustration permits an unpayable positive form; sufficiently large diagonal budgets can still pay a particular frustrated form. |
| Treating a finite-dimensional duality as a cofinal certificate. | The finite theorems here have no uniformity in the number of points; transporting them to a growing arithmetic family is a separate estimate. |

---

## 6. How the interfaces constrain a research argument

**Payment must keep its quantifiers.** Balance guarantees that every nonnegative realization is
payable. Frustration supplies counterexamples to that universal guarantee; it does not classify
the actual continuum adverse profiles or force failure of every allocation. To apply the finite
law to AIP, first derive the discretized coupling, its budgets and its limiting error from the
same global form. The comparison ground energy then measures the cost of that specific allocation.

**Completion must retain the source.** For `η>0`, the centred chain acts on `c₀`; admission asks
whether its reciprocal orbit lies in `ℓ²`. This is equivalent to square summability of its first
column. An operator bound would control all finite linear combinations of columns, including their
mixed Gram terms; bounds on individual columns alone do not establish it. The residue identity
provides exact coordinates but no unconditional subhalf `ℓ²` bound.

**Continuation must allow recovery.** Once the right endpoint is admitted, ACCE's signed integrated
relative loss is equivalent to admission at the left endpoint. The radial law identifies the work
being measured. Tangent length and the positive part of the loss are stronger sufficient bounds;
Compensation Theory supplies admitted families for which positive-part budgets fail. Neither a
compact forward semigroup nor a dense eigenmode family supplies a uniform inverse estimate.

**Sampling and profile extraction need quantitative arithmetic inputs.** The polynomial companion
law requires both enough distinct nodes and a controlled Lagrange price. Actual on-line zeros need
not furnish a uniformly distributed set of companions at every height; a total zero-count average
is not that input. Compact negativity prevents a given adverse sequence from vanishing weakly,
but does not prove that its nonzero adverse limit is impossible. A positivity proof still needs an
arithmetic argument excluding that limit.

---

## 7. Questions the programme aims to answer

Each question is stated with what is established and where the open part sits.

1. **Which sign-changing odd profiles can create net unpaid prime demand after all favourable gains
   are restored?** In the finite incidence model: none on balanced patterns (mechanism 4); on
   complete patterns some positive realization is unpayable exactly when a triangle is frustrated
   (mechanism 8), and on every pattern some compatible positive form is unpayable exactly when a
   cycle is frustrated (mechanism 11). In the sampled prime ledger the frustration comes only
   from odd folding: even profiles pay locally, and three odd positions with pairwise sums
   `log 2, log 3, log 5` already frustrate it (mechanism 14). With the archimedean and polar
   weights added, every frustrated cycle passes through a pair of positions summing to a
   prime-power logarithm (mechanism 15); on aligned forms with nonnegative polar weights one-signed profiles are the worst
   case. The continuum profiles of the actual kernel, the pairs between lattice points of Arithmetic
   Incidence Positivity (its open problem 1), are open.
2. **Can those profiles be reduced to a controlled family without excessive norm loss?** Among
   trains that are products along the towers, the extremal profiles are the sine products, with
   explicit finite-length deficits (mechanisms 18–21). On the smooth-number simplex the joint
   capacity is exact and strictly below the sum of the single capacities (equal weights, paragraph
   after mechanism 21), and on every support that is not a box the joint capacity is strictly below
   that sum for all positive weights (paragraph after it). The exact joint capacity on other
   supports with the actual unequal weights is open.
3. **What signed arithmetic estimate bounds the averaged damping loss uniformly in horizon?** An
   `ℓ²` bound on the reciprocal orbit, equivalently on the first column of the chain (mechanisms
   24, 30); it must read the source rather than the operator (mechanism 32) and the signs of `μ`
   below half damping (mechanism 35). The estimate itself is open; at cofinally small damping it
   is RH.
4. **Which residue observable gives uniform actual-row cancellation?** The full residue series in
   `ℓ²` (mechanism 34). The size-only reading is extremized by the positive twin and has resolution
   exactly half damping (mechanism 35 and the envelope paragraph after it); at that resolution the
   signed orbit is `ℓ²`-continuous while the twin's energy diverges (paragraphs after mechanism 28).
   The sub-half
   cancellation is the receiver problem of Bézout–Valuation Incidence (its §7.1) in residue
   coordinates, and is open.
5. **Does the signed floor have the width rate in unrestricted `L²` without uniform unsigned depth
   mass?** In the polynomial companion model signed sampling can replace the unsigned hypothesis
   by a companion condition with an explicit Lagrange price (mechanism 40). The Paley–Wiener and
   actual-ζ transfer is open (topic 6).
6. **Which topology preserves the source normalization and the sign?** A completion keeps the sign
   exactly when it keeps the polar functional (mechanisms 22–23); for the damping chain the
   receiver topology is `ℓ²` on the chain coordinate (mechanisms 24–29), where the centred chain is
   Hilbert–Schmidt exactly above half damping and bounded at half damping. Boundedness below half
   damping is open (topic 4).
7. **Can a pre-profile orientation law force the local–global defect to vanish?** On complete
   incidence patterns the triangle holonomies are the complete gauge-invariant sign data, their
   alignment forces lossless payment and a single frustrated triangle forces a defect (mechanisms
   7–8); on every pattern the closed-walk holonomies play this role (mechanisms 10–11). Identifying the standalone candidates' seam and mate diagnostics with such holonomies is
   open.
8. **What mechanism supplies all-rank uniformity?** Compact negativity, which keeps an adverse weak
   limit nonzero and adverse, while its failure permits escape (mechanisms 37–38). The actual
   restricted Weil form is compactly negative at every fixed aperture (mechanism 39); the
   aperture-uniform version is open (topic 7).

---

## 8. The tools

| Tool | What is developed | Input → output | Failure mode and success test |
|---|---|---|---|
| Arithmetic allocation duality | Pillar I; chain lending; holonomy; comparison form; overload duality; canonical-path certificates; Kron reduction to frustration terminals | finite signed incidence ledger → local allocation, or a negative profile of the comparison form (a dual adverse profile), or a frustrated triangle; the exact budget increase that restores payment | Finite duality is not cofinal. Success: an allocation for a growing arithmetic family with losses uniform in its size. |
| Covariance continuation estimate | radial loss law; orbit reformulation; backward ill-posedness | source path and its tangent → log-energy change bounded by the signed radial rate | Discarding the sign of the radial rate gives the tangent-norm majorant. Success: a horizon-uniform bound on `‖C_a r‖_{ℓ²}`. |
| Arithmetic profile decomposition | energy splitting; compact negativity; escape; compact negativity of the restricted Weil form at every fixed aperture | adverse sequence → weak limit with energy at most the limit, or an escape channel | Compactness can fail at origin, height, aperture or modulus. Success: compact negativity of the actual form with constants uniform in a growing aperture. |
| Graded functional calculus | chain in the receiver norm; residue modes; sign-blind threshold; first column; Hilbert–Schmidt exactly above half damping by Mellin–Plancherel of the columns; bounded at half damping through the symbol `ζ(−s)/(sζ(η−s))` and dyadic mean values of the dilation symbol | damping chain + norm → eigenmodes, sizes, strong continuity at zero damping with the unbounded generator `−log d` on residue modes, unboundedness of the transition, truncation approximation at every horizon, the first column as the receiver | Dense eigenmodes need not give a stable expansion. Success: `ℓ²` bounds for the centred chain or for the orbit of `1/k`. |
| Signed sampling / observability | local companion law | companion heights + depth mass + local degrees of freedom → a floor at the Lagrange price, or a defeating profile | A local model is not the Paley–Wiener class. Success: the companion law for sources of aperture `A`, with the Lagrange price controlled uniformly in height. |
| Source-faithful completion with defect accounting | polar defect law; centring in the receiver norm | completion + polar functional → sign kept or lost | Strong convergence can lose the polar functional. Success: a completion whose polar functional is proved continuous. |
| Boundary-sensitive rigidity | triangle holonomy; converse construction | sign pattern of the source → lossless or not | A diagnostic indexed by the zeros restates RH. Success: an arithmetic diagnostic identified with a holonomy and computed from the source. |

---

## 9. Open research topics

1. **Arithmetic holonomy.** Compute the sign pattern of the overlaps of AIP's global incidence ledger
   on a finite resolution of the logarithmic line and locate its frustrated cycles (mechanism 11;
   triangles on complete patterns). For the prime translations alone this is settled at the level
   of sign patterns: even folding is aligned, odd folding is anti-aligned exactly where the kernel
   at the sum exceeds the kernel at the difference, and the prime triangle `log 2, log 3, log 5` is
   frustrated (mechanism 14). With the archimedean kernel and the pole charge added, every
   frustrated cycle still passes through a prime sum, and sampling sets free of prime sums are
   lossless (mechanism 15); at fine resolution (small relative weight of `K`) the prime triangle
   frustrates the full odd ledger. The amount of frustration is a count: switching across a cut
   trades anti-aligned for aligned overlaps, so when the prime-sum pairs of a sample have degree at
   most a quarter of the sample no switching helps, and the frustration index is the number of
   anti-aligned prime-sum overlaps; on matched samples it is `2|Q|`, so samples at aperture `A` reach
   twice a prime count at scale `e^{2A}` (`frustrationIndex_oddWeilLedger_of_sparse`, `exists_frustrationIndex_ge`,
   Arithmetic Orientation Theory). Open: the holonomies at a fixed mesh, where `K` and the prime
   atoms are comparable, and the budgets they supply. The aligned
   part is payable by mechanism 4; the frustrated part is where the even–odd balance of AIP lives.
2. **Allocation at growing size.** Prove a local allocation (or a frustration bound) for a family of
   strips whose number grows with the aperture, with losses uniform in that number. This is the
   cofinal form of Pillar I and the shared-surplus problem of Arithmetic Incidence Positivity (its
   open problem 7 and research topic 6).
3. **Sign-changing gauges.** On an aligned form with nonnegative polar weights, the new polar
   comparison reduces positivity to one-signed profiles; in the coercive case its exact test is
   `Σg_i(C⁻¹g)_i≤1`. Determine where the actual discretized form leaves this class and estimate
   the resulting global polar charge. The cost of *local* payment is exact: the ground-energy gap
   between a form and its comparison form (mechanism 9). What remains is the cheapest *nonlocal*
   payment of the frustrated part — a gauge with sign changes, or a global square absorbing the
   rank-one charges — and its cost for the actual critical form; the signed-gauge certificates of
   Arithmetic Criticality Theory (its research topic 1) are the continuum instance. On a single frustrated cycle the answer is complete: the path pays the frustrated
   edge through the half-sine certificate, at the exact factor `cos(π/k)` (mechanism 12). For
   several frustrated cycles the canonical-path certificate (mechanism 13) is a sufficient
   nonlocal payment with the competition made explicit as a packing constraint. The exact nonlocal
   payment is the Kron reduction to the frustration terminals (paragraph after mechanism 16); for
   one frustrated overlap the price is `(t − β)² ≤ αγ`, `β` the effective conductance of the
   aligned interior. Open: the reduced coupling of the actual ledger on its prime-sum terminals and
   its uniformity in the number of terminals.
4. **The centred chain on `ℓ²`.** `C_η` is Hilbert–Schmidt exactly for `½ < η < 1` and bounded at
   `η = ½`, where Hilbert–Schmidt fails (paragraphs after mechanism 28). Decide boundedness for some
   `η < ½`: the Mellin route needs `1/ζ` on `Re = η + ½`, inside the critical strip; by mechanism 25
   a positive answer at cofinally small `η` would be RH.
   Its first column is exactly the receiver (mechanism 30); the computation of mechanism 30 writes
   the `k`-th column, up to `O(k/m)`, as `(k/m)(k^{−η} P(⌊m/k⌋) − (k+1)^{−η} P(⌊m/(k+1)⌋))`, a
   difference of dilated sources, so boundedness is a
   uniform version over the dilations `k` of admission, with the operator norm controlling all linear combinations and their mixed Gram terms,
   not merely the sum or supremum of individual column energies.
5. **Square-root cancellation against the residue Gram.** Bound `‖Σ_d μ(d) d^{−η} v_d‖_{ℓ²}` below
   half damping on a horizon-dependent range of moduli with explicit tails; this is the receiver
   problem of Bézout–Valuation Incidence in residue coordinates.
6. **Signed sampling beyond the local model.** The transfer to general sources is reduced to the
   local approximation error (mechanism 40, `companions_pay_up_to_error`), and for smooth sources
   to the Taylor remainder (`companions_pay_up_to_taylor`); for trigonometric sources of aperture `A`
   the loss `2 #s ((Aδ)^d m/d!)²` is uniform in the height (`companions_pay_aperture`), and the price
   is explicit in the spacing and spread (`companions_pay_aperture_explicit`). What remains is the
   companion geometry of the actual on-line zeros: `k + 1` of them spaced by `δ` within `r ≪ 1/A`
   of every height, which is information about the zeros on the line. Prove the companion law of mechanism 40 for
   Paley–Wiener sources of aperture `A`, with a Lagrange price uniform in the height, and combine it
   with sufficiently strong information about the **on-line** zeros of `ζ` to obtain the
   plain-`L²` floor at the width rate. Control the Taylor remainder and infinite zero tail as well
   as the interpolation price; the polynomial model alone supplies none of these transfers.
7. **Compact negativity uniformly in the aperture.** At fixed aperture the restricted Weil form is
   compactly negative (mechanism 39). Determine how the compactness — the finite-rank
   approximation of the embedding seen by the polar and prime remainder — degrades as the aperture
   grows; this uniformity is the input Pillar V needs to exclude escape of adverse profiles at
   growing aperture.
8. **Trains not aligned with the towers.** For trains that are products along the towers the
   capacities add (mechanism 21). Profiles that are not such products are where a cross-prime
   saving can live; determine their joint charge. On a box the additive bound holds for every amplitude, product or not
   (`grid_joint_capacity`, `cartesian_lower_bound`), so a saving can only come from the geometry of
   the support: trains whose positions do not fill a box of the multiplicative lattice. On the
   simplex `j + k ≤ n` with equal weights the joint charge is exactly `cos θ + cos 2θ`,
   `θ = π/(n+3)`, strictly below the box sum. On every support that is not a box the towers do not
   add, for all positive weights, in particular on `j log p + k log q ≤ X` with the weights
   `Λ(p)p^{−½}`, `Λ(q)q^{−½}`. Open: the size of that saving, its order `X^{−2}` constant and its
   dependence on `log q/log p`.

---

## 10. Success criteria and contributions

**Success means a quantitative transfer on the actual source.** Examples include a shared
allocation that proves the full incidence inequality, or a horizon-uniform `ℓ²` bound for the
reciprocal orbit at specified dampings. An operator bound is a stronger sufficient route; cofinal
admission is RH. A compact-negativity estimate or a finite allocation theorem is useful structural
progress, but still needs exclusion of adverse profiles or control of its losses before it yields
positivity. State the resulting aperture, damping or width explicitly.

**A contribution to the programme must**

- carry the full passport: source, domain, norm, observation, signed ledger, parameter range and
  limit order;
- keep the signed ledger signed: positive and negative pieces are separated only where the theorem
  says why the separation is lossless;
- state which dividing line it crosses and which input lets it cross: a balanced structure, a
  continuous polar functional, a source-specific cancellation, a compact negativity;
- be unconditional in Lean, with no hypothesis restating the sign or the estimate it is about;
- come with its sharpness: an extremal, a converse, or a counterexample in its class;
- name the arithmetic instance it applies to, or say that it is structural infrastructure and
  count it as zero in the shared units;
- for a no-go, state the positive survivor.

---

## 11. Principles

1. **Search the corpus first** (`scripts/formal_tools.py research "<query>"` from the repository root): the strips and
   trains are AIP's, the chain and modes are BVI's, the continuation criterion is ACCE's.
2. **Name the pattern and budgets.** Signs decide the universal lossless-payment theorem;
   magnitudes and diagonal budgets decide payment of a particular form.
3. **Name the norm.** Every statement about the damping chain says whether it is in `c₀`, in the
   pronic weight on the chain coordinate, or in the receiver norm `ℓ²`.
4. **Keep the pole global.** A pure rank-one form with three nonzero coordinates cannot be
   allocated to pairs from its own diagonal budgets; additional resources must be identified.
5. **Read the source, not the operator.** Continuation statements must use the vector `1/k` and the
   coefficients `μ(d)`; operator statements alone cannot go backwards.
6. **Finite before cofinal.** A finite theorem is infrastructure until its losses are shown uniform
   in the size of the family it is applied to.
