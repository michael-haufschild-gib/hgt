# Signed Arithmetic Energy and Incidence (`GaloisForLFunctions.SignedArithmeticEnergyIncidence`)

**One question.** How does exact multiplicative incidence constrain signed quadratic energies across
scale — and which of those constraints survive a change of coordinates, a regularization, or a
completion?

Signed arithmetic energy and incidence (SAEI) is the interface theory of the corpus's critical
energy programmes. It owns no critical form of its own. It studies the four operations that every
closing argument performs on one: **paying** a signed form out of local resources, **completing**
it in a new norm, **transporting** it along a parameter, and **decomposing** its adverse sequences.
Each operation has a sharp law, proved here in a general finite or Hilbert-space setting, and each
law is instantiated on a literal arithmetic object of the corpus: the prime lag charges of
`ArithmeticIncidencePositivity`, the damped Möbius source and its damping chain of
`BezoutValuationIncidence`, and the continuation criterion of
`ArithmeticContinuationAndCriticalEnergy`. Every statement is unconditional and names its source,
its domain, its norm and its parameter range.

---

## The place of the programme

The closing problems of the corpus split into a list of open obstacles (the companion report
`docs/reports/review-2210/hard-obstacles-summary.md`). Five of them — signed damping continuation
(O2), arithmetic structure beyond generic dispersion (O3), global positivity with one shared budget
(O4), width and visibility (O5) and faithful completion (O7) — meet at three interfaces, and SAEI is
the theory of those interfaces:

1. **Arithmetic cancellation → norm bound.** Which exact identity of the literal Möbius or prime row
   excludes the generic bad coefficients, and in which norm does its gain survive? SAEI answers
   the structural half: in the receiver norm the damped source is the Möbius-weighted series of
   the residue modes, the modes have size `≍ d^{−1/2}`, and therefore *sign-blind summation stops
   exactly at half damping*. Below it the signs of `μ` are the estimate.
2. **Local payment → global conservation.** How do one-strip or one-block gains combine without
   spending a resource twice? SAEI proves the exact dividing line: *local payment is lossless
   exactly on balanced incidence*, and on complete overlap patterns balance is the vanishing of the
   frustration of every triangle. A rank-one polar charge is frustrated on any three points and
   can never be paid pair by pair.
3. **Reconstruction → quantitative control.** Dense eigenmodes, exact recovery and faithful
   divisors identify an object without bounding it. SAEI makes the bound a statement about the
   right norm: the critical energy is the `ℓ²` energy of the damping chain's orbit of the
   reciprocal `1/k`; an `ℓ²`-bounded chain would be a receiver; and *no backward stability
   estimate exists*, so continuation to smaller damping must read the source vector itself.

**The theorem passport.** Every SAEI statement carries seven data, and a statement missing one of
them is not yet a theorem of the programme: the **source** (which arithmetic object), the
**domain** (which class of profiles, rows or configurations), the **norm** (in which the bound is
stated), the **observation** (what the argument reads of the source), the **signed ledger** (which
positive and negative pieces are kept separately), the **parameter range** (damping, aperture,
rank, height), and the **limit order** (which limits are taken, in which order, under which
uniformity).

### This programme's role

SAEI is the layer between the faces of the critical form and the closing estimate. It hands the
other programmes three kinds of results:

- **Sharp dividing lines** for methods: a local allocation succeeds exactly on balanced incidence; a
  completion keeps the sign exactly when it keeps the polar functional; a sign-blind summation
  succeeds exactly above half damping; a backward operator estimate never exists.
- **Exact extremals**: the sine trains, not the resonant trains, carry the largest single-prime
  charge at finite length; on two aligned towers the prime capacities add.
- **Reformulations in the right norm**: admission as `ℓ²`-membership of a semigroup orbit; the
  relative loss as a radial rate.

In the shared units of the corpus most of these results count as **zero** — they are dividing
lines, extremals and dictionaries, not new apertures, exponents or dampings. Their value is that a
proposed estimate can be checked against them before it is attempted: an estimate that crosses a
dividing line without the input that line names is refuted in advance.

### How the programme connects to the other programmes

- **Arithmetic Incidence Positivity** supplies the strips, atoms, trains and the global incidence
  ledger. SAEI's local–global principle is the abstract form of AIP's allocation problem (research
  topic 6 of AIP): an allocation of the shared surplus to overlapping strips is a local allocation
  of a signed incidence form. The frustration theorems say why the global ledger cannot be reduced
  to own-strip payments, and the train theorems sharpen AIP's resonant-train envelopes at finite
  length (`SineTrainsAreExtremalForOnePrime`, `TowerGridCapacitiesAdd` against AIP's
  `ResonantTrainWitness` and `BiLatticeTrainWitness`).
- **Arithmetic Criticality Theory** supplies the gauges. A positive gauge with nonnegative action is
  a positive supersolution, and the ground-state transform of `SignedIncidenceForms` is the finite
  form of ACT's ground-state representation. The balanced theorem says exactly when a positive
  gauge must exist; the frustration theorems say when no positive gauge can pay the form and a
  sign-changing gauge (ACT research topic AC-2) is unavoidable.
- **Bézout–Valuation Incidence** supplies the damping chain `C_η` on `c₀`, its compactness, its
  semigroup law, the residue modes and their `c₀`-density, and the entrance law. SAEI moves these
  to the receiver norm (`TheReceiverIsTheChainOrbitOfTheReciprocal`,
  `ResidueModesAndBackwardContinuation`, `TheSourceIsTheDampedMoebiusResidueSeries`): it identifies
  the receiver's coordinate as `ℓ²` on the chain coordinate, shows that the uncentred transition is
  unbounded there at every damping, and answers BVI research topic 6 (carry the chain to the
  receiver's norm) in the form that matters: the orbit of `1/k`, not the operator, must be bounded.
- **Arithmetic Continuation and Critical Energy** supplies the exact continuation criterion (a
  horizon-uniform bound on the integrated signed relative loss is admission). SAEI adds the radial
  structure of that loss (`TheRadialLossLaw`) and the impossibility of a source-blind backward
  estimate.
- **Square-Root Threshold** supplies the width/rate dictionary and the local depth-mass hypothesis.
  SAEI's polar defect and profile theorems are the abstract mechanisms behind its floors; the
  signed sampling question (O5) is recorded below as an open topic of this programme.
- **Scale-Signed Incidence Criticality** supplies the language of readings and resolution limits.
  The sign-blind threshold is a resolution limit in that language: the reading that sees only
  `|μ(d)|` has resolution exactly half damping.
- **Trans-Horizon Incidence Mechanics, Bi-Scale Uncertainty, Arithmetic Positivity Theory** supply
  the observation, recovery and restricted-family results whose quantitative transfer to the
  receiver is SAEI's third interface; the sign-changing screw gauge (`SignChangingScrewGauge`)
  supplies the one-signed and edge-profile charge laws that the balanced theorem explains.

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

- in the damping reading, the triangle inequality over the residue modes admits the source exactly
  above half damping (`summable_signBlind_iff`, `admits_of_signBlind`), and the series with all
  Möbius signs replaced by `+1` has infinite receiver energy at every damping `0 < ε ≤ ½`
  (`not_summable_positiveTwin`);
- in the incidence reading, replacing the sign pattern of the overlaps by its absolute values turns
  a frustrated pattern into a balanced one, and the theorems of §3 show that this is exactly where
  local payment stops being lossless.

**Incidence is substantive.** Whether a positive form can be paid locally depends on which overlaps
exist and on the signs they carry, not on their sizes: on a complete overlap pattern, local
payment is lossless for *every* positive form realizing the pattern exactly when every triangle of
the pattern is unfrustrated (`localPayment_lossless_iff`). The holonomy of a triangle is computed
from the source before any profile or gauge is chosen. Density statistics of the overlaps do not
determine it.

**Across scale is substantive.** The damping is the time of the chain: the damped Möbius source is
the orbit `η ↦ C_η(1/k)` of the compact centered semigroup (`centeredOperator_orbit`). Continuation
to smaller damping is backward evolution, and the semigroup has no bounded backward version in any
of the norms in play (`not_backward_stable_l2`, `not_backward_stable_c0`). Every continuation
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
| Sign pattern, realization | symmetric `σ_ij = ±1`; `c` realizes `σ` if `c_ij σ_ij > 0` | `SignPattern`, `Realizes` |
| Rank-one charge | `w_i w_j`, the square of `Σ w_i f_i` | `rankOneCoupling` |
| Comparison form | same budgets, overlap charges `−|c_ij|` | `comparisonCoupling` |
| Frustrated triangle | unit budgets, charge `κ` on three pairs | `triangleCoupling` |
| Chain | budgets `d_k`, overlap charges `e_k` between `k`, `k+1` | `chainCoupling`, `chainEntry` |
| Running sign | switching that aligns a chain | `chainSign` |
| Sine gauge of a train | `sin((k+1)π/(n+2))` | `trainSine` |
| Amplitude train | `Σ_{k ≤ M} f_k g(· + kL)` | `amplitudeTrain` |
| Grid train | amplitudes on `(M+1) × (N+1)`; row/column charges and mass | `gridRowCharge`, `gridColCharge`, `gridMass`, `productSine` |
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

**Words.**

- **Pay locally**: every overlap is paid by the two shares its endpoints lend it, and no point lends
  more than its budget. Nothing is spent twice.
- **Aligned, balanced, frustrated**: an overlap is aligned when its charge is `≤ 0` (it rewards
  equal values at its ends); a pattern is balanced when switching aligns all of it; a cycle is
  frustrated when no switching aligns it. On complete patterns frustration is read off the
  triangles.
- **Holonomy**: the product of the charges around a triangle. Negative holonomy is the aligned case.
- **Supersolution**: a gauge `v > 0` with `Cv ≥ 0`. For aligned forms it is the same thing as a
  local allocation; for frustrated forms it need not exist.
- **Polar charge**: the square of one linear functional — the shape of the pole in every face of the
  critical form.
- **Receiver norm of the chain**: `ℓ²` on the chain coordinate; it is the pronic energy of the
  prefix `P = n · C r`.
- **Orbit**: `η ↦ C_η r`, the damped Möbius source as a function of the damping.
- **Sign-blind**: an argument that reads only the absolute values of the Möbius coefficients.
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
   invariant (`triangleHolonomy_switch`).
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
   payment is the gap between the ground energies of the form and of its comparison form.

### Chains and trains

10. **Chain lending duality.** Chains are balanced, whatever the signs of their overlaps
   (`chainCoupling_isBalanced`, by the running sign `chainSign`), so a chain is positive exactly
   when it has a lending ledger: each point splits its budget between its two overlaps
   (`chain_nonneg_iff_locallyPayable`).
11. **Capacity of a uniform train.** The sine gauge solves the train equation
    `2 cos θ · v_k = v_{k−1} + v_{k+1}` with zero boundary values
    (`couplingAction_uniformTrain_trainSine`); as a positive supersolution it certifies
    `2 Σ_{k<n} f_k f_{k+1} ≤ 2 cos(π/(n+2)) Σ_{k≤n} f_k²` (`uniformTrain_capacity`), attained at the
    sine (`uniformTrain_capacity_attained`) and sharp (`uniformTrain_capacity_sharp`).
12. **The first-lag law of a train.** For `M + 1` disjoint copies of a bump at spacing `L`,
    `A_S(L) = (Σ_{k<M} f_k f_{k+1}) A_g(0)` and `A_S(0) = (Σ f_k²) A_g(0)`
    (`autoCorr_amplitudeTrain_first`, `autoCorr_amplitudeTrain_zero`, from AIP's translate
    calculus). Hence `|A_S(L)| ≤ cos(π/(M+2)) A_S(0)` (`autoCorr_amplitudeTrain_first_le`,
    `..._ge`), attained by the sine train (`autoCorr_sineTrain_first`).
13. **The resonant train is not extremal for one prime.** The unit train carries `M/(M+1)` of its
    mass at the first lag, strictly less than `cos(π/(M+2))` from `M = 2` on
    (`resonant_ratio_lt_cos`). The extremal deficit is `1 − cos(π/(M+2)) ≍ π²/(2M²)`.
14. **Two aligned towers add.** On an `(M+1) × (N+1)` grid train, the joint first-power charge of
    two primes is at most `(w_p cos(π/(M+2)) + w_q cos(π/(N+2)))` times the mass
    (`grid_joint_capacity`), attained by the product sine (`grid_joint_capacity_attained`) and sharp
    (`grid_joint_capacity_sharp`): no cross-prime cancellation on multiplicatively aligned trains.

### Poles and completion

15. **Polar defect law.** `‖v‖² − Σ_j ⟪g_j, v⟫² ≥ 0` for all `v` iff the synthesis of the polar
    vectors is a contraction, `‖Σ c_j g_j‖² ≤ Σ c_j²` (`polarDefect_nonneg_iff`). In rank one the
    ground ratio is exactly `1 − ‖g‖²`, attained on `g` (`polarDefect_ge`, `polarDefect_self`,
    `polarDefect_nonneg_iff_norm_le_one`).
16. **Completion keeps the sign exactly when it keeps the polar functional.** Positivity on a dense
    set transfers to the completion for a continuous polar functional
    (`polarDefect_nonneg_of_dense`); an unbounded polar functional leaves no floor at all
    (`exists_polarDefect_lt_of_unbounded`).

### The damping chain in the receiver norm

17. **The receiver is the chain orbit of the reciprocal.** `(C_η r)(n) = P_η(n+1)/(n+1)`
    (`centeredOperator_reciprocal_apply`), `C_s C_t r = C_{s+t} r` (`centeredOperator_orbit`), and
    `E_η(T) = Σ_{m<T} (m+1)/(m+2) · (C_η r)(m)²` (`dampedMobiusEnergy_eq_orbitEnergy`). Admission is
    `ℓ²`-membership of the orbit (`admits_iff_summable_orbit`); the Riemann hypothesis is the orbit
    entering `ℓ²` at arbitrarily small times (`riemannHypothesis_iff_orbit_summable`).
18. **An `ℓ²`-bounded chain is a receiver.** If `C_η` is `ℓ²`-bounded on finitely supported
    sequences, `η` is admitted (`admits_of_chain_l2_bounded`): truncations of `r` converge in `c₀`,
    the chain is `c₀`-continuous, and every horizon passes to the limit.
19. **The centring is indispensable in receiver coordinates.** The uncentred transition sends the
    first state to a column converging to the positive entrance mass
    (`arithmeticDampingEntrance_one_pos`), so it is `ℓ²`-unbounded at every damping
    (`not_summable_transition_first_column`).
20. **The first column of the chain is the receiver.** On the first state the centred chain is the
    dyadic difference `D_η(m) = P_η(m) − 2^{−η} P_η(⌊m/2⌋)` of the source over `m`, up to a term of
    size `1/m` (`centeredOperator_firstState_apply_eq`). The dyadic difference loses nothing in the
    receiver norm — a two-to-one count one way, the geometric inversion
    `P(m) = Σ_j 2^{−jη} D(⌊m/2^j⌋)` with a weighted Cauchy–Schwarz inequality the other
    (`summable_dyadicDifference_iff`) — so the first column lies in `ℓ²` iff `η` is admitted
    (`admits_iff_summable_firstColumn`, `riemannHypothesis_iff_firstColumn_summable`). The first
    test of `ℓ²`-boundedness of the chain is already the receiver.
21. **Residue modes are the eigenmodes, and have receiver size `≍ 1/d`.** `C_η v_d = d^{−η} v_d`
    (`centeredOperator_normalizedResidueMode`); `(d − 1)/d² ≤ ‖v_d‖²_{ℓ²} ≤ 2/d`
    (`tsum_sq_normalizedResidueProfile_ge`, `..._le`).
22. **Backward continuation is ill-posed.** No `‖b‖ ≤ K ‖C_t b‖` holds in `ℓ²` or in `c₀`, for any
    `t > 0` (`not_backward_stable_l2`, `not_backward_stable_c0`); on `v_d` the ratio is `d^t`.
23. **The source is the damped Möbius residue series.** `(C_η r)(n) = Σ_d μ(d) d^{−η} v_d(n)`
    (`centeredOperator_reciprocal_eq_tsum`).
24. **The sign-blind threshold.** `Σ_d d^{−ε} ‖v_d‖_{ℓ²}` converges iff `ε > ½`
    (`summable_signBlind_iff`); the triangle inequality bounds every horizon by its square
    (`orbit_partial_energy_le`) and admits the source above half damping (`admits_of_signBlind`);
    the positive twin `Σ_d d^{−ε} v_d` has infinite receiver energy for `0 < ε ≤ ½`
    (`not_summable_positiveTwin`, via `positiveTwin_le`).

### Adverse sequences

25. **Energy splitting.** For a bounded symmetric form and `u_n ⇀ u`,
    `Q(u_n) − Q(u) − Q(u_n − u) → 0` (`tendsto_energy_splitting`).
26. **Adverse profiles cannot vanish under compact negativity.** If `Q` is compactly negative, it is
    weakly lower semicontinuous along bounded sequences (`energy_le_of_weakConv`); a unit-bounded
    adverse sequence with `Q(u_n) → μ < 0` has a nonzero weak limit with `Q(u) ≤ μ ‖u‖²`
    (`adverse_weakLimit`). A form bounded below by one finite-rank charge is compactly negative
    (`compactlyNegative_of_finiteRank`).
27. **Escape through a noncompact negative part.** For `Q = −‖·‖²` an orthonormal sequence is
    adverse with weak limit `0` (`adverse_escape_of_orthonormal`).

### Continuation

28. **The radial loss law.** The relative loss `−2⟪u, u'⟫/(1 + ‖u‖²)` is the derivative of
    `−log(1 + ‖u‖²)` (`hasDerivAt_log_one_add_energy`); tangential motion is free
    (`radialLoss_add_tangential`, `radialLoss_of_inner_eq_zero`, `log_energy_eq_of_tangential`);
    `|L| ‖u‖ ≤ |⟪u, u'⟫|` and `|L| ≤ ‖u'‖` (`abs_radialLoss_mul_norm_le`, `abs_radialLoss_le`),
    so the log-energy moves by at most the path length (`abs_log_energy_sub_le`).

---

## 4. Foundational pillar theorems

**Pillar I — the signed local–global principle.** For balanced signed incidence forms, positivity,
local payability and (for aligned forms) existence of a positive supersolution coincide
(`nonneg_iff_locallyPayable_of_isBalanced`, `locallyPayable_of_supersolution`). On complete overlap
patterns, local payment is lossless for every positive form realizing a sign pattern iff every
triangle of the pattern has negative holonomy (`localPayment_lossless_iff`). For every form, local
payability is positivity of its comparison form, and the exact cost of local payment is the gap
between the two ground energies (`locallyPayable_iff_comparison_nonneg`,
`locallyPayable_regularized_iff`). A rank-one charge on three points is never locally payable
(`not_locallyPayable_rankOneCoupling`).

**Pillar II — the polar defect law.** The sign of `‖·‖² − Σ (polar charges)` is the contraction
property of the polar synthesis map; a completion keeps the sign iff it keeps the polar functional
continuous (`polarDefect_nonneg_iff`, `polarDefect_nonneg_of_dense`,
`exists_polarDefect_lt_of_unbounded`).

**Pillar III — the receiver as a semigroup orbit.** The damped Möbius source is the `c₀` orbit of
`1/k` under the compact centered damping chain; the critical energy is its `ℓ²` energy; admission
is `ℓ²`-membership, already equivalent to `ℓ²`-membership of the chain's first column;
`ℓ²`-boundedness of the chain is sufficient, backward stability is impossible, and sign-blind
summation stops exactly at half damping (`admits_iff_summable_orbit`,
`admits_iff_summable_firstColumn`, `admits_of_chain_l2_bounded`, `not_backward_stable_l2`,
`summable_signBlind_iff`, `not_summable_positiveTwin`).

**Pillar IV — train capacities.** A single prime's first-lag charge on a train of length `M + 1` is
at most `cos(π/(M+2))` of the mass, attained by sine amplitudes; on aligned two-tower grids the
capacities add (`autoCorr_amplitudeTrain_first_le`, `autoCorr_sineTrain_first`,
`grid_joint_capacity_attained`).

**Pillar V — profile compactness.** Under compact negativity, adverse sequences converge weakly to
genuine adverse profiles; without it they escape (`adverse_weakLimit`,
`adverse_escape_of_orthonormal`).

**Pillar VI — the radial loss law.** Signed continuation charges only the radial rate of the
source; the tangent norm is the orientation-blind majorant (`radialLoss_add_tangential`,
`abs_log_energy_sub_le`).

---

## 5. Traps

| Trap | What is true instead |
|---|---|
| "Each atom is paid by its own strip, so the form is paid." | Own-strip payments are a local allocation only if the shares are drawn once from each budget. Overlapping strips form a signed incidence pattern; a frustrated cycle in it can make a positive form unpayable (mechanism 8). |
| "Positivity of a form implies a positive gauge." | Only for balanced forms. Frustrated forms can be positive with no positive supersolution and no local allocation (mechanisms 5–6). |
| Treating the pole as a local charge. | A rank-one charge on three or more points is never locally payable (mechanism 5). The pole must be paid by a global dual-norm bound (mechanism 15). |
| Reading the frustrated triangle as an artefact of equal weights. | The converse construction of mechanism 8 realizes every frustrated pattern on every complete overlap graph. |
| "The resonant (unit) train is the extremal adverse direction." | For several lags at once the unit train attains the Euler envelopes; for one lag at finite length the sine train is extremal and the unit train is strictly worse from `M = 2` on (mechanism 13). |
| Expecting cross-prime cancellation on aligned trains. | On two-tower grids the single-prime capacities add exactly (mechanism 14). |
| Taking the pronic weight on the chain coordinate as the receiver. | The receiver is `ℓ²` on the chain coordinate (mechanism 17). In the pronic weight on the chain coordinate the centring functional is unbounded below half damping (BVI); in the receiver norm the transition is unbounded and the centring is what makes the receiver possible (mechanism 19). |
| "Compactness of the chain on `c₀` gives continuation." | Compactness makes the backward problem ill-posed: no backward stability estimate exists in `c₀` or `ℓ²` (mechanism 22). |
| "Dense residue modes give a stable expansion of the source." | The modes diagonalize the chain and span `c₀` densely, but the source is a signed series in them whose sign-blind majorant converges only above half damping (mechanism 24). |
| Bounding the relative loss by the tangent norm and calling it the criterion. | The tangent norm is the orientation-blind majorant; tangential motion is free and only the signed radial rate enters (mechanism 28). |
| "An adverse sequence has an adverse limit." | Only under compact negativity; with a noncompact negative part the weak limit can be zero (mechanisms 26–27). |
| Treating a finite-dimensional duality as a cofinal certificate. | The finite theorems here have no uniformity in the number of points; transporting them to a growing arithmetic family is a separate estimate. |

---

## 6. The questions and what is answered

The programme was proposed with eight questions. Each answer below says exactly what is proved, in
which class, and what remains.

1. **Which sign-changing odd profiles can create net unpaid prime demand after all favourable gains
   are restored?** *Answered in the finite incidence model.* Unpaid demand with global positivity
   exists exactly where the incidence of the charges is frustrated: balanced patterns never carry
   it (Pillar I), and on complete overlap patterns a single triangle of holonomy `+1` suffices for
   it (mechanism 8); for an arbitrary form the unpaid demand is measured exactly by its comparison
   form (mechanism 9). A rank-one polar charge carries it on any three points. In the folded odd
   reading of AIP the archimedean same-side and crossing conductances combine into aligned charges
   (AIP mechanism 23), while crossing prime atoms off the lattice and the polar square are
   anti-aligned; the adverse sign-changing profiles are those that load a frustrated cycle formed by
   them. The continuum classification of such profiles for the actual kernel is AIP's AI-2 and
   remains open.
2. **Can those profiles be reduced to a controlled family without a norm loss that grows faster than
   the available budget?** *Answered for one prime and for two aligned towers.* The extremal
   adverse profiles are the sine trains and the product sine grids; the reduction to them loses
   nothing, and their deficit from the full envelope is explicit, `1 − cos(π/(M+2))` per tower
   (Pillar IV). Because the deficit tends to zero, no reduction to trains can create slack against
   the full prime envelope: the budget must come from outside the aligned trains. Profiles not
   aligned with the towers remain open.
3. **What signed arithmetic estimate bounds the averaged damping loss uniformly in horizon?**
   *Answered as an exact reformulation with its necessary structure.* The estimate is exactly
   `ℓ²`-membership of the chain orbit `C_a(1/k)` (mechanism 17 with ACCE's averaged-budget
   criterion), equivalently of the chain's first column (mechanism 20); an `ℓ²`-bounded chain
   suffices (mechanism 18). Any such estimate must read the source
   vector — no backward operator estimate exists (mechanism 22) — must read the signs of `μ` below
   half damping (mechanism 24), and must control only the signed radial rate (mechanism 28). The
   estimate itself at cofinally small damping is RH-strength and open.
4. **Which residue observable gives actual-row cancellation uniformly over the growing moduli and
   tails?** *Answered structurally.* The observable is the full damped Möbius residue series
   `Σ_d μ(d) d^{−η} v_d`, read in `ℓ²` (mechanism 23). Its modes have receiver size `≍ d^{−1/2}`, so
   the cancellation required below half damping is square-root cancellation of `μ` against the
   residue-mode Gram uniformly in the modulus; any fixed set of moduli, and any sign-blind majorant,
   is insufficient (mechanisms 21, 24). The quantitative cancellation is BVI's BV-2 and remains
   open.
5. **Does the signed Weil floor have the sharp width rate in unrestricted `L²` without uniform
   unsigned depth mass?** *Open, and recorded as a research topic.* SAEI supplies the abstract
   mechanisms the answer will need (polar defect law, compact negativity) but no theorem settling
   the actual-ζ case; SRT's equivalence of unsigned sampling with local depth mass is the present
   boundary. The specific signed mechanism left to study is the compensation of an off-line cluster
   by the positive contributions of nearby on-line zeros, which a source of aperture `A` cannot
   annihilate once their local number exceeds its `≍ A` degrees of freedom per unit height.
6. **Which topology preserves both the full source normalization and the sign needed by a carrier
   construction?** *Answered for the damping carrier and in general.* A completion keeps the sign
   exactly when it keeps the polar functional continuous (Pillar II). For the damping chain the
   right topology is `ℓ²` on the chain coordinate (the pronic energy of the prefix): the centring
   functional is bounded there, the uncentred transition is not, and boundedness of the centred
   chain would be a receiver (mechanisms 17–19); already its first column is in `ℓ²` exactly at
   admitted dampings (mechanism 20). The pronic weight on the chain coordinate forgets the
   normalization below half damping (BVI). Whether the centred chain is `ℓ²`-bounded is open.
7. **Can a pre-divisor conservation or orientation law force the known seam/mate diagnostics to
   vanish?** *Answered in the incidence model.* The triangle holonomy is a pre-profile,
   gauge-invariant orientation diagnostic computed from the source alone; its alignment forces the
   vanishing of the local–global defect and its failure forces a defect (mechanisms 7–8). The
   arithmetic seam and mate diagnostics of the standalone candidates are not identified with it;
   such an identification would be a contribution.
8. **What mechanism supplies the all-rank/all-height uniformity absent from fixed-rank theorems?**
   *Answered structurally.* Compact negativity: under it adverse sequences have genuine adverse
   limits (Pillar V); escape is exactly the failure of compactness of the negative part. A
   uniform-in-rank theorem must therefore prove a compact-negativity estimate that survives the
   growing family. The arithmetic instance at growing aperture is open.

---

## 7. The tools

| Tool | What is developed | Input → output | Failure mode and success test |
|---|---|---|---|
| Arithmetic allocation duality | Pillar I; chain lending; holonomy; comparison form | finite signed incidence ledger → local allocation, or a negative profile of the comparison form (a dual adverse profile), or a frustrated triangle; the exact budget increase that restores payment | Finite duality is not cofinal. Success: an allocation for a growing arithmetic family with losses uniform in its size. |
| Covariance continuation estimate | radial loss law; orbit reformulation; backward ill-posedness | source path and its tangent → log-energy change bounded by the signed radial rate | Discarding the sign of the radial rate gives the tangent-norm majorant. Success: a horizon-uniform bound on `‖C_a r‖_{ℓ²}`. |
| Arithmetic profile decomposition | energy splitting; compact negativity; escape | adverse sequence → weak limit with energy at most the limit, or an escape channel | Compactness can fail at origin, height, aperture or modulus. Success: compact negativity for the actual form at a growing aperture. |
| Graded functional calculus | chain in the receiver norm; residue modes; sign-blind threshold; first column | damping chain + norm → eigenmodes, sizes, unboundedness of the transition, sufficiency of `ℓ²`-boundedness, the first column as the receiver | Dense eigenmodes need not give a stable expansion. Success: `ℓ²` bounds for the centred chain or for the orbit of `1/k`. |
| Signed sampling / observability | (open topic, §8) | depth data → energy bound | Unsigned local depth mass is the present boundary (SRT). |
| Source-faithful completion with defect accounting | polar defect law; centring in the receiver norm | completion + polar functional → sign kept or lost | Strong convergence can lose the polar functional. Success: a completion whose polar functional is proved continuous. |
| Boundary-sensitive rigidity | triangle holonomy; converse construction | sign pattern of the source → lossless or not | A diagnostic indexed by the zeros restates RH. Success: an arithmetic diagnostic identified with a holonomy and computed from the source. |

---

## 8. Open research topics

1. **Arithmetic holonomy.** Compute the sign pattern of the overlaps of AIP's global incidence ledger
   on a finite resolution of the logarithmic line and locate its frustrated triangles. The aligned
   part is payable by mechanism 4; the frustrated part is where the even–odd balance of AIP lives.
2. **Allocation at growing size.** Prove a local allocation (or a frustration bound) for a family of
   strips whose number grows with the aperture, with losses uniform in that number. This is the
   cofinal form of Pillar I and the content of AIP's AI-1.
3. **Sign-changing gauges.** The cost of *local* payment is now exact: the ground-energy gap
   between a form and its comparison form (mechanism 9). What remains is the cheapest *nonlocal*
   payment of the frustrated part — a gauge with sign changes, or a global square absorbing the
   rank-one charges — and its cost for the actual critical form; ACT's AC-2 is the continuum
   instance.
4. **The centred chain on `ℓ²`.** Decide whether `C_η` is `ℓ²`-bounded on finitely supported
   sequences for some `η ≤ ½`; by mechanism 18 a positive answer at cofinally small `η` would be RH.
   Its first column is exactly the receiver (mechanism 20); the computation of mechanism 20 writes
   the `k`-th column, up to `O(k/m)`, as `(k/m)(k^{−η} P(⌊m/k⌋) − (k+1)^{−η} P(⌊m/(k+1)⌋))`, a
   difference of dilated sources, so boundedness is a
   uniform version over the dilations `k` of admission, with the operator norm measuring how the
   column energies sum.
5. **Square-root cancellation against the residue Gram.** Bound `‖Σ_d μ(d) d^{−η} v_d‖_{ℓ²}` below
   half damping on a horizon-dependent range of moduli with explicit tails; this is BVI's BV-2 in
   residue coordinates.
6. **Signed sampling.** Prove or refute the plain-`L²` signed floor at the width rate in a class of
   configurations where off-line clusters are accompanied by on-line zeros of a stated local
   density.
7. **Compact negativity of the critical form.** Prove that at fixed aperture the prime and polar
   charges of the Weil form are compactly negative against its archimedean energy, and determine how
   the compactness constants degrade with the aperture; this is the input Pillar V needs for O6.
8. **Trains beyond two towers.** Extend the grid capacity to any finite set of towers and to trains
   not aligned with the towers; the latter is where cross-prime saving can live.

---

## 9. Success criteria and contributions

**The programme succeeds** when one of its interface theorems is upgraded from a dividing line to a
closing estimate: a local allocation of the global incidence ledger at every aperture with a
uniform loss; a horizon-uniform `ℓ²` bound on the chain orbit of `1/k` at cofinally small damping;
an `ℓ²` bound on the centred chain; a compact-negativity estimate for the critical form uniform in
the aperture. Each would discharge an existing receiver (AIP's global allocation, ACCE's averaged
budget, BVI's interior contraction, RW's ground energy).

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

## 10. Principles

1. **Search the corpus first** (`../scripts/formal_tools.py research "<query>"`): the strips and
   trains are AIP's, the chain and modes are BVI's, the continuation criterion is ACCE's.
2. **Name the pattern.** Every local–global statement says which overlaps exist and what signs they
   carry; sizes without signs decide nothing.
3. **Name the norm.** Every statement about the damping chain says whether it is in `c₀`, in the
   pronic weight on the chain coordinate, or in the receiver norm `ℓ²`.
4. **Keep the pole global.** Never allocate a rank-one charge to pairs.
5. **Read the source, not the operator.** Continuation statements must use the vector `1/k` and the
   coefficients `μ(d)`; operator statements alone cannot go backwards.
6. **Finite before cofinal.** A finite theorem is infrastructure until its losses are shown uniform
   in the size of the family it is applied to.
