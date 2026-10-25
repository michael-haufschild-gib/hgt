# Signed Arithmetic Energy and Incidence (SAEI)

**One question.** How does exact multiplicative incidence constrain signed quadratic energies across
scale — and which constraints survive a change of coordinates, a regularization, or a completion?

SAEI owns no critical form. It is the interface theory of the critical-energy programmes and
studies four operations every closing argument performs on a signed form: **paying** it from local
resources, **completing** it in a new norm, **transporting** it along a parameter, **decomposing** its
adverse sequences. It proves sharp finite/Hilbert-space laws and applies them to AIP's prime lag
charges, BVI's damped Möbius source and damping chain, and ACCE's continuation criterion.

Namespace `GaloisForLFunctions.SignedArithmeticEnergyIncidence`; umbrella `SignedArithmeticEnergyIncidence.lean`.

---

## 1. Place in the research

Supporting framework for the incidence (AIP), Möbius-continuation (BVI/ACCE) and compensation
routes: signed-graph/frustration calculus, prime-tower capacities, receiver coordinates of the
damping chain, signed sampling. Local PSD or local payment is never the full continuum sign; the
canonical-path and Kron certificates are methods whose premises (supersolution, coercivity,
horizon-uniform packing) must be proved on each route's actual coupling.

| Programme | Connection |
|---|---|
| [arithmetic-positivity-theory](../arithmetic-positivity-theory/README.md) | Full-source positivity and Schur reductions; SAEI audits norm and polar terms they keep |
| [ArithmeticIncidencePositivity](../ArithmeticIncidencePositivity/README.md) | Strips, prime charges, shared surplus; SAEI's allocation duality prevents double spending; trains sharpen first-lag capacities |
| [BezoutValuationIncidence](../BezoutValuationIncidence/README.md) | Compact `c₀` damping chain, entrance law, dense residue modes; SAEI identifies the receiver norm and source orbit |
| [ArithmeticContinuationAndCriticalEnergy](../ArithmeticContinuationAndCriticalEnergy/README.md) | Admission and its signed averaged criterion; SAEI's radial loss identifies what it measures |
| [ArithmeticCriticalityTheory](../ArithmeticCriticalityTheory/README.md) | Continuum ground-state transforms; SAEI's finite transform separates supersolution from payment |
| [SquareRootThreshold](../SquareRootThreshold/README.md) | Width/floor dictionaries; signed sampling replaces unsigned depth mass |
| [ArithmeticOrientationTheory](../ArithmeticOrientationTheory/README.md) | Frustration index/mass of switching classes; prime triangle has index 2 |
| [ArithmeticCastelnuovoSeveri](../ArithmeticCastelnuovoSeveri/README.md) | Hyperbolic pole plane, Cartesian prime incidence; SAEI computes payment costs and train capacities |
| [TransThresholdPairCorrelation](../TransThresholdPairCorrelation/README.md) | Shares the Dirichlet-polynomial mean value at `X ≍ T`; below half damping SAEI's obstruction is `1/ζ` in the strip |
| [ArithmeticCompensationTheory](../ArithmeticCompensationTheory/README.md) | Mixed source terms; comb laws: large majorants need not mean large signed charge |
| [ArithmeticDefectRigidity](../ArithmeticDefectRigidity/README.md) | Normalized escape and signed cofactor tools that keep what a fixed-window weak limit loses |
| BSU, THIM, SSIC | Countermodels; finite incidence before the horizon limit; reading language |

---

## 2. Why

- **A critical form is a signed incidence form.** Read conductance by conductance (AIP), the zero
  form has off-diagonal charges on pairs coupled by divisibility, prime powers, archimedean density
  and the pole; strip by strip it is overlapping local pieces paid from one surplus; along the
  damping it is the norm of a source moving under an arithmetic Markov semigroup. Each closing
  argument turns a signed object into a bound and each reading has its own way to lose the sign.
- **Signed is substantive.** Sign-blind residue summation admits the source exactly above half damping
  (`summable_signBlind_iff`, `admits_of_signBlind`); the all-`+1` twin has infinite receiver energy for
  `0 < ε ≤ ½` (`not_summable_positiveTwin`). Replacing overlap signs by magnitudes turns frustrated
  patterns balanced — exactly where local payment stops being lossless.
- **Incidence is substantive.** Lossless local payment for all magnitudes ⇔ every closed walk aligned
  (`localPayment_lossless_iff_alignedCycles`); holonomy is computed from the source, not from density statistics.
- **Across scale is substantive.** The damped Möbius source is the orbit `η ↦ C_η(1/k)`
  (`centeredOperator_orbit`); continuation to smaller damping is backward evolution with no stability
  estimate in `c₀` or `ℓ²` (`not_backward_stable_l2`, `not_backward_stable_c0`). Every continuation estimate
  must use the source vector.

---

## 3. Objects and language

| Object | Meaning | Lean |
|---|---|---|
| Signed incidence form | symmetric `c`, energy `Σ c_ij f_i f_j` | `incidenceEnergy`, `IsSymmetricCoupling` |
| Local allocation | shares `a_ij ≥ 0`, `c_ij² ≤ a_ij a_ji`, `Σ_{j≠i} a_ij ≤ c_ii` | `PairAllocation`, `LocallyPayable` |
| Aligned / balanced | overlaps `≤ 0` / some switching aligns | `HasNonpositiveOverlaps`, `switchCoupling`, `IsBalanced` |
| Ground-state transform | `E(vg) = Σ v_i(Cv)_i g_i² − ½Σ c_ij v_iv_j(g_i−g_j)²` | `couplingAction`, `incidenceEnergy_mul_eq` |
| Holonomy | triangle `c_ijc_jkc_ki`; walk product of `−c_xy/|c_xy|` | `triangleHolonomy`, `walkHolonomy`, `HasAlignedCycles` |
| Compatible form, cycle witness | charges nonneg multiples of pattern `σ`; unit budgets, charge `t` on a cycle | `SignCompatible`, `cycleWitness` |
| Comparison form | same budgets, overlaps `−|c_ij|` | `comparisonCoupling` |
| Path certificate | signed supersolution + aligned walks + path budgets + packing | `PathCertificate` |
| Harmonic frame | terminal indicators harmonic off `T`; reduced coupling | `HarmonicFrame`, `exists_harmonicFrame` |
| Mirror ledger, folds | translation charges sampled at `±p_x`; even/odd folds | `mirrorCoupling`, `evenFold`, `oddFold` |
| Prime / Weil kernels | `Σ Λ(n)n^{-½}[e^{|u|}=n]`; `K(u)=2e^{-u/2}/(1−e^{-2u})−4cosh(u/2)` | `primeKernel`, `weilKernel`, `weilLedgerKernel` |
| Trains | chain, sine gauge, amplitude/grid trains, Cartesian product | `chainCoupling`, `trainSine`, `amplitudeTrain`, `productSine`, `cartesianCoupling` |
| Polar form / defect | `E_c(f) − (Σg_if_i)²`; `‖v‖² − Σ⟪g_j,v⟫²` | `polarForm`, `polarDefectForm` |
| Damping chain | BVI's centred `C_η` on `c₀`; source `r = 1/k` | `BezoutValuationIncidence.arithmeticDampingCenteredOperator`, `reciprocalObservable` |
| Residue mode | `v_d(n) = ⌊(n+1)/d⌋/(n+1) − 1/d`, eigenvalue `d^{−η}` | `BezoutValuationIncidence.normalizedResidueMode` |
| Residue term / twin | `μ(d)d^{−η}v_d`; `Σ d^{−ε}v_d` | `residueTerm`, `positiveTwin`, `DampedCoefficients`, `residueSeries` |
| Dyadic difference | `D_η(m) = P_η(m) − 2^{−η}P_η(⌊m/2⌋)` | `dyadicDifference`, `firstState` |
| Signed energy, compact negativity | `⟪Tu,u⟫`; `Q ≥ −(finite rank) − ε‖·‖²` ∀ε | `signedEnergy`, `CompactlyNegative`, `WeakConv` |
| Radial loss | `−2⟪u,u'⟫/(1+‖u‖²)` | `radialLoss` |
| Companion form | `Σ p(γ_i)² − w p'(t)²`; Lagrange price | `companionForm`, `lagrangePrice`, `pwSource` |

**Words.** *Pay locally*: each overlap paid by two shares, no point lends beyond its budget.
*Frustrated*: no switching aligns the cycle. *Supersolution*: `v > 0`, `Cv ≥ 0`. *Polar charge*: square of one
functional — the pole's shape in every face of the critical form. *Receiver norm*: `ℓ²` on the chain
coordinate (pronic energy of `P = n·Cr`). *Orbit*: `η ↦ C_η r`. *Adverse sequence*: unit-bounded profiles with
energy → negative limit; *escape*: weak limit with nonnegative energy.

---

## 4. Mechanisms

### Local payment, balance, frustration
1. **Local payment ⇒ positivity**; switching transports both (`incidenceEnergy_nonneg_of_pairAllocation`, `locallyPayable_switch_iff`).
2. **Ground-state transform**: weighted dominance under a positive gauge is a local allocation; for
   aligned forms = positive supersolution (`locallyPayable_of_supersolution`).
3. **Inverse positivity**: coercive aligned forms have `Cv = 1`, `v > 0` (`exists_pos_solution_of_coercive`).
4. **Balanced ⇒ positivity = local payability** (`nonneg_iff_locallyPayable_of_isBalanced`), via
   regularization + compactness of allocations.
5. **Rank-one charges cannot be localized** on ≥3 points (`not_locallyPayable_rankOneCoupling`).
6. **Frustrated triangle** (unit budgets, charge κ): positive iff `−½ ≤ κ ≤ 1`, payable iff `|κ| ≤ ½`.
7. **Holonomy decides balance**: triangles on complete patterns (`isBalanced_iff_triangleHolonomy_neg`,
   `switchingEquivalent_iff_triangleHolonomy_eq`); closed walks on every pattern
   (`isBalanced_iff_alignedCycles`, Harary).
8. **Signed local–global principle**: lossless for every realization ⇔ all triangles holonomy −1
   (`localPayment_lossless_iff`); on every pattern ⇔ balanced (`localPayment_lossless_iff_isBalanced`).
   Converse witnesses constructive (`frustrationWitness_not_locallyPayable`, `cycleWitness_not_locallyPayable`).
9. **Local payment = comparison-form positivity** (`locallyPayable_iff_comparison_nonneg`); exact cost =
   ground-energy gap (`locallyPayable_regularized_iff`); duality: unpayable ⇔ a nonnegative overload profile
   (`not_locallyPayable_iff_exists_overload`).
10. **Frustrated `k`-cycle**: capacity exactly `2cos(π/k)` (half-sine telescoping cotangents,
    `frustratedCycle_capacity`, `frustratedCycle_nonneg_iff`); window `½ < t ≤ 1/(2cos(π/k))` (`cycleWitness_window`).
11. **Canonical-path payment**: signed supersolution + aligned walks closing anti-aligned overlaps +
    path budgets + packing ⇒ nonnegative (`incidenceEnergy_nonneg_of_pathCertificate`). Shared hubs inflate
    their gauge: `Σ_{b∈S} c_ab v_b ≤ |c_au| v_u` (`packed_shared_step_gauge_lower_bound`). A coupling with all
    off-diagonals ≥ 0 (one > 0) has no path certificate (`isEmpty_pathCertificate_of_nonneg_offDiag`).
12. **Positivity decided on terminals** (Kron reduction): `E = R + E(f − Σf_τh_τ)`
    (`incidenceEnergy_eq_reduced_add`, `nonneg_iff_interior_and_reduced`); one frustrated overlap:
    `(t − β)² ≤ αγ` with β the effective conductance (`nonneg_iff_two_terminal`). Through an aligned coercive
    interior Kron **never creates frustration** (`HarmonicFrame.reduced_eq_sub_conductance`,
    `HarmonicFrame.pos_of_reduced_pos`); healed terminal pairs ⇒ positivity = local payment
    (`nonneg_iff_payable_of_healed`); aligning off-terminal overlaps only raises conductances (Rayleigh
    monotonicity, `HarmonicFrame.conductance_mono`, `healed_mono`).

### The prime and Weil ledgers
13. **Odd folding is the source of frustration.** Translation ledgers are aligned; even folds never
    frustrate (`evenFold_lossless`, `evenFold_prime_lossless`); an odd folded overlap is anti-aligned iff
    `w(p_x+p_y) > w(p_x−p_y)` (`oddFold_pos_iff`); monotone kernels fold aligned. The sparse prime kernel
    at positions with pairwise sums `log 2, log 3, log 5` gives an unbalanced odd triangle for all budgets
    (`oddFold_primeTriangle_not_isBalanced`, `exists_unpayable_odd_primeTriangle`).
14. **Odd Weil ledger frustrated only by primes.** `K` is nonincreasing on `(0,∞)` (`weilKernel_antitone`),
    so anti-aligned odd overlaps need `e^{p_x+p_y}` a prime power (`oddFold_pos_imp_primeSum`,
    `frustrated_walk_has_primeSum`, `oddWeilLedger_lossless_of_no_primeSum`); the prime triangle stays
    frustrated for small archimedean weight (`exists_weight_oddWeilLedger_primeTriangle_not_isBalanced`).
15. **Source-faithful calibration** `α = β = 1`: `K(log x) = −2(x³−x−1)/((x²−1)√x)` (`weilKernel_log_eq`);
    prime triangle unconditionally frustrated (`oddFold_primeTriangle_weilLedgerKernel_one_not_isBalanced`)
    and paid along `1→0→2` in gauge `(4,1,1)` (`incidenceEnergy_oddFold_primeTriangleCanonical_nonneg`);
    two frustrated overlaps pack through one hub (`incidenceEnergy_oddFold_packedPrimeCanonical_nonneg`).
    Actual samplings are not complete overlap patterns (`not_isCompleteOverlap_oddFold_arithLogGrid`).

### Chains and trains
16. **Chains are balanced** (`chainCoupling_isBalanced`): positive ⇔ lending ledger (`chain_nonneg_iff_locallyPayable`).
17. **Train capacity** `cos(π/(n+2))`, attained by sine (`uniformTrain_capacity`, `uniformTrain_capacity_sharp`);
    first-lag law `|A_S(L)| ≤ cos(π/(M+2))A_S(0)` (`autoCorr_amplitudeTrain_first_le`, `autoCorr_sineTrain_first`);
    resonant unit train is not extremal from `M = 2` (`resonant_ratio_lt_cos`).
18. **Towers add on boxes, not elsewhere.** Cartesian products split energy (`incidenceEnergy_cartesian`,
    `cartesian_lower_bound`, `cartesian_attained`, `grid_joint_capacity_attained`). On the smooth simplex
    `j + k ≤ n` the joint capacity is `cos θ + cos 2θ`, strictly below the sum (`simplex_joint_capacity`,
    `simplex_capacities_do_not_add`). In general: strict saving ⇔ support misses a box point
    (`joint_capacity_lt_iff_not_box`); slanted supports `j log p + k log q ≤ X` save (`slanted_capacities_do_not_add`).

### Poles and completion
19. **Polar defect law**: `‖v‖² − Σ⟪g_j,v⟫² ≥ 0` ⇔ polar synthesis is a contraction (`polarDefect_nonneg_iff`);
    rank one ground ratio `1 − ‖g‖²`.
20. **Completion keeps the sign iff it keeps the polar functional continuous** (`polarDefect_nonneg_of_dense`,
    `exists_polarDefect_lt_of_unbounded`).
21. **Polar solution**: aligned + nonneg polar weights ⇒ `Q(|f|) ≤ Q(f)` (`polarForm_abs_le`); coercive ⇒
    `Q ≥ 0 ⇔ Σ g_iv_i ≤ 1`, `Cv = g` (`polarForm_nonneg_iff_polarSolution`). A positive overlap can make
    sign changes cheaper (`signChange_beats_abs`) but switching moves the polar weights too.

### The damping chain in the receiver norm
22. **Receiver = chain orbit of the reciprocal**: `(C_η r)(n) = P_η(n+1)/(n+1)`, `C_sC_t r = C_{s+t}r`;
    admission ⇔ orbit in `ℓ²` (`admits_iff_summable_orbit`); RH ⇔ orbit in `ℓ²` at arbitrarily small times
    (`riemannHypothesis_iff_orbit_summable`); ⇔ first column in `ℓ²` (dyadic difference loses nothing;
    `admits_iff_summable_firstColumn`, `riemannHypothesis_iff_firstColumn_summable`). Truncations approximate at
    every horizon (`tendsto_truncation_partialEnergy`); centring indispensable (`not_summable_transition_first_column`).
23. **Residue modes**: eigenmodes `C_ηv_d = d^{−η}v_d`, `‖v_d‖² ≍ 1/d`; source `= Σ μ(d)d^{−η}v_d` coordinatewise
    (`centeredOperator_reciprocal_eq_tsum`); **Bessel, not Riesz**: `‖Σc_dv_d‖² ≤ 48Σc_d²`
    (`sum_sq_finiteResidueCombination_le`), no lower frame bound (`not_riesz_residueModes`).
24. **Sign-blind threshold ½**: envelope class `|a_d| ≤ d^{−ε}` admitted ⇔ `ε > ½` (`signBlind_admission_iff`);
    positive twin is the extremal sign pattern (`abs_residueSeries_le_abs_positiveTwin`).
25. **Backward ill-posed; unbounded generator**: no backward stability (ratio `d^t` on `v_d`); strongly
    continuous on `c₀`, `‖C_η − I‖ ≥ 1`, generator `−log d` (`tendsto_dampingFlow`, `not_exists_bounded_generator`).
26. **Hilbert–Schmidt ladder**: above 1 (`centeredOperator_l2_le`), above `1/√2` (floor jumps,
    `centeredOperator_l2_le_of_inverseRootTwo`), above golden `(√5−1)/2` (short-interval divisor sums; sharp for
    pointwise majorants, `centeredOperator_l2_le_of_goldenThreshold`), **exactly above ½** in Mellin coordinates:
    source transform `−ζ(−s)/(sζ(η−s))` on `Re s = −½`, Plancherel + dilation-symbol bound + critical mean square
    (`sum_sum_sq_centeredRow_le_halfDamping`); diagonal ⇒ no HS bound at `η ≤ ½`
    (`not_bounded_sum_sum_sq_centeredRow_of_le_half`). Only `|μ| ≤ 1` and the critical-line mean square enter.
27. **At half damping**: bounded (`exists_centeredOperator_l2_le_half`; dyadic mean values of the dilation
    symbol, `1/ζ` on the 1-line — signs of μ enter here), compact (`exists_centeredOperator_tail_l2_le_half`,
    tails `≪ K^{−1/10}`), norm limit from above (`centeredOperator_norm_tendsto_half`); receiver `ℓ²`-continuous
    (`orbit_l2_tendsto_half`); Riesz-weighted residue sums converge and Tauberian upgrade gives ordinary
    convergence (`rieszResidueSum_l2_tendsto_half`, `residuePartialSum_l2_tendsto_centeredOperator`); twins diverge
    (`positiveTwin_energy_unbounded`, `rieszTwin_energy_unbounded`). Below ½ the Mellin route needs `1/ζ` on
    `Re = η + ½`, inside the strip.

### Adverse sequences
28. **Energy splitting** under weak convergence (`tendsto_energy_splitting`).
29. **Compact negativity ⇒ adverse limits nonzero and adverse** (`adverse_weakLimit`,
    `eventually_energy_ge_weakLimit`); without it escape (`adverse_escape_of_orthonormal`).
30. **Restricted Weil form of ζ is compactly negative at every aperture** (`ccmRestrictedWeilForm_adverse_weakLimit`).

### Signed sampling
31. **Companion law (local model)**: on-line companions pay off-line depth iff `w Λ(t) ≤ 1` with enough
    companions (`companions_pay_iff`); one short: only at critical points of the node polynomial
    (`oneShort_companions_pay_iff`); two short: never (`twoShort_companions_never_pay`); complete count law
    (`exists_payable_iff`). Transfer to general sources at the local approximation error
    (`companions_pay_up_to_error`, `companions_pay_up_to_taylor`, `companions_pay_aperture_explicit`).
32. **Paley–Wiener law**: lattice companions pay all aperture-`A` sources iff density `≥ A/π` (Nyquist), price
    `A³h/(3π)` (`pwCompanions_pay`, `pwCompanions_price_sharp`, `pwCompanions_never_pay`); stable under
    displacement (`pwPerturbedCompanions_pay`); finite configurations ⇔ derivative-kernel Gram `≤ 2π/h` (a polar
    defect law, `pwConfiguration_pay_iff_gram`); at Nyquist one missing companion pays only at zeros of `s'`
    (`nyquistMinusOne_pay_iff`).

### Continuation
33. **Radial loss law**: tangential motion free; `|L| ≤ ‖u'‖` is the orientation-blind majorant
    (`radialLoss_add_tangential`, `abs_log_energy_sub_le`).

---

## 5. Pillar theorems

1. **Signed local–global principle**: balanced ⇒ positivity = payment; lossless ⇔ aligned cycles;
   cycle window `cos(π/k)`; comparison gap; canonical paths; Kron terminals
   (`nonneg_iff_locallyPayable_of_isBalanced`, `localPayment_lossless_iff_alignedCycles`, `frustratedCycle_nonneg_iff`,
   `locallyPayable_iff_comparison_nonneg`, `incidenceEnergy_nonneg_of_pathCertificate`, `nonneg_iff_payable_of_healed`).
2. **Prime origin of frustration** (`frustrated_walk_has_primeSum`, `oddFold_primeTriangle_weilLedgerKernel_one_not_isBalanced`).
3. **Polar defect law** (`polarDefect_nonneg_iff`, `polarDefect_nonneg_of_dense`, `exists_polarDefect_lt_of_unbounded`).
4. **Receiver as semigroup orbit; threshold ½** (`admits_iff_summable_orbit`, `riemannHypothesis_iff_firstColumn_summable`,
   `not_backward_stable_l2`, `signBlind_admission_iff`, `sum_sum_sq_centeredRow_le_halfDamping`,
   `exists_centeredOperator_l2_le_half`, `residuePartialSum_l2_tendsto_half`, `not_riesz_residueModes`).
5. **Train capacities** (`autoCorr_amplitudeTrain_first_le`, `cartesian_attained`, `joint_capacity_lt_iff_not_box`).
6. **Profile compactness** (`adverse_weakLimit`, `ccmRestrictedWeilForm_adverse_weakLimit`).
7. **Signed sampling** (`companions_pay_iff`, `exists_payable_iff`, `pwCompanions_pay`, `pwConfiguration_pay_iff_gram`).
8. **Radial loss** (`radialLoss_add_tangential`).

---

## 6. Traps

| Trap | Truth |
|---|---|
| Each atom paid by its own strip ⇒ form paid | Only if shares are drawn once; overlapping strips frustrate |
| Positivity ⇒ positive gauge | Only for balanced forms; frustrated positive forms have none |
| Pole as a local charge | Rank one on ≥3 points never local; pay it by a global dual norm |
| Frustrated triangle is an equal-weight artefact | Every frustrated pattern realizes the window `½ < t ≤ 1/(2cos(π/k))` |
| Resonant unit train is extremal | Sine train is, strictly from `M = 2` |
| Cross-prime cancellation on aligned trains | Capacities add exactly on boxes; savings come only from the support |
| Pronic weight is the receiver | Receiver is `ℓ²` on the chain coordinate; centring makes it exist |
| Compactness of the chain gives continuation | Backward problem ill-posed in `c₀` and `ℓ²` |
| Dense residue modes give a stable expansion | Bessel not Riesz; sign-blind majorant converges only above ½ |
| HS/bounded at ½ ⇒ progress below ½ | Below ½ the route needs `1/ζ` inside the strip; cofinal boundedness is RH |
| Column bounds = operator bound | Operator bound needs mixed Gram terms of all combinations |
| Tangent norm is the continuation criterion | Only the signed radial rate counts |
| Adverse sequence has adverse limit | Only under compact negativity |
| Finite duality is a cofinal certificate | No uniformity in the number of points without a separate estimate |
| Kron/path certificate as a structure field | Premises must be proved on the actual coupling |

---

## 7. Open problems

1. **Arithmetic holonomy at a fixed mesh**: holonomies and frustrated-part budgets of AIP's global ledger
   where `K` and prime atoms are comparable (sparse case counted by AOT's frustration index).
2. **Allocation at growing size**: payment or frustration bounds uniform in the number of strips (AIP shared surplus).
3. **Nonlocal payment of the actual ledger**: effective conductances between prime-sum terminals; the
   unhealed regime; horizon-uniform path budgets and packing for an actual AIP/PM/MC coupling.
4. **Chain on `ℓ²` below half damping**: boundedness for some `η < ½` (needs `1/ζ` on `Re = η+½`); cofinal = RH.
5. **Square-root cancellation against the residue Gram** below ½ on horizon-dependent modulus ranges
   (BVI receiver problem in residue coordinates).
6. **Companion geometry of the on-line zeros**: non-lattice companion sets (Beurling density with
   clustering); `k+1` companions within `r ≪ 1/A` at every height from the actual zero divisor; infinite tail.
7. **Compact negativity uniform in aperture** with a common normalization and compatible embeddings.
8. **Cross-prime saving off the box**: size, `X^{−2}` constant, dependence on `log q/log p`.

---

## 8. Tools

| Tool | Built | Success test |
|---|---|---|
| Allocation duality | Pillar 1, holonomy, comparison, canonical paths, Kron | Allocation for a growing arithmetic family with uniform loss |
| Continuation estimate | radial loss, orbit reformulation, ill-posedness | Horizon-uniform `‖C_a r‖_{ℓ²}` |
| Profile decomposition | splitting, compact negativity, escape | Aperture-uniform compact negativity |
| Graded functional calculus | receiver norm, residue modes, HS ladder, half-damping boundedness/compactness, Riesz expansion | `ℓ²` bounds below ½ |
| Signed sampling | companion count law, Taylor/aperture transfer, Nyquist, kernel Gram | Companion law from actual on-line zeros |
| Polar completion accounting | polar defect law, centring | Completion with proved-continuous polar functional |
| Boundary rigidity | holonomy, converse witnesses | Arithmetic diagnostic identified with a holonomy, computed from the source |

---

## 9. Contribution rules and principles

A contribution carries the full passport (source, domain, norm, observation, signed ledger, parameter
range, limit order); keeps the ledger signed except where separation is proved lossless; names the
dividing line it crosses and the input that lets it cross; is unconditional with no hypothesis
restating the sign; comes with sharpness (extremal, converse or counterexample); names its arithmetic
instance or counts as infrastructure; states the positive survivor of a no-go.

Principles: search the corpus first (strips/trains are AIP's, chain/modes BVI's, continuation ACCE's);
name the pattern and budgets; name the norm (`c₀`, pronic, `ℓ²`); keep the pole global; read the source
(`1/k`, `μ(d)`), not the operator; finite before cofinal.
