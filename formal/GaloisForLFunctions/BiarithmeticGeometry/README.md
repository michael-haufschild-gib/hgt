# Biarithmetic Geometry (BG)

**One question.** Does the joint additive and multiplicative action of the integers at finite horizon
supply signed arithmetic estimates that disappear when one keeps only multiplicative identities,
complete-period quadratic data, or a limiting energy?

Target: the critical arithmetic form shared by the corpus's RH approaches. An exact finite identity is a
foundation; an independent estimate uniform in the horizon is still required. BG keeps four things
together: the **horizon**, **signed linear data**, **both ring operations**, and **integer invariants** —
and seeks a source-derived relation between them and the analytic norm, or an exact classification of why
a proposed relation fails.

Namespace `GaloisForLFunctions.BiarithmeticGeometry`; umbrella `BiarithmeticGeometry.lean`.

---

## 1. Place in the research

Over `𝔽_q`, Frobenius is a ring map and point counts come from a complete finite object. Over `ℤ`, divisor
incidence on `{1..N}` has period `L_N = lcm(1..N)`; completing it changes the observation scale.
Complete-period quadratic data keep squared Selberg coordinates and lose signs (BVI); normalized escape
limits keep dilation but lose fixed successors (ADR); local prime-power payments exist but shared resources
need not suffice (AIP). BG studies the ring action at the horizon itself, and builds the payment/escape
algebra of explicit calibration sources (geometric prime-five towers, the golden datum).

| Programme | Interface |
|---|---|
| [BezoutValuationIncidence](../BezoutValuationIncidence/README.md) | Divisor rows, Selberg coordinates, complete-period blindness, signed prefixes |
| [TransHorizonIncidenceMechanics](../TransHorizonIncidenceMechanics/README.md) | Centered prefixes, critical Wiener convolution, additive selectivity |
| [ArithmeticDefectRigidity](../ArithmeticDefectRigidity/README.md) | Escaping energies, common cofactor Gram limits, Wiener modules, moving-successor scales |
| [ArithmeticOrientationTheory](../ArithmeticOrientationTheory/README.md) | `𝒲_{1/2}`, paid ideals, Bohr hulls, box invariant `E(s)` |
| [ArithmeticCastelnuovoSeveri](../ArithmeticCastelnuovoSeveri/README.md) | Golden datum, effectivity, `𝔽_q` calibration |
| [ArithmeticOrientationGeometry](../ArithmeticOrientationGeometry/README.md) | Correspondences, source vs sign |
| [ArithmeticIncidencePositivity](../ArithmeticIncidencePositivity/README.md) | Local prime-power payments, shared surplus, two-pole Chebyshev defect |
| [BiScaleUncertainty](../BiScaleUncertainty/README.md) | Square-root resolution, node criticality, countermodels |

Precedents: Cuntz's `ax+b`-semigroup algebra (here truncation and boundary are part of the object);
van der Geer–Schoof theta dimensions (real-valued analogues stay distinct from integer dimensions).

---

## 2. Objects and language

- **Horizon space** `HorizonSpace N`: real vector space on cells `{0..N}`; `e_j = 0` for `j > N` (absorption);
  the origin is a genuine cell; no quotient mod `N`.
- **Affine pushforward** `T_(a,b)e_j = e_(aj+b)` (`a ≥ 1`, `b ≥ 0`); successor `U = T_(1,1)`, dilation `D_a = T_(a,0)`.
- **Box invariant** `E(s) = e^s + s − 1 − ψ(e^s)` (real-valued). **Horizon torsion** `Q_N = L_N/N`,
  `horizonTorsionOrder`.
- **Weighted digit rows** `D_a(n)` (base-5 digits evaluated at `a`); **geometric tower source** `I_a(5^r) = a^r`,
  zero elsewhere; **five-tower kernel lift** `k(5^r) = f_r` (`fiveTowerKernelLift`); **critical lift**
  `k_g(5^r) = √5^r g_r` (`fiveCriticalWienerLift`, complex version).
- **Golden source** at parameter `t`: `a = αt`, `b = βt` (golden roots), arithmetic source
  `δ₁ − I_a/√5 + I_b/√5` (`goldenArithmeticSource`).
- **Cofactor action** of a kernel `k`: `P_k(n) = Σ_{j≤n} k(j)A(⌊n/j⌋)`; **paid ideal** `paidIdeal`; **cofactor graph
  domain** in `𝒲_{1/2} × ℓ²` (`cofactorGraphDomain`).
- **Escape modules**: completions of finite cofactor packets in their limiting Gram norm with `𝒲_{1/2}` acting
  by dilation (ADR). Arbitrary positive kernels with dilation bounds are calibration models, not escape states.
- **Payment obstruction**: ambient `H¹`, adverse index, capacity deficit and real weighted Euler invariant
  are four different objects.

---

## 3. Mechanisms and foundational results

### Affine geometry of the horizon
1. **Exact composition** `T_(a,b)T_(c,d) = T_(ac,ad+b)`, `D_aU = U^aD_a` (`horizonAffine_comp`, `horizon_ring_relation`).
2. **Faithful finite quotient**: images of `e_0, e_1` determine the operator; exactly `1 + (N+1)(N+2)/2` operators
   (`card_horizonAffine_image`) — polynomial size, no period.
3. **Joint rigidity**: common commutant of `U` and `D_2` is scalar (`horizon_joint_commutant`); invariant
   subspaces are exactly the `N+2` tails — indecomposable, not irreducible (`horizon_affine_indecomposable`).
4. **Exact boundary loss** `B_N(Tv,Tw) + Σ_{aj+b>N} v_jw_j = B_N(v,w)` (`horizonPairing_affine_add_boundary`);
   successor-invariant observables are constant (`horizon_successor_invariant_iff`).
5. **Normalization freedom**: every multiplicative character `w` gives an exact action `w(a)T_(a,b)`
   (`twisted_dilation_eq_iff`) — covariance cannot select the analytic normalization.
6. **Unitary rigidity**: a continuous unitary family with an invertible expanding intertwiner is trivial in
   finite dimension (`finite_affine_unitary_rigidity`) — nontrivial translation limits need infinite rank.

### Arithmetic Euler characteristic
7. **Not an ordinary index**: `E(log 3/2) = ½ + log(3/2) ∈ (0,1)`, so no `ℕ`-valued `h⁰ − h¹ = E`
   (`no_dimension_model_for_boxDefect`).
8. **Degree minus log torsion**: `E(log N) = (N − 1) − log #(ℤ/Q_Nℤ)` (`boxDefect_eq_degree_sub_log_torsion`);
   cell interpolation adds `(e^s − N) + (s − log N)` (`boxDefect_all_apertures`); period reductions
   `ℤ/L_{N+1} → ℤ/L_N` have cyclic kernels of log-order `Λ(N+1)` (`card_horizonTransition_prime_pow`,
   `boxDefect_all_apertures_kernel`).
9. **Shared-budget descent**: singleton-admissible allocations glue iff `k ≤ 1` or `B = 0`; sharp excess `kB`
   (`sharedBudget_sharp_excess`).

### Visibility and domains
10. **Exact prefix visibility**: rows with equal complete-period covariance have centred prefixes within
    `V_N(M,c) = Σ_q|R_q(M)Y_q|`, diameter exactly `2V_N` (`prefix_visibility_diameter`); covariance determines the
    prefix iff every `R_q(M)Y_q = 0` (`prefix_covariance_determines_iff`).
11. **Diagonal scaling does not determine the metric**: a 3-dimensional cyclic dilation model with correct
    diagonal and packet contraction is not homogeneous (`cyclicKernel_not_homogeneous`); stationary averaging
    restores homogeneity (`stationaryCyclicKernel_homogeneous`).
12. **Prime-log jump domain**: `Σ_p w_p‖f − τ_{log p}f‖²` finite iff weights summable or `f = 0`
    (`primeJump_summable_iff`).
13. **Pronic energy domain**: admission = summable cell energies (`receiverBounded_iff_summable_pronicCellEnergy`);
    the cofactor graph is a closed complete submodule of `𝒲 × ℓ²` (`isClosed_cofactorGraphDomain`), its input image
    = paid ideal (`paidIdeal_iff_existsUnique_cofactorGraph`), Wiener-closed iff a uniform output bound holds
    (`isClosed_range_cofactorGraphInput_iff`); payment ⇔ bounded full cofactor action
    (`receiverBounded_dirichletConv_iff_cofactorNorm`).
14. **Pronic dilation representation**: `‖D_jf‖ = ‖f‖/√j`, `D_jD_k = D_{jk}`, integrating to a unital `𝒲_{1/2}`
    representation (`pronicWienerRepresentation`); coordinates read the arithmetic floor sums
    (`pronicRowCoordinate_wiener`); every finite source horizon extends (`formalWienerCofactor_comp`). Finite pronic
    pairings are exact step Grams (`finitePronicPairing_eq_integral`).
15. **Paid perturbations** leave the whole repairing ideal unchanged (`paidIdeal_add_paid`).

### Escape-module bridge (actual Möbius receiver)
16. `P_k = A_{k⋆c_ε} − m_εA_k`; paid `k` ⇒ bounded `P_k`; admission or `‖P_k‖²/E_ε → 0` for every repairing
    kernel incl. infinite ones (`admitted_or_paidKernelAction_vanishes`); hence every actual common limit's
    annihilator contains the paid ideal and its hull lies in the obstruction hull
    (`admits_or_all_actual_annihilators`, `admits_or_all_actual_moduleHulls`). No classification of the kernels.

### The prime-five calibration laboratory
17. **Digits.** `D_a(5n+r) = r + aD_a(n)`; for `a > 1` normalized grids converge uniformly to a self-similar profile
    (`fiveDigitGrid_tendstoUniformly`); the tower source's centred prefix is exactly `−a/(5−a)·D_a(n)`
    (`fiveTower_actualPrefix_eq_digitRow`). Signed digit second moments are exact; leading digit variance cannot be
    cancelled (`fiveDigitBlock_leading_lower`); energy bounded ⇔ `Σ x_l²/5^l < ∞` (`bounded_fiveDigitPronicEnergy_iff`).
    Cofactor packets act by geometric convolution (`fiveWeightedDigitRow_convolution`).
18. **Admission threshold**: tower paid ⇔ `|a| < √5` (`receiverBounded_fiveTower_abs_iff`); golden source paid ⇔
    `αt < √5` (`receiverBounded_goldenArithmeticSource_iff`); critical parameter `t_crit = √5/α`.
19. **Payment criterion**: `k(5^r) = f_r` repairs `I_a` ⇔ `Σ(a²/5)^l(Σ_{r≤l} f_r/a^r)² < ∞`
    (`receiverBounded_fiveTowerKernelLift_iff`); at criticality ⇔ partial sums of `g` square-summable
    (`receiverBounded_critical_fiveTower_iff_partialSums`, `mem_paidIdeal_golden_critical_fiveTower_iff`). Lifts are
    isometric (`norm_fiveCriticalWienerLift`).
20. **Critical paid ideal is not closed.** Finite zero-sum repairs converge to an unpaid kernel
    (`not_isClosed_golden_critical_paidIdeal`); closure of the critical coefficient domain = kernel of total
    evaluation, distance = |total| (`closure_criticalCoefficientDomain`, `criticalTotalEvaluation_minimum_distance`);
    zero-sum lifts lie in the closure (`fiveComplexCriticalWienerLift_mem_closure_paidIdeal`). Power-tail family
    pays iff exponent > ½ (`powerTailWiener_mem_paidIdeal_iff`); exponents in `(0, ½)` are independent, so both the
    payment quotient and the closure defect have Hamel dimension exactly continuum
    (`rank_criticalGoldenPaymentQuotient_eq_continuum`, `rank_criticalGoldenPaymentClosureDefect_eq_continuum`).
21. **Golden source algebra.** Exact inverse coefficients `−(a^n − b^n)/√5` (`goldenInverseSeriesAt_coeff`); mean
    `(5−6t+t²)/(5−5t+t²)`; golden paid ideal = primary tower's (`paidIdeal_goldenArithmeticSource`). Divisor
    response at valuation `M` decreases with valuation and damping (`goldenDivisorProfile_antitone`). Intrinsic
    golden counting changes the receiver: at `t = 1` the intrinsic row is constant while the ordinary-floor receiver
    escapes (`goldenIntrinsicReceiverSeries_one`) — calibrations must name their counting kernel.
22. **Normalized cube test.** `z ↦ z³/5` keeps product 5 but produces negative point counts
    (`golden_pointCount_positive_but_normalizedCube_negative`); integral trace survivors are classified and pure
    (`exists_normalizedCubicTrace_iff`, `normalizedCubicRoot_survivor_pure`).
23. **Analytic helpers**: geometric pole extraction (`geometricPole_extraction`), geometric future tail
    (`tsum_norm_geometricFutureTail_le`), finite geometric convolution bound
    (`sum_sq_finiteGeometricConvolution_le`), shell completion is a line (`finrank_geometricShellTangentSpace`),
    digital circle seed has Fourier coefficients `−ζ(s)/(Ls)` (`fourierCoeff_digitalCircleProfile`).

---

## 4. Pillar theorems

1. Affine horizon geometry (`horizonAffine_comp`, `card_horizonAffine_image`, `horizon_joint_commutant`, `horizonPairing_affine_add_boundary`).
2. Arithmetic Euler formula (`no_dimension_model_for_boxDefect`, `boxDefect_eq_degree_sub_log_torsion`).
3. Exact visibility (`prefix_visibility_diameter`).
4. Payment = graph domain (`paidIdeal_iff_existsUnique_cofactorGraph`, `isClosed_range_cofactorGraphInput_iff`).
5. Module–ideal bridge (`admits_or_all_actual_moduleHulls`).
6. Prime-five / golden payment classification (`receiverBounded_fiveTower_abs_iff`, `receiverBounded_fiveTowerKernelLift_iff`, `not_isClosed_golden_critical_paidIdeal`, `rank_criticalGoldenPaymentQuotient_eq_continuum`).

---

## 5. Traps

1. Affine identities need a normalization: scalar character twists preserve them.
2. Integer indices and real charges are complementary; `E` is degree minus log torsion, not a dimension.
3. Local existence is not a sheaf axiom; restrictions and gluing must be proved; linearization can lose the
   unpaid inequalities.
4. Curve `H¹` has dimension `2g` under RH; a purity obstruction must be a different group or adverse part.
5. Truncations of a repairing kernel need not repair; use the full-action norm bound.
6. A finite Gram limit does not control moving tails; white noise has a unique antipodal extension.
7. Structural (Class III) selectivity is not source selectivity.
8. Paid ideals need not be Wiener closed; zero evaluation is weaker than critical payment.
9. Golden calibration depends on the counting kernel (ordinary floor vs intrinsic).
10. Square-root energy scale for moving successors is excluded (ADR: raw `o(k^{2(1−ε)})`, recentred `o(k^{1−ε})`).

---

## 6. Open problems

- **Horizon-complete observation**: sign visibility between prefix and full period at polynomial horizon.
- **Escape classification**: classify actual common-limit Wiener modules; compare annihilators with paid ideals;
  golden family and translated-zero-hull comparison.
- **Critical translations**: a scale beyond `k^{1−ε}` at which moving successors keep source information, with
  dilation covariance and limit order.
- **Arithmetic payment theory**: an allocation site/complex keeping shared capacity, relating its integer
  obstruction to degree/torsion; exact sequences, transition laws, duality.
- **Quantitative Class III**: bound signed off-diagonal Vaughan entries using joint `+`/`×` structure.
- **Stepanov at integer horizon**: finite-field counts in packet coordinates; a simultaneous prime-power vanishing
  mechanism failing for parity twins.
- **Infinite-rank coercivity**: transfer prime-coordinate bounds to the dense logarithmic orbit.
- **Amplification and orientation**: specify operations and conductor; an independently positive polarization
  compatible with ring action and normalization.

---

## 7. Selectivity and success criteria

Battery: genuine curves, golden datum, Beurling systems with off-line zeros, shifted pairs, single-prime Euler
deformations, parity twins, node deletions `log 4`, `log 6`. Affine theorems are structural (Class III) and make
no claim about Euler weights; the Euler formula uses actual weights; neither is an orientation theorem.

Full success needs five gates: recover curve `H¹` and duality with the right obstruction; pass the battery;
recover PNT, VK band and Guth–Maynard density in source coordinates; produce new unconditional analytic output or
an actual escape-family classification; formalize every finite-horizon claim without new premises. A contribution
names its source object and horizon, keeps signs, states its selectivity class, separates structural
classification from analytic estimate, and records the positive survivor of a failed mechanism.
