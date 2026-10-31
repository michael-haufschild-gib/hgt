# Signed Arithmetic Energy and Incidence (SAEI)

Namespace `GaloisForLFunctions.SignedArithmeticEnergyIncidence`; umbrella
`SignedArithmeticEnergyIncidence.lean`; 53 modules. Everything unconditional; RH appears only in
two exact equivalences (§8).

## 1. Motivation

Every positivity argument for a critical form does four things to a signed quadratic energy: it
**pays** it from local budgets, **completes** it in a norm, **transports** it along a parameter
(damping, aperture), and **decomposes** its adverse sequences. SAEI owns no critical form. It proves
the sharp laws of these four operations on finite incidence forms, Hilbert-space forms and the
Bezout damping chain, and calibrates them on the actual arithmetic ledgers (odd Weil ledger, prime
towers, damped Möbius source, restricted Weil form). Its question: which part of the sign is decided
by *incidence* (who overlaps whom, with which orientation), and which part needs *cancellation*
(the signs of $\mu$, the zeros of $\zeta$)?

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Signed incidence form | `incidenceEnergy`, `IsSymmetricCoupling`, `couplingAction` | $E(f)=\sum c_{ij}f_if_j$; $c_{ii}$ budget, $c_{ij}$ overlap charge |
| Local allocation | `PairAllocation`, `LocallyPayable` | shares $a_{ij}\ge0$, $c_{ij}^2\le a_{ij}a_{ji}$, $\sum_{j\ne i}a_{ij}\le c_{ii}$ |
| Orientation | `HasNonpositiveOverlaps`, `switchCoupling`, `IsBalanced`, `SignPattern`, `SignCompatible` | aligned = overlap $\le0$; balanced = some $\pm1$ switching aligns all |
| Holonomy | `triangleHolonomy`, `edgeSign`, `walkHolonomy`, `HasAlignedCycles` | product of $-c_{xy}/|c_{xy}|$ along a closed walk; switching invariant |
| Comparison form | `comparisonCoupling` | same budgets, overlaps $-|c_{ij}|$ |
| Witnesses | `rankOneCoupling`, `triangleCoupling`, `frustrationWitness`, `cycleWitness` | positive unpayable forms |
| Nonlocal certificates | `PathCertificate`, `HarmonicFrame`, `HarmonicFrame.reduced`, `HarmonicFrame.conductance` | gauge + aligned walks + packing; Kron reduction to terminals |
| Folds and kernels | `oddFold`, `evenFold`, `mirrorCoupling`, `primeKernel`, `weilLedgerKernel`, `arithLogGrid`, `primeTrianglePos`, `packedPrimePos` | translation ledger sampled at $\pm p_x$; $w=\alpha K+\beta\cdot$prime atoms |
| Trains | `chainCoupling`, `trainSine`, `amplitudeTrain`, `cartesianCoupling`, `gridMass`, `gridRowCharge`, `simplexPsi`, `slantedSupport`, `CarriedBy` | prime towers $\{p^j\}$, boxes, simplices, smooth-number supports |
| Polar forms | `polarForm`, `polarDefectForm` | $E(f)-(\sum g_if_i)^2$; $\|v\|^2-\sum\langle g_j,v\rangle^2$ |
| Damping chain | `arithmeticDampingCenteredOperator` (BVI), `reciprocalObservable`, `firstState`, `dampingFlow` | $C_\eta$ on $c_0$, $C_sC_t=C_{s+t}$; source $r(k)=1/k$ |
| Source profiles | `sourceProfile`, `columnProfile`, `dilatedSource`, `combinedProfile`, `orbitCoord`, `dyadicDifference` | $P_\eta(x)=A_\eta(\lfloor x\rfloor)-\rho_\eta x$; $C(n,k)=(K/N)\Delta_K(N)$ |
| Mellin symbols | `criticalSymbol`, `dilationSymbol`, `zetaHalfWeight`, `criticalWeightMass` | $MP_\eta(-\tfrac12+it)=-\zeta(-s)/(s\zeta(\eta-s))$ |
| Residue modes | `normalizedResidueProfile` (BVI), `residueTerm`, `residueSeries`, `positiveTwin`, `DampedCoefficients`, `finiteResidueSum`, `rieszResidueSum`, `residuePartialSum`, `gramKernel` | $v_d(n)=-\{(n+1)/d\}/(n+1)$, $C_\eta v_d=d^{-\eta}v_d$ |
| Signed energies | `signedEnergy`, `CompactlyNegative`, `compactPerturbedEnergy`, `WeakConv`, `WeakConvC` | $\langle Tu,u\rangle$; $Q\ge-$finite rank$-\varepsilon\|\cdot\|^2$ |
| Companion forms | `companionForm`, `lagrangePrice`, `sampleForm`, `taylorPoly`, `trigSourceDeriv` | $\sum p(\gamma_i)^2-wp'(t)^2$; $\Lambda(t)=\sum\ell_i'(t)^2$ |
| Paley–Wiener | `pwSource`, `pwDeriv`, `pwKernel`, `pwGram`, `configurationForm`, `pwSampleWeight`, `sincDensity` | aperture-$A$ sources, lattice $t_0+h\mathbb Z$ |
| Radial loss | `radialLoss` | $L=-2\langle u,u'\rangle/(1+\|u\|^2)$ |

## 3. Language

- **Pay locally**: every overlap paid by two shares; no point lends beyond its budget.
- **Aligned / anti-aligned** overlap: charge $<0$ / $>0$ (edge sign $-c/|c|=+1/-1$). **Frustrated** cycle: `walkHolonomy` $=-1$ (equivalently `triangleHolonomy` $c_{ij}c_{jk}c_{ki}>0$); no switching aligns it.
- **Supersolution**: $v>0$, $Cv\ge0$. **Ground-state transform**: $E(vg)=\sum v(Cv)g^2-\tfrac12\sum c_{ij}v_iv_j(g_i-g_j)^2$.
- **Terminals**: endpoints of anti-aligned overlaps; **effective conductance** $\beta_{\sigma\tau}$: Kron-reduced aligned coupling.
- **Polar charge**: square of one linear functional (a pole).
- **Receiver norm**: $\ell^2$ on the chain coordinate $n\mapsto(C_\eta b)(n)$ (= pronic energy of $P$); not the pronic weight on the chain coordinate.
- **Admission** at $\eta$: orbit $C_\eta r\in\ell^2$. **Positive twin**: residue series with every $\mu(d)$ replaced by $1$.
- **Sign-blind**: uses only $|\mu|\le1$. **Adverse sequence**: unit profiles with $Q\to\mu<0$; **escape**: weak limit carries no negativity.
- **Companion**: on-line zero near an off-line cluster of squared-depth mass $w$ (local model of $\Xi$).

## 4. Mechanisms

**A. Local payment and orientation (finite forms)**
1. Local payment ⇒ $E\ge0$ (unspent budget + binary forms); switching transports both.
2. Discrete Allegretto–Piepenbrink: aligned + $E\ge0$ ⇒ locally payable (coercive ⇒ $Cv=1$ has $v>0$; regularize; compactness of allocations). Balanced ⇒ positivity ⇔ local payment.
3. Rank-one charges on $\ge3$ points are positive and never locally payable: poles are global.
4. Holonomy classifies sign patterns up to switching (complete gauge invariant); Harary: balanced ⇔ every closed walk aligned.
5. **Signed local–global principle**: every nonnegative form with pattern $\sigma$ is locally payable ⇔ $\sigma$ balanced; frustrated patterns carry explicit positive unpayable witnesses.
6. Frustration halves capacity: frustrated $k$-cycle locally payable ⇔ $t\le\tfrac12$, nonnegative ⇔ $2t\cos(\pi/k)\le1$ (half-sine gauge, exact); triangle window $\tfrac12<\kappa\le1$.
7. Local payment = positivity of the comparison form; exact price of frustration = gap of the two ground energies; allocation duality: unpayable ⇔ a nonnegative overload profile.
8. Polar form with aligned overlaps and $g\ge0$: one-signed profiles are worst; $Q\ge0$ ⇔ $\ell(v)\le1$ for $Cv=g$. Adverse sign-changing profiles come only from anti-aligned overlaps.

**B. Nonlocal certificates**
9. Canonical paths: supersolution + aligned walks + path budgets + packing ⇒ $E\ge0$; shared hub edges cap routed demand $\sum_bc_{ab}v_b\le|c_{au}|v_u$.
10. Kron reduction: $E(f)=R(f|_T)+E(g)$, no cross term; $E\ge0$ ⇔ interior $\ge0$ and $R\ge0$; all frustration lives on terminals. One frustrated overlap: $(t-\beta)^2\le\alpha\gamma$ with effective conductance $\beta$ (exact price; one path overpays).
11. Kron never creates frustration ($h_\tau\ge0$, $R=c-\beta$, $\beta\ge0$); healed terminal pairs ⇒ positivity = local payment of $R$; Rayleigh monotonicity in aligned overlaps.

**C. Arithmetic ledgers**
12. Odd folding is the source of frustration: even folds and translation ledgers aligned; odd fold anti-aligned ⇔ $w(p_x+p_y)>w(p_x-p_y)$.
13. $K$ nonincreasing on $(0,\infty)$ ⇒ odd Weil ledger frustrated only through prime sums $e^{p_x+p_y}=p^m$; samplings free of prime sums are lossless.
14. Source-faithful calibration $\alpha=\beta=1$ on sums $\log2,\log3,\log5$: holonomy $+1$, frustrated for every budget, yet positive at budgets $(6,2,21)$ via the path $1\to0\to2$; two frustrated triangles sharing a hub need $(5,3,43,41)$ and gauge $(8,1,1,1)$. Pure prime kernel ($\alpha=0$) admits no path certificate.

**D. Prime trains**
15. Chains are balanced; positive ⇔ lending ledger; uniform train capacity $\cos(\pi/(n+2))$, sine-attained.
16. Amplitude train lag law $A_S(L)=(\sum f_kf_{k+1})A_g(0)$: sine train extremal, resonant train strictly not ($M\ge2$).
17. Cartesian products add ground energies: aligned towers never cancel. Capacities add **exactly on boxes**: strict saving ⇔ support misses a box point; simplex $j+k\le n$ joint capacity $\cos\theta+\cos2\theta$, $\theta=\pi/(n+3)$; smooth-number supports $j\log p+k\log q\le X$ never add.

**E. Poles and completion**
18. Polar defect law: $Q\ge0$ ⇔ polar synthesis is a contraction (Gram $\le I$); rank one: ground ratio $1-\|g\|^2$ on the representer.
19. Completion keeps the sign iff the polar functional stays continuous; unbounded ⇒ $\inf Q=-\infty$.

**F. The damping chain in the receiver norm**
20. Receiver = chain orbit: $(C_\eta r)(n)=P_\eta(n+1)/(n+1)$; damping is time; admission ⇔ orbit $\in\ell^2$ ⇔ first column $\in\ell^2$ (dyadic difference loses nothing); centring indispensable.
21. Source = damped Möbius residue series $\sum\mu(d)d^{-\eta}v_d$, absolutely convergent; residue modes diagonalize $C_\eta$.
22. Backward continuation ill-posed in $\ell^2$ and $c_0$ (ratio $d^t$ on $v_d$); flow strongly continuous, not norm continuous, generator $-\log d$ unbounded.
23. Sign-blind resolution exactly $\tfrac12$: every row $|a_d|\le d^{-\varepsilon}$ admitted ⇔ $\varepsilon>\tfrac12$; the positive twin dominates pointwise (modes $\le0$) and diverges for $\varepsilon\le\tfrac12$.
24. Hilbert–Schmidt ladder: size of source ($\eta>1$); floor-jump sparsity + interpolation ($\eta>1/\sqrt2$); divisor short-interval bound ($\eta^2+\eta>1$); Mellin columns with critical-line mean square ($\eta>\tfrac12$, sharp: diagonal $\ge(1-\rho)K^{-\eta}$).
25. Mellin: $P_\eta=-\sum\mu(d)d^{-\eta}\{x/d\}$; $MP_\eta=-\zeta(-s)/(s\zeta(\eta-s))$ on $\Re s=-\tfrac12$; columns multiply by $K^{s-\eta}-(K+1)^{s-\eta}$; Plancherel for profiles $\ll\min(x^a,x^{1-a})$.
26. At $\eta=\tfrac12$: bounded (head = Dirichlet polynomial, MVT; tail = Fourier of a step function, Plancherel; weight $\ll T^{-5/4}\log^4T$ via $1/\zeta\ll\log^2$ on the 1-line), compact (tails $\ll K^{-1/10}$), norm limit of $C_\eta$, receiver $\ell^2$-continuous, Riesz and plain residue expansions converge. Signs of $\mu$ enter only through $1/\zeta$ near $\Re=1$.
27. Residue modes are Bessel ($\le48\sum c_d^2$, Gram $\le6\min^{-1/4}\max^{-3/4}$) but not Riesz: the receiver at $\tfrac12$ exists by cancellation against a non-orthogonal Gram while $\sum\mu(d)^2/d=\infty$.

**G. Adverse sequences**
28. Energy splitting under weak convergence; compact negativity ⇒ weak lsc, adverse limits nonzero and at least as adverse; noncompact negative part ⇒ escape.
29. Restricted Weil form at fixed aperture $=\|u\|^2+\langle R(Ju),Ju\rangle$ with $J$ compact ⇒ adverse profiles cannot vanish.

**H. Signed sampling (off-line depth vs on-line companions)**
30. Local model: deg $<\#s$ ⇒ pays ⇔ $w\Lambda(t)\le1$ (exact); one short ⇔ $N'(t)=0$; two short never. Smooth sources: loss $2\#s(M\delta^d/d!)^2$; aperture-$A$ trig sources: $2\#s((A\delta)^dm/d!)^2$, explicit in companion spacing.
31. Paley–Wiener: lattice pays all aperture-$A$ sources ⇔ density $1/h\ge A/\pi$, sharp price $A^3h/(3\pi)$; below Nyquist never; perturbation $2A\delta\le\varepsilon$ costs $(1-\varepsilon)^2$; finite configurations ⇔ kernel Gram $\le2\pi/h$ (polar defect law); at $Ah=\pi$ removing one companion pays only at critical points of its sinc.

**I. Continuation**
32. Radial loss: tangential motion free; $|L|\le\|u'\|$ (orientation-blind majorant); log-energy moves by $-\int L$.

## 5. Pillar theorems

| Theorem | Lean | Content |
|---|---|---|
| Signed local–global principle | `nonneg_iff_locallyPayable_of_isBalanced`, `localPayment_lossless_iff_isBalanced`, `localPayment_lossless_iff`, `switchingEquivalent_iff_triangleHolonomy_eq` | lossless local payment ⇔ balance ⇔ aligned holonomy |
| Frustrated capacity | `frustratedCycle_nonneg_iff`, `cycleWitness_window`, `locallyPayable_iff_comparison_nonneg`, `not_locallyPayable_iff_exists_overload` | $2t\cos(\pi/k)\le1$ vs $t\le\tfrac12$; exact price |
| Terminal reduction | `nonneg_iff_interior_and_reduced`, `nonneg_iff_two_terminal`, `nonneg_iff_payable_of_healed`, `HarmonicFrame.conductance_mono` | frustration lives on terminals; Kron never creates it |
| Prime origin of frustration | `frustrated_walk_has_primeSum`, `oddFold_primeTriangle_weilLedgerKernel_one_not_isBalanced`, `incidenceEnergy_oddFold_primeTriangleCanonical_nonneg` | frustrated yet path-paid source-faithful prime triangle |
| Train capacities | `uniformTrain_capacity`, `autoCorr_amplitudeTrain_first_le`, `cartesian_lower_bound`, `joint_capacity_lt_iff_not_box`, `slanted_capacities_do_not_add`, `simplex_capacities_do_not_add` | towers add on boxes only |
| Polar defect law | `polarDefect_nonneg_iff`, `polarDefect_nonneg_iff_norm_le_one`, `exists_polarDefect_lt_of_unbounded` | poles paid by one dual norm |
| Receiver = orbit | `centeredOperator_reciprocal_apply`, `admits_iff_summable_orbit`, `admits_iff_summable_firstColumn`, `centeredOperator_reciprocal_eq_tsum` | admission as $\ell^2$ of a semigroup orbit |
| Sign-blind threshold | `signBlind_admission_iff`, `summable_signBlind_iff`, `not_summable_positiveTwin`, `abs_residueSeries_le_abs_positiveTwin` | size alone reaches exactly $\tfrac12$ |
| Continuation is not an operator estimate | `not_backward_stable_l2`, `not_backward_stable_c0`, `not_exists_bounded_generator`, `one_le_norm_dampingFlow_sub_id` | must read the source |
| HS ladder | `centeredOperator_l2_le`, `centeredOperator_l2_le_of_inverseRootTwo`, `centeredOperator_l2_le_of_goldenThreshold`, `sum_sum_sq_centeredRow_le_halfDamping`, `not_bounded_sum_sum_sq_centeredRow_of_le_half` | HS ⇔ $\eta>\tfrac12$ |
| Half damping | `exists_centeredOperator_l2_le_half`, `centeredOperator_half_tail_small`, `centeredOperator_norm_tendsto_half`, `orbit_l2_tendsto_half`, `residuePartialSum_l2_tendsto_half`, `positiveTwin_energy_unbounded` | bounded, compact, continuous at $\tfrac12$ |
| Bessel not Riesz | `sum_sq_finiteResidueCombination_le`, `not_riesz_residueModes` | cancellation, not coefficient size |
| Adverse profiles | `adverse_weakLimit`, `adverse_escape_of_orthonormal`, `ccmRestrictedWeilForm_adverse_weakLimit` | no escape at fixed aperture |
| Companion count law | `companions_pay_iff`, `oneShort_companions_pay_iff`, `exists_payable_iff`, `companions_pay_aperture_explicit` | companions vs local degrees of freedom |
| Nyquist law | `pwCompanions_pay`, `pwCompanions_price_sharp`, `pwCompanions_never_pay`, `pwPerturbedCompanions_pay`, `pwConfiguration_pay_iff_gram`, `nyquistMinusOne_pay_iff` | continuum companion law |
| Radial loss | `radialLoss_add_tangential`, `abs_radialLoss_le`, `hasDerivAt_log_one_add_energy` | only radial motion costs |

## 6. Tools

**Developed**
- Allocation calculus: `PairAllocation`, switching, regularization `regularizedCoupling`, compactness of allocations, comparison form, overload dual certificate.
- Ground-state transform `incidenceEnergy_mul_eq`; weighted dominance `locallyPayable_of_weightedDominance`; supersolution criterion.
- Holonomy toolkit (triangle, walk, Harary switching, shortest frustrated simple cycle `exists_nodup_frustrated`).
- Half-sine / sine gauges with cotangent telescope; Poincaré gap `frustratedCycle_poincare`.
- `PathCertificate` with packing; `HarmonicFrame` (Kron reduction, effective conductance, discrete minimum principle, Rayleigh monotonicity).
- Certified interval arithmetic for $K(\log x)$ (`weilKernel_log_eq`, log bounds) giving unconditional orientations.
- Trains: chain/lending ledger, amplitude-train lag law, Cartesian product splitting, simplex gauge `simplexGauge`, box-gap compactness argument.
- Receiver toolkit: `c0OfTendsto`, orbit/first-column/dyadic-difference equivalences, floor-jump sparsity `sum_floorJump_le`, short-interval divisor bound `abs_centeredPrefix_sub_le_short`, interpolation exponents `interpExp`, `goldenExp`, below-$\sqrt N$ zeta-product summation `sum_belowSqrt_rpow_le`.
- Mellin machinery: `mellin_fractSeries`, `integral_sq_div_sq_eq_mellin`, `mellinConvergent_of_two_sided`, dilation symbol bound `norm_cpow_sub_cpow_le`, head/tail split `head_eq_dirPoly`, `tail_eq_neg_mul_fourier`, dyadic summation `integral_le_of_even_dyadic`, continuity in damping `continuousAt_centeredRow`.
- Residue-mode Gram/Schur test, Riesz-mean Tauberian `residuePartialSum_tauberian`.
- Hilbert space: energy splitting, compact negativity, `tendsto_of_weakConvC`, `tendsto_of_dense_of_bounded`.
- Sampling: Lagrange price, Taylor chain bound `abs_sub_taylorSum_le`, lattice Parseval `hasSum_sq_pwSource_lattice`, polarized Parseval, derivative sampling formula `hasSum_pwDeriv_eq`, Nyquist defect bump.

**To build**
- Allocation/frustration bounds for growing arithmetic families with uniform loss (number of strips → ∞).
- Effective conductances between prime-sum terminals of the actual odd Weil ledger at fixed mesh; horizon-uniform path budgets and packing.
- $\ell^2$ bounds for $C_\eta$ below $\tfrac12$ (needs $1/\zeta$ on $\Re=\eta+\tfrac12<1$); square-root cancellation against the residue Gram.
- Compact negativity uniform in aperture for the restricted Weil form.
- Companion law from the actual on-line zero divisor: non-lattice companion sets, $\asymp\log T$ companions vs $\asymp A$ degrees of freedom per unit height.
- Explicit size of cross-prime saving off the box as a function of $\log q/\log p$ (current gap constant is non-explicit).

## 7. Open questions

1. Holonomy and frustrated budgets of the full odd Weil ledger where $K$ and prime atoms are comparable; is the prime-triangle certificate scalable?
2. Is there a nonlocal (Kron/path) certificate uniform in the number of sampling points?
3. Does the $\ell^2$ boundedness of $C_\eta$ persist for some $\eta<\tfrac12$ unconditionally? (Cofinal persistence is RH.)
4. What arithmetic property of $\mu$ beyond PNT-strength $1/\zeta(1+it)$ controls cancellation against the residue Gram below $\tfrac12$?
5. Does compact negativity of the restricted Weil form hold uniformly in aperture, and with what rate of the finite-rank part?
6. Companion count law with actual zeros: does the Nyquist density $A/\pi$ match zero density $\frac1{2\pi}\log T$ at the relevant aperture?
7. Exact size of the smooth-number cross-prime saving; does it grow with the number of primes?
8. Can the radial loss of the damped source be bounded by a signed radial rate rather than the tangent norm?

## 8. Traps

| Trap | Truth |
|---|---|
| Each overlap paid by its own strip ⇒ form paid | Only for balanced patterns; frustrated patterns carry positive unpayable witnesses |
| Positivity ⇒ positive gauge | Only for aligned/balanced forms |
| Pole as a local charge | Rank one on $\ge3$ points never local; paid by one global dual norm |
| Pairwise-complete overlap patterns | False on actual arithmetic samplings ($\Lambda(6)=0$) |
| Prime-kernel frustration paid by paths | Pure prime kernel admits no path certificate; archimedean part supplies aligned steps |
| Canonical path is the exact price | Effective conductance is; one path overpays |
| Resonant unit train is extremal | Sine train is, strictly from $M=2$ |
| Cross-prime cancellation on aligned trains | Capacities add exactly on boxes |
| Pronic weight is the receiver norm | Receiver is $\ell^2$ on the chain coordinate |
| Compactness of $C_\eta$ gives continuation | Backward problem ill-posed; generator unbounded |
| Dense residue modes give a stable expansion | Bessel, not Riesz |
| HS/bounded at $\tfrac12$ ⇒ progress below $\tfrac12$ | Needs $1/\zeta$ inside the strip; `riemannHypothesis_iff_orbit_summable`, `riemannHypothesis_iff_firstColumn_summable` are exact RH equivalences |
| Pointwise kernel majorants reach $\tfrac12$ | Stop at $1/\sqrt2$, golden ratio; only Mellin columns reach $\tfrac12$ |
| Column bounds ⇒ operator bound | Operator bound at $\tfrac12$ needs the combined symbol (mixed Gram terms) |
| Adverse sequence has adverse limit | Only under compact negativity |
| Finite duality is a cofinal certificate | No uniformity in the number of points/aperture |
| Companion laws apply to $\zeta$ | Proved in local polynomial / Paley–Wiener models; transfer to actual zeros open |
| Path/Kron certificate as structure field | Premises (supersolution, coercivity, packing) must be proved on the actual coupling |

## 9. Context

| Programme | Relation |
|---|---|
| RHTower (19 imports) | inputs: Weil kernel sign, CCM restricted Weil form, zero-free strip bounds for $1/\zeta$, convexity, critical-line mean square, Dirichlet MVT, Riesz means of $\mu$ on the 1-line, fractional-part zeta |
| HTGeometry (4) | Mellin–Plancherel on lines, two-sided exponential moments, real Dirichlet series, Lagrange-basis derivative bounds |
| BezoutValuationIncidence (3) | owns $C_\eta$, semigroup law, residue-mode completeness; SAEI identifies its receiver norm, threshold and compactness; BVI re-imports SAEI for spectrum and residue coordinates |
| ArithmeticContinuationAndCriticalEnergy (3) | owns `dampedMobiusEnergy`, `Admits`, cofinal admission ⇔ RH; SAEI explains what admission measures |
| ArithmeticIncidencePositivity (1) | resonant train witness; AIP re-imports SAEI for allocation synthesis |
| ArithmeticOrientationTheory (5 importers) | builds frustration index, damping-flow orientation and lattice odd ledger on SAEI's holonomy theory |
| goldbach, MainTheorems | consume the RH bridges |
| SquareRootThreshold, TransThresholdPairCorrelation | width/floor dictionaries and Dirichlet-polynomial MVT at $X\asymp T$ share the signed-sampling and half-damping mechanisms (no imports) |

## 10. Big picture

SAEI separates what a positivity proof can get from *structure* from what it must get from
*cancellation*. Structure is powerful but bounded: orientation (holonomy) decides exactly when local
bookkeeping suffices; Kron reduction pushes all difficulty onto a few frustrated terminals; trains,
boxes and companions give sharp capacities. In the arithmetic ledgers the frustration is real and is
created only by primes, and the obstructions are always one step beyond the structure: the prime
triangle is frustrated, the smooth-number support saves across primes, the residue modes are not a
Riesz family. On the analytic side the programme pins the barrier precisely: every sign-blind
argument stops at half damping, everything up to and including half damping is unconditional (with
PNT-strength input), and continuation below it cannot be an operator estimate — it has to read the
Möbius source and needs $1/\zeta$ inside the critical strip, which is RH-strength. The lesson for the
RH programme: positivity frameworks that only manage budgets, norms or sizes will saturate at the
same threshold; the missing ingredient is a signed cancellation statement about $\mu$ (equivalently
about zeros), and SAEI supplies the exact interfaces — terminal conductances, polar dual norms,
companion counts, aperture-uniform compactness — where that statement would have to enter.
