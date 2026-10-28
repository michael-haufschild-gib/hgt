# Signed Arithmetic Energy and Incidence (SAEI)

Namespace `GaloisForLFunctions.SignedArithmeticEnergyIncidence`; umbrella `SignedArithmeticEnergyIncidence.lean`.

**Question.** How does exact multiplicative incidence constrain signed quadratic energies across
scale — and which constraints survive a change of coordinates, a regularization, or a completion?

SAEI owns no critical form. It is the interface theory of the critical-energy programmes and studies
four operations every closing argument performs on a signed form: **paying** it from local resources,
**completing** it in a new norm, **transporting** it along a parameter, **decomposing** its adverse
sequences. It proves sharp finite/Hilbert-space laws and applies them to AIP's prime lag charges,
BVI's damped Möbius source and damping chain, and ACCE's continuation criterion.

---

## 1. Place in the research

Supporting framework for the incidence (AIP), Möbius-continuation (BVI/ACCE) and compensation routes.
Local PSD or local payment is never the full continuum sign; canonical-path and Kron certificates are
methods whose premises (supersolution, coercivity, horizon-uniform packing) must be proved on each
route's actual coupling.

| Programme | Connection |
|---|---|
| arithmetic-positivity-theory | Full-source positivity and Schur reductions; SAEI audits norm and polar terms |
| ArithmeticIncidencePositivity | Strips, prime charges, shared surplus; allocation duality prevents double spending |
| BezoutValuationIncidence | Damping chain, entrance law, residue modes; SAEI identifies receiver norm and source orbit |
| ArithmeticContinuationAndCriticalEnergy | Admission criterion; radial loss identifies what it measures |
| ArithmeticCriticalityTheory | Continuum ground-state transforms; finite transform separates supersolution from payment |
| SquareRootThreshold | Width/floor dictionaries; signed sampling replaces unsigned depth mass |
| ArithmeticOrientationTheory | Frustration index of switching classes; prime triangle has index 2 |
| ArithmeticCastelnuovoSeveri | Pole plane, Cartesian prime incidence; train capacities |
| TransThresholdPairCorrelation | Shares the Dirichlet-polynomial mean value at $X\asymp T$ |
| ArithmeticCompensationTheory, ArithmeticDefectRigidity | Comb laws; signed cofactor tools that keep what weak limits lose |

---

## 2. Why

- **A critical form is a signed incidence form**: conductance by conductance (AIP), strip by strip
  (overlapping local pieces paid from one surplus), or along the damping (a source moving under an
  arithmetic Markov semigroup). Each reading has its own way to lose the sign.
- **Signed is substantive.** Sign-blind residue summation admits the source exactly above half damping;
  the all-$+1$ twin has infinite receiver energy for $0<\varepsilon\le\tfrac12$.
- **Incidence is substantive.** Lossless local payment for all magnitudes ⇔ every closed walk aligned;
  holonomy is computed from the source, not from density statistics.
- **Across scale is substantive.** The damped Möbius source is the orbit $\eta\mapsto C_\eta(1/k)$;
  continuation to smaller damping is backward evolution with no stability estimate in $c_0$ or $\ell^2$.
  Every continuation estimate must use the source vector.

---

## 3. Objects and language

| Object | Meaning | Lean |
|---|---|---|
| Signed incidence form | symmetric $c$, energy $\sum c_{ij}f_if_j$ | `incidenceEnergy` |
| Local allocation | shares $a_{ij}\ge0$, $c_{ij}^2\le a_{ij}a_{ji}$, $\sum_{j\ne i}a_{ij}\le c_{ii}$ | `PairAllocation`, `LocallyPayable` |
| Aligned / balanced | overlaps $\le0$ / some switching aligns | `HasNonpositiveOverlaps`, `IsBalanced` |
| Ground-state transform | $E(vg)=\sum v_i(Cv)_ig_i^2-\tfrac12\sum c_{ij}v_iv_j(g_i-g_j)^2$ | `incidenceEnergy_mul_eq` |
| Holonomy | walk product of $-c_{xy}/|c_{xy}|$ | `walkHolonomy`, `HasAlignedCycles` |
| Comparison form | same budgets, overlaps $-|c_{ij}|$ | `comparisonCoupling` |
| Path certificate, harmonic frame | supersolution + aligned walks + packing; Kron reduction | `PathCertificate`, `HarmonicFrame` |
| Folds; prime / Weil kernels | even/odd folds of translation ledgers; $K(u)=2e^{-u/2}/(1-e^{-2u})-4\cosh(u/2)$ | `evenFold`, `oddFold`, `primeKernel`, `weilKernel` |
| Trains | chain, sine gauge, amplitude trains, Cartesian products | `chainCoupling`, `amplitudeTrain`, `cartesianCoupling` |
| Polar form / defect | $E_c(f)-(\sum g_if_i)^2$; $\|v\|^2-\sum\langle g_j,v\rangle^2$ | `polarForm`, `polarDefectForm` |
| Damping chain, residue modes | BVI's $C_\eta$ on $c_0$, source $r=1/k$; $v_d$ with eigenvalue $d^{-\eta}$ | `arithmeticDampingCenteredOperator`, `normalizedResidueMode` |
| Signed energy, compact negativity | $\langle Tu,u\rangle$; $Q\ge-(\text{finite rank})-\varepsilon\|\cdot\|^2$ | `signedEnergy`, `CompactlyNegative` |
| Radial loss | $-2\langle u,u'\rangle/(1+\|u\|^2)$ | `radialLoss` |
| Companion form | $\sum p(\gamma_i)^2-wp'(t)^2$ | `companionForm` |

**Words.** *Pay locally*: each overlap paid by two shares, no point lends beyond its budget.
*Frustrated*: no switching aligns the cycle. *Supersolution*: $v>0$, $Cv\ge0$. *Polar charge*: square of
one functional (the pole's shape in every face). *Receiver norm*: $\ell^2$ on the chain coordinate.
*Adverse sequence*: unit profiles with energy → negative limit; *escape*: weak limit with nonnegative energy.

---

## 4. Mechanisms

### Local payment, balance, frustration
1. **Local payment ⇒ positivity**; switching transports both. Ground-state transform: dominance under a
   positive gauge is a local allocation; for aligned forms = positive supersolution.
2. **Balanced ⇒ positivity = local payability.** Holonomy decides balance (Harary). Rank-one charges cannot
   be localized on $\ge3$ points.
3. **Signed local–global principle.** Lossless for every realization ⇔ all cycles aligned; constructive
   converse witnesses. Frustrated $k$-cycle: capacity $2\cos(\pi/k)$, unpayable window
   $\tfrac12<t\le1/(2\cos(\pi/k))$.
4. **Local payment = comparison-form positivity**; exact cost = ground-energy gap; unpayable ⇔ a nonnegative
   overload profile.
5. **Canonical-path payment.** Signed supersolution + aligned walks + path budgets + packing ⇒ nonnegative;
   shared hubs inflate their gauge.
6. **Kron reduction.** Positivity decided on terminals; through an aligned coercive interior Kron never
   creates frustration; healed terminal pairs ⇒ positivity = local payment; Rayleigh monotonicity.

### The prime and Weil ledgers
7. **Odd folding is the source of frustration.** Translation ledgers and even folds are aligned; an odd
   folded overlap is anti-aligned iff $w(p_x+p_y)>w(p_x-p_y)$.
8. **Odd Weil ledger is frustrated only by primes.** $K$ is nonincreasing, so anti-aligned odd overlaps
   need $e^{p_x+p_y}$ a prime power. The prime triangle (sums $\log2,\log3,\log5$) is unconditionally
   frustrated at the source-faithful calibration, yet paid along one canonical path.

### Chains and trains
9. **Chains are balanced**: positive ⇔ lending ledger.
10. **Train capacity** $\cos(\pi/(n+2))$, attained by sine; first-lag law $|A(L)|\le\cos(\pi/(M+2))A(0)$.
11. **Towers add on boxes, not elsewhere.** Cartesian products split energy; strict saving ⇔ support misses
    a box point (simplex $j+k\le n$, slanted supports $j\log p+k\log q\le X$).

### Poles and completion
12. **Polar defect law**: $\|v\|^2-\sum\langle g_j,v\rangle^2\ge0$ ⇔ polar synthesis is a contraction.
13. **Completion keeps the sign iff it keeps the polar functional continuous.**
14. **Polar solution**: aligned + nonnegative polar weights ⇒ $Q(|f|)\le Q(f)$; coercive ⇒ $Q\ge0\iff\sum g_iv_i\le1$.

### The damping chain in the receiver norm
15. **Receiver = chain orbit of the reciprocal.** $(C_\eta r)(n)=P_\eta(n+1)/(n+1)$; admission ⇔ orbit in
    $\ell^2$ ⇔ first column in $\ell^2$; RH ⇔ orbit in $\ell^2$ at arbitrarily small times.
16. **Residue modes are Bessel, not Riesz**: $\|\sum c_dv_d\|^2\le48\sum c_d^2$, no lower frame bound.
17. **Sign-blind threshold ½**; positive twin is the extremal sign pattern.
18. **Backward ill-posed; unbounded generator** $-\log d$.
19. **Hilbert–Schmidt ladder** above 1, $1/\sqrt2$, golden ratio, and **exactly above ½** in Mellin
    coordinates (source transform $-\zeta(-s)/(s\zeta(\eta-s))$); no HS bound at $\eta\le\tfrac12$.
20. **At half damping**: bounded, compact, receiver $\ell^2$-continuous, residue sums converge (Riesz +
    Tauberian). Below ½ the Mellin route needs $1/\zeta$ on $\Re=\eta+\tfrac12$, inside the strip.

### Adverse sequences
21. **Energy splitting** under weak convergence; compact negativity ⇒ adverse limits nonzero; without it
    escape. The restricted Weil form of $\zeta$ is compactly negative at every aperture.

### Signed sampling
22. **Companion law**: on-line companions pay off-line depth iff $w\Lambda(t)\le1$ with enough companions; one
    short only at critical points; two short never.
23. **Paley–Wiener law**: lattice companions pay all aperture-$A$ sources iff density $\ge A/\pi$
    (Nyquist), sharp price $A^3h/(3\pi)$; finite configurations ⇔ derivative-kernel Gram $\le2\pi/h$.

### Continuation
24. **Radial loss law**: tangential motion is free; $|L|\le\|u'\|$ is the orientation-blind majorant.

---

## 5. Pillar theorems

1. **Signed local–global principle** (`nonneg_iff_locallyPayable_of_isBalanced`,
   `localPayment_lossless_iff_alignedCycles`, `frustratedCycle_nonneg_iff`, `nonneg_iff_payable_of_healed`).
2. **Prime origin of frustration** (`frustrated_walk_has_primeSum`,
   `oddFold_primeTriangle_weilLedgerKernel_one_not_isBalanced`).
3. **Polar defect law** (`polarDefect_nonneg_iff`, `exists_polarDefect_lt_of_unbounded`).
4. **Receiver as semigroup orbit; threshold ½** (`admits_iff_summable_orbit`, `riemannHypothesis_iff_firstColumn_summable`,
   `not_backward_stable_l2`, `signBlind_admission_iff`, `exists_centeredOperator_l2_le_half`).
5. **Train capacities** (`autoCorr_amplitudeTrain_first_le`, `joint_capacity_lt_iff_not_box`).
6. **Profile compactness** (`ccmRestrictedWeilForm_adverse_weakLimit`).
7. **Signed sampling** (`companions_pay_iff`, `pwCompanions_pay`).

---

## 6. Traps

| Trap | Truth |
|---|---|
| Each atom paid by its own strip ⇒ form paid | Only if shares are drawn once; overlapping strips frustrate |
| Positivity ⇒ positive gauge | Only for balanced forms |
| Pole as a local charge | Rank one on ≥3 points never local; pay it by a global dual norm |
| Resonant unit train is extremal | Sine train is, strictly from $M=2$ |
| Cross-prime cancellation on aligned trains | Capacities add exactly on boxes |
| Pronic weight is the receiver | Receiver is $\ell^2$ on the chain coordinate |
| Compactness of the chain gives continuation | Backward problem ill-posed |
| Dense residue modes give a stable expansion | Bessel not Riesz |
| HS/bounded at ½ ⇒ progress below ½ | Needs $1/\zeta$ inside the strip; cofinal boundedness is RH |
| Column bounds = operator bound | Operator bound needs mixed Gram terms |
| Adverse sequence has adverse limit | Only under compact negativity |
| Finite duality is a cofinal certificate | No uniformity in the number of points |
| Kron/path certificate as a structure field | Premises must be proved on the actual coupling |

---

## 7. Open problems

1. **Arithmetic holonomy at a fixed mesh**: holonomies and frustrated budgets of AIP's ledger where $K$
   and prime atoms are comparable.
2. **Allocation at growing size**: payment or frustration bounds uniform in the number of strips.
3. **Nonlocal payment of the actual ledger**: effective conductances between prime-sum terminals;
   horizon-uniform path budgets and packing for an actual coupling.
4. **Chain on $\ell^2$ below half damping** (needs $1/\zeta$ on $\Re=\eta+\tfrac12$); cofinal = RH.
5. **Square-root cancellation against the residue Gram** below ½.
6. **Companion geometry of on-line zeros**: non-lattice companion sets; $k+1$ companions within $r\ll1/A$
   at every height from the actual zero divisor.
7. **Compact negativity uniform in aperture.**
8. **Cross-prime saving off the box**: size and dependence on $\log q/\log p$.

## 8. Tools to build

Allocation for a growing arithmetic family with uniform loss; horizon-uniform $\|C_ar\|_{\ell^2}$;
aperture-uniform compact negativity; $\ell^2$ chain bounds below ½; a companion law from the actual
on-line zeros; an arithmetic diagnostic identified with a holonomy computed from the source.

## 9. Principles

A contribution carries the full passport (source, domain, norm, observation, signed ledger, parameter
range, limit order); keeps the ledger signed except where separation is proved lossless; comes with
sharpness (extremal, converse or counterexample); names its arithmetic instance or counts as
infrastructure. Strips/trains are AIP's, chain/modes BVI's, continuation ACCE's. Name the norm ($c_0$,
pronic, $\ell^2$); keep the pole global; read the source ($1/k$, $\mu(d)$), not the operator; finite before cofinal.
