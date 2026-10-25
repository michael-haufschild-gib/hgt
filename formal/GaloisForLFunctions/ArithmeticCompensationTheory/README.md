# Arithmetic Compensation Theory (ACCC)

**One question.** When several exact arithmetic descriptions belong to the same source, what
signed critical-norm estimates do their compatibility conditions force that none of the
descriptions forces separately?

ACCC (*arithmetic compatibility and compensated coercivity*) studies cancellation between
descriptions of one source. Separately divergent pieces can cancel to leading order while their sum
still exceeds the critical norm. The task: identify the coherent part, retain its mixed terms, and
estimate the absolute remainder with constants independent of the cutoff. **Relative cancellation
is the starting point, not admission.**

Namespace `GaloisForLFunctions.ArithmeticCompensationTheory`; umbrella
`ArithmeticCompensationTheory.lean`.

---

## 1. Place in the research

Governing example: the actual centred receiver
$A_\varepsilon(n)=\sum_{d\le n}\mu(d)d^{-\varepsilon}\lfloor n/d\rfloor-n/\zeta(1+\varepsilon)$, $E_T(\varepsilon)=\sum_{n\le T}|A_\varepsilon(n)|^2/(n(n+1))$;
admission $\exists B_\varepsilon\forall T$; RH = cofinal admission (`RHTower.riemannHypothesis_iff_cofinal_budget`);
accumulation infimum $\Theta-\tfrac12$.

ACCC is the **compensation layer**: subtract the coherent piece before any absolute value; keep
mixed Gram terms, poles, even parts and boundary terms attached until used; pay every change of norm,
cutoff, gauge, scale or origin with an explicit transfer term. Progress is a **rate** (residual
exponent, log saving, aperture decay, resolution threshold); identities and criteria are structure.

| Programme | Interface |
|---|---|
| [ArithmeticIncidencePositivity](../ArithmeticIncidencePositivity/README.md) | Cross-prime comb aggregate: ACCC proves it is $\sim4e^{2r}$ (AIP's polynomial target fails); comb = translation/resolvent |
| [ArithmeticContinuationAndCriticalEnergy](../ArithmeticContinuationAndCriticalEnergy/README.md) | Owns admission and averaged budgets; ACCC adds positive-part failure, core debt limit, adverse first cell, adapted energies |
| [ArithmeticCriticalityTheory](../ArithmeticCriticalityTheory/README.md) | Gaussian ceiling of $\mu(A)$ read as a forced loss rate |
| [BezoutValuationIncidence](../BezoutValuationIncidence/README.md) | Centred prime row: ACCC widens the range to $Q\le P^{30/17-\delta}$ and the balanced regime |
| [SquareRootThreshold](../SquareRootThreshold/README.md) | Graded floor dictionary used as scoring rule |
| [BiScaleUncertainty](../BiScaleUncertainty/README.md) | Schur residual algebra; selectivity test models |
| [TransHorizonIncidenceMechanics](../TransHorizonIncidenceMechanics/README.md), [ScaleSignedIncidenceCriticality](../ScaleSignedIncidenceCriticality/README.md) | Recovery needs stability; origin loss |
| [ArithmeticDefectRigidity](../ArithmeticDefectRigidity/README.md) | Next step after the blow-up profile: paid power subtraction, antipodal cofactor |
| [ArithmeticOrientationTheory](../ArithmeticOrientationTheory/README.md) | Floors must respect doubly exponential decay; correctors are readings until built from source terms |
| Others (APT, ACS, SAEI) | Weil–Markov–pole target; effectivity; signed incidence kernel |

Feeds AIP, MC, RW, ACT, BVI; supplies no source-derived zero-rate bound. `RHTower` supplies PNT via
Abel summation, the $17/30$ short-window theorem and module `RHTower/PMRamanujanComplementaryCancellation.lean`.

---

## 2. Why

The walls are failures of particular estimates, each a missing **rate**. Two facts make compensation
the right object: (1) the actual source already realizes leading-order cancellation of divergent
pieces — the large-prime sector $L$ and its complement $C$ of the damped Möbius–Ramanujan expansion
have $\|C\|^2/\|L\|^2\to1$, $\langle L,C\rangle/\|L\|^2\to-1$ — yet the remainder can still grow with a power;
(2) a majorant can be exponentially larger than the signed quantity: raw prime-comb energy is $\sim4e^{2r}$
while the first-power charge is $o(e^r)$ — Cauchy–Schwarz discarded the translation geometry that kills
the charge.

---

## 3. Objects and language

**Prime comb** at aperture $r$: $C_rF=\sum_{p\le e^{2r}}w_pF(\cdot+\log p)$, $w_p=\sqrt p\log p/(p-1)$; mass $S_r$,
energy $E_r(F)=\sum w_pw_qA_F(\log q-\log p)$, cross aggregate, diagonal, first-power charge
(`combWeight`, `combMass`, `combEnergy`, `combCross`, `combDiagonal`, `combCharge`). Depth
$u_p=2r-\log p$; comb tail $D_r(u)=S_{r-u/2}/S_r$; **horizon law** density $\frac12e^{-u/2}$; **horizon energy**
$J(F)=\iint A_F(u-v)\frac12e^{-u/2}\frac12e^{-v/2}$ (`horizonEnergy`); slowly varying tests $F_r=r^{-1/2}f(x/r)$.

**Compensation coordinates.** Amplitude $\alpha=-\langle L,C\rangle/\|L\|^2$, transverse remainder $R=C+\alpha L$
(`compensationAmplitude`, `transverseRemainder`; Gram versions `gramAmplitude`, `gramTransverse`).

**Budgets.** Signed averaged (`AveragedContinuation`), positive-part (`PositivePartContinuation`),
pointwise (`LinearContinuation`), adapted energy (`AdaptedEnergy`: comparable to $1+E_T$ with
horizon-free constants and signed log-loss budget).

**Words.** Coherent subtraction; signed pairing; anchored restriction (actual source, not a class);
refinement (scale change with boundary terms); compensated transport; defect extraction.
**Four qualifiers** for any "bounded correction": which norm, uniform in which cutoff, on which
source class, with which damping/aperture dependence.

---

## 4. Mechanisms

### The prime comb
1. **Mass** $S_r\sim2e^r$ (PNT via Abel summation).
2. **Horizon concentration:** primes below $e^{(2-\delta)r}$ carry vanishing mass; rescaled shifts concentrate at 2.
3. **Universal bound** $E_r\le S_r^2A_F(0)$.
4. **Sharp exponential rate:** on slowly varying tests $E_r\sim4e^{2r}A_f(0)$ and the cross aggregate too
   (diagonal $O(r^3)$).
5. **Translation survivor:** $(\sqrt r/S_r)(C_rF_r)(r\cdot)\to f(\cdot+2)$.
6. **No adverse charge:** $S_r^{-1}\sum w_pA_{F_r}(\log p)\to A_f(2)=0$ for $f$ in $[-1,1]$.
7. **Compensated ledger residual.** Prime atoms vs polar density cancel up to $E(s)$ before squaring;
   residuals carry the dlVP saving; $\hat Z=\text{archimedean budget}-\text{reflectedPrimePolarCost}$
   (budget $\ge-\frac{27}5\int F^2$); unconditional floor $-Ke^{r-c\sqrt r}(\frac14\int F^2+\int F'^2)$, pure $L^2$ on the
   sub-envelope Dirichlet cone; **width $\le\sigma_0$ ⇔ cost $\le Ce^{2\sigma r}(\frac14\int F^2+\int F'^2)$ for all $\sigma>\sigma_0$**;
   exponent $<\tfrac12$ ⇔ $\Theta<1$; every positive exponent ⇔ RH.
8. **Depth law** $D_r(u)\to e^{-u/2}$ uniformly; depth statistics → horizon law uniformly over translates.
9. **Comb resolvent law:** $E_r(F)\sim4J(F)e^{2r}$ for every continuous compact $F$, $S_r^{-1}C_r\approx\tau_{2r}\Psi$,
   $\Psi$ = resolvent of $1+2\partial$, $J(F)=\|\Psi F\|^2>0$ (pointwise positive, not uniformly coercive).
10. **dlVP rate:** $|S_r-2e^r|\le Ke^{r-c\sqrt r}$; resolvent law at rate $e^{-c\sqrt r}$ with universal constants.
11. **Resolvent energy identity** $J(F)+4J(F')=A_F(0)$; sandwich $A_F(0)-4\int F'^2\le J\le A_F(0)$; second order
    $J=A_F(0)-4A_{F'}(0)+16J(F'')$; quartic second correction; fixed-aperture coercivity on odd regularity
    classes $1-4(1-e^{-R})\Lambda^2$; without derivative bounds infimum 0.
12. **Coercivity: integers vs curves.** Concentrated tests defeat the integer comb ($J(F_\lambda)=O(1/\lambda)$); a
    curve comb (lattice $\mathbb N\log q$, geometric weights) is uniformly coercive, $J_q\ge((1-q^{-1/2})^2/12)\int F^2$.
13. **Curve models.** Horizon law geometric $q^{-k/2}$ with error the zero-set width; curve receiver
    admitted above the zero width; annihilator filters isolate each Frobenius mode (no cancellation
    across blocks of length $m+3$); **cofinal admission ⇔ Weil bound** (`weil_iff_cofinal_curveReceiverEnergy`).

### Compensation coordinates
14. **Pythagorean law** $\|L+C\|^2=(1-\alpha)^2\|L\|^2+\|R\|^2$, $\langle L,R\rangle=0$.
15. **Actual instance and rate.** Large-prime sector at cutoff $P^2$: $\alpha_P\to1$, $\|R_P\|^2/\|L_P\|^2\to0$, defect
    $O(\log^{-m}P)$ for every $m$; complete energy still $O(P^{1-2\varepsilon}/\log^mP)$ (growing). Dyadic summability;
    moving projection with exact connection identity; **two-scale cutoff shift saves a power**
    $O(P^{1-3\varepsilon})$ (the divisor remainder cancels on the common head).

### Blow-up profiles, origins
16. **Blow-up escapes to the horizon.** Trivial growth $E_N\le D(1+N^{1-2\varepsilon})$ ⇒ admitted, or energy below
    $E_T^{\theta/(1-2\varepsilon)}$ is a vanishing fraction. Normalized profile $u=A_\varepsilon/\sqrt{E_T}$: unit pronic energy,
    horizon-shell concentration, two-sided dilation sandwich, normalized inversion law, self-improving
    identity, Möbius-factored tangent; drifted, majorant, aliasing and oscillating-probe profiles embed.
    (ArithmeticDefectRigidity continues: power subtraction ⇒ antipodal renormalized cofactor.)
17. **Change of origin** by $k$ costs exactly $(k+1)(k+2)/2$; admission invariant; a **drifting** origin is
    priced by the tail beyond it; uniform drift tolerance iff bounded drift.

### Budgets and floors
18. **Signed budget strictly weaker than positive part** (lacunary $\sum2^{-k}(2+\sin16^k\varepsilon)$).
19. **Core debt on positive intervals** $=\log\zeta(1+\eta)-\log\zeta(1+\varepsilon)$; first cell has adverse work $W_1\to-\tfrac12$.
20. **Aperture floors decay doubly exponentially:** $B(A)\ge\pi e^{2(A-2)}-\frac{11}2A+\log(m_0/K)$; half-summable and
    harmonic transports impossible.
21. **Adapted energy = admission** (`adaptedEnergy_iff_admits`); **Bézout unit-boundary corrector**
    $\sum(1-2A_\varepsilon)/(n(n+1))$ completes the square to $1+$ dual residual, is $(1/3,3)$-comparable
    unconditionally, removes the adverse first cell, has bounded derivative; composite correctors
    within $\theta$ keep comparability and change log loss by $\le\log\frac{1+\theta}{1-\theta}$; boundary families give
    strips; cofinal bounds ⇔ RH.

### Internal transfer
22. **Huxley window at the Guth–Maynard exponent**: uniform $|\psi(x+h)-\psi(x)-h|\le\varepsilon h$ for $x^\alpha\le h\le x/2$,
    $\alpha>17/30$ (tiling).
23. **Centred prime row** on $P^{1+\delta}\le Q\le P^{30/17-\delta}$ and the balanced regime $P\le Q\le BP$; centring keeps
    100% of the omitted-residue-class term, cancelled by `omittedClassCorrector`; a power saving in the
    short-window mean square ⇔ crossing below half damping.

---

## 5. Pillar theorems

1. Comb is a translation (`exists_odd_smooth_family_sharp_comb_rate`).
2. Comb resolvent law (`tendsto_combEnergy_div_combMass_sq_horizonEnergy`, `horizonEnergy_pos`,
   `exists_abs_combEnergy_div_sub_horizonEnergy_le`, `horizonEnergy_add_four_mul_horizonEnergy_deriv`).
3. Pythagorean law and actual rate (`norm_add_sq_eq_compensation`, `pmCompleteHeadEnergy_eq_compensation`,
   `exists_compensationDefect_le_inv_log_pow`, `exists_twoScaleCompleteShiftEnergy_le_pow_saving`).
4. Compensated ledger graded by width (`exists_abs_primeShift_sub_polar_le`,
   `exists_fullZeroForm_ge_deLaValleePoussin_poleTiltedSobolev`,
   `zetaZeroWidth_le_iff_forall_gt_reflectedPrimePolarCost_le_poleTiltedSobolev`,
   `riemannHypothesis_iff_forall_pos_reflectedPrimePolarCost_le_poleTiltedSobolev`).
5. Signed recovery strictly weaker than positive part (`exists_admitted_monotone_not_positivePartContinuation`).
6. Core debt and first cell (`tendsto_integral_workCore_logZeta`, `tendsto_signedDampingWork_one`).
7. Forced aperture loss (`not_relative_step_transport`, `exists_le_floorLoss_of_floor`).
8. Correctors (`adaptedEnergy_dampedMobiusEnergy_iff_admits`, `bezoutCorrectedEnergy_comparison`,
   `riemannHypothesis_iff_cofinal_bezoutCorrected_loss`).
9. Function-field calibration (`curveCombEnergy_ge`, `weil_iff_cofinal_curveReceiverEnergy`).
10. Origins and blow-ups (`pronicEnergy_shift_le`, `forall_admitted_drift_admitted_iff`,
    `admits_or_escapesToHorizon`, `pronicEnergy_rowDilate_sandwich`).
11. Balanced regime (`exists_abs_rowBilinear_centredPrimeRow_le_of_range`,
    `exists_balanced_centredPrimeBlock_rowBilinear_le`, `primePowerWindowSaving_iff_receiverDampingRate_lt_half`).

---

## 6. Traps

| Trap | Truth |
|---|---|
| Raw comb energy / aggregate is polynomial | $\sim4e^{2r}$; universal bound attained |
| Large comb energy = large adverse charge | Charge is $o(S_r)$ on the extremal family |
| Comb is rank one | Translation (slow tests) / resolvent (fixed tests) |
| Relative cancellation = bounded remainder | Coordinates add exactly to the relative complete energy |
| Pay every local loss separately | Positive-part budget is strictly stronger |
| Nonnegative signed work | $W_1\to-\tfrac12$ |
| Core divergence on positive intervals | Converges to a zeta-log ratio there |
| Transport a fixed positive aperture floor | Impossible; target a graded negative floor |
| Choose a corrector from the desired bound | Circular; the content is the construction |
| Fixed-length short windows = uniform ones | Needs tiling and $\psi$ monotonicity |
| $30/17$ range covers balanced scales | Needs the short-window mean-square transfer |
| Subtract a smooth prime main term and call the remainder estimated | The remainder is the zero-width problem relocated |
| Integer comb is uniformly coercive | Narrow bumps defeat it; curves differ |

---

## 7. Open problems

1. **Single-scale divisor remainder below ½**: horizon-free bound at one fixed $\varepsilon<\tfrac12$ (admission in
   compensation coordinates); current $O(P^{1-2\varepsilon}/\log^mP)$.
2. **Horizon-shell defect profiles**: exclude oscillating profiles below ½, or classify survivors of the
   paid power subtraction and moving-horizon signed pairing (ArithmeticDefectRigidity).
3. **Ledger exponent $<\tfrac12$** (= $\Theta<1$): which second representation of the prime–polar pairing supplies it;
   pure $L^2$ beyond the sub-envelope cone.
4. **Tail decay** of the actual receiver beyond the origin (drift tolerance).
5. **A corrector below ½**: horizon-free bound on integrated Bézout-corrected loss on some $[a,c]$, $a<\tfrac12$,
   from independently estimated terms.
6. **Graded aperture floor** at one $\sigma<\tfrac12$ via the isolated signed prime-shell contribution (ACCE).
7. **Power saving in the balanced regime** (= crossing below half damping).
8. **Two decompositions of one tangent** (prime-dilation vs Möbius-dilation): turn their compatibility
   into an inequality on the quadratic deviation term of the work.

What compatibility must contribute: a second representation constraining the same residual
differently (shared divisor coefficients, overlapping cuts, common successor boundary, source-fixed
pole), surviving the change of representation including projection motion. Keep relative vs
absolute, energy vs signed charge, criterion vs arithmetic producer distinct.

---

## 8. Tools

Horizon concentration and horizon law (qualitative and at dlVP rate); comb resolvent law and
resolvent identity; compensated prime–polar and full-ledger residuals; curve-model combs and
receivers (annihilator filters, coefficient calculus); compensation coordinates and two-scale
transition calculus; budget hierarchy and lacunary countermodel; adapted energies and Bézout
correctors; aperture loss-rate calculus; origin calculus; source growth bounds and normalized
blow-up profiles; length-uniform short windows, block-mass elimination, omitted-class corrector.
Compatibility identities used as constraints (owned by ACCE/BVI): tangent law, prime-dilation form,
inversion law, $D^fD^g=D^{f*g}$, Möbius-dilation form of the tangent.

---

## 9. Success criteria and principles

Degrees of success: a two-scale rate on the actual source with transfer terms; a corrector on one
interval; a classified defect family; the endpoint (cofinal admission = RH). Every contribution:
unconditional on the anchored source; keeps mixed terms, poles, even parts, boundary terms; pays
every representation change; states uniformity; comes with stability if it recovers; reports a
rate; keeps failure constructive; hides no analytic input in an interface. Search the corpus first —
comb, pairing calculus, receiver and dictionaries exist.
