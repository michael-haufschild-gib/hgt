# Arithmetic Compensation Theory (ACompT)

Namespace `GaloisForLFunctions.ArithmeticCompensationTheory`; umbrella
`ArithmeticCompensationTheory.lean`; 30 modules.

## 1. Motivation

Several exact descriptions of one arithmetic source can each diverge while their sum stays smaller.
ACompT asks what cancellation between descriptions of the **same** source (prime atoms vs polar
density, large-prime sector vs complement, two cutoffs, two origins, a receiver and its corrector)
forces that no single description forces, and prices every such cancellation as a rate. Relative
cancellation is the starting point; admission (a horizon-free absolute bound) is the target.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Prime comb | `combWeight`, `combPrimes`, `combMass` | $w_p=\sqrt p\log p/(p-1)$, $p\le e^{2r}$, $S_r=\sum w_p$ |
| Comb energies | `combEnergy`, `combCross`, `combDiagonal`, `combCharge` | $\sum w_pw_qA_F(\log q-\log p)$; off-diagonal; $\sum w_p^2$; $\sum w_pA_F(\log p)$ |
| Slowly varying / concentrated tests | `rescaledTest`, `concentratedTest`, `oddBump`, `unitOddBump` | $r^{-1/2}f(x/r)$; $\sqrt\lambda\varphi(\lambda x)$ |
| Depth, horizon law | `combDepth`, `combTail`, `horizonDensity`, `horizonIntegral` | $u_p=2r-\log p$; $D_r(u)=S_{r-u/2}/S_r$; $\tfrac12e^{-u/2}du$ |
| Horizon energy | `horizonEnergy`, `horizonAutoCorr`, `crossCorr` | $J(F)=\iint A_F(u-v)\,d\mu\,d\mu=\int_{u>0}A_F\,d\mu$ |
| Prime–polar residual | `chebyshevTwoPoleDefect`, `primePolarCutoffSymbol` | $E(s)=e^s+s-1-\psi(e^s)$ |
| Full ledger | `archimedeanLedgerBudget`, `reflectedPrimePolarCost`, `SobolevGradedIncidenceAllocation` | `fullZeroForm` = budget − cost |
| Test cones | `BoundedDirichletCone`, `SubEnvelopeDirichletCone`, `OddApertureRegularityClass` | $\int F'^2\le\Lambda^2\int F^2$ etc. |
| Curve model | `curvePointCount`, `curveComb`, `curveCombEnergy`, `curveHorizonEnergy` | $N(n)=q^n+1-\Re\sum\alpha_i^n$ |
| Curve receiver | `curveZ`, `curveDampedZinv`, `curveCentredPrefix`, `curveReceiverEnergy`, `ZeroChainCondition` | power-series model of the damped centred source |
| Compensation coordinates | `compensationAmplitude`, `transverseRemainder`, `gramAmplitude`, `gramTransverse`, `compensationDefect` | $\alpha=-\langle L,C\rangle/\|L\|^2$, $R=C+\alpha L$ |
| Two-scale data | `twoScaleCompleteShiftEnergy`, `pmConnectionEnergy`, `pmTransverseTransitionEnergy` | cutoff $P^2$ vs $Q^2$ |
| Pronic norm, origin | `pronicEnergy`, `pronicShellEnergy`, `quarterPower` | $\sum a(n)^2/(n(n+1))$ |
| Blow-up profile | `normalizedReceiverProfile`, `properUnitDilation`, `normalizedTangentProfile`, `cofactorAliasingWave` | $u_{\varepsilon,T}=A_\varepsilon/\sqrt{E_T}$ |
| Budgets | `PositivePartContinuation`, `AdaptedEnergy`, `lacunaryEnergy` | continuation demands |
| Corrector | `bezoutUnitCorrector`, `bezoutCorrectedEnergy`, `compositeCorrectedEnergy`, `bezoutCorrectedRelativeLoss` | $C_T=\sum(1-2A_\varepsilon)/(n(n+1))$ |
| Aperture ceiling | `apertureCeilingExponent` | $\tfrac{11}2A-\pi e^{2(A-2)}$ |
| Prime blocks | `flatWindowRow`, `omittedClassWeight`, `omittedClassCorrector`, `packetOmittedCorrector`, `kloostermanPacket` | centred block and its sieve correctors |

## 3. Language

- **Coherent subtraction**: remove the part of one description that matches another before any absolute value.
- **Horizon**: the top scale $e^{2r}$ (comb) or $T$ (receiver); **depth** = distance below it.
- **Admitted**: horizon-free bound on the pronic energy; **blow-up**: energy $\to\infty$.
- **dVP rate**: error $\exp(-c\sqrt r)$ from PNT with de la Vallée Poussin; a power saving would be a zero-free strip.
- **Four qualifiers** of any "bounded correction": norm, uniformity in cutoff, source class, damping/aperture dependence.

## 4. Mechanisms

**A. The prime comb (integers).**
1. $S_r\sim2e^r$; primes below $e^{(2-\delta)r}$ carry vanishing mass; rescaled shifts concentrate at the horizon.
2. Universal $E_r(F)\le S_r^2A_F(0)$, attained asymptotically on slowly varying tests: $E_r\sim4e^{2r}A_f(0)$; diagonal $O(r^3)$, so the cross aggregate is also $\sim4e^{2r}$.
3. Normalized comb is a **translation** $f(\cdot+2)$ in $L^2$; first-power charge $=o(S_r)$ for $f$ in $[-1,1]$: Cauchy–Schwarz discards exactly the translation geometry.
4. Depth law $D_r(u)\to e^{-u/2}$ uniformly; **resolvent law** $E_r(F)/S_r^2\to J(F)$ for every continuous compact $F$: the comb acts as $S_r\cdot\tau_{\text{horizon}}\circ(1+2\partial)^{-1}$. $0<J(F)\le A_F(0)$ for $F\ne0$; probe bound $G(v)^2\le A_F(0)J(F)$.
5. All of it at the dVP rate with universal constants: $|S_r-2e^r|\le Ke^{r-c\sqrt r}$; $|E_r/S_r^2-J|\le K(\Lambda\|F\|_1+A_F(0))e^{-c\sqrt r}$.
6. $J(F)=\int_{u>0}A_F\,d\mu$; $A(0)-A(s)=\tfrac12\int(F-F(\cdot+s))^2$; horizon moments $2^kk!$. Translation deficit is exactly inverse-square: $r^2(A_f(0)-E_r/S_r^2)\to4\|f'\|^2$.
7. **Resolvent energy identity** $J(F)+4J(F')=A_F(0)$ on $C^1_c$; hence $\int F^2-4\int F'^2\le J\le\int F^2$ and $J=A_F(0)-4A_{F'}(0)+16J(F'')$; second correction exactly $-16\|f''\|^2/r^4$, no $r^{-3}$ term; prime error reaches neither.
8. Coercivity: $J(G)\le(1-e^{-R})\int G^2$ for support $[-R,R]$; on odd tests with $\int F'^2\le\Lambda^2\int F^2$, $J\ge(1-4\Lambda^2)\int F^2$, constant 4 optimal. Without derivative control (even at fixed aperture, odd, smooth) $\inf J/\int F^2=0$: narrow bumps defeat the integer comb.

**B. The prime–polar ledger.**
9. Prime atoms and polar density cancel before squaring: $\sum\Lambda(n)h(\log n)-\int(e^s+1)h=\int E(s)h'(s)$; $|E(s)|e^{-\theta s}\le Ke^{(1-\theta)S-c\sqrt S}$; the saving over $e^{S/2}$ is exactly PNT's.
10. Literal cutoff symbol: linear frequency loss uniformly, frequency-free bound $17e^{S/2}$ from positivity of each measure.
11. Full ledger `fullZeroForm` = archimedean budget ($\ge-\tfrac{27}5\int F^2$) − compensated cost; cost = Chebyshev-defect integral (first order) = critical-scale-prefix integral (second order). Unconditional floor $\ge-Ke^{r-c\sqrt r}(\tfrac14\int F^2+\int F'^2)$, pure $L^2$ on the sub-envelope cone.
12. Width ladder: $\sigma>$ width ⇒ cost $\le K_\sigma e^{2\sigma r}(\tfrac14\int F^2+\int F'^2)$; converse via difference-lag tests (uniformly in a bounded Dirichlet cone). Exponent of the cost **is** the width.

**C. Curve models (calibration; eigenvalue bound is a model hypothesis).**
13. Curve comb: geometric horizon law $q^{-k/2}$ with error $O(gDq^{-D/2})$, growing like $\lambda^D$ off the Weil circle; shift by bounded $\tau_{\log q}$ inverted by geometric weights ⇒ **uniformly coercive** $\|C_DF\|^2\ge(q^D/12)\int F^2$; discrete resolvent law, $J_q\ge((1-q^{-1/2})^2/12)\int F^2$.
14. Curve receiver: centring removes the pole at $u=1/q$ exactly; admitted above zero width ($\lambda<q^\varepsilon$), refuted below. Annihilator filter of degree $m+2$ isolates each Frobenius mode at degrees $\ge2m+2$: oscillating modes cannot cancel. Exact law: admitted at $\varepsilon$ ⇔ **zero-chain condition** $\mathrm{mult}(a)\le\mathrm{mult}(q^{-\varepsilon}a)+[a=q]$ for $|a|\ge\sqrt q\,q^\varepsilon$ (curve form of "admitted damping translates zeros"). Isolated admitted dampings may sit below the width (chain pairs); accumulating ones read it; cofinal admission ⇔ Weil bound.

**D. Compensation coordinates on the actual source.**
15. Pythagorean law $\|L+C\|^2=(1-\alpha)^2\|L\|^2+\|R\|^2$: coordinates carry no information beyond the complete energy.
16. Large-prime sector of the damped Möbius–Ramanujan expansion: $\alpha_P\to1$, defect $\le K_m/\log^mP$ for every $m$ (from all log-powers of Möbius harmonic savings); absolute energy still $O(P^{1-2\varepsilon}/\log^mP)$, growing. Amplitude has bounded (polynomially weighted) dyadic variation.
17. Two cutoffs share the cutoff-independent divisor remainder: $S_Q-S_P$ cancels it exactly and saves a **power**, $O(P^{1-3\varepsilon})$; relative $O(P^{-\varepsilon}\log^2P)$; absolute $\to0$ for $\varepsilon>\tfrac13$. Moving-projection connection identity splits $R_Q-R_P$ into shift, sector step, and $(\alpha_Q-\alpha_P)L_P$.

**E. Receiver blow-up, origins, budgets.**
18. Trivial growth $E_N\le D(1+N^{1-2\varepsilon})$ ⇒ admitted or **blow-up escapes to the horizon** (scales below $E_T^{\theta/(1-2\varepsilon)}$ carry $o(1)$). Normalized profile: unit energy, deep cofactors vanish, exact normalized inversion law $u+D^{\ge2}u=\rho_\varepsilon/\sqrt{E_T}\in[0,n/\sqrt{E_T}]$ (homogeneous in the limit), self-improving identity, Möbius-factored tangent. Escape families embed: drifted $n^{1/4}$, sign-blind majorant (violates the inversion sign), oscillating probes with exact spectral shares.
19. Origin shift by $k$ costs exactly $(k+1)(k+2)/2$ (attained); admission invariant under finite shifts; a drifting origin is priced by the tail; uniform drift tolerance ⇔ bounded drift ($n^{1/4}$ defeats every unbounded drift).
20. Signed budget strictly weaker than positive part (lacunary family); first-cell work $W_1\to-\tfrac12$; core debt on $[\eta,\varepsilon]$, $\eta>0$, converges to $\log\zeta(1+\eta)-\log\zeta(1+\varepsilon)$.
21. Gaussian ceiling forces any positive aperture floor to decay doubly exponentially; no positive floor along unbounded apertures; half-summable and harmonic transports impossible.
22. Adapted energy ⇔ admission (with admitted right end). Bézout corrector completes the square to $1+$ dual residual, is $(1/3,3)$-comparable unconditionally, removes the adverse first cell, has bounded derivative; composite correctors within $\theta$ cost $\log\frac{1+\theta}{1-\theta}$; families on $(a_0,c]$ give $\Theta\le\tfrac12+a_0$.

**F. Prime blocks (transfers).**
23. Guth–Maynard $17/30$ made uniform in window length by tiling; centred prime row estimate on $P^{1+\delta}\le Q\le P^{30/17-\delta}$.
24. Centring $\Lambda$ by 1 kills block mass but keeps 100% of the omitted-residue-class term $-\pi^2(p^2-1)^2/(144p^2(p-1))$; the omitted-class corrector cancels it; short-window average controls block mass by Cauchy–Schwarz; balanced regime $P\le Q\le BP$ gets unconditional $o(1)$ savings over the large sieve.
25. Kloosterman packets: dual Parseval (linear = Kloosterman energy); Montgomery–Vaughan two-sided quasi-isometry on every window; $p^4$-order non-cancellation floor; CRT lets one packet corrector cancel the omitted-class bias at all $p\in S$ simultaneously.

## 5. Pillar theorems

| Theorem | Content |
|---|---|
| `exists_odd_smooth_family_sharp_comb_rate`, `tendsto_testPairing_normalizedComb_sub_translate` | comb rate $4e^{2r}$; translation |
| `tendsto_combEnergy_div_combMass_sq_horizonEnergy`, `exists_abs_combEnergy_sub_le` | resolvent law, dVP rate |
| `horizonEnergy_add_four_mul_horizonEnergy_deriv` | resolvent energy identity |
| `tendsto_pow_four_mul_combEnergy_rescaledTest_second_deficit` | exact second correction |
| `not_exists_horizonEnergy_ge`, `exists_curveCombEnergy_ge` | integer comb not coercive; curve comb is |
| `exists_fullZeroForm_ge_deLaValleePoussin_poleTiltedSobolev` | unconditional ledger floor |
| `curveReceiver_admits_iff`, `weil_iff_cofinal_curveReceiverEnergy` | zero-chain admission law; Weil calibration |
| `norm_add_sq_eq_compensation`, `exists_compensationDefect_le_inv_log_pow` | Pythagorean law; all-log-power rate |
| `exists_twoScaleCompleteShiftEnergy_le_pow_saving` | two-scale power saving |
| `admits_or_escapesToHorizon`, `normalizedReceiverProfile_add_properUnitDilation_eq` | horizon escape; normalized inversion law |
| `forall_admitted_drift_admitted_iff` | drift tolerance = bounded drift |
| `exists_admitted_monotone_not_positivePartContinuation` | signed ≠ positive-part budget |
| `exists_le_floorLoss_of_floor` | forced doubly exponential loss |
| `bezoutCorrectedEnergy_eq_one_add_residual`, `bezoutCorrectedEnergy_comparison` | corrector completion and comparability |
| `tendsto_mul_kernelStatistic_centredPrimeBlock`, `exists_balanced_centredPrimeBlock_rowBilinear_le` | omitted-class law; balanced savings |
| `abs_sum_window_kloostermanPacket_sq_sub_le` | Kloosterman packet quasi-isometry |

## 6. Tools

**Developed.** Comb/horizon calculus (mass, tail, shells, depth statistics, resolvent energy
identity, Sobolev sandwiches, moments); dVP-rate versions with universal constants; prime–polar
compensated identity and ledger decomposition; curve-model power-series algebra (centring tail,
annihilator filters, zero-chain multiset matching, weighted $\ell^2$ energies); compensation
coordinates (abstract and Gram); two-scale connection identities; pronic origin/drift pricing;
normalized blow-up profile calculus; Bézout and composite correctors; omitted-class and packet
correctors; uniform $17/30$ window by tiling; Montgomery–Vaughan Kloosterman packets.

**To build.** A second representation of the prime–polar pairing with exponent $<\tfrac12$; a
corrector below $\tfrac12$ whose loss bound is proved from independently estimated terms; tail decay
of the actual receiver beyond a drifting origin; classification of horizon-shell defect profiles
with arithmetic constraints; a signed prime-shell estimate yielding a graded (negative) aperture floor.

## 7. Open questions

1. Single-scale divisor remainder: a horizon-free bound at one $\varepsilon<\tfrac12$ (current $O(P^{1-2\varepsilon}/\log^mP)$).
2. Which horizon-escaping profiles survive the normalized inversion law and its sign constraint below $\tfrac12$?
3. What compatibility (shared divisor coefficients, overlapping cuts, common origin, source-fixed pole) constrains the same residual differently enough to lower the ledger exponent below $\tfrac12$?
4. Can the two-scale power saving be iterated over dyadic scales without the connection term reintroducing the single-scale growth?
5. Turn the two factorizations of the damping tangent (prime dilation, Möbius dilation) into an inequality on the quadratic deviation of the work.
6. Power saving in balanced-regime block mean squares (equivalent to crossing below half damping).

## 8. Traps

| Trap | Truth |
|---|---|
| Raw comb energy or cross aggregate is polynomial | $\sim4e^{2r}$; universal bound attained |
| Large comb energy means large adverse charge | charge $o(S_r)$ on the extremal family |
| The integer comb is uniformly coercive | narrow bumps defeat it; only curve combs are |
| Relative cancellation = bounded remainder | coordinates sum exactly to the relative complete energy |
| A log saving iterates to admission | absolute energies still grow; dyadic sums diverge |
| Pay every local loss separately | positive-part budget strictly stronger than signed |
| Signed damping work is nonnegative | $W_1\to-\tfrac12$ |
| Fix a positive aperture floor and transport it | impossible; ceiling forces doubly exponential loss |
| Pick a corrector from the desired bound | adapted energy ⇔ admission; content is the construction |
| One admitted damping bounds the width | chain pairs are admitted below the width |
| Finite origin information changes admission | it never does; only a drifting origin |
| Centring removes all prime bias | omitted-residue-class term survives at 100% |
| Fixed-length short windows suffice | uniform-length version needs tiling and monotonicity |
| RH-equivalent restatements (cost exponents, cofinal correctors, cofinal Bézout loss, block power savings) | criteria, not progress |

## 9. Context

| Programme | Relation (verified imports) |
|---|---|
| ArithmeticContinuationAndCriticalEnergy | 11 imports: receiver, admission, averaged budgets, damped Möbius energy, renormalization; 4 ACCE modules import ACompT back |
| BezoutValuationIncidence | 7 imports: centred prime row, omitted-class law, dual norm, Kloosterman Gram, short-window ⇔ quasi-RH; 2 BVI modules import back |
| ArithmeticIncidencePositivity | comb energy reduction, ledger reduction, lag Abel summation, global allocation, translate pairing |
| SquareRootThreshold | incidence ledger graded by width, walls, receiver damping |
| ArithmeticCriticalityTheory | Gaussian ground-energy ceiling |
| RHTower, HTGeometry, TransHorizonIncidenceMechanics | PNT inputs, 17/30 windows, Möbius–Ramanujan cancellation; smooth transitions; probe spectrum |
| Consumers | ArithmeticDefectRigidity (escape, blow-up profile), ArithmeticOrientationTheory (aperture ceiling, horizon escape), ArithmeticIndexDescent (prime–polar cutoff), ScaleSignedIncidenceCriticality, ArithmeticCastelnuovoSeveri, ArithmeticCorrespondencePositivity, BiarithmeticGeometry, ReflectiveDirichletPolynomialS2 |

## 10. Big picture

ACompT shows that the arithmetic sources of the RH programme are full of genuine cancellation —
the comb is a translation, prime atoms cancel the polar density, the large-prime sector cancels its
complement, two cutoffs cancel the divisor remainder, a sieve corrector cancels residue-class bias —
and that every such cancellation, measured honestly, stops exactly at the zero width: the exponent of
the compensated ledger is the width, the curve receiver is admitted exactly on zero chains, and a
power saving in any single-scale residual is a zero-free strip. Cancellation buys log powers and
relative rates unconditionally; it buys powers only between two representations that share the
same hard term. The lesson for the RH proof is that a decisive estimate will not come from making
one description smaller but from a compatibility between two descriptions that constrains the
residual differently, kept signed, kept anchored to the actual source, and paid for every change of
scale, origin and norm. Function fields confirm that the receiver framework is faithful (admission
⇔ Weil); over the integers the missing piece is the coercivity that curves get from a discrete
spectrum and integers do not have.
