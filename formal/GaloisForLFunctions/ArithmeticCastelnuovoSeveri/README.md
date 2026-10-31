# Arithmetic Castelnuovo–Severi Theory (ACS)

Namespace `GaloisForLFunctions.ArithmeticCastelnuovoSeveri` (sub-namespaces `LogCells`,
`MeanZeroIntervals`, `IntervalVariance`, `SeparatedSections`, `HigherInertia`, `SineKernel`,
`MomentDepth`); umbrella `ArithmeticCastelnuovoSeveri.lean`; 218 modules.

## 1. Motivation

Weil proved RH for curves over $\mathbb F_q$ by reading $\zeta_C$ as intersection theory on $C\times C$:
the explicit formula is the Castelnuovo–Severi (CS) defect, its positivity is the Hodge index
theorem, and Hodge index comes from Riemann–Roch (RR) on all divisors. ACS builds the same
intersection theory for $\mathbb Z$ (the **scaling surface**), calibrates every statement over
$\mathbb F_q$ (curves, fake curves), and asks which of Weil's ingredients exist for $\mathbb Z$, which are
provably absent, and what a missing one would have to produce. Every theorem is unconditional unless
marked; many end in an exact equivalence with RH (traps, §8).

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Polar surface | `PolarSurface`, `polar`, `defect`, `prim`, `polarPart` | symmetric pairing, isotropic $H,V$, $H\cdot V=1$; $\delta=\text{polar}-\text{pair}$ |
| Hodge index, CS | `HodgeIndex`, `CastelnuovoSeveri`, `AmpleHodgeIndex` | $\delta\ge0$ ⇔ $x^2\le2(x\cdot H)(x\cdot V)$ |
| Weil classes | `WeilRealizable` | $\Gamma\cdot H=1,\Gamma\cdot V=q,\Delta^2=2-2g,\Gamma\cdot\Delta=N,\Gamma^2=s$ |
| Curve datum | `CurveDatum`, `pointCount`, `graphPair`, `spanDefect`, `spanGram` | normalized eigenvalues $\beta=\alpha/\sqrt q$; span defect = Toeplitz form in power sums |
| Fake curves | `goldenDatum`, `hidingDatum`, `pureDatum` | golden: $q=5$, $\beta=\varphi^{\pm1}$, integral $N_j=5^j+1-L_j$, defect 1 |
| Scaling surface of $\mathbb Z$ | `scalingSurface`, `ScalingCycle`, `poleB`, `poleA`, `localPair`, `weilPair` | cycles $aH+bV+f$; $f\cdot H=\int fe^{-u/2}$, $f\cdot V=\int fe^{u/2}$; defect = Weil form |
| Zero configurations | `ZeroConfig`, `TemperedConfig`, `rightZeros`, `zeroGram`, `zeroCoord`, `zeroMap` | $W_Z(f,g)=\sum m_\rho h_f(\gamma_\rho)\overline{h_g(\bar\gamma_\rho)}$ as Krein form on $\ell^2(Z)$ |
| Hodge defect | `hermNegIndex`, `hodgeDefectAt`, `sectorHodgeDefectAt` | negative squares of $W$; filtered by aperture (degree) and parity |
| Hecke/Adams action | `translate`, `scalingAction`, `adamsOp`, `heckeCorrespondence`, `heckeCycle`, `arithLefschetz` | $T_a$ = shift by $\log a$; exact isometries of the surface |
| Hecke incidence | `heckeIncidence`, `towerWeight`, `eulerEnvelope`, `collarWeight` | prime part of $\Gamma_a\cdot\Gamma_b$; $\tau_p(k)=\log p\,p^{-k/2}$, $E_p=2\log p/(\sqrt p-1)$ |
| Prime towers | `frobEig`, `towerVec`, `towerGram`, `towerMoment`, `frobWeight`, `outerEig`, `visibleSet` | $\beta_\tau=p^{\tau-1/2}$; Toeplitz Gram of Lefschetz sequence $c_m=W(T_{p^m}g,g)$ |
| Folded spectrum | `activeFoldedSpectrum`, `foldedSpectrum`, `AccessibleOff`, `NullAccessibleOff` | reciprocal eigenvalues of active zeros; wall geometry |
| Effectivity axioms | `RiemannRochAxiom`, `AmpleAxiom`, `BezoutAxiom`, `SurfaceRiemannRochAxiom` | Weil's three properties of effective divisors |
| Cones | `positiveCone`, `openPositiveCone`, `nefQuadrant`, `ampleHalfSpace`, `posTestCone` | form-defined and naive cones |
| Source cones | `sourceCone`, `gradedSourceCone`, `l2SourceCone`, `sobolevSourceCone`, `exactArithmeticSourceCone`, `arithmeticMajorantSourceCone`, `globalArithmeticMajorantCone`, `lefschetzEnvelopeCone`, `rosatiSourceCone` | effectivity defined by a reserve $\Phi$ (section count) |
| Arithmetic sections | `arithmeticSection`, `sinhNeutralArithmeticSections`, `sectionSum` | independent profiles at $\log n$ or separated centres |
| Log cells | `rawCell`, `cellAtom`, `cellSection`, `logCellWidth`, `logStep`, `finiteCellWeil`, `roughWeil` | $[\log a,\log(a+1))$; finite arithmetic Weil forms |
| Haar (balanced) cells | `haarProfile`, `haarMass`, `haarSectionProfile`, `coarseProfile`, `completePairProfile` | mean-zero jump-one pair profile; average + detail |
| Gamma kernel | `archLevyDensity`, `levyEnergy`, `gammaKernelMeasure`, `gammaFarCharge`, `gammaTailMass` | $k(t)=\sum_k e^{-(2k+1/2)t}$; archimedean jump energy |
| Haar interaction | `haarPrimeMatrix`, `haarGammaCoupling`, `haarPoleCoupling`, `haarWeilInteraction` | complete finite Weil matrix on Haar coefficients |
| Ledgers | `fullZeroForm`, `chebyshevTwoPoleDefect`, `criticalDeficitSourceEnergy` | $E(s)=e^s+s-1-\psi(e^s)$ |
| Off-line field | `offLineField`, `localZeroWeight` | $\Phi(\gamma)=\sum(\Re q-\tfrac12)^2/(1+(\Im q-\gamma)^2)^2$ |
| Gram certificates | `ZeroBlockData`, `IsInertiaCertificate`, `qStar`, `sineKappa₄` | inertia functionals of the zero-side evaluation Gram |
| Meyer source carrier | `MeyerScalingCycle`, `meyerSourceTrace`, `meyerPrincipalCycle`, `meyerTraceBoundedIdeal`, `meyerHilbertReserve` | genuine Poisson source space, sharp involution, convolution, Hasse jets at $\xi$ zeros |
| $L$-polynomial depth | `invRootPoly`, `deepRoots`, `depthProduct` | $\prod(1-\alpha u)$, deep roots $|\alpha|r>1$ |

## 3. Language

- **Degree** = aperture (support radius); **Hodge defect** = number of negative squares of $W$.
- **Right zero**: $\Re\rho>\tfrac12$; **outer eigenvalue**: $|p^{\rho-1/2}|>1$; **visible**: nonzero Frobenius weight.
- **Cardinal invariant**: Hodge defect (#distinct right zeros). **Metric invariant**: exponential rate of the defect floor in the degree (= zero width).
- **Fake datum**: satisfies all span/Euler/integrality data, violates RH. **Unitary**: all $|\beta|=1$.
- **Kronecker rank**: rank of zero frequencies (1 for curves = period, ∞ for $\zeta$).
- **Resonant prime/scale**: two right zeros share $e^{\ell(\rho-1/2)}$.
- **Wall**: closed folded spectrum separating $b^{-1}$ from 0 (or positive area near it).
- **Deep-sparse**: right zeros of depth $\ge\sigma$ have convergence exponent $<1$ for every $\sigma>\tfrac12$.
- **Reserve** $\Phi$: source energy defining a section count $\{(\alpha,\beta):\Phi\le2\alpha\beta\}$.
- **Blind**: transform vanishes at every off-line zero.

## 4. Mechanisms

**A. Polar surfaces and the $\mathbb F_q$ calibration.**
1. Orthogonal splitting $x\cdot y=\text{polar}(x,y)+x^\circ\cdot y^\circ$; HI ⇔ CS ⇔ $\delta\ge0$ ⇔ one positive square; $\delta(x,y)^2\le\delta(x,x)\delta(y,y)$ is the one inequality of Weil's proof.
2. Adjunction carries the bound: $(\Gamma,\Delta)$ realizable ⇔ $(q+1-N)^2\le(2q-s)2g$; only the lower adjunction bound $\Gamma^2\ge q(2-2g)$ is used.
3. Span defect = Toeplitz form in power sums; span HI ⇔ unitarity; contact law: Toeplitz PD on window $n$ ⇔ $n\le$ #distinct eigenvalues, radical = multiples of the reduced characteristic polynomial; F_q Pontryagin law: defect = #distinct $|\alpha|>\sqrt q$, fully visible at window $2g$.
4. Fake data: golden datum has integral counts, rational zeta, FE, Witt integrality (ghost components = Lefschetz numbers), rank-one Beurling structure (edge shift, $N_k=\sum_{d|k}d\pi_d$), Adams isometries — and defect 1. Positive Euler/subshift data $N_k\le q^k+1$ cannot satisfy HI at all.
5. What forces the sign over $\mathbb F_q$: 9-way TFAE after pole subtraction (HI, Rosati invariance $\beta\mapsto1/\bar\beta$, zero reflection defect, Hasse–Weil envelope, bounded normalized traces, Toeplitz positivity on $2g$ graphs, Bézout on positive cone). Lower Lefschetz bounds force unitarity; upper bounds miss exactly a positive real outer eigenvalue (golden: $\varphi$). Genus one: defect of a graph = 2·degree; HI = degree positivity of the **ring** $\mathbb Z[F]$ (theorem of the square) = Hasse.
6. Curve inside the scaling surface: the $q$-tower Gram is $\log q\|g\|^2\cdot$spanGram; degree filtration = window filtration (jumps $0\to\infty$); radical aperture $=d\log q/2$; numerical equivalence = Frobenius ideal $P(T_q)$; Weil floor rate = 2·zero width; first negative lag located by Turán. Towers at $\ell=(a/b)\log q$ have finitely many outer eigenvalues ($b$-th roots of $\beta^a$; $\ell=a\log q$ = base change), irrational $\ell/\log q$ gives infinite defect.
7. Moments cap depth only: $\prod_{\text{deep}}|\alpha|r\le\max_{|u|=r}|L|$; an off-line pair $\rho,\rho^{-1}$ costs the circle maximum only $(1+\rho)(1+\rho^{-1})$, so moment generating functions cannot see fixed numbers of off-line pairs.

**B. The scaling surface of $\mathbb Z$.**
8. $\mathbb Z$-surface: $H^2=V^2=0$, $H\cdot V=1$, defect = Weil form; local intersection = local side of explicit formula (prime comb − archimedean collar, pole cancelled). Signature law (Haynsworth): #pos $=1+$#neg$(W)$; one positive square ⇔ RH ∧ weight $=\Lambda$.
9. Pontryagin laws: finite, tempered (density of the zero map in $\ell^2(Z)$; $W$ = Krein form with negative vectors $e_\rho-e_{1-\bar\rho}$), cyclic (translates of one generic test along any dense shift set, e.g. $k\log p+l\log q$), sector (even/odd each carry half for $\zeta$; real off-line zeros odd-only). Defect counts distinct right zeros, not multiplicity or depth.
10. Kronecker-rank dichotomy: vertically recurrent configurations (periodic, finite Dirichlet polynomials) have defect 0 or ∞. Infinite genus: a compact test vanishing at all but finitely many simple critical zeros is 0, so over $\mathbb Q$ $W$ has no radical.
11. Degree filtration of $\zeta$: defect 0 through degree $3/10$ (odd through $181/500$, past prime 2 via Schur lending); finite at every degree: $\le1+4aT(a)/\pi$ (band inequality + Bessel–Shannon count); HI holds on tests vanishing on an explicit finite low-frequency grid $D_a$ + pole (coercivity $E(a)(1-1/\pi)\int f^2$); near radical has two-sided Landau–Widom dimension $(2\pm\eta)e^{2L}$, eigenvalues doubly-exponentially small.
12. Visibility: isolated pair seen at $\sinh(2\delta a)/\delta=2L+2a$; collective invisibility; under RvM background density visibility aperture is exactly $\Theta((\log\log\gamma_0)/\delta_0)$; height-uniform visibility under bounded off-line copies; unconditional alternative: defect rate = zero width, or off-line copies cluster without bound.
13. Metric invariant: odd and full defect floor rates $=$ `Ici zetaZeroWidth` (H¹ normalisation); all-parity identity $\text{fullZeroForm}=(\gamma_0-2)\|F\|^2+\text{Lévy}+4J(F)+2\int_0^{2A}I\,D^2(\text{autocorr})$; Vinogradov–Korobov floor $-Ce^{r-\kappa r^{ex}}$.
14. Nondegeneracy: the scaling pairing has zero numerical radical (numerical equivalence = equality); nonzero compact sources are never Hecke/Adams eigenvectors and their orbits are linearly independent.

**C. Hecke incidence and the prime side.**
15. Cartesian/Kronecker law: $\Gamma_a\cdot\Gamma_b$ prime part $=\tau_p(|v_p(a)-v_p(b)|)$ if exponent vectors differ in one prime, else 0: Euler product on the surface; cross-prime coupling only archimedean/polar. Successors $k,k+1$ meet only through the collar ($\omega(\log(1+1/k))\asymp k/2$) and carry pole mass $1/(k(k+1))$.
16. Finite Euler lattice form $\kappa\sum c^2-\text{heckeForm}$ is PSD on all $P$-boxes ⇔ $\kappa\ge\sum_{p\in P}E_p$ (exact); resonator adjunction remainder is negative definite ($w_r^2<E_r$); the mean-field adjunction conjecture is refuted (cross aggregate $\asymp e^{2r}$).

**D. Towers, Lefschetz sequences, one prime vs two.**
17. One prime tower = period quotient: Toeplitz Gram in Laurent moments; defect ≤ #visible distinct outer eigenvalues; equality by Cesàro class extraction when levels are well-founded; almost every prime separates finitely many right zeros.
18. Wolff obstruction: two annulus Wolff measures give injective families with all Laurent moments zero; a symmetric Wolff configuration makes one prime blind (Toeplitz $=4\sum c\cdot I$). Positive survivors: blindness of a fixed test needs a **wall** — discrete Cauchy transform $G(z)=\sum q_\tau/(1-c_\tau z)$ vanishes on the origin component; residue/∂̄-uniqueness extracts the class at every accessible or null-accessible pole; countable folded spectra never blind.
19. Test-side removal of Wolff accumulation: Ingham–Paley–Wiener annihilators kill a sparse set ($\sum|a|^{-s}<\infty$, $s<1$) and nothing else off $\mathbb R$, at any support radius. $\zeta$ is deep-sparse (Ingham–Huxley), so one test at every prime carries one negative square per distinct $p^{\rho-1/2}$; one probe modulation $\varphi e^{isu}$ makes every outer eigenvalue at every prime visible (class weight entire in $s$, positive at $s=t+i\delta$).
20. Over all tests, for every tempered configuration and scale: some window has $n$ negative squares ⇔ ≥ $n$ outer eigenvalues (interpolation + density; no sparsity). One shift $v>0$: no right zero ⇔ $W(g-T_vg)\ge0$ for all $g$.
21. Lefschetz growth: one universal test has $c_m^{(p)}=O(R^m)$ ⇔ $R\ge p^w$ at every prime ($w$ = zero width); off-line zeros are Lefschetz ratios $c_{m+1}/c_m\to p^{\rho-1/2}$ and two primes determine $\rho$; one-sided bounds suffice (rotating phase rises above $|W|/8$ infinitely often; two-term tests $g+cT_vg$ rotate real-eigenvalue weights), at one prime and on tests of arbitrarily short support. Local/global split: windows of width ≤ 3/10 are Weil positive, the Lefschetz bound for $T_{p^m}$ on them is all of RH.
22. Resonant scales are countable; at all but finitely many primes #outer eigenvalues = #right zeros.

**E. Effectivity, Bézout, Riemann–Roch.**
23. HI ⇔ some effectivity with RR + Ample (or RR + Bézout, or surface RR + nef + Bézout). Bézout holds unconditionally for nonnegative disjoint tests (prime incidence + collar $\ge0$); self-intersections carry $-A(0)\|f\|^2$. Positive test cones fail RR.
24. Universal floor law: for any ample cone of nonnegative degree, RR ⇔ open positive cone ⊆ E ∧ defect ≥ 0. The unconditional half of an RR/Ample split is always the trivial half.
25. Source cones: RR ⇔ $\Phi\le$ defect; RR + Bézout ⇔ $\Phi=$ defect exactly; Bézout ⇔ $\max(\delta,0)^2\le\Phi^+\Phi^+$. $L^2$ effectivity (RR ∧ Ample) ⇔ $c>0$ ∧ $c$-coercive; at aperture $r\ge3$ coercivity $c\le K\exp(\tfrac{11}2r-\pi e^{2(r-2)})$ even under RH; no aperture-independent Hardy weight.
26. Finite information cannot give Bézout: $W$ (and unit-mass $W$) is unbounded on every finite-reading kernel, so no function of finitely many readings (and mass) is a Bézout reserve; the exact arithmetic cone needs infinitely many degrees.
27. Majorants: local ($\text{defect}+2(10+72e^r)\|f\|^2$) and global (exponential mass pays $\sum\Lambda/n^{3/2}$) reserves give Bézout + Ample, pointed generating convex cones, never RR. Bézout costs exactly twice the negative reserve.
28. Exact arithmetic source cone (critical-deficit reserve) = positive cone: RR unconditional, Bézout/Ample/additivity/one-Adams-stability ⇔ RH.
29. λ-ring and Lefschetz: λ-splitting, Adams isometries, Lefschetz trace formula $\Gamma_{p^k}\cdot\Gamma_{p^l}=p^{\min}L(p^{|k-l|})$ hold verbatim and for any weight (not discriminating); pole-cancelled Lefschetz–adjunction identity; Hecke graphs of $\mathbb Z$ obey no parallelogram relation (monoid, not ring).

**F. Arithmetic sections and cells.**
30. Arithmetic sections below integer-log spacing ($w\le c/N$): prime sum = finite Hecke matrix; Lévy $\log(1/w)$ + tilted rows beat $\log N$; complementary pole sums pay the pole product ⇒ $\int f^2\le W$, RR + Ample + HI on the whole section space. Separated profiles: span $\le\kappa\log(1/\delta)$, $\kappa<2$.
31. Complete-cell transfer: every compact $C^2$ test is the limit (rate $1/N$) of complete log-cell sections retaining Gamma energy, all prime translations, mass and both pole moments; Weil prime term = limit of divisibility forms; pole-preserving smoothing (equal exponential moments at $\pm\tfrac12$) gives smooth cell spans of exact dimension (Titchmarsh).
32. Haar cells: prime action = incidence of odd boundaries $(2a+1)m=2b+1$ (prime 2 drops out; average→detail block zero); prime energy ≤ $\sum(16+\log(2a+1)/\sqrt2)M_ac_a^2$; divisor-square completion $D_X=Q_X+\sum\Lambda(2a+1)M_ad_a^2\ge(\log2/12)\sum M_ad_a^2$; Gamma pays $\sum\log a\,M_ad_a^2$; poles $\ge-\tfrac{7}{144}\sum M_ad_a^2$. Every single cell has $W\ge M_a/10$; high tails have $W\ge\sum M_ac_a^2$; smooth versions give RR/Ample/HI in every dimension.
33. Gamma accounting: $k=\sum e^{-(2k+1/2)t}$ ⇒ rank-one inequalities; disjoint intervals: $\sum\log(1/|I|)\mathrm{Var}_I f\le\text{levyEnergy}$, plus a positive mean graph and exterior charge; exact $\Gamma(\sum f_i)=\sum\Gamma(f_i)-\sum\text{rectangles}$ with error $\le e^{1/2}\sum|I_i|D_i$; all Haar Gamma cross terms are $\ge0$ (Laplace factorization) and $\le16e^{1/2}\int h^2$ in total; mixed coarse/detail coupling $B^2\le128e^{1/2}\Gamma(g)\int h^2$; complete source pays full coarse Gamma + log detail up to $C\int g^2$ (universal $C$).
34. Exact Haar Weil matrix: $W(h)+G_X=Q_{\rm res}+R_X+P(h)+\sum V_X(a)u_a^2$ with additive Gamma graph $G_X\ge0$; prime edges retain $(1-\log2/\log3)$ of their divisor squares and have interaction entries $\le-(\log3-\log2)M_b/\sqrt m<0$; the signed potential $V_X$ remains.

**G. Zero-density-filtered positivity (heights).**
35. Carrier modulation $F_0\cos\gamma u$ keeps prime support but localizes zeros to $|\Im\rho|\asymp\Gamma$; each zero contributes depth-sum square − depth-difference square. Frequency-averaged: sub-power floor for $A\le\alpha\log\Gamma$, $\alpha<2/3$; strict positivity $\ge\tfrac1{128}\log\Gamma\|F_0\|^2$ for $A\le\kappa_0\log\Gamma$; short windows $H\ge\Gamma^{99/100}$.
36. Pointwise: $Q_\gamma(F_0)\ge-4(A+1)^2e^AN(F_0)^2\Phi(\gamma)$; $\Phi>\eta$ on measure $O(H/(\eta\log\Gamma))$; at zero ordinates $Q\ge(\int F_0)^2-\dots$ ⇒ strict positivity at almost every zero ordinate and on a positive proportion of heights, uniform in aperture and nonnegative test.

**H. Gram certificates (proportions of simple zeros).**
37. Rank–trace inertia certifies $(2-\kappa)N$ simple critical zeros (2/3 at $\kappa=4/3$) without orthogonality; coalescent off-line pairs and double zeros are indistinguishable to Gram functionals; spectral slack conserved; grid ceiling refutes the 3/4 slack hypothesis for $\lambda<3/4$; HD(1) ≥ 1681/2500 but < 254/375; off-line moment ≤ 0.066V; 3/4 is conditional (prime surplus, coalescent surplus ≤ 1/18).
38. Higher inertia: cubic weights add nothing beyond 2/3 at sine moments ($\kappa_2=4/3,\kappa_3=2$ equal the blind spot); fourth moment $\kappa_4=13/4$ (computed) separates it and gives exactly 16/21 — conditional on $\zeta$'s Gram having sine moments.

**I. Meyer source carrier.**
39. Poisson principal cycles are invisible to every reading; numerical radical = Mellin values vanish (= boundary ⇔ $\xi$ simple); origin degree does not descend; boundaries are dense in origin $L^2$ (every continuous class reading constant).
40. Algebra: sharp-stable *-algebra; finite jet blocks $\mathbb C[t]/t^{m_\rho}$; central projectors; algebraic characters = $\xi$-point evaluations; positive Hermitian degrees see only critical values with weights ≥ 0.
41. Carriers with unconditional HI/RR/Bézout/Ample: bounded centered orbits (= critical top jets), and the **maximal blind ideal** (off-line Mellin values zero) — the unique maximal sharp-stable positive ideal; whole space ⇔ RH. Faithful HS reserve: Bézout + Ample, RR ⇔ RH ∧ simple; flow-invariant majorant ⇔ RH.
42. Harmonic coupling: escaping the blind ideal needs dilated channels; nonnegative cosine polynomials obey the strict Fejér barrier $a_1<2a_0$ (saddle gain LUB $3-2\sqrt2$, unattained); this reproduces $\zeta(1+it)\ne0$ and dVP collars; double-pole and periodic-pole countermodels show sharpness.

## 5. Pillar theorems

| Theorem | Lean |
|---|---|
| HI ⇔ CS ⇔ defect ≥ 0; the one CS inequality | `hodgeIndex_tfae`, `defect_sq_le_of_hodgeIndex` |
| Adjunction/Hasse–Weil threshold | `realizable_adjunction_iff`, `realizable_of_free_selfIntersection` |
| Span defect = Toeplitz; span HI = RH of datum; F_q Pontryagin | `spanDefect_eq_toeplitz`, `hodgeIndexOnSpan_iff_unitary`, `pontryagin_law_curve` |
| Fake curves | `goldenDatum_negIndex_spanGram`, `witt_integral_not_pure`, `goldenDatum_beurling_not_pure`, `not_hodgeIndex_of_subshift_bound` |
| Forcing data over F_q | `forcing_arithmetic_data_tfae`, `oneSided_forcing_tfae`, `genusOne_hasse_tfae`, `heckeCorrespondence_no_square_relation` |
| Scaling HI = RH; signature; Λ selected | `scalingSurface_hodgeIndex_iff`, `riemannHypothesis_iff_one_positive_square`, `one_positive_square_iff_vonMangoldt` |
| Pontryagin laws | `pontryagin_law_finite`, `pontryagin_law`, `cyclic_pontryagin_law`, `sector_pontryagin_law` |
| Kronecker dichotomy; infinite genus | `recurrent_pontryagin_dichotomy`, `expPoly_pontryagin_dichotomy`, `eq_zero_of_paperFT_vanish` |
| Degree filtration of ζ | `zeta_hodgeDefectAt_eq_zero`, `hodgeDefectAt_zeta_le_shannon`, `re_W_zeta_nonneg_of_lowGrid`, `lowBlindTests_effectivity` |
| Landau–Widom near radical | `zeta_landau_widom_two_sided_dimension_law` |
| Metric invariant = width | `oddDefectFloorRate_eq_zetaZeroWidth`, `fullDefectFloorRates_eq_Ici`, `exists_fullZeroForm_ge_neg_vk_sobolev` |
| Visibility | `hodgeDefectAt_isolatedPair`, `scalingSurface_defectRate_eq_zetaZeroWidth_or_offLine_cluster` |
| Nondegeneracy; Hecke freeness | `scalingSurface_pairing_nondegenerate`, `heckeCorrespondence_sum_numerically_trivial_iff` |
| Kronecker law; finite Euler threshold | `heckeIncidence_box`, `box_finiteEulerForm_nonneg_forall_iff`, `resonatorRemainder_neg`, `not_exists_polynomial_adjunction_bound` |
| Tower laws | `tower_pontryagin_law`, `tower_law`, `zeta_one_prime_tower_law`, `zeta_exists_test_onePrime_tower_law`, `zeta_almost_every_prime_tower_law` |
| Wolff obstruction and walls | `exists_symmetric_wolff_toeplitz_blind_configuration`, `not_accessibleOff_of_towerGram_psd`, `not_nullAccessibleOff_of_towerGram_psd` |
| Annihilators; ζ deep-sparse; probes | `exists_annihilating_test`, `deepSparse_zeta`, `exists_probe_frobWeight_ne_zero` |
| Lefschetz growth/ratios | `zeta_exists_universal_lefschetz_growth`, `zeta_exists_test_lefschetz_ratio` |
| One-sided, short cycles | `zeta_width_le_iff_oneSided_onePrime`, `zeta_twoWindows_local_global`, `rightZeros_eq_empty_iff_twoWindow` |
| Base changes; resonance | `curve_tower_law_baseChange`, `countable_resonantScales`, `finite_primes_encard_outerEig_ne` |
| Effectivity ⇔ HI; Bézout | `exists_effectivity_iff_hodgeIndex`, `exists_bezout_effectivity_iff_hodgeIndex`, `localPair_nonneg` |
| Floor law; source-cone rigidity | `riemannRoch_iff_openPositiveCone_subset_and_defect_nonneg`, `sourceCone_riemannRoch_and_bezout_iff`, `l2SourceCone_effectivity_iff` |
| Gaussian ceiling; Sobolev RR = width | `exists_l2SourceCone_realTestsAt_coercivity_le_doubleExp`, `zetaZeroWidth_le_iff_gradedSobolevSourceCone_riemannRoch` |
| No finite-reading Bézout | `finiteLinearReadingSourceCone_not_bezout`, `globalExactArithmeticSourceCone_not_finiteLinearReading` |
| Majorants; factor 2 | `arithmeticMajorantSourceCone_bezout`, `globalArithmeticMajorantCone_bezout`, `sourceCone_doubledReserve_bezout_iff` |
| Exact cone; Lefschetz identity | `exactArithmeticSourceCone_eq_positiveCone`, `arithLefschetz_eq_selfPair_add_defect_add_adamsVar` |
| Arithmetic sections | `integral_sq_le_weilPair_arithmeticSection`, `exists_separatedSections_effectivity` |
| Complete-cell transfer | `exists_completeFiniteSourceTransfer`, `finrank_smoothCell_span` |
| Haar effectivity | `haarPrimeLogDefect_ge_mass`, `haarPrimeLogDefect_add_pole_ge_mass`, `haarProfile_roughWeil_ge`, `exists_haarTail_roughWeil_floor`, `exists_smooth_haar_effectivity` |
| Gamma accounting | `levyEnergy_ge_sum_log_variance`, `abs_levyEnergy_sum_sub_diagonal_le`, `haarGammaCoupling_nonneg`, `completeGammaMixed_sq_le`, `exists_completePair_gamma_coarse_detail_bound` |
| Exact Haar matrix | `haarSectionProfile_roughWeil_add_graph_eq`, `haarPrimeGammaReserve_ge`, `haarWeilInteraction_prime_edge_neg` |
| Odd sector past prime 2 | `scalingSubsurface_odd_hodgeIndex`, `weilPair_self_ge_of_mem_primitiveSmoothRealTestsAt_primeTwo` |
| Height-filtered positivity | `exists_logarithmic_aperture_frequencyAverage_fullZeroForm_cosineSource_pos`, `exists_shortWindow_frequencyAverage_quadrature_pos`, `neg_offLineField_le_fullZeroForm`, `exists_shortWindow_almostEvery_zeroOrdinate_positive`, `exists_shortWindow_positiveProportion_heights_weilPositive` |
| Gram certificates | `two_thirds_and_pair_correlation_escape`, `not_three_quarters_zeroSideSlack_of_lt_three_quarters`, `eventually_offLineMoment_le_sixtySix_thousandths`, `sineKappa₄_eq`, `ae_eq_zero_of_doubleExp_simpleCritical_ge_three` |
| Meyer carrier | `meyerSourceTrace_radical_eq_boundary_iff_simple`, `meyerMultiplicativeDegree_iff_point`, `isGreatest_meyerSharpPositiveIdeal`, `meyerTraceBoundedSurface_hodgeIndex`, `meyerHilbertSourceCone_bezout`, `no_continuous_faithful_meyer_class_reading` |
| Fejér barrier and its sharpness | `cosinePolynomial_purchase_ratio_lt_two`, `riemannZeta_boundary_ne_zero_from_harmonic_forcing`, `doublePole_boundary_zero_survives_all_degrees`, `isLUB_fejerSaddleGainSet` |
| Moment depth ceiling | `depthProduct_le`, `depthProduct_offLinePair` |

## 6. Tools

**Developed.**
- Abstract polar-surface calculus: polar/primitive splitting, effectivity axioms, cone classification, compensated surfaces, source-section cones and their rigidity criteria.
- F_q laboratory: curve data, fake data (golden, hiding, pure), Witt/λ-ring series, Beurling shifts, span Toeplitz forms, base change, Turán lag location.
- Zero-side Krein machinery: `zeroMap` density, `exists_test_interpolating`, dual tests, symmetrized sector vectors, rectangular-congruence inertia bounds.
- Tower machinery: Laurent-moment Toeplitz Grams, Cesàro/top-down class extraction, discrete Cauchy transforms, ∂̄-uniqueness (Cauchy–Pompeiu), accessibility geometry, Ingham annihilators, probe modulations, two-term rotations.
- Low-frequency analysis: band inequality, Lipschitz sampling grids, sharp Bessel–Shannon counts, Gaussian Riemann-kernel ceilings.
- Cell calculus: log-cell atoms, exact Hecke subdivision, log-step profiles, pole-preserving smoothing, Haar cells, Gamma rank-one/variance/rectangle measures, uniform row bounds (near/adjacent/distant), Laplace factorization of Gamma couplings.
- Height filtering: modulated sources, depth-sum/depth-difference polarization, off-line field, short-window Selberg absorption.
- Gram certificates: rank–trace and quartic inertia functionals, sine-kernel moment integrals ($\int S^6=11/20$, four-cycle vanishing).
- Meyer algebra: Hasse jet sources, causal projectors, Hermitian degree parts, HS reserves, centered flow.

**To build.**
- An effectivity with ampleness proved without the sign and RR from a section law (count or vanishing) that reduces to Weil's over $\mathbb F_q$.
- Joint payment on complete cells: the signed potential $V_X$, remaining Gamma graph and both poles together, first-prime and coarse sources.
- A one-prime Lefschetz bound on short cycles.
- A positivity mechanism on a sharp-stable carrier larger than the blind ideal that passes $a_1<2a_0$.
- A correspondence ring for $\mathbb Z$ (graph map with a theorem of the square).

## 7. Open questions

1. RR for $\mathbb Z$: close the finitely many low-frequency directions ($D_a$ + pole) at every degree by an effectivity not defined through the sign.
2. A section law: source-defined cone whose RR follows from counting/vanishing, not from a floor.
3. Full-source Haar/complete-cell positivity: control $V_X$, $G_X-G_{\rm prime}$ and $P(h)$ jointly.
4. Degree floor below rate ½ (= zero-free strip) from an effectivity input.
5. One fixed test across a wall of positive area or a separating continuum.
6. The one-prime Lefschetz bound on cycles of width ≤ 3/10 — the whole content of HI.
7. The clustering branch of the visibility alternative.
8. Positivity beyond the maximal blind ideal; vanishing of the Meyer packet residual.
9. Sine moments of $\zeta$'s zero-side Gram (needed for 16/21); coalescent surplus ≤ 1/18 (for 3/4).
10. Whether $\mathbb Z$ has a substitute for $\mathbb Z[F]$: a parallelogram relation among Hecke graphs.

## 8. Traps

| Trap | Truth |
|---|---|
| Span/Euler/integrality/FE/λ-ring data force HI | Golden fake curve has all of them and defect 1 |
| Adjunction is the missing ingredient | It is exact on $\mathbb Z$; RR is missing |
| Positive tests are effective | Bézout yes, RR no |
| An unconditional half of an RR/Ample split is progress | That half is always trivial; the content moves to the other axiom |
| A source cone with RR is new | RR ⇔ coercive floor $\Phi\le$ defect; with Bézout ⇔ $\Phi=$ defect |
| Finitely many readings + mass give Bézout | $W$ unbounded on every finite-reading kernel |
| A bigger arithmetic reserve helps | Gives Bézout + Ample, kills RR; Bézout costs 2× the reserve |
| Compensated-surface HI is RH | It is a floor statement |
| Subexponential/constant floor, one-prime towers, one shift, Lefschetz minors, one-sided bounds, Hecke-stable cones, blind ideal = whole space | Each is an exact RH equivalent |
| One fixed test always sees the tower | Only off a wall; over all tests (or one probe at ζ) yes |
| Multiplicities/depth count | Defect counts distinct right zeros |
| Short-window positivity settles RH | Windows ≤ 3/10 are positive; the Lefschetz bound on them is all of RH |
| Height-averaged positivity implies RH | Pointwise positivity at every height is RH; averages and a.e. statements are not |
| Gram functionals separate double zeros | Coalesced pairs and double zeros have equal Gram through third order |
| Moment growth sees off-line pairs | Only through the depth product; fixed pairs hide |
| Linear section counts are selective | Reweighting-invariant: Λ and shifted pair indistinguishable |
| Origin $L^2$ completion keeps the arithmetic | Boundaries are dense; continuous class readings are constant |
| Harmonic coupling escapes freely | Strict Fejér barrier $a_1<2a_0$; it reproduces only the classical zero-free region |
| Paper Haar positivity on tails is full positivity | Signed potential and joint pole/graph payment remain open |

## 9. Context

| Programme | Relation |
|---|---|
| `RHTower` (119 imports) | Explicit formula, Weil Gram, zero-density, Ingham–Huxley, Selberg windows, Deninger–Meyer sources, CCM ground energies |
| `HTGeometry` (27) | Hermitian inertia, Cauchy–Pompeiu, Wolff measures, cosine-polynomial cap, HS operators |
| `SquareRootThreshold` (24) | Tempered configurations, zero width, small-aperture positivity, lag tests |
| `ArithmeticIncidencePositivity` | Schur lending odd window 181/500; shared-derivative ledger |
| `ArithmeticCriticalityTheory` | Gaussian/primitive-hyperplane ground energies, quartic gauge window |
| `ArithmeticCompensationTheory` | Horizon energy and inverse-square translation deficit in the all-parity identity |
| `BiScaleUncertainty` | Critical-deficit endpoint law; zero-density-filtered deficit |
| `TransThresholdPairCorrelation` | Close-pair energy and 4/3 smooth certificate for proportion laws |
| `SpacingScaleHarmonicAnalysis` | Atom self-energy, stability at spacing scale, Lévy-norm continuity of $W$ |
| `RenormalizedArithmeticPotentialTheory` | Inverse prime number operator / occupation energy for Haar valuation coordinates |
| `ArithmeticOrientationTheory`, `ArithmeticOrientationGeometry` | Nyquist rank bounds, Schur dominance of prime towers, width functor; orientation of cycles (both directions of import) |
| `ArithmeticPositiveDuality`, `ArithmeticDefectRigidity` | Hamburger rigidity, record-minimum cofactor limits (used in `ArithmeticForcesBlindness`) |
| `ArithmeticIndexDescent` (23 importers) | Builds finite-index descent on complete cells and Haar/Gamma accounting |
| `SignedArithmeticHodgeTheory`, `ArithmeticCorrespondencePositivity`, `HeckeKreinToeplitz`, `ArithmeticLorentzianGeometry`, `ArithmeticEffectivityTheory`, `ArithmeticPolarization`, `BiarithmeticGeometry`, `SelectiveMultiscaleArithmeticPositivity` | Downstream users of the scaling surface, tower laws and effectivity cones |

ACS is the geometric core: it supplies the intersection-theoretic dictionary (surface, Hecke
correspondences, Frobenius towers, effectivity) that orientation, index-descent, Hodge and Krein
programmes take as their language.

## 10. Big picture

ACS shows that $\mathbb Z$ already has almost all of Weil's machine: an intersection pairing,
hyperbolic fibres, exact Lefschetz and adjunction identities, unconditional Bézout for effective
cycles, a nondegenerate pairing, a cardinal and a metric measure of failure that equal the number of
right zeros and the zero width, and a prime tower that sees every off-line zero. What is missing is
narrow and sharply located: an effectivity whose ampleness and Riemann–Roch are proved without the
sign. Every source-defined cone tried either reduces RR to a coercive floor, or buys Bézout and
ampleness at the price of RR, and no finite-information cone can be Bézout. The fake curves show why
data cannot force the sign — only effectivity (sections) does — and genus one shows that Weil/Hasse
use a ring of correspondences, while $\mathbb Z$ only has a free monoid of Hecke graphs. Positivity
does exist in large unconditional pieces: short windows, low-frequency-blind subspaces, arithmetic
and Haar sections, the blind ideal, almost every height. Each piece fails exactly at a stated
boundary (finitely many low frequencies, a signed potential, the Fejér barrier, a wall, a one-prime
Lefschetz bound). The message for the RH programme: the proof must construct sections — an
arithmetic Riemann–Roch on the scaling surface — rather than refine estimates of the form; once the
finitely many low-frequency directions at each degree are governed by such sections, the rest of the
Hodge index is already in place.
