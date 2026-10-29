# Arithmetic Castelnuovo–Severi Theory (ACS)

Namespace `GaloisForLFunctions.ArithmeticCastelnuovoSeveri`; umbrella `ArithmeticCastelnuovoSeveri.lean`.

**Question.** Weil proved RH for curves over $\mathbb F_q$ by reading the zeta function as an
intersection theory on $C\times C$ and the positivity of its explicit formula as the Hodge index
theorem. Which ingredients of that proof exist for $\mathbb Z$, which are provably absent, and what
would a proof of the missing ones have to produce?

ACS is the intersection theory of the **scaling surface** of $\mathbb Z$: cycles are the pole plane
$\langle H,V\rangle$ (directions $e^{\mp u/2}$) plus Weil tests; the pairing is the local side of the
explicit formula; the Castelnuovo–Severi defect is Weil's form; the Hodge index is RH
(`scalingSurface_hodgeIndex_iff`). The surface is a vector space with a pairing, not a scheme. Every
statement is unconditional and calibrated over $\mathbb F_q$.

---

## 1. Place in the research

Live route: source-defined sections → all-aperture Riemann–Roch with ampleness → scaling Hodge
index → RH. ACS contributes the exact count of the form's failure (right zeros), its localisation on
one prime tower, the $\mathbb F_q$ calibration, the fake data any forcing argument must exclude, and the
source-carrier (Meyer) theory of where effectivity can live.

| Programme | Connection |
|---|---|
| arithmetic-positivity-theory | The Weil–Markov–pole form whose positivity is Hodge index |
| ArithmeticIncidencePositivity | Ratio atoms = Hecke incidence; odd-sector ledger |
| SquareRootThreshold | Visibility laws → degree filtration; width–floor alternative |
| ScaleSignedIncidenceCriticality | Bounded readings; ACS supplies hiding examples over $\mathbb F_q$ and $\mathbb Q$ |
| BezoutValuationIncidence | Consecutive integers have no prime Hecke intersection |
| ArithmeticCriticalityTheory | Same sign via ground energies; ACS counts it via signature |
| ArithmeticCompensationTheory | Comb mean field; horizon energy $J$ in the all-parity identity |
| TransThresholdPairCorrelation | Analytic engine of the route to $3/4$ simple zeros |
| ArithmeticOrientationTheory | Takes the scaling surface as geometric core |
| ArithmeticOrientationGeometry, ArithmeticLocalDivisorGeometry | Reflection transport; source-defined local divisor tests |
| `HTGeometry` | Blaschke-wall permeability, factorial/log bounds used by tower laws |

`RHTower` supplies the explicit formula, Weil criterion, Lévy–Khintchine form and matrix inertia.

---

## 2. Why

Weil's five ingredients: (i) intersection pairing; (ii) fibres $H,V$, $H^2=V^2=0$, $H\cdot V=1$;
(iii) Frobenius graphs, $\Gamma\cdot\Delta=\#C(\mathbb F_q)$ (Lefschetz); (iv) $\Gamma^2=q(2-2g)$ (adjunction);
(v) Riemann–Roch ⇒ Hodge index $D^2\le2(D\cdot H)(D\cdot V)$ ⇒ $|N-q-1|\le2g\sqrt q$.
Over $\mathbb Z$, (i)–(iv) are exact (hyperbolic pole plane, prime comb = Lefschetz, archimedean term =
adjunction). Over $\mathbb F_q$ the same span identities hold for **fake** data violating RH, so they
cannot force the sign. Weil's sign comes from **effectivity**: effective divisors are zero sets of
sections, meet nonnegatively (Bézout), and Riemann–Roch supplies enough of them. ACS isolates which
of these the scaling surface has.

---

## 3. Objects and language

| Weil over $\mathbb F_q$ | Scaling surface of $\mathbb Z$ | Lean |
|---|---|---|
| $C\times C$, pairing | cycles $aH+bV+f$, explicit-formula pairing | `scalingSurface` |
| fibres | pole plane; $f\cdot H=\int fe^{-u/2}$, $f\cdot V=\int fe^{u/2}$ | `PolarSurface`, `poleB`, `poleA` |
| defect $2(D\cdot H)(D\cdot V)-D^2$ | Weil form | `defect` |
| Frobenius graphs | Hecke cycles $T_a$ (translates by $\log a$) | `heckeCycle`, `translate` |
| Frobenius eigenvalues | $p^{\rho-1/2}$ on the tower of $p$ | `frobEig`, `towerGram` |
| Lefschetz numbers | prime comb; Lefschetz sequence $c_m=W(T_{p^m}g,g)$ | `graphPair` |
| adjunction | archimedean collar (Lévy jump form) | `re_archCross_eq` |
| genus $2g$ | zero count (infinite) | — |
| Bézout | disjoint nonnegative tests meet $\ge0$ | `localPair_nonneg` |
| RR ⇒ Hodge | effectivity with RR + ample axioms | `RiemannRochAxiom`, `AmpleAxiom`, `BezoutAxiom` |
| #eigenvalues $|\alpha|>\sqrt q$ | #distinct zeros $\Re\rho>\tfrac12$ | `pontryagin_law_curve`, `pontryagin_law` |

Further objects: curve data (`CurveDatum`), span defect = Toeplitz form (`spanGram`), fake curves
(`goldenDatum`: $q=5$, $\beta=\varphi,\varphi^{-1}$), zero configurations (`ZeroConfig`, `TemperedConfig`),
Hodge defect (`hermNegIndex`, `hodgeDefectAt`), source cones (`gradedSourceCone`, `l2SourceCone`,
`sobolevSourceCone`), Hecke incidence (`heckeIncidence`), odd degree-$r$ subsurface
(`scalingSubsurface`), complete log-cell sections and Haar (balanced pair) cells.

**Words.** *Degree* (pairing with $H+V$) vs *aperture* (support bound). *Hodge defect* = negative
squares of Weil's form. *Unitary* / *fake* datum. *Kronecker rank* of zero frequencies (1 for curves,
∞ for $\zeta$). *Folded spectrum* $\{\beta_\tau^{-1}\}$ of a tower. *Resonant prime/scale* (two right zeros
share $p^{\rho-1/2}$). *Meyer source carrier*: the genuine Poisson source space with sharp involution,
convolution, centred scaling flow, Hasse jets at Xi zeros.

---

## 4. Mechanisms

### Polar surfaces and $\mathbb F_q$ calibration
1. **Polar decomposition** $x\cdot y=(x\cdot H)(y\cdot V)+(x\cdot V)(y\cdot H)+x^\circ\cdot y^\circ$; under Hodge index,
   Cauchy–Schwarz on the defect is the only inequality in Weil's proof. Only $\Gamma^2\ge q(2-2g)$ is used.
2. **Span defect = Toeplitz form** in power sums; span Hodge index = unitarity; Pontryagin law over
   $\mathbb F_q$. A curve's towers are its base changes: the defect is finite exactly at arithmetic scales
   $\ell\in\mathbb Q_{>0}\log q$ and infinite elsewhere.
3. **Fake curves.** The golden datum has integral counts, rational zeta, functional equation, Witt
   integrality, Beurling structure, Adams operations — and Hodge defect exactly 1.

### The scaling surface
4. **Signature law**: #positive squares $=1+$#negative; RH ⇔ one positive square.
5. **Pontryagin law** for every tempered configuration: max negative squares $=\#\{\Re\rho>\tfrac12\}$
   (distinct zeros, not multiplicities).
6. **Degree filtration**: additive; $\zeta$ has defect 0 through degree $3/10$, odd sector through $181/500$;
   finite at every degree ($\le1+4aT(a)/\pi$); failure confined to a low-frequency grid + pole.
7. **Visibility.** Isolated pairs seen at $\sinh(2\delta a)/\delta=2L+2a$; on lag lattices the defect jumps
   $0\to\infty$; under local boundedness of off-line copies the visibility lag is doubly logarithmic
   (dichotomy: defect rate = width, or clustering).
8. **Kronecker-rank dichotomy.** Finite-rank configurations have defect 0 or ∞.
9. **Towers and Lefschetz sequences.** Translates of one generic test along a dense shift set carry
   the whole defect ($\mathbb Z\log p+\mathbb Z\log q$ suffices for $\zeta$). One tower = period quotient with
   Toeplitz Gram in Laurent moments; tower defect = #visible distinct outer eigenvalues $p^{\rho-1/2}$.
   - *Over all tests one prime sees everything*, for every tempered configuration at every scale
     (density of the zero map + interpolation). RH ⇔ $\Re W(T_vg,g)\le W(g,g)$ for complex tests, any $v>0$.
   - *A fixed test is blind only behind a wall*: blindness to $b$ needs the closed folded spectrum to
     meet every disc about $b^{-1}$ in positive area or to separate it from 0; countable folded spectra
     never blind; probes $\varphi e^{isu}$ see every outer eigenvalue. Wolff configurations realise
     Toeplitz blindness of a fixed test at a non-attained top.
   - *Lefschetz growth = width*: $c_m=O(R^m)$ iff $R\ge p^w$; RH ⇔ $|c_m|\le c_0$; one-sided bounds at one
     prime suffice (two-term tests rotate the Frobenius weight); off-line zeros are Lefschetz ratios
     $c_{m+1}/c_m\to p^{\rho-1/2}$; resonant scales are countable.
   - *Short cycles carry all of RH*: the laws hold on tests in $[-\eta,\eta]$ for every $\eta>0$, and for
     $\eta\le3/10$ each window is Weil positive. Hodge index = local positivity (theorem) + the
     one-prime Lefschetz bound on short cycles (all of RH).

### Effectivity, Bézout, Riemann–Roch
10. **Hodge index ⇔ effectivity with RR + ample** (`exists_effectivity_iff_hodgeIndex`); positivity is not
    effectivity; form-defined cones are tautological.
11. **Bézout holds** for effective cycles without common component via the Lévy jump form;
    self-intersections carry $-A(0)\|f\|^2$.
12. **Source cones and boundary rigidity.** RR ⇔ reserve $\Phi\le$ defect; RR + Bézout force $\Phi=$
    defect; Bézout costs twice the negative reserve. Universal floor law: every ample cone of
    nonnegative degree has RR ⇔ open positive cone ⊆ E ∧ defect $\ge0$.
13. **Graded RR.** Explicit negative constants at every aperture; away from the low-frequency divisor
    $D_a$ and the pole, coercivity gives RR, ampleness and Hodge at every degree; no
    aperture-independent weighted cone has RR at all apertures; Sobolev cones: width $\le\sigma$ ⇔
    graded RR at rate $2\beta$, $\forall\beta>\sigma$.
14. **Arithmetic sections.** Narrow profiles at $\log n$ (width $\le c\log(1+1/N)$), or narrow profiles
    at separated centres of span $\le\kappa\log(1/\delta)$, satisfy $W\ge\int f^2$ with no pole condition:
    RR + ample + Hodge on those spans (support restriction remains).
15. **Complete-cell transfer.** Every compact $C^2$ test is recovered by complete logarithmic-cell
    sections; $W$ converges at order $1/N$ with all prime powers, Gamma energy and pole moments; smooth
    pole-preserving cell sections of every dimension.
16. **Haar-cell effectivity.** On balanced pairs of cells: prime energy $\le\sum_a(16+\log(2a+1)/\sqrt2)M_ac_a^2$
    (only odd multipliers $(2a+1)m=2b+1$ couple); Gamma pays $\sum_a\log(a)M_ac_a^2$ (mean-zero/variance
    coercivity $\sum\log(1/w_i)\int_{I_i}(f-\bar f)^2\le\Gamma(f)$); pole $\ge-2\sum M_ac_a^2$. Hence a unit-mass
    floor on balanced tails beyond a fixed index, uniform in horizon, and RR/ample/Hodge on smooth
    versions of every dimension. Every individual Haar cell, including index one,
    now has original Weil energy at least one tenth of its exact mass
    (`EveryHaarCellHasPositiveWeilEnergy`). Exact interval polarization pays
    the central archimedean mass; centering the exponential weights pays
    both poles; the actual prime self-interaction vanishes. Signed sums of
    distinct low-index cells still require their cross terms.
    On every signed Haar section, exact divisor-square completion gives
    $D_X=Q_X+\sum_a\Lambda(2a+1)M_ad_a^2\ge(\log2/12)\sum_aM_ad_a^2$,
    with no removed head (`TheHaarPrimeDefectHasAUniformMassFloor`). Here
    $D_X=\sum_a[\log(2a+1)M_a+O_X(a)]d_a^2-\operatorname{haarPrimeEnergy}$,
    and the exact outgoing charge obeys
    $O_X(a)\le2M_a\sum_{m=2}^{2X+1}\Lambda(m)/m^2$
    (`TheHaarPrimeSourceRetainsItsDivisorSquares`). Both original poles now
    obey $P(h)\ge-7\int h^2/144$ and leave
    $D_X+P(h)\ge D_X/8\ge\int h^2/144$ for every signed section,
    including its whole head (`TheHaarArithmeticReservePaysBothPoles`).
    The exact shared-boundary distance moment makes both exponential
    functionals summable in Haar mass. Every signed Gamma cross term now
    shares one ordinary-mass budget:
    $|\Gamma(h)-\sum_a d_a^2\Gamma(H_a)|\le16e^{1/2}\int h^2$
    (`TheHaarGammaCrossTermsCostOnlyMass`). The stronger bound retains
    the original positive rectangle remainders, including touching cells
    and index one. The joint signed Gamma/central-mass comparison with
    the logarithmic/outgoing arithmetic diagonal remains open.
    Every actual Gamma cross-entry also has a summable positive Laplace
    expansion, including touching cells (`TheHaarGammaCrossTermsArePositive`).
    With $u_a=\sqrt{2a+1}\,d_a$ and
    $K_{ab}=J_{ab}/(\sqrt{2a+1}\sqrt{2b+1})\ge0$, the complete signed form is
    $\Gamma(h)=\sum_a[\Gamma(H_a)/(2a+1)+\sum_bK_{ab}]u_a^2-G_X(u)$,
    where $G_X(u)=\tfrac12\sum_{a,b}K_{ab}(u_a-u_b)^2\ge0$.
    The original Weil form therefore satisfies
    $W(h)+G_X(u)=D_X+P(h)+\sum_aV_X(a)u_a^2$
    (`TheHaarGammaDebtIsAnAdditiveGraph`). The explicit potential
    $V_X(a)=[\Gamma(H_a)+(2\operatorname{gammaHardyPhaseRate}(0)-\log(2a+1))M_a-O_X(a)]/(2a+1)
      +\sum_bK_{ab}$ remains signed. Joint payment must control this
    potential and the graph energy together, retaining both original poles.
    The literal prime edges now pay their own Gamma interactions:
    $J_{ab}\le\log(2)M_b/\sqrt m$ when $2b+1=m(2a+1)$ and $m\ge3$.
    Their graph contribution satisfies $0\le G_{\rm prime}\le G_X$,
    with no duplicated edge, and the remaining divisor squares obey
    $Q_{\rm res}+G_{\rm prime}=Q_X$ and
    $Q_{\rm res}\ge(1-\log(2)/\log(3))Q_X\ge0$
    (`TheHaarPrimeEdgesRetainTheirGammaReserve`). Each surviving original
    prime conductance is strictly positive. The exact full source retains
    $W(h)+(G_X-G_{\rm prime})=Q_{\rm res}+R_X+P(h)+\sum_aV_X(a)u_a^2$,
    where $R_X$ is the entire absent-root charge. The complete interaction
    matrix, including both poles jointly, has prime-edge entries at most
    $-(\log(3)-\log(2))M_b/\sqrt m<0$. This shared-edge payment is checked;
    the remaining graph, signed potential, and poles still need joint payment.
    The actual signed divisor source also has complete valuation coordinates:
    with $x_a=d_a/\sqrt{2a+1}$ and $w_a=(2a+1)M_a\ge1/2$,
    $D_X+T_Q=\tfrac12\sum_e E_Q(e)|\widehat x(e)|^2+R_X$
    (`TheHaarDivisorReserveControlsValuationOccupation`). Here Q consists
    of the source's primes, the product basis has parameters $q_p=1/p$,
    and $E_Q(e)=\sum_{p:e_p>0}\log p\,(e_p+1/(p^2-1))$.
    The full series is summable; original-domain membership is proved.
    The exact cell-weight remainder $R_X$ and boundary charge
    $T_Q=\tfrac12\sum_a(C_Q-O_{0,X}(a))x_a^2$ are nonnegative,
    where $C_Q=\sum_{p\in Q}\log p/(p^2-1)$ and $O_{0,X}$ is the
    actual inverse-square outgoing row. Joint payment must retain T_Q;
    this identity does not bound occupation by D_X alone.
    Pair averages: the average→detail prime block vanishes and
    $\Gamma(g)+\sum\log(a)M_ad_a^2\le\Gamma(f)+C\int g^2$ (coarse source inherits Gamma payment).
    Homogeneous recovery removes the additive mass error at a fixed multiplicative cost:
    $\Gamma(g)+\Gamma(h)\le C\Gamma(f)$, uniformly in horizon. Moreover,
    $\Gamma(f)$ is equivalent to $\Gamma(g)+\sum_a\log(1/w_a)M_ad_a^2$
    (`ArithmeticIndexDescent.CompleteCellAveragesAreBoundedInGammaEnergy`).
    The actual Gamma coupling $B=\Gamma(f)-\Gamma(g)-\Gamma(h)$ satisfies
    $B^2\le128e^{1/2}\Gamma(g)\int h^2$. For every $\varepsilon>0$, one fixed
    detail head approximates $B$ within $\varepsilon\Gamma(f)$ uniformly over
    all signed coefficients and horizons
    (`ArithmeticIndexDescent.GammaCouplingHasUniformFiniteHeads`).
    With $Q=\Gamma(g+h)-\Gamma(h)+W(h)$ and $D=\sum_a\log(1/w_a)M_ad_a^2$,
    one fixed detail head gives
    $Q-B_2-B_{\rm odd}\ge(1-\varepsilon)\Gamma(g)+(1-1/\sqrt2)D/4+\int h^2$.
    Here $B_2$ contains every even mixed exponent and $B_{\rm odd}$ every odd
    mixed exponent at least three. The square tail is arbitrarily small in
    the original complete-profile Gamma energy, using sublogarithmic
    $\zeta'/\zeta$ on $\Re s=1$ and a centred boundary estimate. Moreover,
    $W(h)$ includes every prime-power diagonal, archimedean mass and the actual
    Haar pole product. This subform has uniformly bounded negative dimension
    (`ArithmeticIndexDescent.EveryMixedExponentAboveOneLeavesACoarseReserve`).
    Replacing the Haar pole by the full original pole $P(f)$ retains
    $(1-\varepsilon)\Gamma(g)+(1-1/\sqrt2)D/8+\int h^2$ and the positive
    cosh square, at the cost of the single actual sinh square. The detail
    head and that moment give uniform negative dimension at most $A+1$
    (`ArithmeticIndexDescent.TheFullPolarNonfirstSourceHasUniformFiniteIndex`).
    The entire Haar prime diagonal, including first powers, admits one
    finite coefficient head with error at most $\varepsilon\Gamma(f)$,
    uniformly over all original profiles and horizons
    (`ArithmeticIndexDescent.TheFullHaarPrimeSourceHasUniformFiniteHeads`).
    The exact divisor sum makes large multipliers small; upward incidence
    controls bounded multipliers after a coefficient cutoff. Consequently
    the full-pole source $R$ above obeys
    $|R-(\Gamma(f)+P(f))|\le\varepsilon\Gamma(f)$ after one fixed head,
    retaining $(1-\varepsilon)\Gamma(f)$ and the positive cosh square
    (`ArithmeticIndexDescent.TheFullNonfirstSourceRetainsAlmostAllGamma`).
    This preserves the complete Gamma coupling; the first-prime mixed and
    coarse signed sources still require payment.
    Retained coarse Gamma also pays the missing coarse square source.
    The resulting joint form includes the entire even-prime source exactly
    once, retaining positive coarse Gamma, coarse mass, weighted detail mass,
    detail mass and the cosh square. One fixed head and the original sinh
    and ordinary-mean moments give uniform negative dimension at most $A+2$
    (`ArithmeticIndexDescent.TheEntireSquareSourceSharesTheFullDetailReserve`).
    For odd powers of exponent at least three, the mixed and pure-detail blocks combine into
    $P_{\rm odd}(f)-P_{\rm odd}(g)=\sum_mw_m\operatorname{Re}\langle T_mh,f\rangle$.
    A fixed detail head makes this entire difference Gamma-small; jointly with the full even-power
    source it has uniform negative dimension at most $A+1$
    (`ArithmeticIndexDescent.OddHigherPrimePowersPayTheirWholeDetailBlock`). The paid form retains
    a positive multiple of coarse Gamma plus weighted detail mass after a fixed head
    (`exists_squareOddHigherRefinement_coarse_detail_reserve`). Beyond the
    joint whole-square payment, coarse first-prime and odd higher-power
    sources, coarse archimedean mass and first-prime mixing remain open.
    Finite heads, the sinh coordinate and the ordinary mean still cost
    negative directions. Standalone source estimates cannot be added when
    their Gamma reserves overlap.
    The entire prime–polar residual also satisfies
    $|\operatorname{primeSum}(f)-P(f)|\le\varepsilon e^R(\Gamma(f)+\int f^2)$
    for all sufficiently large $R$, uniformly over every real BV profile
    supported in $[-R,R]$
    (`ArithmeticIndexDescent.TheFullPrimePolarSourceCancelsInGammaNorm`).
    This removes the derivative-norm restriction while retaining all prime
    powers and both pole moments. The aperture factor remains, so the estimate
    does not settle the unpaid signs or finite index costs above.
17. **Finite readings cannot supply Bézout**: Weil Rayleigh quotients are unbounded in every
    finite-reading kernel; arithmetic majorants give Bézout + ampleness but break RR.
18. **Hecke–Lefschetz rigidity.** Hecke correspondences are isometries; RH ⇔ $T_2$ maps the open positive
    cone into the ample half-space; Rosati source cone has RR exactly on unitary data.

### Meyer source carrier
19. **Poisson principal cycles** are invisible to every intersection reading; origin mass is
    flow-invariant but does not bound the Weil trace; Poisson boundaries are dense in origin $L^2$, so
    continuous class readings are constant.
20. **Meyer surfaces.** Linear trace degree gives graded RR unconditionally; Bézout, ampleness,
    additive closure ⇔ RH; numerical = principal ⇔ Xi simplicity. The bounded-orbit carrier (critical
    highest jets) has RR, Bézout, ampleness unconditionally.
21. **Maximal blind ideal.** Sources whose Mellin transform vanishes at every off-line Xi zero form the
    **unique maximal sharp-stable convolution ideal with nonnegative trace**: single-channel positivity
    is exhausted by off-line blindness.
22. **Harmonic coupling and the Fejér barrier.** Escaping blindness needs coupled dilated channels;
    nonnegative cosine polynomials obey $a_1<2a_0$, which yields exactly the classical zero-free region.
23. **Faithful degrees.** Positive faithful degree ⇔ RH + simplicity ⇔ arithmetic sharp = Hilbert
    adjoint; algebraic characters are Xi evaluations; positive degrees see only reduced critical jets;
    finite Xi packets split positive energy with a nonnegative residual (vanishing open).

### Odd ledger, sections, Gram certificates
24. **Degree floor = width**: floor rate sets are exactly $[\text{width},\infty)$ (Sobolev normalisation);
    over $\mathbb F_q$ the $L^2$ floor rate is twice the width. All-parity critical-deficit identity
    $\hat Z(F)=(\Omega(0)-2)\|F\|^2+\text{Lévy}+4J(F)+2\int_0^{2A}I\,Da_F$.
25. **Section counts.** Polar box DoF − prime node count $=E(s)$; rank counts are reweighting-invariant
    (not selective), Frobenius norms separate $\Lambda$ from the shifted pair.
26. **Infinite genus.** Over $\mathbb F_q$ the radical is the Frobenius ideal; over $\mathbb Q$ the near radical has
    two-sided Landau–Widom count $(2\mp\eta)e^{2L}$.
27. **Rank–trace inertia.** The normalized rank–trace inequality certifies $(2-\kappa)N$ simple
    fixed-label mass without pairwise orthogonality. Coordinate examples prove sharpness among all
    normalized abstract blocks, not within the prescribed arithmetic evaluation family. Full Gram
    coalescence also holds for arbitrary real vectors (`CoalescenceDoesNotRequireOrthogonality`).
    The studied sub-threshold profiles exceed $2/3$; the $3/4$ criteria require spectral slack or surplus (TTPC).
28. **Which data force the sign over $\mathbb F_q$**: Rosati invariance ⇔ pole-subtracted Hasse–Weil ⇔
    forward light-cone Bézout; genus one: Hasse = degree positivity of $\mathbb Z[F]$, which Hecke scales lack.

---

## 5. Pillar theorems

1. **Scaling Hodge index = RH; signature and Pontryagin laws** (`scalingSurface_hodgeIndex_iff`,
   `riemannHypothesis_iff_one_positive_square`, `pontryagin_law`).
2. **Calibration and fakes** (`hodgeIndexOnSpan_iff_unitary`, `goldenDatum_negIndex_spanGram`).
3. **Degree filtration, finite for $\zeta$** (`hodgeDefectAt_zeta_le_shannon`).
4. **Tower laws** (`tower_law`, `zeta_one_prime_tower_law`, `zeta_lefschetz_growth_law`,
   `exists_symmetric_wolff_toeplitz_blind_configuration`).
5. **Effectivity ⇔ Hodge; Bézout holds** (`exists_effectivity_iff_hodgeIndex`, `localPair_nonneg`).
6. **Source-cone laws; universal floor law** (`gradedSourceCone_riemannRoch_iff_le_defect`,
   `zetaZeroWidth_le_iff_gradedSobolevSourceCone_riemannRoch`,
   `riemannRoch_iff_openPositiveCone_subset_and_defect_nonneg`).
7. **Degree floor = width** (`fullDefectFloorRates_eq_Ici`).
8. **Near-radical law** (`zeta_landau_widom_two_sided_dimension_law`).
9. **Gram certification** (`universal_gram_certification_classification`).
10. **Meyer carrier**: maximal blind ideal, faithful degrees (modules `MaximalBlindIdealOfTheMeyerSource`,
    `FaithfulPositiveMeyerDegrees`, `HarmonicCouplingForcesSourceBlindness`).
11. **Haar-cell effectivity** (module `HaarCellEffectivity`, `HaarCellSmoothEffectivity`).

---

## 6. Traps

| Trap | Truth |
|---|---|
| Adjunction is missing | It is exact; Riemann–Roch is missing |
| Span data force Hodge index | Fake data satisfy them all and fail |
| Positive tests are effective | Bézout yes, RR no |
| `riemannHypothesis_iff_exists_effectivity` is progress | Progress = effectivity defined without the sign |
| A source-defined cone escapes the estimate | Its RR is exactly a coercive floor |
| Subexponential floor is a reduction | Equivalent to RH; power savings are strips |
| Odd ledger is a positivity mechanism | It is the explicit formula rewritten |
| One fixed test sees the whole tower | Only off a wall; over all tests yes |
| Multiplicities count | The defect counts distinct right zeros |
| Finitely many readings plus mass give Bézout | Rayleigh quotients unbounded in every finite kernel |
| A bigger arithmetic reserve helps | Gives Bézout, kills RR |
| Single-channel positivity beyond the blind ideal | Needs harmonic coupling, which hits the Fejér barrier |
| Short-window positivity settles RH | Windows $\le3/10$ are positive; the Lefschetz bound on short cycles is all of RH |
| Section effectivity on narrow/Haar spans is full effectivity | Support/span restrictions remain; mixed coarse–detail payment open |
| Rank-based section counts are selective | Reweighting-invariant; use norms or $E(s)$ |

---

## 7. Open problems

1. **Riemann–Roch for $\mathbb Z$.** Close the low-frequency directions read by $D_a$ and the pole, at every
   degree, by an effectivity defined without the sign of the form.
2. **An arithmetic section law.** A source-defined cone whose RR follows from a law of its sections
   (count, vanishing) rather than the floor, reducing over $\mathbb F_q$ to Weil's.
3. **Full mixed payment on complete cells.** Extend Haar-cell effectivity to the coarse (pair-average)
   level and the mixed coarse–detail terms, i.e. full-source effectivity.
4. **Degree floor below rate ½** (= strip): which effectivity input lowers the rate before the sign?
5. **One fixed test across a wall**: an infinite defect carried by one test over an uncountable folded
   spectrum (tool: light Blaschke walls are permeable, `HTGeometry`).
6. **One-prime Lefschetz bound on short cycles**: the whole remaining content of Hodge index.
7. **Clustering branch** of the visibility/defect-rate dichotomy (unrestricted $L^2$).
8. **Beyond the maximal blind ideal**: a harmonic-coupled positivity mechanism passing $a_1<2a_0$ on a
   sharp-stable carrier containing off-line-visible sources.
9. **Meyer packet residual**: vanishing of the residual in the finite-projector energy split.
10. **Beyond 2/3 simple zeros** (owned by TTPC).

## 8. Tools to build

An effectivity with ampleness proved without the sign; a section law; mixed coarse–detail payment
on complete cells; a short-cycle Lefschetz estimate at one prime.

## 9. Principles

Success: an effectivity whose ampleness is proved without the sign of the form and which satisfies
RR, or a proof that no cone from a stated class of arithmetic data has both. A contribution names the
Weil ingredient it concerns, states what it gives for fake data, non-$\Lambda$ weights and positive
tests, runs first over $\mathbb F_q$, and records the positive survivor of every no-go. Compute, then
bound; fix the source ($\Lambda$, pole weight one), not the sign; separate metrology (what a degree sees)
from geometry (what a cycle is); a reformulation is not a reduction.
