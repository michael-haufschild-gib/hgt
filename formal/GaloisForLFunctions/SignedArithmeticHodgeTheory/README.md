# Signed Arithmetic Hodge Theory

**Central question.** How can arithmetic incidence, archimedean energy and the two polar
coordinates jointly control the index of the actual Weil form under source exhaustion?

Signed arithmetic Hodge theory with source-compatible renormalization studies this question on
the original arithmetic source. Its purpose is to turn positive arithmetic sections into
quantitative control of their mixed interactions and complement. A positive section alone does
not orient the complete form. A renormalized prime spectrum alone does not recover the
archimedean term or the poles.

Namespace: `GaloisForLFunctions.SignedArithmeticHodgeTheory`.
Umbrella: `SignedArithmeticHodgeTheory.lean`.

## Motivation

Three constructions supply concrete starting points.

* Balanced logarithmic Haar sections have a full rough-Weil lower bound above a fixed lower
  index, uniformly in the upper horizon. They leave coarse directions and interactions between
  scales.
* Narrow arithmetic sections admit a bounded Weil-orthogonal projection in the complete source
  graph. Their complement contains an infinite null radical. Its nonnegativity is open; a strict
  lower bound on the whole complement is false.
* Ramanujan profiles give actual prime-matrix quasimodes and distinct spectral points for each
  fixed finite conductor packet. One explicit Gram budget controls arbitrary finite conductor
  families, and one horizon-independent constant controls their prime residuals with explicit
  conductor cost. Bounded renormalized prime-energy sets admit uniform finite Ramanujan approximation.
  Comparison with the full source graph, Gamma and both poles remains a separate requirement.

There is also a canonical nonnegative critical source energy. Its finiteness detects finite
off-line support; its sharp smallness threshold detects RH. Known index costs bound it from
below. An arithmetic upper bound is a separate missing result.

These are connected problems, not interchangeable criteria. This programme must produce new
estimates on their shared source and explicit interfaces between their different forms.

## Objects and language

Every comparison specifies five pieces: **source, form, domain, exhaustion and error currency**.

| Object | Mathematical content |
|---|---|
| Arithmetic source | Real compactly supported logarithmic tests, their complete source-graph closure, and explicitly embedded finite cell or class spaces |
| Signed form | The complete symmetric Weil pairing, with its prime, Gamma, mass and two-pole terms retained |
| Paid section | A source-defined subspace on which a proved coercive estimate supplies a bounded Weil projection |
| Residual | The original source minus that projection, with the induced signed form |
| Radical | Vectors pairing to zero with every source vector; these may have nonzero graph norm |
| Mixed charge | The bilinear interaction between chosen source blocks, measured in a stated norm |
| Reserve | A proved positive term available once in a joint estimate |
| Renormalization | An explicit counterterm subtraction on an identified domain, accompanied by convergence and error estimates |
| Modal source | Actual Ramanujan profiles in the prime matrix, with Gram, residual, pole and complementary errors |
| Critical energy | The canonical extended-real limit of quadratic-scale source work, including off-line/critical exterior pairs |

A morphism is a specified linear source map together with proved formulas for its mixed-form and
polar defects. Form preservation must be proved. No interface field may assume the sign, the
missing complement bound or an unproved arithmetic estimate.

“Hodge” refers to signed orthogonal decomposition, index and the arithmetic source of a sign.
It does not assert the existence of a new cohomology theory or a positive polarization.
“Source-compatible” means that the actual test functions, their poles and their mixed pairings
survive every comparison. “Renormalized” does not mean that an unpaid divergent term is discarded.

The form attached to a radical matters. The CHMD signed-source radical can be removed while
retaining both polar moments. The resulting full Weil form still has a two-dimensional polar
radical, spanned by the ground and odd polar classes. Quotienting this larger radical preserves
the Weil pairing but discards nonzero polar coordinates unless they are stored separately.
[CHMDQuotientWeilForm](../RHTower/CHMDQuotientWeilForm.lean) proves this distinction and the exact
two-pole classification. Here `arithmeticWeilRadical` always refers to the full Weil form.

## Mechanisms and pillar theorems

### Exact residual calculus

For a proved positive section with Weil projection \(P\), write \(R=1-P\). The basic identity is

\[
 W(x,y)=W(Px,Py)+W(Rx,Ry).
\]

The programme supplies a quantitative trial-correction theorem on the actual unbounded carrier
\(K\). Let \(T_W\) be the original graph Weil operator and
\(J=\Pi_K T_W\), where \(\Pi_K\) is graph-orthogonal projection. For every source \(x\) and
every trial correction \(u\in K\),

\[
\begin{aligned}
 W(x-u)&=W(Rx)+W(Px-u),\\
 \|Px-u\|&\le2\|J(x-u)\|,\\
 W(x-u)-2\|J(x-u)\|^2
 &\le W(Rx)
 \le W(x-u)-\tfrac12\|Px-u\|^2.
\end{aligned}
\]

Equality \(W(x-u)=W(Rx)\) holds exactly when \(u=Px\). For two independent sources and trials,

\[
 |W(x-u,y-v)-W(Rx,Ry)|
 \le2\|J(x-u)\|\,\|J(y-v)\|.
\]

[TheArithmeticSchurComplementHasCertifiedErrorBounds](TheArithmeticSchurComplementHasCertifiedErrorBounds.lean)
proves these statements without a sign premise on the residual. The constants are independent
of aperture and profile count. Restricting \(T_W\) to the carrier charges only the interaction
that the correction must remove. The error estimate is quadratic in stationarity, while the
graph error is linear.

These are certified comparison tools. They do not bound stationarity on a new exhaustive
arithmetic family or prove nonnegativity of the exact complement.

### One budget for a complete coefficient family

Let \(F:E\to H\) be a bounded source family on a real normed coefficient space, and let
\(U:E\to K\) be its bounded trial correction. The single stationarity operator is
\(D=J(F-U)\). For every coefficient vector \(c\),

\[
0\le W(Fc-Uc)-W(RFc)\le2\|D\|^2\|c\|^2,
\qquad
\|PFc-Uc\|\le2\|D\|\|c\|.
\]

For any two coefficient vectors,

\[
|W(Fc-Uc,Fd-Ud)-W(RFc,RFd)|
\le2\|D\|^2\|c\|\|d\|.
\]

[OneStationarityBudgetControlsTheWholeSourceFamily](OneStationarityBudgetControlsTheWholeSourceFamily.lean)
proves these simultaneous estimates. They apply before a choice of entries or blocks, so a
shared reserve is charged once through the operator norm. The arithmetic task is to construct
an exhaustive family and corrections for which this norm is sufficiently small; the estimates
do not assume or supply that smallness.

### Exact radical retention

The arithmetic complement is \(\ker P=\ker J\). Its bilinear radical, viewed inside the
original graph, is exactly \(\ker T_W\): restricting to the complement creates no new radical.
For \(z\in\ker T_W\),

\[
P(x+z)=Px,\qquad R(x+z)=Rx+z.
\]

[TheSignedComplementRetainsExactlyTheWeilRadical](TheSignedComplementRetainsExactlyTheWeilRadical.lean)
proves these identities and retains the actual infinite independent theta family in the
residual. The positive carrier has no radical, so all full-form null information stays in the
complement. Neither the kernel description nor radical removal determines its remaining sign.

### Scale growth and scalar renormalization

For a nonzero compact real source \(f\), let \(x_t\) be the original graph lift of
\(f(\,\cdot-t)\). The complete Weil value is translation invariant. The two pole moments
scale by \(e^{t/2}\) and \(e^{-t/2}\), respectively; these are established identities of the
arithmetic scaling surface. Graph size behaves differently. For every \(B\ge0\), there is
\(c_{f,B}>0\) such that

\[
c_{f,B}e^{B|t|}\le\|x_t\|^2\qquad(t\in\mathbb R).
\]

The proof uses the literal source weight \(\cosh(u/2)/\Phi(u)\) and theta decay at every
exponential rate. Compact support supplies \(|u|\ge|t|-R_f\) wherever the translated source
is nonzero. No positivity of \(W(f)\) is required.

The growth also survives removal of the paid section. With \(C_W\) the bounded Weil-pairing
constant, every graph vector satisfies

\[
\|x\|^2\le4W(x)+(4C_W+2)\|Rx\|^2.
\]

Consequently, \(c_{f,B}e^{B|t|}-4W(f)\le(4C_W+2)\|Rx_t\|^2\), and each nonzero compact
translation orbit eventually lies outside the fixed coercive carrier.

Every scalar amplitude \(a\) satisfies the stronger joint estimate

\[
c_{f,B}e^{B|t|}\,|W(a x_t)|\le |W(f)|\,\|a x_t\|^2.
\]

Thus scalar normalization cannot retain both a bounded original graph norm and a nonzero
Weil energy along an escaping orbit. Even multiplication by any fixed exponential
\(e^{-a|t|}\) leaves an exponentially growing graph norm.
[TranslationPreservesWeilEnergyButEscapesEveryExponentialGraphBound](TranslationPreservesWeilEnergyButEscapesEveryExponentialGraphBound.lean)
proves the quantitative bounds. They concern the original graph topology; they do not rule
out every form-preserving quotient or a different topology with separately proved source and
pole comparisons. They also do not assert that each individual fixed translation lacks a
bounded extension on the whole graph.

### Transport on bounded source windows

The positive replacement keeps aperture and translation range explicit. For fixed \(R,T\ge0\),
there is \(C\ge1\), uniform over all compact source profiles supported in \([-R,R]\) and all
\(|t|\le T\), such that

\[
\|x_t\|^2\le C\|x_0\|^2,
\qquad
\|x_0\|^2\le C\|x_t\|^2.
\]

[BoundedWindowsAdmitSourceCompatibleScaleTransport](BoundedWindowsAdmitSourceCompatibleScaleTransport.lean)
proves both bounds. The upper estimate uses a maximum of the exact theta mass weight on the
enlarged aperture, the bounded full Weil pairing and a global ordinary-mass bound in the
graph norm. Applying that estimate to inverse translation gives the lower bound.

This supplies a faithful local comparison for arbitrary profiles, with no sign premise and
no restriction on their two polar moments. Its constants are not uniform as the windows and
translation ranges exhaust the source. A renormalization argument must carry those costs.

### Faithful transport on completed apertures

Let \(H_A\) be the existing graph completion of the smooth source core on aperture \(A>0\).
Literal translation extends to a bounded linear, injective map

\[
T_{A,t}:H_A\longrightarrow H_{A+|t|}\subset H.
\]

For every bounded shift range, the same upper and lower graph bounds hold uniformly on all of
\(H_A\). The map agrees with translation of every smooth test representative and satisfies

\[
\begin{aligned}
W(T_{A,t}p,T_{A,t}q)&=W(p,q),\\
\widehat{T_{A,t}p}(z)&=e^{izt}\widehat p(z)
\quad\text{for }|\operatorname{Im}z|\le\tfrac12.
\end{aligned}
\]

The evaluations at \(-i/2\) and \(i/2\) retain the two pole factors \(e^{t/2}\) and
\(e^{-t/2}\). The construction takes place before any radical quotient.
[CompletedAperturesCarryTheLiteralScaleTransport](CompletedAperturesCarryTheLiteralScaleTransport.lean)
proves these statements by extending the bounded core map along its dense inclusion, then
passing the actual form and readout identities by continuity. It reuses the existing CHMD
aperture spaces. Uniformity under unbounded aperture or translation growth is a separate
arithmetic requirement, constrained by the escape bounds above.

### Signed block payment

For a decomposition \(x=\sum_j x_j+r\), diagonal lower bounds are useful only with a simultaneous
bound for all mixed terms. The target is a source-defined matrix or operator bound whose norm
is smaller than the available diagonal reserve, with explicit treatment of the coarse residual.
Absolute-value estimates are acceptable only when their total cost is affordable.

The first substantive target is a coherent family of Haar and coarse blocks with one Gamma
allocation, both poles and an error uniform in the family size. A complete all-coefficient
nonnegative result would establish the complete Weil sign and therefore RH.

Complete logarithmic cells have a dyadic multiresolution: the cell at index one and the low
details recur along translations by \(\log2\), while high details have a proved full-form floor.
The remaining task includes cross-level interactions and the finite generator orbits.
The corpus supplies a useful one-prime estimate:
[ThePrimeTwoMixedTailIsGammaSmall](../ArithmeticIndexDescent/ThePrimeTwoMixedTailIsGammaSmall.lean)
bounds the high-detail tail of the actual prime-two mixed form by any prescribed positive
fraction of Gamma energy, uniformly in the horizon. Its Gamma energy is evaluated on the
complete source, with all coarse coefficients free. Finitely many detail coordinates therefore
approximate this mixed term. Summing such estimates across primes or levels still requires one
joint reserve allocation; the one-prime estimate does not supply the coarse-generator sign.

### Renormalized adjunction

For conductor \(m\), the actual mode is

\[
 v_m(n)=\frac{c_m(n)}{\sqrt{\phi(m)n}},\qquad
 E_m=\gamma+\log m+\operatorname{tameDifferent}(m).
\]

The prime matrix has trial energy \(\log N-E_m\). Write
\(F_{S,N}a(n)=\sum_{m\in S}a_m v_m(n)\) on \(1\le n\le N\), for any finite set of positive
conductors \(S\). The programme proves the simultaneous estimate

\[
\left|\|F_{S,N}a\|_2^2-\log N\sum_{m\in S}a_m^2\right|
\le\left(1+2\sum_{m\in S}m^2\right)\sum_{m\in S}a_m^2.
\]

With the exact harmonic normalizer \(H_N\), the constant is \(2\sum_{m\in S}m^2\).
[GrowingRamanujanFamiliesHaveAUniformGramBudget](GrowingRamanujanFamiliesHaveAUniformGramBudget.lean)
proves both bounds. Complete-period orthogonality and Abel summation first give the entry
bound \(2ml\). Summing those bounds and applying Cauchy–Schwarz controls every coefficient
vector with one constant. The Gram cost is \((1+2\sum_{m\in S}m^2)/\log N\), with all
family and horizon dependence explicit. For conductors at most \(M\), this cost is
\(O(M^3/\log N)\).

The arithmetic row correction also has an explicit conductor cost. For positive row and
complementary horizon \(n,y\),

\[
\left|\operatorname{corr}_{m,y}(n)
 +(\log m+\operatorname{tameDifferent}(m))u_m(n)\right|
\le\frac{4\sqrt{\phi(m)}\log m}{y},
\qquad u_m(n)=\sqrt n\,v_m(n).
\]

Here \(\operatorname{corr}_{m,y}(n)\) is the literal upward and downward prime-row correction
`poleProfileCorrection` from the exact prime-matrix action.
[TheRamanujanCorrectionHasAnExplicitConductorCost](TheRamanujanCorrectionHasAnExplicitConductorCost.lean)
proves the bound. The reciprocal Mangoldt tail on the powers of a prime \(p\) is at most
\(2\log p/y\). Only conductor primes contribute, and their logarithms sum to at most
\(\log m\). This pays the correction uniformly in every row, without relying on fixed-conductor
tail convergence.

The complete residual admits one shared arithmetic budget. Set

\[
\begin{aligned}
b(y)&=\left|\sum_{t=1}^y\frac{\Lambda(t)}t-\log y+\gamma\right|+\frac1y,\\
B_N&=\sum_{n=1}^N\frac{b(\lfloor N/n\rfloor)^2}{n},\\
C_m&=\sqrt{\phi(m)}(1+4\log m),\\
r_{m,N}&=P_Nv_{m,N}-(\log N-E_m)v_{m,N}.
\end{aligned}
\]

Here \(P_N\) is the literal prime matrix and \(v_{m,N}\) is the profile restricted to
\(1,\ldots,N\). For every finite positive-conductor family and every real coefficient vector,

\[
\left\|\sum_{m\in S}a_m r_{m,N}\right\|_2^2
\le B_N\left(\sum_{m\in S}C_m^2\right)\left(\sum_{m\in S}a_m^2\right),
\qquad \frac{B_N}{\log N}\longrightarrow0.
\]

[OneArithmeticRemainderControlsEveryRamanujanResidual](OneArithmeticRemainderControlsEveryRamanujanResidual.lean)
proves this from the exact prime-row identity, the correction estimate, the square-root totient
bound on normalized modes, and the proved Mertens theorem. The same \(B_N\) applies to every
conductor and coefficient family.

The arithmetic budget is bounded at every horizon: there exists \(B>0\), independent of
\(N,S,a\), such that

\[
B_N\le B,\qquad
\left\|\sum_{m\in S}a_m r_{m,N}\right\|_2^2
\le B\left(\sum_{m\in S}\phi(m)(1+4\log m)^2\right)
       \left(\sum_{m\in S}a_m^2\right).
\]

[TheArithmeticResidualBudgetIsUniformInTheHorizon](TheArithmeticResidualBudgetIsUniformInTheHorizon.lean)
proves this bound. The corpus's global Mertens decay gives \(b(y)\le C/(1+\log y)\).
Exact floor roundoff bounds the corresponding squared profile by twice the Wiener logarithmic
kernel. That kernel is summable and has total mass at most \(1+2\pi^2\), yielding
\(B=2C^2(1+2\pi^2)\). Summability is proved before comparing a finite sum with its infinite sum.

Growing-family control therefore has two explicit costs:
\((1+2\sum m^2)/\log N\) for the Gram matrix and
\(B\sum\phi(m)(1+4\log m)^2/\log N\) for the squared residual.
These budgets measure finite prime-matrix approximation in \(\ell^2\).

On each fixed renormalized prime-energy sublevel, the corpus proves uniform approximation by a
finite Ramanujan span, with any prescribed error.
[TheRenormalizedPrimeEnergyControlsTheDefect](../RenormalizedArithmeticPotentialTheory/TheRenormalizedPrimeEnergyControlsTheDefect.lean)
proves this for the actual horizon matrices. This supplies a prime-side completeness statement
on bounded energy sets. It does not supply uniform constants as the energy window grows or
identify the full continuous source.

A source-compatible comparison must control continuous Gamma, polar images and the full-form
complement on the same growing family. Choosing an arbitrarily slow diagonal sequence from
fixed-mode limits does not establish those comparisons. Distinct spectral labels also require
comparison with the separation of their adjunction energies.

### Critical-work control

The canonical energy satisfies

\[
 R^2\bigl(\mathcal W(2R)-\mathcal W(R)\bigr)
 \longrightarrow\mathcal E_{\mathrm{crit}}\in[0,\infty].
\]

The first target is an upper bound from prime or theta arithmetic retaining the exterior rows.
Finiteness would give finite off-line support. The endpoint
\(\mathcal E_{\mathrm{crit}}\le1294047/2000\) is equivalent to RH.
An index lower bound, a nonnegative pair expansion or monotone convergence supplies no such
upper bound by itself.

## Established foundations in the corpus

These are imported mathematical foundations, not new contributions of this programme.

| Foundation | Source |
|---|---|
| Complete mixed-cell transfer and source-graph projection | [ArithmeticIndexDescent](../ArithmeticIndexDescent/TheUnboundedCellCarrierHasAWeilProjection.lean) |
| High Haar full-form floor | [HaarCellEffectivity](../ArithmeticCastelnuovoSeveri/HaarCellEffectivity.lean) |
| Mean-zero Gamma payment | [GammaMeanZeroCoercivity](../ArithmeticCastelnuovoSeveri/GammaMeanZeroCoercivity.lean) |
| Actual Ramanujan prime quasimodes | [TheRamanujanPoleProfilesArePrimeQuasimodes](../RenormalizedArithmeticPotentialTheory/TheRamanujanPoleProfilesArePrimeQuasimodes.lean) |
| Distinct spectral points for fixed finite conductor packets | [TheFullPrimeMatrixRealizesFiniteAdjunctionPackets](../RenormalizedArithmeticPotentialTheory/TheFullPrimeMatrixRealizesFiniteAdjunctionPackets.lean) |
| Uniform finite Ramanujan approximation on bounded prime-energy sets | [TheRenormalizedPrimeEnergyControlsTheDefect](../RenormalizedArithmeticPotentialTheory/TheRenormalizedPrimeEnergyControlsTheDefect.lean) |
| Prime gap on the harmonic pole hyperplane | [ThePrimeFormHasASpectralGapBelowItsPole](../RenormalizedArithmeticPotentialTheory/ThePrimeFormHasASpectralGapBelowItsPole.lean) |
| Canonical critical source energy | [TheCriticalSourceRateHasACanonicalEnergy](../ArithmeticIndexDescent/TheCriticalSourceRateHasACanonicalEnergy.lean) |
| Source synthesis beyond narrow spacing | [TheSecondOrderSynthesis](../SpacingScaleHarmonicAnalysis/TheSecondOrderSynthesis.lean) |

The trial-correction estimates, whole-family operator bounds, exact radical retention and
quantitative source-scale bounds with faithful completed-aperture transport, and simultaneous
Ramanujan Gram and family-residual budgets are formalized contributions of this programme.
Complete signed block payment, quantitative growing-family schedules with full-form complement and
Gamma/pole transfer, and arithmetic upper control of critical work remain research targets.

## Questions and open topics

1. Can cross-level interactions of the complete-cell multiresolution be paid jointly, leaving
   finitely many \(\log2\)-orbit generators? Can a bounded-index version be proved first?
2. Which twin-selective arithmetic inequality controls those generator orbits with Gamma and
   both poles retained? How far can the discrete prime gap be transferred beyond narrow spacing?
3. Which prime or theta law bounds canonical critical energy above, retaining exterior rows?
   Can it first exclude infinitely many off-line zeros without presupposing their absence?
4. Which enlarging arithmetic corrections make stationarity uniformly small, and which growing
   Ramanujan families control a useful full-source domain? What complement estimate survives
   the Gamma and continuous two-pole comparison?
5. Which counterterms yield convergence in a topology strong enough to preserve mixed Weil
   pairings? How do conductor, class variation and horizon constrain one another?
6. Can selective localization see every possible exceptional ordinate with affordable conductor
   and inverse costs?

These questions include intermediate theorems as well as RH-strength endpoints. A proof of an
intermediate statement must state precisely which endpoint remains open.

## Traps and boundary conditions

* A null vector is not a negative direction. A graph-norm floor cannot hold on a residual that
  contains a nontrivial Weil radical.
* Ordinary mean zero, the discrete harmonic pole constraint and two continuous exponential
  moments are different conditions.
* Shared Gamma reserve cannot be spent separately on every block. Summed estimates must
  account for each source term exactly once.
* Fixed support, fixed conductor and fixed profile variation do not supply uniform growing
  families. Domain escape must be measured.
* Prime-matrix positivity and full Weil positivity concern different forms.
* Nonnegative entries in the critical pair energy do not establish positive semidefiniteness
  of its kernel.
* A sparse positive carrier can be proper. Larger horizons alone do not prove density.
* A diagonal gauge is unavailable in obstructed overlap regimes. Signed block geometry must
  address that obstruction rather than assume it away.
* Generic intersection identities and synthetic positive models do not select the actual
  arithmetic source. Equivalences and definitions cannot provide the missing sign.

## Relation to other programmes

Arithmetic Castelnuovo–Severi supplies the scaling surface and positive arithmetic sections.
Arithmetic Orientation Geometry studies signs along scaling correspondences.
Arithmetic Index Descent supplies complete source domains, projections, index capture and
critical-work costs. Renormalized Arithmetic Potential Theory supplies arithmetic finite parts,
adjunction modes and pole-gap selectivity. Spacing Scale Harmonic Analysis supplies source
synthesis and quantitative overlap estimates. Arithmetic Lorentzian Geometry identifies
constraints on positive gauge and stability mechanisms.

This programme's contribution should be the paid comparison between those objects: exact
residual optimization, coherent signed block estimates, uniform renormalized transfer and
arithmetic upper control. Existing modules remain the owners of their foundational results.

## Success and contribution criteria

A contribution must identify its actual source and prove a new estimate, sharp classification
or structural theorem needed by an estimate. It must preserve the complete relevant form,
state every growing parameter, account for mixed terms and poles, and discharge its arithmetic
inputs. Abstract helper lemmas are useful only when instantiated on the actual arithmetic
objects.

A substantive success answers part of the signed-complement, growing-mode or critical-upper-bound
questions. Full success requires the tools and source-complete forcing mechanisms demanded by
those questions; names, reformulations and conditional wrappers do not meet that standard.

Every claimed proof must be formalized in Lean without added axioms, placeholders, hidden
analytic premises or increased elaboration limits. The final statement and its dependencies,
not its title or intended application, determine what has been proved.
