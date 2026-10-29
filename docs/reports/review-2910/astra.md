# RH research: opportunities, priorities, and the mathematics still missing

29 October 2026

**The best opportunity is a new estimate inside the existing arithmetic framework, not another RH equivalence.** The strongest opening is to turn the recently proved cyclotomic curvature and affine Ramanujan identities into a nonperturbative comparison for the complete overlapping Weil operator. The clearest numerical breakthrough target is the signed prime-pair budget for 75% simple critical zeros. For Quasi-RH, the corpus gives unusually precise targets, including an exact five-sixths detector budget, but does not supply their analytic inputs.

I do not see a credible, completely unrelated RH proof that avoids every existing obstruction. This is a conclusion about the mechanisms examined, not an impossibility claim about future mathematics. Several apparently radical alternatives are already developed, and sometimes sharply obstructed, in this corpus.

## Scope and status

I read the six requested reports and followed `research-programmes.md` from oldest to newest, reading the programme documents it lists. Repeated entries point to current versions, not historical snapshots. The listed ShallowCauchyPrimeEnergy directory has no README; its results were researched through the Lean search tool and source. I used `scripts/formal_tools.py research` for mathematical discovery and inspected the relevant Lean statements. No web research, builds, or proof-integrity audit was performed.

The persistent record is [the research log](../../../logs/astra-rh-research.log); structured corpus-search results are saved beside it as `astra-search-*.json`. An existing version of this report was preserved in `logs/astra-report-before-this-research.txt` before replacement.

Throughout:

- **Established** means a supplied report or an inspected Lean declaration supports the statement. It does not mean I freshly compiled it. The source reports' distinctions between integrated, working, and individually checked results still apply.
- **Receiver** means a proved implication or equivalence whose decisive arithmetic premise remains open.
- **Proposal** means a research target or mathematical inference here, not a newly formalized theorem.

The current frontier includes the optimized overlap certificate, with strict endpoint described below. Some earlier programme summaries still list its predecessor as open. I use the later, more specific result rather than treating those older open lists as the frontier.

## Answers at a glance

| Question | Assessment |
|---|---|
| A new mechanism circumventing a wall? | Yes, a plausible mechanism: cyclotomic positivity of the actual affine overlap correction, transported through the complete operator. The scalar arithmetic ingredients exist; the operator comparison does not. A secondary opportunity is a slower Denjoy–Carleman synthesis schedule. |
| A wildly different, wall-free RH route? | None I can responsibly identify. New terminology, a new positive kernel, or a statistical-mechanics realization would repeat mechanisms already present. |
| Improved Quasi-RH? | Concrete opportunities, no completed improvement. Five-sixths requires a joint improvement of two detector Gram contributions. Three-quarters requires changing an additional part of that detector budget, or using a different source estimate. |
| At least 75% on the line? | The best target is the actual signed coalescent surplus at bandwidth $4/3$, at most $N/18+o(N)$, with the same admissible profiles as the census. It would give 75% **simple** critical zeros. |
| Three priorities? | Complete arithmetic overlap comparison; signed coalescent discrepancy; an independent count producer retaining sublinear, ultimately square-root, precision. |
| A new field? | The required field is already emerging in these programmes. Its missing core is a calculus converting exact arithmetic compatibility into signed inequalities while preserving precision and simultaneous limits. Section 7 gives a concrete specification. |

## 1. What the programme history has established

The programmes form a mathematical progression. Their main achievement is locating where information is lost, then replacing broad obstructions by exact boundaries and positive survivors.

| Stage in the requested sequence | Main advance | What survived as the hard problem |
|---|---|---|
| Arithmetic positivity, BiScaleUncertainty, TransHorizonIncidenceMechanics, Bézout–valuation incidence, criticality and square-root thresholds | Exact energy, aperture, damping, incidence and zero-width dictionaries; sharp thresholds for blind or absolute estimates. | Signed information from the actual Möbius/prime source at the deciding scale. |
| Incidence positivity, continuation and compensation, Castelnuovo–Severi, signed energy incidence, trans-threshold correlation | Completed source identities, geometric and census receivers, precise accounting of poles and mixed terms. | Producing the sign or count that the identities consume. |
| Orientation, local divisor geometry, successor arithmetic, defect rigidity, biarithmetic and positive duality | Arithmetic gauges and successor coupling become explicit; source identification and positive realizations are separated from spectral purity. | Selecting the actual source does not orient its full form. |
| Correlation geometry, Künneth theory, correspondences, polarization, effectivity and conjugate diagonal geometry | Tensor and localization costs; positive collided metric $D$; arithmetic reconstruction of $D$ and the defect separating it from $W$. | Bounding the reflection defect, not merely computing it or finding another positive metric. |
| Selective thresholds, electrostatics, intersection and renormalization | Local tower signs, exact counterterms, survival cones, virial identities, quantized exceptional costs. | Joint payment across places and scales; an upper bound below an exceptional quantum. |
| Spacing analysis, Lorentzian geometry, Gabor pinching, index descent, signed Hodge theory | Spacing-scale payment, genuine census slack, complete-cell index capture, source-compatible projections and substantial joint Gamma/higher-power control. | First-prime interactions, retained coarse/orbit sign and exhaustive overlap. |
| Selective multiscale positivity, counting positivity, Hecke–Krein–Toeplitz and arithmetic Krein–Langer theory | Exact gauge-gap classifications, index/zero/wave laws, finite-stratum structure and appropriate limit topologies. | An arithmetic index ceiling or count; finite index is already Lindelöf-strength. |
| Square-root precision, critical arithmetic correlations, Trans-Metzler positivity | The count's exact perturbation class; where inversion loses precision; conductor-uniform finite arithmetic positivity; full Weil positivity beyond the Metzler boundary. | A nonperturbative signed comparison on a family large enough to decide RH. |

This progression rules out a diagnosis of “we lack the right equivalent formulation.” The receivers are abundant and increasingly faithful. The shortage is an inequality about the original source.

### Three core problems, but several different strengths

The [unification ledger](route-unification-ledger.md) distinguishes endpoint equivalence from a proved source transfer. That distinction should govern research allocation. Saying that two statements both imply RH does not transfer an estimate between their norms, profiles, or growing parameters.

The three core families remain:

1. **Selective arithmetic cancellation:** a sufficiently precise signed estimate involving $\Lambda$, $\mu$, or a source constructed from them.
2. **Complete-form comparison and exhaustion:** preserve Gamma, both poles, every mixed block and the required limit while transporting that estimate.
3. **Independent production:** an arithmetic construction that supplies the estimate without placing it in an assumption or an equivalent definition.

These are not three independent tasks in every proof. A direct count producer could avoid most atomic operator analysis. A complete source positivity construction could avoid extracting a pointwise Chebyshev bound until the end. Their common endpoint does not force identical proof mechanisms.

Several distinctions prevent overstrengthening the research problem:

- A proportion theorem tolerates exceptions. A fixed strip excludes every zero beyond a specified depth. Finite index says all sufficiently high zeros are critical. RH excludes every off-line zero. These targets are not interchangeable.
- The count tolerates a nontrivial perturbation class; full Weil positivity does not.
- A fixed generator on a prime tower can alias. Positivity for **all generators** on a fixed prime tower is a much stronger statement and already decides RH. “Two primes are always necessary” is too broad.
- “An auxiliary must vanish at primes” identifies the point-side obligation of a Stepanov-style construction. The compressor obstructions do not prove that every conceivable RH proof must take that form.

### A particularly useful correction: count precision is not coefficient rigidity

Let
$$
\mathcal Q=\left\{\delta:\sum_{n\le x}\delta(n)=O(\sqrt{x}\log^2x)\right\}.
$$
The corpus proves that `Count(a)` is exactly $a-1\in\mathcal Q$. At a weight already satisfying Count, its additive stabilizer is $\mathcal Q$. In contrast, all-generator tower positivity at $\Lambda+\delta$ holds exactly when RH holds and $\delta(n)=0$ for $n\ge2$.

Thus $\Lambda+1/n$ has Count iff RH, but is never tower-positive. Finite prime flips likewise need not be rejected by a count-level sufficient condition. They must be rejected by a claim of full positivity for the perturbed weight. This is an actual distinction in [TowerPositivityIsPrecisionExact](../../../formal/GaloisForLFunctions/ArithmeticOfSquareRootPrecision/TowerPositivityIsPrecisionExact.lean), especially `count_and_not_towerIndexZero_add_inv`.

**Research consequence:** a count route should work modulo its permissible error class. Demanding exact source selection from it imposes a harder problem than its endpoint requires. Conversely, a positivity route cannot import that tolerance without a proved bridge.

## 2. Opportunities to circumvent or break a wall

### 2.1 One supposed barrier has already been bypassed

The complete Weil form can be positive where no unimodular gauge makes the atomic Markov form Metzler. This is a significant conceptual result: a failed positive-basis mechanism did not obstruct the sign of the original form.

For the explicit plateau $\varphi_0=\mathrm{plateau}(1/1000)$, the original theorem reaches $c=1+10^{-18}$, while the current optimized certificate proves eventual positive definiteness at every fixed
$$
c=1+\delta,\qquad 0\le\delta<\delta_*=\frac1{107520002048050000},
$$
in addition to the regime $0<c\le1$. The optimized asymptotic floor is
$$
\frac1{25}-2000\delta\bigl(1+1024000(2100000+1/25)\bigr).
$$
The endpoint $\delta_*$ is a boundary of this certificate, not a proved spectral transition and not an asserted positive endpoint. See `eventually_completeWeilMatrix_posDef_certified` in [OptimizedTransMetzlerFloor](../../../formal/GaloisForLFunctions/TransMetzlerWeilPositivity/OptimizedTransMetzlerFloor.lean).

Here $c=Nw$; the exact spacing ratio is $w/\log(1+1/N)$, asymptotic to $c$. Keeping these parameters distinct matters at touching.

The mechanism is a joint use of the completed low-mode floor and a strict-variance prime-defect reserve. It retains the poles. The Liouville twin fails in part of this same range. Therefore an older statement that all proved complete-form positivity is twin-blind is no longer accurate.

Improving $10^{-18}$ to $\delta_*$ improves a certificate. Moving to a macroscopic ratio, such as $3/2$, would require mathematical control that the present perturbative argument does not provide.

### 2.2 Main opportunity: cyclotomic positivity of the affine overlap operator

**Proposal.** Derive the complete low-energy operator at a fixed macroscopic overlap from its exact arithmetic successor shells, and use cyclotomic norm positivity before taking absolute values. This extends CACT and Trans-Metzler; it is not a newly discovered independent route.

Three recent ingredients make this more concrete than a request for “better cancellation.”

**First, a uniform arithmetic positive quantity already exists.** For $m>1$, put
$$
P_m(k)=\sum_{\zeta\text{ primitive }m\text{-th root}}\left|\sum_{j=0}^{k-1}\zeta^j\right|^2,
$$
$$
A_m(t)=\sum_{d\mid m}\mu(m/d)d^2\{t/d\}(1-\{t/d\}).
$$
The corpus proves
$$
A_m(k+u)=(1-u)P_m(k)+uP_m(k+1),\qquad 0\le u<1,
$$
and
$$
\frac{A_m(t)}{\varphi(m)}\ge\{t\}(1-\{t\})\ge0.
$$
The crucial input is an actual nonzero cyclotomic integer: its norm has magnitude at least one. This gives $P_m(k)\ge\varphi(m)$ when $m\nmid k$. The lower bound is uniform in conductor, not a fixed-mode limit. See [CyclotomicNormGivesAConductorUniformCurvatureFloor](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/CyclotomicNormGivesAConductorUniformCurvatureFloor.lean), `fract_quadratic_le_normalized_arithmeticOverlapCurvature`.

**Second, the affine averaging rule is realized by actual primes.** For fixed $q,n,h,A,B$, $q,A>0$, $A\le B$, the corpus proves
$$
\sum_{AN<k\le BN}\frac{\Lambda(k)}k c_q(kn+h)
\longrightarrow
(\log B-\log A)\frac{c_q(n)c_q(h)}{\varphi(q)}.
$$
This is `tendsto_affineRamanujanPrimeWindow` in [ActualPrimeWindowsDiagonalizeAffineRamanujanModes](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/ActualPrimeWindowsDiagonalizeAffineRamanujanModes.lean). It supplies the arithmetic eigenvalue of an affine successor average. It does **not** yet supply a norm estimate when conductor, lag and coefficients vary together.

**Third, growing conductor packets now have useful frame bounds.** On $\lparen A,2A]$, for $A\ge4Q(Q-1)$, the actual packet
$$
F_a(n)=\sum_{m\le Q}a_m\frac{c_m(n)}{\sqrt{\varphi(m)n}}
$$
has square mass between $\frac14\sum a_m^2$ and $\frac54\sum a_m^2$. But the same source proves that the literal prime kernel compressed to one such annulus is zero: no two distinct integers there divide one another. The arithmetic transport lives **between** annuli. See [AnnularRamanujanFamiliesHaveTwoSidedFrames](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/AnnularRamanujanFamiliesHaveTwoSidedFrames.lean).

These results suggest the following specific mechanism:

1. Organize non-ratio terms by $kn-j=r$, retaining the sign, boundary terms and actual overlap Gram. For fixed bounded overlap, only finitely many integer successor shells occur, once boundary conventions are included.
2. Compute their action on Ramanujan packets using affine unit averages and the exact logarithmic divisor correction. Combine prime, Robin, Gamma and pole contributions **before** estimating the remainder.
3. Identify whether the resulting completed symbol contains an integral of $A_m(t)/\varphi(m)$ with nonnegative weight. This identification is an open theorem, not a consequence of the displayed scalar positivity.
4. Treat cross-conductor and cross-annulus interactions as part of one operator. If a paid block is $D>0$, the remaining form is $A-BD^{-1}B^*$, not $A$. A scalar positive symbol cannot pay an uncontrolled Schur subtraction.
5. Prove a complement estimate and a norm residual on the actual source, uniform over the packet needed at that overlap. Only then infer a full-matrix lower bound.

The first meaningful endpoint would be one explicit, fixed, full-support profile at $c=3/2$, or another macroscopic ratio beyond the present range, with all coefficient vectors controlled. A profile whose effective width shrinks while its nominal support grows would not answer this question.

Why this could circumvent a wall: the sign would come from exact algebraic cancellation and an integer norm, rather than an entrywise Metzler gauge or absolute payment of every prime edge. Why it may fail: the cyclotomic positive quantity may describe only a diagonal compression, or the actual off-diagonal/complement cost may consume its entire reserve. Either failure should yield an explicit residual operator or sharp obstruction, not another unnamed “error.”

A further useful test is a remote prime flip $\omega_p$, $p\ge11$. Such flips attain the same maximal discrete gap $2\log2$ as zeta. Their bounded-overlap behaviour is therefore a better diagnostic than repeating the Liouville test. Failure to separate a remote flip at one fixed ratio would not refute the local theorem; it would reveal the scale at which its information becomes insufficient.

### 2.3 A smaller but tractable opportunity: improve the synthesis schedule

The established RH receiver uses one Steklov profile and
$$
c_N=(\log\log N)(\log\log\log N)^\beta,\qquad\beta>2.
$$
This is [SuperGevreyCriticalGrowth](../../../formal/GaloisForLFunctions/TransMetzlerWeilPositivity/SuperGevreyCriticalGrowth.lean), `riemannHypothesis_iff_steklovDCProfile_nonneg_superGevrey`.

**Proposal, not a proved extension:** construct a profile from summable radii of the shape
$$
a_m\asymp\frac1{m\log m(\log\log m)^{1+\eta}},\qquad\eta>0,
$$
with harmless shifts at small $m$. The expected derivative bound has the form
$$
\|\varphi^{(q)}\|_1\le C^{q+1}q!(\log q)^q(\log\log q)^{(1+\eta)q}.
$$
Optimizing the differentiation order suggests Fourier/synthesis decay governed by
$$
\exp\left[-c\frac{R}{\log R(\log\log R)^{1+\eta}}\right].
$$
Writing $L=\log\log N$, this points to schedules
$$
c_N=L\log L(\log\log L)^\beta,\qquad\beta>1+\eta.
$$
This is a proposed adaptation of the current construction. The derivative estimates, optimized remainder and continuity in the complete Weil norm all need proof. The existing quasi-analytic obstruction remains; this does not predict bounded-overlap synthesis.

Its value is to reduce the amount of overlap a future arithmetic estimate must handle. It supplies no positivity. There is also a profile obligation: positivity is currently proved for a plateau, whereas the sharp receiver uses a different Steklov profile. A schedule improvement must either use a compatible profile or include a signed transfer between the profiles.

### 2.4 What would not break the main wall

A better scalar overlap constant, another width/index equivalence, or a new source reconstruction identity can be useful without supplying the missing estimate. In particular:

- The impressive nonfirst-source result retains nearly all original Gamma after a fixed detail head, together with the actual cosh and sinh coordinates. It does not pay the complete remaining first-prime source. See `exists_fullPolarNonfirst_completeGamma_reserve` in [TheFullNonfirstSourceRetainsAlmostAllGamma](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheFullNonfirstSourceRetainsAlmostAllGamma.lean).
- Restoring the entire square source adds a genuine advance, but coarse first/odd-higher terms, coarse mass, first-prime mixing and head/moment costs still need joint payment. “Only first powers remain” is a useful slogan only after the exact residual is specified.
- A finite number of retained Haar generators still has infinitely many translation levels. Finite-head approximation is not finite-dimensional compactness.
- A uniform finite index of the **complete** form would imply finite off-line support, hence RH above a height and Lindelöf. It is a major theorem, not an inexpensive intermediate target.
- Fixed-$c$ eventual positivity, even if proved separately for every $c$, does not automatically imply positivity along a prescribed growing $c_N$. The horizon may grow too fast. Nor is bounded-overlap completeness currently established.

## 3. Is there a wildly different route avoiding the existing walls?

**I do not currently see one with a concrete, independently justified producer.** The corpus is broad enough that many suggestions which sound unconventional are repetitions.

For example, I searched specifically for Lee–Yang/Ising constructions rather than treating them as a new statistical-mechanics route. The corpus already contains graph constructions, phase-centered receivers and restrictions on their possible limits. It proves that constant-normalized ferromagnetic graph partition functions of the stated class cannot converge locally uniformly to a zero-free entire factor times Xi. Integer-anchored field frequencies face a separate obstruction. Balanced/phase-centered constructions retain a receiver, with convergence unproved. See [IsingGraphCenteringLaw](../../../formal/GaloisForLFunctions/RHTower/IsingGraphCenteringLaw.lean) and [LeeYangIsingGraphDatum](../../../formal/GaloisForLFunctions/RHTower/LeeYangIsingGraphDatum.lean).

Even the softer proposal “prove ferromagnetic inequalities for Riemann's measure, then infer Lee–Yang” is addressed. The smoothable model
$$
Z(t)=1+\frac34\cos t
$$
satisfies the stated GHS and fourth-cumulant inequalities but has nonreal zeros. Thus these inequalities do not provide real-rootedness. See [FerromagneticInequalitiesLeeYangBlind](../../../formal/GaloisForLFunctions/RHTower/FerromagneticInequalitiesLeeYangBlind.lean). This does not prohibit every statistical-mechanics construction; it prevents calling an already obstructed class a new answer.

Likewise, generic positive operators, determinant identities, heat monotonicity, tensor amplification, source rigidity, and infinite-symmetry continuation have already been separated from the arithmetic assertion that would make them decide RH. In the positive-genus affine-Eisenstein direction, pole detection is now exact even for impure curve data. The missing confinement input is substantive; continuation does not supply it.

The most useful radical change of viewpoint would be **to construct a count without first constructing a positive Weil realization**. But that is the independent-producer direction already recognized by ASRP, effectivity and AKL. Its unanswered content is specific: an identity or auxiliary construction whose analytic extraction retains the cancellation lost by absolute estimates and Möbius inversion. Merely saying “a characteristic-zero Frobenius” adds no mechanism.

A new idea deserves a separate route when it provides at least one of the following:

- a source-built inequality unavailable to current methods, with a proved transfer to the target;
- a new invariant whose value is computed from arithmetic and forces the sign;
- a faithful approximation by independently signed objects, with the required complete-form convergence proved.

A novel object with its deciding property still assumed is a candidate, not a new proof mechanism. Conversely, none of the scoped no-go theorems rules out an unknown construction outside its hypotheses. Trans-Metzler positivity is the existing example of that distinction working productively.

## 4. Opportunities for improved Quasi-RH

### 4.1 The baseline needs its stated status

The supplied frontier labels the seven-eighths manuscript result **[E]: external claim, not locally validated**. The local intake contains detector ingredients and budget calculations, not a completed zero-free capstone. I therefore use $7/8$ as the requested comparison value, not as an established local premise. This is a status distinction, not an attempted verification of the external proof.

Let
$$
\Theta=\sup\{\operatorname{Re}\rho:\xi(\rho)=0\}.
$$
A proof of $\Theta\le\theta<7/8$ would improve the requested strip, giving $1-\theta\le\operatorname{Re}\rho\le\theta$. Endpoint nonvanishing is a separate matter if one wants strict inequalities at exactly $1-\theta,\theta$.

### 4.2 Exact arithmetic targets already available

Define the actual boundary-free sum and its cumulative energy by
$$
S(M)=\sum_{2\le n<M}\frac{\psi(n)-n}{\sqrt n},\qquad
\mathcal E(N)=\sum_{2\le M\le N}\left(\frac{S(M)}M\right)^2.
$$
These are `chebyshevNormalizedCesaroSum` and `chebyshevNormalizedCesaroMeanSquareEnergy`. The exact abscissa law identifies the infimum of admissible energy exponents with $2\Theta$.

| Desired closed strip | Sufficient one-sided bound | Equivalent energy target, for every $\varepsilon>0$ | Escaped Möbius saving |
|---|---|---|---|
| $[1/8,7/8]$ | $S(M)/M\ll1+M^{3/8}$ | $\mathcal E(N)\ll_\varepsilon N^{7/4+\varepsilon}$ | exponent $1/8$, up to $\varepsilon$ |
| $[1/6,5/6]$ | $S(M)/M\ll1+M^{1/3}$ | $\mathcal E(N)\ll_\varepsilon N^{5/3+\varepsilon}$ | exponent $1/6$, up to $\varepsilon$ |
| $[1/4,3/4]$ | $S(M)/M\ll1+M^{1/4}$ | $\mathcal E(N)\ll_\varepsilon N^{3/2+\varepsilon}$ | exponent $1/4$, up to $\varepsilon$ |
| Critical line | a corresponding critical receiver | $\mathcal E(N)\ll_\varepsilon N^{1+\varepsilon}$ | exponent $1/2$, up to $\varepsilon$ |

The $5/6$ and $3/4$ one-sided implications even allow sampling on a fixed power mesh $M=j^m$, $m\ge1$. They remain all-scale arithmetic estimates on that mesh, not finite checks. See [QuasiRHNormalizedChebyshevCesaroAndMertensActionAbscissaLaw](../../../formal/GaloisForLFunctions/RHTower/QuasiRHNormalizedChebyshevCesaroAndMertensActionAbscissaLaw.lean), especially the two strip implications and the two mean-square equivalences.

The escaped-boundary dictionary is equally precise. For $0<\vartheta\le1/2$, the appropriate $O_\varepsilon(M^{-\vartheta+\varepsilon})$ decay, where $M=(N-b)/a$, is equivalent to $\Theta\le1-\vartheta$. One dyadic multiplier already suffices. Uniform decay measured in $N$ over every multiplier is false; the escaped endpoint is the correct scale. See `growingEndpointEscapedMoebiusLaw_tfae` in [MoebiusEscapedPairingBoundaryLaw](../../../formal/GaloisForLFunctions/SelectivePositivityAndThresholdLaws/MoebiusEscapedPairingBoundaryLaw.lean).

These targets show exactly how much power saving buys an improved strip. They do not themselves produce any saving. Nor does improved zero density force extinction of an individual zero: the supplied density envelopes still allow one exception.

### 4.3 The detector budget gives a concrete five-sixths research problem

The strongest numerical guidance comes from two inspected modules:

- [QuasiRHDetectorScaleBudget](../../../formal/GaloisForLFunctions/RHTower/QuasiRHDetectorScaleBudget.lean);
- [QuasiRHDetectorGramTradeoff](../../../formal/GaloisForLFunctions/RHTower/QuasiRHDetectorGramTradeoff.lean).

Their conclusions concern the stated upper-bound model. They are not lower bounds on actual energy and are not zero-free theorems.

Write the Gram profile as
$$
1+P^\nu+\frac{P^\kappa}{Y},\qquad
X=Z^x,\quad Y=Z^{1-s-x},\quad P=Y/X,
$$
where $s$ is total slot length. After principal-signal normalization and the reflected allowance, the boundary is
$$
B(x,s;\nu,\kappa)=\frac56+\frac{x-s}{6}
+\frac12\max\left(0,\nu(1-s-2x),(\kappa-1)(1-s)-(2\kappa-1)x\right)
+\frac12\max\left(0,\frac{6s-1}{5}\right).
$$
The source proves the following exact statements.

| Change | Budget conclusion |
|---|---|
| Retune the original detector scales and slot length, retaining the existing losses | Minimum remains $7/8$. A nominal gain from longer slots is paid back by a reflected-budget face. |
| Save $\sigma$ in the original exceptional Gram exponent, at the original scales | The displayed boundary improves to $7/8-\sigma/16$, while the other terms and admissibility remain controlled. |
| Remove the exceptional contribution but retain the ordinary $P^2/Y$ term | Optimized boundary is $23/27\approx0.851852$, still worse than $5/6$. |
| Improve both nonunit contributions | For $\nu\ge0$, a boundary at most $5/6$ is feasible exactly when $\nu\le1/15$ and $\kappa+4\nu\le4/3$. |
| Remove both nonunit Gram contributions, retaining principal/reflected allowances | The remaining boundary has minimum $29/36>3/4$, at the degenerate low-scale endpoint $x=0,s=1/6$. |

An explicit five-sixths budget witness is
$$
\nu=\frac1{30},\qquad\kappa=\frac65,\qquad
x=\frac5{48},\qquad s=\frac16,\qquad
Y=Z^{35/48}.
$$
These values give **a concrete prospective estimate to research**, not a proposed proof by algebraic substitution. The unresolved task is to establish the corresponding bound for the actual detector Gram, uniformly in its moving parameters, while retaining enough of the principal signal and paying the reflected terms.

This identifies two useful directions:

1. **A small genuine Gram saving** would move the seven-eighths budget, if the rest of the detector argument were completed at the same scales.
2. **A five-sixths programme must attack both exceptional and ordinary Gram losses.** Improving only the exceptional-frequency estimate cannot reach that boundary in this model.

The three-quarters target needs more: even ideal Gram improvements cannot overcome the retained $29/36$ floor. One must improve the principal/reflected mechanism, or prove a different source bound such as the Cesàro-energy target above.

There is also a precise warning against an overly broad fourth-moment conjecture. [QuasiRHSubfieldMoment](../../../formal/GaloisForLFunctions/RHTower/QuasiRHSubfieldMoment.lean) constructs sextic characters and shift sets with fourth moments exceeding a cardinality-only $C|K||S|^2$ bound by an unbounded factor. This does not refute bounds for the actual structured detector sets. It says that any new bound must use their additional structure. Projecting away bad subspaces is useful only if one also proves how much detecting signal survives the projection.

**My assessment:** five-sixths is the most concrete improved detector target supplied by the corpus. Three-quarters is a sensible target in the direct arithmetic energy language, but there is no present input establishing it. A generic logarithmic improvement, density estimate, or parameter retuning is not the missing mechanism.

## 5. Opportunities for at least 75% of zeros on the critical line

### 5.1 What is established, and what is not the same statistic

The local census goes beyond the Montgomery–Taylor constant through Incommensurable Gabor Pinching. The inspected theorem `simple_critical_proportion_ge_67250071` gives, for every $\varepsilon>0$, eventually
$$
N_{0,\mathrm{simple}}(0,T)\ge(0.67250071-\varepsilon)N(0,T).
$$
The stronger symbolic gain is $H_D(1)+10^{-8}$. See [CriticalLineZeroProportion](../../../formal/GaloisForLFunctions/IncommensurableGaborPinching/CriticalLineZeroProportion.lean). This is the corpus result, including its Zeta23 foundation; no external historical benchmark was substituted for it.

The supplied reports also distinguish statistics that must not be conflated with 75% on the line: “simple or critical,” distinct ordinates carrying a critical zero, and zeros within $4/\log T$ of the line. None of those statements alone answers this question. Nor does the 75% dichotomy: if 75% critical fails, it forces a substantial population of simple off-line zeros within $A/\log T$; it does not eliminate that population.

### 5.2 The best target: one signed surplus, with explicit room to spare

Let $N=N(T,2T)$, and let $S_{u,\eta}(T)$ be the actual coalescent surplus for an admissible smooth window, at bandwidth $4/3$. The corpus proves the stronger simple-critical certificate
$$
N_{0,\mathrm{simple}}(T,2T)
\ge
\left(\frac{29}{36}-32\pi\varepsilon_1-\varepsilon\right)N
-S_{u,\eta}(T)+M_{\mathrm{off,multiple}}(T,2T),
$$
where the final term is nonnegative. This is `zeta_coalescent_certificate_four_thirds_simple_and_offLineMultiple` in [ParitySensitiveRamanujanStabilizerTransfer](../../../formal/GaloisForLFunctions/TransThresholdPairCorrelation/ParitySensitiveRamanujanStabilizerTransfer.lean).

Consequently, the arithmetic target
$$
S_{u,\eta}(T)\le\left(\frac1{18}+o(1)\right)N
$$
with arbitrarily small collar loss gives
$$
\liminf_{T\to\infty}\frac{N_{0,\mathrm{simple}}(0,T)}{N(0,T)}\ge\frac34,
\qquad\frac{29}{36}-\frac1{18}=\frac34.
$$
The passage from eventual dyadic-window bounds to the cumulative bound uses the same uniform eventual statement and the zero-count asymptotic. This conclusion is stronger than the requested critical-line proportion.

**Quantifiers are part of the target.** For every desired loss, choose $0<\eta<1/3$, a sufficiently small collar and an admissible profile, then prove both the certificate and the surplus estimate for that same choice and all sufficiently large heights. A favorable surplus for a different window, or only a subsequence of heights, does not plug into this receiver.

The surplus can be reduced to odd prime pairs with even shifts. Proper prime powers contribute
$$
O(T^{-1/3+\eta})N=o(N),
$$
not necessarily $o(1)$ absolutely. The normalized statement and the full/prime-only equivalence are in [CoalescentPrimeReductionAndParitySieve](../../../formal/GaloisForLFunctions/TransThresholdPairCorrelation/CoalescentPrimeReductionAndParitySieve.lean).

The useful hierarchy at this bandwidth is simple: a surplus bound $S\le bN+o(N)$ buys $29/36-b$. Thus $b<5/36$ beats $2/3$, $b\le19/180$ gives 70%, and $b\le1/18$ gives 75%, before any additional structural slack is credited.

### 5.3 Target the centered discrepancy, not full Hardy–Littlewood

There is an exact finite decomposition
$$
S_{\mathrm{prime}}=S_{\mathrm{Ramanujan\ model},Q}+D_Q,
$$
with parity retained in both terms. Its unnormalized form is `oddEvenShiftPrimeCoalSum_eq_stabilizerModel_add_discrepancy`. This is an identity about actual primes, not an assumed prime-pair asymptotic.

The model calibration gives a useful measure of how much accuracy is needed. In the corpus normalization, the Hardy–Littlewood/GUE model has surplus ratio $-1/144$. Therefore, **if** the chosen model truncation and end corrections are proved to have that asymptotic, it is enough to show
$$
D_Q/N\le\frac1{16}+o(1),
\qquad
-\frac1{144}+\frac1{16}=\frac1{18}.
$$
A strict allowance below $1/16$ would leave room for collar and truncation errors. Proving a full $o(N)$ discrepancy is unnecessary for the 75% target. Establishing the model evaluation with the selected cutoff is itself part of this programme; the finite identity alone does not establish its limiting value.

This is the most promising way to weaken the required arithmetic input without weakening the desired conclusion: seek one signed weighted inequality with a substantial error allowance, rather than uniform Hardy–Littlewood for every shift.

The sign must survive. A positive majorant discards the cancellation of the Poisson contribution against the precise singular-series term. In the supplied calibration, the sub-threshold positive majorant gives $8/27$ for the trans-threshold integral, where $1/9$ is required. The independent-Poisson model gives surplus $1/16$, which **misses** the budget $1/18$. An “uncorrelated” normalization with surplus zero is a different model. See [CoalescentSieveAnatomyAndModelCalibration](../../../formal/GaloisForLFunctions/TransThresholdPairCorrelation/CoalescentSieveAnatomyAndModelCalibration.lean).

The research question is therefore not whether prime-pair counts can be bounded above. It is whether their **centered, parity-sensitive signed reading** can be bounded at the required constant.

### 5.4 Two supporting opportunities

**Optimize structural slack, and then combine it with arithmetic slack.** IGP proves that scalar trace estimates discard a real macroscopic reserve: the cosine window's zero set does not support the requisite orthogonal lattice. Better packing, more spans and joint window optimization might enlarge $10^{-8}$. This is worthwhile mathematics. There is no supplied theorem indicating that it can supply the entire gap to 75%, about $0.0774993$. A more credible role is to carry the additional pinching credit into the trans-threshold certificate, thereby relaxing its prime-surplus budget. That combined receiver must be proved; gains from different windows cannot simply be added.

**Pursue a small displacement-sensitive energy budget.** The actual shallow Cauchy estimate is
$$
\frac1{\log T}E_{1/\log T}(T)\le C\,N(T,2T)
$$
for some constant $C$. It controls multiplicity and clustering but supplies no suitably small constant. See [ShallowCauchyImplications](../../../formal/GaloisForLFunctions/ShallowCauchyPrimeEnergy/ShallowCauchyImplications.lean).

If $R_{\rm sh},R_{\rm deep}$ count right-half-plane zero copies, the exact reflection accounting is
$$
N=N_0+2(R_{\rm sh}+R_{\rm deep}).
$$
Hence a paid upper bound $R_{\rm sh}+R_{\rm deep}\le N/8$ would give 75% critical zeros. Small deep-tail density does not suffice while the shallow term is only $O(N)$. Different Ward/Cauchy/cubic receivers use different energy normalizations; their constants must not be transferred without the matching comparison.

**Assessment:** the signed coalescent target is the leading 75% opportunity. Structural slack is a complementary source of room. Shallow energy is a second, displacement-sensitive approach, but its decisive constant remains missing. None of these estimates is currently a proof of 75%.

## 6. Three open questions to prioritize

I would focus the main research effort on the following three questions. They ask for new mathematical inputs with measurable intermediate outcomes, rather than another representation of RH.

### Priority 1 — Does cyclotomic arithmetic control the full overlap operator at a macroscopic ratio?

**Question.** Can the exact affine successor-shell source be converted into a completed operator estimate at $c=3/2$, then larger $c$, using the conductor-uniform curvature floor and retaining all mixed blocks, Gamma and both poles?

The theorem to aim for initially is eventual nonnegativity of the actual complete matrices for one fixed, quantitatively nondegenerate profile at a macroscopic ratio. The method should provide a usable dependence on ratio, conductor and horizon so that an exhausting schedule is a subsequent mathematical question, not a hidden quantifier exchange.

The first decisive lemma would identify the completed shell symbol and its cross-mode residual. It should explain exactly where the cyclotomic positive term enters and how the Schur cost is paid. A theorem controlling only each selected diagonal entry would leave the main question unanswered.

**Why first:** the necessary source identities, positive arithmetic quantities and bounded-overlap base case now coexist. This is the closest opportunity to convert several established tools into a genuinely new positivity mechanism.

**Useful failure:** a sharp negative symbol or unavoidable cross-mode term would identify which arithmetic information the current Ramanujan description loses. It would narrow the producer problem substantially.

**Walls addressed:** 3.26, 3.28, 3.42 and the first-prime/polar transfer faces of Wall 1; it deliberately avoids the impossible atomic Metzler repair.

### Priority 2 — Can the actual signed stabilizer discrepancy meet a census budget?

**Question.** For the exact admissible bandwidth-$4/3$ windows, can one prove
$$
S_{\mathrm{prime}}(T)\le(1/18+o(1))N(T,2T),
$$
by retaining parity and singular-series cancellation? Equivalently as a proposed decomposition target, can one evaluate the selected model and bound the remaining normalized discrepancy within the $1/16$ allowance described above?

A first milestone is a nontrivial constant saving in the same functional, sufficient to improve the current census. The $19/180$ budget gives a clear 70% checkpoint within the $4/3$ receiver; the narrower-band exchange-rate route may offer another checkpoint with different estimates. Those inputs should be compared by actual arithmetic difficulty, not by the numerical size of a coefficient in unrelated normalizations.

**Why second:** this target is weaker than RH, permits exceptions and has a known quantitative receiver. A new signed prime-correlation estimate would also teach us what arithmetic information can survive beyond the usual threshold.

**Useful failure:** characterize which class of signed dispersion estimates still collapses to a parity-blind majorant, and preserve the best constant or exact main-term cancellation it does prove.

**Walls addressed:** the census and coalescence faces 1.27, 1.30, 1.31 and 1.33. No claim that the estimate alone transfers to RH without a separate source theorem.

### Priority 3 — Can an independent integer-side construction retain sublinear count precision?

**Question.** Can exact arithmetic identities or signed auxiliary integrals produce a one-sided bound
$$
\psi(x)-x\le Cx^\theta
\quad\text{or}\quad
\psi(x)-x\ge-Cx^\theta,\qquad\theta<1,
$$
without assuming a Mertens bound, an RH-equivalent sign, or a suitably small integral? A first fixed exponent is the milestone; improving it below $7/8$, then toward $1/2$, supplies a clear progression.

The most concrete source to test is the exact factorial identity and its structured inversion. With
$$
I_n(E)=\sum_{k\le n}\mu(k)E(n/k),\qquad F(y)=y\log y-y,
$$
the established Stirling split gives
$$
\psi(n)=I_n(F)+I_n(G)+I_n(h),
$$
where $G$ is a small monotone remainder and $h=F(\lfloor y\rfloor)-F(y)$ is the sawtooth. Generic size control on $E$ cannot survive inversion with sublinear precision. Monotone control invokes Mertens precision. Therefore the new theorem must exploit the **joint constraints on these actual terms**, before separating them into absolute bounds.

A complementary realization of the same producer question uses the attained Nair lattice:
$$
\min\left\{\int_0^1P>0:P\in\mathbb Z[x],\deg P\le n\right\}
=\frac1{\operatorname{lcm}(1,\ldots,n+1)}.
$$
The floor is exact. What is missing is an independent analytic ceiling with signed cancellation and controlled positivity. Merely naming the minimizing polynomial computes the unknown $\psi(n+1)$ again. Generic sup-norm or divisibility arguments do not supply the requisite precision.

**Why third:** this is the most serious route to a producer that need not solve the full atomic comparison problem. It uses the ring's exact arithmetic and aims at the weaker, correct quotient by the count's precision class.

**Useful failure:** a sharp classification of the structured remainders or auxiliary class, with the best achievable exponent. An obstruction only for arbitrary errors is already known and should not be reproved as if it addressed the actual factorial remainder.

**Walls addressed:** 1.34–1.37 and the producer faces of Wall 14.

### Why these priorities differ from the existing three-question list

The supplied wall ledger puts infinite-symmetry polar confinement in its third slot. I would keep that as exploratory foundational work, but put a concrete census estimate among the three main priorities. The reason is mathematical: pole survival and continuation now work for the impure calibration data too. The additional confinement principle still lacks an independent source. The census has an explicit, weaker arithmetic target and a numerical allowance.

Similarly, I would not prioritize “prove finite complete index” as an easy bridge. Its equivalence to eventual RH and its Lindelöf consequence make it a much stronger endpoint than a modest census gain or a first fixed strip. None of this retires the geometric, heat-flow or confinement programmes; it changes which missing inequality receives primary attention.

## 7. What new mathematics would supply the missing tools?

### 7.1 A field specification: arithmetic correlation and precision theory

I would develop **arithmetic correlation and precision theory**: the study of how exact additive–multiplicative relations force signed estimates, and how those estimates survive inversion, localization and limiting processes at a specified precision.

This name describes a missing body of theorems, not a claim to have discovered an independent subject. CriticalArithmeticCorrelationTheory already supplies some of its finite arithmetic foundations. ArithmeticOfSquareRootPrecision supplies its distinction between identities and estimates. ArithmeticIndexDescent, SignedArithmeticHodgeTheory and the census programmes supply examples of transfers that preserve part of the needed sign. The proposed field should grow from these results.

Its central question would be:

> Which exact compatibility laws of arithmetic force cancellation or positivity beyond what follows from size, symmetry, local spectra and separate marginal distributions?

The object of study is not an arbitrary sequence satisfying broad bounds. It is the actual source together with all the relations that constrain it: additive shifts, divisibility, prime-power structure, residue stabilizers, logarithmic weights, and the analytic completion. A theorem may start with a class of sources, but membership of the actual source must be proved independently of the desired estimate.

This perspective addresses the repeated failure pattern in the ledgers. Absolute estimates forget sign. Marginal positivity forgets cross terms. Exact reconstruction forgets orientation. Weak convergence forgets escaping mass. Inversion can destroy precision. The new tools would control those losses together.

### 7.2 Objects and language

**Arithmetic sources with their relations.** Keep the weighted source and the actions relating its coordinates. For the prime source these include divisibility edges and affine successor edges; for the count they include the exact factorial and Möbius relations. A residue distribution alone is insufficient when the target reads correlations between residues, shifts and scales.

**Complete forms with designated reserves.** A form should carry its actual coefficient space, test profile, Gram matrix, Gamma term, both polar coordinates and arithmetic interaction blocks. A reserve is a proved lower bound available in a specified norm. A transfer records how much reserve it spends. This extends the successful joint-payment results and prevents the same Gamma credit being used twice.

**Precision spaces.** For a counting problem, record the allowed partial-sum error. For example, write
$$
\mathcal Q_{\theta,k}
=
\left\{\delta:
\sum_{n\le x}\delta(n)
=
O\!\left(x^\theta(\log x)^k\right)
\right\}.
$$
The square-root count uses a particular such class. A central problem is to determine which operations preserve these classes, which lose powers, and which preserve them only on the constrained remainders produced by arithmetic. The classification should distinguish linear error tolerance from the nonlinear requirement of complete positivity.

**Signed correlation functionals.** Treat the actual weighted reading as the object, including its centering and parity. In the census this is the coalescent surplus, not the collection of unweighted prime-pair counts. In the overlap problem it is the completed successor-shell operator, not a list of diagonal eigenvalues. Different functionals can require very different amounts of correlation information.

**Defect and escape data.** A proposed new construction is a matrix-valued description of what remains after projecting onto arithmetic packets. It would retain cross-mode terms, cross-annulus transport, polar coupling and mass escaping every bounded window. Such an object has not been constructed here. Its value would be a proved decomposition and convergence theorem; naming an “arithmetic defect measure” without those would add nothing.

The corresponding language should make three features explicit: **which source**, **which topology or norm**, and **which simultaneous parameter range**. “Positive,” “small,” and “converges” are incomplete statements without them.

### 7.3 Foundational principles it must satisfy

These are requirements for the theory, not new axioms that assert its desired conclusions.

1. **Arithmetic realizability.** Any correlation law used for zeta must be derived for the actual arithmetic source. A positive abstract model is a calibration until the source-to-model comparison is proved.

2. **Completion before sign extraction.** The decisive estimate must retain the terms that can change sign, including the two poles and mixed blocks. Separate estimates are legitimate when their combined cost is controlled in the original norm.

3. **Target-dependent precision.** A count theorem may work modulo its established error class. A complete positivity theorem must meet its stronger rigidity requirement. A census theorem need only pay an aggregate exceptional budget. The theory should exploit these differences.

4. **Uniformity as mathematical content.** Fixed-conductor convergence, finite-dimensional positivity and each fixed-overlap theorem are distinct from a growing-conductor, exhaustive result. A usable theorem supplies the required joint range or proves an admissible diagonal choice.

5. **Visible cancellation.** Centering, parity and the relations between terms remain present until their cancellation has been used. Triangle inequalities are applied after the relevant signed combination has been identified.

6. **Graded coercivity.** A reserve may decrease as overlap, conductor or resolution grows. The goal is a sufficient lower bound relative to the actual residual and synthesis error. Requiring one positive floor at every scale would impose a stronger, sometimes false, problem.

7. **Sharp calibration and positive salvage.** A failed theorem should expose the precise lost information and the strongest surviving bound. The Metzler boundary, cyclotomic floor, count stabilizer and exact detector budget illustrate what useful failures produce.

These principles guide theorem design. They cannot replace the independent arithmetic estimate.

### 7.4 The mathematical tools to build

**A signed arithmetic symbol calculus.** Classical diagonalization is not enough here: the arithmetic operator mixes multiplicative scales and additive successor shifts. The desired calculus would compute the completed action on growing Ramanujan packets, isolate the exact divisor jet, and bound the residual in operator norm. It would include composition and elimination rules that preserve the full Schur cost.

The first theorem should be modest and concrete: identify the symbol at one macroscopic overlap, and decide whether the cyclotomic curvature floor pays its residual. A general calculus is justified by such a theorem, not the other way round.

**A dispersion theory for centered arithmetic functionals.** Develop estimates that use parity, singular series and signed windows jointly. The census supplies an unusually clear benchmark: model evaluation plus discrepancy at most the stated constant allowance. A successful theory would prove a useful aggregate inequality without requiring every individual prime-pair asymptotic.

It must also distinguish exceptional structured sets from arbitrary sets. The finite-field fourth-moment counterexample shows why cardinality alone is not an adequate hypothesis for detector estimates.

**A constrained inversion theory.** Möbius inversion on arbitrary bounded or monotone errors already encounters sharp barriers. The open object is the particular correlated tuple of main term, Stirling remainder and sawtooth arising from the factorial identity. The desired theorem would estimate their joint inversion more accurately than the sum of separate bounds.

This is an opportunity for a new kind of cancellation theorem: precision follows from the relations among errors, rather than from a stronger norm bound on each error. Its first success would be a fixed sublinear one-sided count estimate, with every input derived from the arithmetic identity.

**A quantitative theory of exhaustion.** Approximation theorems should track profile regularity, aperture, conductor and height together in the complete form. Denjoy–Carleman synthesis supplies one starting point. The proposed slower schedule in Section 2.3 would be a concrete advance even before an arithmetic positivity theorem reaches that schedule.

**A theory of arithmetic selection and invisible perturbations.** The corpus already shows that different observables see different changes to the source. Count precision can ignore a remote finite prime change; exact full positivity cannot. Infinite prime patterns can lose all bounded-window spectral mass while retaining a nontrivial limiting question. The field should classify what each observable determines, what it cannot detect, and which additional coupling supplies the missing information.

**A constructive theory of signed auxiliaries.** For the Nair and point-count directions, seek arithmetic objects with exact integrality and independently proved analytic smallness. The subject must explain how signed cancellation coexists with a controlled positive output. Integrality without an analytic ceiling, or an auxiliary defined using the unknown answer, does not satisfy the specification.

### 7.5 Calibration families and criteria for success

A general theorem should be tested on the calibration family appropriate to its conclusion.

| Proposed conclusion | Required calibration |
|---|---|
| Full Weil positivity for the actual prime source | Distinguish the Liouville twin where the claimed range already separates it; eventually detect finite prime flips if the asserted family is exhaustive. |
| Square-root count precision | Respect the proved perturbation class, including changes that a count cannot distinguish. Rejecting every such perturbation is not a necessary criterion. |
| A 75% census | Use the same windows and normalization as the receiver; retain the difference between the Poisson and singular-series models. |
| An improved detector estimate | Survive the actual structured set geometry while respecting the arbitrary-set fourth-moment counterexample. |
| Spectral or polar purity from a realization | Supply an input absent from the impure calibration objects that already satisfy the weaker realization and continuation properties. |
| A limit theorem | Track mass escape and the decisive cross terms in the topology used by its receiver. |

The first successes should be new inequalities with useful scope, not a collection of equivalent definitions. Examples would be a completed macroscopic overlap bound; a signed census discrepancy improving the actual proportion; a detector Gram estimate meeting a better joint exponent budget; or a constrained inversion estimate yielding a fixed narrower strip.

A broad theory would become credible when the same proved technique supplies more than one of these gains through explicit transfers. Until then, common language is useful organization, not evidence that the residual arithmetic problems have been unified.

### 7.6 Research topics and sequence

The field's research programme should proceed through interacting, concrete problems:

- finite cyclotomic positivity and affine residue identities;
- signed local-to-global operator comparison, including complementary modes;
- arithmetic dispersion with parity and prescribed centering;
- exact precision classes under inversion and auxiliary constructions;
- joint limiting theorems with escaping mass;
- profile regularity and the least overlap needed for synthesis;
- quantitative interpolation between census, fixed-strip and exhaustive-sign targets, only where a source transfer is actually proved.

The first three priority questions in Section 6 would serve as its test problems. They are deliberately different: one asks for a complete sign, one for a tolerable signed error, and one for a new producer. A field that supplies tools for those distinctions could change the research frontier. A field whose foundational “positivity principle” merely restates RH would leave the present walls intact.
