# Signed Arithmetic Hodge Theory (SAHT)

Namespace `GaloisForLFunctions.SignedArithmeticHodgeTheory`; umbrella `SignedArithmeticHodgeTheory.lean`.

**Question.** How can arithmetic incidence, archimedean energy and the two polar coordinates jointly control the index of the
actual Weil form under source exhaustion? Turn positive arithmetic sections into quantitative control of their mixed
interactions and their complement. A positive section alone does not orient the complete form; a renormalized prime spectrum
alone does not recover the archimedean term or the poles.

"Hodge" = signed orthogonal decomposition, index and the arithmetic source of a sign — not a new cohomology or a positive
polarization. "Source-compatible" = actual tests, poles and mixed pairings survive every comparison. "Renormalized" never means
discarding an unpaid divergence.

---

## 1. Place in the research

Three starting constructions, each partial:
- **Balanced logarithmic Haar sections** (ACS): full rough-Weil floor above a fixed lower index, uniform in the horizon; coarse
  directions and inter-scale interactions remain.
- **Narrow arithmetic sections** (AID): bounded Weil-orthogonal projection in the complete source graph; the complement contains an
  infinite null radical; its nonnegativity is open (a strict lower bound on it is false).
- **Ramanujan profiles** (RAPT): prime-matrix quasimodes with distinct spectral points per finite conductor packet; comparison with
  the full source graph, Gamma and both poles is separate.

Plus the **canonical critical source energy** (AID): finiteness ⇔ finite off-line support; sharp smallness ⇔ RH; index costs bound it
below; an arithmetic upper bound is missing. SAHT's contribution is the *paid comparison* between these objects.

| Programme | Supplies |
|---|---|
| ArithmeticCastelnuovoSeveri | Scaling surface, Haar-cell effectivity, mean-zero Gamma payment |
| ArithmeticIndexDescent | Complete mixed-cell transfer, source-graph projection, index capture, critical-work costs |
| RenormalizedArithmeticPotentialTheory | Ramanujan quasimodes, adjunction energies, pole-gap selectivity, finite Ramanujan approximation |
| SpacingScaleHarmonicAnalysis | Source synthesis beyond narrow spacing |
| ArithmeticLorentzianGeometry | Constraints on positive gauges and stability mechanisms |
| ArithmeticOrientationGeometry | Signs along scaling correspondences |
| `RHTower` (CHMD) | Signed-source radical; two-pole classification of the quotient Weil form |

---

## 2. Objects and language

Every comparison specifies **source, form, domain, exhaustion, error currency**.

| Object | Content |
|---|---|
| Arithmetic source | Real compact logarithmic tests, complete source-graph closure, embedded cell/class spaces |
| Signed form | Complete Weil pairing with prime, Gamma, mass and two-pole terms |
| Paid section; residual | Subspace with a proved coercive estimate and bounded Weil projection $P$; $R=1-P$ with induced form |
| Radical | Vectors pairing to zero with all source vectors (may have nonzero graph norm); `arithmeticWeilRadical` = radical of the full form |
| Mixed charge; reserve | Bilinear block interaction in a stated norm; a positive term spent once |
| Dyadic clock | Weighted log-cell shift $W_2e_a=\alpha_ae_{2a}+\beta_ae_{2a+1}$, wandering details $d_a=\beta_ae_{2a}-\alpha_ae_{2a+1}$ |
| Stopping-cell source | The same whole-orbit cutoff as logarithmic block averaging; literal finite real BV head and tail, with ordinary mean and square mass accounted for |
| Modal source | Ramanujan profiles $v_m(n)=c_m(n)/\sqrt{\varphi(m)n}$, energies $E_m=\gamma+\log m+\text{tameDifferent}(m)$ |
| Critical energy | $R^2(\mathcal W(2R)-\mathcal W(R))\to\mathcal E_{\rm crit}\in[0,\infty]$ |

A morphism is a linear source map with proved formulas for its mixed-form and polar defects. No interface field may assume the
sign, a complement bound or an unproved estimate. The CHMD signed-source radical can be removed keeping both polar moments; the
full Weil form then still has a 2-dimensional polar radical (ground and odd polar classes) — quotienting it discards polar
coordinates unless stored separately.

---

## 3. Mechanisms

1. **Exact residual calculus**: for a paid section with projection $P$, exact identities for the residual form; one stationarity operator
   $D=J(F-U)$ gives a single budget for a whole coefficient family with a bounded trial correction.
2. **Exact radical retention**: the complement is $\ker P=\ker J$; restricting to it creates no new radical.
3. **Scale growth and scalar renormalization**: Weil value is translation invariant, pole moments scale by $e^{\pm t/2}$; quantitative source-scale
   bounds on bounded windows; translation extends to a bounded injective map on completed apertures (faithful transport).
4. **Dyadic clock**: $W_2$ is a pure isometry with complete wandering decomposition; the details $d_a$ are exactly the literal balanced Haar
   sources; every finite cell source has a finite dyadic expansion; integer translations act by a triangular level matrix (prime two
   shifts levels by one).
5. **Gamma allocation on the dyadic tree**: exact parent variance identity $V_{\rm parent}=V_{\rm left}+V_{\rm right}+\dots$ gives joint Gamma payment of all
   parent variances and logarithmic Haar tails across all levels. Whole generator cutoffs split every dyadic correlation exactly;
   the complete prime-two Euler contribution has one original-source Gamma budget. Orthogonal tail localization and Gamma
   translation invariance pay every real-lag correlation, each fixed finite Euler family, and jointly every cube and higher power
   of every prime. The cutoff is exactly logarithmic stopping-cell averaging: it preserves the ordinary mean and splits square
   mass orthogonally. The full even-power source error costs arbitrarily little head-plus-tail Gamma plus the paid tail mass.
   Uniform Gamma stability, first-prime transfer and full-Weil signed payment remain separate.
6. **Renormalized adjunction**: growing Ramanujan families have one Gram budget $(1+2\sum_{m\in S}m^2)/\log N$; prime-row corrections cost
   $C_m=\sqrt{\varphi(m)}(1+4\log m)$; one Mertens-type remainder $B_N$, bounded uniformly in $N$, controls every Ramanujan residual.
7. **Local capture and escape**: modal families lose normalized mass on every fixed integer window ($\le K_{S,L}/(\log N-D_S)$); every bounded
   prime-energy sublevel escapes fixed windows — completeness on bounded energy coexists with escape in fixed coordinates.

---

## 4. Pillar theorems

1. **Exact residual calculus and radical retention** (`TheArithmeticSchurComplementHasCertifiedErrorBounds`,
   `OneStationarityBudgetControlsTheWholeSourceFamily`, `TheSignedComplementRetainsExactlyTheWeilRadical`).
2. **Scale transport**: source-compatible on bounded windows, faithful on completed apertures; translation preserves Weil energy but
   escapes every exponential graph bound (`BoundedWindowsAdmitSourceCompatibleScaleTransport`, `CompletedAperturesCarryTheLiteralScaleTransport`,
   `TranslationPreservesWeilEnergyButEscapesEveryExponentialGraphBound`).
3. **Complete wandering decomposition of the log-cell clock; Haar details are the wandering basis**
   (`TheLogCellClockHasACompleteWanderingDecomposition`, `BalancedCellDetailsFormTheWanderingBasis`,
   `TheDyadicDetailsAreTheLiteralBalancedHaarSources`, `ArithmeticTranslationsHaveAnExactDyadicLevelMatrix`).
4. **One Gamma reserve pays all dyadic parent variances**; finite generator orbits approximate the physical cell source, high generator
   tails are small across levels, but compact details do not make translation orbits compact (`OneGammaReservePaysAllDyadicParentVariances`,
   `TheSiblingGammaChargePaysItsParentVariance`, `FiniteGeneratorOrbitsApproximateThePhysicalCellSource`,
   `CompactDetailsDoNotMakeTranslationOrbitsCompact`).
5. **Uniform Ramanujan budgets** (`GrowingRamanujanFamiliesHaveAUniformGramBudget`, `OneArithmeticRemainderControlsEveryRamanujanResidual`,
   `TheArithmeticResidualBudgetIsUniformInTheHorizon`).
6. **Local capture cost and escape of bounded prime energy** (`RamanujanFamiliesHaveAnExplicitLocalCaptureCost`,
   `BoundedPrimeEnergyEscapesEveryFixedIntegerWindow`).
7. **Actual stopping-cell averages and complete even-power head error** (`EveryGeneratorCutoffStopsAtAnActualDyadicCell`,
   `GeneratorCutoffsAreLogarithmicBlockAverages`, `ActualGeneratorHeadsPreserveTheSourceMean`,
   `TheSquareSourceHeadErrorHasOnlyAGammaStabilityCost`).

For the actual complete-cell clock $W_2$, the generator cutoff $P_A$ retains the root and every Haar label $a<A$ at every level.
[GeneratorOrbitCutoffsReduceTheDyadicClock](GeneratorOrbitCutoffsReduceTheDyadicClock.lean) proves $P_AW_2^k=W_2^kP_A$ and
\[
\langle W_2^kx,x\rangle-\langle W_2^kP_Ax,P_Ax\rangle
=\langle W_2^k(x-P_Ax),x-P_Ax\rangle.
\]
Thus every head–tail dyadic correlation vanishes exactly. Let $E_2$ denote the complete physical correlation sum with weights
$2\Lambda(2^{k+1})/\sqrt{2^{k+1}}$ and literal translations by $\log(2^{k+1})$.
[OneGammaReserveControlsTheDyadicEulerTail](OneGammaReserveControlsTheDyadicEulerTail.lean) proves absolute convergence and, for
every finite original cell profile $f$ and $A\ge1$,
\[
|E_2(f)-E_2(P_Af)|\le
\frac{64\log2}{\sqrt2-1}\frac{\Gamma(f)}{1+\log A}.
\]
Here $P_Af$ means the physical image of the cutoff applied to the source's exact cell coordinates. One finite generator set makes
this error at most $\delta\Gamma(f)$ for every profile and horizon, for any $\delta>0$. Entire translation orbits remain; neither
Gamma contraction under projection nor a coarse-source norm bound is assumed. This controls the full prime-two correlation
contribution across all levels. It does not determine the complete Weil sign or the sign on the retained generator orbits.

For every real lag $t$, write $C_t(F)=\operatorname{Re}\langle T_tF,F\rangle$ and
$Q_A=U(1-P_A)U^*$ on whole-line $L^2$. On an original real profile,
$C_t(f)=\int f(x)f(x+t)\,dx$.
[EveryTranslationHasAnAllLevelGammaTailBound](EveryTranslationHasAnAllLevelGammaTailBound.lean) proves
\[
|C_t(f)-C_t(f-Q_Af)|\le\frac{96\Gamma(f)}{1+\log A}
\]
for every compact real BV source. The identity $\langle Q_Af,g\rangle=\langle Q_Af,Q_Ag\rangle$ pays each mixed
probe from both original Gamma budgets; translating the original source preserves its Gamma. For general profiles the noncell
component remains in $f-Q_Af$. For actual finite cell sources this is exactly $UP_AU^*f$.

Let $E_P$ sum the complete critical Euler correlations over a fixed finite prime set $P$.
[FiniteEulerFactorsHaveAllLevelGeneratorApproximation](FiniteEulerFactorsHaveAllLevelGeneratorApproximation.lean) proves
absolute convergence for each prime on whole-line $L^2$, equality with the original profile-integral series, and
\[
|E_P(f)-E_P(UP_AU^*f)|\le
96\left(\sum_{p\in P}\frac{2\log p}{\sqrt p-1}\right)\frac{\Gamma(f)}{1+\log A}
\]
for every finite original cell source. Choosing $A>\exp(96C_P/\delta)$, with $C_P$ the displayed coefficient sum, gives
error at most $\delta\Gamma(f)$ for every source and horizon. Every prime power and every retained dyadic level is included.
No odd-prime commutation is assumed. The complete-power constants are not summable over all primes, and the retained spaces remain
infinite-dimensional.

The all-prime higher-power sector has finite total coefficient mass
\[
H=\sum_{p\text{ prime}}\sum_{k\ge3}\frac{2\log p}{p^{k/2}}<\infty.
\]
[AllHigherPrimePowersHaveAllLevelGeneratorApproximation](AllHigherPrimePowersHaveAllLevelGeneratorApproximation.lean)
proves absolute convergence of its complete correlation on whole-line $L^2$, directed finite-sum convergence, and the stronger
joint error estimate
\[
\sum_p\sum_{k\ge3}\frac{2\log p}{p^{k/2}}
 \left|C_{k\log p}(f)-C_{k\log p}(f-Q_Af)\right|
\le\frac{96H\Gamma(f)}{1+\log A}.
\]
This bounds the complete source and every finite prime-power selection before cancellation. For actual finite cell sources,
one $A>\exp(96H/\delta)$ gives error at most $\delta\Gamma(f)$ simultaneously for every profile, horizon and finite selection.
All retained generator orbits remain intact. General BV profiles retain their noncell component.

[CriticalEulerCoefficientMassStartsAtCubes](CriticalEulerCoefficientMassStartsAtCubes.lean) gives the sharp boundary:
the coefficient tail beginning at exponent $r+1$ is summable exactly when $r\ge2$.
Both $\sum_p2\log p/\sqrt p$ and $\sum_p2\log p/p$ diverge. This classifies the absolute-coefficient method; it does not
assert divergence of actual compact-source correlations or exclude signed prime–pole compensation. The higher-power theorem
is its positive survivor, with the literal physical source and one original Gamma reserve.

The whole-orbit cutoff also has an exact physical description. Write $\ell_n=\log((n+1)/n)$.
Repeated integer halving stops at a pair $(j,a)$ with $n/2^j$ having integer part $a<2A$;
if $n\ge A$, then $A\le a<2A$. Its block is
$B_{j,a}=\{2^ja,\ldots,2^j(a+1)-1\}$, and its physical interval is
$[j\log2+\log a,j\log2+\log(a+1))$.
[EveryGeneratorCutoffStopsAtAnActualDyadicCell](EveryGeneratorCutoffStopsAtAnActualDyadicCell.lean) and
[GeneratorCutoffsAreLogarithmicBlockAverages](GeneratorCutoffsAreLogarithmicBlockAverages.lean) prove
that the projected physical height on this block is
\[
\frac{1}{\ell_a}\sum_{m\in B_{j,a}}\ell_m f_m,
\qquad \sum_{m\in B_{j,a}}\frac{\ell_m}{\ell_a}=1.
\]
Cells $n<2A$ are fixed. Every cell in the projected image of cell $n$ has label below $2n$.
Thus an original finite horizon $X$ produces a finite real head using labels below $2X$, with every retained generator orbit intact.

[ActualGeneratorHeadsPreserveTheSourceMean](ActualGeneratorHeadsPreserveTheSourceMean.lean) constructs this head $h=P_Af$
and tail $t=f-h$ as actual compact BV functions for every finite real cell source, including the original `wholeCellProfile`.
It proves
\[
\int h=\int f,\quad \int t=0,\quad \int ht=0,\quad
\int f^2=\int h^2+\int t^2,\qquad
\int t^2\le\frac{32\Gamma(f)}{1+\log A}.
\]
Let $S_{\rm even}(f)=2\sum_n\Lambda(n)n^{-1}C_{2\log n}(f)$, the literal `squarePrimeSource`.
This includes **all even prime powers**, with exponents at least four also belonging to the higher-power sector above.
Its centered version subtracts $\tfrac12(\int f)^2+s_0\int f^2$, where $s_0$ is the square-source regular symbol at zero.
Both centering corrections cancel exactly in the mixed difference for $f=h+t$.
[TheSquareSourceHeadErrorHasOnlyAGammaStabilityCost](TheSquareSourceHeadErrorHasOnlyAGammaStabilityCost.lean) proves that,
for every $\varepsilon>0$, one $C_\varepsilon\ge0$ works for every cutoff and every finite source family:
\[
|S_{\rm even}(f)-S_{\rm even}(h)|
\le\varepsilon\bigl(\Gamma(h)+\Gamma(t)\bigr)
 +C_\varepsilon\frac{32\Gamma(f)}{1+\log A}.
\]
The proof extracts the centered diagonal estimate by quadratic homogeneity, then pays the zero-mean tail's remaining correction
with its square mass. The actual projected Gamma energies remain explicit. A bound
$\Gamma(h)+\Gamma(t)\le K\Gamma(f)$ uniform in cutoff and horizon is an unresolved intermediate target; it is not assumed here.
Ordinary mean preservation does not preserve the two exponential Weil moments. These four modules pass individual Lean checks
and their printed capstones use only `propext`, `Classical.choice` and `Quot.sound`.

---

## 5. Traps

- A null vector is not a negative direction; no graph-norm floor on a residual containing a Weil radical.
- Ordinary mean zero, the discrete harmonic pole constraint and two continuous exponential moments are different conditions.
- The sparse Euler shift $e_m\mapsto e_{2m}$ is not the complete-cell clock $e_m\mapsto\alpha_me_{2m}+\beta_me_{2m+1}$; a pole-hyperplane theorem for one is not one for the other.
- Shared Gamma reserve cannot be spent on every block separately.
- Fixed support, conductor or profile variation do not give uniform growing families; domain escape must be measured.
- Prime-matrix positivity ≠ full Weil positivity.
- Nonnegative entries of the critical pair energy do not make its kernel PSD.
- Larger horizons alone do not prove density; sparse positive carriers can be proper.
- No diagonal gauge in obstructed overlap regimes; signed block geometry must address that.
- Choosing a slow diagonal sequence from fixed-mode limits does not establish Gamma/pole/complement comparisons.

---

## 6. Open problems

1. **Joint full-Weil payment** using the all-level Gamma allocation. The complete even-power head error has an explicit
   $\varepsilon(\Gamma(h)+\Gamma(t))$ cost and an original-Gamma tail-mass cost. Seek uniform Gamma stability of the actual
   stopping-cell average, or a direct way to pay that remaining cost. Averaged Levy-kernel comparison and weighted Haar upper
   synthesis are concrete analytic candidates, not proved inputs or established globally open problems. First-prime transfer,
   both exponential polar moments, retained-orbit sign and a complete-form bounded-index theorem remain separate obligations.
2. **Twin-selective control of generator orbits** with Gamma and both poles; transfer of the discrete prime gap beyond narrow spacing.
3. **Arithmetic upper bound on $\mathcal E_{\rm crit}$** retaining exterior rows (finiteness ⇒ finite off-line support; $\mathcal E_{\rm crit}\le1294047/2000$ ⇔ RH).
4. **Growing Ramanujan families** controlling a useful full-source domain, with a complement estimate surviving Gamma and the continuous
   two-pole comparison; enlarging corrections making stationarity uniformly small.
5. **Counterterms converging in a topology preserving mixed Weil pairings**; constraints between conductor, class variation and horizon.
6. **Selective localization** seeing every exceptional ordinate at affordable conductor and inverse cost.

## 7. Tools to build

Complete signed block payment on the dyadic tree; quantitative growing-family schedules with full-form complement and
Gamma/pole transfer; arithmetic upper control of critical work; moving-coordinate norm comparisons for escaping modes.

## 8. Contribution standard

Identify the actual source; prove a new estimate, sharp classification or structural theorem an estimate needs; preserve the
complete form; state every growing parameter; account for mixed terms and poles; instantiate abstract lemmas on actual
arithmetic objects; say precisely which endpoint remains open.
