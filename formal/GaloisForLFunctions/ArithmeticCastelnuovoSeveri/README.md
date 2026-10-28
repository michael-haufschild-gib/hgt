# Arithmetic Castelnuovo–Severi Theory (ACS)

**One question.** Weil proved RH for curves over $\mathbb F_q$ by reading the zeta function as an
intersection theory on $C\times C$ and the positivity of its explicit formula as the Hodge index
theorem. Which ingredients of that proof exist for $\mathbb Z$, which are provably absent, and what
would a proof of the missing ones have to produce?

ACS is the intersection theory of the **scaling surface** of $\mathbb Z$: cycles are the pole plane
$\langle H,V\rangle$ (directions $e^{\mp u/2}$) plus Weil tests; the pairing is the local side of the
explicit formula; the Castelnuovo–Severi defect is Weil's form; the Hodge index is RH
(`scalingSurface_hodgeIndex_iff`). The surface is a vector space with a pairing, not a scheme. Every
statement is unconditional and calibrated over $\mathbb F_q$.

Namespace `GaloisForLFunctions.ArithmeticCastelnuovoSeveri`; umbrella `ArithmeticCastelnuovoSeveri.lean`.

---

## 1. Place in the research

ACS is a live route: source-defined sections → all-aperture Riemann–Roch with ampleness → scaling
Hodge index → RH. It contributes the exact count of the form's failure (right zeros), its
localisation on one Hecke orbit and one prime tower, the $\mathbb F_q$ calibration, the fake data any
forcing argument must exclude, and the source-carrier (Meyer) theory of where effectivity can live.

| Programme | Connection |
|---|---|
| [arithmetic-positivity-theory](../arithmetic-positivity-theory/README.md) | The Weil–Markov–pole form whose positivity is Hodge index |
| [ArithmeticIncidencePositivity](../ArithmeticIncidencePositivity/README.md) | Ratio atoms = Hecke incidence; odd-sector ledger |
| [SquareRootThreshold](../SquareRootThreshold/README.md) | Visibility laws → degree filtration; width–floor alternative |
| [ScaleSignedIncidenceCriticality](../ScaleSignedIncidenceCriticality/README.md) | Bounded readings; ACS supplies hiding examples over $\mathbb F_q$ and $\mathbb Q$ |
| [BezoutValuationIncidence](../BezoutValuationIncidence/README.md) | Consecutive integers have no prime Hecke intersection |
| [BiScaleUncertainty](../BiScaleUncertainty/README.md) | Adversarial models; fake curves |
| [ArithmeticCriticalityTheory](../ArithmeticCriticalityTheory/README.md) | Same sign via ground energies; ACS counts it via signature |
| [ArithmeticCompensationTheory](../ArithmeticCompensationTheory/README.md) | Comb mean field; horizon energy $J$ in the all-parity identity |
| [TransThresholdPairCorrelation](../TransThresholdPairCorrelation/README.md) | Analytic engine of the route to $3/4$ |
| [ArithmeticOrientationTheory](../ArithmeticOrientationTheory/README.md) | Takes the scaling surface as geometric core; Nyquist rank bound = shadow of missing RR |
| [ArithmeticOrientationGeometry](../ArithmeticOrientationGeometry/README.md), [ArithmeticLocalDivisorGeometry](../ArithmeticLocalDivisorGeometry/README.md) | Reflection transport; source-defined local divisor tests |
| Others (THIM, ACCE, SAEI) | Finite identities vs critical estimates; transport; signed Möbius source |

`RHTower` supplies the explicit formula, Weil criterion, Lévy–Khintchine form and matrix inertia.

---

## 2. Why

Weil's five ingredients: (i) intersection pairing; (ii) fibres $H,V$, $H^2=V^2=0$, $H\cdot V=1$;
(iii) Frobenius graphs, $\Gamma\cdot\Delta=\#C(\mathbb F_q)$ (Lefschetz); (iv) $\Gamma^2=q(2-2g)$ (adjunction);
(v) Riemann–Roch ⇒ Hodge index $D^2\le2(D\cdot H)(D\cdot V)$ ⇒ $|N-q-1|\le2g\sqrt q$.
Over $\mathbb Z$, (i)–(iv) are exact (hyperbolic pole plane, prime comb = Lefschetz, archimedean term
= adjunction). Over $\mathbb F_q$ the same span identities hold for **fake** data violating RH, so
they cannot force the sign. Weil's sign comes from effectivity: effective divisors are zero sets
of sections, meet nonnegatively (Bézout), and Riemann–Roch supplies enough of them. ACS isolates
which of these the scaling surface has.

---

## 3. Objects and language

| Weil over $\mathbb F_q$ | Scaling surface of $\mathbb Z$ | Lean |
|---|---|---|
| $C\times C$, pairing | cycles $aH+bV+f$, explicit-formula pairing | `scalingSurface` |
| fibres | pole plane; $f\cdot H=\int fe^{-u/2}$, $f\cdot V=\int fe^{u/2}$ | `PolarSurface`, `poleB`, `poleA` |
| defect $2(D\cdot H)(D\cdot V)-D^2$ | Weil form | `defect`, `scalingSurface_defect_self` |
| Frobenius graphs | Hecke cycles $T_a\Delta_g$ (translates by $\log a$) | `heckeCycle`, `translate` |
| Frobenius eigenvalues | $p^{\rho-1/2}$ on the tower of $p$ | `frobEig`, `towerGram` |
| Lefschetz numbers | prime comb | `graphPair`, `arithLefschetz_split` |
| adjunction | archimedean collar (Lévy jump form) | `re_archCross_eq` |
| genus $2g$ | zero count (infinite) | `eq_zero_of_paperFT_vanish` |
| Bézout | disjoint nonnegative tests meet $\ge0$ | `localPair_nonneg` |
| RR ⇒ Hodge | effectivity with RR + ample axioms | `RiemannRochAxiom`, `AmpleAxiom`, `BezoutAxiom` |
| #eigenvalues $|\alpha|>\sqrt q$ | #distinct zeros $\Re\rho>\tfrac12$ | `pontryagin_law_curve`, `pontryagin_law` |

Further objects: curve data (`CurveDatum`), span defect = Toeplitz form (`spanDefect`, `spanGram`),
fake curves (`goldenDatum`: $q=5$, $\beta=\varphi,\varphi^{-1}$), zero configurations (`ZeroConfig`,
`TemperedConfig`), intersection Gram (`intersectionGram`), Hodge defect (`hermNegIndex`,
`hodgeDefectAt`), spectrally generic tests (`SpectrallyGeneric`), source cones (`sourceCone`,
`gradedSourceCone`, `l2SourceCone`, `sobolevSourceCone`, compensated surfaces), Hecke incidence
(`heckeIncidence`, `towerForm`), odd degree-$r$ subsurface (`scalingSubsurface`, `oddRealTestsAt`).

**Words.** *Degree* (pairing with $H+V$) vs *aperture* (support bound). *Hodge defect* = negative
squares of Weil's form. *Unitary* / *fake* datum. *Kronecker rank* of zero frequencies (1 for curves,
finite for exponential polynomials, ∞ for $\zeta$). *Resonant prime* (two right zeros share $p^{\rho-1/2}$).
*Meyer source carrier*: the genuine Poisson source space (all-weight source with Poisson boundaries),
with sharp involution, convolution, centred scaling flow, Hasse jets at Xi zeros.

---

## 4. Mechanisms

### Polar surfaces and $\mathbb F_q$ calibration
1. **Polar decomposition** $x\cdot y=(x\cdot H)(y\cdot V)+(x\cdot V)(y\cdot H)+x^\circ\cdot y^\circ$; four forms of Hodge index; under
   it, Cauchy–Schwarz on the defect — the only inequality in Weil's proof. Adjunction carries the
   bound: realizability ⇔ PSD defect Gram; only $\Gamma^2\ge q(2-2g)$ is used; free $\Gamma^2$ bounds nothing.
2. **Span defect = Toeplitz form** in power sums; span Hodge index = unitarity; Pontryagin law over
   $\mathbb F_q$ (defect = #outer eigenvalues, reached at window $2g$); span = period quotient of the scaling
   surface (Poisson along tilted lattices); contact law; window law. **Towers of a curve at every
   scale:** one probe sees each; the defect is finite exactly at arithmetic scales $\ell\in\mathbb Q_{>0}\log q$
   (at $a\log q$ the Frobenius span over $\mathbb F_{q^a}$, at $(a/b)\log q$ the $b$-th roots of the
   $\beta_i^a$) and infinite at every other scale (`TheTowersOfACurveAreItsBaseChanges.lean`).
3. **Fake curves.** Golden datum: integral counts, rational zeta, functional equation, Witt
   integrality, Beurling structure — Hodge defect exactly 1. A rank-one Beurling system satisfies
   every listed constraint and fails Hodge index.

### The scaling surface
4. **Signature law** #positive squares $=1+$#negative squares of $W$; RH ⇔ one positive square;
   signature correct iff RH and weight $=\Lambda$.
5. **Pontryagin law** for every tempered configuration: max negative squares $=\#\{\Re\rho>\tfrac12\}$; for $\zeta$
   the Hodge defect counts right zeros (interpolation at zeros / zero-side inertia).
6. **Reflection sectors** (even/odd) and **degree filtration**: additive at every degree; $\zeta$ has
   defect 0 through degree $3/10$, odd sector through $181/500$; invariant under multiplicity and depth
   deformation (a count, not a mass); **finite at every degree** for $\zeta$: $\le1+4aT(a)/\pi$ (archimedean
   horizon + Bessel/Shannon count); failure confined to an explicit low-frequency grid + pole.
7. **Visibility.** Isolated pairs seen at $\sinh(2\delta a)/\delta=2L+2a$; hidden subsets by pair energy;
   height-uniform visibility under unit-window counts; under `OffLineCopiesLocallyBounded` the
   modulated lag is doubly logarithmic, two-sided $\Theta((1+\log\log\gamma_0)/\delta_0)$, intrinsic; dichotomy:
   doubly-log visibility and defect rate = width, or off-line clustering. On lag lattices (curves,
   crystals) the defect jumps $0\to\infty$. Lag tests over $\mathbb F_q$ decide purity (Turán).
8. **Kronecker-rank dichotomy.** Vertically recurrent configurations (finite rank) have defect 0 or ∞;
   a finite nonzero number of off-line zeros needs infinite rank.
9. **Cyclic law and prime towers.** Translates of one generic test by any dense shift set carry the
   whole defect; for $\zeta$, $\mathbb Z\log p+\mathbb Z\log q$ suffices. One tower = period quotient with Toeplitz Gram
   in Laurent moments; tower defect = #visible outer Frobenius eigenvalues when real parts are
   well-founded; resonances at most one prime per pair; almost every prime sees every right zero
   (finite case); attained tops always seen. **Wolff obstruction:** at a non-attained top with
   increasing real parts, symmetric Wolff configurations are Toeplitz-blind on every window; two
   primes recover the full defect. **Deep sparseness defeats Wolff:** the extraction reads only
   levels where the test is nonzero, and when the zeros of depth $\ge\sigma$ have convergence
   exponent $<1$ (every $\sigma>\tfrac12$) an Ingham annihilator kills all but chosen
   representatives; then one prime sees every distinct outer eigenvalue. $\zeta$ is deep-sparse
   (Ingham–Huxley), so at **every** prime $\sup$ tower defect $=\#\{\text{distinct }p^{\rho-1/2}\}$
   and RH ⇔ Weil positivity on the towers of one prime (`OnePrimeSeesTheWholeDefectOfZeta.lean`).
   **Fixed tests: blindness is separation.** The Cauchy transform of a vector orthogonal to a tower
   vanishes on the component of the origin off the closed folded spectrum `{β_τ⁻¹}`; its residues
   are class sums. A fixed test sees every visible `b` with `b⁻¹` accessible from `0`, so Wolff
   blindness needs the folded zeros to wall `b⁻¹` off; countable folded spectra never blind
   (`WolffBlindnessRequiresSeparation.lean`). **Blindness needs a wall:** the `∂̄`-equation of the
   Cauchy kernel replaces residues, so no isolation is needed; a fixed test is blind to `b` only if
   the closed folded spectrum meets every disc about `b⁻¹` in positive area or walls part of it off
   from `0`. For countable folded spectra one probe carries the whole tower defect, whatever the
   order type of the real parts (`WolffBlindnessNeedsAWall.lean`). **Weights never cancel for probes:** the class weight
   of `φe^{isu}` continues to an entire function of `s`, equal to `Σ m_τ|φ̂|² > 0` at `s = t+iδ`;
   one probe sees every outer eigenvalue at every prime of every tempered configuration, and its
   tower carries all distinct eigenvalues when real parts are well-founded
   (`OneProbeSeesEveryOuterEigenvalue.lean`). **One test suffices for `ζ`:** at every prime a single
   test's tower carries every distinct `p^{ρ−½}` and decides RH — a killing test when infinitely many
   eigenvalues share a depth (separated subsequence), a probe otherwise
   (`OneTestCarriesTheDefectOfZetaAtEachPrime.lean`). **Weil's two-element windows suffice:** the
   Lefschetz sequence `c_m = W(T_{p^m}g, g)` of one test is `O(R^m)` (`R ≥ 1`) iff `R ≥ p^w`, `w` the
   zero width; RH ⇔ `|c_m| ≤ c_0` for all `m`, and `c_m = O(p^{θm})` ⇔ the strip `|Re ρ−½| ≤ θ`
   (`OneLefschetzSequenceGrowsAtTheZeroWidth.lean`). **One cycle for every prime:** a single test reads
   `p^w` at every prime; attained tops are read by any test with nonzero top weight (Cesàro, no
   isolation), non-attained ones by a subsequence convergent in `∏_p ℂ`; curves at every scale
   (`OneCycleReadsTheWidthAtEveryPrime.lean`). **Off-line zeros are Lefschetz ratios:** for each right
   zero `ρ` of `ζ` one test has `c_m ~ W p^{m(ρ−½)}` at every prime, so `c_{m+1}/c_m → p^{ρ−½}`,
   Weil's inequality fails at every large `m`, and two primes determine `ρ` (no period over `ℤ`)
   (`OffLineZerosAreLefschetzRatios.lean`). **Resonant scales** (towers merging right zeros) are
   countable; off them one tower carries the Hodge defect; for `ζ` all but finitely many primes are
   non-resonant (all but one if right zeros are infinite); a curve resonates at every arithmetic
   scale (`TheResonantScalesOfAConfiguration.lean`). **One-sided bounds suffice at two primes:** the
   width is `≤ θ` iff every test has `±Re c_m^{(p)} = O(p^{θm})` at two distinct primes; RH iff the
   upper (or the lower) one-sided Weil inequalities hold there — the `𝔽_q` real-zero exception of
   one-sided Lefschetz bounds disappears because prime logarithms are independent and `ζ` has no
   real zeros (`OneSidedLefschetzBoundsAtTwoPrimesAreTheStrip.lean`). **One prime suffices:** two-term
   tests `g + c T_v g` rotate the Frobenius weight of a kept zero into any half-plane, so at one prime
   the width is `≤ θ` iff every test has `ε Re c_m = O(p^{θm})`, and RH iff the upper (or lower)
   one-sided Weil inequality holds for every test (`OneSidedLefschetzBoundsAtOnePrimeAreTheStrip.lean`).
   **Short cycles suffice:** the same laws hold on tests supported in `[−η, η]` for every `η > 0`;
   RH iff `Re W(g − T_{p^m} g) ≥ 0` for every such `g` and `m`, while for `η ≤ 3/10` each window is
   Weil positive — Hodge index splits into local positivity (a theorem) and the one-prime Lefschetz
   bound on short cycles (all of RH) (`TheStripLivesOnShortCycles.lean`). **Density settles one
   prime for every configuration:** a window's negative squares depend continuously on `X(g)` and
   the zero map has dense range, so Lagrange interpolation at `b, b̄⁻¹` on one finitely supported
   vector gives `sup_{g,K}` tower defect `= #`distinct outer eigenvalues for every tempered
   configuration at every scale — no deep sparseness, no Ingham–Huxley; Wolff blindness is a
   property of a fixed test. For any `v > 0`, no right zeros iff `W(g − T_v g) ≥ 0` for all complex
   tests; RH iff `Re W(T_v g, g) ≤ W(g, g)` — the complex-test form of the orientation of the
   scale-stable family `(1 − T_v)(tests)` (`OnePrimeSeesTheDefectOfEveryConfiguration.lean`).

### Effectivity, Bézout, Riemann–Roch
10. **Hodge index ⇔ effectivity with RR + ample** (`exists_effectivity_iff_hodgeIndex`); positivity is
    not effectivity (positive test cones fail RR); form-defined cones are tautological.
11. **Bézout positivity holds** for effective cycles without common component via the Lévy jump form
    (prime incidence + collar, both $\ge0$); self-intersections carry $-A(0)\|f\|^2$; Bézout + RR ⇒ Hodge.
12. **Source cones** ($\Phi(x)\le2(x\cdot H)(x\cdot V)$, pole degrees nonnegative). RR ⇔ $\Phi\le$ defect; strict ampleness ⇔
    $\Phi>0$ on primitives; $L^2$ cones: ample iff $c>0$, RR iff $c\int f^2\le W$. **Boundary rigidity:** for
    fibre-invariant even reserves, Bézout ⇔ $\text{defect}(x,y)^2\le\Phi(x)\Phi(y)$; RR + Bézout force
    $\Phi=\text{defect}(x,x)$ (also for signed/asymmetric reserves via $\max(\Phi,0)$); ampleness ⇔ $\Phi\le0$ only on
    the mixed-defect radical (= fibre plane on the compact surface; compact numerical equivalence is
    equality). **Bézout costs twice the negative reserve.**
13. **Graded RR at every aperture** with explicit negative constants ($-(10+72e^r)$ etc.); compensated
    surfaces have RR + ample + Hodge unconditionally; **away from the low-frequency divisor** $D_a$ and the
    pole, coercivity $E(a)(1-1/\pi)$ gives RR, ampleness and Hodge at every degree. No aperture-independent
    weighted cone has RR at all apertures; Gaussian ceiling on coercivity; polar ground-energy strict
    decrease self-upgrades all-aperture Hodge to strict; Sobolev cones: width $\le\sigma$ ⇔ graded RR at rate
    $2\beta$, all $\beta>\sigma$. Exact arithmetic reserve (Gamma + Lévy + horizon + integrated prime deficit) gives
    RR at every aperture, Bézout/ample ⇔ its sign.
    **Independent arithmetic sections:** for an explicit constant $c>0$, every
    $f(u)=\sum_{1\le n\le N}g_n(u-\log n)$ with independently varying real $C^2$ profiles supported
    in $[0,w]$, $0<w\le c\log(1+1/N)$, satisfies $W(f,f)\ge\int f^2$, with no pole-moment or sign
    condition. A retained tilted prime-row reserve pays the entire adverse pole product through
    complementary weighted moment bounds (`ArithmeticSectionsPayThePole.lean`). The whole linear
    section space has RR, ampleness, and Hodge index on the original scaling subsurface. The support
    restriction remains; no unrestricted section-count or Hodge theorem follows.
    **Independent separated sections:** for every fixed separation $s>0$ and $0<\kappa<2$,
    sufficiently narrow profiles of width $\delta$ at arbitrary $s$-separated centres of span
    at most $\kappa\log(1/\delta)$ satisfy the same square-mass floor, uniformly over all local
    shapes and signs (`IndependentSeparatedSections.lean`). Mixed correlations are assigned to
    their separate masses; symmetry converts the prime interactions into row bounds. The entire
    linear carrier has RR, ampleness, and Hodge index, including non-ratio prime interactions.
    Full-source effectivity beyond this span restriction remains open.
    **Complete logarithmic-cell prime transfer:** every real compact $C^2$ test is recovered
    by complete cell sections and arithmetic divisibility forms. The actual quadratic $L^2$
    prime energy converges to the existing `RHTower.primeSum` at order $1/N$, retaining all
    prime powers and signed successor terms (`CompletePrimeSourceTransfer.lean`). Compactness
    derives the support horizon, and smoothness supplies uniform mass and derivative bounds.
    **Complete source transfer:** one complete cell system for each finite family of real compact
    $C^2$ sources recovers the original `zetaZeroConfig.W` on every linear combination and all
    polarized Gram entries (`CompleteWeilSourceTransfer.lean`). The form depends only on finite
    cell coefficients and retains square mass, full Gamma Lévy energy, every prime translation,
    and both pole moments. The profiles converge in $L^2$; bounded variation pays their entire
    jump-error energy at order $1/N$. Identification with the actual cell vectors and compatibility
    with linear synthesis are exact.
    **Smooth complete-cell sections:** one positive convolution operator preserves exact Hecke
    subdivision and both pole degrees. The resulting compact $C^2$ sections have dimension $X$
    on the first $X$ whole cells, at every smoothing scale (`SmoothArithmeticCellSections.lean`).
    Regularization contracts the entire Gamma jump energy and recovers it in the limit.
    The original `zetaZeroConfig.W` on these smooth profiles converges to the existing
    `finiteCellWeil c 0 1 X`, retaining every prime translation and both signed pole terms
    (`SmoothFiniteCellArithmeticForm.lean`). Full-source effectivity and the signed
    Gamma–prime–pole index bound remain open.
    **Balanced complete-cell prime bound:** the actual balanced pair on cells $2a,2a+1$
    has square mass $M_a$. Its translated real pairing with pair $b$ is exactly $M_b$
    when $(2a+1)m=2b+1$, and zero otherwise; every even multiplier vanishes
    (`HaarCellPrimeCompression.lean`). For arbitrary signed coefficients, the entire prime
    energy is at most $\sum_a (16+\log(2a+1)/\sqrt2)M_a c_a^2$, independently of the upper
    horizon (`HaarCellPrimeBound.lean`). This pays the prime term on a concrete source
    subspace. The compact BV representatives have exactly zero mean on every pair, exact
    weighted square mass, and the same original `RHTower.primeSum` (`HaarCellProfiles.lean`).
    **Coherent Gamma payment:** finite disjoint mean-zero intervals retain their full
    reciprocal-width logarithms in the original Lévy form, including touching intervals and
    nonzero exterior source values (`GammaMeanZeroCoercivity.lean`). On the actual balanced
    pairs this gives $\sum_a \log(a)M_a c_a^2 \leq \operatorname{levyEnergy}(f)$
    (`HaarCellGammaPayment.lean`). The pole bound and full-source effectivity remain open.
14. **Finite readings cannot supply Bézout.** Weil Rayleigh quotients are unbounded in every
    finite-reading kernel (smooth unit-mass witnesses in `SmoothFiniteReadingKernels.lean`), so no reserve from finitely many linear
    readings (plus mass) gives Bézout; exact effectivity needs infinitely many degrees; arithmetic
    majorants give Bézout + ampleness but their extra reserve breaks RR. Their aperture cones are
    convex, pointed and generating (`ArithmeticMajorantConeGeometry.lean`).
15. **Hecke–Lefschetz rigidity.** Adams operations and Hecke correspondences are isometries; Lefschetz
    splitting; a single correspondence scaling $(x\cdot H,x\cdot V)$ by $(1,a)$ replaces the ample axiom:
    RR ⇔ open positive cone ⊆ E ∧ defect ≥ 0; RH ⇔ $T_2$ maps the open positive cone into the ample half
    space. Rosati source cone over $\mathbb F_q$: RR exactly on unitary data, violated by the golden datum.
    Hecke classes do not move numerically.
16. **Universal floor law.** Every ample cone of nonnegative degree has RR ⇔ open positive cone ⊆ E ∧
    defect $\ge0$ — no construction escapes the defect floor.

### Meyer source carrier
17. **Poisson principal cycles.** The all-weight source admits genuine Poisson boundaries; pole-moment
    compensation gives nonzero principal cycles invisible to every intersection reading; origin degree does not
    descend through Poisson boundaries (pole-blind boundaries have positive origin degree).
    This strictly positive source mass is centered-flow invariant, but Weil trace is unbounded on
    its unit sphere at every positive aperture; no nonlinear function of mass bounds the mixed
    trace (`InvariantOriginMassDoesNotBoundTheWeilTrace.lean`).
    Factorial-normalized actual classes obey truncated local polynomial product rules and the
    reflected parity law for sharp; every finite causal section has an exact Hasse expansion
    (`MeyerFiniteJetAlgebra.lean`). Actual finite causal projectors select complete jet blocks and
    are central convolution multipliers; each value idempotent acts as its whole local block
    projector (`MeyerFiniteProjectorAlgebra.lean`).
18. **Meyer source surface.** Linear trace degree on genuine cohomology gives graded RR
    unconditionally; Bézout, ampleness, additive closure ⇔ RH; numerical = principal ⇔ Xi simplicity.
    Bounded-orbit carrier (full-Hasse Hilbert–Schmidt): RR, Bézout, ampleness unconditional;
    numerical = principal ⇔ simple critical zeros. Boundedness, norm isometry, and support only in
    critical highest jets are equivalent; these classes form a nontrivial sharp-stable convolution
    subspace. Trace-one witnesses exist above every height.
19. **Maximal blind ideal.** Mixed-trace boundedness along the centred flow defines a pre-divisor
    carrier = sources whose Mellin transform vanishes at every off-line Xi zero; it is the **unique
    maximal sharp-stable convolution ideal with nonnegative trace**, with Hodge, RR, Bézout, ampleness
    unconditional. Single-channel correspondence-stable positivity is exhausted by off-line blindness.
20. **Harmonic coupling exit and its Fejér barrier.** Escaping single-channel blindness requires coupling
    dilated harmonic channels ($n^{-ik\omega}=(n^{-i\omega})^k$). Nonnegative cosine polynomials obey the strict
    barrier $a_1<2a_0$; quantized divisor-order forcing excludes zeros on $\Re s=1$ and from the dlVP collars
    — the classical zero-free mechanism; Beurling countermodels show both hypotheses (simple pole,
    harmonic pole isolation) are needed.
21. **Faithful degrees and adjoints.** Faithful positive linear degree on genuine cohomology ⇔ RH +
    simplicity ⇔ arithmetic sharp = Hilbert adjoint; flow-invariant majorants of the mixed trace ⇔ RH;
    critical trace degree positive with exact kernel; quasi-inverse radical vanishes ⇔ simplicity.
    Every positive Hermitian degree restricts on finite causal packets to nonnegative critical
    value weights: off-line blocks and higher jets vanish. Conversely finite nonnegative critical
    weights define positive Hermitian degrees on the whole quotient
    (`PositiveMeyerDegreesSeeReducedCriticalJets.lean`).
    Every complex degree splits uniquely as `h + I • k` with Hermitian `h,k`; their square
    readings are exactly the original real and imaginary parts. Real square positivity and its
    finite critical-value classification therefore depend only on `h` (`MeyerHermitianDegreePart.lean`).
    Every nonzero algebraic character is a unique Xi evaluation, without continuity; Hermitian
    and positive characters are exactly critical evaluations. All characters separate classes iff
    Xi zeros are simple; positive characters separate iff RH + simplicity
    (`MeyerAlgebraicCharacters.lean`).
    Every finite Xi packet splits positive degree energy into its exact critical-value weighting
    and a nonnegative remainder. Critical packets also split the sharp square in genuine
    cohomology. The supremum of finite projected energies is nonnegative and bounded by full
    energy (`FiniteMeyerProjectorsSplitPositiveEnergy.lean`); vanishing of the residual remains open.
    The faithful Hilbert–Schmidt reserve gives Bézout and ampleness; its RR and exact linear-degree
    representation hold iff RH + simplicity. Reserve boundedness and invariance both select critical
    highest jets. On that restricted carrier, faithful-reserve RR and linear representation hold iff
    critical zeros are simple; invariance is unconditional.
    Genuine Poisson boundaries are dense in origin half-density L2. Every source class has
    arbitrarily small origin square mass, and its exact lower bounds are the nonpositive reals
    (`PoissonBoundariesAreDenseInOriginMass.lean`). Every continuous class reading into a
    Hausdorff space is constant; neither faithful compact-open Xi comparison nor full-Hasse
    convolution admits continuous recovery there (`OriginHilbertCohomologyObstruction.lean`).
    Every cohomological reading with dense normed image has full product graph closure with
    origin L2. This includes every finite full-Xi-jet packet and the entire faithful operator
    range; the finite closed graph is single-valued exactly for the empty packet
    (`EveryFiniteMeyerJetGraphIsDenseInOriginHilbertSpace.lean`).

### Odd ledger, floors, sections
22. **Odd-sector ledgers** (reflected-prime/polar, Chebyshev $E(s)$): identities. **Degree floor = width:**
    $-75e^r$, $-(3+\varepsilon)e^r$, dlVP Sobolev; floor rate sets are exactly $[\text{width},\infty)$ in the Sobolev
    normalisation (attained); over $\mathbb F_q$ the $L^2$ floor rate is twice the width.
23. **All-parity critical-deficit identity:**
    $\hat Z(F)=(\Omega(0)-2)\|F\|^2+\text{Lévy}+4J(F)+2\int_0^{2A}I(t)\,Da_F(t)dt$, $D=(d/dt-\frac12)^2$; VK floors
    $-Ce^{A-\kappa A^\alpha}(\|F\|^2+\|F'\|^2)$, $\alpha<3/5$.
24. **Section counts.** Prime-power node sections $h^0\ge\dim W-\#\text{nodes}$; polar box DoF − prime node
    count $=E(s)$; odd pole charge cancels; rank counts are reweighting-invariant (not selective),
    Frobenius norms separate $\Lambda$ from the shifted pair.

### Hecke incidence, near-radicals, Gram certificates
25. **Cartesian / rank-$P$ Kronecker law** of Hecke incidence; resonator remainders negative for $|P|\le3$;
    intra/cross-tower collar bounds; finite-Euler-product lattice form PSD iff $\kappa\ge\sum E_p$; comb
    aggregate is a mean field (no polynomial adjunction bound); successor cell meets only via the collar.
26. **Infinite genus.** No compact test annihilates all but finitely many zeros; over $\mathbb F_q$ the radical
    is the Frobenius ideal $P(T_q)g$ opening at aperture $d\log q/2$; over $\mathbb Q$ the near radical is
    finite-dimensional with two-sided Landau–Widom count $(2\mp\eta)e^{2L}$.
27. **Rank–trace inertia.** Without effectivity a Gram functional certifies a proportion: $(2-\kappa)N$ simple
    critical zeros; coalescence blind spot at $c=2$; $>2/3$ below pair correlation, never $3/4$ there;
    $3/4$ needs a spectral slack or coalescent surplus $\beta\le1/18$ (TTPC); corpus upgrades ($66/1000$).
28. **Which data force the sign** over $\mathbb F_q$: Rosati invariance ⇔ pole-subtracted Hasse–Weil ⇔ forward
    light-cone Bézout; one-sided Lefschetz bounds force purity except upper bounds at real zeros; genus
    one: Hasse = degree positivity of $\mathbb Z[F]$ (theorem of the square), which Hecke scales of $\mathbb Z$ lack.

---

## 5. Pillar theorems

1. Scaling Hodge index = RH; signature law (`scalingSurface_hodgeIndex_iff`, `riemannHypothesis_iff_one_positive_square`).
2. Pontryagin law (`pontryagin_law`, `zeta_hodgeDefect_iff`, `pontryagin_law_curve`).
3. Calibration and fakes (`hodgeIndexOnSpan_iff_unitary`, `curve_hodgeIndex_tfae`, `goldenDatum_negIndex_spanGram`).
4. Degree filtration, finiteness for $\zeta$ (`iSup_hodgeDefectAt`, `hodgeDefectAt_zeta_le_shannon`, `re_W_zeta_nonneg_of_lowGrid`).
5. Cyclic and tower laws (`cyclic_pontryagin_law`, `riemannHypothesis_iff_twoPrime_negIndex_eq_zero`,
   `almost_every_prime_tower_sees_every_right_zero`, `one_prime_vs_two_primes_complete_law`,
   `exists_symmetric_wolff_toeplitz_blind_configuration`, `zeta_one_prime_tower_law`,
   `riemannHypothesis_iff_onePrime_towers`, `zeta_exists_test_riemannHypothesis_iff`,
   `zeta_lefschetz_growth_law`, `zeta_riemannHypothesis_iff_universal_minors`, `tower_law`,
   `rightZeros_eq_empty_iff_twoWindow`).
6. Effectivity and Bézout (`exists_effectivity_iff_hodgeIndex`, `exists_bezout_effectivity_iff_hodgeIndex`,
   `localPair_nonneg`, `riemannHypothesis_iff_exists_effectivity`).
7. Source-cone laws (`gradedSourceCone_riemannRoch_iff_le_defect`, `gradedL2SourceCone_realTestsAt_all_apertures_riemannRoch`,
   `lowBlindTests_effectivity`, `zetaZeroWidth_le_iff_gradedSobolevSourceCone_riemannRoch`).
8. Universal floor law and Hecke rigidity (`riemannRoch_iff_openPositiveCone_subset_and_defect_nonneg`,
   `scalingSurface_hodgeIndex_iff_heckeCorrespondence_openPositiveCone_ample`, `goldenDatum_not_rosatiSourceCone_riemannRoch`).
9. Degree floor = width (`fullDefectFloorRates_eq_Ici`, `oddDefectFloorRates_eq_Ici`).
10. Near-radical law (`zeta_landau_widom_two_sided_dimension_law`, `exists_radical_test_iff`).
11. Gram certification (`universal_gram_certification_classification`, `HD_one_lt_three_quarters`).
12. Forcing data (`forcing_arithmetic_data_tfae`, `oneSided_forcing_tfae`).

Meyer carrier anchors are module-level: `MeyerSourceIntersectionSurface.lean`, `BoundedMeyerSourceSurface.lean`,
`MaximalBlindIdealOfTheMeyerSource.lean`, `HarmonicCouplingForcesSourceBlindness.lean`,
`FaithfulPositiveMeyerDegrees.lean`, `FiniteReadingsAndMassCannotSupplyBezout.lean`.
Bounded-orbit and reserve results are in `MeyerBoundedCenteredOrbits.lean`,
`MeyerCriticalTopAlgebra.lean`, `FaithfulHilbertSchmidtSourceReserves.lean`,
`MeyerHilbertReserveFlowRigidity.lean`, and `BoundedMeyerFaithfulReserve.lean`.

---

## 6. Traps

| Trap | Truth |
|---|---|
| Adjunction is missing | It is exact; Riemann–Roch is missing |
| Weil needs $\Gamma^2$ exactly | Only the lower bound; free $\Gamma^2$ bounds nothing |
| Span data force Hodge index | Fake data satisfy them all and fail |
| Positive tests are effective | Bézout yes, RR no |
| `riemannHypothesis_iff_exists_effectivity` is progress | A reformulation; progress = effectivity defined without the sign |
| Open/closed positive cones settle ampleness/RR | Their other axiom is Hodge index |
| A source-defined cone escapes the estimate | Its RR is exactly a coercive floor |
| Subexponential floor is a reduction | It is equivalent to RH; power savings are strips |
| Odd ledger is a positivity mechanism | It is the explicit formula rewritten |
| Cyclic law bounds the defect | It localises it |
| One prime always sees everything | Over all tests yes, for every tempered configuration (density); one fixed test can be Wolff-blind, and resonances merge eigenvalues |
| Multiplicities count | The defect counts distinct right zeros |
| A finite degree certifies positivity | Over $\mathbb Q$ no degree works for all configurations |
| Finitely many readings plus mass give Bézout | Rayleigh quotients unbounded in every finite kernel |
| A bigger arithmetic reserve helps | Extra reserve gives Bézout but kills RR |
| Single-channel positivity beyond the blind ideal | Exhausted by off-line blindness; needs harmonic coupling, which hits the Fejér barrier |
| Adams operations make a Weil surface | Golden datum has them too |
| 3/4 modules prove 75% | Conditional on slack or coalescent surplus |
| Rank-based section counts are selective | Reweighting-invariant; use norms or $E(s)$ |

---

## 7. Open problems

1. **Riemann–Roch for $\mathbb Z$ (open core).** Close the finitely many low-frequency directions read by $D_a$
   and the pole, at every degree, by an effectivity defined without the sign of the form
   (equivalently $0\le\delta(x,x)$ there).
2. **An arithmetic section law.** A source-defined cone whose RR follows from a law of its sections
   (count, vanishing, RR-type inequality) rather than the floor, reducing over $\mathbb F_q$ to Weil's.
3. **Degree floor below rate ½** (= strip): which effectivity input lowers the rate before the sign?
4. **Beyond 2/3 and HD(1)**: spectral slack $\ge N/12$ near $\lambda=1$, or coalescent surplus $\beta\le1/18$, or
   $F\le B$, $B\le2954/1035$ (owned by TTPC).
5. **One prime against two** — resolved: for every tempered configuration and scale the towers of
   tests carry every distinct outer eigenvalue (`tower_law`); one test carries an infinite defect
   when the closed folded spectrum is countable (`exists_test_tower_law_of_countable_folded`).
   Open: one test carrying an infinite defect across an uncountable folded spectrum (a wall). Tool:
   light Blaschke walls are permeable — Blaschke poles with `Σ|ν|/(1 − |a|) < ∞` cannot cancel
   behind the circle (`HTGeometry/LightBlaschkeWallsArePermeable.lean`).
6. **Clustering branch** of the visibility/defect-rate dichotomy (unrestricted $L^2$, not Sobolev).
7. **Lattice → continuum**: carry finite-Euler lattice positivity to Weil's form with collar and signed
   coefficients.
8. **Beyond the maximal blind ideal**: a multi-channel (harmonic-coupled) positivity mechanism that
   passes the Fejér barrier $a_1<2a_0$ — i.e. goes beyond classical zero-free-region coupling — on a
   sharp-stable carrier containing off-line-visible sources.

---

## 8. Tools

Polar surfaces; $\mathbb F_q$ calibration (curve data, Toeplitz spans, Pontryagin, fakes, period quotient,
Frobenius ideal); scaling surface signature/Pontryagin/sectors/degree filtration; visibility calculus;
Kronecker-rank dichotomy; cyclic density and prime towers (Laurent moments, `wfVisibleSet`, Wolff
counterexamples); Bézout via Lévy jump form; source cones and boundary rigidity; Hecke incidence
and multi-tower collar; rank–trace inertia; λ-ring and Hecke–Lefschetz rigidity; odd ledger and
section counts; Landau–Widom near-radical calculus; annihilating tests for sparse spectra; Meyer
source carrier (Poisson cycles, trace degrees, bounded orbits, blind ideal, harmonic coupling,
faithful degrees, finite-reading obstructions).

---

## 9. Success criteria and principles

Success: an effectivity whose ampleness is proved without the sign of the form and which satisfies
RR, or a proof that no cone from a stated class of arithmetic data has both — reducing over $\mathbb F_q$
to Weil. A contribution names the Weil ingredient it concerns, states what it gives for fake data,
non-$\Lambda$ weights and positive tests, runs first over $\mathbb F_q$, gives identities where Weil's step is an
identity, and records the positive survivor of every no-go.

Principles: compute, then bound; audit hypotheses against fake data; fix the source ($\Lambda$, pole weight
one), not the sign; calibrate over $\mathbb F_q$; separate metrology (what a degree sees) from geometry (what
a cycle is); a reformulation is not a reduction; search the corpus first.
