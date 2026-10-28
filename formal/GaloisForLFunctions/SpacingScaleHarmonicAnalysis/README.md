# Arithmetic Harmonic Analysis at the Spacing Scale (SSHA)

Namespace `GaloisForLFunctions.SpacingScaleHarmonicAnalysis`; umbrella `SpacingScaleHarmonicAnalysis.lean`.

**Question.** The prime and archimedean places of $\mathbb Q$ regularize the same diagonal. On a test built from narrow atoms at $\log n$,
$n\le N$, the archimedean place pays a self-energy $\log(1/w)$ per unit mass and the prime place charges at most $\log N$. Below the
spacing $\delta_N=\log(1+1/N)$ nothing arithmetic is seen; at the spacing the divergences match; beyond it atoms overlap and tests see
the zeros. **How far does the archimedean place pay the prime place, what does the matching leave, where does positivity stop
being unconditional, and where does a form first see the arithmetic gauge?**

**Object.** The **atomic family**: tests $f_x=\sum_{n\le N}x_ng(\cdot-\log n)$ from one bump $g$ of width $w$, read through the **overlap ratio**
$\varrho=w/\delta_N$.

> At the spacing every divergence is matched with constant one; what remains is a joint estimate between the archimedean
> cross kernel (large only at the top scale) and the prime kernel (large only across scales). A Schur weight tilted across
> scales separates them: Weil's form is nonnegative up to the pole on atomic tests of width $c_0\delta_N$, every $N$; without the pole
> it fails at every width $c\delta_N$, $c>e/(2\pi)$. Once the overlap beats $(\log\log N)^{1+\varepsilon}$, narrow atoms synthesize every fixed test and
> positivity *is* RH: the critical exponent is one, the decisive scale is bounded overlap, and RH says the pole remains the only
> negative square.

---

## 1. Place in the research

Every positive mechanism of the corpus stops at a threshold, and the thresholds line up at the spacing scale: where the
archimedean place stops paying for free, where the gauge becomes visible, where tests see zeros up to height $\asymp N$.

| Programme | Takes / adds |
|---|---|
| ArithmeticElectrostatics | Atomic tests, $\text{primeSum}=(\int g^2)P_N$ below spacing, stability at $N^{-O(1)}$ / stability at a fixed fraction of the spacing |
| RenormalizedArithmeticPotentialTheory | Covariant counterterm $\log N+O(1)$, finite part / tilted rows; exact Robin constant |
| ArithmeticIntersectionTheory | Tower coordinates, gauge blindness / archimedean side at width $c\delta_N$; non-ratio lags |
| BiarithmeticGaugeGeometry | Sign twins / diamagnetic inequality |
| ArithmeticOrientationGeometry, ArithmeticCastelnuovoSeveri | Spline orbit, Weil Grams of translates / same law on atomic families |
| ArithmeticLorentzianGeometry | Metzler sign below spacing, frustration beyond / analytic inputs (Lévy–Markov form, overlap law) |
| `RHTower` (Weil–Markov) | $\text{archForm}=2\theta'(0)\|f\|^2+\text{levyEnergy}$, Markov property, Euler–Maclaurin |
| SquareRootThreshold, SelectivePositivityAndThresholdLaws | Aperture positivity; Liouville failure at $23/40$ |

---

## 2. Why

**Two divergences.** Prime place: $P_N(x)=\sum_{m\mid n}x_mx_n\Lambda(n/m)(n/m)^{-1/2}$, norm $\log N+O(1)$ attained on the pole vector $n^{-1/2}$.
Archimedean place: Lévy energy $\int\omega(y)\|f-f(\cdot+y)\|^2dy$, $\omega(y)=e^{-y/2}/(1-e^{-2y})\sim1/(2y)$: an atom costs $\log(1/w)$, constant one. At $w\asymp1/N$ they coincide.

**Three regimes.** (1) Below the spacing: self-energy dominates every cross term. (2) At the spacing: atoms disjoint, prime sum
exactly $(\int g^2)P_N$, but the archimedean **cross kernel** $\approx wn/(n-m)$ has row $\approx c(m/N)\log N$ while the margin $\log(1/c)$ is bounded: no
diagonal argument closes, a joint estimate does. (3) Beyond: atoms overlap, non-ratio lags $\log k\approx\log(n/m)$ enter.

**Nyquist reading.** $\hat f_x=h_gD_x$ with the Dirichlet polynomial $D_x$; zero density at height $T$ is $\log T/2\pi$, Nyquist density of length-$N$
polynomials is $\log N/2\pi$; they match at $T\asymp N$, i.e. $w\asymp\delta_N$. **The spacing scale is the Nyquist scale of the atomic family.**

---

## 3. Objects and language

| Object | Lean |
|---|---|
| Atomic test, atomic Weil prime form | `atomicTest`, `atomicWeilForm` |
| Lévy density, Lévy energy, Lévy–Markov form | `archLevyDensity`, `levyEnergy`, `levyMarkovForm` |
| Markov energy $M=\text{archForm}-\text{primeSum}$; Weil quadratic $Q$ | `markovEnergy`, `weilQuad` |
| Tilt $r(n)=1+n/N$ | `atomicWeilForm_le_tilted` |
| Lag forms, non-ratio form $NR_w$ | `lagForm`, `primeSum_atomicTest_eq_ratio_add_nonRatio` |
| Overlap growth (orders), stable forms | `riemannHypothesis_iff_atomicFamilies_nonneg_of_growth` |
| Robin constant of an atom; two-atom pairing | `archRobinConstant_eq`; modules `TheRobinConstantOfAnAtom`, `TheArchimedeanPairingOfTwoAtoms` |
| Universal threshold $K_{\rm univ}$ | `universalThreshold_finite` |

**Words.** *Width*, *spacing*, *overlap ratio*; *ratio lag* ($n=km$) vs *non-ratio lag*; *stable form* (translation invariant, moved by
$o(1)$ under small $C^2$ perturbations with Lévy control); *synthesis* (atoms reproducing a fixed test); *alias ripple*; *pole
hyperplane* $m_-=\int ge^{-u/2}=0$.

---

## 4. Mechanisms

1. **Constant one on both sides**: $1/(2y)\le\omega(y)\le e^{y/2}/(2y)$; atom self-energy $(\log(1/w)+O(1))\|g\|^2$; prime Schur rows $\le\log N+O(1)$.
2. **Cross-kernel law**: row at atom $m$ $\le4e^{5/2}wm(1+\log(N+1))$; inverse-square increment control of $\omega$.
3. **The tilt**: with $r(n)=1+n/N$ the down tower loses $\ge(m/4N)\log m$ (every proper divisor is at most half way down), the up tower gains $\le\log4+4$:
   $P_N(x)\le\sum x_m^2(\log N+C-(m/4N)\log m)$. Power weights cannot do this.
4. **Payment scale by scale**: at $w\le c_1/N$ the down-tower saving pays the cross kernel atom by atom ⇒ $M\ge0$ and $\Re W+2S^2\ge0$ at $w\le c_0\delta_N$.
5. **Diamagnetic inequality**: Lévy energy is a Dirichlet form, so $\zeta$ is the ground state of its gauge orbit; the spacing law holds for every
   real twist $|\omega|\le1$ — it carries no arithmetic beyond $|a(k)|\le\Lambda(k)$.
6. **Non-ratio lags**: $\text{primeSum}=\|g\|^2P_N+NR_w$; the gauge defect lives only on non-ratio lags (none below spacing, some within $4\delta_N$); at bounded
   overlap three rows of shape $(m/N)\log N$ compete (tilt saving, cross kernel, non-ratio lags).
7. **Synthesis**: cell / trapezoid / Euler–Maclaurin weights reproduce a fixed test with errors $O(1/\varrho)$, $O(1/\varrho^2)$, $O(\varrho^{-p})$; in $s=e^t$ the atoms are
   the integers. Gevrey and Denjoy–Carleman profiles push the threshold to $(\log\log N)^{1+\varepsilon}$. Weil's form is continuous in the Lévy
   norm, so synthesis transfers every stable form's sign.
8. **The pole is the correction**: $M=Q-2m_-m_+$; synthesis carries both $M$ and the pole hyperplane to atomic families.
9. **One zero weighs at most the overlap ratio** (Cauchy–Schwarz on the two Dirichlet factors).
10. **Finite part on the pole vector**: Rayleigh quotient $(\log(1/c)+\beta(\varphi)/\|\varphi\|^2-\log2\pi)\log N$; $2c_\infty=2\log2+\pi/2$; Euler's constant cancels.

---

## 5. Pillar theorems

1. **Constant one** (`archLevyDensity_ge_inv_two_mul`, `levyEnergy_atom_ge`, `levyEnergy_atom_le`).
2. **Cross-kernel law; tilted rows** (`levyEnergy_atomicTest_ge`, `atomicWeilForm_le_tilted`).
3. **Stability at the spacing, universal over twists** (`re_W_add_sinh_sq_nonneg_spacing`, `markovEnergy_atomicTest_nonneg_spacing`,
   `twistedMarkov_atomicTest_nonneg_spacing_of_abs_le`).
4. **Diamagnetic inequality** (`diamagnetic_inequality`).
5. **Unbounded overlap is RH**; negative index counts right zeros (`riemannHypothesis_iff_splineAtomic_negIndex_eq_zero_of_width`).
6. **Overlap law**: for every smooth (Gevrey, Denjoy–Carleman) profile and overlap growth of any order, RH ⇔ eventual nonnegativity on atomic
   families; a twist is seen iff it is not Weil positive (Liouville, $c\Lambda$, quadratic mixtures fail); RH ⇔ $M\ge0$ on atomic tests in the pole
   hyperplane (`riemannHypothesis_iff_atomicFamilies_nonneg`, `weilPositive_iff_atomicFamilies_nonneg`, `markovThreshold_bracket`).
7. **The Markov form fails inside the separated regime** for $c>e^{\beta/\|\varphi\|^2}/(2\pi)$; plateau profiles give every $c\in(e/2\pi,1)$ (`archRobinConstant_eq`).
8. **The universal threshold is finite**: some sign twist fails $\Re W_\omega+2S^2\ge0$ at a finite overlap; $c_0\le K_{\rm univ}<\infty$ (`universalThreshold_finite`).
9. **Dictionary and weight of one zero** (`paperFT_atomicTest`, `norm_Wsummand_atomicTest_le`).

---

## 6. Traps

| Trap | Truth |
|---|---|
| The self-energy constant does not matter | With $e^{-1/2}$ positivity stops at $N^{-O(1)}$; constant one reaches the spacing |
| At the spacing the cross kernel is lower order | Its row is $\asymp c(m/N)\log N$, as large as the margin is small |
| A uniform or power Schur weight works | Only a tilt across scales pays the down tower |
| Stability at the spacing is RH | It is a theorem (positive Nyquist margin) |
| A fixed-width family is "near the spacing" | Its overlap is unbounded; positivity there is RH |
| RH-strength needs polynomial overlap | $(\log N)^\varepsilon$, even $(\log\log N)^{1+\varepsilon}$, suffices |
| At bounded ratio atoms reproduce smooth tests | Only up to an alias ripple whose Lévy cost grows like $\log N$ |
| Gauge selectivity can come from the Markov form | $\zeta$ is its ground state; only the pole is anti-Markovian |
| Twins differ from $\zeta$ on every lag | Only non-ratio lags carry the gauge |
| The rank-one pole correction is a method artifact | The Markov form alone fails at $c>e/(2\pi)$ |
| Universal methods reach every bounded overlap | $K_{\rm univ}<\infty$ |
| A twin positive at the spacing stays positive beyond | Liouville is stable at $c_0\delta_N$ and fails under overlap growth |

---

## 7. Open problems

1. **The critical constant** $c_M^*\in[c_0,e/(2\pi)]$ of the Markov form (cross-term density on the pole vector; the profile minimizing $\beta/\|\varphi\|^2$), and
   the critical constant of $\Re W+2S^2$, where the pole decides.
2. **The window below $(\log\log N)^{1+\varepsilon}$**: the alias fraction $A(\varrho)$ of the best synthesis; whether RH-strength begins at $A(\varrho)\log N\asymp1$; whether any
   growth $\varrho_N\to\infty$ suffices; at fixed $\varrho$, a Nyquist penalty making every twist's Weil form positive on bounded-aperture atomic tests.
3. **Gauge margin at bounded overlap**: a signed test separating $\zeta$ from every twin flipping a prime $\le p_N$ with margin bounded below, from
   non-ratio lags — first Liouville at overlap $\approx e^{23/40}$.
4. **Interior anti-alignment**: the outward reserve of an off-line zero as a large value of $D_x$ at its ordinate.
5. **A Hecke-covariant tilt surviving overlap.**
6. **A large sieve over the zeros**: frame constants of the zeros for length-$N$ Dirichlet polynomials as functions of $wN$ and $T/N$.

## 8. Tools to build

The cross-term density of the pole vector; the archimedean cross kernel of overlapping atoms with constants (to close the
joint estimate at fixed $K$); the alias fraction at bounded overlap; a large sieve over the zeros.

## 9. Contribution standard

State width, spacing and overlap ratio of every statement; separate ratio from non-ratio lags; say whether a law is universal
over twists (diamagnetic) or selective; report the pole correction rank; unconditional, with RH only inside equivalences.
