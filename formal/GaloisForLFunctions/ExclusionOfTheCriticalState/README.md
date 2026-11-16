# Exclusion of the Critical State (ECS)

Namespace `GaloisForLFunctions.ExclusionOfTheCriticalState`; umbrella `ExclusionOfTheCriticalState.lean`.

## 1. Motivation

Weil's form, restricted to real tests on the half-line $u<0$ and confined by the weight $e^{-8u}$, has a
**critical state** exactly when RH fails: either RH holds, or the global window threshold $W_0$ is finite
and a unit profile $F$ attains the confined form's zero at ratio $W_0$
(`riemannHypothesis_or_exists_criticalHalfLineGroundState`, AHD). The state is unique up to sign,
solves the weak Euler–Lagrange equation on the actual energy domain, and its Laplace transform has no
zero on $\operatorname{Re} w\ge0$. RH is the statement that **one explicit function does not exist**.

ECS turns this into a field. It writes the state's equation in coordinates where the arithmetic is
visible, makes every exact property of the state a theorem, and looks for the property that contradicts
the arithmetic of $\zeta$. Each result is a reduction "no function with properties $P_1,\dots,P_k$
exists $\Rightarrow$ RH" with a growing list of properties. At the state every relation is an identity,
so nothing is lost between stages.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Energy domain $\mathcal H$ | `CriticalHalfLineEnergyDomain` (AHD) | $F$ on $u<0$; $F,F^2,F^2e^{-8u}$ integrable; finite Gamma energy |
| Transform | `negativeHalfLineLaplace (cx F)` | $\mathcal LF(w)=\int F(u)e^{wu}du$ |
| Bare / full / mixed form | `bareHalfLineEnergy`, `bareMixedEnergy`, `criticalHalfLineFullEnergy`, `criticalHalfLineMixedEnergy` | Weil's form; $Q_R=B+a(R)W_8$, $W_8=\int F^2e^{-8u}$ |
| State | `IsCriticalHalfLineGroundState` (AHD) | the unit null direction of $Q_{W_0}$ |
| Probes | `probe p` | $e_p(u)=e^{pu}\mathbf 1_{u<0}$; in $\mathcal H$ for $p>4$ |
| Probe symbol | `probeSymbol` | $D(p)=\xi'/\xi(\tfrac12+p)$ written with poles, digamma and $\Lambda$ |
| Holomorphic state equation | `stateEquation`, `stateGamma`, `stateTail` | $\alpha\mathcal LF(p-8)+\Gamma F(p)+\mathcal LF(p)\tfrac{\zeta'}{\zeta}(\tfrac12+p)-TF(p)+\text{pole}(p)$ |
| Cleared equation | `stateEquationCleared` | the same with $\zeta(\tfrac12+p)$ multiplied through |
| Pole-free remainder | `stateRemainder` | the equation minus $\alpha\mathcal LF(p-8)$, written with $(s-1)\zeta(s)$ and a divided difference at $\tfrac12$ |
| Tail measure | `tailMeasure` | $F(-v)\,dv$ on $v>T$, for Landau's theorem |
| Lévy pairing | `levyGamma`, `levyKernel`, `levyTail` | $\Gamma F(p)=2\theta'(0)\mathcal LF(p)+\int_0^\infty\omega(x)\big[\mathcal LF(p)(2-e^{-px})-e^{px}\!\int_{u<-x}Fe^{pu}\big]dx$ |
| Lévy symbol, heads | `levySymbol`, `levyHead`, `levyHeadTerm` | $g(p)=\int\omega(x)(2-e^{-px}-e^{px})dx$; $H_x(p)=\int_{-x}^0Fe^{pu}$; $JF(p)=\int\omega(x)e^{px}H_x(p)dx$ |
| Prime heads | `primeHead` | $\hat SF(p)=\sum\Lambda(n)n^{p-1/2}H_{\log n}(p)$ |
| Three remainders | `levyRemainder`, `stripRemainder`, `leftRemainder`, `globalRemainder` | the remainder right of, on, and left of $\operatorname{Re}p=-\tfrac12$ |
| Continuations | `stateContinuation`, `levyContinuation`, `stateMeromorphic` | $-R(w+8)/a$ on $\operatorname{Re}w>-8$, $>-\tfrac{17}2$, and on $\mathbb C$ |
| Entire state product | `stateXiProduct` | $E(w)=\xi(w+\tfrac{17}2)\mathcal LF(w)$, extended across the shifted zeros |
| Averaged state | `averagedState`, `averageSymbol` | $A(t)$: exponential averages of $F(-\cdot)$ at the rates $9,\dots,12$; $\int_0^\infty A(t)e^{-zt}dt=\mathcal LF(z)/((z+9)(z+10)(z+11)(z+12))$ |
| Heat test, heat kernel | `stateHeatSymbol`, `stateHeatKernel` | $e^{\varepsilon p^2-pT}$; $k_\varepsilon(x)=(4\pi\varepsilon)^{-1/2}e^{-x^2/4\varepsilon}$ |
| Heated state | `heatedState` | $\int k_\varepsilon(u-T)e^{-8u}F(u)\,du$ |
| Profile beyond the wall | `beyondWallProfile`, `heatedBeyondWall` | $F^+$ on $x>0$: archimedean head, prime heads and the two charges, with $\mathcal LF(w)=\int_0^\infty F^+(x)e^{(w+8)x}dx$ for $\operatorname{Re}w<-9$; its heat average |
| Centred zeros, zero sum | `centredZero`, `zeroSum` | $z=\rho-\tfrac12$ with multiplicity; $ZF(p)=\sum_z\mathcal LF(z)\big(\tfrac1{p-z}-\tfrac1{1-z}\big)$ |
| Divided-difference sum | `dividedTerm`, `dividedSum` | $\Delta F(p)=\sum_z\big(\tfrac{\mathcal LF(z)-\mathcal LF(p)}{p-z}-\tfrac{\mathcal LF(z)}{1-z}-\tfrac{\mathcal LF(p)}{z}\big)$, holomorphic at the zeros |
| Defect | `explicitDefect`, `rightFormDefect`, `stripFormDefect`, `entireDefect` | $BF(1)-BF(p)+ZF(p)$ with $BF=$ `globalRemainder`, and its pole-free forms |
| Nonpositive cone | `NonpositiveUnitTest`, `confinementBound` | smooth unit half-line tests with $Q_R\le0$ |

## 3. Language

- **Probe identity**: the weak equation tested on $e_p$. **Prime coordinates**: the probe identity with
  the prime part split into the Euler term $\mathcal LF(p)\sum\Lambda(n)n^{-1/2-p}$ and the prime tail
  $TF(p)=\sum\Lambda(n)n^{p-1/2}\int_{u<-\log n}F(u)e^{pu}du$.
- **Seen zero**: a zero $z=\rho-\tfrac12$ with $\mathcal LF(z)\neq0$; all zeros with $\operatorname{Re}z\ge0$ are seen.
- **Decay exponent** $b^*=\sup\{b:\int F^2e^{-bu}<\infty\}$; **holomorphy abscissa** $\kappa^*$ of $\mathcal LF$.
- **Critical ratio** of $Q_R$: a ratio where a null direction appears; **index** at $R$: the largest
  orthonormal family in the nonpositive cone.
- **Soft property**: holds for the states of every symmetric configuration. **Arithmetic property**:
  fails on a named model (prime-two deformations, positive Euler twins).

## 4. Mechanisms

1. **Probe calculus.** On probes each part of Weil's form is a function of $p,q$: pole part
   $(\frac1{p\pm1/2},\frac1{q\pm1/2})/(p+q)$, prime part $-(\zeta'/\zeta(\tfrac12+p)+\zeta'/\zeta(\tfrac12+q))/(p+q)$,
   Gamma part the Poisson integral of $\operatorname{Re}\psi(\tfrac14+\tfrac{ir}2)$. Their sum is the Carathéodory
   kernel $\frac{D(p)+D(q)}{p+q}$, and the two-channel resolvent identity makes it the zero sum: the
   explicit formula holds on the probe span.
2. **Prime coordinates suffice.** The probe identity is a closed formula in transforms of $F$; each term
   continues holomorphically in $p$ (Laplace transform from square moments, Gamma pairing from the
   Gamma energy, prime tail from the confinement mass). Replacing $\sum\Lambda(n)n^{-1/2-p}$ by
   $-\zeta'/\zeta(\tfrac12+p)$ continues the whole equation; no zero-side explicit formula on $\mathcal H$ is needed.
3. **Residue transport.** After clearing $\zeta(\tfrac12+p)$ the equation reads
   $\zeta(\tfrac12+p)A(p)+\mathcal LF(p)\zeta'(\tfrac12+p)=0$. At a zero $\rho$ the residue of $\zeta'/\zeta$ forces
   $m_\rho\,\mathcal LF(\rho-\tfrac12)=0$ unless $A$ is singular at $\rho-\tfrac12$, i.e. unless $\mathcal LF$ is
   singular at $\rho-\tfrac{17}2$. The pole of $\zeta'/\zeta$ is transported eight units to the left.
4. **Landau.** A one-signed tail makes the real point of the abscissa singular. The remainder, written
   with $(s-1)\zeta(s)$ and the divided difference of $\mathcal LF$ at $\tfrac12$, is holomorphic near the real
   segment because $\zeta$ has no real zero in $(\tfrac12,1)$; so the abscissa is at most $-8$.
5. **Confinement compactness.** On the nonpositive cone, $Q_R=Q_{2R}+\tfrac{a(R)}2W_8$ and $\lambda(2R)$ bound
   $W_8$; bounded confinement and energy are $L^2$-compact, and orthonormal families are $\sqrt2$-separated.
6. **Lévy continuation.** Polarizing the Lévy–Khintchine form of the Gamma energy and evaluating on a probe
   gives a Gamma pairing whose density $\omega(x)\sim e^{-x/2}$ makes it holomorphic on $\operatorname{Re}p>-\tfrac12$;
   the continuation crosses the critical line without deforming a contour.
7. **The functional equation in Lévy form.** On the imaginary axis $2\theta'(0)+g(ir)=2\theta'(r)$ and
   $\zeta'/\zeta(\tfrac12+ir)+\zeta'/\zeta(\tfrac12-ir)=-2\theta'(r)$; the identity theorem, applied to the product cleared of
   $\zeta(\tfrac12\pm p)$, gives $2\theta'(0)+g(p)=-\big(\zeta'/\zeta(\tfrac12+p)+\zeta'/\zeta(\tfrac12-p)\big)$ on $|\operatorname{Re}p|<\tfrac12$. With
   $\int_{u<-x}=\mathcal LF-H_x$: $\Gamma F(p)=-\mathcal LF(p)\big(\zeta'/\zeta(\tfrac12+p)+\zeta'/\zeta(\tfrac12-p)\big)+JF(p)$.
8. **Euler cancellation left of the strip.** For $\operatorname{Re}p<-\tfrac12$ the prime tail is
   $-\mathcal LF(p)\zeta'/\zeta(\tfrac12-p)-\hat SF(p)$ (Dirichlet series of $\Lambda$ at $\tfrac12-p$). Its Euler part cancels the reflected
   Euler term of the Gamma pairing exactly, and the remainder is $JF+\hat SF+\mathcal LF(\tfrac12)/(p-\tfrac12)+\mathcal LF(-\tfrac12)/(p+\tfrac12)$:
   left of the strip the state is its head term, its prime heads and its two charges.
9. **Pole removal.** $ZF(p)=\Delta F(p)+\mathcal LF(p)\,\xi'/\xi(\tfrac12+p)$, and $\Delta F$ converges absolutely and is
   holomorphic on $\operatorname{Re}p>-2$, zeros included. With $(s-1)\zeta(s)=2\xi(s)/(s\Gamma_{\mathbb R}(s))$ the Euler term of the
   remainder is $\mathcal LF\cdot(\xi'/\xi-1/s-\Gamma_{\mathbb R}'/\Gamma_{\mathbb R})$, so the defect $BF(1)-BF+ZF$ has no pole: one
   pole-free form right of $\operatorname{Re}p=-\tfrac12$, one on $-2<\operatorname{Re}p<\tfrac12$ with the reflected Euler factor.
10. **Liouville on the defect.** The Lévy pairing and the regular part grow linearly on $\operatorname{Re}p\ge0$, heads
   and tails are bounded on their half-planes, $\Gamma_{\mathbb R}'/\Gamma_{\mathbb R}$ is linear, both sums are quadratic. The glued
   defect is entire of order $O(|p|^2)$, vanishes at $1$ and is $o(|p|)$ along the negative axis; its
   divided difference at $1$ is zero. No bound for $\zeta'/\zeta$ inside the strip is used.
   The cleared state product $E$ is entire. At a seen zero $z=\rho-\tfrac12$ of multiplicity $m$,
   $E$ has order exactly $m-1$ at $z-8$: in $\xi R+\mathcal LF\,\xi'$, only the derivative term contributes
   to the leading jet. Conversely, $E$ has order at least $m$ there exactly when $\mathcal LF(z)=0$.
11. **Bounds off the zeros and the averaged line shift.** At distance $\delta$ from the zeros
   $|ZF(p)|\le C(1+|p|)(1+|p|/\delta)$, so the continuation is $O(|w|^2)$ on every vertical line off the
   pole strip. An exponential average of the state at four rates divides the transform by a quartic;
   the inversion line then moves from $\operatorname{Re}w=1$ to $\operatorname{Re}w=\kappa'-8$ for every $\kappa'$ above the
   real parts of the centred zeros. The raw transform does not decay on these lines, so the unaveraged
   $L^2$ law needs more than the width of the zero strip.
12. **Two lines weigh the zero values.** For entire $H$ of fourth-order decay on $a\le\operatorname{Re}p\le b$,
   $a\le-1$, $1\le b$: $\sum_z\mathcal LF(z)H(z)=\frac1{2\pi}\big(\int_{\operatorname{Re}p=b}H\,BF-\int_{\operatorname{Re}p=a}H\,BF\big)$. The zero
   sum integrates term by term and the constant of the explicit formula drops out. For the state the
   right line carries $\mathcal LF$ and the left line its continuation. With $H=e^{\varepsilon p^2-pT}$ each line
   integral is a heat average (Fubini and one Gaussian integral): the series $\sum_z\mathcal LF(z)e^{-zu}$ is
   $-a\,e^{-8u}F(u)$ left of the wall and $a\,F^+(u)$ beyond it.

## 5. Questions

| # | Question | Status |
|---|---|---|
| Q1 | Probe kernel $B(e_p,e_q)=\frac{D(p)+D(q)}{p+q}$ and its zero side | answered (Lean) |
| Q2 | Zero side of $B$ on all of $\mathcal H$; zero-coordinate form $(\star)$ | partial (Lean): probe and heated zero-side identities; two general profiles open |
| Q3 | State equation, continuation, residues | answered (Lean): global meromorphic continuation, exact residues and uniform left decay |
| Q4 | Decay law | partial (Lean): divergent law, left Hardy bounds and averaged/heated decay; unaveraged $L^2$ law open |
| Q5 | Sign law | answered (Lean): one sign on no ray |
| Q6 | Index law | $\zeta$: finite index at every ratio (Lean); exact count of critical ratios open |
| Q7 | Rigidity: no state for $\zeta$ | open; equivalent to RH |
| Q8 | The arithmetic property that excludes the state | open |
| Q9 | Wall, collar, charges $\mathcal LF(\pm\tfrac12)$ | partial (Lean): vanishing average wall mass, uniform right $o(1/\sigma)$ decay and charge cancellation; leading asymptotics and exclusion open |

## 6. Tools

**Developed.** Probe calculus (`probe`, moments, confinement pairings, Fourier transform); probe kernel
and zero side on probes; prime-coordinate state equation; holomorphy of Laplace transforms from
square or absolute moments; holomorphy of the Gamma pairing and the prime tail; the cleared equation
and the residue argument; tail measures with Landau's theorem (via the corpus abscissa calculus and
Cauchy estimates); the pole-free remainder across $p=\tfrac12$; confinement compactness of the
nonpositive cone; the Gamma pairing in Lévy form with near/far dominations of the Lévy kernel; the
prime tail on $\operatorname{Re}p>-4$ from the confinement mass; the Lévy symbol and the head term with their
dominations; the functional equation in Lévy form; prime heads and the Dirichlet series of $\Lambda$ left
of the strip; gluing of three remainders into one continuation; $\zeta\ne0$ on $\operatorname{Re}s=0$; the zero-sum
calculus (one subtraction, absolute convergence off the zeros, divided-difference sum, pole removal);
linear growth of every pairing of a profile with a probe; the pole-free forms of the defect, their
gluing and Liouville. Bounds of the pairing and of the
continuation off the zeros; the Volterra–Laplace calculus of exponential averages; the entire product
and its difference equation; two-line weighing of the zero values against entire tests; Gaussian line
integrals of Laplace integrals as heat averages.

**To build.** Vertical square bounds toward the pole strip and their transfer to weighted decay of the original state, for the convergent half of the decay law; the exact critical-ratio count; the leading asymptotics of
$JF$ and $\hat SF$ as $p\to-\infty$ (the wall seen from the left formula); the square-summability of the zero values behind the
unaveraged decay law; $F^+$ in prime form (the remainder of the prime number theorem averaged by $F$)
and its comparison with $e^{-8u}F$ at the wall.

## 7. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| RH or a critical state exists | `riemannHypothesis_or_exists_criticalHalfLineGroundState` (AHD) | inherited |
| Probes lie in the domain | `criticalHalfLineEnergyDomain_probe` | unconditional |
| Probe kernel = Carathéodory kernel of $\xi'/\xi$ | `bareMixedEnergy_probe`, `probeSymbol_eq_logDeriv_xiCent`, `criticalHalfLineMixedEnergy_probe` | unconditional |
| Explicit formula on probes | `bareMixedEnergy_probe_eq_zeroSide` | unconditional |
| State equation on probes | `criticalState_probeEquation` | unconditional (for the state) |
| Holomorphic state equation | `stateEquation_ofReal_eq_zero`, `stateEquation_eqOn_zero`, `stateEquationCleared_eqOn_zero` | unconditional |
| Holomorphy reads the zeros | `zero_re_le_of_laplace_holomorphic` | unconditional |
| Decay ruler | `criticalState_not_integrable_of_zero`, `riemannHypothesis_or_criticalState_decay_ruler` | unconditional |
| Sign law | `criticalState_changes_sign_on_every_ray`, `riemannHypothesis_or_criticalState_changes_sign` | unconditional |
| Finite index at every ratio | `exists_bound_orthonormal_nonpositive` | unconditional |
| Poles of the state = zeros right of the line | `riemannHypothesis_or_criticalState_poles_at_zeros` | unconditional |
| Gamma pairing in Lévy form, holomorphic on $\operatorname{Re}p>-\tfrac12$ | `levyGamma_eq_stateGamma`, `differentiableOn_levyGamma` | unconditional |
| Continuation across the line; a pole at every zero with $\operatorname{Re}\rho\ge\tfrac12$ | `riemannHypothesis_or_criticalState_poles_across_line` | unconditional |
| Functional equation in Lévy form | `levySymbol_eq_neg_logDeriv`, `levyGamma_eq_reflected_euler` | unconditional |
| The state is meromorphic in the plane; prime heads left of the strip | `riemannHypothesis_or_criticalState_meromorphic`, `stateMeromorphic_eq_left` | unconditional |
| The zero sum converges after one subtraction; pole removal | `summable_zeroSum_term`, `differentiableAt_dividedSum`, `zeroSum_eq_dividedSum_add` | unconditional |
| Linear growth of the pairings with a probe | `exists_bound_levyGamma`, `exists_bound_levyRegularPart`, `exists_bound_leftRemainder` | unconditional |
| Explicit formula on the domain against probes | `entireDefect_eq_zero`, `globalRemainder_sub_eq_zeroSum`, `globalRemainder_sub_eq_tsum` | unconditional |
| $(\star)$: the state is the Cauchy transform of its values at the zeros | `criticalState_starEquation`, `criticalState_zeroValues_cauchy`, `riemannHypothesis_or_criticalState_starEquation` | unconditional |
| Exact multiplicities of the entire state product; full multiplicity detects unseen zeros | `criticalState_stateXiProduct_order`, `le_analyticOrderAt_stateXiProduct_iff`, `stateXiProduct_first_nonzero_jet` | unconditional (for the state or energy-domain profile) |
| $\xi(w+\tfrac{17}2)\mathcal LF(w)$ is entire | `differentiable_stateXiProduct`, `riemannHypothesis_or_criticalState_xi_mul_entire` | unconditional |
| $(\star)$ normalised at the left end; the Cauchy system of the zero values | `criticalState_starEquation_normalised`, `criticalState_zeroValues_cauchy_normalised` | unconditional |
| The continuation is $O(\lvert w\rvert^2)$ off the zeros | `norm_globalRemainder_le_of_dist`, `norm_stateMeromorphic_le_of_re` | unconditional |
| The averaged state decays at the rate of the zeros, beyond the barrier | `exists_bound_averagedState`, `criticalState_averaged_decay_beyond_barrier`, `riemannHypothesis_or_criticalState_averaged_decay` | unconditional |
| Two vertical lines cut out the zero series | `hasSum_zeroValues_two_lines`, `criticalState_hasSum_zeroValues_two_lines` | unconditional |
| The zero series is the state left of the wall and the prime side beyond it | `criticalState_hasSum_heated_zeroSeries`, `criticalState_heatedState_add_zeroSeries_le` | unconditional |

## 8. Traps

| Trap | Truth |
|---|---|
| Stability, outerness or cyclicity exclude the state | They hold off RH (killed-route ledger) |
| The state has one sign | It changes sign on every ray (sign law) |
| Continuation of $\mathcal LF$ needs the explicit formula on $\mathcal H$ | Prime coordinates and $\zeta'/\zeta$ suffice |
| Improving the exponential barrier is free | By the decay ruler it is a zero-free half-plane: $b$ yields $\Theta\le\frac{17-b}2$ |
| On-line zeros give a new decay bound $b\le16$ | The state exists only off RH, where off-line zeros already give $b^*<16$ |
| Finite index needs arithmetic | Confinement compactness gives it for every configuration |
| Functional equation + Euler product + positive coefficients exclude | Positive Euler twins retain these and real-axis nonvanishing despite off-line zeros; logarithmic positivity fails |
| The sign law is soft | It uses that $\zeta$ has no real zero in $(\tfrac12,1)$; prime-two deformations can have one |
| The exponent 8 is canonical | Any confinement exponent works; 8 only fixes the shift of the residue transport |
| The Gamma pairing continues only by deforming the Fourier contour | Its Lévy form converges on $\operatorname{Re}p>-\tfrac12$, and its symbol is the functional equation |
| Continuation past the strip needs the explicit formula | Left of the strip the Euler parts cancel; the remainder is head term, prime heads and charges |
| $(\star)$ needs bounds for $\zeta'/\zeta$ on horizontal segments of the strip | Pole removal and Liouville use linear growth of the pairings and $\sum_z\lvert z\rvert^{-2}<\infty$ only |
| $\sum_z\mathcal LF(z)/(w+8-z)$ converges | $\mathcal LF(z)$ is bounded and need not decay; the sum converges after one subtraction, and $(\star)$ is a two-point identity |
| The convergent half of the decay law is a line shift of $(\star)$ | The continuation does not decay on vertical lines; the shift works after averaging |
| $F(u)=-a^{-1}e^{8u}\sum_z\mathcal LF(z)e^{-zu}$ pointwise | The series is a distribution on the line; heated it converges absolutely, and left of the wall it differs from the state by the prime side behind a Gaussian |

## 9. Context

| Neighbour | Interface |
|---|---|
| ArithmeticHodgeTheoryOfDegenerations | stage 0: domain, forms, threshold, state, weak equation, zero-freeness, ground energy, variational compactness |
| CriticalArithmeticCorrelationTheory | Gamma/prime/pole mixed forms, prime-term summability |
| RHTower | $\xi'/\xi$ partial fractions, two-channel resolvent kernel, Poisson–digamma reproduction, Landau abscissa calculus, residues of $\zeta'/\zeta$, $(s-1)\zeta(s)$ |
| HTGeometry | Cauchy estimates and real Taylor coefficients of holomorphic functions, analyticity of $\zeta$ |
| ArithmeticCastelnuovoSeveri | Pontryagin law (negative squares = right zeros) |
| ArithmeticOrientationGeometry | orientation index = seen right zeros |
| FrustratedArithmeticDirichletForms | frustration of the even sector |
| BlackHoleRingdown, SelbergClass, HTGeometry | prime-two deformations, positive twins, Euler-log positivity (O11) |
| MetaplecticMobiusDescent | the seed $\Theta\le20999/24000$: decay exponent at most $183001/12000$ |

## 10. Success criteria and contributions

**Success.** Stages 1–4 in Lean, unconditional, stated for the actual state of the dichotomy. Stage 5
either proved, or reduced to a named arithmetic property that fails on the prime-two deformations or the
positive Euler twins, with the Lean theorem "property $\Rightarrow$ no state"; or a model on which the properties
of stages 0–4 are realized together, which proves that the missing property lies outside them.

**A contribution** proves a property of the critical state (or of the critical states of model
configurations, with the model's role stated) that is unconditional and either an exact identity or a
restriction that removes candidate states. Restating an RH equivalence, fixed-aperture numerics and
finite computations are not contributions. A claim aimed at stage 5 names the arithmetic it uses and the
model on which it fails.

## 11. Big picture

The state is a single function whose transform is meromorphic in the plane and carries the zeros of
$\zeta$ as poles shifted by the confinement exponent: every zero in the strip is transported to $\rho-\tfrac{17}2$,
with residue $-m_\rho\mathcal LF(\rho-\tfrac12)/a$, nonzero on and right of the line. Right of the strip the equation
is read in prime coordinates; across it the Gamma pairing is the functional equation in Lévy form; left of
it the Euler parts cancel and $-a\mathcal LF(w)$ is the head term, the prime heads and the charges at $w+8$:
the prime side seen from beyond the wall. The explicit formula holds on the whole domain against probes,
so the state is the Cauchy transform of its own values at the zeros: $(\star)$ is a theorem, and stage 5
says that this Cauchy system has no solution in $\mathcal H$. Decay, sign and index laws are theorems and are
compatible with the existence of the state. What remains is the arithmetic contradiction (Q7–Q9): the two descriptions
of one meromorphic function, by its poles at the zeros and by its prime heads left of the strip, must be
shown incompatible. In time this is one series: $\sum_z\mathcal LF(z)e^{-zu}$ is $-a\,e^{-8u}F(u)$ left of the wall
and $a\,F^+(u)$ beyond it.
