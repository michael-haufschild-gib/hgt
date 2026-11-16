# Exclusion of the Critical State (ECS)

Namespace `GaloisForLFunctions.ExclusionOfTheCriticalState`; umbrella `ExclusionOfTheCriticalState.lean`.

## 1. Motivation

Weil's form, restricted to real tests on the half-line $u<0$ and confined by the weight $e^{-8u}$, has a
**critical state** exactly when RH fails: either RH holds, or the global window threshold $W_0$ is finite
and a unit profile $F$ attains the confined form's zero at ratio $W_0$
(`riemannHypothesis_or_exists_criticalHalfLineGroundState`). The state is unique up to sign, solves
the weak Euler–Lagrange equation against every test of the actual energy domain, has a zero-free
Laplace transform on $\operatorname{Re} w\ge0$, decays like $e^{\beta u}$ for $\beta<15/2$, and has mass
on every interval $(-d,0)$. RH is therefore the statement that **one explicit function does not exist**.

ECS makes this a research field. It writes the state's equation in the coordinates of the zeros, turns
every exact property of the state into a theorem, and looks for the property that contradicts the
arithmetic of $\zeta$. Each stage is a reduction "no function with properties $P_1,\dots,P_k$ exists
$\Rightarrow$ RH"; the list grows and the premise weakens. At the state every relation is an identity,
so nothing is lost between stages: the route has one open statement, about one function.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Energy domain $\mathcal H$ | `CriticalHalfLineEnergyDomain` (AHD) | measurable $F$ on $u<0$; $F,F^2,F^2e^{-8u}$ integrable; finite Gamma energy |
| Laplace transform | `paperFT` ($\mathcal LF(w)=$ `paperFT F (-I*w)`) | $\mathcal LF(w)=\int F(u)e^{wu}\,du$ |
| Bare form $B$ | `bareHalfLineEnergy` (AHD) | $\mathrm{arch}-\mathrm{prime}+2\mathcal LF(\tfrac12)\mathcal LF(-\tfrac12)$ (Weil's form) |
| Confinement | $W_8(F)=\int F^2e^{-8u}$, `criticalAliasCoefficient` $a(R)=a(1)/R$ | |
| Full form, mixed form | `criticalHalfLineFullEnergy`, `criticalHalfLineMixedEnergy` (AHD) | $Q_R=B+a(R)W_8$ |
| Threshold, state | `windowThreshold`, `IsCriticalHalfLineGroundState` (AHD) | $W_0=\inf_A$ windowThreshold, $F$ at $W_0$ |
| Probes | $e_p(u)=e^{pu}\mathbf 1_{u<0}$, $p>4$ (to build) | exponentials of the domain; $\mathcal Le_p(w)=1/(p+w)$ |
| Probe kernel | $K_a(p,q)=\frac{D(p)+D(q)}{p+q}+\frac a{p+q-8}$ (to build) | $D(p)=\xi'/\xi(\tfrac12+p)$ |
| Charges | $c_z=\mathcal LF(z)$, $z=\rho-\tfrac12$ (to build) | the state seen by the zeros |
| Cauchy matrix | $C(z',z)=1/(8+z'-z)$, pairing $\beta(c,d)=\sum_z c_zd_{-z}$ (to build) | the equation $(a+C)c=0$ |
| Configuration form | $B_Z(F)=\sum_{z\in Z}\mathcal LF(z)\mathcal LF(-z)$ (to build) | bare form of a model zero set $Z$ |
| Wall, collar | $u=0$; $-\log2<u<0$ | where the state meets the prime side |

## 3. Language

- **Critical ratio** of a configuration: an $a>0$ at which $B_Z+aW_8$ has a null vector; **critical state**:
  that null vector. For $\zeta$, $a(W_0)$ is the largest critical value.
- **Probe identity**: the weak equation tested on $e_p$.
- **State equation** $(\star)$: $a\,\mathcal LF(w)=-\sum_z\mathcal LF(z)/(w+8-z)$, $\operatorname{Re} w>-4$.
- **Charge** of a zero: $\mathcal LF(z)$; **seen** zero: nonzero charge. Every zero with
  $\operatorname{Re} z\ge0$ is seen.
- **Decay exponent**: $b^*=\sup\{b:\int F^2e^{-bu}<\infty\}$; a **ruler** for $\Theta$.
- **Soft property**: holds for the critical states of every tempered symmetric configuration.
- **Arithmetic property**: fails for a named model (prime-two deformations, positive Euler twins).

## 4. Mechanisms

1. **Probe calculus.** On probes each part of Weil's form is a function of $p,q$: the pole part is
   $\big(\frac1{p-\frac12}+\frac1{p+\frac12}+(p\leftrightarrow q)\big)/(p+q)$, the prime part is
   $-(\zeta'/\zeta(\tfrac12+p)+\zeta'/\zeta(\tfrac12+q))/(p+q)$, the Gamma part is the Poisson integral of
   $\operatorname{Re}\psi(\tfrac14+\tfrac{ir}2)$, i.e. $\tfrac12(\psi(\tfrac14+\tfrac p2)+\psi(\tfrac14+\tfrac q2))-\log\pi$
   over $p+q$. Together: $B(e_p,e_q)=\frac{D(p)+D(q)}{p+q}$, the Carathéodory kernel of $\xi'/\xi$, whose
   positivity on $\operatorname{Re}p>0$ is RH. The confinement adds $a/(p+q-8)$.
2. **Probe identity.** $Q(F,e_p)=0$ reads $a\,\mathcal LF(p-8)=-B(F,e_p)$. In prime coordinates
   $B(F,e_p)=D(p)\mathcal LF(p)-E_F(p)$, where $E_F$ collects difference quotients of $\mathcal LF$ at
   $\pm\tfrac12$ and against the Gamma density, and the prime tails
   $\sum_n\Lambda(n)n^{p-\frac12}\int_{u<-\log n}F(u)e^{pu}\,du$, convergent on $\operatorname{Re}p>-\beta$.
3. **Zero coordinates.** With the zero side $B(F,G)=\sum_z\mathcal LF(z)\mathcal LG(-z)$ on $\mathcal H$,
   the probe identity is $(\star)$; $E_F(p)=\sum_z(\mathcal LF(p)-\mathcal LF(z))/(p-z)$ is the linear explicit
   formula of the primitive $H_p(s)=-e^{-ps}\int_{-\infty}^sF(t)e^{pt}dt$.
4. **Continuation by steps of 8.** $(\star)$ continues $\mathcal LF$ meromorphically; its poles are the
   points $z-8$, residue $-\mathcal LF(z)/a$.
5. **Landau.** A transform of a function of one sign is singular at the real point of its abscissa; the
   poles $z-8$ are not real because $\zeta$ has no zero in $(0,1)$.
6. **Finite-rank index.** For a finite configuration $B_Z$ has rank $\le|Z|$ on
   $L^2(e^{-8u})$; its negative index is the number of points right of the line (Pontryagin law), and
   critical ratios are minus the negative eigenvalues of the Cauchy matrix.
7. **Translates.** The full mixed form of $F(\cdot+s),F(\cdot+t)$ is
   $a(1-e^{-8\min(s,t)})\langle\cdot,\cdot\rangle_{L^2(e^{-8u})}$ (`criticalHalfLineMixedEnergy_ground_translates`).

## 5. Questions

| # | Question | Stage | Kind |
|---|---|---|---|
| Q1 | $B(e_p,e_q)=\frac{D(p)+D(q)}{p+q}$ for $p,q>4$, from the literal arch/prime/pole parts | 1 | work |
| Q2 | The zero side of $B$ on $\mathcal H$: convergence and equality | 1 | work |
| Q3 | $(\star)$ for the state, continuation (a) and the two-sided series (b) | 2 | work |
| Q4 | Decay law: $\int F^2e^{-bu}=\infty$ for $b>17-2\Theta$; convergence below | 3 | half work, half open |
| Q5 | Sign law: $F$ has one sign on no ray $(-\infty,-T)$ | 3 | work |
| Q6 | Index law: exactly $\kappa$ critical ratios for a finite configuration; for $\zeta$, finite index at every ratio | 4 | finite: work; $\zeta$: open |
| Q7 | Rigidity: for the zeros of $\zeta$, $(\star)$ has no solution $F\neq0$ in $\mathcal H$ | 5 | open, equivalent to RH |
| Q8 | Which property, absent from the prime-two deformations and the positive Euler twins, enters an exclusion of the state? | 5 | open |
| Q9 | The wall: $F$ at $u\to0^-$ against the PNT-remainder side at $u\to0^+$; the collar $(-\log2,0)$; the charges $\mathcal LF(\pm\tfrac12)$ | 5 | open |

## 6. Tools

**Inherited** (AHD): existence, weak equation, uniqueness up to sign, closed-RHP zero-freeness, exponential
barriers, endpoint mass, translate kernel, phase structure.

**To build.**
- Probe calculus on $\mathcal H$ and the probe kernel (Q1).
- The explicit formula on $\mathcal H$ with a zero-side bound by the domain norm (Q2).
- The transform of the state: continuation, residues, abscissa and Landau test (Q3–Q5).
- Confined configuration forms: finite rank, Cauchy matrices of zero sets, indefinite pairings (Q6).
- Wall and collar calculus for the two-sided series (Q9).

## 7. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| RH or a critical state exists | `riemannHypothesis_or_exists_criticalHalfLineGroundState` | inherited |
| Weak equation | `criticalHalfLineMixedEnergy_groundState_eq_zero` | inherited |
| Probe kernel = Carathéodory kernel of $\xi'/\xi$ | — | target (Q1) |
| State equation $(\star)$, continuation | — | target (Q2–Q3) |
| Sign and decay laws | — | target (Q4–Q5) |
| Finite index law | — | target (Q6) |

## 8. Traps

| Trap | Truth |
|---|---|
| Stability, outerness or cyclicity exclude the state | They hold off RH (killed-route ledger) |
| A holomorphic multiplier dominates the pole term | No uniform one exists (AHD multiplier no-go) |
| The state has one sign | Frustrated in every sign gauge past the plastic threshold; sign law forbids one-signed tails |
| Functional equation + Euler product + positive coefficients exclude | Positive Euler twins have all three and an off-line zero |
| Stage 5 is a statement about zeros alone | Stages 1–4 hold for every tempered symmetric configuration; prime-two deformations have finite onset |
| $b<15$ is the decay law | It is the value at $\Theta=1$; the law is $17-2\Theta$ |
| The exponent 8 is canonical | Any weight exponent $p>1$ pays every window |
| The finite index law transfers to $\zeta$ | Infinitely many off-line zeros may accumulate critical ratios |
| Positivity of the probe kernel on real $p>4$ is weaker than RH | It is RH once probes span $\mathcal H$ in the energy norm |

## 9. Context

| Neighbour | Interface |
|---|---|
| ArithmeticHodgeTheoryOfDegenerations | owns stage 0: domain, forms, threshold, state, weak equation, barriers, phase structure |
| CriticalArithmeticCorrelationTheory | Gamma/prime/pole mixed forms on the weighted domain |
| RHTower | partial fractions of $\xi'/\xi$, Carathéodory criterion, two-channel resolvent kernel, Landau abscissa |
| ArithmeticCastelnuovoSeveri | Pontryagin law: negative squares = right zeros |
| ArithmeticOrientationGeometry | orientation index = seen right zeros (the finite index law is its confined analogue) |
| FrustratedArithmeticDirichletForms | frustration of the even sector in every sign gauge |
| BlackHoleRingdown, SelbergClass, HTGeometry | prime-two deformations, positive twins, Euler-log positivity (O11 separator) |
| MetaplecticMobiusDescent | the seed $\Theta\le20999/24000$: decay target $183001/12000$ |

## 10. Success criteria and contributions

**Success.** Stages 1–4 in Lean, unconditional, stated for the actual state of the dichotomy. Stage 5
either proved, or reduced to a named arithmetic property that fails on the prime-two deformations or the
positive Euler twins, with the Lean theorem "property $\Rightarrow$ no state"; or a model on which the
properties of stages 0–4 are realized together, which proves that the missing property lies outside them.

**A contribution** proves a property of the critical state (or of the critical states of model
configurations, with the model's role stated) that is unconditional and either an exact identity or a
restriction that removes candidate states. Restating an RH equivalence, fixed-aperture numerics and
finite computations are not contributions. A claim aimed at stage 5 names the arithmetic it uses and the
model on which it fails.
