# Trans-Horizon Incidence Mechanics

A divisor sieve of horizon $N$ reads an integer $k$ only through the divisors
$d\le N$ that are incident to it. Trans-Horizon Incidence Mechanics asks what
such a finite observer can see, say, and pay when it is read far beyond its own
horizon, $k\gg N$, and how those finite arithmetic observations transfer to the
continuous energies that the Riemann Hypothesis is equivalent to: the signed
sieve energies of the Bézout–valuation theory, the reciprocal-cell traces of the
Fermi–Nyman approximation, and the odd-sector prime-chain energies of the
arithmetic Markov operator. "Incidence" is the relation $d\mid k$ at $d\le N$;
"mechanics" means exact conservation and dissipation laws for quadratic energies
under the step $k\mapsto k+1$, the horizon step $N\mapsto N+1$, and the prime
dilation $k\mapsto pk$; "trans-horizon" means that the omitted divisors, composite
as well as prime, are the whole story.

This document is the foundational introduction: why the theory exists, which
objects it speaks about, which mechanisms carry its proofs, where its sharp
boundaries lie, and how to work inside it. Mathematics only; no ledger.

---

## 1. Why

### 1.1 The horizon barrier

The Bézout–valuation theory controls the renormalized prefix defect of a sieve
weight below its horizon: for $M+1\le N$ the defect is nonpositive, because
below the horizon the truncated divisor sum is the complete divisor sum. Every
receiver that would deliver RH lives above the horizon. There the truncated sum
omits divisors, and a highly composite endpoint $M+1$ can carry a response
$\lvert s_{N,c}(M+1)\rvert$ larger than the initial response
$\lvert s_{N,c}(1)\rvert$, so the boundary term of the Dirichlet polarization
changes sign. Exact transfer identities between the finite and continuous
pictures exist in abundance; none of them pays the bound. The theory was built
to find out exactly where the finite observer loses control, to prove the laws
that still hold above the horizon, and to classify the failures sharply enough
that their positive survivors become the next tools.

### 1.2 The three receivers

**Interior pronic energy.** For the power-damped Möbius weight
$c_\varepsilon(d)=\mu(d)d^{-\varepsilon}$ and its Bézout interior prefix
$I_\varepsilon(n)$,
$$
\forall\delta>0\ \exists\varepsilon\in(0,\delta)\ \exists B_\varepsilon<\infty\
\forall T\ge1:\quad \sum_{n=1}^{T}\frac{I_\varepsilon(n)^2}{n(n+1)}\le B_\varepsilon
\quad\Longrightarrow\quad\text{RH}.
$$
The constant may depend on the damping; it may not depend on the horizon $T$.
The bound is known for every $\varepsilon\ge1/2$ and open for $0<\varepsilon<1/2$.

**Odd-sector positivity.** For the arithmetic Markov operator with resolvent
on the mass space of the theta ground state, RH holds iff for every odd
$v\in C^2_c(\mathbb R)$
$$
\int\Theta(x)\,v(x)^2\cosh(x/2)\,dx\ \le\
\mathcal E_{\mathrm{arch}}(v)+\mathrm{sameSide}(v)+\mathrm{sameSide}(\tilde v)
+\sum_{q}\mathrm{chainIntegral}(v,q),
$$
the right side being the archimedean Doob jump energy, the two same-side prime
jump energies, and the complete bipartite prime-power chain variances.
Equivalently, RH fails iff the resolvent has a nonzero odd eigenvector with
eigenvalue in the open interval $(1/2,1)$.

**Nyman–Beurling approximation.** RH holds iff $\mathbf 1_{(0,1]}$ lies in the
closed span of the functions $\{1/(kx)\}$, $k\ge1$, in $L^2((0,\infty),dx)$. A
finite row $a_{N,k}$ has origin tail
$\int_0^{1/N}\lvert\sum_ka_{N,k}\{1/(kx)\}\rvert^2dx=\int_N^\infty\lvert\sum_ka_{N,k}\{u/k\}\rvert^2du/u^2$;
bounded norms plus local convergence on compact intervals give weak convergence
and hence RH, but a tail bound alone identifies neither the weak limit nor the
bulk.

Each receiver demands a horizon-uniform estimate on a literal arithmetic
source. The theory supplies the finite identities, the exact classifications,
and the sharp obstructions on the way; it does not yet supply any of the three
estimates.

### 1.3 Why finite observers

Three finite observation layers read the same sieve weight: the truncated
divisor sum itself, the reciprocal-cell jumps of the Fermi trace, and the
valuation clocks of translation. Each has an exact inversion theorem and an
exact conditioning constant, and each loses control in a different, sharply
located way. The theory treats these losses as theorems, not accidents: a unit
envelope that holds exactly up to ratio five, a trace conditioning that grows
exactly like $(4/\pi^2)(\log_2N)^2$, a successor dynamics that is deterministic
exactly up to horizon two. Those boundaries are the arithmetic content of the
horizon barrier.

---

## 2. What

### 2.1 Sieve responses and horizon states

For a real weight $c:\mathbb N\to\mathbb R$ and horizon $N$,
$$
s_{N,c}(k)=\sum_{\substack{d\mid k\\1\le d\le N}}c(d),\qquad
Y_{N,c}(e)=\sum_{\substack{1\le d\le N\\e\mid d}}\frac{c(d)}d .
$$
The **observation state** $\sigma_N(k)=\operatorname{lcm}\{d\le N:d\mid k\}=\gcd(k,L_N)$
with $L_N=\operatorname{lcm}(1,\dots,N)$ is a complete invariant: two integers
have the same response for every weight iff they have the same state. For
squarefree-supported weights the **radical state** $\gcd(k,N\#)$ with the
primorial $N\#$ suffices. The **observation phase** is $k\bmod L_N$. An integer
$r$ is **$N$-rough** when its only divisor $\le N$ is $1$; every prime $p>N$ is
$N$-rough, and $N$-rough integers form a multiplicative monoid.

The weights in use are the literal Möbius weight $\mu$, the damped weights
$c_\varepsilon(d)=\mu(d)d^{-\varepsilon}$ with full divisor sum
$\tau_\varepsilon(n)=\sum_{d\mid n}c_\varepsilon(d)=\prod_{p\mid n}(1-p^{-\varepsilon})$,
and the actual power-damped Ramanujan cofactor row of the PM route, which is
squarefree-supported and vanishes on multiples of four. Coefficient
perturbations are measured by the **divisor-incidence distance**
$W(N,K;c,b)=\sum_{d\le N}\lvert c(d)-b(d)\rvert\lfloor K/d\rfloor$.

### 2.2 Energies and defects

| Object | Definition |
|---|---|
| prefix $L^2$ energy | $\mathcal E_N(M;c)=\sum_{k=1}^Ms_{N,c}(k)^2$ |
| Selberg diagonal form | $Q_{\mathrm{Sel}}(N,c)=\sum_{e=1}^N\varphi(e)Y_{N,c}(e)^2$ |
| Bézout coprime form | $Q_{\mathrm{Bez}}(N,c)=\sum_{\gcd(d_1,d_2)=1}c(d_1)c(d_2)/(d_1d_2)$ |
| successor reserve | $\mathcal R_N(c)=Q_{\mathrm{Sel}}-Q_{\mathrm{Bez}}=\sum_{e=2}^N(\varphi(e)-\mu(e))Y_{N,c}(e)^2$ |
| harmonic sum | $H_c(N)=\sum_{d\le N}c(d)/d=Y_{N,c}(1)$ |
| prefix discrepancy | $\sum_{d\le N}c(d)\lfloor M/d\rfloor-MH_c(N)=-\sum_{d\le N}c(d)\{M/d\}$ |
| combined defect | $\mathcal D_N(M;c)=\sum_{d_1,d_2\le N}c(d_1)c(d_2)\{M/\operatorname{lcm}(d_1,d_2)\}+\text{Bézout sawtooth remainder}$ |
| renormalized defect | $\widetilde{\mathcal D}_N(M;c)=\mathcal D_N(M;c)-M\,\mathcal R_N(c)$ |
| short-window defect | $\widetilde{\mathcal D}_N(M_0,M;c)=\widetilde{\mathcal D}_N(M_0+M;c)-\widetilde{\mathcal D}_N(M_0;c)$ |
| centered sawtooth | $\tilde B_1(d,n)=\{n/d\}-(d-1)/(2d)$ |
| weighted sawtooth sum | $W_{N,c}(k)=-\sum_{d\le N}c(d)\tilde B_1(d,k)$, split into active ($d\mid m$) and inactive parts |
| Poincaré excess | $\sum_{e=2}^N(\varphi(e)-2\mu(e))Y_{N,c}(e)^2\ge0$ |

The renormalized defect is the unit-shift correlation minus the variance over
the prefix, and the **Dirichlet polarization**
$$
2\,\widetilde{\mathcal D}_N(M;c)=-\sum_{k=1}^{M}\bigl(s_{N,c}(k+1)-s_{N,c}(k)\bigr)^2
+s_{N,c}(M+1)^2-s_{N,c}(1)^2
$$
is the identity every sign statement in the theory passes through: the sum is
the Dirichlet energy of the unit step, and the two boundary squares are the only
terms that can be positive.

### 2.3 Fermi traces and pronic energies

The Fermi cell matrix $2\lfloor n/2d\rfloor-\lfloor n/d\rfloor$ gives the cell
response $F_{N,c}(n)=\sum_{d\le N}c(d)\bigl(2\lfloor n/2d\rfloor-\lfloor n/d\rfloor\bigr)$
on the reciprocal cell $(1/(n+1),1/n]$, and the **boundary jump**
$J(n)=F(n)-F(n-1)$. An odd boundary reads $J(2m+1)=-s_{N,c}(2m+1)$; an even one
reads $J(2m+2)=2s_{N,c}(m+1)-s_{N,c}(2m+2)$. The physical weight of the cell
$n$ is the **pronic** weight $1/(n(n+1))$. The complete **sieve pronic energy**
$P(N,c)=\sum_{n\ge1}s_{N,c}(n)^2/(n(n+1))$ and the complete **selected trace**
energy $Q(N,c)$ of the odd and four-divisible boundary readings are both
summable for every finite horizon. Their homogeneous versions use the weight
$1/n^2$ in odd-ray coordinates $n=2^k(2j+1)$. The optimal physical inverse
constants $K_N=\sup P/Q$ and $K_N^+$ (nonnegative coefficients) measure the
conditioning of the observation.

### 2.4 Valuation clocks

For $q\ge1$ the **visibility clock** is $\tau(q)=q/\operatorname{rad}(q)$. The
Ramanujan lag coefficient $c_q(h)=\sum_{d\mid q}\mu(q/d)\,d\,\mathbf 1_{d\mid h}$
and the normalized multiplier $c_q(h)/\varphi(q)$ describe which Selberg mode
$q$ a translation by $h$ can see: the mode is visible iff $\tau(q)\mid h$. The
von Mangoldt function is reconstructed from the clock with a prime guard,
$$
\Lambda(d)=\begin{cases}\log\bigl(d/\tau(d)\bigr)&\text{if }d/\tau(d)\text{ is prime},\\0&\text{otherwise};\end{cases}
$$
the guard is essential, since $\tau(6)=1$ while $\Lambda(6)=0$. Clock wavelets
are differences of lag multipliers at consecutive clock scales $p^a$, $p^{a-1}$.

### 2.5 Prime chains and the odd sector

On the divisor lattice of $N$ with product index, a cut at logarithmic height
$u$ along the $p$-adic chain over the base $b$ (coprime to $p$) splits the chain
into $L=\{m:\log m<u\}$ and $R=\{k:\log k\ge u\}$. The **bipartite energy**
$\sum_{m\in L}\sum_{k\in R}(a_m-a_k)^2$ equals the **variance energy**
$\lvert R\rvert\,\mathrm{scatter}(L)+\lvert L\rvert\,\mathrm{scatter}(R)+\lvert L\rvert\lvert R\rvert(\bar a_L-\bar a_R)^2$,
and the **chain variance** is $\sum_{p\mid N}\log p\sum_{b\mid N}\mathrm{var}(L,R)$.
Reading a profile $v$ along $m\mapsto v(u-\log m)$ gives the chain density, the
chain integral over $u$, and the prime crossing of the continuous theory.

On the continuous side: $\Theta$ is Riemann's kernel; the **odd profile**
$m_a(x)=(\Theta(x-a)-\Theta(x+a))/(2\sinh(a/2))$, its gauge $\Psi_a=m_a/\Theta$,
the odd polar weight $\Psi_a(x)w(x)$ for an even window $w$, the cosh mass
$\int\Theta v\cosh(x/2)$, the Lévy density $\omega(x)=e^{-x/2}/(1-e^{-2x})$ of
the archimedean symbol, the shift jump $m_a(x)m_a(x+t)(w(x)-w(x+t))^2$, the
origin-crossing collar square $m_a(x)m_a(t-x)(w(x)-w(t-x))^2$ on $(0,t)$, and
the collar mixed density. The spectral side is the source graph with its
energy, polarization, signed radical, ground vector $\mathbf 1$, resolvent, and
the Beurling–Deny contractions $q\mapsto q^+,q^-,\lvert q\rvert$. An off-line
zero $\rho=1/2+\beta+i\alpha$ is modelled by the radial envelope
$r_\beta(m)=m^\beta$ paired with $r_{-\beta}$.

### 2.6 Scales

| Scale | Meaning |
|---|---|
| $k\le N$ | sub-horizon: $s_{N,c}(k)=\sum_{d\mid k}c(d)$ is complete |
| $N<k\le2N$ | first octave: one omitted divisor, $s=\sum_{d\mid k}c(d)-c(k)$; for $\mu$, $s=-\mu(k)$ |
| $2N<k\le3N$ | second band: also $c(k/2)$ when $2\mid k$ |
| $3N<k\le4N$ | third band: also $c(k/3)$ when $3\mid k$ |
| $4N<k\le5N$ | fourth band: also $c(k/4)$ when $4\mid k$ |
| $k<5(N+1)$ | the damped unit envelope $\lvert s_N(c_\varepsilon,k)\rvert\le1$ holds, sharply |
| $k=5N+5$ | first failure: $N=6p-1$, $k=30p$, response $2$, for every prime $p>5$ |
| $k<6(N+1)$ | responses of magnitude at most $2$; literal Möbius defects nonpositive |
| $p\le M<p^2$ | quadratic window of a prime horizon: $\lfloor M/p\rfloor\le N$ lies in the exact zone |
| $L_N$ vs $N!$ | least full period divides $\operatorname{lcm}(1..N)$; $N!$ is a convenient period, not the same integer |

### 2.7 Glossary

| Object | Lean name |
|---|---|
| $s_{N,c}$, $Y_{N,c}$ | `sieveSeq`, `selbergMultiplesCoord` |
| observation state, modulus, phase; radical state | `horizonObservationState`, `horizonObservationModulus`, `horizonObservationPhase`, `horizonRadicalState` |
| $N$-rough | `IsTransHorizonRough` |
| weights $\mu$, $c_\varepsilon$, $\tau_\varepsilon$, cofactor row | `moebiusReal`, `pmPowerDampedRealWeight`, `pmPowerDampedDivisorCoeff`, `pmCofactorRealWeight` |
| incidence distance, normalized perturbation | `divisorIncidenceDistance`, `normalizedSquarefreeMobiusPerturbation` |
| $\mathcal E_N(M;c)$, band operator | `sieveL2PrefixEnergy`, `sieveBandSeq` |
| $Q_{\mathrm{Sel}}$, $Q_{\mathrm{Bez}}$, $\mathcal R_N$, Poincaré excess | `selbergTotientDiagonalForm`, `bezoutCoprimeQuadraticForm`, `sieveSuccessorReserve`, `sievePoincareExcess` |
| combined, renormalized, short-window defect | `sieveCombinedPrefixDefect`, `sieveRenormalizedPrefixDefect`, `shortWindowRenormalizedDefect` |
| harmonic sum, discrepancy, fractional sum | `finiteHarmonicSum`, `sievePrefixDiscrepancy`, `sievedFractSum` |
| sawtooth $\tilde B_1$, $W_{N,c}$, active, inactive | `centeredDiscreteSawtooth`, `weightedCenteredSawtoothSum`, `activeCenteredSawtoothSum`, `inactiveCenteredSawtoothSum` |
| complementary quotient tail | `complementaryQuotientTail` |
| period Dirichlet energy, period window | `horizonPeriodDirichletEnergy`, `horizonPeriodDefectWindow` |
| Fermi cell matrix, response, jump | `fermiCellMatrix`, `fermiCellResponse`, `fermiBoundaryJump` |
| pronic weight, $P$, $Q$, homogeneous forms | `pronicSeq`, `sieveTotalPronicEnergy`, `fermiSelectedTotalPronicEnergy`, `sieveHomogeneousEnergy`, `fermiSelectedHomogeneousEnergy` |
| four-free projection, coefficient transport, reading | `fermiFourFreeWeight`, `fermiSelectedCoefficient`, `fermiSelectedReading` |
| $K_N$, $K_N^+$ | `fermiPhysicalInverseConstant`, `fermiNonnegativePhysicalInverseConstant` |
| antichain admissibility, bank parity ratio | `fermiDyadicAntichainAdmissible`, `fermiPrimeBankParityRatio` |
| clock $\tau$, radical, Ramanujan coefficient, multiplier | `lagVisibilityClock`, `primeRadical`, `ramanujanLagCoefficient`, `sieveLagMultiplier` |
| clock wavelets, composite and tensor wavelets | `clockWaveletMultiplier`, `clockWaveletRamanujan`, `compositeClockWaveletMultiplier`, `clockTensorMultiplier` |
| totient threshold, recovery clock, trace distance | `horizonTotientThreshold`, `horizonFaultRecoveryClock`, `valuationTraceDistance` |
| active-sample inversion, amplification | `activeSawtoothMobiusLift`, `activeSampleAmplification` |
| bipartite and variance energy, chain variance, density, integral, crossing | `bipartiteEnergy`, `varianceEnergy`, `chainVariance`, `chainDensity`, `chainIntegral`, `primeCrossing` |
| radial envelope, global chain variances, continuous density | `offlineRadialEnvelope`, `globalOfflineChainVariance`, `globalCriticalChainVariance`, `continuousOfflineTwoChannelDensity` |
| $\Theta$, $m_a$, $\Psi_a$, polar weight, cosh mass | `riemannKernelReal`, `oddProfile`, `oddPolarFunction`, `oddPolarWeight`, `phiDoobCoshMass` |
| shift jump, collar square, collar mixed, across jump | `oddProfileShiftJump`, `oddProfileCollarDiffSq`, `oddProfileCollarMixed`, `oddProfileAcrossJump` |
| $\omega$, absorbed slice, collar ratios, budget | `archLevyDensity`, `absorbedArchSlice`, `primeCollarArchRatio`, `coshSinhPolarRatio`, `supportArchBudget` |
| Chebyshev step and discrepancy | `vonMangoldtChebyshevStep`, `vonMangoldtChebyshevDiscrepancy` |
| sinh potential, defect density, tail price | `oddSinhPotential`, `oddPolarDefectDensity`, `oddPolarTailPrice` |
| canonical odd and primitive cutoffs | `canonicalOddCutoff`, `canonicalPrimitiveCutoff` |
| source energy, pairing, radical, ground vector, contractions | `sourceEnergy`, `sourcePair`, `signedRadical`, `oneL`, `absGraph`, `posGraph`, `negGraph`, `evenFold` |
| windowed quarter zeros | `windowedQuarterZeros` |
| Nyquist cell primitive, interior prefix | `nyquistCellPrimitive`, `pmBezoutInteriorPrefix` |

---

## 3. How

### 3.1 Rough absorption and checkpoint rigidity

Multiplication by an $N$-rough integer is invisible to the sieve:
$s_{N,c}(qr)=s_{N,c}(q)$, hence $s_{N,c}(r)=s_{N,c}(1)$, the active sawtooth
sum resets to zero at $r-1$ and $r$, and the Möbius weight has an infinite
trans-horizon zero cone $s_{N,\mu}(qr)=0$ for $2\le q\le N$. At a **rough
checkpoint** $M=r-1$ the boundary squares cancel and
$2\widetilde{\mathcal D}_N(r-1;c)=-\sum_{k<r}(\Delta s)^2\le0$ for every
weight, at arbitrarily large scales. This is sharp as a universal law: the
renormalized defect at $k-1$ is nonpositive for every weight iff $k$ is rough,
and every nonrough endpoint has a positive witness already among nonnegative
squarefree weights in $[0,1]$ with $c(1)=1$. Changing only $c(1)$ leaves every
jump unchanged and moves the defect affinely by the endpoint response
difference, so equal endpoint responses are exactly the locus of universal
nonpositivity under unit shifts; the active sawtooth profile is blind to unit
shifts at every horizon and position.

### 3.2 Horizon filtration and band laws

Stepping the horizon injects one divisibility spike,
$s_{N+1,c}(k)-s_{N,c}(k)=c(N+1)\mathbf 1_{N+1\mid k}$, and across $N_1\le N_2$ it
adds $\sum_{d\in(N_1,N_2],\,d\mid k}c(d)$. At $N_2=M$ the sum is complete, so
for $N\le M$ and $k\le M$
$$
s_{N,c}(k)=\sum_{d\mid k}c(d)-\sum_{\substack{d\mid k\\ N<d}}c(d)
=\sum_{d\mid k}c(d)-\sum_{\substack{q\mid k\\ k/q>N}}c(k/q),
$$
the second form by the involution $d\mapsto k/q$. For $k\le(B+1)N$ the omitted
quotients lie in $[1,B]$, which gives the band normal forms of §2.6 and the
$B$-rough extension of the first-octave law up to $(B+1)N$. Between two rough
checkpoints the defect obeys the excursion law
$2(\widetilde{\mathcal D}_N(M)-\widetilde{\mathcal D}_N(r-1))=-\sum_{k=r}^M(\Delta s)^2+s(M+1)^2-s(1)^2$,
so every scale with $s(M+1)^2\le s(1)^2$ sits strictly below the already
nonpositive checkpoint; pronic cells $(r-1)r$ and $r(r+1)$ at a rough $r$
collapse to the linear neighbours $r-1$ and $r+1$.

### 3.3 The unit envelope and its exact boundary

Deleting one prime quotient contracts the damped response: with
$F_p(u)=1$ if $p\mid u$ and $1-p^{-\varepsilon}$ otherwise, and $A=F_p(u)F_q(u)$,
$$
\tau_\varepsilon(pqu)-c_\varepsilon(pqu)-c_\varepsilon(qu)-c_\varepsilon(pu)
=A\,\tau_\varepsilon(u)+(1-A)\,c_\varepsilon(u),
$$
a convex combination of two quantities of modulus at most one. Divisor
absorption handles square factors. Hence for every $\varepsilon\ge0$
$$
\lvert s_N(c_\varepsilon,k)\rvert\le1\qquad(2\le k<5(N+1)),
$$
and the bound is exact in two senses: the universal real ratio $C$ for which
$k\le CN$ suffices is exactly $C\le5$, and the universal additive buffer $b$
after $5N$ is admissible exactly when $b<5$. The obstruction is a symbolic
family, not a search: for every prime $p>5$, $N=6p-1$ and $k=30p=5N+5$ have
$s_{N,\mu}(k)=2$, the omitted quotients being $1,2,3,5$ with signs $+,-,-,-$.
The response persists along every power $k^m$, and excluding $\varepsilon=0$
changes nothing. Radical invariance transports the envelope to every positive
power of every certified base and to every endpoint whose radical state is
$<5(N+1)$, giving nonpositive defects $2\widetilde{\mathcal D}\le-E\le0$ on
unbounded checkpoint families.

The unit envelope is a method boundary, not a sign boundary. The Möbius path is
integer valued, so its jump energy over a nonempty prefix is at least
$1+\lvert s(M+1)\rvert$ and
$2\widetilde{\mathcal D}_N(M;\mu)\le s(M+1)^2-\lvert s(M+1)\rvert-2$:
endpoint magnitude two is admissible, responses are at most two before
$6(N+1)$, and the response-two family has nonpositive defect. A prime
$p\in(N,2N]$ gives the excursion $1,0,1,0$ at $1,2,p,2p$ and the strict margin
$\widetilde{\mathcal D}_N(M;\mu)\le-1$ for all $N\ge2$, $M\ge1$ with radical
state below $6(N+1)$. Continuity in $\varepsilon$ then yields explicit damping
radii on which the margin survives as $\le-1/2$:
$\delta_N=1/(96N(N+1)\log N)$ from the coefficient $\ell^1$ bound
$\sum_{d\le N}\lvert c_\varepsilon(d)-\mu(d)\rvert\le\varepsilon N\log N$, and the
larger $1/(96(N+1)(\log N)^2)$ from charging perturbations at their actual
divisor incidences. In the incidence ball $W\le1/20$ around $\mu$ every
squarefree-supported weight keeps $\widetilde{\mathcal D}\le-59/100$ on the
certified fibres, while the prime family keeps response above $39/20$. The
radii shrink with $N$; no fixed-damping cofinal statement follows.

### 3.4 Spike cancellation and the arithmetic uncertainty principle

Extracting the last step of the Dirichlet sum cancels the endpoint square
exactly:
$2\widetilde{\mathcal D}_N(M)=-\sum_{k<M}(\Delta s)^2+2s(M)s(M+1)-s(M)^2-s(1)^2$.
Whenever the sieve changes sign or vanishes between the coprime neighbours $M$
and $M+1$, the defect is at most $-(s(M)^2+s(1)^2)/2$, however large the
composite spike at $M+1$. Averaging two consecutive prefixes cancels both
boundary squares and leaves the coprime product $s(M)s(M+1)$. The discrete
path Poincaré inequality $(f(a+L)-f(a))^2\le L\sum_{j<L}(f(a+j+1)-f(a+j))^2$
says that a spike at additive distance $L$ from a zero of the sieve, or from a
rough anchor where $s=s(1)$, costs at least $s(a+L)^2/L$ of local Dirichlet
energy.

### 3.5 Period laws and the torus Poincaré inequality

On any window of a common return period $L$ (every $d\le N$ divides $L$) the
variance, the shifted correlation and the Dirichlet energy are
$L\,Q_{\mathrm{Sel}}$, $L\,Q_{\mathrm{Bez}}$ and $2L\,\mathcal R_N$, independent
of the offset. The combined defect is periodic and the renormalized defect
dissipates linearly, $\widetilde{\mathcal D}_N(M+qL)=\widetilde{\mathcal D}_N(M)-qL\,\mathcal R_N$;
a complete period shift costs exactly half the period Dirichlet energy, flat
responses have zero defect, and every nonflat response escapes to $-\infty$
along each phase. Subtracting the harmonic mode gives the exact excess
$2\mathcal R_N-(Q_{\mathrm{Sel}}-H_c(N)^2)=\sum_{e\ge2}(\varphi(e)-2\mu(e))Y_{N,c}(e)^2\ge0$,
with equality in a term only at $e=6$, hence on every sliding period window
$$
\sum_{k=M+1}^{M+L}s_{N,c}(k)^2-L\,H_c(N)^2\le\sum_{k=M+1}^{M+L}\bigl(s_{N,c}(k+1)-s_{N,c}(k)\bigr)^2 :
$$
the discrete Poincaré constant on the torus of period $L\sim e^N$ is at most one
for every divisor incidence sum, because the Bézout coprimality $\gcd(k,k+1)=1$
annihilates all non-coprime correlations in a single step.

### 3.6 Buchstab energy calculus

Across a horizon step the prefix energy changes by
$$
\mathcal E_{N+1}(M)-\mathcal E_N(M)=c(N+1)^2\Bigl\lfloor\frac M{N+1}\Bigr\rfloor
+2c(N+1)\sum_{j=1}^{\lfloor M/(N+1)\rfloor}s_{N,c}\bigl((N+1)j\bigr),
$$
and the step vanishes when $N+1$ is not squarefree and $c$ is
squarefree-supported, since then $s_{N,c}(dk)=s_{N,c}(k)$ for $d\mid k$ at every
horizon. At a prime horizon $p=N+1$ rough absorption reduces the dilated sum
to $\sum_{j\le\lfloor M/p\rfloor}s_{N,c}(j)$, which for Möbius equals one on the
quadratic window $p\le M<p^2$: $\mathcal E_p(M;\mu)-\mathcal E_{p-1}(M;\mu)=\lfloor M/p\rfloor-2$,
contraction by one in the first band, conservation in the second, growth after.
Telescoping down from the exact top value $\mathcal E_M(M;\mu)=1$ through the
squarefree steps gives closed forms: $\mathcal E_N(M;\mu)=1+\sum_{N\le n<M}\mu(n+1)^2$
in the first octave, a parity dichotomy in the second band (even steps
$-2\mu(n+1)^2$, odd steps $0$), a $(2,3)$-adic classification in the third
($-3\mu^2$ if $2\mid n+1$, $-\mu^2$ if $3\mid n+1$ only, $+\mu^2$ if coprime to
six), and linear bounds $\mathcal E_N(M;\mu)\le1+B(M-N)$ through the fourth band.
Centering the $q=1$ quotient yields
$(B-2)(\mathcal E_n-\mathcal E_{n+1})=S_2^2-((B-2)\mu(n+1)+S_2)^2$ with
$S_2=\sum_{2\le q\le B}s_{n,\mu}(q(n+1))$, so the downward step dissipates
whenever $\lvert S_2\rvert\le(B-2)/2$, and a completed square gives the
universal subadditivity
$\mathcal E_N(M)\le\mathcal E_{N+1}(M)+\mathcal E_N(\lfloor M/(N+1)\rfloor)$ at
prime horizons.

### 3.7 Observation states, phases, and recovery

The observation state is a complete invariant but not a dynamics: the successor
state is determined by the state exactly when $N\le2$, and beyond that
indistinguishable states with different successors occur arbitrarily far out.
The positive refinement is the phase $k\bmod L_N$. Phase equality is
equivalent to equality of all future observations, and a window of
$W\ge\Phi_{\max}(N)=\max_{p^a\le N}\varphi(p^a)<N$ consecutive states suffices,
sharply: for one prime power the pair $1$, $1+p^{a-1}$ collides on
$\varphi(p^a)-1$ steps. For radical states the window is $\max_{p\le N}(p-1)$.
With at most $e$ corrupted and $s$ erased observations, recovery is possible
exactly when the window reaches $\max_{p^a\le N}\bigl((e+s/2)p^a+(\varphi(p^a)\text{ if }s\text{ even, else }p^a)\bigr)$.

Coefficients are recovered too. Active self-endpoint samples form a divisor
transform of the nonunit coefficients and are inverted by Möbius inversion;
samples may be moved to arbitrarily high common powers; one harmonic scalar
restores the unit coefficient and every prefix defect. The worst-case error
amplification at a squarefree target $d$ is exactly
$(2d/(d-1))\cdot\#(\text{divisors of }d\text{ other than }1)$, attained by a
Möbius-sign sample vector. Short windows are classified by endpoints: the
short-window defect is nonpositive for all weights iff the endpoint states
agree, for all nonnegative weights iff the right state divides the left one
(reverse divisibility), with calibrated two-atom positive witnesses otherwise.
Among all integers with a given observation class, the canonical radical state
$\gcd(k,N\#)$ maximizes the defect, so a global upper bound reduces to finitely
many radical-state tests.

### 3.8 Valuation clocks and prime chains

The clock reconstructs $\Lambda$ as in §2.4 and gives the exact three-zone
filter law for a prime-power mode $q=p^b$ sampled at lag $p^a$: multiplier $1$
and coefficient $\varphi(p^b)$ in the passband $b\le a$, multiplier $-1/(p-1)$
and coefficient $-p^a$ at the frontier $b=a+1$, zero in the stopband
$b\ge a+2$. The difference of two consecutive clock scales is a wavelet
supported on exactly the two shells $\{a,a+1\}$, with values $p/(p-1)$ and
$-1/(p-1)$, and an unnormalized dipole $+p^a,-p^a$ of zero net charge. Coprime
moduli tensor both multipliers and coefficients, so a transverse lag equal to
the transverse clock detects the two adjacent valuations of every nonzero
integer. On the prime-chain side, stepping from a chain base $b$ coprime to $p$
to $pb$ renormalizes the horizon:
$s_H(c,pb)-s_H(c,b)=s_{H/p}\bigl(c(p\,\cdot),b\bigr)$.
For $p>H$ the right side is empty, so every $p$-chain variance of a truncated
sieve profile vanishes identically; for squarefree-supported weights every
excited node collapses to the first excited level, and excited-to-excited jumps
vanish at every horizon.

### 3.9 Fermi observability and its conditioning

The two selected schedules, odd boundaries and boundaries divisible by four,
recover the whole sieve sequence exactly iff the admitted coefficients on
multiples of four vanish; on that class the energies satisfy $Q\le P\le4Q$ with
sharp constants and exact nonnegative slack, and the actual cofactor row of the
PM route lies in it. For arbitrary coefficients the selected trace is still
injective, through an explicit even-chain coefficient transport whose inverse
costs at most $3/2$ in coefficient energy, sharply. Physical conditioning is a
different matter. The horizon forces dyadic saturation after
$L=\lfloor\log_2N\rfloor+1$ levels, giving $P\le(L+4)(L+1)Q$; dyadic coefficient
ramps give $P\ge L(L+1)(2L+1)/12$ with $Q\le2L$, also inside the nonnegative
cone, so no horizon-independent inverse exists. The sharp law is
$$
\frac{K_N}{(\log_2N)^2}\longrightarrow\frac4{\pi^2},\qquad
\frac{K_N^+}{(\log_2N)^2}\longrightarrow\frac4{\pi^2},
$$
from a mixed-boundary sine inequality along dyadic rays and nonnegative cosine
packets attaining it; at finite horizon the two constants differ, $K_3^+<K_3$,
because the shift $c\mapsto c+t(e_2-e_1)$ changes both energies by the same
quadratic and the signed centering strictly improves the ratio. On dyadic
antichains (one index per odd part) with odd prime factors in a set $\Pi$, a
horizon-uniform $P\le CQ$ holds, also on nonnegative packets, iff
$\sum_{p\in\Pi}1/p<\infty$, with the explicit constant $8e^{6M}$ for reciprocal
mass $M$; divergent capacity produces nonnegative packets with
$P\ge(L-1)/2$ and $0<Q<5/6$ for every $L\ge2$, built from disjoint prime banks
whose parity ratios $\prod(p-1)/(p+1)$ are small.

### 3.10 Off-line hyperbolic chain excess

A two-channel wave $(r\cos\theta,r\sin\theta)$ has squared jump
$(r_m-r_k)^2+r_mr_k\bigl((\cos\theta_m-\cos\theta_k)^2+(\sin\theta_m-\sin\theta_k)^2\bigr)$.
For the functional-equation pair $r_{\pm\beta}(m)=m^{\pm\beta}$ the symmetrized
variance on every chain cut exceeds the critical-line variance by
$\tfrac12(\mathrm{var}(r_\beta)+\mathrm{var}(r_{-\beta}))$ plus a nonnegative phase
amplification, strictly on nonempty cuts when $\beta\ne0$. One clock step
$b\to pb$ pays $\log p\,r_\beta(b)^2(e^{\beta\log p}-1)^2$; at a ground cut
$u\in(0,\log2)$ all prime factors pay at once, and the convexity inequality
$(e^x-1)^2+(e^{-x}-1)^2\ge x^2$ gives the quadratic floor
$\tfrac12\beta^2\sum_{p\mid N}(\log p)^3$. The continuous crossing density of
the waves $e^{-\beta x}\cos\gamma x$, $-e^{-\beta x}\sin\gamma x$ factors as
$e^{-2\beta u}\cdot\mathrm{fiber}(N,u)\cdot$ the discrete global variance, and
compactly windowed versions keep the ground-step bounds when the window equals
one at the two evaluation points. Along a chain the wave satisfies the exact
recurrence $\Phi(r+1)-2e^{\beta\tau}\cos(\alpha\tau)\Phi(r)+e^{2\beta\tau}\Phi(r-1)=0$,
$\tau=\log p$. These are lower bounds for inserted modes; they do not exclude
an actual zero.

### 3.11 The odd sector in quotient coordinates

Every odd mass vector is orthogonal to the ground vector $\mathbf 1$, so by
ergodicity of the archimedean jump measure every nonzero odd eigenvector of the
resolvent has eigenvalue below one, and RH is equivalent to the absence of odd
eigenvalues in $(1/2,1)$, to nonnegativity of the source energy on the
radical-reduced odd sector, and to the prime-chain Poincaré inequality of §1.2.
For an eigenvector $q$ with eigenvalue $\mu\ne0$ the nodal lobes obey
$$
\mathrm{sourceEnergy}(\lvert q\rvert)-4\,\mathrm{sourcePair}(q^+,q^-)=\frac{1-2\mu}\mu\|q\|^2,\qquad
\mathrm{sourceEnergy}(\lvert q\rvert)-4\,\mathrm{sourceEnergy}(q^+)=\frac{2\mu-1}\mu\|q\|^2,
$$
so RH is equivalent to $\mathrm{sourceEnergy}(\lvert q\rvert)\le4\,\mathrm{sourceEnergy}(q^+)$
for every odd eigenvector. On the odd sector both lobes carry half the mass, the
ground-vector defect of $\lvert q\rvert$ is the cross-lobe rank-one pairing
$8\langle q^+,\mathbf 1\rangle\langle q^-,\mathbf 1\rangle$, and the five-term
nonnegative jump sum of $\lvert q\rvert$ equals the local diagonal energy of $q$.
Collar splits with the $\cosh(R/2)$ denominator bound the ground potential by
collar plus far field at any radius. A premised four-term positive-lobe excess
over the ground potential would give RH; nothing here proves it.

### 3.12 Collar transport

Across a prime cut every edge $(m,k)$ straddles the origin, so for an odd
profile $v$ and its even fold $v(\lvert x\rvert)$ the bipartite energies obey a
parallelogram law, and when $v\ge0$ on the half-line the origin flip reinforces
every jump: the odd chain density dominates the folded one. The low-prime
window $\tfrac32\log d+\delta+L\le a$ is treated by Schur completion. $m_a$ is
strictly increasing on $[0,a]$, and the exact identity
$$
\mathrm{shift}-\mathrm{collar}+\frac{m_a(x)}{m_a(t+x)-m_a(t-x)}\,\mathrm{across}
=\frac{m_a(x)\bigl(m_a(t+x)(w(x)-w(x+t))-m_a(t-x)(w(x)-w(t-x))\bigr)^2}{m_a(t+x)-m_a(t-x)}\ge0
$$
moves the origin-crossing collar square onto a jump between $t-x$ and $t+x$,
both at distance at least $t/2$ from the origin. The archimedean gap
$\omega(s)-\omega(2y+s)\ge(1-e^{-y})\omega(s)$ then pays that across-jump by the
two-dimensional absorbed integral on a continuum bridge window. The ratio is
unconditional: from the drop bounds
$\pi e^{2u_1}\Theta(u_2)(u_2-u_1)\le\Theta(u_1)-\Theta(u_2)\le2\pi(e^{2u_2}+2)\Theta(u_1)(u_2-u_1)$
one gets $m_a(x)\le4e^{4t}(m_a(t+x)-m_a(t-x))$ for $x\in[0,t/2]$ whenever
$\tfrac32t+\tfrac12\log2\le a$.
Above twice the support radius of $w$ the collar is dominated by the direct
jump at zero archimedean cost, so for $a\ge3R+\delta+L$ the whole prime collar
sum is paid by half-line jumps plus a cutoff-free budget $C_{\mathrm{supp}}(R,\delta,L)$
times one absorbed archimedean integral. Midpoint reflection collapses the
collar mixed density to a one-point diagonal potential; a Stieltjes
integration by parts turns $\sum_{\log d<a}\Lambda(d)d^{-1/2}(\cdots)$ into a pole
term plus a Chebyshev discrepancy transport; and the mean-value comparison
$m_a(x)\le(2M/\sinh(a/2))\sinh(x/2)$ on $[0,R]$, with $M$ a bound for $\Theta'$ on
$[a-R,a+R]$, bounds the cosh mass by a sinh potential,
so that cosh mass and all prime collars are absorbed with net coefficient
$\theta\le1$ whenever the literal cosh/sinh ratio is at most $\theta$. That
ratio condition is the hinge, and §3.13 shows it fails.

### 3.13 The absorption boundary and primitive horizons

For $0<a\le\log2/2$ and $x\ge\log2$,
$$
\frac{m_a(x)\cosh(x/2)}{\Theta(x)\sinh(x/2)}\ \ge\ \pi\,e^{2x-5\log2/4}>1,
$$
so every derivative-based absorption coefficient exceeds one at radius
$R\ge\log2$ and, by smooth paired-bump localization, every fixed integrated
coefficient fails on compact even profiles. The survivors are exact: the
confinement law $K(L)\,P_{\mathrm{tail}}(L,w)\le C_a(w)$ with
$K(L)=\pi e^{2L-5\log2/4}$ (bounded cosh mass forces exponential sinh-tail
control), the least continuous even nonnegative local correction
$[\Theta\psi_a^2\cosh(x/2)-\theta m_a\sinh(x/2)]_+$, and the complete compensated
identity in which Markov energy plus $\theta$ times the sinh potential plus
this correction equals the nonnegative jump energies plus a reserve. On the
primitive side, cutting the theta profile by the same cutoff before translating
and subtracting two normalized odd translates kills both hyperbolic moments
exactly; the family converges in graph norm to a nonzero signed-radical
difference, and its complete original energy obeys
$\lvert E(g_{a,b,n})\rvert\le2(L_a+L_b)/(n+1)^2$ with every prime, the cosh
subtraction and the reflected collar retained. Hence no uniform positive energy
gap relative to the graph norm exists on compact primitive tests; vanishing
energy neither proves nor refutes nonnegativity.

### 3.14 Bridges

Quarter-plane zeros in any height box are finite without hypothesis, inherit
the Ingham–Huxley, Huxley $12/5$ and density-hypothesis exponents, are
annihilated above the Route-T zero-free width, and the Chebyshev discrepancy on
dyadic prime shells inherits the Vinogradov–Korobov rate. A fourth-root
Brun–Titchmarsh level cancels one $\log q$ on prime-supported von Mangoldt
weights; Gallagher transfers multiplicative to linear windows; the
Matomäki–Teräväinen coefficients obey Rankin–Euler tail bounds. The Nyquist
log-cell integral of the Chebyshev gauge decomposes with exact pronic
coefficient,
$\int_{\log n}^{\log(n+1)}e^{-t}(c+1-t-e^t)^2dt=c^2/(n(n+1))-2c(\cdots)+\text{const}$,
linking the bi-scale gauge to the pronic Abel summation of the interior
prefix; the interior gradient plus local impulse cross sum tracks its
logarithmic counterterm within a horizon-independent constant, and a cofinal
strict interior contraction would give RH. The shifted ground state has a
two-sided collar duality $R_a(u)+D_a(u)=4\int_{x>0}u^2m_aC_a$ and a variation
inequality equivalent to nonnegativity of its Markov energy, while every
nonnegative combination of two shifted ground states is a strict subsolution
near the origin and at infinity.

---

## 4. Traps and sharp boundaries

| Trap | Why it fails |
|---|---|
| RH "lives" only in $N<M\le N^2$ | No such restriction is justified; trans-horizon control is needed at every scale. |
| The full period is $N!$ | The least period divides $\operatorname{lcm}(1,\dots,N)$; $N!$ is only a convenient common period. |
| Full-period diagonalization controls a moving window | Period laws fix complete periods; short and moving windows are classified by endpoint states instead. |
| The unit envelope holds beyond ratio five | False at $k=5N+5$ for arbitrarily large horizons; the exact classification is $C\le5$, buffer $b<5$. |
| Envelope failure is a positive defect | Integer jump energy certifies nonpositive defect for all responses of magnitude $\le2$, including the counterfamily. |
| The Nyman origin tail uses $dx/x^2$ with $\{1/(kx)\}$ | That integral has a periodic integrand and diverges; the correct transform is $\int_N^\infty\lvert\cdot\rvert^2du/u^2$. |
| A tail bound proves Nyman approximation | Weak closure needs bounded norms and local convergence on compact intervals as well. |
| Selberg damping keeps exact divisor cancellation | For $c(d)=\mu(d)\log(N/d)/\log N$, $\sum_{d\mid k}c(d)=\Lambda(k)/\log N$, not zero. |
| $\Lambda(d)=\log(d/\tau(d))$ for every $d$ | $d=6$ has clock $1$ and $\Lambda(6)=0$; the prime guard is essential. |
| Clock visibility is a valuation-change rule | It describes nonvanishing of a Ramanujan lag multiplier, not when an integer's valuation changes. |
| State equality is successor dynamics | Deterministic successor evolution holds only for $N\le2$; the phase $k\bmod L_N$ is the refinement. |
| Finite observability gives a cofinal source estimate | Exact recovery and conditioning constants say nothing about cancellation in the recovered values. |
| Injectivity of the selected trace gives uniform physical coercivity | The optimal constant grows exactly like $(4/\pi^2)(\log_2N)^2$, even on nonnegative coefficients. |
| The antichain capacity law classifies literal PM rows | It concerns antichain packets with restricted odd prime factors; the cofactor row is handled by the four-free law instead. |
| The highest-dyadic recovery theorem applies to Möbius rows | Squarefree-supported rows have zero highest-dyadic anchor for $N\ge4$; the hypothesis excludes them. |
| Checkpoint signs transfer to every prefix | Rough checkpoints and certified fibres are unbounded families, not all prefixes. |
| A bounded difference of two uncontrolled energies bounds either | Only the difference is controlled. |
| Fixed-horizon ratios give cofinal estimates | Damping radii and coefficient neighbourhoods shrink with $N$. |
| Off-line chain excess excludes a zero | It is a lower bound for an inserted mode, not an upper constraint on the same complete energy. |
| The signed quotient inherits the source mass | Source mass does not descend through the signed radical; only the signed form does. |
| Finite multiplicity above $1/2$ gives compactness | Eigenvalues may accumulate at $1/2$; the threshold radical is infinite-dimensional. |
| A fixed cosh/sinh absorption coefficient | Fails for every $R\ge\log2$; the literal ratio grows like $\pi e^{2x}$. |
| Rewriting an eigenvalue bound as a four-term inequality proves it | It restates the RH-equivalent criterion in new coordinates. |
| Replacing $v$ by $\lvert v\rvert$ and keeping only the Markov gain | Contraction loses the factor between $\mu<1$ and $\mu\le1/2$; the pole and parity data change. |
| Vanishing primitive energy settles the sign | The $O((n+1)^{-2})$ family only excludes a uniform gap relative to the graph norm. |
| Compensated positivity is odd Weil positivity | The local correction is not shown to be paid by jump energy on arbitrary profiles. |
| The PM receiver needs a bound uniform in damping | It needs a bound uniform in the horizon at each arbitrarily small fixed damping; the constant may depend on $\varepsilon$. |

**Lean conventions.** Everything lives in
`GaloisForLFunctions.TransHorizonIncidenceMechanics`. Sieve objects are imported
from the Bézout–valuation and bi-scale theories, the Markov operator, prime
chains and theta kernel from the RH tower. Capstones take data only: a weight
`c : ℕ → ℝ`, a horizon `N`, a prefix `M`, a damping `ε`, with ranges encoded by
natural offsets such as `n + 1` or by the predicate `IsTransHorizonRough`. No
positivity, cancellation or zero-location hypothesis appears; RH occurs only as
the conclusion of an implication or inside an equivalence. Universal statements
over all weights are stated as `∀ c`, and "for all squarefree-supported weights"
as an explicit support premise on `c`. Every `tsum` is preceded by a
summability theorem. Counterexamples are symbolic families indexed by a prime
`p`, never evaluated instances. Classical constituents are marked `[Known]` or
`[Corollary]` in docstrings, new formulations `[New formulation]`; no heartbeat
settings are raised.

---

## 5. The frontier

**The complete signed trans-horizon energy.** The PM receiver needs
$\sup_T\sum_{n\le T}I_\varepsilon(n)^2/(n(n+1))<\infty$ at arbitrarily small fixed
$\varepsilon$. The observation cost on the actual cofactor row is now paid with
the uniform constant four; the defect is nonpositive on every certified
checkpoint; what is missing is cancellation in the complete coefficient-weighted
energy with means, endpoints, mixed covariance and growing cutoffs retained.
Uncentered active-pair budgets diverge at small damping, so only the
log-renormalized remainder remains viable.

**Defect sign beyond the envelope.** For $\varepsilon=0$ the Möbius defect is
nonpositive before $6(N+1)$ and on all certified fibres; for fixed positive
$\varepsilon$ the known radii shrink with $N$. The half-band criterion
$\lvert S_2\rvert\le(B-2)/2$ identifies the cancellation that would make every
downward Buchstab step dissipative at large ratios.

**The odd sector.** After exact collar cancellation the remaining obligation is
an independently quantified bound on the low-prime diagonal potential, or an
actual-source nodal estimate paying the primitive ground-projection defect. The
cosh/sinh ratio cannot be made $\le1$ on compact profiles; the minimal local
correction must be paid by jump energy, or the source class restricted so that
the confinement law suffices.

**Fermi–Nyman.** Origin and bulk tightness on one explicit approximation
sequence; the trace conditioning $(4/\pi^2)(\log_2N)^2$ is the price of reading
the row through selected boundaries.

**Observation.** Whether adding the cells $2\parallel n$ to the schedule changes
the sharp loss is a new observation model, not a repair of the old one.

---

## 6. Working in the theory

Fix the weight class first: arbitrary real weights, squarefree-supported
weights, nonnegative weights, the literal Möbius weight, the damped family, or
the cofactor row. Many laws are universal in the weight; the sharp ones are not,
and the obstruction examples are usually nonnegative squarefree weights with
$c(1)=1$. State every bound with its range of $k$, $M$ and $N$ and say which
band it lives in. Pass every sign claim through the Dirichlet polarization and
name the boundary squares. Transport certificates along radical fibres and
positive powers rather than reproving them at large scale. When a universal
law fails, locate the first failure exactly and prove the classification; the
positive survivor is the theorem. Search the corpus before building: Buchstab
steps, Ramanujan lag coefficients, Montgomery–Vaughan interval bounds, the
Gutzmer and Hardy path inequalities, GCD Gram kernels, the theta drop bounds
and the Lévy density are all present. Comments in Lean are mathematics; status,
dates and logs belong on the pipeline cards.
