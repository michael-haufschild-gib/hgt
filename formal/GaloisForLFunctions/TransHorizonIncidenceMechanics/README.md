# Trans-Horizon Incidence Mechanics

A divisor sieve of horizon $N$ reads $k$ through divisors $d\le N$. Trans-Horizon Incidence
Mechanics asks what this finite observer can recover and bound far beyond its horizon, $k\gg N$,
and how its observations transfer to RH-equivalent energies: signed Bézout–valuation sieve
energies, Fermi–Nyman reciprocal-cell traces and odd-sector arithmetic Markov prime chains.
“Incidence” is $d\mid k$; “mechanics” means conservation and dissipation under succession
$k\mapsto k+1$, horizon growth $N\mapsto N+1$ and prime dilation $k\mapsto pk$.
“Trans-horizon” concerns omitted divisors, composite as well as prime.

---

## Place in the research

THIM is the **finite-observer theory of signed arithmetic receivers**. Exact recovery, good
conditioning and period variance bounds do not imply payment of the centred-prefix energy
`Σ_{n≤T} A_c(n)²/(n(n+1))`, where `A_c(n) = Σ_{j≤n}((c*1)(j) − Σ_d c(d)/d)`.
Pronic weights retain small arguments as the coefficient horizon grows; full-period
diagonalization cannot replace uniformity in `T` or justify exchanging horizon and damping limits.

| Neighbour | Interface |
|---|---|
| [Bézout–Valuation Incidence](../BezoutValuationIncidence/README.md) | Selberg coordinates, successor polarization, window Poincaré laws and single-modulus pronic Gram structure. |
| [Bi-Scale Uncertainty](../BiScaleUncertainty/README.md) | Full-period observation theory, signed packets, Chebyshev gauge and calibration countermodels. |
| [Arithmetic Continuation and Critical Energy](../ArithmeticContinuationAndCriticalEnergy/README.md) | Transports the receiver in damping or cutoff; THIM identifies the boundary and the observations that lose its signs. |
| [Arithmetic Compensation Theory](../ArithmeticCompensationTheory/README.md) | Tests whether signed derivative work can be paid by the admitted energy without restating admission. |
| [Scale-Signed Incidence Criticality](../ScaleSignedIncidenceCriticality/README.md) | Abstracts parity pairs into exact limits on what a data reading can prove. |
| [Signed Arithmetic Energy Incidence](../SignedArithmeticEnergyIncidence/README.md) | Keeps the arithmetic source and its cross terms when passing from receiver data to energy. |
| [Arithmetic Criticality Theory](../ArithmeticCriticalityTheory/README.md), [Arithmetic Incidence Positivity](../ArithmeticIncidencePositivity/README.md) | The odd-sector and crossing-pair formulations of the same complete-form obstruction. |
| [Arithmetic Positivity Theory](../arithmetic-positivity-theory/README.md), [Square-Root Threshold](../SquareRootThreshold/README.md) | Source approximation and zero-detection coordinates for estimates that reach a continuous receiver. |
| [Arithmetic Castelnuovo–Severi](../ArithmeticCastelnuovoSeveri/README.md) | Seeks source-derived arithmetic effectivity that generic observer and dissipation identities do not provide. |
| [Arithmetic Orientation Theory](../ArithmeticOrientationTheory/README.md) | Treats the even flip as an orientation and reads it exactly at the prime $2$ through the first pronic moment. Restates the parity barrier for readings, and proves that the critical Wiener kernels form a monoid whose orbits the paid class is a union of. |
| [Signed Successor Arithmetic](../SignedSuccessorArithmetic/README.md) | Keeps a Möbius orientation in successor and coprime-factor observations; tests whether their inverse constants survive a growing horizon. |
| [Arithmetic Defect Rigidity](../ArithmeticDefectRigidity/README.md) | Reads the same pronic receiver through cofactor energy and its signed forcing pairing, and studies what an unbounded normalized receiver can escape from. |
| [Trans-Threshold Pair Correlation](../TransThresholdPairCorrelation/README.md) | Meets the sieve parity barrier at close prime pairs beyond the Montgomery–Vaughan threshold, where upper-bound sieves lose the signed correlation by a factor two. |

Complementary-divisor normal forms, boundary-retaining polarization, Ramanujan diagonalization,
Fermi inversion and Mellin continuation expose two distinct thresholds: sign-blind payment
requires damping above $1/2$; signed horizon-limit commutation includes $1/2$.
Below it, an infinite source can be paid while its truncated rows remain unbounded.

Start with the receivers (§1.2), then objects (§2), finite laws (§§3.1–3.8), recovery (§§3.9–3.11),
signs and continuation (§§3.16–3.17), phase diagrams and probes (§§3.18–3.19), and the actual signed
source (§§3.20–3.21). Pillars (§4) guide the research questions (§§6–7).

The PM route uses cofactor mean preservation, growing-cutoff transfer and Fermi traces; MC uses
oscillating probes and their anti-alignment criterion (all oscillating smooth-power probes below half damping
are unpaid iff RH). BVI shares the sieve objects, owns the Vaughan pronic calibration and feeds
PM, MC and CTF.

---

## 1. Why

### 1.1 The horizon barrier

Bézout–valuation controls the renormalized defect below the horizon: for $M+1\le N$ it is
nonpositive because the truncated divisor sum is complete. RH receivers also require control
above the horizon. Omitted divisors at a highly composite endpoint can make
$\lvert s_{N,c}(M+1)\rvert>\lvert s_{N,c}(1)\rvert$, reversing the boundary term's sign in
Dirichlet polarization. Transfer identities alone do not pay that term. The programme locates
these failures and extracts the conservation laws, sharp boundaries and classifications that survive.

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

Each receiver needs a horizon-uniform estimate on a literal arithmetic source.
The finite identities, classifications and obstructions below do not supply these estimates.

### 1.3 Why finite observers

Divisor sums, Fermi reciprocal-cell jumps and translation clocks observe the same weight with
different inversion and conditioning laws. Their sharp limits explain the horizon barrier:
the unit envelope ends at ratio five, trace conditioning grows as $(4/\pi^2)(\log_2N)^2$,
and deterministic successor dynamics ends at horizon two.

---

## 2. What

### 2.1 Sieve responses and horizon states

For a real weight $c:\mathbb N\to\mathbb R$ and horizon $N$,
$$
s_{N,c}(k)=\sum_{\substack{d\mid k\\1\le d\le N}}c(d),\qquad
Y_{N,c}(e)=\sum_{\substack{1\le d\le N\\e\mid d}}\frac{c(d)}d .
$$
The **observation state** $\sigma_N(k)=\operatorname{lcm}\{d\le N:d\mid k\}=\gcd(k,L_N)$,
$L_N=\operatorname{lcm}(1,\dots,N)$, determines the response for every weight, and conversely.
Squarefree-supported weights need only the **radical state** $\gcd(k,N\#)$, with primorial $N\#$;
dividing it by $N+1$ gives the **radical ratio**. The **observation phase** is $k\bmod L_N$.
An **$N$-rough** integer has no divisor $\le N$ except $1$; these form a monoid containing every
prime $p>N$. A prime $p\in(N,2N)$ and its four-divisible neighbour form a **rough-prime boundary**.

Weights include $\mu$ and $c_\varepsilon(d)=\mu(d)d^{-\varepsilon}$, whose complete divisor sum is
the **damped divisor function**
$\tau_\varepsilon(n)=\sum_{d\mid n}c_\varepsilon(d)=\prod_{p\mid n}(1-p^{-\varepsilon})\in[0,1]$,
and the PM route's power-damped Ramanujan cofactor row
$c_Q(d)=\operatorname{Re}\bigl(d\sum_{m\le Q/d}\mu(m)w_\varepsilon(dm)\bigr)$,
supported on squarefree integers in $[1,Q]$ (hence zero on multiples of four). The weight $c_\varepsilon$ has **Ramanujan coefficients**
$w_\varepsilon(e)=\sum_{e\mid d}\mu(d)d^{-1-\varepsilon}=\mathbb E[\tau_\varepsilon]\,\mu(e)/D_\varepsilon(e)$
with $D_\varepsilon(e)=\prod_{p\mid e}(p^{1+\varepsilon}-1)\ge\varphi(e)$, mean
$\mathbb E[\tau_\varepsilon]=\rho_\varepsilon=1/\zeta(1+\varepsilon)$, second
moment $\mathbb E[\tau_\varepsilon^2]$, **variance** $V(\varepsilon)$ and
**dissipation rate** $R(\varepsilon)=\sum_{e\ge2}(\varphi(e)-\mu(e))w_\varepsilon(e)^2$.
Coefficient perturbations are measured by the **divisor-incidence distance**
$W(N,K;c,b)=\sum_{d\le N}\lvert c(d)-b(d)\rvert\lfloor K/d\rfloor$.

### 2.2 Energies and defects

| Object | Definition |
|---|---|
| prefix $L^2$ energy | $\mathcal E_N(M;c)=\sum_{k=1}^Ms_{N,c}(k)^2$ |
| Selberg diagonal form | $Q_{\mathrm{Sel}}(N,c)=\sum_{e=1}^N\varphi(e)Y_{N,c}(e)^2$ |
| Bézout coprime form | $Q_{\mathrm{Bez}}(N,c)=\sum_{\gcd(d_1,d_2)=1}c(d_1)c(d_2)/(d_1d_2)$ |
| successor reserve | $\mathcal R_N(c)=Q_{\mathrm{Sel}}-Q_{\mathrm{Bez}}=\sum_{e=2}^N(\varphi(e)-\mu(e))Y_{N,c}(e)^2=\sum_{\gcd(d,e)>1}c(d)c(e)\gcd(d,e)/(de)$ |
| harmonic sum | $H_c(N)=\sum_{d\le N}c(d)/d=Y_{N,c}(1)$ |
| prefix discrepancy | $\sum_{d\le N}c(d)\lfloor M/d\rfloor-MH_c(N)=-\sum_{d\le N}c(d)\{M/d\}$ |
| primitive energy | $\mathcal E_{\mathrm{prim}}(N;c)$, the complete-period mean square of the centred discrepancy; $12\,\mathcal E_{\mathrm{prim}}=\sum_{2\le q\le N}J_2(q)Y_{N,c}(q)^2$ with the Jordan totient $J_2(q)=q^2\prod_{p\mid q}(1-p^{-2})$ |
| combined defect | $\mathcal D_N(M;c)=\sum_{d_1,d_2\le N}c(d_1)c(d_2)\{M/\operatorname{lcm}(d_1,d_2)\}+\text{Bézout sawtooth remainder}$ |
| renormalized defect | $\widetilde{\mathcal D}_N(M;c)=\mathcal D_N(M;c)-M\,\mathcal R_N(c)$ |
| short-window defect | $\widetilde{\mathcal D}_N(M_0,M;c)=\widetilde{\mathcal D}_N(M_0+M;c)-\widetilde{\mathcal D}_N(M_0;c)$ |
| period covariance | $\mathrm{Cov}_N(h;c)$, the complete-period centred covariance at lag $h$; $\mathrm{Cov}_N(h)=\sum_{2\le e\le N}c_e(h)Y_{N,c}(e)^2$ |
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

### 2.3 Horizon steps, slopes and bands

Stepping the horizon from $m-1$ to $m$ changes the prefix energy by the **band
step** $\Delta(m,B)$ with **band index** $B=\lfloor M/m\rfloor$; for the Möbius
weight $\Delta(m,B)=\mu(m)^2B+2\mu(m)\sum_{j\le B}s_{m-1,\mu}(mj)$. The
**Buchstab slope** of a squarefree horizon is
$$
\lambda(m)=1+2\mu(m)\sum_{d<m}\mu(d)\frac{\gcd(d,m)}d,\qquad
\lambda(p)=1-2\,\mathfrak m(p-1),\quad \mathfrak m(x)=\sum_{d\le x}\frac{\mu(d)}d ,
$$
and the **reserve slope** $\vartheta(m)=1+2\mu(m)\sum_{d<m,\ \gcd(d,m)>1}\mu(d)\gcd(d,m)/d$.
The **coprime harmonic Möbius sums** $\mathfrak m_f(x)=\sum_{d\le x,\ (d,f)=1}\mu(d)/d$
and the **gcd-twisted sums** $G_a(x)=\sum_{d\le x}\mu(d)\gcd(d,a)/d$ are the
quantities through which the prime number theorem enters. The **smooth core**
of a horizon $m$ in band $B$ is $\gcd(m,B\#)$; the **band average**
$A(B)$ is the mean of $\Delta(m,B)$ over horizons $m$, and the **energy
profile** $P(B)$ is the limit of $\mathcal E_N((B+1)N;\mu)/N$. For the damped
weight the **damped prime slope** is
$\lambda_\varepsilon(p)=p^{-\varepsilon}-2\sum_{d<p}\mu(d)d^{-1-\varepsilon}$ and the
**crossover scale** is $\Lambda(\varepsilon)=\log(1/(2\rho_\varepsilon))/\varepsilon$.

### 2.4 Fermi traces, schedules and pronic energies

On reciprocal cell $(1/(n+1),1/n]$, the Fermi response is
$F_{N,c}(n)=\sum_{d\le N}c(d)(2\lfloor n/2d\rfloor-\lfloor n/d\rfloor)$ with **boundary jump**
$J(n)=F(n)-F(n-1)$: $J(2m+1)=-s_{N,c}(2m+1)$ and
$J(2m+2)=2s_{N,c}(m+1)-s_{N,c}(2m+2)$. The cell's **pronic** weight is $1/(n(n+1))$.
The complete **sieve pronic energy** $P(N,c)=\sum_{n\ge1}s_{N,c}(n)^2/(n(n+1))$ and **selected
trace energy** $Q(N,c)$, reading odd and four-divisible boundaries, are summable at finite horizon.
Their homogeneous versions use $1/n^2$ in odd-ray coordinates $n=2^k(2j+1)$.

A **dyadic schedule** $S\subseteq\mathbb N$ reads boundaries with $v_2(n)\in S$. On a **dyadic ray**
$n=2^kb$, $b$ odd, put $z_k=s_{N,c}(2^kb)$: readings are $-z_0$ and $2z_{k-1}-z_k$.
The ray **saturates** at $L=\lfloor\log_2N\rfloor$, with $z_k=z_L$ for $k\ge L$; there are $L+2$
**slots**, $0,\dots,L$ and the saturated slot $L+1$. The **selected trace** omits slot $1$,
the **all-boundary trace** omits none, and the **one-gap trace** omits level $g$.
Their optimal physical inverse constants are $K_N=\sup P/Q$, $K^{\mathrm{all}}_N$ and $K_g(N)$;
$K_N^+$ restricts selected-trace coefficients to be nonnegative. A ray profile $y_0,\dots,y_L$
is synthesized by $c(1)=y_0$, $c(2^{k+1})=2^{k+1}y_{k+1}-2^ky_k$.
**Dirichlet chain**, **mixed chain**, **soft prefix** and **Robin ramp** name its boundary structures.

### 2.5 Valuation clocks

The **visibility clock** $\tau(q)=q/\operatorname{rad}(q)$ ($q\ge1$) controls the Ramanujan
coefficient $c_q(h)=\sum_{d\mid q}\mu(q/d)d\mathbf 1_{d\mid h}$: its normalized multiplier
$c_q(h)/\varphi(q)$ sees mode $q$ iff $\tau(q)\mid h$. It reconstructs von Mangoldt with a prime guard:
$$
\Lambda(d)=\begin{cases}\log\bigl(d/\tau(d)\bigr)&\text{if }d/\tau(d)\text{ is prime},\\0&\text{otherwise};\end{cases}
$$
The guard matters: $\tau(6)=1$ but $\Lambda(6)=0$. Clock wavelets subtract multipliers at
$p^a$ and $p^{a-1}$. For squarefree-supported weights, period covariance sees only $\operatorname{rad}(h)$.

### 2.6 Prime chains and the odd sector

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

### 2.7 Scales

| Scale | Meaning |
|---|---|
| $k\le N$ | sub-horizon: $s_{N,c}(k)=\sum_{d\mid k}c(d)$ is complete |
| $N<k\le2N$ | first octave: one omitted divisor, $s=\sum_{d\mid k}c(d)-c(k)$; for $\mu$, $s=-\mu(k)$; contains the rough-prime boundaries |
| $2N<k\le3N$ | second band: also $c(k/2)$ when $2\mid k$ |
| $3N<k\le4N$ | third band: also $c(k/3)$ when $3\mid k$ |
| $(B+1)N$ | linear window of band $B$: at most $B$ omitted divisors, all with cofactor $\le B$ |
| $k<5(N+1)$ | the damped unit envelope $\lvert s_N(c_\varepsilon,k)\rvert\le1$ holds, sharply |
| $k=5N+5$ | first failure: $N=6p-1$, $k=30p$, response $2$, for every prime $p>5$ |
| radical ratio $<11$ | Möbius responses of magnitude at most $2$; literal Möbius defects nonpositive |
| radical ratio $11$ | $N=105p-1$, $k=1155p$, response $-3$ |
| radical ratio $<13$ | Möbius responses of magnitude at most $3$ |
| radical ratio $13$ | $N=1155p-1$, $k=15015p$, response $4$ |
| radical ratio $Q$ | prime shells give responses of size $\asymp Q/\log Q$; the envelope is at most $Q$ |
| $M\le N^A$ | polynomial windows: paid by first-octave edges and rough-prime boundaries, eventually in $N$ |
| $M\ge10N^2$ | long windows, at every horizon $N\ge2$: the Möbius defect decreases with slope at least $1/(4N)$ and is nonpositive beyond $10N^2+8N$; for the damped weight beyond $10N^2+72N^{1+2\varepsilon}$ |
| $p\le M<p^2$ | quadratic window of a prime horizon: $\lfloor M/p\rfloor\le N$ lies in the exact zone |
| $\log p\lessgtr\Lambda(\varepsilon)$ | damped prime horizons inject below the crossover scale $\exp((1+o(1))\log(1/2\varepsilon)/\varepsilon)$ and dissipate above it |
| $L_N$ vs $N!$ | least full period divides $\operatorname{lcm}(1..N)$; $N!$ is a convenient period, not the same integer |

### 2.8 Parity data and receiver classes

For a weight $c$ with absolutely convergent **Ramanujan coefficients**
$W_c(e)=\sum_{e\mid d}c(d)/d$, the **receiver** is the pronic energy of the centred prefix of
$c*1$,
$$
E_T(c)=\sum_{n\le T}\frac{A_c(n)^2}{n(n+1)},\qquad A_c(n)=\sum_{j\le n}\bigl((c*1)(j)-W_c(1)\bigr),
$$
and $c$ is **paid** when $\sup_TE_T(c)<\infty$. For $c_\varepsilon$ this is the interior receiver of
§1.2 up to the factor $2$ and the constant $1/2$. The **damped class**
$\mathcal C(K,\varepsilon)$ is the set of weights with $\lvert c(d)\rvert\le Kd^{-\varepsilon}$.

**Sign-blind data** of a weight are the amplitude spectrum $\lvert W_c(e)\rvert$, the
complete-period translation statistics of $c*1$ (mean and every lag covariance
$\sum_ec_e(h)W_c(e)^2$) and the pronic mode masses $W_c(e)^2\mathcal G(e,e)$. They are invariant
under the **parity involution** $W\mapsto\lambda\cdot W$ on moduli ($\lambda(e)=\mu(e)$ on
squarefree support). Signed coefficients determine the weight (Möbius inversion over multiples),
so the parity is the whole content. A **parity pair** is two weights with the same sign-blind data,
one paid and one not. The **parity twin** of $c_\varepsilon$ is the nonnegative weight
$c'_\varepsilon(d)=(\rho_\varepsilon/U_\varepsilon)\,d\,\mu^2(d)\prod_{p\mid d}(p^{1+\varepsilon}-2)^{-1}$
with $W_{c'_\varepsilon}(e)=\mu(e)w_\varepsilon(e)$. **Parity rows** are horizon-$N$ sign twists of
truncated rows in Selberg coordinates. The **even flip** $c^\flat$ twists the even moduli; on
four-free weights $c^\flat=c+c_e\star(\delta_1-2\delta_2)$ with $c_e(d)=\mathbf 1_{\mathrm{odd}}(d)c(2d)$,
the Fermi cell factor $1-2\cdot2^{-s}$.

The **critical Wiener algebra** is the set of kernels $g$ with $\sum_q\lvert g(q)\rvert q^{-1/2}<\infty$,
Dirichlet series absolutely convergent on $\operatorname{Re}s\ge1/2$. The **pole value** of a
kernel at damping $\varepsilon$ is $K(1-\varepsilon)=\sum_jk(j)j^{-(1-\varepsilon)}$, its **pole
slope** $\sum_jk(j)\log j\,j^{-(1-\varepsilon)}$. A nonnegative weight has **dyadic masses**
$M_k=\sum_{2^k<d\le2^{k+1}}c(d)$ and **drift** $n\sum_{n<d\le2n}c(d)/d$. The **first pronic
moment** is $M(c)=\sum_nA_c(n)/(n(n+1))$, the **logarithmic moments** are $M(c\log^k)$, and the
higher von Mangoldt functions $\Lambda_{k+1}$ satisfy $\sum_{e\mid d}\Lambda_{k+1}(e)=\log^{k+1}d$
and are positive exactly on the $e\ge2$ with at most $k+1$ distinct prime factors. The **Mellin
cells** are $\Delta_n(\sigma)=n^{-\sigma}-(n+1)^{-\sigma}$, with $\Delta_n(1)$ the pronic weight, and
the **Mellin pairing** is $\Phi_c(\sigma)=\sum_nA_c(n)\Delta_n(\sigma)$. A multiplicative $f$
**pretends** to a model $g$ when $f(p)=g(p)$ at every prime; its **local factor** at $p$ is
$L_p=\sum_{e\ge0}f(p^e)p^{-e}$.

### 2.9 Glossary

| Object | Lean name |
|---|---|
| $s_{N,c}$, $Y_{N,c}$ | `sieveSeq`, `selbergMultiplesCoord` |
| observation state, modulus, phase; radical state | `horizonObservationState`, `horizonObservationModulus`, `horizonObservationPhase`, `horizonRadicalState` |
| $N$-rough, rough-prime boundary, prime shell | `IsTransHorizonRough`, `roughPrimeBoundary`, `primeShell` |
| weights $\mu$, $c_\varepsilon$, $\tau_\varepsilon$, cofactor row | `moebiusReal`, `pmPowerDampedRealWeight`, `pmPowerDampedDivisorCoeff`, `pmCofactorRealWeight` |
| Ramanujan coefficients $w_\varepsilon$, second moment, variance, dissipation rate, Bézout limit | `dampedRamanujanCoeff`, `pmPowerDampedSecondDensity`, `pmPowerDampedDivisorVariance`, `dampedDissipationRate`, `dampedBezoutLimit` |
| damped autocorrelation $A_\varepsilon(h)$, gcd kernel and tail | `dampedAutocorrelation`, `dampedGcdKernel`, `dampedGcdTail` |
| incidence distance, normalized perturbation | `divisorIncidenceDistance`, `normalizedSquarefreeMobiusPerturbation` |
| $\mathcal E_N(M;c)$, band operator | `sieveL2PrefixEnergy`, `sieveBandSeq` |
| $Q_{\mathrm{Sel}}$, $Q_{\mathrm{Bez}}$, $\mathcal R_N$, Poincaré excess | `selbergTotientDiagonalForm`, `bezoutCoprimeQuadraticForm`, `sieveSuccessorReserve`, `sievePoincareExcess` |
| combined, renormalized, short-window defect | `sieveCombinedPrefixDefect`, `sieveRenormalizedPrefixDefect`, `shortWindowRenormalizedDefect` |
| harmonic sum, discrepancy, fractional sum, primitive energy | `finiteHarmonicSum`, `sievePrefixDiscrepancy`, `sievedFractSum`, `sievePrimitiveEnergy` |
| period covariance | `periodCovariance` |
| sawtooth $\tilde B_1$, $W_{N,c}$, active, inactive | `centeredDiscreteSawtooth`, `weightedCenteredSawtoothSum`, `activeCenteredSawtoothSum`, `inactiveCenteredSawtoothSum` |
| complementary quotient tail | `complementaryQuotientTail` |
| period Dirichlet energy, period window | `horizonPeriodDirichletEnergy`, `horizonPeriodDefectWindow` |
| band step $\Delta(m,B)$, class value, rough density $\delta_B$, band average $A(B)$, profile $P(B)$ | `moebiusBandStep`, `bandClassValue`, `bandRoughDensity`, `bandAverageStep`, `cofinalMobiusQuadraticProfile` |
| Buchstab slope, reserve slope, damped prime slope, crossover scale | `buchstabSlope`, `reserveSlope`, `dampedPrimeSlope`, `dampedCrossoverScale` |
| coprime harmonic and gcd-twisted Möbius sums, prime-factor window correction | `coprimeHarmonicMoebius`, `gcdTwistedHarmonicMoebius`, `primeFactorWindowCorrection` |
| Fermi cell matrix, response, jump | `fermiCellMatrix`, `fermiCellResponse`, `fermiBoundaryJump` |
| pronic weight, $P$, $Q$, homogeneous forms | `pronicSeq`, `sieveTotalPronicEnergy`, `fermiSelectedTotalPronicEnergy`, `sieveHomogeneousEnergy`, `fermiSelectedHomogeneousEnergy` |
| all-boundary, twice-odd, one-gap and level energies; ray energies | `fermiAllBoundaryPronicEnergy`, `fermiTwiceOddPronicEnergy`, `fermiGapPronicEnergy`, `fermiLevelPronicEnergy`, `fermiRaySieveEnergy`, `fermiRayAllBoundaryEnergy`, `fermiRayGapEnergy` |
| four-free projection, coefficient transport, reading | `fermiFourFreeWeight`, `fermiSelectedCoefficient`, `fermiSelectedReading` |
| $K_N$, $K_N^+$, $K^{\mathrm{all}}_N$, $K_g(N)$ | `fermiPhysicalInverseConstant`, `fermiNonnegativePhysicalInverseConstant`, `fermiAllBoundaryInverseConstant`, `fermiGapInverseConstant` |
| schedules, slots, profile packets, quarter waves, mixed constant | `FermiScheduleInjective`, `FermiSlotObserved`, `fermiDyadicProfilePacket`, `gapBottomWave`, `gapTopWave`, `quarterWaveAngle`, `mixedChainConstant` |
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
| Ramanujan coefficients of a weight, receiver energy, paid receiver, damped class | `weightRamanujanCoeff`, `weightPronicEnergy`, `ReceiverBounded`, `DampedClass` |
| parity twin, even-flip row, dyadic mass | `parityTwinWeight`, `evenFlipRow`, `dyadicMass` |
| critical Wiener algebra, pole value, first pronic moment, higher von Mangoldt | `CriticalWiener`, `poleValue`, `firstPronicMoment`, `higherVonMangoldt` |

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
quotients lie in $[1,B]$, which gives the band normal forms of §2.7 and the
$B$-rough extension of the first-octave law up to $(B+1)N$. Between two rough
checkpoints the defect obeys the excursion law
$2(\widetilde{\mathcal D}_N(M)-\widetilde{\mathcal D}_N(r-1))=-\sum_{k=r}^M(\Delta s)^2+s(M+1)^2-s(1)^2$,
so every scale with $s(M+1)^2\le s(1)^2$ sits strictly below the already
nonpositive checkpoint; pronic cells $(r-1)r$ and $r(r+1)$ at a rough $r$
collapse to the linear neighbours $r-1$ and $r+1$.

A second exact normal form lives on the divisor side. For a prime $p\mid k$ the
divisors $d$ and $pd$ with $p\nmid d$ carry opposite Möbius signs and every pair
inside the horizon cancels, so
$$
s_{X,\mu}(k)=\sum_{\substack{d\mid k,\ p\nmid d\\ X/p<d\le X}}\mu(d):
$$
the response at a multiple of $p$ lives on the top $p$-adic window of the
$p$-free divisors, and for even $k$ it is the sum of $\mu$ over the odd divisors
in the top octave (`sieveSeq_moebiusReal_prime_mul_eq_window`). Pairing each
$p$-free divisor of a squarefree $a\ge2$ with a second prime factor shows that
any divisor subset has Möbius sum at most $2^{\omega(a)-1}$ in modulus
(`abs_sum_filter_divisors_moebiusReal_le_half_card`), giving the universal
radical-support envelope $\lvert s_{N,\mu}(r)\rvert\le 2^{\omega(r)-2}$ for every
squarefree $r$ with $\omega(r)\ge2$ (`abs_sieveSeq_moebiusReal_squarefree_le_two_pow_sub_two`).
Together with squarefree saturation this is the prime-chain
renormalization $s_H(c,pb)-s_H(c,b)=s_{H/p}(c(p\,\cdot),b)$ of §3.9.

### 3.3 The envelope ladder

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
$<5(N+1)$.

Beyond its horizon a squarefree Möbius response is a truncated Möbius divisor
sum of the radical: for squarefree $r\ge2$,
$$
s_{N,\mu}(r)=-\mu(r)\sum_{\substack{q\mid r\\ q(N+1)\le r}}\mu(q),\qquad
\lvert s_{N,\mu}(r)\rvert\le\frac r{N+1},
$$
so only the divisors below the radical ratio are seen, and the envelope is a
**ladder indexed by the ratio**: every truncated Möbius divisor sum below $11$
has magnitude at most two (the only positive channels $6,10$ need the negative
channels $2,3,5$, and the channel $7$ opens only after $6$) and below $13$ at
most three, so $\lvert s_{N,\mu}(k)\rvert\le2$ whenever the radical state of $k$
is below $11(N+1)$ and $\le3$ below $13(N+1)$, at every horizon. Both rungs are
exact: $N=105p-1$, $k=1155p$ gives $-3$ at ratio $11$ and $N=1155p-1$,
$k=15015p$ gives $4$ at ratio $13$. In general, for a set $P$ of primes with
largest element $Q$ and all pair products above $Q$, and a prime $\ell>Q$, the
integer $\ell\prod P$ read at ratio exactly $Q$ has response $\pm(\lvert P\rvert-1)$;
the shell of primes in $(\sqrt Q,Q]$ makes the response at ratio $Q$ as large as
$\pi(Q)-\pi(\sqrt Q)-1$. The ladder grows almost linearly, $Q/\log Q\lesssim\max\lvert s\rvert\le Q$,
so every method that pays the endpoint square by integer jump energy must fail
at ratios of size $(\log N)^{O(1)}$; that is where the long-window regime of
§3.4 takes over.

The unit envelope is a method boundary, not a sign boundary. The Möbius path is
integer valued, so its jump energy over a nonempty prefix is at least
$1+\lvert s(M+1)\rvert$ and
$2\widetilde{\mathcal D}_N(M;\mu)\le s(M+1)^2-\lvert s(M+1)\rvert-2$:
endpoint magnitude two is admissible, so the Möbius renormalized defect is
nonpositive whenever the radical state of $M+1$ is below $11(N+1)$, and a
positive Möbius defect needs radical ratio at least $11$. By the $2^{\omega(r)-2}$
radical envelope, every prefix with $\omega(\gcd(M+1,N\#))\le3$ also has
$\lvert s_{N,\mu}(M+1)\rvert\le2$ and $\widetilde{\mathcal D}_N(M;\mu)\le0$ at
every horizon (`moebius_prefix_defect_nonpos_of_card_primeFactors_radical_le_three`,
`moebius_prefix_defect_nonpos_of_card_primeFactors_le_three`, and $\le-1$ when
$\omega\le2$, $N\ge2$, $M\ge1$, `moebius_prefix_defect_le_neg_one_of_card_primeFactors_radical_le_two`).
Consequently $\widetilde{\mathcal D}_N(M;c_\varepsilon)\le0$ for all $N\le4$,
$\varepsilon\ge0$, and $M\in\mathbb N$ (`pmPowerDamped_defect_nonpos_of_le_four`),
and $\widetilde{\mathcal D}_N(M;\mu)\le0$ for all $N\le10$ and $M\in\mathbb N$
(`moebius_defect_nonpos_of_le_ten`). A prime
$p\in(N,2N]$ gives the excursion $1,0,1,0$ at $1,2,p,2p$ and the strict margin
$\widetilde{\mathcal D}_N(M;\mu)\le-1$ on the certified fibres. Perturbation
radii in the damping or in the incidence distance (the ball $W\le1/20$ around
$\mu$ keeps $\widetilde{\mathcal D}\le-59/100$ on the certified fibres) exist
but shrink with $N$; they are not how the sign is proved at large horizons.

### 3.4 The global sign of the defect

Two dissipation regimes control the renormalized defect above the horizon, and
they overlap.

**Polynomial windows.** At fixed damping $\varepsilon>0$ the sieve below its
horizon is the complete coefficient $\tau_\varepsilon$, which steps from
$\tau_\varepsilon(p)=1-p^{-\varepsilon}$ at an odd prime $p<N$ to an even argument
where $\tau_\varepsilon\le1-2^{-\varepsilon}$; each such prime boundary dissipates at
least $(2^{-\varepsilon}-p^{-\varepsilon})^2$ of jump energy, so the Dirichlet
energy of every prefix reaching the horizon is at least $\kappa_\varepsilon N/\log N$
while the endpoint divisor square is a small power. At $\varepsilon=0$ this
dissipation vanishes, and the literal Möbius weight waits for the first octave.
The mechanism that does not degenerate is the **rough-prime boundary**: a prime
$p\in(N,2N)$ is $N$-rough, so $s(p)=s(1)=1$ exactly at every damping, while
one of its neighbours $p\pm1$ is divisible by four and lies in $[N,2N]$, where
the only omitted divisor is the argument itself, which is not squarefree, so
the response there is $\tau_\varepsilon(p\pm1)\le1-2^{-\varepsilon}$. Each such prime
carries a boundary of jump energy at least $4^{-\varepsilon}$, distinct primes
carry distinct boundaries, and the prime number theorem gives jump energy at
least $N/(8\log N)$ uniformly for $0\le\varepsilon\le1$. Hence, eventually in
$N$, $\widetilde{\mathcal D}_N(M;c_\varepsilon)\le-\kappa\,N/\log N$ on every window
$N\le M+1\le N^{A}$, and by radical-state transport the defect is nonpositive
at every prefix of any size whose horizon radical state is at most a fixed
power of the horizon.

**Long windows and small horizons.** Applying the Montgomery–Vaughan constant
$N(N-1)$ directly to the conjugate-paired step-difference amplitudes
$(1-\zeta_e)y(e)$ gives the reserve-proportional window Dirichlet sandwich
$\lvert D_W-2K\mathcal R_N(c)\rvert\le 2N(N-1)\mathcal R_N(c)\le 4N(N-1)V(c)$
and the coercivity bound $D_W\ge 2(K-N(N-1))\mathcal R_N(c)\ge(K-N(N-1))V(c)$
(`abs_shortWindowDirichletEnergy_sub_reserve_le_mv`, `shortWindowDirichletEnergy_bounds_mv`),
reducing the window Poincaré constant from $10N^2-5$ to $2N(N-1)$
(`window_poincare_mv`) and giving the long-window dissipation law
$2\widetilde{\mathcal D}_N(M;c)\le 2H_c(N)^2-s_{N,c}(1)^2-(M-(2N^2-2))V(c)$
(`two_mul_sieveRenormalizedPrefixDefect_le_mv`). The infimal window sandwich and
reserve Dirichlet constants $S_{\mathrm{opt}}(N)$ and $R_{\mathrm{opt}}(N)$ are
attained at every $N\ge2$ and satisfy $\Phi(N)-2\le S_{\mathrm{opt}}(N)\le N(N-1)$
and $0\le R_{\mathrm{opt}}(N)\le N(N-1)$ (`optimalWindowSandwichConstant_bounds`,
`optimalReserveDirichletConstant_bounds`, `window_poincare_and_prefix_dissipation_optimal`).
A Bertrand prime $p\in(N/2,N]$ has the
single-multiple Selberg coordinate $c(p)/p$, so $V\ge(p-1)c(p)^2/p^2$, at least
$1/(2N)$ for the Möbius weight. For the Möbius weight $\lvert H_\mu(N)\rvert\le1$
and $s_{N,\mu}(1)^2=1$, so at every horizon $N\ge2$
$2\widetilde{\mathcal D}_N(M;\mu)\le 1-(M-(2N^2-2))/(2N)$, nonpositive for all
$M\ge 2N^2+2N-2$ (`moebius_defect_nonpos_of_mv_window`, improving $10N^2+8N$ by
more than $5\times$); at $N=11,12$ the threshold is $2N^2+2N-2\le 310<1154=3\cdot5\cdot7\cdot11-1$,
overlapping the radical-state region $1155\nmid(M+1)$ where $\lvert s_{N,\mu}(M+1)\rvert\le2$
across $[310,1153]$ to certify $\widetilde{\mathcal D}_N(M;\mu)\le0$ for every
$N\le12$ and every $M\in\mathbb N$ (`moebius_defect_nonpos_of_le_twelve`). At large horizons the white-noise floor $V\ge1/288$ of §3.6 makes
the slope horizon-uniform, $2\widetilde{\mathcal D}_N(M;\mu)\le4-(M-10N^2)/288$.
For the damped weight $\lvert H_\varepsilon(N)\rvert\le3$ and the threshold shrinks from
$10N^2+72N^{1+2\varepsilon}$ to $2N^2-2+34N^{1+2\varepsilon}$
(`pmPowerDamped_defect_nonpos_of_mv_window`). The polynomial-window regime has not yet ended
there, so no prefix is left uncovered: **at every sufficiently large horizon
the renormalized defect is nonpositive at every prefix**, strictly negative at
every prefix $M\ge2N$ for the literal Möbius weight, for every fixed damping
$\varepsilon>0$, and uniformly for all $\varepsilon\in[0,1]$ with one threshold
independent of the damping. Only the polynomial-window regime is eventual; the
long-window law is explicit at every horizon.

**The actual receiver row.** The cofactor row $c_Q$ is supported on $[1,Q]$, so
its horizon-$Q$ response is its complete divisor sum at every integer, which by
the Ramanujan expansion is the truncation $s_Q(n)=\operatorname{Re}\sum_{q\le Q}w_\varepsilon(q)c_q(n)$
of $\tau_\varepsilon(n)=\sum_qw_\varepsilon(q)c_q(n)$. With
$\lvert w_\varepsilon(q)\rvert\le q^{-1-\varepsilon}$ and $\lvert c_q(n)\rvert\le\sum_{d\mid(n,q)}d$,
$$
\lvert s_Q(n)-\tau_\varepsilon(n)\rvert\ \le\ \frac{1+\varepsilon}\varepsilon\,\tau(n)\,Q^{-\varepsilon}
\qquad(n\ge1),
$$
uniformly small on every polynomial range $n\le Q^r$. Its exact Haar mean
$H_{c_Q}(Q)=Y_Q(1)=\rho_\varepsilon$ (`finiteHarmonicSum_pmCofactorRealWeight`,
`selbergMultiplesCoord_one_pmCofactorRealWeight`) removes the linear mean-drift dipole.
The resulting prefix and pronic error bounds are developed in §3.21. For the defect sign,
the complete damped divisor function obeys the
global unit envelope $0\le\tau_\varepsilon\le1=\tau_\varepsilon(1)$ and has first
jump $\tau_\varepsilon(1)-\tau_\varepsilon(2)=2^{-\varepsilon}$; polarization with the
truncation error $\eta=4^{-\varepsilon}/64$ gives
$2\widetilde{\mathcal D}_Q(M)\le-(2^{-\varepsilon}-2\eta)^2+(1+\eta)^2-(1-\eta)^2<0$ on
polynomial ranges, and the long-window law with the terminal prime mode
$(p-1)\rho_\varepsilon^2/(p^{1+\varepsilon}-1)^2$ covers the rest. No rough primes, no
ladder and no ratio-five boundary enter: the sign of the receiver row is
controlled by one jump.

### 3.5 Spike cancellation and the arithmetic uncertainty principle

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

### 3.6 Period laws, white noise and the torus Poincaré inequality

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

**The Möbius observer is white.** The lag-$h$ period covariance is diagonal in
the Selberg coordinates with the Ramanujan lag weights as eigenvalues,
$\mathrm{Cov}_N(h)=\sum_{2\le e\le N}c_e(h)Y_N(e)^2$, and for the Möbius weight
$Y_N(f)=\mu(f)f^{-1}\mathfrak m_f(N/f)$. Each prime of a squarefree $f$ at most
doubles the coprime harmonic sum (through the recursion
$\mathfrak m_{fp}(n)=\mathfrak m_f(n)+\mathfrak m_{fp}(n/p)/p$), so
$\lvert\mathfrak m_f\rvert\le\tau(f)$, and $\mathfrak m_f\to0$ by the prime
number theorem. The lag weights are bounded by $\sigma(h)$, so every lag $h\ge1$
sees only the summable masses $\tau(f)^2/f^2$ against null sums:
$\mathrm{Cov}_N(h;\mu)\to0$, and in particular the Bézout form
$Q_{\mathrm{Bez}}(N;\mu)=\sum_{f\le N}\mu(f)f^{-2}\mathfrak m_f(N/f)^2\to0$, so
successive Möbius observations decorrelate completely over a period and
$\mathcal R_N(\mu)-Q_{\mathrm{Sel}}(N;\mu)\to0$. The variance does not collapse:
on the top octave $N/2<e\le N$ the harmonic sum is $\mathfrak m_e(1)=1$, so
$\mathrm{Cov}_N(0;\mu)\ge\sum\varphi(e)/e^2$ over the odd squarefree integers
there, and Cauchy–Schwarz against $\sum1/\varphi(e)\le8$ with the density
$4/\pi^2$ of odd squarefree integers gives $\mathrm{Cov}_N(0;\mu)\ge1/288$ at
all large horizons. The variance has a limit: $\mathrm{Cov}_N(0;\mu)\to\kappa$, the slope of
the cofinal Möbius profile (Bézout–Valuation Incidence §3.10), so $\kappa\ge1/288$ and
$\mathcal R_N(\mu)\to\kappa$
([TheMoebiusPeriodVarianceConvergesToTheCofinalSlope](TheMoebiusPeriodVarianceConvergesToTheCofinalSlope.lean)).
Hence the normalized correlation tends to zero at every
positive lag, every translation dissipates twice the variance, and the
dissipation rate has the horizon-uniform floor $\mathcal R_N(\mu)\ge1/576$: the
Möbius renormalized defect drops by at least $L/576$ per complete period.

**The reserve has a horizon law.** Since $1/\operatorname{lcm}(d,e)=\gcd(d,e)/(de)$
the coprime pairs of the Selberg kernel are the Bézout kernel, so the dissipation
rate is the non-coprime part of the lcm kernel and across a horizon step
$$
\mathcal R_m-\mathcal R_{m-1}=\frac1m\Bigl(c(m)^2+2c(m)\sum_{\substack{d<m\\ \gcd(d,m)>1}}c(d)\frac{\gcd(d,m)}d\Bigr),
\qquad \mathcal R_p-\mathcal R_{p-1}=\frac{c(p)^2}p ,
$$
for every weight at every prime: the Möbius cancellation that governs the
Selberg and Bézout steps separately drops out of their difference, weights
vanishing on composites dissipate at exactly $\sum_{p\le N}c(p)^2/p$, and the
Möbius reserve slope satisfies $\vartheta(p)=1$ and $\vartheta(aq)\to\lambda(a)$.

### 3.7 Buchstab energy calculus

Across a horizon step the prefix energy changes by
$$
\mathcal E_{N+1}(M)-\mathcal E_N(M)=c(N+1)^2\Bigl\lfloor\frac M{N+1}\Bigr\rfloor
+2c(N+1)\sum_{j=1}^{\lfloor M/(N+1)\rfloor}s_{N,c}\bigl((N+1)j\bigr),
$$
and the step vanishes when $N+1$ is not squarefree and $c$ is
squarefree-supported. Dilating a sieve by $m$ counts each divisor $d$ once per
multiple of $d/\gcd(d,m)$, $\sum_{j\le B}s_{N,c}(mj)=\sum_{d\le N}c(d)\lfloor B\gcd(d,m)/d\rfloor$,
which gives the exact Möbius horizon step at every horizon $m$ and the **slope
law**: at a squarefree horizon the step is $B\lambda(m)$ up to an error at most
$2(m-1)$ independent of $M$. At a prime the slope is $1-2\mathfrak m(p-1)$, so by
the prime number theorem every large prime horizon **injects** energy at every
ratio $B\ge2$ (three regimes: the quadratic window, where the floor identity is
exact; $p\le B<4p$ through Mertens values and $M(x)=o(x)$; $B\ge4p$ through
$\mathfrak m(p-1)\le1/4$), while the ratio $B=1$ is the first-octave step $-1$.
Composite horizons can have negative slope: at $m=6$ the step is exactly
$-B-2\lfloor B/5\rfloor$ for every prefix. The slope is the horizon derivative of
the period mean square, $Q_{\mathrm{Sel}}(m)-Q_{\mathrm{Sel}}(m-1)=\mu(m)^2\lambda(m)/m$,
and it is inherited under large primes: for squarefree $a$ and a prime $q>a$,
$\lambda(aq)=\lambda(a)-2\mu(a)\bigl(G_a(aq-1)+A(a)/q\bigr)$ with $G_a\to0$ (a
finite combination of coprime harmonic Möbius sums, each null by the
contracting recursion), hence $\lambda(aq)\to\lambda(a)$: rough absorption acts
on horizon steps, large primes are invisible to the slope, and
$\lambda(q)\to1$, $\lambda(2q)\to-1$, $\lambda(3q)\to0$, $\lambda(pq)\to1-2\mathfrak m(p-1)$.

**The smooth-core law.** Past the horizon $s_{m-1,\mu}(mj)=-\sum_{q\mid mj,\ q\le j}\mu(mj/q)$,
and the complementary quotients $q\le j\le B$ cannot see a prime factor of $m$
larger than $B$. Hence in band $B$ a squarefree horizon $m=rm'$ whose cofactor
$m'$ has only prime factors $>B$ satisfies $\Delta(rm',B)=\Delta(r,B)$ for $r\ge2$
and $\Delta(m',B)=B-2$ for $r=1$: the step depends only on the smooth core
$\gcd(m,B\#)$ and takes at most $2^{\pi(B)}+1$ values in each band, one per
squarefree divisor of $B\#$ and the value $0$ of non-squarefree horizons. The
first octave, the parity dichotomy of the second band and the $(2,3)$-adic law
of the third are the cases $B\le3$; explicit classes are $\Delta(2,B)=-B$,
$\Delta(3,B)=2\lfloor B/2\rfloor-B$, $\Delta(6,B)=-B-2\lfloor B/5\rfloor$. In band $1$,
every squarefree core $r\ge1$ has negative step $v_1(r)=-1<0$ (`bandClassValue_first_band`); in
band $2$, the step is $-2<0$ on even squarefree cores and $0$ on odd squarefree cores
(`bandClassValue_second_band`). On the
divisor side the prime pairing of §3.2 splits every squarefree step
$\Delta(pa,B)=-B-2\mu(a)\sum_{a<d<pa,\ p\nmid d}\mu(d)\lfloor B\gcd(d,a)/d\rfloor$ into
the universal dissipation $-B$ and a window correction (`primeFactorWindowCorrection`): the rough
core $r=1$ has negative step iff $B=1$ (`bandClassValue_one_trichotomy`), a composite or prime core
$r=pa$ ($p\nmid a$) has negative step $v_B(pa)<0$ iff $2\mu(a)W_p(a,B)>-B$
(`bandClassValue_prime_mul_neg_iff`), and dividing by $B\to\infty$ gives the prime-factor Buchstab
slope law $\lambda(pa)=-1-2\mu(a)\sum_{a<d<pa,\ p\nmid d}\mu(d)\gcd(d,a)/d$
(`tendsto_moebiusBandStep_div`, `buchstabSlope_prime_mul`). For an odd prime $q$
no odd $d\in(q,2q)$ meets $q$, so the horizon $2q$ steps by exactly $-B$ in every
band $B\le q+1$, and $\mathcal E_{2q}(M)=\mathcal E_{2q-1}(M)-\lfloor M/(2q)\rfloor$
for $M<2q(q+2)$.

**Band averages, radical-invariant jumps, and the energy profile.** The horizons of core $r$ in
band $B$ have density $\delta_B/r$ with $\delta_B=(6/\pi^2)\prod_{p\le B}p/(p+1)$, so the
mean step of band $B$ exists and is the finite class average
$A(B)=\delta_B\sum_{r\mid B\#}v_B(r)/r$ with $v_B(1)=B-2$, $v_B(r)=\Delta(r,B)$.
Telescoping the horizon from the top value $\mathcal E_M(M;\mu)=1$ down to $N$
through the bands $(M/(b+1),M/b]$ gives
$$
P(B)=\lim_N\frac{\mathcal E_N((B+1)N;\mu)}N=-(B+1)\sum_{b\le B}\frac{A(b)}{b(b+1)},
\qquad A(B)=(B+1)P(B-1)-BP(B)=P(B-1)-B\gamma_B,
$$
where $\gamma_B=P(B)-P(B-1)\ge0$ is the band slope (`bandAverageStep_eq_profile_sub_slope`), so
$A(B)/B\to0$ since $P(B)/B$ and $\gamma_B$ share the limit $\kappa$ (`tendsto_bandAverageStep_div`).
Stepping from band $B$ to $B+1$ gives the exact divisor-sum jump law
$$
A(B+1)-A(B)=-(B+1)\bigl(P(B+1)-2P(B)+P(B-1)\bigr)=-\frac6{\pi^2}\sum_{a\mid(B+1)}c_{\mathrm{step}}(a),
$$
where $c_{\mathrm{step}}(1)=1$ and $c_{\mathrm{step}}(a)=2a\,\mathrm{moebiusSigma}(a)\sum_{b\le a-1,\ (b,a)=1}\mathrm{moebiusSigma}(b)$
for $a\ge2$, vanishing off squarefree $a$ (`bandAverageStep_succ_sub_eq_sum_divisors`,
`bandStepDivisorWeight_eq_zero_of_not_squarefree`). Because only squarefree divisors contribute,
$A(B+1)-A(B)$ depends only on the radical $\operatorname{rad}(B+1)$
(`bandAverageStep_succ_sub_eq_of_primeFactors_eq`), and at every prime power $p^k\ge3$ it equals
$-\frac6{\pi^2}(1+c_{\mathrm{step}}(p))$ (`bandAverageStep_prime_pow_sub`). Evaluating $c_{\mathrm{step}}$
at $2,3,5,6,7,10$ gives the exact values through $B=10$ (in units of $\rho=6/\pi^2$):
$A(1)=-1$, $A(2)=-\frac23$, $A(3)=-\frac23$, $A(4)=-\frac13$, $A(5)=-\frac{23}{36}$,
$A(6)=-\frac5{36}$, $A(7)=-\frac59$, $A(8)=-\frac29$, $A(9)=-\frac29$, and the first positive
value $A(10)=+\frac19$ (`bandAverageStep_neg_of_le_nine`, `bandAverageStep_ten_pos`), while at
every power of five $P(5^k)-2P(5^k-1)+P(5^k-2)=\frac{11}{36\cdot5^k}\rho>0$, so $P$ fails
concavity infinitely often (`cofinalMobiusQuadraticProfile_second_diff_five_pow_pos`,
`cofinalMobiusQuadraticProfile_not_concave`). Centering the
$q=1$ quotient yields $(B-2)(\mathcal E_n-\mathcal E_{n+1})=S_2^2-((B-2)\mu(n+1)+S_2)^2$
with $S_2=\sum_{2\le q\le B}s_{n,\mu}(q(n+1))$, and a completed square gives the
universal subadditivity
$\mathcal E_N(M)\le\mathcal E_{N+1}(M)+\mathcal E_N(\lfloor M/(N+1)\rfloor)$ at
prime horizons.

### 3.8 The damped observer

**Freezing into $\tau_\varepsilon$.** On the linear window $k\le(B+1)N$ an integer
has at most $B$ divisors above the horizon, each damped by at least
$(N+1)^{-\varepsilon}$, so $\lvert\tau_\varepsilon(k)-s_N(k;c_\varepsilon)\rvert\le B(N+1)^{-\varepsilon}$
uniformly, and $\mathcal E_N((B+1)N;c_\varepsilon)/N\to(B+1)\mathbb E[\tau_\varepsilon^2]$.
The damped profile is linear with slope $\mathbb E[\tau_\varepsilon^2]\sim\varepsilon/2$,
erasing Möbius band structure. Over complete periods the trans-horizon tail
$\tau_\varepsilon-s_N$ has mean square at most the tail beyond $N$ of the convergent
gcd series $G(d,e)=(de)^{-\varepsilon}/\operatorname{lcm}(d,e)$ (its boxes are
Selberg forms of $d^{-\varepsilon}$, bounded by $\zeta(1+\varepsilon)^2\zeta(1+2\varepsilon)$),
so $Q_{\mathrm{Sel}}(N;c_\varepsilon)\to\mathbb E[\tau_\varepsilon^2]$ and
$\mathrm{Cov}_N(0;c_\varepsilon)\to V(\varepsilon)\sim\varepsilon/2$. Against the Möbius
floor $1/288$ this is the first non-commuting limit:
$\lim_{\varepsilon\to0}\lim_N\mathrm{Cov}_N(0;c_\varepsilon)=0<1/288\le\kappa=\lim_N\mathrm{Cov}_N(0;\mu)$.
Fixed damping suppresses the trans-horizon divisors carrying Möbius variance.

**Parseval and the receiver's spectrum.** The Selberg coordinates converge to
the Ramanujan coefficients, $Y_N(e;c_\varepsilon)\to w_\varepsilon(e)$, dominated by
$\zeta(1+\varepsilon)e^{-1-\varepsilon}$, so the period forms converge term by term
and
$$
\mathbb E[\tau_\varepsilon^2]=\sum_e\varphi(e)w_\varepsilon(e)^2,\qquad
V(\varepsilon)=\sum_{e\ge2}\varphi(e)w_\varepsilon(e)^2,\qquad
Q_{\mathrm{Bez}}(N;c_\varepsilon)\to\sum_e\mu(e)w_\varepsilon(e)^2 .
$$
The receiver row's Selberg coordinates are $w_\varepsilon(e)$ for $e\le Q+1$; its period variance
increases to $V(\varepsilon)$ and its dissipation is at most $2V(\varepsilon)$. These bounds are
horizon-uniform and, at small damping, below the Möbius floors. Lag covariances
converge to the damped autocorrelation
$A_\varepsilon(h)=\sum_{e\ge2}c_e(h)w_\varepsilon(e)^2$ with
$\lvert A_\varepsilon(h)\rvert\le16\sigma(h)\mathbb E[\tau_\varepsilon]^2$, and since
$\mathbb E[\tau_\varepsilon]\sim\varepsilon$ while $V(\varepsilon)\sim\varepsilon/2$,
$A_\varepsilon(h)/V(\varepsilon)\to0$: the correlation structure commutes with the
damping limit (white, like Möbius) while the variance does not.

**Exact linear dissipation.** The dissipation rate converges,
$\mathcal R_N(c_\varepsilon)\to R(\varepsilon)=\sum_{e\ge2}(\varphi(e)-\mu(e))w_\varepsilon(e)^2\in(0,2V(\varepsilon)]$,
with $R(\varepsilon)\ge2w_\varepsilon(2)^2$. For every weight and horizon the Cesàro
mean of the successor energy $(\Delta s_N)^2$ is $2\mathcal R_N$; the complete
damped divisor function is not periodic, but the gcd tail approximates it in
mean square by periodic responses, which transfers the law:
$X^{-1}\sum_{k\le X}(\tau_\varepsilon(k+1)-\tau_\varepsilon(k))^2\to2R(\varepsilon)$. On the
linear window the gradient energy is therefore $2(B+1)NR(\varepsilon)+o(N)$ and
$$
\frac{\widetilde{\mathcal D}_N((B+1)N;c_\varepsilon)}N\ \longrightarrow\ -(B+1)R(\varepsilon):
$$
the prime-boundary mechanism of §3.4 belongs to positive-density Haar dissipation.
Since $R(\varepsilon)=V(\varepsilon)-A_\varepsilon(1)$,
$\lvert A_\varepsilon(1)\rvert\le16\,\mathbb E[\tau_\varepsilon]^2=O(\varepsilon^2)$
and $V(\varepsilon)\sim\varepsilon/2$, we have $R(\varepsilon)/\varepsilon\to\tfrac12$,
$R(\varepsilon)/V(\varepsilon)\to1$ and small-damping window slope
$\lim_{\varepsilon\to0}\varepsilon^{-1}\lim_N\widetilde{\mathcal D}_N((B+1)N;c_\varepsilon)/N=-(B+1)/2$.
At second order the rates separate:
$$
V(\varepsilon)=\tfrac\varepsilon2-\varepsilon^2+o(\varepsilon^2),\qquad
R(\varepsilon)=\tfrac\varepsilon2+o(\varepsilon^2),\qquad
A_\varepsilon(1)=-\varepsilon^2+o(\varepsilon^2):
$$
Euler's constant cancels in the second moment
$\mathbb E[\tau_\varepsilon^2]=H(\varepsilon)\zeta(1+2\varepsilon)/\zeta(1+\varepsilon)^2=\varepsilon/2+o(\varepsilon^2)$,
with the Euler-product variance correction obeying the exact second-order law
$(1-K_\varepsilon)/\varepsilon^2\to\sum_p(\log p/(p-1))^2$
(`tendsto_one_sub_varianceCorrection_div_sq`); parity kills the lag-one Bézout mean to $O(\varepsilon^3)$
with the exact third-order limit
$$
\lim_{\varepsilon\to0^+}\frac{\mathrm{dampedBezoutLimit}(\varepsilon)}{\varepsilon^3}
=4\log2\sum_{j=0}^\infty\frac{\mu(2j+1)}{\varphi(2j+1)^2},
$$
so the lag-one autocorrelation and the dissipation-minus-variance gap obey the exact third-order laws
$$
\lim_{\varepsilon\to0^+}\frac{A_\varepsilon(1)+\varepsilon^2}{\varepsilon^3}
=-\lim_{\varepsilon\to0^+}\frac{R(\varepsilon)-V(\varepsilon)-\varepsilon^2}{\varepsilon^3}
=2\gamma+4\log2\sum_{j=0}^\infty\frac{\mu(2j+1)}{\varphi(2j+1)^2}
$$
(`tendsto_dampedBezoutLimit_div_cube`, `tendsto_dampedAutocorrelation_one_third_order`,
`tendsto_dampedDissipationRate_sub_variance_third_order`), and consecutive values of
$\tau_\varepsilon$ are anti-correlated at the scale of the squared mean
because one of two consecutive integers is even. The actual receiver row
inherits the rate: $\widetilde{\mathcal D}_Q((B+1)Q;c_Q)/Q\to-(B+1)R(\varepsilon)$,
since the Ramanujan truncation error is negligible against the window and the
divisor moments keep the boundary values bounded. The spectral geometry of the
two rows is opposite: the Möbius variance **escapes**, every fixed modulus
losing its mass $\varphi(e)Y_N(e)^2\to0$ while the total stays above $1/288$,
so the floor is carried by moduli comparable with the horizon; the damped
spectrum is **tight** uniformly in the horizon, the moduli above $E$ carrying at
most $\zeta(1+\varepsilon)^2((1+2\varepsilon)/2\varepsilon)E^{-2\varepsilon}$. The pronic
observable alone commutes with the damping limit, $P(N;\mu)\to1/2$ and
$\lim_\varepsilon\lim_NP(N;c_\varepsilon)=1/2$, because the pronic weight sees only
bounded arguments; the horizon effect lives in the trans-horizon bulk. The
Selberg tangent row $\ell_N(d)=\mu(d)\log(N/d)$, whose response is Selberg's
truncated von Mangoldt function, has period covariances
$\mathrm{Cov}_N(h;\ell_N)\to\mathfrak S(h)-1$ at every lag $h\ge1$, the
Hardy–Littlewood singular series, with divergent variance: unlike the Möbius
row it sees prime-pair correlations on the period torus, and its horizon limit
agrees at every lag with the Haar limit $\lim_\varepsilon A_\varepsilon(h)/\varepsilon^2$
of the damped row.

**Slope reversal and the crossover.** At a prime horizon the damped step is, with
$r=p^{-\varepsilon}$, $\mathcal E_p(M)-\mathcal E_{p-1}(M)=r^2B-2r\sum_{d<p}c_\varepsilon(d)\lfloor B/d\rfloor=rB\lambda_\varepsilon(p)+O(rp)$.
Completing the floor sum to horizon $B$ turns it into the damped divisor sum
$\sum_{j\le B}\tau_\varepsilon(j)\ge\kappa_\varepsilon B$ (mean $\rho_\varepsilon>0$), the
omitted divisors $d\ge p$ cost at most $B(1+\varepsilon)\varepsilon^{-1}p^{-\varepsilon}$,
and the injection $r^2B$ is $o(rB)$: for every fixed $\varepsilon>0$ every large
prime horizon strictly **lowers** the energy at every trans-horizon prefix
$M\ge p$, the opposite of the Möbius law. The slope moves by at most
$\varepsilon\log p\,(2p-1)$, so injection persists near $\varepsilon=0$ on bounded
horizon ranges, and the dissipation threshold $P(\varepsilon)$ diverges as
$\varepsilon\to0$. Its location is exact: Abel summation against $\mathfrak m(t)$
gives $\lvert\rho_\varepsilon-H_\varepsilon(n)\rvert\le2\sup_{t\ge n}\lvert\mathfrak m(t)\rvert\,(n+1)^{-\varepsilon}$
uniformly in the damping, so the sign of $\lambda_\varepsilon(p)$ is the sign of
$p^{-\varepsilon}-2\rho_\varepsilon$ past one absolute $P_0$, and with
$\Lambda(\varepsilon)=\log(1/(2\rho_\varepsilon))/\varepsilon$,
$$
\log p\le(1-\delta)\Lambda(\varepsilon)\ \Rightarrow\ \lambda_\varepsilon(p)>0,\qquad
\log p\ge(1+\delta)\Lambda(\varepsilon)\ \Rightarrow\ \lambda_\varepsilon(p)<0,\qquad
\varepsilon\Lambda(\varepsilon)-\log\tfrac1{2\varepsilon}\to0 .
$$
To second order $\rho_\varepsilon=\varepsilon-\gamma\varepsilon^2+o(\varepsilon^2)$, so
$\Lambda(\varepsilon)=\log(1/(2\varepsilon))/\varepsilon+\gamma+o(1)$ and the crossover prime
is $e^{\gamma+o(1)}(2\varepsilon)^{-1/\varepsilon}$; at each individual prime $p$ with $H_\varepsilon(p-1)>0$
the prime-local scale $\Lambda_p(\varepsilon)=-\log(2H_\varepsilon(p-1))/\varepsilon$ decides the sign of
$\lambda_\varepsilon(p)$ with zero gap (`dampedPrimeSlope_local_sign_trichotomy`), and since the Möbius
harmonic sums decay like $(\log t)^{-3}$ the Abel error is $O(\varepsilon^3p^{-\varepsilon})$ against a
quadratic gap of order $\varepsilon^3\rho_\varepsilon$ once $\log p$ leaves
$\Lambda(\varepsilon)\pm(96C+1)\varepsilon^2$ (`dampedPrimeSlope_quadratic_crossover`). This shrinks the
universal transition window from $\pm\varepsilon$ to $O(\varepsilon^2)$ (and hence to $\pm\delta\varepsilon$
for every $\delta>0$, `dampedPrimeSlope_sublinear_additive_crossover`), resolving the sign of
$\lambda_\varepsilon(p)$ inside the additive window $\lvert\log p-\Lambda(\varepsilon)\rvert<\varepsilon$.
The receivers at fixed small damping live beyond this injection-to-dissipation crossover.

**The threshold at one half.** In the Jordan spectrum (§2.2), $J_2(q)\le q^2$ and damped mode
masses have size $q^{-2\varepsilon}$:
for $\varepsilon>1/2$ the primitive energy is bounded uniformly in the horizon and
converges to $\tfrac1{12}\sum_{q\ge2}J_2(q)w_\varepsilon(q)^2$; for $0<\varepsilon\le1/2$
the prime modes alone carry $J_2(p)w_\varepsilon(p)^2\ge\tfrac34\mathbb E[\tau_\varepsilon]^2/p$,
whose sum diverges, so it tends to infinity, with the exact order
$\mathcal E_{\mathrm{prim}}(N;c_\varepsilon)\asymp N^{1-2\varepsilon}$ for $0<\varepsilon<1/2$
(every mode at most $\zeta(1+\varepsilon)^2q^{-2\varepsilon}$; the odd squarefree top
octave carries at least $N^{1-2\varepsilon}/3456$): the discrepancy grows like a walk
of $N^{1-2\varepsilon}$ independent unit steps. For the Möbius row the growth is exactly
linear, $12\,\mathcal E_{\mathrm{prim}}(N;\mu)/N\to c\approx0.3311$ with an explicit Euler-product
series for $c$ (Bézout–Valuation Incidence §3.10).
Below half damping, receiver estimates must use pronic weights rather than complete-period averages.

### 3.9 Observation states, phases, and recovery

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

### 3.10 Valuation clocks and prime chains

The clock reconstructs $\Lambda$ as in §2.5 and gives the exact three-zone
filter law for a prime-power mode $q=p^b$ sampled at lag $p^a$: multiplier $1$
and coefficient $\varphi(p^b)$ in the passband $b\le a$, multiplier $-1/(p-1)$
and coefficient $-p^a$ at the frontier $b=a+1$, zero in the stopband
$b\ge a+2$. The difference of two consecutive clock scales is a wavelet
supported on exactly the two shells $\{a,a+1\}$, with values $p/(p-1)$ and
$-1/(p-1)$, and an unnormalized dipole $+p^a,-p^a$ of zero net charge. Coprime
moduli tensor both multipliers and coefficients, so a transverse lag equal to
the transverse clock detects the two adjacent valuations of every nonzero
integer. A squarefree-supported weight has vanishing Selberg coordinates at
every non-squarefree mode, and at a squarefree mode the lag weight depends on
the lag only through $\gcd(e,h)$, so for Möbius, damped and receiver rows the
translation statistics see only $\operatorname{rad}(h)$: the clock of the lag is
invisible. On the prime-chain side, stepping from a chain base $b$ coprime to
$p$ to $pb$ renormalizes the horizon,
$s_H(c,pb)-s_H(c,b)=s_{H/p}\bigl(c(p\,\cdot),b\bigr)$.
For $p>H$ the right side is empty, so every $p$-chain variance of a truncated
sieve profile vanishes identically; for squarefree-supported weights every
excited node collapses to the first excited level, and excited-to-excited jumps
vanish at every horizon.

### 3.11 Fermi observability: schedules and their conditioning

The two selected schedules, odd boundaries and boundaries divisible by four,
recover the whole sieve sequence exactly iff the admitted coefficients on
multiples of four vanish; on that class the energies satisfy $Q\le P\le4Q$ with
sharp constants and exact nonnegative slack, and the actual cofactor row of the
PM route lies in it. For arbitrary coefficients the selected trace is still
injective, through an explicit even-chain coefficient transport whose inverse
costs at most $3/2$ in coefficient energy, sharply.

**Which schedules see the sieve.** Along a dyadic ray the slots give the
relations $z_0=0$, $z_k=2z_{k-1}$ and $z_L=0$, a chain pinned at both ends. For
$N\ge1$ a dyadic schedule determines every horizon-$N$ row iff it misses at most
one slot: with one missing slot the chain is pinned from both sides; with two
missing slots $a<b$ the profile $z_k=2^k$ on $[a,b)$, realized by a row supported
on powers of two, is invisible. The selected and the full schedules are
injective, odd boundaries alone are not once $N\ge2$, and an injective schedule
needs $\lfloor\log_2N\rfloor+1$ slots: the observation depth equals the dyadic
depth of the horizon.

**The price of a gap is its position.** The horizon forces dyadic saturation
after $L=\lfloor\log_2N\rfloor+1$ levels, so no horizon-independent inverse
exists, and the sharp selected law is
$$
\frac{K_N}{(\log_2N)^2}\longrightarrow\frac4{\pi^2},\qquad
\frac{K_N^+}{(\log_2N)^2}\longrightarrow\frac4{\pi^2},
$$
from a mixed-boundary sine inequality along dyadic rays and nonnegative cosine
packets attaining it; at finite horizon $K_3^+<K_3$, because the shift
$c\mapsto c+t(e_2-e_1)$ changes both energies by the same quadratic and the
signed centering strictly improves the ratio. The mechanism is the boundary
structure of a ray: the selected schedule leaves the step from the odd base to
its first double unobserved, so each ray is free at its bottom and pinned only
by saturation at its top, a mixed chain with ground mode $\cos((k+\tfrac12)\pi/(2L+3))$
and constant $(2L/\pi)^2$. The cells $n\equiv2\pmod4$ observe exactly that step,
so under the all-boundary trace each ray is pinned at both ends, a Dirichlet
chain with ground mode $\sin((k+1)\pi/(L+2))$ and constant $(L/\pi)^2$; the
saturation tail costs as much as a three-step ramp to zero (a terminal value
$y$ continued by halving costs exactly $y^2/3$), and the low-level weight
deficit is absorbed by splitting the first steps into half-steps. Hence
$$
\frac{K^{\mathrm{all}}_N}{(\log_2N)^2}\longrightarrow\frac1{\pi^2},\qquad
\frac{K_N}{K^{\mathrm{all}}_N}\longrightarrow4,
$$
for real and for nonnegative coefficients, with explicit two-sided bounds
($(1-4/(L+2))(L+2)^2/\pi^2\le K^{\mathrm{all}}_N$ for $N\ge4$), attained by the
rising sine packets $y_k=\sin((k+1)\pi/(L+2))$, whose synthesizing coefficients
are nonnegative by the reflection $2\sin((k+1)\theta)\ge\sin(k\theta)$. A one-gap
trace at level $g$ splits each ray into two mixed chains, bottom and top, each of
constant $\lambda_n=2-2\cos(\pi/(2n+1))$ with $1/\lambda_n\le((2n+1)^2+2)/\pi^2$,
and quarter-wave packets $\sin(j\theta)$, $(2n+1)\theta=\pi$, are their ground
modes with mass $(2n+1)/4$ and jump energy exactly $\lambda_n$ times the mass.
The two bounds squeeze the constant: if the gap sits at relative depth
$h/L\to\alpha$,
$$
\frac{K_{h+1}(N)}{(\log_2N)^2}\longrightarrow\frac{4\max(\alpha,1-\alpha)^2}{\pi^2}.
$$
One unobserved dyadic level costs the square of the longer of the two
half-observed chains it creates: nothing at half depth, where the constant is
the $1/\pi^2$ of the full trace, and a factor four at either edge, the selected
trace being the edge case $\alpha=0$.

**Multi-gap schedules, $p$-adic traces, and origin–bulk tightness.** Under a
two-gap schedule omitting levels $1\le g_1<g_2\le\lfloor\log_2N\rfloor$
($g_1=h_1+1$, $g_2=h_2+1$), each odd ray $b$ splits into the bottom pinned chain
$[0,h_1]$, the interior floating block $[h_1+1,h_2]$, and the top pinned chain
$[h_2+1,\lfloor\log_2N\rfloor+1]$ with the saturation ramp. The interval power
row `fermiIntervalKernelRow` has normalized ray value $1$ on $[g_1,g_2)$ and $0$
outside, with vanishing boundary jump at every level $k\notin\{g_1,g_2\}$
(`fermiBoundaryJump_fermiIntervalKernelRow_eq_zero_of_ne`). Conversely, any row
in the kernel of the two-gap schedule vanishes outside $[h_1+1,h_2]$ and is
constant on $[h_1+1,h_2]$ along every odd ray
(`twoGap_ray_profile_of_zero_jumps`), so the schedule is injective on both the
anchor-pinned subspace ($y_{h_2}(b)=0$) and the least-squares block-mean-zero
subspace ($\sum_{k=h_1+1}^{h_2}y_k(b)=0$)
(`twoGap_schedule_injective_on_anchored_rows`,
`twoGap_schedule_injective_on_meanZero_rows`). On the floating block the
variance around the block mean $\bar y$ is controlled by the interior jumps with
constant $\lambda_{h_2-h_1-1}$ (`floating_block_variance_sine_bound`), yielding
the three-chain ray inequality (`fermiRayTwoGapEnergy_ge`,
`fermiRaySieveEnergy_anchored_le_twoGap`). For any prime $p$, the $p$-adic Fermi
cell matrix $p\lfloor n/(pd)\rfloor-\lfloor n/d\rfloor$ has cell response
$p\sum_{k\le n/p}s_{N,c}(k)-\sum_{k\le n}s_{N,c}(k)$ and boundary jump
$p\mathbf 1_{p\mid n}s_{N,c}(n/p)-s_{N,c}(n)$, saturating at
$L_p=\lfloor\log_pN\rfloor$, and a $p$-adic schedule is injective iff it misses
at most one of the $L_p+2$ slots (`pAdicFermiScheduleInjective_iff`); for
general positive ray weights $w_j>0$, the weighted trace energy controls node
$k$ by the series resistance $\sum_{j\le k}w_j^{-1}$
(`sq_le_rayResistance_mul_weightedRayTraceEnergy`) and inherits the mixed-chain
sine constant above any weight floor (`weighted_mixed_chain_sine_bound`). Finally,
the cellular response satisfies the exact centered-prefix wavelet identity
$$
\mathrm{fermiCellResponse}_{N,c}(n)
=2A_{\mathrm{row}(c,N)}(\lfloor n/2\rfloor)-A_{\mathrm{row}(c,N)}(n)-(n\bmod2)\,m_c(N)
$$
(`fermiCellResponse_eq_weightCenteredPrefix_horizonRow`), so the bulk pronic norm
is bounded by $(1+\sqrt2)\,\|A_{\mathrm{row}(c,N)}\|_T+\lvert m_c(N)\rvert$
(`pronicNorm_fermiCellResponse_le`) and any subpower prefix bound
$\lvert A_{\mathrm{row}(c,N)}(k)\rvert\le Bk^\gamma$ ($0\le\gamma<1/2$) gives
both uniform bulk boundedness and uniform origin-tail tightness across all
horizons $N$ and cutoffs $T$ (`fermiBulk_and_originTail_tight_of_prefix_rpow`,
`fermiBulk_and_originTail_tight_dampedSign_of_partialSum_rpow`,
`fermiBulk_and_originTail_tight_moebius_of_half_zetaZeroAbscissa_lt`).

**Capacity.** On dyadic antichains (one index per odd part) with odd prime
factors in a set $\Pi$, a horizon-uniform $P\le CQ$ holds, also on nonnegative
packets, iff $\sum_{p\in\Pi}1/p<\infty$, with the explicit constant $8e^{6M}$
for reciprocal mass $M$; divergent capacity produces nonnegative packets with
$P\ge(L-1)/2$ and $0<Q<5/6$ for every $L\ge2$, built from disjoint prime banks
whose parity ratios $\prod(p-1)/(p+1)$ are small.

### 3.12 Off-line hyperbolic chain excess

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

### 3.13 The odd sector in quotient coordinates

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

**The pole reading is canonical, and the odd gap is exactly one square.** The odd polar ground
vectors at two different admissible shifts differ by an element of the signed radical, so every
pairing against them agrees: $\mathrm{sourcePair}(\Psi_a,q)=\mathrm{sourcePair}(\Psi_b,q)=\langle q,\tanh_L\rangle$
for every graph vector and every pair of nonzero shifts. The shift is therefore not a parameter of
the theory but a gauge, and the quantity it reads is one *shift-independent pole moment*. In that
reading the odd sector has an exact two-term decomposition: for every primitive — in particular
every odd — graph vector,
$$
\mathrm{sourceEnergy}(q)=\mathrm{weilForm}(q)+2\,\langle q,\tanh_L\rangle^2 .
$$
The odd Weil form is the source energy minus twice one squared pole moment, with no remainder and
no choice of shift; the odd primitive part — the vector with its pole moment subtracted — is
$\mathrm{sourcePair}$-orthogonal to every polar ground vector, at every shift. This is the quotient
coordinate the section's name promises: the whole polar risk of the odd sector is rank one, it is
computed by a single canonical functional, and the open question is a statement about
$\mathrm{sourceEnergy}$ on its kernel. It is the source-graph counterpart of the parity decoupling
of Arithmetic Positivity Theory, where odd compact tests carry the whole pole risk $S(g)^2/2$.

**Two unconditional tightenings on the lobes, and the cross-lobe sandwich.** First, a Rayleigh
excess: for a primitive resolvent eigenvector the modulus–primitive excess equals, exactly, four
times a cross-lobe combination of a resolvent pairing and the rank-one ground-vector products, and
the cross-lobe resolvent pairing is bounded below by $-\nu^2\mathrm{sourcePair}(q^+,q^-)>0$ at
positive eigenvalue. Second, a chiral drift inequality holding on *both* lobes of every odd graph
vector,
$$
\langle \mathrm{primeShift}\,q^+,q^+\rangle^2+\tfrac14\langle\mathrm{oddPrimeDrift}\,q,\lvert q\rvert\rangle^2
\ \le\ \langle\mathrm{primeDiagonal}\,q^+,q^+\rangle^2 ,
$$
because the odd prime-drift operator has vanishing diagonal on odd vectors. Beyond lobe-local
bounds, for every odd graph vector $p$ and every odd mass vector $z$, $\langle(p^+)_1,z\rangle=-\langle(p^-)_1,z\rangle=\tfrac12\langle p_1,z\rangle$ and $\langle\lvert p\rvert_1,z\rangle=0$ (`odd_lobe_inner_odd_mass`), so both individual lobes of an odd eigenvector satisfy the shift-independent odd-polar balance $(2\mu-1)\langle(q^\pm)_1,(\Psi_a)_1\rangle+\mu\langle(q^\pm)_1,\tanh_L\rangle=0$ (`odd_eigenvector_posGraph_and_negGraph_oddPolarVectorAt_pairing`), and the Weil bilinear form polarizes across the lobes as $\mathrm{weilBilin}(p^+,p^-)=\mathrm{sourcePair}(p^+,p^-)+\tfrac12\langle\lvert p\rvert_1,\mathbf 1\rangle^2+\tfrac12\langle p_1,\tanh_L\rangle^2$ with $\mathrm{weilForm}(\lvert p\rvert)-\mathrm{weilForm}(p)=4\,\mathrm{weilBilin}(p^+,p^-)$ (`odd_weilForm_and_weilBilin_lobe_polarization`). For every odd eigenvector $q=\mathrm{rieszLift}(w)$ ($0<\mu$, $\mathrm{reflectMass}(w)=-w$), the four-term positive-lobe excess equals $((1-2\mu)/(2\mu))\|q_1\|^2$ identically, and the cross-lobe pairings obey the unconditional two-sided sandwich
$$
0\ \le\ 4\mu^2\langle\mathrm{primeShift}(q^+)_1,(q^-)_1\rangle
\ \le\ -4\mu^2\mathrm{sourcePair}(q^+,q^-)
\ \le\ 4\langle\mathrm{resolvent}(q^+)_1,(q^-)_1\rangle
\ \le\ (1-\mu)\|q_1\|^2
$$
with strict positivity for $w\ne0$, reducing RH to $\mathrm{weilBilin}(q^+,q^-)\le\tfrac12\langle q_1,\tanh_L\rangle^2$ on odd eigenvectors (`odd_eigenvector_four_term_excess_and_cross_lobe_sandwich`, `odd_eigenvector_cross_lobe_strict_bounds_of_ne_zero`, `riemannHypothesis_of_odd_eigenvector_cross_lobe_weilBilin_le_tanhL_sq` in [OddSectorCrossLobeEstimatesAndNineModuliCollarBridge](OddSectorCrossLobeEstimatesAndNineModuliCollarBridge.lean)).

**Fermi curvature against the Bézout gradient.** On the second trans-horizon octave the two
observers are reciprocal rather than independent: for $m\in[N,2N)$ the second difference of the
Fermi cell response at $2m+1$ plus the forward Bézout gradient of the sieve response at the same
point equals exactly $-2\mu(m+1)$, the Möbius value of the half-scale parent in the *first*
octave. Cauchy–Schwarz turns the identity into a coercivity statement with no cancellation
hypothesis: the combined second-octave Fermi curvature energy and Bézout gradient energy is at
least twice the first-octave odd squarefree count, hence at least a positive density of the
window. The two trans-horizon observers cannot both be small, and the quantity that forbids it is
an octave below.

### 3.14 Collar transport

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
collar mixed density to a one-point diagonal potential; for any continuous
midpoint-symmetric kernel $K(t-x)=K(x)$ (including the polar weight
$P_{\log d}(x)$, the atom-minus-pole excess $A_d(x)$, and the total
archimedean-plus-atom excess $T_d(x)$), the weighted collar-mixed integral over
$(0,t)$ equals twice the one-point diagonal integral against
$m_a(x)K^{\mathrm{diag}}_{a,t}(x)w(x)^2$
(`integral_symmetric_mul_oddProfileCollarMixed_eq_two_mul_diag`). Since
$m_a(x)K^{\mathrm{diag}}_{a,\log d}(x)>0$ on $(0,\log d)$, the one-point
diagonal potential matches the anti-diagonal classification term by term: its
atom-minus-pole excess is positive on all of $(0,\log d)$ iff
$d\in\{2,3,4,5,7\}$ (`atomAntiDiagonal_oddProfile_diag_pos_on_Ioo_iff`), its
total excess is positive on all of $(0,\log d)$ iff
$d\in\{2,3,4,5,7,8,9,11,13\}$ (the nine moduli,
`totalAntiDiagonal_oddProfile_diag_pos_on_Ioo_iff`), and for $d\ge23$ the paid
middle interval $[L_d,\log d-L_d]\cap(0,\log d)$ has nonpositive excess while
the inner axis ends $(0,\min(\ell_d,\log d))\cup(\log d-\min(\ell_d,\log d),\log d)$
remain strictly positive (`totalAntiDiagonal_oddProfile_nonpos_on_paid_middle_of_twenty_three_le`).
A Stieltjes integration by parts turns $\sum_{\log d<a}\Lambda(d)d^{-1/2}(\cdots)$ into a pole
term plus a Chebyshev discrepancy transport; and the mean-value comparison
$m_a(x)\le(2M/\sinh(a/2))\sinh(x/2)$ on $[0,R]$, with the explicit unconditional slope bound
$M(a,R)=2\pi(e^{2(a+R)}+2)\Theta(0)$ (`riemannKernelReal_shift_diff_le_thetaDerivBound`,
`unconditional_oddProfile_le_sinh`), bounds the cosh mass by a sinh potential,
so that cosh mass and all prime collars are absorbed with net coefficient
$\theta\le1$ whenever the literal cosh/sinh ratio is at most $\theta$. That
ratio condition is the hinge, and §3.15 shows it fails.

### 3.15 The absorption boundary and primitive horizons

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
$[\Theta\psi_a^2\cosh(x/2)-\theta m_a\sinh(x/2)]_+$, the unconditional upper
bound $\mathrm{oddPolarDefect}(a,\theta,w)\le\max(R_{\mathrm{uncond}}(a,R)-\theta,0)\,\mathrm{oddSinhPotential}(a,w)$
on compact even profiles supported in $(-R,R)$ with exact vanishing when
$R_{\mathrm{uncond}}(a,R)\le\theta$ (`unconditional_oddPolarDefect_le_oddSinhPotential`,
`unconditional_oddPolarDefect_eq_zero_of_le`), and the complete compensated
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

### 3.16 The parity pair: sign-blind data and the receiver

**The universal law and the threshold.** Along $k\mapsto k+1$ the centred prefix splits exactly,
$A_c(n)=\sum_{d\le n}c(d)(\lfloor n/d\rfloor-n/d)-n\sum_{d>n}c(d)/d$. On $\mathcal C(K,\varepsilon)$
this gives $\lvert A_c(n)\rvert\le KC_\varepsilon n^{1-\varepsilon}$ with
$C_\varepsilon=1+1/(1-\varepsilon)+1/\varepsilon$, hence $E_T\le(KC_\varepsilon)^2\sum_{n\le T}n^{-2\varepsilon}$
on the whole class: above half damping one constant pays every weight, signs are irrelevant. Below
it, everything lives in the trans-horizon tail $n\sum_{d>n}c(d)/d$ and in the head drift, both of
order $n^{1-\varepsilon}$.

**Positive weights cannot cancel.** For $c\ge0$ both terms of the split are nonpositive and
$A_c(n)\le-n\sum_{n<d\le2n}c(d)/d$. The receiver of a nonnegative weight is exactly the
$\ell^2(2^{-k})$ norm of its dyadic masses: $c$ is paid iff $\sum_kM_k^2/2^k<\infty$, with explicit
two-sided constants (`bounded_weightPronicEnergy_iff_summable_dyadicMass`). For $c\asymp d^{-\varepsilon}$,
$M_k\asymp2^{k(1-\varepsilon)}$: half damping is the square-root law of the dyadic masses. For
nonnegative weights the horizon limit commutes with the receiver (`rows_uniformly_bounded_iff`).

**Bounded partial sums pay.** A weight $c(d)=s(d)d^{-\varepsilon}$ whose sign pattern $s$ has bounded
partial sums is paid at every $\varepsilon>0$: split the moduli at $D=\lfloor n^{1/(2+\varepsilon)}\rfloor$,
bound the short ones absolutely and count the long ones along the cofactor step $k\mapsto k+1$, which
gives $\lvert A_c(n)\rvert\le6Bn^{1/(2+\varepsilon)}$.

**The pairs and the barrier.** Twists that preserve the amplitudes turn these two laws into pairs.
At half damping, $\mu(d)d^{-1/2}$ (paid, through the corpus Mellin bound and $\zeta(1+it)\ne0$) and its
twin $c'_{1/2}$ (drift on the squarefree integers of $(n,2n]$) form a pair
(`parityPair_at_half_damping`); the twin diverges at every $\varepsilon\le1/2$, so for the Möbius
weight a parity pair at damping $\varepsilon$ exists exactly when its receiver is bounded there. At
every damping $\varepsilon\le1/2$ and for every real non-principal character $\chi$, the weight
$\chi(d)d^{-\varepsilon}$ and the positive twin $(\lvert L\rvert/O)\mathbf 1_{(d,q)=1}d^{-\varepsilon}$
form a pair, unconditionally; the twist is the parity of the inert prime factors (`char_parityPair`).
The completion $\hat\chi$ ($\pm1$-valued, completely multiplicative) pairs with the full-density
smooth power $\kappa d^{-\varepsilon}$ (`charCompletion_parityPair`), and $\lambda(d)d^{-1/2}$ pairs with
$\kappa d^{-1/2}$ (`liouville_parityPair_at_half_damping`). The positive members attain the maximal
growth $\sum n^{-2\varepsilon}$ of the class, so the pairs are extremal. Hence the **parity barrier**:
on $\mathcal C(K,\varepsilon)$ boundedness of the receiver is a function of the Ramanujan amplitudes
if and only if $\varepsilon>1/2$ (`receiverBounded_amplitudeInvariant_iff`, `parity_barrier`). This is
the parity barrier of sieve theory as a sharp theorem in the receiver's coordinates. The same holds
at every horizon: the rows $\chi(d)d^{-\varepsilon}\mathbf 1_{d\le N}$ and their twins have equal
Selberg coordinates up to sign and equal two-point translated moments, uniformly bounded against
divergent pronic energy (`char_parityRows`).

**Which additive data read the parity.** Translated moments of degree two see only $Y(q)^2$. Cubic
moments read the sign at every odd modulus through $\zeta_q\zeta_q\zeta_q^{q-2}=1$ and pin squarefree
rows up to the even flip (`scaledSelbergRow_eq_or_evenFlip_of_translatedMoment_three`). The even flip
is invisible to translated moments of every degree and shift on squarefree rows
(`translatedMoment_evenFlipRow`), and on the receiver it is the Fermi transform of the even part. It
can break the receiver: $F=(\delta_1-2^{1-\varepsilon}\delta_2)\star\mathbf 1_{\mathrm{odd\,sqf}}d^{-\varepsilon}$ is
paid and $F^\flat$ is not (`fermi_evenFlip_parityPair`), and their rows agree in every translated
moment of every degree at every horizon (`fermi_parityRows`). So for squarefree rows no additive
moment of any degree decides the receiver.

**First-order data at prime powers and the logarithmic hierarchy.** Summation by parts along
$n\mapsto n+1$ and harmonic numbers along $k\mapsto dk$ give
$\sum_n(\lfloor n/d\rfloor-n/d)/(n(n+1))=-\log d/d$, hence the first pronic moment is the von
Mangoldt pairing, $M(c)=-\sum_e\Lambda(e)W_c(e)$ (`hasSum_firstPronicMoment`). It orders every pair
with a positive member, strictly iff $W_c<0$ at some prime power. The weight
$2\rho_\varepsilon\delta_1-\mu(d)d^{-\varepsilon}$, which has the Möbius receiver, agrees with the twin
at every prime power and in the first moment (`firstMomentBlind_parityPair`); its parity lives on
the moduli $pq$ and is read by $M(c\log)=-\sum_e\Lambda_2(e)W_c(e)$
(`logMoment_separates_firstMomentBlind`). In general $M(c\log^k)=-\sum_e\Lambda_{k+1}(e)W_c(e)$ reads
the moduli with at most $k+1$ prime factors, a positive pair is separated at the order of the least
$\omega(e)$ with $W_c(e)<0$ (`exists_logMoment_separating`), and since the logarithmic moments are the
Taylor coefficients at $s=1$ of $\sum_dc(d)d^{-s}$ they determine the weight up to the unit mass, which
the receiver does not see: every parity pair is separated by some logarithmic moment
(`exists_logMoment_ne`). The first moment is a derivation, $M(a\star b)=m_bM(a)+m_aM(b)$; for the damped
Möbius weight $M(c_\varepsilon)=\rho_\varepsilon\sum_n\Lambda(n)n^{-1-\varepsilon}\to1$ as
$\varepsilon\to0^+$, and the twin and the first-moment-blind weight have $-M(c_\varepsilon)$.

**Receiver-preserving symmetries.** The pronic weight contracts the dilation $n\mapsto\lfloor n/p\rfloor$
by exactly $p^{-1/2}$, and a local factor acts as $A_{c\star(\delta_1-a\delta_p)}(n)=A_c(n)-aA_c(\lfloor n/p\rfloor)+am\{n/p\}$:
for $\lvert a\rvert<\sqrt p$ the receiver class is invariant, sharply
(`bounded_weightPronicEnergy_localFactor_iff`). Zeros of Euler factors never hurt; poles hurt exactly
when they lie on or to the right of $\operatorname{Re}s=1/2$. Globally,
$A_{g\star c}(n)=\sum_{q\le n}g(q)A_c(\lfloor n/q\rfloor)+m_cA_g(n)$ and
$\lVert A_{g\star c}\rVert\le G\lVert A_c\rVert+(\sqrt2+1)G\lvert m_c\rvert$, $G=\sum_q\lvert g(q)\rvert q^{-1/2}$:
kernels of the critical Wiener algebra preserve paid receivers (`receiverBounded_dirichletConv`). So
the Möbius and Liouville receivers are bounded at the same dampings, through the square dilation
$k\mapsto j^2k$ (`receiverBounded_moebius_iff_liouville`); the receiver of a multiplicative weight
with $\lvert f\rvert\le1$ is decided at the primes, with the trichotomy $\chi$-pretentious paid at every
damping, $\mu$-pretentious paid wherever $\mu$ is, nonnegative $1$-pretentious unpaid for
$\varepsilon\le1/2$ (`receiver_trichotomy`); flips on a prime set with
$\sum_{p\in P}p^{-1/2-\varepsilon}<\infty$ never change the class (`receiverBounded_of_sparse_flip`), so a
paid $\pm1$ pattern flips a prime set of divergent critical-line mass. The twist kernels of all the
pairs lie just outside the algebra exactly when $\varepsilon\le1/2$.

**Higher prime powers at half damping.** Let $f'$ be multiplicative with $\lvert f'\rvert\le1$ and $f$
its completely multiplicative companion ($f(p)=f'(p)$). The kernel $g=f'\star\mu f$ has $g(p)=0$ and
$\lvert g(p^k)\rvert\le2$, and its inverse $h$ has local sums
$\sum_k\lvert h(p^k)\rvert p^{-k}\le(1-r_p)^{-1}$, $r_p=\sum_k\lvert g(p^k)\rvert p^{-k}\le3p^{-2}$ for odd $p$
(`sum_range_abs_mul_pow_le_of_inv`). At $p=2$, $r_2<1$ unless every two-adic step is extremal,
which happens exactly for the tails $f'(2^k)=-1$ and $f'(2^k)=(-1)^{k+1}$ (`twoAdicStep_extremal_iff`).
Off these two tails $h$ is critical Wiener and $f'(d)d^{-1/2}$ is paid iff $f(d)d^{-1/2}$ is
(`receiverBounded_half_iff_companion`). On them the two-adic local factor vanishes on $\operatorname{Re}w=1$
and can repair the boundary: at $t_0=2\pi m/\log2$ the weight $f'(n)=(-1)^{[2\mid n]}f_{t_0}(n)$,
$f_{t_0}(p)=\cos(t_0\log p)$, has series $(1-2^{1-w})F_{t_0}(w)$ and is always paid
(`receiverBounded_twoAdicRepair`), while its companion is paid iff $\zeta(\tfrac12+it_0)=0$
(`receiverBounded_twoAdicCompanion_iff`).

**The pole law.** The Mellin pairing is multiplicative under convolution,
$\Phi_{k\star q}=K(\sigma)\Phi_q+m_q\Phi_k$, because the cells of a dilation telescope. A paid receiver
has $\lvert\Phi(\sigma)\rvert=O((\sigma-1/2)^{-1/2})$, while a positive drift $\kappa n^{1-\varepsilon}$
forces $\Phi_q(1-\varepsilon+\delta)\asymp-\delta^{-1}$. Hence for every kernel of the critical Wiener
algebra, $k\star q$ with $q$ a positive drift weight is unpaid unless $K(1-\varepsilon)=0$
(`not_receiverBounded_dirichletConv_of_drift_critical`); this is the divergence tool for
sign-changing weights. For finite kernels over any positive weight pretending to one ($d^{-\varepsilon}$,
$\mu^2$, the odd squarefree weight, the coprime weights) the paid perturbations form one universal
hyperplane, $K(1-\varepsilon)=0$ (`receiverBounded_dirichletConv_primesOne_iff`). A multiplicative
$1$-pretentious weight with finite local factors is paid iff some $L_p=0$
(`receiverBounded_iff_exists_poleLocalFactor_eq_zero`), never when $\lvert f\rvert\le1$, since then
$L_p\ge1$: higher prime powers enter only through the local factor at the pole. The even flip shifts
the pole value by the even part of the kernel, $K^\flat(1-\varepsilon)=K(1-\varepsilon)+(1-2^\varepsilon)K_e(1-\varepsilon)$
(`evenFlip_exactLoss`), so at most one member of a flipped pair is paid when $K_e(1-\varepsilon)\ne0$.
A pole of order two needs a zero of order two: under a logarithmic drift a paid convolution has
vanishing pole value and pole slope
(`poleValue_eq_zero_and_poleSlope_eq_zero_of_receiverBounded`). At all orders $m\ge0$, the
logarithmic pole moments $M_m(k;1-\varepsilon)=\sum_{j\le J}k(j)(\log j)^mj^{-(1-\varepsilon)}$ obey the
exact binomial Leibniz identity under Dirichlet convolution
(`poleLogMoment_dirichletConv`), so pole-vanishing order is strictly additive under convolution
(`poleLogMoment_dirichletConv_eq_zero_of_lt`, `poleLogMoment_dirichletConv_add`,
`poleLogMoment_dirichletConv_ne_zero`), and the $r$-th iterated Fermi kernel
$(\delta_1-2^{1-\varepsilon}\delta_2)^{\star r}$ has exact pole vanishing order $r$ with leading moment
$r!(-\log 2)^r\ne0$ (`poleLogMoment_iteratedFermiKernel`,
`poleLogMoment_iteratedFermiKernel_ne_zero`). The receiver reads the order of the
pole, and the separating observables on the kernel side are the Taylor coefficients of $K$ at
$s=1-\varepsilon$, the counterpart of the logarithmic hierarchy.

**The damping unit and closure of the blind class.** Sign-blind payment holds exactly on
$(\tfrac12,\infty)$; its derived set $[\tfrac12,\infty)$ includes the endpoint where sign-blindness fails.
Post-processing, pairing and arbitrarily large families of amplitude-derived readings preserve
blindness: $\tfrac12$ is a floor for this whole class of methods.

For Möbius, the infimum of the derived admission set is $\Theta-\tfrac12$
(`receiverDampingRate_eq_zetaZeroAbscissa_sub_half`); RH is accumulation at $0$
(`riemannHypothesis_iff_cofinal_budget`, `widthDictionary_tfae`). A single admitted damping only
translates zeros along $\rho,\rho-\varepsilon,\rho-2\varepsilon,\dots$; width information comes from
accumulation, as in the aperture coordinate.

The pole law explains positive twins: prime flips introduce the pole at $1-\varepsilon$.
For Möbius, poles of $1/\zeta(s+\varepsilon)$ right of $\Re s=1/2$ are precisely zeros with
$\Re\rho>1/2+\varepsilon$. A receiver bound must exclude them using signed information.

### 3.17 Mellin continuation and the horizon-limit boundary

The receiver is also an analytic regularity condition. Write
$C(s)=\sum_d c(d)d^{-s}$, $m=C(1)$ and
$\Phi(s)=\sum_n A_c(n)(n^{-s}-(n+1)^{-s})$.
A paid receiver makes $\Phi$ holomorphic on $\Re s>1/2$: Cauchy–Schwarz against
$1/(n(n+1))$ controls the Mellin cells locally uniformly. Where the original series
converges inside the strip, $\Phi(s)=\zeta(s)(C(s)-m)$.
Thus the **product** continues holomorphically; division by $\zeta$ gives a meromorphic
continuation of $C-m$, not an unconditional zero-free half-plane
([APaidReceiverContinuesTheDirichletSeriesAcrossItsAbscissa](APaidReceiverContinuesTheDirichletSeriesAcrossItsAbscissa.lean)).

At a real convergence boundary $a\in(1/2,1)$, $\zeta(a)\ne0$, so the continued
$C$ is analytic there. Its approach to its limiting value is Lipschitz, and a
nonzero two-sided power law $|C(a+u)-C(a)|\asymp u^\alpha$ has positive integer
exponent. Under the explicit logarithmic prime-mean hypothesis
`Σ_p f(p)p^(−w) = ν log(1/(w−1)) + O(1)`, a real completely multiplicative
pattern with `|f(p)| ≤ 1` can be paid at `0 < ε < 1/2` only if `ν ∈ {0, −1}`.
For a sign pattern with the corresponding logarithmic flipped-prime density this
means density `1/2` or `1`. These are necessary conditions, not sufficient ones;
a mere informal density heuristic is not the hypothesis of the theorem.

At half damping the real boundary lies on the edge of the holomorphy domain,
so the replacement is an energy identity. For `|c(d)| ≤ K d^(−1/2)` and
$1/2<\sigma<1$, with $G(s)=\zeta(s)(C(s)-m)$,
$$
\sum_n A_c(n)^2\bigl(n^{-2\sigma}-(n+1)^{-2\sigma}\bigr)
=\frac{\sigma}{\pi}\int_{\mathbb R}
\left|\frac{G(\sigma+it)}{\sigma+it}\right|^2dt.
$$
Uniform line-energy bounds across $1/2<\sigma<3/4$ are two-sided equivalent to payment, with explicit
bound $\int_{\mathbb R}\lvert G(\sigma+it)/(\sigma+it)\rvert^2dt\le 4\pi E$ across $1/2<\sigma<1$
([TheHalfDampedReceiverIsTheBoundaryEnergyOfItsDirichletSeries](TheHalfDampedReceiverIsTheBoundaryEnergyOfItsDirichletSeries.lean),
`lineEnergy_le_four_pi_mul_of_weightPronicEnergy_le`,
`receiverBounded_iff_exists_lineEnergy_le`).
Pointwise control at the real boundary is weaker than this whole-line condition.

**The general pole law.** For every weight of the half-damped class the Mellin pairing of the
centred prefix with the cells $n^{-\sigma}-(n+1)^{-\sigma}$ is $\zeta(\sigma)(C(\sigma)-m)$ on
$1/2<\sigma<1$: one modulus pairs to $\zeta(\sigma)(d^{-\sigma}-1/d)$, because along $N=dM$ the two
growing terms cancel exactly and leave the partial-sum asymptotic of $\zeta$ inside the strip. Since
$\lvert\zeta(\sigma)\rvert\ge1$ on $[1/2,1)$, Cauchy–Schwarz gives, for a paid weight,
$\lvert C(\sigma)-m\rvert\le2\sqrt E\,(2\sigma-1)^{-1/2}$
(`abs_dirichletSeries_sub_mean_le_of_energy`). The receiver at half damping reads the size of the
weight's own Dirichlet series as $\sigma\downarrow1/2$, with no factorisation; the pole law of the
critical Wiener algebra (§3.16) is the special case $c=k\star q$.

The pole law also has a constructive converse. For the smooth power
$q(d)=d^{-\varepsilon}$, `0 < ε < 1/2`, and every critical Wiener kernel $k$,
$$
\operatorname{ReceiverBounded}(k*q)
\iff \sum_j k(j)j^{-(1-\varepsilon)}=0.
$$
Each pole-free dilation has energy $O(1/j)$; Minkowski sums them with the
critical norm $\sum_j|k(j)|j^{-1/2}$
([CriticalWienerPerturbationsOfTheSmoothPowerAreDecidedAtThePole](CriticalWienerPerturbationsOfTheSmoothPowerAreDecidedAtThePole.lean)).
This extends the finite-kernel hyperplane to the whole algebra in the strict
sub-half range. General necessity already works for kernels absolutely
summable at the abscissa, a weaker requirement than critical Wiener summability
([APaidReceiverBoundsTheDirichletSeriesUpToItsAbscissa](APaidReceiverBoundsTheDirichletSeriesUpToItsAbscissa.lean)).

**The half-damping logarithmic threshold.** At $\varepsilon=1/2$, vanishing
$K(1/2)$ alone is insufficient on the full critical Wiener algebra. The exact sufficient
logarithmic weight is
$\sum_j|k(j)|j^{-1/2}\sqrt{1+\log j}<\infty$: on this class,
$\operatorname{ReceiverBounded}(k*d^{-1/2})\iff K(1/2)=0$
(`receiverBounded_dirichletConv_unit_half_iff`). The extra factor comes from the harmonic
sum below each dilation scale, whose pole-free energy is $O((1+\log j)/j)$.
A lacunary kernel supported at $J_r=2^{4^{r+1}}$, with coefficient
$2^{-(r+1)}\sqrt{J_r}$ and a compensating coefficient $-1$ at $1$, lies in every class with
$(1+\log j)^\alpha$, $0\le\alpha<1/2$, and has $K(1/2)=0$, but is not paid
(`halfDamped_hyperplaneLaw_logarithmic_threshold`). This proves sharpness among these logarithmic
power weights, not necessity of that absolute weight for each individual paid kernel.

The obstruction is a stronger real-axis necessary law: under absolute Dirichlet convergence
for every real exponent above $1/2$, a paid source satisfies
$\sqrt u\,|C(1/2+u)-m|\to0$ as $u\downarrow0$
(`tendsto_sqrt_mul_abs_dirichletSeries_sub_mean`). It follows by splitting the Mellin pairing
into a finite head and a tail of arbitrarily small energy. It is necessary, not a replacement
for the complete vertical-line boundary-energy criterion
([TheHalfDampedHyperplaneLawHasAnExactLogarithmicThreshold](TheHalfDampedHyperplaneLawHasAnExactLogarithmicThreshold.lean)).

**The partial pole sums across $(0,1)$.** The exact criterion behind the logarithmic threshold is a
signed energy that holds across the entire strip $0<\varepsilon<1$. With
$S_{k,\varepsilon}(n)=\sum_{j\le n}k(j)j^{-(1-\varepsilon)}$ the partial sums at the pole abscissa,
$Z_\varepsilon=\Re\zeta(1-\varepsilon)/(1-\varepsilon)<0$, and
$L_{T,\varepsilon}(k)=\sum_{n\le T}(n^{1-\varepsilon}S_{k,\varepsilon}(n))^2/(n(n+1))$, any kernel $k$ (with
no critical Wiener hypothesis) satisfies
$\lvert\sqrt{E_T(k\star q_\varepsilon)}-\lvert Z_\varepsilon\rvert\sqrt{L_{T,\varepsilon}(k)}\rvert\le\lVert\sum_{j\le n}k(j)R_{\varepsilon,j}(n)\rVert_T+\lvert m_{q_\varepsilon}\rvert\lVert A_k\rVert_T$
(`abs_sqrt_weightPronicEnergy_dirichletConv_unit_subHalf_sub_le_of_bounds`). Each dilated remainder has
pronic norm $O(j^{-1/2})$ (`pronicNorm_subHalfDilationRemainder_le`), so for every $k\in\mathrm{CriticalWiener}$
and $0<\varepsilon<1$, $\lvert\sqrt{E_T(k\star q_\varepsilon)}-\lvert Z_\varepsilon\rvert\sqrt{L_{T,\varepsilon}(k)}\rvert\le B$
(`abs_sqrt_weightPronicEnergy_dirichletConv_unit_subHalf_sub_le`) and $k\star d^{-\varepsilon}$ is paid iff
$\sum_n(n^{1-\varepsilon}S_{k,\varepsilon}(n))^2/(n(n+1))<\infty$
(`receiverBounded_dirichletConv_unit_subHalf_iff_summable_partialPoleSum`). At $\varepsilon=1/2$ this is
$L_T(k)=\sum_{n\le T}S_k(n)^2/(n+1)$ with $2\lvert Z\rvert=\lvert Z_{1/2}\rvert$
(`abs_sqrt_weightPronicEnergy_dirichletConv_unit_half_sub_le`,
`receiverBounded_dirichletConv_unit_half_iff_summable_partialPoleSum`). Beyond both the critical Wiener
class and abscissa-summable kernels, the Möbius-inverted kernel
$k_{s,\varepsilon}(j)=(s\star\mu)(j)j^{-\varepsilon}$ satisfies $k_{s,\varepsilon}\star d^{-\varepsilon}=s(d)d^{-\varepsilon}$
(`dirichletConv_moebiusInvertedKernel_unit`), so any bounded or subpower partial-sum target $s$ gives a
paid individual kernel (`receiverBounded_dirichletConv_moebiusInvertedKernel_of_partialSum_rpow`); in
particular $c_\varepsilon(j)=\mu(j)j^{-\varepsilon}$ is not absolutely summable at $1-\varepsilon$
(`not_summable_abs_pmPowerDamped_abscissa`) and lies outside $\mathrm{CriticalWiener}$ for
$\varepsilon\le1/2$ (`not_criticalWiener_pmPowerDamped`), yet $c_\varepsilon\star d^{-\varepsilon}=\delta_1$ has
zero receiver energy (`receiverBounded_dirichletConv_pmPowerDamped_unit`)
([SubHalfDampingPartialPoleSumsAndLogarithmicMomentIndexLaws](SubHalfDampingPartialPoleSumsAndLogarithmicMomentIndexLaws.lean)).

Finally, centre every dyadic row at **its own** finite mean. Uniformly paid rows
always pay their limit when the mean converges. The converse holds throughout
$\mathcal C(K,\varepsilon)$ exactly from $\varepsilon=1/2$ onwards. Below half
damping, lacunary zero-mean dipoles give a paid signed weight whose rows have
unbounded energy: a horizon can cut a cancelling dipole in half and retain a
large mean drift. This is the sharp classification, not an unresolved exchange
of limits
([TheHorizonLimitCommutesWithTheReceiverExactlyFromHalfDamping](TheHorizonLimitCommutesWithTheReceiverExactlyFromHalfDamping.lean)).
On the convolution class the dipole obstruction never occurs: for $0<\varepsilon<1/2$ and every
critical Wiener kernel, the rows of $k\star d^{-\varepsilon}$ are uniformly paid iff
$k\star d^{-\varepsilon}$ is paid iff $K(1-\varepsilon)=0$
(`rows_bounded_iff_dirichletConv_unit_poleValue_eq_zero`). A horizon can only cut such a weight
into finitely many rows of pole-free dilations, each of energy $O(1/j)$, and one row of the smooth
power, all tied to the pole by the single number $K(1-\varepsilon)$.

For a general paid weight $c$ with harmonic tail $\tau_N=\sum_{d>N}c(d)/d$, on $1\le n\le N$ the
row prefix is $A_{\mathrm{row}(c,N)}(n)=A_c(n)+\tau_N n$, and because the pronic mass of $n$ on
$[1,N]$ is pinched between $N/2$ and $N$, the sub-horizon row energies ($T\le N$) are uniformly
bounded iff $\sup_N N\tau_N^2<\infty$ (`subHorizon_horizonRowEnergy_bounded_iff`). Across all
cutoffs, uniformly paid horizon rows are closed under the critical Wiener monoid: because
$qm\le N\iff m\le\lfloor N/q\rfloor$, $\mathrm{row}(g\star c,N)=\sum_{q\le N}g(q)(\delta_q\star\mathrm{row}(c,\lfloor N/q\rfloor))$,
giving the exact prefix decomposition
$A_{\mathrm{row}(g\star c,N)}(n)=\sum_{q\le N}g(q)A_{\mathrm{row}(c,\lfloor N/q\rfloor)}(\lfloor n/q\rfloor)+\sum_{q\le N}g(q)m_c(\lfloor N/q\rfloor)(\lfloor n/q\rfloor-n/q)$
and the norm bound $\lVert A_{\mathrm{row}(g\star c,N)}\rVert_T\le G(B+\sqrt 2\sum_d\lvert c(d)/d\rvert)$
(`weightCenteredPrefix_horizonRow_dirichletConv`, `horizonRows_bounded_dirichletConv`).
([PrefixStabilityAndCriticalWienerClosureOfMoebiusRows](PrefixStabilityAndCriticalWienerClosureOfMoebiusRows.lean)).

### 3.18 Multiplicative phase diagrams: what the receiver reads in a sign pattern

Completely multiplicative weights $f(d)d^{-\varepsilon}$ with $\lvert f\rvert\le1$ test which
arithmetic data of a sign pattern decide the receiver. The tool throughout is the boundary-energy
identity of §3.17 together with Euler-product bounds for $C(s)=\sum f(d)d^{-s}$ beside the line
$\Re s=1-\varepsilon$.

**The constant-sign pattern.** For $z\in[-1,1]$ and $c_{z,\varepsilon}(d)=z^{\Omega(d)}d^{-\varepsilon}$
the whole $(z,\varepsilon)$ plane is decided: $c_{z,\varepsilon}$ is paid iff $\varepsilon>1/2$, or
$\varepsilon=1/2$ and $z<1/2$, or $z=0$, or $z=-1$ and $\mu(d)d^{-\varepsilon}$ is paid
(`receiverBounded_constantSign_damped_iff`). At half damping this is the **quarter law**
(`receiverBounded_constantSign_iff_full`). The Euler product gives
$\lvert F_z(w)\rvert\le e^{2S}\lvert\zeta(w)\rvert^z$, which near $w=1$ is $O(\lvert\Im w\rvert^{-z})$
and square integrable on the line exactly when $2z<1$; for $z>1/2$ a real-axis lower bound and at
$z=1/2$ the off-axis bound $\lvert F_{1/2}\rvert^2\gtrsim1/\lvert w-1\rvert$ make the line energy grow
like $\log(1/u)$; for $z<0$ the bound $1/\lvert\zeta\rvert\ll\lvert\Im w\rvert^{1/4}$ beside the line
pays. Read as a pattern flipping primes with density $\delta=(1-z)/2$, the threshold is $\delta=1/4$:
the receiver reads the order of the singularity at $s=1$, and the critical flipped density $1/4$ is
the order $1/2$.

**The integer-order obstruction.** Below half damping a paid receiver continues
$\zeta(s)(C(s)-m)$ holomorphically to $\Re s>1/2$, so $C$ is meromorphic at every point of the
abscissa line and behaves along rays like an integral power. A weight with logarithmic real-axis
prime mean $\nu$ is therefore unpaid unless $\nu\in\{0,-1\}$ (`not_receiverBounded_of_primeMean`),
which is why the constant-sign diagram has only the Liouville line below half damping. The same
holds height by height: $f(p)=a\cos(t_0\log p)$, $t_0\ne0$, has local prime mean $a/2$ at height
$t_0$, so $f(d)d^{-\varepsilon}$ is paid iff $a=0$ (`receiverBounded_oscPattern_damped_iff`). The
prime mean is quantized at every height. No mean has to be assumed: if $f(d)d^{-\varepsilon}$ is paid,
$0<\varepsilon<\tfrac12$, then at every height $\log\lvert F(1+u+it_0)\rvert=k\log(1/u)+O(1)$ with
$k\in\mathbb Z$ the order of $\zeta$ minus the order of $C\zeta$ at $1-\varepsilon+it_0$
(`exists_int_localExponent_of_receiverBounded_damped`). Off the real axis
$\lvert\cos x\rvert\le\tfrac34+\tfrac14\cos2x$ and $\zeta(1+2it_0)\ne0$ cap $\lvert k\rvert$ at $\tfrac34$, so $F$
stays bounded and bounded away from $0$ along every ray at $t_0\ne0$
(`exists_abs_log_norm_patternSeries_le_of_receiverBounded_damped`). A Dini box has exponent
$\tfrac12-o(1)$, so Dini patterns, and in particular all completely monotone amplitude defects, are
unpaid at every damping below one half (`not_receiverBounded_damped_of_diniBox`).

**Residue-class flips.** For $f_{q,S}$ flipping the primes in the classes $S\subseteq\mathbb Z/q$,
the flipped primes have exact logarithmic density $\rho=\#(S\cap(\mathbb Z/q)^\times)/\varphi(q)$
(Dirichlet's theorem in integrated form). At half damping every flip with $\rho\le1/4$ is unpaid,
the boundary included (`not_receiverBounded_residueFlip_half_of_le`): the complex class density and
the Euler lower bound $\log\lvert F\rvert\ge\log\lvert\zeta\rvert-2\sum_{f(p)=-1}\Re p^{-w}-O(1)$ give
$\lvert C\rvert^2\gtrsim1/\lvert s-1/2\rvert$. Below half damping only $\rho\in\{1/2,1\}$ can be paid
(`not_receiverBounded_residueFlip`). For $S$ closed under inversion on the units, orthogonality
gives the Euler bound $\lvert F\rvert\le e^B\lvert\zeta\rvert^{1-2\rho}\prod_{\chi\ne1}\lvert L(\cdot,\chi)\rvert^{e_\chi}$
with real exponents, and the quarter law is exact: paid at half damping iff $\rho>1/4$
(`receiverBounded_residueFlip_half_iff`). Symmetry is not needed. For an arbitrary $S$ the character
coefficients $s_\chi=\sum_{u\in S}\chi(u^{-1})$ are complex, and the prime sum of $\chi$ is replaced by
the Euler logarithm $\ell_\chi$ of $L(\cdot,\chi)$, which is bounded on boxes for $\chi\ne1$ and grows
like $9\log\log\lvert\Im w\rvert$ right of the one-line (`RHTower.exists_norm_eulerLog_le_large`).
Complex exponents therefore cost only a power of $\log\lvert\Im w\rvert$, the same line-energy argument
applies, and for every $q\ge1$ and every $S\subseteq\mathbb Z/q$ the flip is paid at half damping iff
$\varphi(q)<4\#(S\cap(\mathbb Z/q)^\times)$ (`receiverBounded_residueFlip_half_iff_general`): the
proportion $1/4$ is the exact threshold on the whole residue family. For a subgroup $H$ of index $k\ge2$, flipping the primes
outside $H$ gives $\rho=1-1/k$ and $\zeta$-exponent $2/k-1\in[-1,0]$, so only $1/\lvert\zeta\rvert$ and
$\lvert L\rvert$ from above are needed — no zero-free region for $L$; for $k\ge3$ the receiver of
$f_H(d)d^{-\varepsilon}$ is paid exactly for $\varepsilon\ge1/2$ (`receiverBounded_subgroupFlip_iff`).

**Oscillating prime patterns, and the limit of prime data.** For $f_{a,t_0}(p)=a\cos(t_0\log p)$,
$a\in[-1,1]$, the half-damped weight is paid iff $(t_0=0\wedge a<1/2)$ or
$(t_0\ne0\wedge(a<1\vee\zeta(\tfrac12+it_0)=0))$ (`receiverBounded_oscWeight_phase_diagram_iff`): at
$a=1$, $t_0\ne0$, a nonvanishing $\zeta(\tfrac12+it_0)$ creates an unpaid
$\lvert s-(\tfrac12+it_0)\rvert^{-1}$ singularity in $\lvert C\rvert^2$, and a critical zero cancels it.
For $t_0\ne0$ the real-axis prime sums are bounded, so the prime mean is $0$ for every amplitude
and the prime signs do not depend on $a>0$. Choosing $\zeta(\tfrac12+it_0)\ne0$, the amplitudes
$1/2$ and $1$ give a paid and an unpaid weight with the same prime signs and the same prime mean
(`exists_paid_unpaid_with_same_prime_signs_and_mean`).

**The phase law, multi-frequency patterns, and prime-varying amplitudes.** Shifting the phase,
$f(p)=a\cos(t_0\log p+\varphi)$ with $\lvert a\rvert\le1$ and $t_0\ne0$, the half-damped weight is paid
iff $a\cos\varphi<1$ or $\zeta(\tfrac12+it_0)=0$ (`receiverBounded_phaseWeight_iff`). Writing
$f(p)p^{-w}=bp^{-(w-it_0)}+\bar bp^{-(w+it_0)}$ with $b=\tfrac a2e^{i\varphi}$, $\log\lvert F\rvert$ is
$\Re(b\,\ell(w-it_0)+\bar b\,\ell(w+it_0))$ up to a bounded term, $\ell$ the Euler logarithm of $\zeta$.
Its real part $\log\lvert\zeta\rvert$ carries $a\cos\varphi$; its imaginary part $\arg\zeta$ carries
$a\sin\varphi$, and the argument is bounded at the pole (`RHTower.exists_abs_im_zetaEulerLog_le`) and
$O(\log\log t)$ at height $t$. So the line integrand has the singularity
$\lvert t-t_0\rvert^{-(a\cos\varphi)^+}$, integrable iff $a\cos\varphi<1$: the receiver reads only the
real part $\Re(ae^{i\varphi})$ of the complex amplitude, and the imaginary part couples to $\arg\zeta$,
which creates no singularity. For a finite superposition
$f(p)=\sum_{k\in K}a_k\cos(t_k\log p+\varphi_k)$ with pairwise distinct positive frequencies $t_k>0$,
the prime-additive Euler product factorization (`norm_patternSeries_le_prod_of_prime_sum`) multiplies
the single-mode bounds, and separated height singularities collapse to a linear sum
$\prod_{k\in K}(\lvert y-t_k\rvert^{-b_k}+1)\le C(1+\sum_{k\in K}\lvert y-t_k\rvert^{-b_k})$
(`exists_prod_rpow_neg_add_one_le_sum`), which is integrable on the vertical line whenever $2b_k<1$ for
every $k\in K$ (`receiverBounded_pattern_half_of_sum_bounds`). Under the amplitude budget
$\sum_{k\in K}\lvert a_k\rvert\le1$, the half-damped weight is paid iff for every $k\in K$,
$a_k\cos\varphi_k<1$ or $\zeta(\tfrac12+it_k)=0$ (`receiverBounded_multiPhaseWeight_iff`); in
particular, sharing the unit budget across two or more active frequencies ($a_{k_1},a_{k_2}\ne0$) forces
$\lvert a_k\rvert<1$ at every mode and pays the half-damped receiver unconditionally
(`receiverBounded_multiPhaseWeight_of_two_active`). Below half damping ($0<\varepsilon<1/2$), payment
forces $a_k\cos\varphi_k=0$ at every mode (`cos_coeff_eq_zero_of_receiverBounded_multiPhase_damped`).
For any multiplicative $f'$ with $\lvert f'(n)\rvert\le1$ and completely multiplicative $f$ with
$\lvert f(p)\rvert\le1$ (with no unimodularity assumption), if
$\sum_p\lvert f'(p)-f(p)\rvert p^{-(1/2+\varepsilon)}<\infty$, the defect kernel $(f'\star\mu f)(d)d^{-\varepsilon}$
lies in the critical Wiener algebra (`criticalWiener_mul_patternMoebiusAF`), so both full-receiver
payment and uniform horizon-row payment are invariant under $\ell^1(p^{-(1/2+\varepsilon)})$ prime
perturbations (`receiverBounded_iff_of_summable_prime_diff`,
`horizonRows_bounded_of_summable_prime_diff`, `receiverBounded_primeVaryingMultiPhase_half_iff`).

**Divergent critical-line mass: the Dini law.** Completely monotone amplitude defects
$f(p)=(1-c\,g(p))\cos(t_0\log p)$, $g(p)=\sum_kw_kp^{-s_k}$ ($w_k\ge0$, $W=\sum_kw_k<\infty$,
$0<s_k\le\tfrac12$, $c\ge0$, $cW\le2$) are decided exactly. The Euler product sees $\zeta$ at $w\pm it_0$
and at the shifted points $w+s_k\pm it_0$, so with $\rho=(\Re w-1)+\lvert\Im w-t_0\rvert$ one has
$\lvert F(w)\rvert^2\asymp e^{-c\Lambda(\rho)}/\rho$, where $\Lambda(\rho)=\sum_kw_k\log(1/(s_k+\rho))$ is the
defect profile (`exists_abs_log_norm_defectSeries_sub_profile_le`). For $t_0>0$ the half-damped weight
is paid iff $\int_0^1e^{-c\Lambda(\rho)}\,d\rho/\rho<\infty$ or $\zeta(\tfrac12+it_0)=0$
(`receiverBounded_defectWeight_iff`). For the harmonic defect $w_k=1/((k+1)(k+2))$, $s_k=e^{-(k+1)}$
the profile is $\log\log(1/\rho)+O(1)$, and for $0\le c\le2$ the weight is paid iff $c>1$ or
$\zeta(\tfrac12+it_0)=0$ (`receiverBounded_harmonicDefect_iff`), while the critical-line mass
$\sum_p\lvert f(p)-\cos(t_0\log p)\rvert/p$ diverges at every $c>0$
(`not_summable_criticalLineMass_harmonic`). The harmonic defect is $1/\log\log p+O((\log\log p)^{-2})$
(`abs_cmDefect_harmonic_sub_le`) and $\sum_p1/(p\,\ell(p)^2)<\infty$ for $\ell=\max(1,\log\log)$
(`summable_inv_mul_logLogFloor_sq`), so the natural amplitude $a_p=1-c/\ell(p)$ has the same
threshold: $(1-c/\ell(p))\cos(t_0\log p)$ is paid iff $c>1$ or $\zeta(\tfrac12+it_0)=0$
(`receiverBounded_logLogPattern_iff`), with divergent critical-line mass at every $c>0$
(`not_summable_criticalLineMass_logLog`). At height zero the boundary amplitude is $\tfrac12$ and the
same law holds: $(1-c\,g(p))/2$ is paid iff $\int_0^1e^{-c\Lambda(\rho)}\,d\rho/\rho<\infty$
(`receiverBounded_halfDefectWeight_iff`; $\zeta(\tfrac12)\ne0$ leaves no zero alternative), with
threshold $c=1$ for the harmonic and log-log defects (`receiverBounded_halfHarmonicDefect_iff`,
`receiverBounded_halfLogLogPattern_iff`) and divergent mass $\sum_p\lvert f(p)-\tfrac12\rvert/p$
(`not_summable_halfHarmonicMass`). Monotone defects are completely monotone up to summable mass: a
step $1_{p<R}$ and $p^{-s}$, $s=\min(\tfrac12,1/\log R)$, differ by
$\sum_p\lvert1_{p<R}-p^{-s}\rvert/p\le12$ (`sum_abs_step_sub_rpow_le`). Hence, for $d$ antitone along the
primes with $0\le d\le2$ and $d\to0$, and $t_0>0$, the pattern $(1-d(p))\cos(t_0\log p)$ is paid iff
$\int_0^1\exp(-\sum_pd(p)p^{-1-\rho})\,d\rho/\rho<\infty$ or $\zeta(\tfrac12+it_0)=0$
(`receiverBounded_monotoneDefectPattern_iff`). Summable-perturbation invariance stops at convergent mass;
the phase boundary lies inside the divergent regime and is the Dini integral of the profile.

**Reading.** For any completely multiplicative $f$ with $\lvert f(p)\rvert\le1$, the Euler product
pinches $\log\lvert F(w)\rvert$ within $S=\sum_p p^{-2}$ of the real part of the prime Dirichlet series
$\Re\ell_f(w)=\sum_p f(p)\Re(p^{-w})$ (`abs_log_norm_patternSeries_sub_re_primeDirichletSeries_le`),
which gives both the universal half-damped lower-bound obstruction at any height with
$\zeta(\tfrac12+it_0)\ne0$ (`not_receiverBounded_pattern_half_of_primeDirichletSeries_re_ge`) and
height-by-height quantization of local logarithmic prime means below half damping
(`int_localPrimeMean_of_receiverBounded_damped`). Neither the density of flipped primes nor the
real-axis prime mean decides the receiver of a multiplicative weight; the size of its Dirichlet
series beside the line $\Re s=1-\varepsilon$, at every height, does. For the Möbius weight the series is
$1/\zeta(s+\varepsilon)$, and its size beside the line is exactly what is unknown.

### 3.19 The receiver as an instrument for the zero divisor

**The oscillating smooth power.** For $c_{\varepsilon,t}(d)=d^{-\varepsilon}\cos(t\log d)=\Re(d^{\rho-1})$,
$\rho=1-\varepsilon+it$, $0<\varepsilon\le1/2$, the hyperbola method gives
$A(n)=\Re((\zeta(\rho)/\rho)n^\rho)+O(n^{(1-\varepsilon)/2})$, so the probe is paid iff
$\zeta(1-\varepsilon+it)=0$ (`receiverBounded_oscillatingSmoothPower_iff`), and RH says that no probe
with $\varepsilon<1/2$ is paid (`riemannHypothesis_iff_forall_not_receiverBounded_oscillatingSmoothPower`).
For $t\ne0$ the real-axis series $\Re\zeta((\sigma+\varepsilon)-it)$ is regular and Lipschitz at
$\sigma=1-\varepsilon$ whether the probe is paid or not: the oscillation moves the pole to
$1-\varepsilon\pm it$, so real-axis tests are blind to it. For every critical Wiener kernel $k$,
$k\star c_{\varepsilon,t}$ is paid iff $\sum_jk(j)j^{-\rho}=0$ or $\zeta(\rho)=0$
(`receiverBounded_dirichletConv_oscillatingSmoothPower_iff`).

**Orders of vanishing.** Differentiating the floor-sum remainder in $\rho$ — holomorphic, with
Cauchy estimates below the exponent $1/2$ — gives: $d^{-\varepsilon}\cos(t\log d)\log d$ is paid iff
$\zeta(\rho)=\zeta'(\rho)=0$ (`receiverBounded_logOscillatingSmoothPower_iff`); all zeros in
$\tfrac12\le\Re s<1$ are simple iff no such weight is paid
(`forall_simple_zero_iff_forall_not_receiverBounded`); and $d^{-\varepsilon}\cos(t\log d)(\log d)^k$ is
paid iff $\zeta^{(i)}(\rho)=0$ for every $i\le k$ (`receiverBounded_logPowerCosine_iff_all`), with
global order-$\le k$ criteria on the strip and on the critical line
(`forall_strip_zero_order_le_iff`, `forall_critical_zero_order_le_iff`). The receiver reads the zero
divisor of $\zeta$, multiplicities included, on the oscillating spectrum.

**Calibration.** Below half damping $E_T/T^{1-2\varepsilon}$ follows an explicit oscillating profile
of amplitude $\lvert\zeta(\rho)/\rho\rvert^2$, so $E_T\asymp\lvert\zeta(\rho)\rvert^2T^{1-2\varepsilon}$ for
$t\ne0$. At half damping $E_T/\log T\to\lvert\zeta(\tfrac12+it)\rvert^2/(2\lvert\tfrac12+it\rvert^2)$
(`tendsto_probeEnergy_half_div_log`, `norm_sq_riemannZeta_half_eq_limit`): finite divisor-sum
energies evaluate $\lvert\zeta\rvert$ on the critical line. On finite combinations of half-damped
probes the receiver is asymptotically the diagonal form with weight
$\lvert\zeta(\tfrac12+it)\rvert^2/(2\lvert\tfrac12+it\rvert^2)$
(`tendsto_halfProbeCombination_energy_div_log`): distinct frequencies are orthogonal for the receiver.

Probe evaluation does not bound the actual Möbius receiver with series $1/\zeta(s+\varepsilon)$.

### 3.20 The actual source at small damping

**Möbius and Liouville.** The all-damping hyperbola split gives
$\lvert A_\varepsilon(n)\rvert\le3D^{1-\varepsilon}+(13/\varepsilon)LnD^{-\varepsilon}$, and with
Vinogradov–Korobov the all-damping prefix bound
$\lvert A_\varepsilon(n)\rvert\le(K/\varepsilon)n^{1-\varepsilon}e^{-\sqrt{\log n}/40}$. From signed
logarithmic data $\lvert\sum_{e\le x}s(e)\log e\rvert\le M_{\log}x$ ($x\ge D\ge 1$), Abel summation
against $1/\log(\max(d,D+1))$ gains $(\log(D+1))^{-1}$ and gives the quantitative prefix bound
$\lvert A_{s,\varepsilon}(n)\rvert\le 6D^{1-\varepsilon}+(26/(\varepsilon\log(D+1)))M_{\log}nD^{-\varepsilon}$
with exact short-modulus loss $6D^{1-\varepsilon}$
(`abs_weightCenteredPrefix_dampedSign_le_of_logWeight_linear_pos`,
`abs_weightCenteredPrefix_pmPowerDamped_le_of_logWeight_linear_pos`); since
$-\mu(n)\log n=(\mu\star\Lambda)(n)$ (`neg_logWeight_moebiusReal_eq_dirichletConv`), a single-exponent
power saving $\lvert\sum_{e\le N}(\mu\star\Lambda)(e)\rvert\le C(N+1)^\beta$ ($\beta<1$) pays both the
Möbius and Liouville receivers at every fixed $\varepsilon>\beta/2$
(`receiverBounded_moebius_and_liouville_of_vonMangoldtConv_partialSum_rpow`). Möbius and
Liouville have the same positive admission set and width accumulation threshold
$\Theta-\tfrac12$; and RH is admission at every positive damping, for either weight
(`riemannHypothesis_iff_forall_pos_receiverBounded_moebius`,
`riemannHypothesis_iff_forall_pos_receiverBounded_liouville`,
`sInf_derivedSet_liouville_dampings_eq_zetaZeroAbscissa_sub_half`). Across $0<\varepsilon\le1/2$
the hyperbola bound controls $E_T(\varepsilon)$, $E_T^{\mathrm{int}}(\varepsilon)$ and the compensated interior martingale
bracket uniformly on the Vinogradov–Korobov band $\varepsilon\ge\tfrac12-\kappa\sigma(T)/(480\log T)$
above any $\varepsilon_0>0$ while the parity twin grows at least as $c_{\varepsilon_0}(\log(T+1)-\log100)$,
and at every fixed $\varepsilon\in(0,1/2)$ bounds $E_T^{\mathrm{int}}(\varepsilon)\le C_\varepsilon T^{1-2\varepsilon}\exp(-\kappa\sigma(T)/270)=o_\varepsilon(E_{\mathrm{prim}}(T))$
(`complete_signed_receiver_equivalence_and_all_damping_vk_laws`). The shrinking band admits no
fixed $\varepsilon<1/2$ at all horizons.

**Horizon rows of Möbius and Liouville.** The dipole obstruction of §3.17 is excluded on the
sub-horizon range $T\le N$ across the entire zero-width admission interval $\varepsilon>\Theta-1/2$:
the harmonic tail $\tau_N(\varepsilon)=\sum_{d>N}\mu(d)d^{-1-\varepsilon}$ is evaluated at
$1+\varepsilon>1$, so Littlewood's bound $\lvert M(x)\rvert\ll_\delta x^{\Theta+\delta}$ and Abel
summation give $\tau_N(\varepsilon)=O(N^{\Theta-1-\varepsilon+\delta})=o(N^{-1/2})$ and uniform
sub-horizon row payment (`subHorizon_horizonRowEnergy_moebius_bounded_of_zetaZeroAbscissa_sub_half_lt`).
Across all cutoffs $T$ and horizons $N$, truncating a sign pattern at $N$ freezes its partial sum at
$S(\min(x,N))$, which is prefix-stable under linear and subpower bounds; hence every horizon row of
$s(d)d^{-\varepsilon}$ satisfies the exact same all-damping hyperbola bound
$3D^{1-\varepsilon}+(13/\varepsilon)LnD^{-\varepsilon}$ as the full weight
(`abs_weightCenteredPrefix_horizonRow_dampedSign_le_of_linear_pos`). This gives uniform full-horizon
row payment for $\mu(d)d^{-\varepsilon}$ and $\lambda(d)d^{-\varepsilon}$ for every
$\varepsilon>\Theta/2$ (`horizonRows_bounded_moebius_of_half_zetaZeroAbscissa_lt`,
`horizonRows_bounded_liouville_of_half_zetaZeroAbscissa_lt`), uniform row payment on the
Vinogradov–Korobov zero-free band above any $\varepsilon_0>0$
(`exists_horizonRow_receiver_le_on_zeroFreeBand_of_pos`,
`exists_liouville_horizonRow_receiver_le_on_zeroFreeBand_of_pos`), and equivalence of uniform row
payment for Möbius and Liouville at every $\varepsilon>0$ (`horizonRows_bounded_moebius_iff_liouville`).

**The bilinear counterterm.** Grouping the triple sum by the cofactor $m=bk$ cancels half of the
principal counterterm $2\sum_{n\le N}\mu(n)w(n)$ against the sub-horizon slice and reduces
$\sum_{N<n\le N^2}\mu(n)w(n)$ to $-\sum_{a\le N}\mu(a)\sum_{N<m\le N^2/a}s_{N,\mu}(m)w(am)$. At a
trans-horizon semiprime $pq>N$ the low-product bilinear sum overcounts $\mu(pq)=1$ by $2$, which the
high-product remainder must cancel. Stepping $N\mapsto N+1$ couples $c(N+1)$ linearly to the
inherited history with zero quadratic diagonal, by pronic coprimality. The eventual all-prefix
defect sign coexists with linear growth of the reserve, $M\mathcal R_N(\mu)\ge M/576$, and of the
diagonal, $\mathcal D_N(N;\mu)\ge N/576-1$
(`eventually_all_prefix_renormalized_nonpos_with_unbounded_reserve`); and first-octave defect
nonpositivity holds for every $\{-1,0,1\}$-valued sequence, $\mu^2$ and $1$ included
(`firstOctaveDefectFunctional_nonpos_of_sq_eq_abs`), a sign-blind fact that cannot bound a signed
receiver.

**Oscillating-probe source estimates.** The probe laws of §3.19 can be read from the source side,
without evaluating $\zeta$. Every oscillating prefix splits into the sawtooth sum
$S_{\varepsilon,t}(n)=\sum_{d\le n}c_{\varepsilon,t}(d)(\lfloor n/d\rfloor-n/d)$ and the tail drift
$T_{\varepsilon,t}(n)=-n\sum_{d>n}c_{\varepsilon,t}(d)/d$, and the sawtooth splits again at $\sqrt n$. The
short moduli $d\le\sqrt n$ cost at most $(1+1/(1-\varepsilon))(\sqrt n)^{1-\varepsilon}$ and have bounded
pronic norm for every $0<\varepsilon<1$ and every height. Admission is therefore boundedness of the
long sawtooth plus the tail
(`receiverBounded_oscillatingSmoothPower_iff_bdd_pronicNorm_longSawtooth_add_tail`).

At $t=0$ both pieces are nonpositive and cannot cancel. The dyadic tail block alone gives
$A_{\varepsilon,0}(n)\le-2^{-(1+\varepsilon)}n^{1-\varepsilon}$, a source-side proof of non-admission
for $0<\varepsilon\le\tfrac12$ that does not use $\zeta(1-\varepsilon)\ne0$
(`not_receiverBounded_oscillatingSmoothPower_zero_from_source`). At $t\ne0$ the tail is
$\Re(n^\rho/(\rho-1))+O(n^{-\varepsilon})$, with energy of exact order $T^{1-2\varepsilon}$ whatever
$\zeta(\rho)$ is, and the long sawtooth is
$\Re((\zeta(\rho)/\rho-1/(\rho-1))n^\rho)+O((\sqrt n)^{1-\varepsilon})$. Admission is therefore a
cancellation of the long sawtooth against the tail, and it happens exactly when $\zeta(\rho)=0$.

In the pronic inner product this becomes an **anti-alignment gap**. A strict Cauchy–Schwarz
anti-alignment, even along a subsequence, excludes the cancellation
(`not_bdd_longSawtooth_add_tail_of_frequently_pronicInner_le`). The quadratic gap
$-2\langle S^{\mathrm{long}},T\rangle_T\le\theta(\lVert S^{\mathrm{long}}\rVert_T^2+\lVert T\rVert_T^2)$,
$\theta<1$, is equivalent to non-admission, and RH is the existence of such a gap for every
$0<\varepsilon<\tfrac12$ and $t\ne0$
(`riemannHypothesis_iff_forall_ne_zero_exists_longSawtooth_tail_antiAlignment_gap`). The explicit
coefficient $\theta_{\mathrm{long}}(\varepsilon,t)\le1$ is strictly below one exactly when the two
pieces differ in amplitude or decorrelate in phase, and this is proved on the Vinogradov–Korobov
collar and on bounded-height boxes (`longSawtoothTailGapTheta_lt_one_vk_and_box`). Tail growth
alone cannot supply the gap: at a paid probe the norm ratio and both anti-alignment ratios tend to
one (`tendsto_longSawtooth_tail_antiAlignment_one_of_receiverBounded`).

Across the polynomial gap $T^{1-2\varepsilon}$ there is no intermediate regime. A uniform prefix
bound $\lvert A_{\varepsilon,t}(n)\rvert\le K(\sqrt n)^{1-\varepsilon}$ and subpower energy
$o(T^{1-2\varepsilon})$ are each equivalent to admission. Explicit lower bounds
$E\ge\lambda T^{1-2\varepsilon}$ hold on every zero-free box and on the Vinogradov–Korobov collar. A
three-term planted Euler kernel shows that such collars near $\varepsilon=0$, and finite sets of
admitted parameters, do not exclude every $0<\varepsilon<\tfrac12$
(`plantedEulerKernel_collar_and_finiteness_obstruction`). The gap rewrites $\zeta(\rho)\ne0$ in source
coordinates, locating the needed cancellation: long moduli against the trans-horizon tail.

### 3.21 The signed interior energy and the selectivity of the laws

**The cofactor row keeps its mean.** A truncated Möbius row has finite-horizon mean $H_\mu(N)$,
which differs from the Haar mean by the harmonic tail $\tau_N$; in the centred prefix this is a
linear mean-drift dipole $n\tau_N$, the obstruction of §3.17. The actual cofactor row of the PM
route has no such dipole: $\sum_{d\le Q}K_Q(d)/d=1/\zeta(1+\varepsilon)$ holds identically, so
$H_{c_Q}(Q)=\rho_\varepsilon$ at every $Q\ge1$, and its centred prefix differs from
$A_\varepsilon(n)$ only by the cumulative Ramanujan truncation $\sum_{k\le n}(s_Q(k)-\tau_\varepsilon(k))$,
of size at most $\frac{1+\varepsilon}\varepsilon(\sum_{k\le n}\tau(k))Q^{-\varepsilon}\le\frac{1+\varepsilon}\varepsilon n^2Q^{-\varepsilon}$
(`sievePrefixDiscrepancy_pmCofactorRealWeight_sub_centeredPrefix_eq`,
`abs_sievePrefixDiscrepancy_pmCofactorRealWeight_sub_centeredPrefix_le`). In the pronic norm,
$$
\Bigl\lvert\sqrt{E^{\mathrm{cof}}_{Q,T}}-\sqrt{E^{\mathrm{int}}_T(\varepsilon)}\Bigr\rvert\le\tfrac12+\tfrac{1+\varepsilon}\varepsilon\,T\sqrt T\,Q^{-\varepsilon},
$$
(`abs_sqrt_sieveTruncatedPronicEnergy_pmCofactor_sub_sqrt_interiorPronic_le`). Along a growing
cutoff with $T\sqrt TQ(T)^{-\varepsilon}$ bounded, the two receivers are bounded together
(`growingCutoff_cofactorPronicEnergy_bounded_iff_interiorPronicEnergy_bounded`). The PM
receiver is the interior receiver of §1.2, with no dipole loss.

**The signed interior energy.** At fixed $\varepsilon\in(0,\tfrac12)$ the interior energy is the
diagonal of a $25$-entry signed pronic Gram matrix of the five pieces of Vaughan's identity, with
moving endpoints retained, plus a mixed remainder:
$E^{\mathrm{int}}_T(\varepsilon)=\sum_{i\le5}G_{ii}+R^{\mathrm{mix}}_T$ (the calibration is owned by
Bézout–Valuation Incidence). The diagonal entries are invariant under the sign flip of each
component, flipping component $k$ changes the energy by $4(\sum_jG_{kj}-G_{kk})$, and the squared
pointwise logarithmic majorant of the source is nonsummable at every $\varepsilon<\tfrac12$
(`complete_signed_interior_energy_and_vaughan_calibration`): no absolute bound on the pieces can
pay, and the content of the receiver is in the off-diagonal signs. Two exact devices control parts
of it. The interior gradient plus twice the local-impulse cross sum equals the active-deleted
diagonal plus twice a predecessor-peak martingale, up to bounded boundary terms; and along a
predecessor jump progression $n_k=d+1+(d+2)k$ at cutoff $N=(d+2)L$, delaying the conditional
jump-orbit mean until each modulus is born bounds the compensated progression by $\tfrac52(d+2)L$
(`abs_pmBezoutInteriorPrefix_birthDelayed_compensated_le_five_halves_mul`). These signed
formulations share the admission set, Vinogradov–Korobov band and subpower saving of §3.20
(`complete_signed_receiver_equivalence_and_all_damping_vk_laws`).

The uncentered Vaughan diagonal has order at least $T$: if
$\rho=\operatorname{Re}(1/\zeta(1+\varepsilon))$, then $G_{44}/T\to\rho^2$ and
$D_T\ge\rho^2T/4-1/4$. Hence $R_T^{\mathrm{mix}}/D_T\to-1$ already follows from the
absolutely convergent divisor mean, uniformly in both cutoffs
(`eventually_pmPronicVaughan_relative_cancellation`). The four pole cross entries sum to
$-\rho^2T+o(T)$, independently of the cutoffs, so they cannot all be sublinear
(`not_all_pmPronicVaughan_pole_cross_entries_sublinear`). These results concern the linear
pole contribution. The long-sawtooth/tail anti-alignment gap at order $T^{1-2\varepsilon}$
remains a separate quantitative obligation; the uncancelled Vaughan energy is exactly
$D_T+R_T^{\mathrm{mix}}=E_T^{\mathrm{int}}$.
At fixed cutoffs the full leading matrix is an explicit rank-one outer product with positive
diagonal density. Consequently bounded interior energy is equivalent to
$|1+R_T^{\mathrm{mix}}/D_T|=O(1/T)$
(`bounded_pmInteriorPronicEnergy_iff_reciprocal_vaughan_relative_error`), which makes the
remaining rate requirement precise. At square-root cutoffs the both-large row vanishes
exactly (`pmPronicVaughanGram_square_large_zero`); the other signed terms remain.
The complete leading matrix now also holds uniformly over both cutoffs. A single summable
divisor majorant controls all floor-mean errors, giving
$\sup_{U,V}|G_{ij}(T)/T-c_i(U,V)c_j(U,V)|\to0$. When both cutoffs diverge the limit is
$\rho^2vv^\mathsf{T}$, $v=(1,1,-1,0,-1)$, along any divergent horizon
(`tendsto_pmPronicVaughanGram_div_moving`); at $U=V=N,T=N^2$ the diagonal divided by the
horizon tends to $4\rho^2$. These BVI laws classify leading cancellation without a residual rate.
The small-small Vaughan specialization of the smooth-power expansion retains its floor
prefix, partial pole sum, and signed dilated remainder exactly
(`pmPronicVaughanPiece_smallSmall_expansion`). Summing the individual remainder norms costs
$W_\varepsilon(U)W_\varepsilon(V)$ with
$W_\varepsilon(N)=\sum_{a\le N}|\mu(a)|a^{-\varepsilon-1/2}$.
At $U=V=N$, the squared absolute budget has exact order $N^{2-4\varepsilon}$ below half
damping (`not_pmVaughan_absolute_square_budget_power_saving`). Individual remainder admission
therefore leaves a signed assembly problem; this budget lower bound is not a lower bound on
the signed remainder.

**Three selectivity classes.** The conservation and dissipation laws of the theory sort exactly by
the structure they use.

- *Class I, Beurling-universal.* Möbius inversion, transverse Gibbs log-submodularity, divided-log
  prime-power completion, the depth-zero Gamma gauge enclosure in $[1,2]$ and the three-sector
  large-label Buchstab decomposition hold in every abstract Beurling system
  (`selectivity_class_I_beurling_universal_laws`). They cannot tell $\zeta$ from a system with an
  off-line zero.
- *Class II, sign-blind.* Every complete-period quadratic form and lag covariance, the diagonal
  Vaughan entries and first-octave step-defect nonpositivity for every $\{-1,0,1\}$-valued sequence
  are invariant under the $(\mathbb Z/2\mathbb Z)^N$ sign flips of Selberg coordinates
  (`selectivity_class_II_signBlind_and_parityOrbit_laws`). They cannot see a parity pair.
- *Class III, Bézout-selective.* Laws driven by $\gcd(n,n+1)=1$ and $pa-qb=1$: zero-diagonal pronic
  Abel summation, $(2r-1)$-step Bézout shell midpoint annihilation, the conditional jump-orbit mean
  classification, least successor-seed resonance, and trans-horizon separation of parity-isometric
  rows (`selectivity_class_III_bezout_successor_selective_laws`).

Classes I and II fail the Beurling and parity tests. Class III retains successor structure,
a candidate source of new information; this classification is not necessary for every possible proof.

### 3.22 Bridges

Quarter-plane zeros are finite in height boxes, inherit the Ingham–Huxley, Huxley $12/5$ and
density-hypothesis exponents, and vanish above the Route-T zero-free width. Dyadic prime-shell
Chebyshev discrepancy inherits Vinogradov–Korobov. A fourth-root Brun–Titchmarsh level saves one
$\log q$ on prime-supported von Mangoldt weights; Gallagher converts multiplicative to linear
windows; Matomäki–Teräväinen coefficients have Rankin–Euler tails. The Nyquist log-cell identity
$\int_{\log n}^{\log(n+1)}e^{-t}(c+1-t-e^t)^2dt=c^2/(n(n+1))-2c(\cdots)+\text{const}$
links the Bi-Scale gauge to interior pronic Abel summation. The interior gradient plus impulse
cross sum tracks its logarithmic counterterm within a horizon-independent constant; a cofinal
strict contraction gives RH. Shifted ground states obey collar duality
$R_a(u)+D_a(u)=4\int_{x>0}u^2m_aC_a$ and a variation criterion for Markov-energy nonnegativity.
Every nonnegative combination of two shifts is a strict subsolution near zero and infinity.
The period laws (§§3.6, 3.8) match PM Haar moments; band averages (§3.7) match BVI's energy profile,
and the long-window law (§3.4) is BVI's window Poincaré law with a variance floor.

---

## 4. Foundational pillar theorems

All are unconditional; RH appears only as a conclusion or in an equivalence. The referenced
sections give the full statements, mechanisms and supporting declarations.

| Pillar | Statement and entry point |
|---|---|
| Global defect sign (§3.4) | Every prefix has nonpositive defect at all sufficiently large horizons, uniformly for $\varepsilon\in[0,1]$; Möbius horizons $N\le12$ are also certified. See `eventually_pmPowerDamped_renormalizedDefect_nonpos_uniform`; the cofactor analogue is `eventually_pmCofactor_renormalizedDefect_nonpos_all`. |
| Envelope boundary (§3.3) | The unit envelope ends at ratio five; failure occurs at $5N+5$, followed by rungs $2$ at ratio $11$, $3$ at $13$, and a $Q/\log Q$ ladder. Entries: `sieveRenormalizedPrefixDefect_moebiusReal_five_succ_nonpos`, `sieveSeq_moebiusReal_rung_two_family`, `sieveSeq_moebiusReal_rung_three_family`. |
| Period versus pronic laws (§§3.6, 3.8) | Period white noise and bounded damped variance coexist with divergent primitive energy for $\varepsilon\le1/2$: `tendsto_periodCorrelation_moebius`, `tendsto_sievePrimitiveEnergy_pmPowerDamped_atTop`. Response-level damping commutation (`tendsto_sieveTotalPronicEnergy_moebius`) is not primitive admission. |
| Positive-weight criterion (§3.16) | Payment is equivalent to $\sum_kM_k^2/2^k<\infty$: `bounded_weightPronicEnergy_iff_summable_dyadicMass`. |
| Parity barrier (§3.16) | Amplitudes decide payment iff $\varepsilon>1/2$; real non-principal characters give parity pairs for $0<\varepsilon\le1/2$. Sign-blind dampings accumulate there only from above: `derivedSet_signBlindDampings`, `signs_read_below_half_damping`. |
| Damping equals zero width (§3.16) | The infimum of the derived admission set is $\Theta-1/2$; RH is cofinal admission, and Möbius and Liouville have identical admission sets. See `receiverDampingRate_eq_zetaZeroAbscissa_sub_half`. |
| Wiener and pole laws (§§3.16–3.17) | Critical Wiener convolution preserves payment; a positive drift requires pole cancellation. The smooth-power criterion is exact below half damping (`receiverBounded_dirichletConv_unit_iff_critical`); partial-pole-sum laws cover $(0,1)$, with a sharp $\sqrt{\log}$ endpoint weight and additive vanishing order. |
| Boundary energy (§3.17) | At half damping, payment is equivalent to bounded vertical-line energy of $\zeta(s)(C(s)-m)/s$ for $1/2<\sigma<3/4$; it gives $\lvert C(\sigma)-m\rvert\le2\sqrt E(2\sigma-1)^{-1/2}$. |
| Horizon-limit commutation (§3.17) | Uniformly paid rows pay the limit; on the damped class the converse holds exactly for $\varepsilon\ge1/2$: `horizonLimit_commutes_with_receiver_iff`. |
| Multiplicative phase diagrams (§3.18) | Constant, residue-flip, subgroup, oscillating and prime-varying patterns have sharp criteria. Prime signs and prime means alone do not determine payment. |
| Zero-divisor spectroscopy (§3.19) | Log-power probes detect zeros with matching multiplicity; half-damped probe energy measures $\lvert\zeta\rvert^2$ on the critical line. |
| Fermi observability (§3.11) | Dyadic and $p$-adic schedules are injective iff at most one slot is missing (`fermiScheduleInjective_iff`); conditioning grows as $(4/\pi^2)(\log_2N)^2$ (`fermiPhysicalInverseConstant_logb_limit`). Anchored/block-mean-zero two-gap recovery and the wavelet bulk/tail bridge extend this calculus. |
| Finite-row parity (§3.16) | At every horizon, paired rows agree in mean, Selberg/Bézout forms, variance, successor covariance/reserve, primitive energy, Franel gcd form, lag covariances, tuple variances and torus Poincaré excess. Their pronic receivers split for $0<\varepsilon\le1/2$: `CompletePeriodQuadraticFormsAgreeOnParityRowPairs`. |
| Odd quotient (§§3.13–3.14) | Source energy equals the Weil form plus twice a squared pole moment; RH is the cross-lobe bound of §7.4. The strict sandwich and five/nine-modulus classifications locate what lobe-local estimates leave unpaid. |
| Buchstab laws (§§3.7–3.8) | Radical-invariant band jumps give $A(B)<0$ through $9$, first positivity at $10$ and nonconcavity at every power of five. The damped crossover is $\Lambda(\varepsilon)\pm O(\varepsilon^2)$, with second/third-order dissipation laws. |
| Signed interior and selectivity (§3.21) | Cofactor rows preserve the Haar mean and transfer along growing cutoffs. The Vaughan Gram diagonal is sign-blind; Bézout-selective laws retain successor information that the Beurling-universal and sign-blind classes lose. |

---

## 5. Traps and sharp boundaries

| Trap | Why it fails |
|---|---|
| RH "lives" only in $N<M\le N^2$ | No such restriction is justified; trans-horizon control is needed at every scale. |
| The full period is $N!$ | The least period divides $\operatorname{lcm}(1,\dots,N)$; $N!$ is only a convenient common period. |
| Full-period diagonalization controls a moving window | Period laws fix complete periods; short and moving windows are classified by endpoint states instead. |
| The unit envelope holds beyond ratio five | False at $k=5N+5$ for arbitrarily large horizons; the ladder continues with exact rungs $2$ at ratio $11$ and $3$ at ratio $13$, and grows like $Q/\log Q$. |
| Ratio five is a sign boundary | Integer jump energy certifies nonpositive Möbius defect up to radical ratio $11$; a positive Möbius defect needs ratio at least $11$. |
| Endpoint-square methods reach every scale | They fail at ratios $(\log N)^{O(1)}$, where the envelope is unbounded; beyond $10N^2$ the long-window law takes over. |
| The defect sign needs a damping radius shrinking with $N$ | At large horizons the sign holds at every prefix uniformly for $\varepsilon\in[0,1]$; rough-prime boundaries do not degenerate as $\varepsilon\to0$. |
| The receiver row needs the envelope ladder | It observes the complete damped divisor function, which never exceeds its initial value; one jump controls its sign. |
| The Möbius picture is the $\varepsilon\to0$ limit of the damped one | Only on bounded horizon ranges: the cofinal limit and the damping limit do not commute for the variance, the dissipation and the energy profile, and the crossover scale diverges. |
| Prime horizons dissipate | For Möbius every large prime horizon injects energy at every ratio $B\ge2$; damped prime horizons dissipate only beyond the crossover $\exp((1+o(1))\log(1/2\varepsilon)/\varepsilon)$. |
| Composite horizons follow the prime slope | The step depends on the smooth core; $m=6$ has negative slope, $2q$ steps by exactly $-B$. |
| Band structure survives damping | The damped profile is linear in the band index; the Möbius band calculus is a pure $\varepsilon=0$ phenomenon. |
| Complete-period averages can bound the discrepancy uniformly below $\varepsilon=1/2$ | The primitive energy diverges on the period torus for $\varepsilon\le1/2$; the pronic weighting of small arguments is essential. |
| The Nyman origin tail uses $dx/x^2$ with $\{1/(kx)\}$ | That integral has a periodic integrand and diverges; the correct transform is $\int_N^\infty\lvert\cdot\rvert^2du/u^2$. |
| A tail bound proves Nyman approximation | Weak closure needs bounded norms and local convergence on compact intervals as well. |
| Selberg damping keeps exact divisor cancellation | For $c(d)=\mu(d)\log(N/d)/\log N$, $\sum_{d\mid k}c(d)=\Lambda(k)/\log N$, not zero. |
| $\Lambda(d)=\log(d/\tau(d))$ for every $d$ | $d=6$ has clock $1$ and $\Lambda(6)=0$; the prime guard is essential. |
| Clock visibility is a valuation-change rule | It describes nonvanishing of a Ramanujan lag multiplier, not when an integer's valuation changes. |
| Translation statistics of a squarefree-supported row see the clock of the lag | They see only $\operatorname{rad}(h)$. |
| State equality is successor dynamics | Deterministic successor evolution holds only for $N\le2$; the phase $k\bmod L_N$ is the refinement. |
| Finite observability gives a cofinal source estimate | Exact recovery and conditioning constants say nothing about cancellation in the recovered values. |
| Odd boundaries alone determine the row | Not once $N\ge2$; a schedule needs all but one of the $\lfloor\log_2N\rfloor+2$ slots. |
| Injectivity of the selected trace gives uniform physical coercivity | The optimal constant grows like $(4/\pi^2)(\log_2N)^2$, even on nonnegative coefficients; reading every boundary only divides it by four. |
| The conditioning loss is the price of reading through boundaries | It is the price of the gap's position: a gap at half depth is free, an edge gap costs four. |
| The antichain capacity law classifies literal PM rows | It concerns antichain packets with restricted odd prime factors; the cofactor row is handled by the four-free law instead. |
| The highest-dyadic recovery theorem applies to Möbius rows | Squarefree-supported rows have zero highest-dyadic anchor for $N\ge4$; the hypothesis excludes them. |
| Checkpoint signs transfer to every prefix | Rough checkpoints and certified fibres are families; the all-prefix sign is a separate theorem at large horizons. |
| A bounded difference of two uncontrolled energies bounds either | Only the difference is controlled. |
| Off-line chain excess excludes a zero | It is a lower bound for an inserted mode, not an upper constraint on the same complete energy. |
| The signed quotient inherits the source mass | Source mass does not descend through the signed radical; only the signed form does. |
| The polar shift is a parameter that can be tuned | It is a gauge: two odd polar ground vectors differ by an element of the signed radical, so all their pairings agree and equal one shift-independent moment $\langle q,\tanh_L\rangle$. |
| The odd gap between source energy and Weil form is an inequality to be estimated | It is the exact identity $\mathrm{sourceEnergy}=\mathrm{weilForm}+2\langle q,\tanh_L\rangle^2$; the content is nonnegativity on the kernel of that one functional. |
| A lobe-local inequality settles the odd sector | The Rayleigh excess and the chiral drift bound are both lobe-local; the four-term excess is a cross-lobe statement. |
| Two trans-horizon observers can be small together | On the second octave the Fermi second difference plus the Bézout forward gradient equals $-2\mu$ of the first-octave parent, so their combined energy is at least twice the odd squarefree count of the window. |
| Finite multiplicity above $1/2$ gives compactness | Eigenvalues may accumulate at $1/2$; the threshold radical is infinite-dimensional. |
| A fixed cosh/sinh absorption coefficient | Fails for every $R\ge\log2$; the literal ratio grows like $\pi e^{2x}$. |
| Rewriting an eigenvalue bound as a four-term inequality proves it | It restates the RH-equivalent criterion in new coordinates. |
| Replacing $v$ by $\lvert v\rvert$ and keeping only the Markov gain | Contraction loses the factor between $\mu<1$ and $\mu\le1/2$; the pole and parity data change. |
| Vanishing primitive energy settles the sign | The $O((n+1)^{-2})$ family only excludes a uniform gap relative to the graph norm. |
| Compensated positivity is odd Weil positivity | The local correction is not shown to be paid by jump energy on arbitrary profiles. |
| The PM receiver needs a bound uniform in damping | It needs a bound uniform in the horizon at each arbitrarily small fixed damping; the constant may depend on $\varepsilon$. |
| Ramanujan amplitudes, translation statistics or pronic mode masses decide the receiver | Only above half damping. For every $0<\varepsilon\le1/2$ every real non-principal character gives an unconditional parity pair; amplitude invariance of boundedness holds iff $\varepsilon>1/2$. |
| The barrier is "no bound $E_T\le F(\lvert W_c\rvert)$" | That follows from a single divergent weight. The parity content is that the predicate "paid" is not a function of the amplitudes, which needs a pair. |
| Adding more sign-blind observables narrows the gap | Blindness is closed under post-processing, pairing and families of arbitrary cardinality; the floor in the damping unit stays $\tfrac12$ for every amplitude-derived reading. |
| One admissible damping bounds the width | It does not: a single admissible damping only translates zeros along $\rho,\rho-\varepsilon,\rho-2\varepsilon,\dots$. The width is the infimum of the derived set of the admissible dampings, exactly $\Theta-\tfrac12$. |
| Higher-degree translated moments see the parity of squarefree rows | Cubic moments pin odd-modulus signs, but the even flip is invisible at every degree and can break the receiver (the Fermi pair). |
| Finitely many flipped primes make a parity pair | Local factors with $\lvert a\rvert<\sqrt p$ never change the receiver class, nor do flips on prime sets of convergent $\sum p^{-1/2-\varepsilon}$; a pair needs a prime set of divergent critical-line mass. |
| Higher prime powers are invisible to the receiver | At half damping, for every $\lvert f'\rvert\le1$ off the two extremal two-adic tails; on those tails the factor at $2$ vanishes on $\operatorname{Re}w=1$ and can pay an unpaid companion. For $1$-pretentious weights they enter through the local factor $L_p$ at the pole. |
| A separating observable bounds the receiver | The logarithmic moments separate every pair and bound nothing; separation is qualitative and carries no exponent. |
| Divergence proofs need a nonnegative weight | The pole law proves divergence of sign-changing convolutions $k\star q$ through the Mellin pairing at $\sigma=1-\varepsilon+\delta$. |
| The density of flipped primes decides the receiver of a sign pattern | Only on residue patterns (quarter law). Oscillating prime patterns with the same prime signs and the same prime mean can be paid and unpaid; the receiver reads the size of the Dirichlet series beside the line at every height. |
| The receiver sees the complex amplitude of a prime oscillation | It sees only $\Re(ae^{i\varphi})$: the imaginary part couples to $\arg\zeta$, which is bounded at the pole. Two phase shifts with the same $a\cos\varphi$ have the same receiver. |
| Below half damping a flipped density near $1/2$ is enough | A paid weight needs logarithmic prime mean in $\{0,-1\}$ exactly, at every height (integer-order obstruction); subgroup flips of index $k\ge3$ are unpaid at every $\varepsilon<1/2$. |
| Payment of a probe is an estimate for Möbius | Probe theorems evaluate weights whose series are known in terms of $\zeta$; the Möbius series $1/\zeta(s+\varepsilon)$ is the unknown. |
| Real-axis abscissa blowup or Lipschitz tests detect unpaid oscillating probes $d^{-\varepsilon}\cos(t\log d)$ ($t\ne0$) | For $t\ne0$, $\sum_d c_{\varepsilon,t}(d)d^{-\sigma}=\operatorname{Re}\zeta((\sigma+\varepsilon)-it)$ converges to $\operatorname{Re}\zeta(1-it)$ and is Lipschitz at $\sigma=1-\varepsilon$ whether $c_{\varepsilon,t}$ is paid or unpaid; the pole sits at $1-\varepsilon\pm it$. |

**Lean conventions.** Namespace: `GaloisForLFunctions.TransHorizonIncidenceMechanics`; sieve
objects come from BVI and Bi-Scale, Markov/chain/theta/Haar objects from `RHTower`.
Capstones take data (`c`, `N`, `M`, `ε`, `S`), with offsets `n + 1` or `IsTransHorizonRough`
encoding ranges. State weight/support quantifiers and nested eventual quantifiers explicitly;
do not assume positivity, cancellation or zero location. Prove summability before `tsum`.
Use symbolic prime-indexed counterexamples and proved PNT inputs: $\mathfrak m(x)\to0$,
$M(x)=o(x)$ and octave prime counts. Docstrings distinguish `[Known]`, `[Corollary]` and
`[New formulation]`; no heartbeat settings are raised.

---

## 6. Questions the theory answers and the tools it builds

### 6.1 Questions

1. **Where does a finite observer lose control?** Envelope, successor and conditioning boundaries: §§3.3, 3.9–3.11.
2. **Which observations retain the needed signs?** Parity pairs and separating moments: §3.16; separation alone gives no bound.
3. **What does the receiver read?** The source's Dirichlet series, its poles and boundary energy: §§3.17–3.19.
4. **Which arithmetic classes pay below half damping?** Wiener and pretentious classes, and multiplicative phase diagrams: §§3.16–3.18.
5. **What remains for Möbius?** A signed bound at one fixed $\varepsilon<1/2$, then cofinally as $\varepsilon\downarrow0$ (§7.1).

### 6.2 Tools

The reusable calculus is developed with its scope in §3: complementary divisors and polarization
(§§3.1–3.5), Ramanujan and Buchstab laws (§§3.6–3.8), state and Fermi inversion (§§3.9–3.11),
odd-sector collars and cross-lobe pairings (§§3.12–3.15), parity/receiver/pole calculus
(§§3.16–3.17), phase diagrams and probe spectroscopy (§§3.18–3.19), and signed hyperbola,
cofactor, Vaughan and selectivity tools (§§3.20–3.21).

The missing tools are quantitative: a signed actual-Möbius bound below half damping (§7.1),
a Class III estimate for off-diagonal Vaughan entries (§7.8), and the odd-eigenvector bound
$\mathrm{weilBilin}(q^+,q^-)\le\tfrac12\langle q_1,\tanh_L\rangle^2$ (§7.4).

---

## 7. Research boundaries and open questions

### 7.1 The actual Möbius receiver at one fixed damping below one half

Everything around the receiver is exact: the parity barrier says which data cannot decide it
(§3.16), the pole and boundary-energy laws say what it reads (§3.17), the probe theorems show it is
a faithful instrument for the zero divisor (§3.19), the damping of the Möbius receiver is the zero
width (§3.16), and the PM receiver is the interior receiver with no dipole loss (§3.21). The open
problem is one estimate: an unconditional bound
$$
\sup_T\Bigl(\sum_{i\le5}G_{ii}+R^{\mathrm{mix}}_T\Bigr)<\infty
$$
on the signed interior energy at one fixed $\varepsilon<\tfrac12$, with no zero-free-width
hypothesis, and then cofinally as $\varepsilon\downarrow0$. In arithmetic terms a power saving
$\lvert\sum_{e\le N}(\mu\star\Lambda)(e)\rvert\le CN^\beta$ at one fixed $\beta<1$ pays Möbius and
Liouville at every $\varepsilon>\beta/2$ (§3.20); Vinogradov–Korobov gives a subpower saving only.
Such a bound must retain information lost by sign-blind observations and by the
Beurling-universal identities. Within the three classes above, the successor
structure is the available source of that information; its quantitative control
of the mixed entries remains the problem.

A complementary coordinate is the cofactor energy from
[Arithmetic Defect Rigidity](../ArithmeticDefectRigidity/README.md): its Gram
geometry gives the exact identity $E=F+G-2Q$, with forcing energy $F$,
cofactor energy $G$ and signed forcing–cofactor pairing $Q$. That dictionary
provides a way to study failure by normalizing divergent energy. It does not
turn finite forcing mass, finite observations, or compactness in a weaker norm
into admission. A useful new estimate must control the signed pairing or the
whole pronic energy, including mass escaping to large indices.

### 7.2 Small horizons

All-prefix nonpositivity of the Möbius defect is certified for $N\le12$ by the overlap of the
radical envelope with the Montgomery–Vaughan window threshold, and for all sufficiently large $N$
by rough-prime boundaries; the polynomial-window regime is the only eventual one. Open: a uniform
argument covering the remaining finite range of horizons, which amounts to making the
prime-number-theorem octave count of §3.4 explicit, rather than inspecting horizons one at a time.

### 7.3 Buchstab calculus

The band averages $A(B)$ are exact class averages with radical-invariant jumps; they are negative
through $B=9$, positive at $B=10$, and the profile $P$ fails concavity along every power of five.
The cofinal slope $\kappa=\lim_N\mathrm{Cov}_N(0;\mu)$ is the one-line energy of $1/\zeta$,
$\kappa=(\rho/2\pi)\int|B(it)|^2\prod_p(1-|p+1-p^{-it}|^{-2})\,|t\zeta(1+it)|^{-2}dt$ (Bézout–Valuation
Incidence, `cofinalMobiusSlope_eq_integral_eulerProduct`). Open: the sign pattern of $A(B)$ beyond
$B=10$, and whether the Möbius band calculus admits a damped deformation that commutes with the
cofinal limit, which none of the period observables does.

### 7.4 The odd sector

RH is $\mathrm{weilBilin}(q^+,q^-)\le\tfrac12\langle q_1,\tanh_L\rangle^2$, equivalently
$\mathrm{sourcePair}(q^+,q^-)+\tfrac12\langle\lvert q\rvert_1,\mathbf 1\rangle^2\le0$, on odd resolvent
eigenvectors: a cross-lobe statement, which no lobe-local inequality proved so far reaches. On the
profile side the low-prime diagonal potential leaves exactly the nine moduli and, for $d\ge23$, the
inner axis ends of $(0,\log d)$ unpaid. Open: pay those intervals by a jump energy, or show
that the cross-lobe term has a sign; either is the nodal counterpart of §7.1.

### 7.5 Fermi–Nyman

Schedules, conditioning and two-gap recovery are classified, and the centred-prefix wavelet
identity reduces bulk boundedness and origin-tail tightness of the Fermi sequence to a subpower
prefix bound. Open: origin-tail tightness of the Möbius sequence below $\varepsilon=\Theta/2$
without zero-free hypotheses, which by the wavelet identity is the fixed-damping prefix problem of
§7.1; and identification of the weak limit of a bounded Nyman–Beurling row family from Fermi data,
which a tail bound alone does not supply.

### 7.6 The horizon-row gap

Full-horizon rows of $\mu(d)d^{-\varepsilon}$ are uniformly paid for $\varepsilon>\Theta/2$, the full
weight for $\varepsilon>\Theta-\tfrac12$, and sub-horizon rows across the whole admission range.
Between $\Theta-\tfrac12$ and $\Theta/2$ a horizon could, in principle, cut a cancelling dipole and
keep a drift. Open: close that gap for the Möbius rows, or exhibit the dipole; on the convolution
class it never occurs.

### 7.7 Beyond the solved phase diagrams

Every completely multiplicative pattern with $\lvert f(p)\rvert\le1$ is decided at half damping by the
size of $\Re\ell_f$ beside the line, height by height; below half damping a paid pattern has an
integral local exponent at every height, zero off the real axis (§3.18), and these conditions are
necessary only. Sufficient conditions below half damping need the size of the
series inside the strip, which for the Liouville pattern is the Möbius problem itself. At half
damping, multiplicative patterns reduce to their completely multiplicative companions except on two
two-adic tails (§3.16), and amplitude defects of divergent critical-line mass obey the Dini law,
including $1-c/\log\log p$ and every defect monotone along the primes (§3.18). Open: non-monotone
defects of divergent critical-line mass.

### 7.8 Research topics

1. **From separation to a bound.** The observables that separate parity pairs are classified:
   first-order data at prime powers, the logarithmic moment hierarchy, the pole value
   $K(1-\varepsilon)$ and its Taylor coefficients. Separation is qualitative. Which of them can be
   given an exponent, so that separating a pair also bounds the paid member?
2. **"Paid" as an index class.** The paid class is a union of orbits of the critical Wiener monoid,
   invariant under local factors with $\lvert a\rvert<\sqrt p$ and sparse flips, and it reads the order
   of a pole through the logarithmic pole moments. Missing is a non-perturbative index formula that
   computes the class of the Möbius weight from arithmetic counts.
3. **One obstruction from two sides.** The unpaid low-prime intervals of the odd-sector diagonal
   potential and the nine moduli of Arithmetic Incidence Positivity are the same obstruction read
   from the sieve side and from the pair side. A theorem that pays it on one side should transfer.
4. **Quantitative Class III laws.** The Bézout-selective laws of §3.21 are identities and
   classifications. Which of them, given a quantitative form, controls the off-diagonal Vaughan
   entries $G_{ij}$, $i\ne j$?

---

## 8. Working in the theory

Fix weight class, ranges of $k,M,N$, band/ratio and polynomial or long-window regime.
Keep horizon and damping limits ordered (§5); many counterexamples already have nonnegative,
squarefree support and $c(1)=1$. Audit signs through polarization with boundary squares, and
period laws through Selberg/Ramanujan coordinates. Transport certificates along radical fibres
and positive powers. A failed law should yield its first failure and strongest surviving classification.

Search neighbouring programmes before building. Beyond §6.2, the corpus supplies chain
renormalization, Haar moments, Montgomery–Vaughan bounds, Gutzmer/Hardy path inequalities,
GCD Gram kernels, theta-drop bounds and Lévy density. Lean comments explain mathematics;
status, dates and logs belong on pipeline cards.
