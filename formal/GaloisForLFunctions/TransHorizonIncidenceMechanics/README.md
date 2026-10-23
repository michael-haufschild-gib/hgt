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

---

## Place in the research

THIM is the **finite-observer theory of signed arithmetic receivers**. A divisor row can be
recovered exactly from its observations while its energy remains uncontrolled. Conversely, a
row can satisfy every complete-period variance estimate and still fail the pronic receiver.
The programme separates identifiability, conditioning, dissipation and actual payment of that
receiver; these are different mathematical demands.

Its organizing object is the centred prefix
`A_c(n) = Σ_{j≤n}((c*1)(j) − Σ_d c(d)/d)` and its energy
`Σ_{n≤T} A_c(n)²/(n(n+1))`. The pronic weight remembers small arguments even while the
coefficient horizon grows. This is why full-period diagonalization cannot replace a bound
uniform in `T`, and why the order of the horizon and damping limits matters.

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

The basic mechanisms are complementary-divisor normal forms, Dirichlet polarization with its
boundary squares retained, Ramanujan diagonalization, exact Fermi trace inversion, and Mellin
continuation. Their sharp boundaries are foundational: sign-blind payment stops above half
damping; signed horizon-limit commutation starts at half damping; below it, cancellation can
pay an infinite source while its truncated rows remain unbounded.

**The shared target.** The programmes in the table work on RH as the sign of one critical
arithmetic form and on the critical cancellation of the actual Möbius and prime source that the
sign needs. THIM contributes the receiver-side half of that problem: an exact account of what a
bound on the actual Möbius receiver below half damping must read, and of every cheaper reading that
provably cannot supply it.

Read the receivers in §1.2 before the many finite identities. Sections 2 and 3.1–3.8 explain
what the observer measures; §§3.9–3.11 explain recovery and its price; §§3.16–3.17 explain
why signs and the analytic continuation of the actual source decide the receiver; §§3.18–3.19
show what the receiver reads in multiplicative sign patterns and on probes of $\zeta$; §3.20 lists
what is proved for the actual source. §4 collects the pillar theorems, §§6–7 the questions and open
problems.

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
and the sharp obstructions on the way; it does not supply any of the three
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
primorial $N\#$ suffices, and the **radical ratio** of $k$ is its radical state
divided by $N+1$. The **observation phase** is $k\bmod L_N$. An integer $r$ is
**$N$-rough** when its only divisor $\le N$ is $1$; every prime $p>N$ is
$N$-rough, and $N$-rough integers form a multiplicative monoid. A prime
$p\in(N,2N)$ together with its neighbour divisible by four is a **rough-prime
boundary**.

The weights in use are the literal Möbius weight $\mu$, the damped weights
$c_\varepsilon(d)=\mu(d)d^{-\varepsilon}$ with complete divisor sum the **damped
divisor function**
$\tau_\varepsilon(n)=\sum_{d\mid n}c_\varepsilon(d)=\prod_{p\mid n}(1-p^{-\varepsilon})\in[0,1]$,
and the actual power-damped Ramanujan cofactor row of the PM route,
$c_Q(d)=\operatorname{Re}\bigl(d\sum_{m\le Q/d}\mu(m)w_\varepsilon(dm)\bigr)$,
supported on $[1,Q]$, squarefree-supported and vanishing on multiples of four.
The damped weight has **Ramanujan coefficients**
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

The Fermi cell matrix $2\lfloor n/2d\rfloor-\lfloor n/d\rfloor$ gives the cell
response $F_{N,c}(n)=\sum_{d\le N}c(d)\bigl(2\lfloor n/2d\rfloor-\lfloor n/d\rfloor\bigr)$
on the reciprocal cell $(1/(n+1),1/n]$, and the **boundary jump**
$J(n)=F(n)-F(n-1)$. An odd boundary reads $J(2m+1)=-s_{N,c}(2m+1)$; an even one
reads $J(2m+2)=2s_{N,c}(m+1)-s_{N,c}(2m+2)$. The physical weight of the cell
$n$ is the **pronic** weight $1/(n(n+1))$. The complete **sieve pronic energy**
$P(N,c)=\sum_{n\ge1}s_{N,c}(n)^2/(n(n+1))$ and the complete **selected trace**
energy $Q(N,c)$ of the odd and four-divisible boundary readings are both
summable for every finite horizon. Their homogeneous versions use the weight
$1/n^2$ in odd-ray coordinates $n=2^k(2j+1)$.

A **dyadic schedule** $S\subseteq\mathbb N$ reads the jump $J(n)$ at the
boundaries whose dyadic level $v_2(n)$ lies in $S$. Along the **dyadic ray**
$n=2^kb$, $b$ odd, with $z_k=s_{N,c}(2^kb)$, the level-$0$ boundary reads
$-z_0$, the level-$k$ boundary reads $2z_{k-1}-z_k$, and the ray **saturates** at
$L=\lfloor\log_2N\rfloor$: $z_k=z_L$ for $k\ge L$. A schedule therefore sees
$L+2$ **slots**, the levels $0,\dots,L$ and the saturated slot $L+1$. The
**selected trace** is the schedule missing slot $1$; the **all-boundary trace**
reads every boundary; the **one-gap trace** at level $g$ reads every boundary
except those of level $g$. The optimal physical inverse constants
$K_N=\sup P/Q$ (selected), $K_N^+$ (nonnegative coefficients), $K^{\mathrm{all}}_N$
and $K_g(N)$ measure the conditioning of each observation. Ray profiles
$y_0,\dots,y_L$ are synthesized by the coefficients $c(1)=y_0$,
$c(2^{k+1})=2^{k+1}y_{k+1}-2^ky_k$; the **Dirichlet chain**, **mixed chain**,
**soft prefix** and **Robin ramp** are the boundary structures of a ray under a
schedule.

### 2.5 Valuation clocks

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
For squarefree-supported weights the clock of the lag is invisible: the period
covariance at lag $h$ depends only on the set of primes dividing $h$.

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
in the top octave. Together with squarefree saturation this is the prime-chain
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
positive Möbius defect needs radical ratio at least $11$. A prime
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

**Long windows.** The phase-uniform window Poincaré law of the Bézout–valuation
theory gives $2\widetilde{\mathcal D}_N(M)\le4H^2-(M-10N^2)V$ with the harmonic
sum $H$, the window observability constant, which has exact order $N^2$, and
the non-harmonic variance $V$. A Bertrand prime $p\in(N/2,N]$ has the
single-multiple Selberg coordinate $c(p)/p$, so $V\ge(p-1)c(p)^2/p^2$, at least
$1/(2N)$ for the Möbius weight. For the Möbius weight the harmonic sum is
bounded by one (the floor identity $\sum_{d\le N}\mu(d)\lfloor N/d\rfloor=1$), so
the long-window regime starts at the quadratic scale at every horizon
$N\ge2$:
$2\widetilde{\mathcal D}_N(M;\mu)\le4-(M-10N^2)/(2N)$, nonpositive beyond
$10N^2+8N$; at large horizons the white-noise floor $V\ge1/288$ of §3.6 makes
the slope horizon-uniform, $2\widetilde{\mathcal D}_N(M;\mu)\le4-(M-10N^2)/288$.
For the damped weight $\lvert H_\varepsilon(N)\rvert\le3$ and the threshold is
$10N^2+72N^{1+2\varepsilon}$. The polynomial-window regime has not yet ended
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
uniformly small on every polynomial range $n\le Q^r$. Far beyond its horizon the
receiver row observes the complete damped divisor function, which obeys the
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
all large horizons. Hence the normalized correlation tends to zero at every
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
$\Delta(3,B)=2\lfloor B/2\rfloor-B$, $\Delta(6,B)=-B-2\lfloor B/5\rfloor$. On the
divisor side the prime pairing of §3.2 splits every squarefree step
$\Delta(pa,B)=-B-2\mu(a)\sum_{a<d<pa,\ p\nmid d}\mu(d)\lfloor B\gcd(d,a)/d\rfloor$ into
the universal dissipation $-B$ and a window correction; for an odd prime $q$
no odd $d\in(q,2q)$ meets $q$, so the horizon $2q$ steps by exactly $-B$ in every
band $B\le q+1$, and $\mathcal E_{2q}(M)=\mathcal E_{2q-1}(M)-\lfloor M/(2q)\rfloor$
for $M<2q(q+2)$.

**Band averages and the energy profile.** The horizons of core $r$ in band $B$
have density $\delta_B/r$ with $\delta_B=(6/\pi^2)\prod_{p\le B}p/(p+1)$, so the
mean step of band $B$ exists and is the finite class average
$A(B)=\delta_B\sum_{r\mid B\#}v_B(r)/r$ with $v_B(1)=B-2$, $v_B(r)=\Delta(r,B)$.
Telescoping the horizon from the top value $\mathcal E_M(M;\mu)=1$ down to $N$
through the bands $(M/(b+1),M/b]$ gives
$$
P(B)=\lim_N\frac{\mathcal E_N((B+1)N;\mu)}N=-(B+1)\sum_{b\le B}\frac{A(b)}{b(b+1)},
\qquad A(B)=(B+1)P(B-1)-BP(B),
$$
so the mean horizon step of every band is a second difference of the energy
profile, which the Bézout–valuation theory builds from dilation-pair densities;
$A(1)=-6/\pi^2$, $A(2)=-4/\pi^2$, $A(3)=-4/\pi^2$, $A(4)=-2/\pi^2$ (in bands
$3$ and $4$ the cores are $1,2,3,6$ with density $3/\pi^2$ each divided by the
core), $P(1)=6/\pi^2$, $P(2)=11/\pi^2$, $P(3)=16/\pi^2$, $P(4)=41/(2\pi^2)$: the
band means $P(B)-P(B-1)$ of the squared response are $6,5,5,9/2$ in units of
$1/\pi^2$, and each of the first four bands dissipates on average. Centering the
$q=1$ quotient yields $(B-2)(\mathcal E_n-\mathcal E_{n+1})=S_2^2-((B-2)\mu(n+1)+S_2)^2$
with $S_2=\sum_{2\le q\le B}s_{n,\mu}(q(n+1))$, and a completed square gives the
universal subadditivity
$\mathcal E_N(M)\le\mathcal E_{N+1}(M)+\mathcal E_N(\lfloor M/(N+1)\rfloor)$ at
prime horizons.

### 3.8 The damped observer

Every fixed damping changes the trans-horizon mechanics qualitatively, and the
cofinal limit does not commute with $\varepsilon\to0$.

**Freezing into $\tau_\varepsilon$.** On the linear window $k\le(B+1)N$ an integer
has at most $B$ divisors above the horizon, each damped by at least
$(N+1)^{-\varepsilon}$, so $\lvert\tau_\varepsilon(k)-s_N(k;c_\varepsilon)\rvert\le B(N+1)^{-\varepsilon}$
uniformly, and $\mathcal E_N((B+1)N;c_\varepsilon)/N\to(B+1)\mathbb E[\tau_\varepsilon^2]$:
the damped energy profile is linear in the band index with slope
$\mathbb E[\tau_\varepsilon^2]\sim\varepsilon/2$, and the whole Möbius band
structure is invisible to it. Over complete periods the trans-horizon tail
$\tau_\varepsilon-s_N$ has mean square at most the tail beyond $N$ of the convergent
gcd series $G(d,e)=(de)^{-\varepsilon}/\operatorname{lcm}(d,e)$ (its boxes are
Selberg forms of $d^{-\varepsilon}$, bounded by $\zeta(1+\varepsilon)^2\zeta(1+2\varepsilon)$),
so $Q_{\mathrm{Sel}}(N;c_\varepsilon)\to\mathbb E[\tau_\varepsilon^2]$ and
$\mathrm{Cov}_N(0;c_\varepsilon)\to V(\varepsilon)\sim\varepsilon/2$. Against the Möbius
floor $1/288$ this is the first non-commuting limit:
$\lim_{\varepsilon\to0}\lim_N\mathrm{Cov}_N(0;c_\varepsilon)=0<1/288\le\liminf_N\mathrm{Cov}_N(0;\mu)$.
The Möbius variance lives in the trans-horizon divisors, which every fixed
damping suppresses.

**Parseval and the receiver's spectrum.** The Selberg coordinates converge to
the Ramanujan coefficients, $Y_N(e;c_\varepsilon)\to w_\varepsilon(e)$, dominated by
$\zeta(1+\varepsilon)e^{-1-\varepsilon}$, so the period forms converge term by term
and
$$
\mathbb E[\tau_\varepsilon^2]=\sum_e\varphi(e)w_\varepsilon(e)^2,\qquad
V(\varepsilon)=\sum_{e\ge2}\varphi(e)w_\varepsilon(e)^2,\qquad
Q_{\mathrm{Bez}}(N;c_\varepsilon)\to\sum_e\mu(e)w_\varepsilon(e)^2 .
$$
The receiver row at horizon $Q+1$ has Selberg coordinates exactly $w_\varepsilon(e)$
for $e\le Q+1$, so its period variance is the partial Parseval sum, increasing
in the cutoff, converging to $V(\varepsilon)$ and never exceeding it, and its
dissipation rate is at most $2V(\varepsilon)$: the receiver's period statistics
are bounded uniformly in the horizon at each fixed damping, and at small damping
they sit strictly below the Möbius floors at every cutoff. The lag covariances
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
the damped defect dissipates linearly in the window at the Haar dissipation rate
of $\tau_\varepsilon$; the prime-boundary mechanism of §3.4 is the visible part of
a positive-density dissipation. The rate is half the damping: the dissipation
splits as variance minus lag-one autocorrelation, $R(\varepsilon)=V(\varepsilon)-A_\varepsilon(1)$,
with $\lvert A_\varepsilon(1)\rvert\le16\,\mathbb E[\tau_\varepsilon]^2=O(\varepsilon^2)$
against $V(\varepsilon)\sim\varepsilon/2$, so $R(\varepsilon)/\varepsilon\to\tfrac12$,
$R(\varepsilon)/V(\varepsilon)\to1$, and the window defect has small-damping slope
$\lim_{\varepsilon\to0}\varepsilon^{-1}\lim_N\widetilde{\mathcal D}_N((B+1)N;c_\varepsilon)/N=-(B+1)/2$:
every unit of window dissipates half the damping parameter. At second order
the two rates separate,
$$
V(\varepsilon)=\tfrac\varepsilon2-\varepsilon^2+o(\varepsilon^2),\qquad
R(\varepsilon)=\tfrac\varepsilon2+o(\varepsilon^2),\qquad
A_\varepsilon(1)=-\varepsilon^2+o(\varepsilon^2):
$$
Euler's constant cancels in the second moment
$\mathbb E[\tau_\varepsilon^2]=H(\varepsilon)\zeta(1+2\varepsilon)/\zeta(1+\varepsilon)^2=\varepsilon/2+o(\varepsilon^2)$,
parity kills the lag-one Bézout mean to $O(\varepsilon^3)$ (removing the prime
$2$ factors out $1-(2^{1+\varepsilon}-1)^{-2}$), and consecutive values of
$\tau_\varepsilon$ are anti-correlated at exactly the scale of the squared mean
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
is $e^{\gamma+o(1)}(2\varepsilon)^{-1/\varepsilon}$; since the Möbius harmonic sums decay
like $(\log t)^{-3}$ the Abel error is $O(\varepsilon^3p^{-\varepsilon})$ against a gap
of at least $2\varepsilon^2\rho_\varepsilon$ once $\log p$ leaves $\Lambda(\varepsilon)\pm\varepsilon$,
and the window is additive: injection for $\log p\le\Lambda(\varepsilon)-\varepsilon$,
dissipation for $\log p\ge\Lambda(\varepsilon)+\varepsilon$. The damped observer is
Möbius-like, injecting at prime horizons, up to horizons
$e^{\gamma-\delta}(2\varepsilon)^{-1/\varepsilon}$ and dissipative beyond
$e^{\gamma+\delta}(2\varepsilon)^{-1/\varepsilon}$; the receivers at fixed small damping
live beyond this scale.

**The threshold at one half.** The primitive energy has the Jordan spectrum
$12\,\mathcal E_{\mathrm{prim}}(N;c)=\sum_{2\le q\le N}J_2(q)Y_N(q)^2$ with
$J_2(q)\le q^2$. For the damped row the mode masses are of size $q^{-2\varepsilon}$:
for $\varepsilon>1/2$ the primitive energy is bounded uniformly in the horizon and
converges to $\tfrac1{12}\sum_{q\ge2}J_2(q)w_\varepsilon(q)^2$; for $0<\varepsilon\le1/2$
the prime modes alone carry $J_2(p)w_\varepsilon(p)^2\ge\tfrac34\mathbb E[\tau_\varepsilon]^2/p$,
whose sum diverges, so it tends to infinity, with the exact order
$\mathcal E_{\mathrm{prim}}(N;c_\varepsilon)\asymp N^{1-2\varepsilon}$ for $0<\varepsilon<1/2$
(every mode at most $\zeta(1+\varepsilon)^2q^{-2\varepsilon}$; the odd squarefree top
octave carries at least $N^{1-2\varepsilon}/3456$): the discrepancy grows like a walk
of $N^{1-2\varepsilon}$ independent unit steps. For the Möbius row the top octave
forces linear growth, capped at $N\log N$ by $\lvert\mathfrak m_f\rvert\le f/\varphi(f)$.
This is the barrier $\varepsilon=1/2$ of the PM receiver
seen on the period torus: below one half no horizon-uniform bound on the
discrepancy can come from complete-period averages, and a receiver estimate must
use the pronic weighting of small arguments.

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

**Two unconditional tightenings on the lobes.** First, a Rayleigh excess: for a primitive resolvent
eigenvector the modulus–primitive excess equals, exactly, four times a cross-lobe combination of a
resolvent pairing and the rank-one ground-vector products, and the cross-lobe resolvent pairing is
bounded below by $-\nu^2\mathrm{sourcePair}(q^+,q^-)>0$ at positive eigenvalue. Second, a chiral
drift inequality holding on *both* lobes of every odd graph vector,
$$
\langle \mathrm{primeShift}\,q^+,q^+\rangle^2+\tfrac14\langle\mathrm{oddPrimeDrift}\,q,\lvert q\rvert\rangle^2
\ \le\ \langle\mathrm{primeDiagonal}\,q^+,q^+\rangle^2 ,
$$
because the odd prime-drift operator has vanishing diagonal on odd vectors. Both are
unconditional and lobe-local; neither supplies the four-term excess, and the gap between them and
it is where the odd sector stands.

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
collar mixed density to a one-point diagonal potential; a Stieltjes
integration by parts turns $\sum_{\log d<a}\Lambda(d)d^{-1/2}(\cdots)$ into a pole
term plus a Chebyshev discrepancy transport; and the mean-value comparison
$m_a(x)\le(2M/\sinh(a/2))\sinh(x/2)$ on $[0,R]$, with $M$ a bound for $\Theta'$ on
$[a-R,a+R]$, bounds the cosh mass by a sinh potential,
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
(`poleValue_eq_zero_and_poleSlope_eq_zero_of_receiverBounded`). The receiver reads the order of the
pole, and the separating observables on the kernel side are the Taylor coefficients of $K$ at
$s=1-\varepsilon$, the counterpart of the logarithmic hierarchy.

**The damping unit, and the closure of the blind class.** The barrier has a number and a scope.
The dampings at which the sign-blind data decide the class are exactly $(\tfrac12,\infty)$, and the
derived set of that range is $[\tfrac12,\infty)$: the threshold is attained from one side only, so
no limiting argument along admissible dampings reaches it. Blindness is closed under
post-processing, pairing and families of arbitrary cardinality — a method may read as many
amplitude-derived observables as it likes, in any combination, and gains nothing — so the barrier
is a floor on a class of methods and not a list of inadequate statistics, and its value in the
damping unit is $\tfrac12$.

For the literal damped Möbius receiver the threshold is the zero width itself. The set of
admissible dampings has infimum of its derived set exactly $\Theta-\tfrac12$
(`receiverDampingRate_eq_zetaZeroAbscissa_sub_half`), so RH is the accumulation of admissible
dampings at $0$, equivalently the cofinal budget criterion
(`riemannHypothesis_iff_cofinal_budget`); and conversely a bound at any single damping is worth
nothing in the width unit, because one admissible damping only translates zeros along the chains
$\rho,\rho-\varepsilon,\rho-2\varepsilon,\dots$. The receiver's damping is therefore a genuine
width coordinate, with the same endpoint behaviour as the aperture: all the content sits at the
accumulation, none at any interior point.

**Reading.** In every case proved, a pole of the weight's Dirichlet series on or to the right of
$\operatorname{Re}s=1/2$ leaves the receiver unpaid and zeros never do; in the pole-law cases the
pole sits at $s=1-\varepsilon$. A parity pair is a pair in which the twist creates such a pole: the
positive twins acquire the pole of $\zeta$, moved to $s=1-\varepsilon$, by flipping a positive density
of primes. For the Möbius weight the series is $1/\zeta(s+\varepsilon)$, whose poles to the right of
$\operatorname{Re}s=1/2$ are the zeros of $\zeta$ with $\operatorname{Re}\rho>1/2+\varepsilon$; these are
what a bound on the Möbius receiver must exclude, and no sign-blind datum can see them.

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
Uniform line-energy bounds as $\sigma\downarrow1/2$ are equivalent to payment
([TheHalfDampedReceiverIsTheBoundaryEnergyOfItsDirichletSeries](TheHalfDampedReceiverIsTheBoundaryEnergyOfItsDirichletSeries.lean)).
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

**The partial pole sums.** The exact criterion behind the logarithmic threshold is a signed
energy. With $S_k(n)=\sum_{j\le n}k(j)j^{-1/2}$ the partial sums of the pole value and
$Z=\lim_N(\sum_{d\le N}d^{-1/2}-2\sqrt N)\le-1$, the receiver of $k\star d^{-1/2}$ satisfies
$\lvert\sqrt{E_T(k\star q)}-2\lvert Z\rvert\sqrt{L_T(k)}\rvert\le B$ at every cutoff, where
$L_T(k)=\sum_{n\le T}S_k(n)^2/(n+1)$
(`abs_sqrt_weightPronicEnergy_dirichletConv_unit_half_sub_le`). Hence $k\star d^{-1/2}$ is paid iff
$\sum_nS_k(n)^2/(n+1)<\infty$
(`receiverBounded_dirichletConv_unit_half_iff_summable_partialPoleSum`). The hyperbola method at
$s=\lfloor\sqrt n\rfloor$ gives $A_q(n)=2Z\sqrt n+O(n^{1/4})$, each dilated remainder has pronic
norm $O(j^{-1/2})$, and Minkowski sums them: a nonzero pole value makes $L_T$ diverge,
$\sqrt{\log}$-summable kernels with vanishing pole value make it converge, and the lacunary kernel
holds its partial pole sums at $-2^{-(R+1)}$ on $[J_R,J_{R+1})$.

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
prime mean is quantized at every height.

**Residue-class flips.** For $f_{q,S}$ flipping the primes in the classes $S\subseteq\mathbb Z/q$,
the flipped primes have exact logarithmic density $\rho=\#(S\cap(\mathbb Z/q)^\times)/\varphi(q)$
(Dirichlet's theorem in integrated form). At half damping every flip with $\rho\le1/4$ is unpaid,
the boundary included (`not_receiverBounded_residueFlip_half_of_le`): the complex class density and
the Euler lower bound $\log\lvert F\rvert\ge\log\lvert\zeta\rvert-2\sum_{f(p)=-1}\Re p^{-w}-O(1)$ give
$\lvert C\rvert^2\gtrsim1/\lvert s-1/2\rvert$. Below half damping only $\rho\in\{1/2,1\}$ can be paid
(`not_receiverBounded_residueFlip`). For $S$ closed under inversion on the units, orthogonality
gives the Euler bound $\lvert F\rvert\le e^B\lvert\zeta\rvert^{1-2\rho}\prod_{\chi\ne1}\lvert L(\cdot,\chi)\rvert^{e_\chi}$
with real exponents, and the quarter law is exact: paid at half damping iff $\rho>1/4$
(`receiverBounded_residueFlip_half_iff`). For a subgroup $H$ of index $k\ge2$, flipping the primes
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

**Reading.** Neither the density of flipped primes nor the real-axis prime mean decides the
receiver of a multiplicative weight; the size of its Dirichlet series beside the line
$\Re s=1-\varepsilon$, at every height, does. Symmetric residue patterns are the class on which the
real-axis density happens to determine that size. For the Möbius weight the series is
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

**Reading.** These theorems are spectroscopy, not estimates. They evaluate probes whose Dirichlet
series are known in terms of $\zeta$, and they show the receiver is a faithful instrument for the
zero divisor. Bounding the actual Möbius receiver is a different problem: its series is
$1/\zeta(s+\varepsilon)$, the unknown itself.

### 3.20 The actual source at small damping

**Möbius and Liouville.** Removing the $\varepsilon\ge1/4$ restriction from the hyperbola split gives
$\lvert A_\varepsilon(n)\rvert\le3D^{1-\varepsilon}+(13/\varepsilon)LnD^{-\varepsilon}$, and with
Vinogradov–Korobov the all-damping prefix bound
$\lvert A_\varepsilon(n)\rvert\le(K/\varepsilon)n^{1-\varepsilon}e^{-\sqrt{\log n}/40}$. Uniform receiver
bounds hold on the horizon-dependent zero-free band above every positive damping floor; Möbius and
Liouville have the same positive admission set and the same width accumulation threshold
$\Theta-\tfrac12$; and RH is admission at every positive damping, for either weight
(`riemannHypothesis_iff_forall_pos_receiverBounded_moebius`,
`riemannHypothesis_iff_forall_pos_receiverBounded_liouville`,
`sInf_derivedSet_liouville_dampings_eq_zetaZeroAbscissa_sub_half`). The shrinking band admits no
fixed $\varepsilon<1/2$ at all horizons.

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

**Oscillating-probe source estimates.** Every oscillating prefix decomposes into the fractional-part
sawtooth sum $S_{\varepsilon,t}(n)=\sum_{d\le n}c_{\varepsilon,t}(d)(\lfloor n/d\rfloor-n/d)$ and the
universal tail drift $T_{\varepsilon,t}(n)=-n\sum_{d>n}c_{\varepsilon,t}(d)/d$
(`weightCenteredPrefix_oscillatingSmoothPower_eq_sawtooth_add_tail`). Splitting $S_{\varepsilon,t}$ at
$\lfloor\sqrt n\rfloor$ (`oscillatingSawtoothPrefix_eq_short_add_long`), the short-modulus sawtooth sum
$1\le d\le\lfloor\sqrt n\rfloor$ satisfies
$\lvert S^{\mathrm{short}}_{\varepsilon,t}(n)\rvert\le(1+1/(1-\varepsilon))(\sqrt n)^{1-\varepsilon}$ and has
uniformly bounded pronic norm for every $0<\varepsilon<1$ and $t\in\mathbb R$
(`pronicNorm_oscillatingShortSawtooth_le`), so sawtooth/tail cancellation reduces to the long-modulus
sawtooth sum $\lfloor\sqrt n\rfloor<d\le n$ against the tail $d>n$
(`receiverBounded_oscillatingSmoothPower_iff_bdd_pronicNorm_longSawtooth_add_tail`). At $t=0$ both
pieces are nonpositively signed, so $\langle S^{\mathrm{long}}_{\varepsilon,0},T_{\varepsilon,0}\rangle_T\ge0$
(`pronicInner_longSawtooth_tail_zero_nonneg`, anti-alignment gap $\theta=0$) and the dyadic tail block
$d\in(n,2n]$ gives $A_{\varepsilon,0}(n)\le-2^{-(1+\varepsilon)}n^{1-\varepsilon}$ and a pure
source-estimate harmonic proof of $\neg\operatorname{ReceiverBounded}(c_{\varepsilon,0})$ for
$0<\varepsilon\le1/2$ without invoking $\zeta(1-\varepsilon)\ne0$
(`not_receiverBounded_oscillatingSmoothPower_zero_from_source`,
`pronicNorm_longSawtooth_add_tail_zero_sq_ge_harmonic`). For general $t\in\mathbb R$,
$T_{\varepsilon,t}(n)=\Re(n^\rho/(\rho-1))+O(n^{-\varepsilon})$ has unconditionally unbounded pronic
norm for all $0<\varepsilon\le1/2$ and $t\in\mathbb R$ regardless of $\zeta(\rho)$
(`not_bdd_pronicNorm_oscillatingTailDrift`) and two-sided $\Theta(T^{1-2\varepsilon})$ energy growth for
$0<\varepsilon<1/2$, $t\ne0$ (`eventually_oscillatingTailDrift_energy_le_and_ge`), while
$S^{\mathrm{long}}_{\varepsilon,t}(n)=\Re((\zeta(\rho)/\rho-1/(\rho-1))n^\rho)+O((\sqrt n)^{1-\varepsilon})$
(`abs_oscillatingLongSawtooth_sub_le`). For $0<\varepsilon<1/2$ and $t\ne0$, a strict Cauchy–Schwarz
anti-alignment bound $-\langle S^{\mathrm{long}}_{\varepsilon,t},T_{\varepsilon,t}\rangle_T\le\theta\lVert S^{\mathrm{long}}_{\varepsilon,t}\rVert_T\lVert T_{\varepsilon,t}\rVert_T$
with $\lvert\theta\rvert<1$, holding even frequently, excludes cancellation of
$S^{\mathrm{long}}_{\varepsilon,t}$ with $T_{\varepsilon,t}$
(`not_bdd_longSawtooth_add_tail_of_frequently_pronicInner_le`,
`not_receiverBounded_of_longSawtooth_tail_inner_le`); quadratic anti-alignment
$-2\langle S^{\mathrm{long}}_{\varepsilon,t},T_{\varepsilon,t}\rangle_T\le\theta(\lVert S^{\mathrm{long}}_{\varepsilon,t}\rVert_T^2+\lVert T_{\varepsilon,t}\rVert_T^2)$
with $\theta<1$ is necessary and sufficient for non-admission and for RH
(`not_receiverBounded_iff_exists_longSawtooth_tail_antiAlignment_gap`,
`riemannHypothesis_iff_forall_ne_zero_exists_longSawtooth_tail_antiAlignment_gap`,
`routeMC_longSawtooth_tail_antiAlignment_master`), with explicit coefficient
$\theta_{\mathrm{long}}(\varepsilon,t)\le1$ satisfying the eventual quadratic bound for every
$0<\varepsilon<1/2$, $t\ne0$ and $\theta_{\mathrm{long}}(\varepsilon,t)<1$ on the Vinogradov–Korobov and
bounded-height collars and iff either the long-sawtooth/tail amplitude mismatch or phase decorrelation
is positive (`eventually_longSawtooth_tail_quadratic_gap`, `longSawtoothTailGapTheta_lt_one_vk_and_box`,
`not_receiverBounded_of_longSawtooth_tail_amp_mismatch_or_decorrelation`,
`norm_sq_longSawtoothAmp_add_tailDriftAmp_eq`,
`riemannHypothesis_iff_forall_ne_zero_longSawtoothTailGapTheta_lt_one`); whereas separate tail growth
does not supply that gap because at any paid probe
$\lVert S^{\mathrm{long}}_{\varepsilon,t}\rVert_T/\lVert T_{\varepsilon,t}\rVert_T\to1$ and both
anti-alignment ratios converge to $1$
(`tendsto_longSawtooth_tail_antiAlignment_one_of_receiverBounded`). Uniform prefix bounds
$\lvert A_{\varepsilon,t}(n)\rvert\le K(\sqrt n)^{1-\varepsilon}$ and subpower energy
$E_{\varepsilon,t}(T)=o(T^{1-2\varepsilon})$ are each equivalent to admission across the polynomial gap
$T^{1-2\varepsilon}$; explicit lower bounds $E\ge\lambda T^{1-2\varepsilon}$ hold on every zero-free box and
on the Vinogradov–Korobov collar; and a three-term planted Euler kernel shows that collars near
$\varepsilon=0$ and finite admitted-parameter sets do not exclude every $0<\varepsilon<1/2$
(`plantedEulerKernel_collar_and_finiteness_obstruction`).

### 3.21 Bridges


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
near the origin and at infinity. The period forms of §3.6 and §3.8 meet the
Haar moments of $\tau_\varepsilon$ in the RH tower's PM lane (second density,
variance, Ramanujan weights), the band averages of §3.7 reproduce the
Bézout–valuation energy profile, and the long-window law of §3.4 is the window
Poincaré law of that theory with its variance bounded below.

---

## 4. Foundational pillar theorems

All unconditional; capstones take data only, and RH appears as the conclusion of an implication or
inside an equivalence.

1. **The global sign of the defect.** At every sufficiently large horizon the renormalized prefix
   defect is nonpositive at every prefix, uniformly for $\varepsilon\in[0,1]$ with one threshold, by
   rough-prime boundaries in polynomial windows and the window Poincaré law beyond $10N^2$
   (`eventually_pmPowerDamped_renormalizedDefect_nonpos_uniform`); the actual cofactor row has the
   same sign through one jump of the damped divisor function
   (`eventually_pmCofactor_renormalizedDefect_nonpos_all`).
2. **The envelope boundary at ratio five.** The unit envelope holds exactly up to ratio five and
   fails at $5N+5$ for arbitrarily large horizons, with exact further rungs and a $Q/\log Q$ ladder
   (`sieveRenormalizedPrefixDefect_moebiusReal_five_succ_nonpos`,
   `sieveSeq_moebiusReal_rung_two_family`, `sieveSeq_moebiusReal_rung_three_family`).
3. **Period laws cannot pay the pronic receiver.** The Möbius response is asymptotically white noise
   on its period (`tendsto_periodCorrelation_moebius`), the damped period variance is bounded
   uniformly in the horizon, and the primitive energy diverges for $\varepsilon\le1/2$
   (`tendsto_sievePrimitiveEnergy_pmPowerDamped_atTop`); the response-level pronic energy commutes
   with the damping limit (`tendsto_sieveTotalPronicEnergy_moebius`), which is not primitive
   admission.
4. **Positive weights are decided by their dyadic masses.** A nonnegative weight is paid iff
   $\sum_kM_k^2/2^k<\infty$ (`bounded_weightPronicEnergy_iff_summable_dyadicMass`).
5. **The parity barrier.** On the damped class boundedness of the receiver is a function of the
   Ramanujan amplitudes iff $\varepsilon>1/2$ (`receiverBounded_amplitudeInvariant_iff`,
   `parity_barrier`); every real character gives an unconditional parity pair at every
   $\varepsilon\le1/2$ (`char_parityPair`), and sign-blind dampings accumulate only from above at
   $1/2$ (`derivedSet_signBlindDampings`, `signs_read_below_half_damping`).
6. **The damping of the Möbius receiver is the zero width.** The infimum of the derived set of
   admissible dampings is $\Theta-\tfrac12$ (`receiverDampingRate_eq_zetaZeroAbscissa_sub_half`), RH is
   cofinal admission (`riemannHypothesis_iff_cofinal_budget`), and Möbius and Liouville are admitted
   at the same dampings (`receiverBounded_moebius_iff_liouville`).
7. **The Wiener algebra and the pole law.** Critical Wiener kernels preserve paid receivers
   (`receiverBounded_dirichletConv`); against a positive drift a convolution is paid only if the
   kernel vanishes at the pole (`not_receiverBounded_dirichletConv_of_drift_critical`); on the smooth
   power the hyperplane law is exact below half damping and has the sharp $\sqrt{\log}$ weight at
   half damping (`receiverBounded_dirichletConv_unit_iff_critical`,
   `receiverBounded_dirichletConv_unit_half_iff_summable_partialPoleSum`).
8. **The receiver is a boundary energy.** At half damping the receiver is the vertical-line energy
   of $\zeta(s)(C(s)-m)/s$ as $\sigma\downarrow1/2$, and a paid weight has
   $\lvert C(\sigma)-m\rvert\le2\sqrt E(2\sigma-1)^{-1/2}$ (`weightPronicEnergy_le_of_lineEnergy_le`,
   `abs_dirichletSeries_sub_mean_le_of_energy`).
9. **Horizon-limit commutation starts at half damping.** Uniformly paid rows pay the limit, and the
   converse holds on the damped class exactly from $\varepsilon=1/2$ (`horizonLimit_commutes_with_receiver_iff`).
10. **Multiplicative phase diagrams.** The constant-sign plane, the quarter law of symmetric residue
    flips, subgroup flips and oscillating prime patterns are decided exactly
    (`receiverBounded_constantSign_damped_iff`, `receiverBounded_residueFlip_half_iff`,
    `receiverBounded_subgroupFlip_iff`, `receiverBounded_oscWeight_phase_diagram_iff`); prime signs and
    prime means do not decide the receiver (`exists_paid_unpaid_with_same_prime_signs_and_mean`).
11. **The receiver reads the zero divisor.** Oscillating log-power probes are paid exactly at zeros
    of $\zeta$ of the matching order, and the half-damped probe energy measures $\lvert\zeta\rvert^2$ on
    the critical line (`receiverBounded_logPowerCosine_iff_all`, `tendsto_probeEnergy_half_div_log`).
12. **Fermi observability.** Dyadic schedules are injective exactly when at most one slot is
    missing, and the optimal physical inverse constant grows like $(4/\pi^2)(\log_2N)^2$
    (`not_fermiScheduleInjective_of_two_missing_levels`, `fermiPhysicalInverseConstant_logb_limit`).

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
| Ramanujan amplitudes, translation statistics or pronic mode masses decide the receiver | Only above half damping. For every $\varepsilon\le1/2$ every real character gives an unconditional parity pair; amplitude invariance of boundedness holds iff $\varepsilon>1/2$. |
| The barrier is "no bound $E_T\le F(\lvert W_c\rvert)$" | That follows from a single divergent weight. The parity content is that the predicate "paid" is not a function of the amplitudes, which needs a pair. |
| Adding more sign-blind observables narrows the gap | Blindness is closed under post-processing, pairing and families of arbitrary cardinality; the floor in the damping unit stays $\tfrac12$ for every amplitude-derived reading. |
| One admissible damping bounds the width | It does not: a single admissible damping only translates zeros along $\rho,\rho-\varepsilon,\rho-2\varepsilon,\dots$. The width is the infimum of the derived set of the admissible dampings, exactly $\Theta-\tfrac12$. |
| Higher-degree translated moments see the parity of squarefree rows | Cubic moments pin odd-modulus signs, but the even flip is invisible at every degree and can break the receiver (the Fermi pair). |
| Finitely many flipped primes make a parity pair | Local factors with $\lvert a\rvert<\sqrt p$ never change the receiver class, nor do flips on prime sets of convergent $\sum p^{-1/2-\varepsilon}$; a pair needs a prime set of divergent critical-line mass. |
| Higher prime powers are invisible to the receiver | True for $\mu$-pretentious weights; for $1$-pretentious weights they enter through the local factor $L_p$ at the pole. |
| A separating observable bounds the receiver | The logarithmic moments separate every pair and bound nothing; separation is qualitative and carries no exponent. |
| Divergence proofs need a nonnegative weight | The pole law proves divergence of sign-changing convolutions $k\star q$ through the Mellin pairing at $\sigma=1-\varepsilon+\delta$. |
| The density of flipped primes decides the receiver of a sign pattern | Only on symmetric residue patterns (quarter law). Oscillating prime patterns with the same prime signs and the same prime mean can be paid and unpaid; the receiver reads the size of the Dirichlet series beside the line at every height. |
| Below half damping a flipped density near $1/2$ is enough | A paid weight needs logarithmic prime mean in $\{0,-1\}$ exactly, at every height (integer-order obstruction); subgroup flips of index $k\ge3$ are unpaid at every $\varepsilon<1/2$. |
| Payment of a probe is an estimate for Möbius | Probe theorems evaluate weights whose series are known in terms of $\zeta$; the Möbius series $1/\zeta(s+\varepsilon)$ is the unknown. |
| Real-axis abscissa blowup or Lipschitz tests detect unpaid oscillating probes $d^{-\varepsilon}\cos(t\log d)$ ($t\ne0$) | For $t\ne0$, $\sum_d c_{\varepsilon,t}(d)d^{-\sigma}=\operatorname{Re}\zeta((\sigma+\varepsilon)-it)$ converges to $\operatorname{Re}\zeta(1-it)$ and is Lipschitz at $\sigma=1-\varepsilon$ whether $c_{\varepsilon,t}$ is paid or unpaid; the pole sits at $1-\varepsilon\pm it$. |

**Lean conventions.** Everything lives in
`GaloisForLFunctions.TransHorizonIncidenceMechanics`. Sieve objects are imported
from the Bézout–valuation and bi-scale theories, the Markov operator, prime
chains, theta kernel and the Haar moments of $\tau_\varepsilon$ from the RH tower.
Capstones take data only: a weight `c : ℕ → ℝ`, a horizon `N`, a prefix `M`, a
damping `ε`, a schedule `S`, with ranges encoded by natural offsets such as
`n + 1` or by the predicate `IsTransHorizonRough`. No positivity, cancellation
or zero-location hypothesis appears; RH occurs only as the conclusion of an
implication or inside an equivalence. Universal statements over all weights are
stated as `∀ c`, and "for all squarefree-supported weights" as an explicit
support premise on `c`. Cofinal statements are nested eventual quantifiers,
never hidden thresholds. Every `tsum` is preceded by a summability theorem.
Counterexamples are symbolic families indexed by a prime `p`, never evaluated
instances. Prime-number-theorem inputs enter only through the proved corpus
forms ($\mathfrak m(x)\to0$, $M(x)=o(x)$, prime counts in octaves). Classical
constituents are marked `[Known]` or `[Corollary]` in docstrings, new
formulations `[New formulation]`; no heartbeat settings are raised.

---

## 6. Questions the theory answers and the tools it builds

### 6.1 Questions

1. **What can a divisor sieve of horizon $N$ see far beyond its horizon, and where does it lose
   control?** Exactly located: the unit envelope to ratio five, the global defect sign at large
   horizons, deterministic successor dynamics to horizon two, schedule conditioning
   $(4/\pi^2)(\log_2N)^2$.
2. **Which observations retain the signs the receiver needs?** Above half damping none are needed;
   at and below half damping no sign-blind datum suffices, cubic moments read odd-modulus signs
   but not the even flip, first pronic moments read prime powers, the logarithmic hierarchy
   separates every pair — and separation bounds nothing.
3. **What does the receiver read in a weight?** The analytic continuation and the size of the
   weight's own Dirichlet series beside the line $\Re s=1-\varepsilon$: poles on or right of
   $\Re s=1/2$ are fatal, zeros never are; at half damping a boundary energy; on probes the zero
   divisor of $\zeta$ with multiplicities.
4. **Which arithmetic class pays the receiver below half damping?** Critical Wiener perturbations
   at their pole hyperplane, $\chi$-pretentious and $\mu$-pretentious weights; nonnegative
   $1$-pretentious weights never; multiplicative sign patterns only at the integer prime means
   $0$ and $-1$.
5. **The question it exists for:** one unconditional bound on the actual Möbius receiver at one fixed
   $\varepsilon<1/2$, read from signed data, and cofinally as $\varepsilon\downarrow0$.

### 6.2 Tools

Built and reusable:

- *Complementary-divisor normal forms* and the four-channel tail formula above the horizon.
- *Dirichlet polarization with boundary squares retained*, radical-state transport and integer
  jump energy.
- *Ramanujan diagonalization* of period laws, white-noise and singular-series correlations.
- *Buchstab horizon calculus*: band steps, class averages and the energy profile.
- *Fermi trace inversion* with exact schedule conditioning.
- *The receiver calculus*: dyadic masses for positive weights, the critical Wiener algebra, the
  pole law, the boundary-energy identity, the general pole law, the partial-pole-sum criterion.
- *Parity pairs* as the sharp test of sign-blindness, and the logarithmic moment hierarchy as the
  complete separating invariant.
- *Euler-product phase diagrams* for multiplicative weights, through $\zeta$ and Dirichlet
  $L$-functions beside the line, with no zero-free region for $L$ required.
- *Probe spectroscopy*: oscillating log-power probes as a calibrated instrument for the zero
  divisor.

To be built:

- a signed estimate on the actual Möbius receiver at one fixed $\varepsilon<1/2$, with its exact loss;
- a cross-lobe estimate for the odd sector;
- least-squares conditioning of multi-gap and non-dyadic Fermi schedules;
- the structure of the Möbius row that excludes the dipole obstruction below half damping.

---

## 7. Open problems

### 7.1 The complete signed trans-horizon energy

The PM receiver needs $\sup_T\sum_{n\le T}I_\varepsilon(n)^2/(n(n+1))<\infty$ at arbitrarily small
fixed $\varepsilon$. The receiver row is understood on the period torus: it observes the complete
damped divisor function, its renormalized defect is eventually nonpositive at every prefix, its
period variance is a partial Parseval sum bounded by $V(\varepsilon)$ uniformly in the horizon, and its
primitive energy diverges for $\varepsilon\le1/2$, so complete-period averages cannot supply the bound.
Missing is the pronic-weighted interior energy below the first period: cancellation in the
coefficient-weighted energy with means, endpoints, mixed covariance and growing cutoffs retained,
at fixed $\varepsilon\in(0,1/2)$, where the small arguments carry the weight $1/(n(n+1))$ and the
Ramanujan truncation error $Q^{-\varepsilon}\tau(n)$ is not small. The actual-source estimates of
§3.20 admit only a horizon-dependent band shrinking to $\varepsilon=1/2$.

### 7.2 Small horizons

The long-window law is explicit and quadratic at every horizon $N\ge2$ (threshold $10N^2+8N$ for
Möbius), but the polynomial-window sign is proved only eventually in the horizon, through prime
counts in octaves. Whether the renormalized defect is nonpositive at every prefix for every
horizon $N\ge2$, and the exact constant of the window observability law (its order $N^2$ is
exact), are open.

### 7.3 Buchstab calculus

The band averages $A(1),\dots,A(4)$ are negative, the profile values $P(1),\dots,P(4)$ are known,
and the cofinal profile $P(B)$ is monotone (`monotone_cofinalMobiusQuadraticProfile`, in
Bézout–Valuation Incidence). Open: the sign of $A(B)$ for every band, concavity of the profile, and
the classification of the squarefree cores with negative slope in each band. The damped crossover
is located to second order with an additive window $\pm\varepsilon$; the sign of the slope for prime
horizons inside that window, $\lvert\log p-\Lambda(\varepsilon)\rvert<\varepsilon$, is open, as is every
term of $V(\varepsilon)$ and $R(\varepsilon)$ beyond the second order.

### 7.4 The odd sector

After exact collar cancellation the remaining obligation is an independently quantified bound on
the low-prime diagonal potential, or an actual-source nodal estimate paying the primitive
ground-projection defect. The cosh/sinh ratio cannot be made $\le1$ on compact profiles; the minimal
local correction must be paid by jump energy, or the source class restricted so that the
confinement law suffices. The coordinates are canonical: the polar risk is rank one, read by the
single shift-independent moment $\langle q,\tanh_L\rangle$ with
$\mathrm{sourceEnergy}=\mathrm{weilForm}+2\langle q,\tanh_L\rangle^2$ exactly, so the question is
nonnegativity of $\mathrm{sourceEnergy}$ on the kernel of one functional, and the shift cannot be
tuned. Two unconditional lobe inequalities are available — the cross-lobe Rayleigh excess at positive
eigenvalue and the chiral drift bound on both lobes — and neither closes the four-term excess. A new
mechanism must add a *cross-lobe* estimate: both tightenings are lobe-local, and the obstruction is
the pairing between the lobes.

### 7.5 Fermi–Nyman

Origin and bulk tightness on one explicit approximation sequence. The observation theory of dyadic
schedules is complete for one gap; the conditioning of schedules with two or more gaps, which are not
injective, is a least-squares question — which rows are recovered and at what price. Non-dyadic
schedules (levels of an odd prime) and weighted traces have no classification.

### 7.6 Signs below half damping

Below half damping the receiver of a weight is not a function of its sign-blind data, every known
pair is decided by a pole at $s=1-\varepsilon$, and the damping threshold of the Möbius receiver is the
zero width, so RH is admission along a positive damping sequence tending to $0$. A single admitted
damping is weaker: the zero-width dictionary uses a boundary at which admitted dampings accumulate.
What is missing is one unconditional bound at one fixed $\varepsilon<\tfrac12$, read from signed data by
the closure of the blind class. The smooth-power classification holds for all critical Wiener
kernels at strict sub-half damping, necessity extends to kernels summable only at the abscissa, and
at half damping the partial-pole-sum energy is the exact criterion (§3.17). Open: criteria for
individual kernels beyond these classes, and quantitative estimates from signed logarithmic data
that control the complete boundary energy.

### 7.7 Beyond the solved phase diagrams

The constant-sign plane, symmetric residue flips, subgroup flips and single-frequency oscillating
patterns are decided. For non-symmetric residue flips with $\rho>1/4$ the nonprincipal coefficients
are complex; the route is the bound $-\Re(s_\chi\sum_p\chi(p)p^{-w})\le\lvert s_\chi\rvert(\lvert\ell_\chi(w)\rvert+S)$
by the Euler logarithm $\ell_\chi$ of $L(\cdot,\chi)$, which grows like $\log\log\lvert\Im w\rvert$
beside the line and leaves the line-energy argument intact. Open beyond residue patterns: patterns
mixing several frequencies or amplitudes varying with the prime, and a classification of general
multiplicative spectra. The phase diagrams fix what such a classification
must read: the Dirichlet series beside the line at every height, never only the flipped density or
the real-axis prime mean.

### 7.8 The dipole obstruction for the Möbius row

The signed horizon-limit question is settled for the damped classes: bounded rows pay the limit, a
paid limit need not have uniformly paid rows below one half, and on the convolution class the
obstruction never occurs. Open: which additional structure of the Möbius row excludes the dipole
obstruction.

### 7.9 Research topics

1. **From separation to a bound.** The parity pairs exist at every damping $\varepsilon\le1/2$ and the
   observables that separate them are classified: first-order data at prime powers, the logarithmic
   moment hierarchy, the pole value $K(1-\varepsilon)$ and its Taylor coefficients (§3.16). Find an
   estimate that turns one of them into a bound on the actual Möbius receiver at one fixed
   $\varepsilon<1/2$, with its exact loss; this is the Type-II input the shared target needs.
2. **The complete signed trans-horizon energy** at fixed small damping, with means, endpoints,
   mixed covariance and growing cutoffs retained.
3. **The odd-sector low-prime diagonal potential**, matched term by term with the unpaid axis
   intervals and the nine moduli of Arithmetic Incidence Positivity: one obstruction read from the
   sieve side and from the pair side.
4. **Selectivity of the transfer laws.** Which conservation and dissipation laws hold for a
   Beurling system or the shifted pair, and which are specific to $\mathbb N$.

---

## 8. Working in the theory

Fix the weight class first: arbitrary real weights, squarefree-supported
weights, nonnegative weights, the literal Möbius weight, the damped family, or
the cofactor row. Many laws are universal in the weight; the sharp ones are not,
and the obstruction examples are usually nonnegative squarefree weights with
$c(1)=1$. Say which limit is taken and in which order: the cofinal limit in the
horizon and the limit $\varepsilon\to0$ do not commute, and a statement at fixed
damping is not a statement about Möbius. State every bound with its range of
$k$, $M$ and $N$ and say which band, which ratio and which regime (polynomial
window or long window) it lives in. Pass every sign claim through the Dirichlet
polarization and name the boundary squares. Pass every period statement through
the Selberg coordinates and the Ramanujan lag weights. Transport certificates
along radical fibres and positive powers rather than reproving them at large
scale. When a universal law fails, locate the first failure exactly and prove
the classification; the positive survivor is the theorem. Search the corpus,
including the other programmes' folders, before building: Buchstab steps,
Ramanujan lag coefficients, the chain renormalization law, the window Poincaré
law, the Haar moments of $\tau_\varepsilon$, Montgomery–Vaughan interval bounds,
the Gutzmer and Hardy path inequalities, GCD Gram kernels, the theta drop bounds
and the Lévy density are all present. Comments in Lean are mathematics; status,
dates and logs belong on the pipeline cards.
