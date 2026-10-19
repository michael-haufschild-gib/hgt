# Bézout–Valuation Incidence

**Bézout–Valuation Incidence** (BVI) is the finite-horizon theory of truncated divisor sums.
Its objects are rows of divisor weights $c(1),\dots,c(N)$, the arithmetic signals
$s_{N,c}(k)=\sum_{d\le N,\;d\mid k}c(d)$ they generate, and the prefix discrepancies of those
signals on windows whose length is polynomial in the cutoff $N$. Its method is exact arithmetic:
the coprimality of consecutive integers (Bézout), the prime-power structure of moduli
(valuation), and the divisibility pattern between moduli and positions (incidence). Its purpose
is to determine, without averaging over the exponentially long period
$\operatorname{lcm}(1,\dots,N)$, which signed cancellations of Möbius-type sources are forced by
arithmetic alone, and to isolate exactly the one inequality that is not.

Everything in the theory is unconditional. The Riemann Hypothesis appears only as the
conclusion of criteria whose premise is one explicit finite inequality; the theory never
asserts that premise.

---

## 1. Why

### 1.1 The object and the regime

Fix a cutoff $N$ and a row $c:\{1,\dots,N\}\to\mathbb R$. The truncated divisor sum
$s_{N,c}(k)$ is periodic with period $L_N=\operatorname{lcm}(1,\dots,N)=e^{\psi(N)}$ and has the
finite Ramanujan expansion
$$
s_{N,c}(k)=\sum_{q=1}^{N}Y_{N,c}(q)\,c_q(k),\qquad
Y_{N,c}(q)=\sum_{\substack{d\le N\\ q\mid d}}\frac{c(d)}{d},
$$
where $c_q$ is Ramanujan's sum. Distinct Ramanujan sums are orthogonal over a full period,
and classical sieve theory (Selberg, Ramanujan–Fourier analysis) works on that period or in the
limit $x\to\infty$ with $N$ fixed.

Every question about primes asks something else: what the signal does on a window
$M\le N^{A}$, where the period is unreachable. There, three things fail at once.

1. **Drift and incidence mix.** The prefix discrepancy
   $$
   L_N(M,c)=\sum_{m=1}^{M}s_{N,c}(m)-M\sum_{d=1}^{N}\frac{c(d)}{d}
   =\sum_{d=1}^{N}c(d)\Bigl(\Bigl\lfloor\frac Md\Bigr\rfloor-\frac Md\Bigr)
   =-\sum_{d=1}^{N}c(d)\Bigl\{\frac Md\Bigr\}
   $$
   receives from every modulus $d>M$ the deterministic drift $-Mc(d)/d$ before that modulus
   has produced a single divisibility event.
2. **Shift and cutoff do not commute.** Translation $n\mapsto n+1$ does not preserve
   $\operatorname{span}\{\mathbf 1_{d\mid n}:d\le N\}$. The successor correlation
   $\sum_{k\le M}s(k)s(k+1)$ is not a function of the row through the period inner product,
   and on short windows its endpoint terms are of the same size as its main term.
3. **Lags and depths couple.** Correlations across a $k$-tuple $(n+h_1,\dots,n+h_k)$, or
   across the number of prime factors $\omega(q)$ of the mode, are governed by exact finite
   factorizations, not by mode-by-mode limits.

### 1.2 Why Bézout, why valuation, why incidence

The three words name the three inputs that are specific to the integers.

**Bézout.** $\gcd(n,n+1)=1$. Hence a divisor of $n$ and a divisor of $n+1$ are coprime, their
product runs bijectively over the divisors of $n(n+1)$, and $\Lambda(n(n+1))=0$ for $n\ge 2$.
For coprime scales $p,q$ the equation $pa-qb=1$ has a least positive solution, and the distance
between a divisibility event of the modulus $pr$ and one of $qr$ is governed by $pa-qb=h$.
None of this holds in a Beurling generalized number system. Such systems satisfy every purely
multiplicative identity (Möbius inversion, Euler products, divisor lattices, Buchstab splits)
and can carry zeros of their zeta function off the critical line. A mechanism that sees the
Riemann Hypothesis must therefore use Bézout structure somewhere; this is the test the theory
applies to each of its own tools.

**Valuation.** What a translation by $h$ can see of a mode $q$ is decided by $p$-adic
exponents: the mode survives the compression of the lag $h$ exactly when
$q/\operatorname{rad}(q)\mid h$. The power-damped Möbius divisor coefficient depends on $n$ only
through its radical. Valuation governs visibility, revival at the clock, radical invariance,
and the $2$-adic and $3$-adic ceilings on consecutive products.

**Incidence.** The $0$–$1$ matrix $\mathbf 1_{d\mid n}$ between moduli $d\le N$ and positions
$n$ in a window, together with its sawtooth geometry $\{n/d\}$. Every quantity in the theory is
a bilinear form in the row against a piece of this matrix, and every mechanism is an exact
rearrangement of that bilinear form.

### 1.3 Where the theory points

The square-root barrier in prime counting (Wall 1) is the statement that a Möbius or prime sum
up to $x$ has error $x^{1/2+\varepsilon}$; it is equivalent to RH. In the coordinates of this
theory it takes the following form. For a damping $\varepsilon>0$ put
$$
\tau_\varepsilon(n)=\sum_{d\mid n}\mu(d)\,d^{-\varepsilon}=\prod_{p\mid n}\bigl(1-p^{-\varepsilon}\bigr),
\qquad \alpha_\varepsilon=\frac{1}{\zeta(1+\varepsilon)},
\qquad A_\varepsilon(n)=\sum_{j=1}^{n}\bigl(\tau_\varepsilon(j)-\alpha_\varepsilon\bigr),
$$
$$
E_T(\varepsilon)=\sum_{n=1}^{T}\frac{A_\varepsilon(n)^2}{n(n+1)} .
$$
If for every $\delta>0$ there is some $\varepsilon\in(0,\delta)$ with $\sup_T E_T(\varepsilon)<\infty$,
then RH holds. The bound is known for every $\varepsilon\ge 1/2$ and unknown for every
$\varepsilon<1/2$; a horizon-uniform bound at a single fixed $\varepsilon<1/2$ is already a
zero-free half-plane statement. The energy $E_T(\varepsilon)$ is the pronic-weighted prefix
energy of the truncated divisor sum with row $c_\varepsilon(d)=\mu(d)d^{-\varepsilon}$, observed
below its own horizon. BVI is the exact finite arithmetic of this energy: the identities that
decompose it, the parts that are bounded or have explicit logarithmic drift, and the single
remaining obligation (§5).

---

## 2. What: objects and language

### 2.1 Rows, responses, and Selberg coordinates

A row $c$ has three coordinate systems.

- **Raw weights** $c(d)$, $1\le d\le N$.
- **Responses** $s_{N,c}(k)=\sum_{d\le N,\,d\mid k}c(d)$, the signal at position $k$.
- **Selberg multiples coordinates** $Y_{N,c}(e)=\sum_{e\mid d\le N}c(d)/d$, $1\le e\le N$.

Raw and Selberg coordinates are related by a triangular bijection; the inverse is finite
Ramanujan inversion, $c(d)=d\sum_{m\le N/d}\mu(m)\,a(dm)$, which realizes any prescribed
$Y$ on $[1,N]$. The coordinate $Y_{N,c}(1)=\mathcal H_N(c)=\sum_{d\le N}c(d)/d$ is the
**harmonic mode**, the mean of the response over a period; the subspace $\mathcal H_N(c)=0$
is written $\ker P$. The period mean square of the centered response is
$\sum_{e\ge 2}\varphi(e)\,Y_{N,c}(e)^2$, and totient-normalized Selberg coordinates are an
isometry from rows to $\ell^2$.

The first discipline of the theory: say in which coordinates a statement lives, and whether it
concerns the period or a prefix. A statement about the period mean square says nothing about a
prefix of length $N$.

### 2.2 Horizons

For the literal Möbius row $c=\mu$ the response is explicit on each band.

| band | response $s_{N,\mu}(k)$ |
|---|---|
| sub-horizon $1\le k\le N$ | $\mathbf 1_{k=1}$ (Möbius inversion) |
| first octave $N<k\le 2N$ | $-\mu(k)$ |
| second octave $2N<k\le 3N$ | $-\mu(k)-\mathbf 1_{2\mid k}\,\mu(k/2)$; zero when $v_2(k)=1$, equal to $\mu(u)$ at $k=4u$ |
| band $k\le (B+1)N$ | minus a sum of at most $B$ complementary quotients, so $\lvert s_{N,\mu}(k)\rvert\le B$ |
| period $L_N$ | exact Ramanujan orthogonality |

The **multiplicative state** of a position is $\sigma_N(k)=\operatorname{lcm}\{d\le N:d\mid k\}$,
its **radical state** is $\gcd(k,N\#)$. Two positions with the same state are indistinguishable
by every row, respectively by every squarefree-supported row.

### 2.3 Discrepancy, sawtooth, and the interior

The **centered sawtooth** of modulus $d$ is $\tilde B_1(d,n)=\{n/d\}-\frac{d-1}{2d}$, with step law
$\tilde B_1(d,n+1)-\tilde B_1(d,n)=\frac1d-\mathbf 1_{d\mid n+1}$. The **weighted centered sawtooth
sum** $W_{N,c}(n)=-\sum_{d\le N}c(d)\tilde B_1(d,n)$ therefore has forward difference
$$
W_{N,c}(n+1)-W_{N,c}(n)=s_{N,c}(n+1)-Y_{N,c}(1),
$$
so on $\ker P$ it is the primitive of the response, and $L_N(M,c)$ is $W_{N,c}(M)$ up to the
constant $W_{N,c}(0)$. Across the step $n\mapsto n+1$ the moduli split three ways:

- **active at $n$** ($d\mid n$): the sawtooth sits at its post-jump peak $+\frac{d-1}{2d}$;
- **active at $n+1$** ($d\mid n+1$): the sawtooth sits at its pre-jump trough $-\frac{d-1}{2d}$
  and flips sign at the step;
- **interior** ($d\nmid n$ and $d\nmid n+1$).

By Bézout no modulus $d\ge 2$ is active at both ends. The active parts have the closed forms
$\pm\frac12\bigl(s_{N,c}(m)-s_{N,c/d}(m)\bigr)$ with $(c/d)(d)=c(d)/d$; for the power-damped row
this is $\pm\frac12(\tau_\varepsilon(m)-\tau_{1+\varepsilon}(m))$, independent of the cutoff. The
**Bézout interior sawtooth sum** collects the interior moduli, and its horizon-free form for the
power-damped row is the **interior prefix** $I_\varepsilon(n)$. Deeper **Bézout shells**
$\{n+1-r,\,n+r\}$ of width $2r-1$ carry the weight $c(d)-(2r-1)c(d)/d$ and vanish at the odd
midpoint modulus $d=2r-1$.

### 2.4 The quadratic forms of a row

All natural second moments of a row are diagonal in the same Selberg coordinates. With
$Y(e)=Y_{N,c}(e)$:

| form | modal weight at $e\ge 2$ | meaning |
|---|---|---|
| Selberg variance $V$ | $\varphi(e)$ | period variance of the response |
| Bézout successor covariance $C$ | $\mu(e)$ | period covariance of $s(k)$ and $s(k+1)$ |
| successor reserve | $\varphi(e)-\mu(e)$ | half the period mean square of the gradient $s(k+1)-s(k)$ |
| one-step phase loss | $\varphi(e)-\mu(e)^2/\varphi(e)$ | variance not predictable from the present |
| primitive energy $\times 12$ | $J_2(e)$ | period mean square of $W_{N,c}$ |
| lag-$h$ covariance | $\varphi(e)\lambda_e(h)$, $\lambda_e(h)=\dfrac{\mu(e/g)}{\varphi(e/g)}$, $g=\gcd(e,h)$ | period covariance at lag $h$ |
| consecutive triple $(0,1,2)$ variance | $3\varphi(e)+4\mu(e)+2\lambda_e(2)\varphi(e)$ | variance of $s(k)+s(k+1)+s(k+2)$ |

The harmonic mode $e=1$ cancels between the Selberg and Bézout forms, $\varphi(1)-\mu(1)=0$,
even off $\ker P$. The successor covariance is the period main term of the finite successor
correlation; its diagonal weight $\mu(e)$ separates $4$ from $6$ where the totient does not
($\varphi(4)=\varphi(6)=2$, $\mu(4)=0\ne 1=\mu(6)$).

### 2.5 Incidence objects

- **Successor incidence count** $\mathcal I(M;d_1,d_2)=\#\{k\le M:d_1\mid k,\ d_2\mid k+1\}$. It is
  zero unless $\gcd(d_1,d_2)=1$, and for coprime moduli every block of $d_1d_2$ consecutive
  integers contains exactly one hit, so $\lfloor M/d_1d_2\rfloor\le\mathcal I\le\lfloor M/d_1d_2\rfloor+1$.
- **Bézout sawtooth defect** $\delta(M;d_1,d_2)=\mathcal I(M;d_1,d_2)-M/d_1d_2\in[-1,1]$ for
  coprime moduli, zero otherwise and zero at common returns.
- **Combined and renormalized defects.** The successor correlation is
  $\sum_{k\le M}s(k)s(k+1)=M\,Q_{\mathrm{Bez}}(c)+\sum c(d_1)c(d_2)\delta(M;d_1,d_2)$ with
  $Q_{\mathrm{Bez}}=\sum_{e\ge 1}\mu(e)Y(e)^2$. The renormalized defect is
  $R_N(M;c)=\sum_{k\le M}s(k)\bigl(s(k+1)-s(k)\bigr)$; its short-window version lives on
  $[M_0+1,M_0+M]$.
- **Prefix $L^2$ energy** $\mathcal E_N(M;c)=\sum_{k\le M}s_{N,c}(k)^2$.
- **Tuple residue occupancy** $\nu_H(p,r)=\#\{i:h_i\equiv r\ (p)\}$ and the prime structure
  factor $S_p(H)=p\sum_r\nu_H(p,r)^2-k^2$ of a $k$-tuple $H$.

### 2.6 Valuation objects

- **Visibility clock** $\tau_{\mathrm{vis}}(q)=q/\operatorname{rad}(q)$, the least lag at which
  the mode $q$ is visible to compressed translation.
- **Lag multiplier trichotomy** at a prime power: $\lambda_{p^{a+1}}(h)=1$ if $p^{a+1}\mid h$,
  $=-1/(p-1)$ if $p^a\mid h$ but $p^{a+1}\nmid h$, $=0$ otherwise.
- **GCD–LCM modular functions**: $F(1)=1$ and $F(j)F(k)=F(\operatorname{lcm}(j,k))\,F(\gcd(j,k))$.
  Every function $n\mapsto\prod_{p\mid n}(1-w(p))$ is of this kind; it is radical-invariant,
  divisor-absorbing ($d\mid m\Rightarrow F(dm)=F(m)$), and satisfies $F(k)F(k+1)=F(k(k+1))$.
  The cases $w(p)=p^{-\varepsilon}$ and $w(p)=1/p$ are $\tau_\varepsilon$ and $\varphi(n)/n$.
- **Shifted exponent**: $\tau_{1+\varepsilon}(n)=\sum_{d\mid n}\mu(d)d^{-1-\varepsilon}$, equal to
  $c_\varepsilon(d)/d$ summed over $d\mid n$, and to $\varphi(n)/n$ at $\varepsilon=0$.

### 2.7 The pronic measure and the non-periodic Gram

The **pronic measure** puts mass $\frac{1}{M(M+1)}$ on each $M\ge 1$; it has total mass $1$ and
tail mass $\frac1{H+1}$ beyond $H$. It replaces period averaging. The **Ramanujan primitive**
$R_e(M)=\sum_{n\le M}c_e(n)$ has period $e$ and mean $-\varphi(e)/2$, with
$\operatorname{Re}R_p(M)=-(M\bmod p)$ at primes, and
$$
L_N(M,c)=\sum_{e=2}^{N}\operatorname{Re}R_e(M)\,Y_{N,c}(e).
$$
Pronic averaging turns the primitives into the von Mangoldt function:
$$
\sum_{M\ge 1}\frac{\operatorname{Re}R_e(M)}{M(M+1)}=-\Lambda(e),\qquad
\sum_{M\ge 1}\frac{L_N(M,c)}{M(M+1)}=-\sum_{e=2}^{N}\Lambda(e)\,Y_{N,c}(e).
$$
The **pronic Gram matrix** $\mathcal G(e_1,e_2)=\sum_M R_{e_1}(M)R_{e_2}(M)/(M(M+1))$ represents
the pronic-weighted squared discrepancy. Its **energy-centered** form uses
$F^{\mathrm{ec}}_e=R_e+\Lambda(e)$, has pronic mean zero, and satisfies
$\mathcal G=\Lambda\Lambda^{\top}+\mathcal G^{\mathrm{ec}}$ with $\mathcal G^{\mathrm{ec}}\succeq 0$;
its **mean-centered** form uses $R_e+\varphi(e)/2$ and differs from the energy-centered one by
the rank-one matrix of $\varphi(e)/2-\Lambda(e)$.

In Hilbert space the primitive of modulus $r$ is a step vector $f_r\in L^2((1,\infty),dx/x^2)$
with $\langle f_r,f_s\rangle=\mathcal G(r,s)$. Dilation $D_c$ acts unitarily, the **dilation
profile** is $\Phi_r(c)=\langle f_r,D_cf_r\rangle$, and prime insertion is the exact law
$f_{pr}=\sqrt p\,D_{1/p}f_r-f_r$ for $p\nmid r$. The profile is also an integer object: the
pairing of the two jump streams of $pr$ and $qr$ on integer cells, whose jump gaps are the
solutions of $pa-qb=h$.

### 2.8 The power-damped source and the Fermi cells

For the row $c_\varepsilon(d)=\mu(d)d^{-\varepsilon}$ the response below the horizon is
$\tau_\varepsilon(n)$, the centered coefficient is $\tilde\tau_\varepsilon=\tau_\varepsilon-\alpha_\varepsilon$,
the centered prefix is $A_\varepsilon$, and the discrete energy is $E_T(\varepsilon)$ of §1.3. The
horizon-free interior prefix $I_\varepsilon(n)$ and the interior energy
$E^{\mathrm{int}}_T(\varepsilon)=\sum_{n\le T}I_\varepsilon(n)^2/(n(n+1))$ are its Bézout-interior
counterparts.

The **Fermi–Nyman cells** $I_n=(\frac1{n+1},\frac1n]$ have Lebesgue measure $\frac1{n(n+1)}$: the
pronic measure is Lebesgue measure on $(0,1]$ read through the cells. The cell response of a row
is $2\sum_{k\le n/2}s_{N,c}(k)-\sum_{k\le n}s_{N,c}(k)$, and the power-damped Fermi–Nyman source
of the Mellin picture equals minus this response on each sub-horizon cell. In this way the
$L^2(0,1]$ energy of the analytic source and the pronic energy of the arithmetic prefix are one
quantity.

### 2.9 Glossary

| object | formula | Lean |
|---|---|---|
| response | $s_{N,c}(k)$ | `sieveSeq N c k` |
| harmonic mode | $\mathcal H_N(c)=Y_{N,c}(1)$ | `finiteHarmonicSum N c` |
| Selberg coordinate | $Y_{N,c}(e)$ | `selbergMultiplesCoord N c e` |
| Ramanujan inverse | row realizing prescribed $Y$ | `pmRamanujanResidueCoeff` |
| variance, successor covariance, reserve | §2.4 | `sieveVariance`, `sieveSuccessorCovariance`, `sieveSuccessorReserve` |
| phase loss, primitive energy | §2.4 | `successorPhaseLoss`, `sievePrimitiveEnergy` |
| lag multiplier, visibility clock | $\lambda_q(h)$, $q/\operatorname{rad}q$ | `sieveLagMultiplier`, `lagVisibilityClock` |
| prefix discrepancy | $L_N(M,c)$ | `sievePrefixDiscrepancy N M c` |
| centered sawtooth, its weighted sum | $\tilde B_1(d,n)$, $W_{N,c}(n)$ | `centeredDiscreteSawtooth`, `weightedCenteredSawtoothSum` |
| interior sawtooth sum, interior prefix | §2.3 | `bezoutInteriorSawtoothSum`, `pmBezoutInteriorPrefix` |
| successor incidence count, sawtooth defect | §2.5 | `bezoutIncidenceCount`, `bezoutSawtoothDefect` |
| renormalized defect | $R_N(M;c)$ | `sieveRenormalizedPrefixDefect` |
| pronic sequence | $n(n+1)$ | `pronicSeq` |
| power-damped row and coefficient | $c_\varepsilon$, $\tau_\varepsilon$ | `pmPowerDampedRealWeight`, `pmPowerDampedDivisorCoeff` |
| centered prefix, discrete energy | $A_\varepsilon$, $E_T(\varepsilon)$ | `pmPowerDampedCenteredDivisorPrefix`, `pmPowerDampedDivisorDiscreteEnergy` |
| interior energy | $E^{\mathrm{int}}_T(\varepsilon)$ | `pmBezoutInteriorPronicEnergy` |
| Ramanujan primitive, pronic Gram | $R_e(M)$, $\mathcal G$, $\mathcal G^{\mathrm{ec}}$ | `pmRamanujanPrimitive`, `pmRamanujanPrimitiveGram`, `pmRamanujanEnergyCenteredGram` |
| dilation profile | $\Phi_r(c)$ | `pmRamanujanDilationProfile` |
| least Bézout seed | least $(a,b)$ with $pa=qb+1$ | `leastSuccessorSeed p q` |
| Fermi cell response | §2.8 | `fermiCellResponse` |
| GCD–LCM modular class | §2.6 | `IsGcdLcmModular`, `radicalPrimeProd` |

---

## 3. How: the mechanisms

The mechanisms are listed in logical order. Each is an exact identity or a sharp finite
inequality; the asymptotic statements of §3.7 and §3.9 all rest on one of them.

### 3.1 Bézout splitting and the prime-power exclusion

Because $\gcd(k,k+1)=1$, the map $(d_1,d_2)\mapsto d_1d_2$ is a bijection from pairs with
$d_1\mid k$, $d_2\mid k+1$, $d_i\le N$ onto the divisors of $k(k+1)$ as soon as $N\ge k+1$, and the
factors are recovered as $d_1=\gcd(n,k)$, $d_2=\gcd(n,k+1)$. A product of two coprime integers
$\ge 2$ is never a prime power, so the centered successor product
$\tilde s(k)\tilde s(k+1)$ contains no prime-power term and $\Lambda(k(k+1))=0$. The same
coprimality gives the **pronic multiplicativity law** $\tau_\varepsilon(k)\tau_\varepsilon(k+1)=\tau_\varepsilon(k(k+1))$,
and since $k(k+1)$ is even, the uniform **$2$-adic ceiling**
$\tau_\varepsilon(k)\tau_\varepsilon(k+1)\le 1-2^{-\varepsilon}$, although each factor tends to $1$ along primes.

This is also where $\log 4$ and $\log 6$ separate: the mixed multiplicative difference
$F(d_1d_2m)-F(d_1m)-F(d_2m)+F(m)$ annihilates $\log$, while the one-axis difference
$F(dm)-F(m)$ does not; a node with two distinct primes is invisible to the former, a prime
power is visible to the latter.

### 3.2 Simultaneous diagonalization and the finite cones

The coprime successor form $Q_{\mathrm{Bez}}(c)=\sum_{\gcd(d_1,d_2)=1}\frac{c(d_1)c(d_2)}{d_1d_2}$
and the Selberg form $Q_{\mathrm{Sel}}(c)=\sum_{e}\varphi(e)Y(e)^2$ are diagonal in the same
coordinates, with weights $\mu(e)$ and $\varphi(e)$. Since $2\mu(e)\le\varphi(e)$ for $e\ge 2$
with equality only at $e=6$, the **half-decorrelation law** $2Q_{\mathrm{Bez}}\le Q_{\mathrm{Sel}}$
holds on $\ker P$. Writing $H=\mathcal H_N(c)$, the universal bounds are
$$
-V\le C\le \tfrac12 V,\qquad V\le 2\bigl(Q_{\mathrm{Sel}}-Q_{\mathrm{Bez}}\bigr)\le 4V,
$$
with $C=Q_{\mathrm{Bez}}-H^2$. For $N\ge 6$ the feasible triples $(H,Q_{\mathrm{Sel}},Q_{\mathrm{Bez}})$
are exactly those with $2H^2\le Q_{\mathrm{Sel}}+Q_{\mathrm{Bez}}$ and $2Q_{\mathrm{Bez}}\le Q_{\mathrm{Sel}}+H^2$,
and a linear inequality $\alpha V+\beta C\ge 0$ is universal iff $\alpha\ge\beta$ and
$2\alpha+\beta\ge 0$. Equality at the upper endpoint $C=V/2$ forces the row onto the harmonic
and divisor-six coordinates; deleting the six-coordinate (an idempotent operation on rows)
lowers the constant to $C\le V/4$, and that constant is optimal.

Adding the primitive energy, the least energy at prescribed $(V,C)$ is
$\max\bigl(5V+2C,\ 6V+4C,\ 6V+12C\bigr)/12$ for $N\ge 6$, with edges supported on the mode pairs
$\{2,3\},\{3,4\},\{4,6\}$; the four modes $\{2,3,4,6\}$ realize every boundary point, and
prime modes escape every upper bound of the energy by the variance ($J_2(p)/\varphi(p)=p+1$).
With two lags and the consecutive triple the cone is spanned by $\{2,3,4,6,12\}$, giving
$0\le\mathcal V_{(0,1,2)}\le 4V$. For an arbitrary $k$-tuple $H$ and prime $p$ the structure
factor satisfies the sum-of-squares identity $p\,S_p(H)=\sum_r(p\,\nu_H(p,r)-k)^2$, and if $H$
omits a residue class modulo $p$ (Hardy–Littlewood admissibility at $p$) then
$S_p(H)\ge k^2/\varphi(p)$; the case $k=2$, $p=3$ is the $1/2$ above.

The mechanism behind all of these is the same: bound the modal weights of the forms against
each other arithmetically, identify the finitely many modes where the bounds are tight, and
realize them by finite Ramanujan inversion.

### 3.3 Polarization, the successor correlation, and renormalization

For every row and horizon the discrete Dirichlet polarization identity holds:
$$
\sum_{k=1}^{M}\bigl(s(k+1)-s(k)\bigr)^2+2\sum_{k=1}^{M}s(k)s(k+1)
=2\sum_{k=1}^{M}s(k)^2+s(M+1)^2-s(1)^2 .
$$
Combined with $\sum_{k\le M}s(k)s(k+1)=M\,Q_{\mathrm{Bez}}+(\text{Bézout sawtooth defect})$ and
$\sum_{k\le M}s(k)^2=M\,Q_{\mathrm{Sel}}+(\text{signed lcm defect})$, this yields the exact
pole-free identity for the finite Dirichlet energy in terms of $2M\sum_{e\ge 2}(\varphi(e)-\mu(e))Y(e)^2$,
the two signed defects, and the endpoint squares. The **renormalized defect**
$R_N(M;c)$ equals the combined defect minus $M$ times the successor reserve and satisfies
$$
2R_N(M;c)=-\sum_{k=1}^{M}\bigl(s(k+1)-s(k)\bigr)^2+s(M+1)^2-s(1)^2,
$$
so for the power-damped row it is $\le 0$ on $M+1\le N$, and for the literal Möbius row it is
exactly $-1$ on $1\le M\le N$ with non-positive increments through the first octave.

Renormalization is forced. For the literal Möbius row the unrenormalized combined defect
equals $M\cdot(\text{reserve})-1$ on $1\le M\le N$, dominates the number of primes in $(N/2,N]$
minus one at $M=N$, and therefore exceeds every $CN^{\alpha}$ with $\alpha<1$ along even
cutoffs. Any estimate must keep the cancellation with the diagonal main term.

On a short window $[M_0+1,M_0+M]$ the renormalized defect is non-positive for all rows iff the
endpoints share their multiplicative state, $\sigma_N(M_0+M+1)=\sigma_N(M_0+1)$, and for all
squarefree-supported rows iff they share their radical state. Period return is replaced by
state return.

### 3.4 Finite-prefix inversion and observability

The discrepancy on the initial prefix $M\in[1,n]$ at level $N=n+1$ determines
$c(2),\dots,c(n+1)$: second differences in $M$ annihilate the drift, Möbius inversion over
divisors recovers each $c(d)$ up to a rank-one coupling to the top column, and an explicit
harmonic endpoint correction interpolates arbitrary prefix data. The rational prefix matrix has
determinant $(-1)^n/(n+1)$; the prefix of length $n-1$ has a non-trivial kernel. Over $\mathbb Z$
the scaled matrix $A_n(M,d)=d\lfloor M/d\rfloor-M$ is unimodularly equivalent to
$\operatorname{diag}(1,2,\dots,n)$, with cokernel $\prod_{j\le n}\mathbb Z/j$, lattice index $n!$,
and kernel modulo $p^a$ of cardinality $p^{\sum_{r\le a}\lfloor n/p^r\rfloor}$. Reconstruction is
stable with a cutoff-independent constant: if two rows have discrepancies within $\varepsilon$
on $M\in[1,d]$ then $|c(d)-b(d)|\le 2\tau(d)\varepsilon$, and sampling the active sawtooth at
arbitrary powers recovers squarefree coefficients with the attained constant
$\frac{2d}{d-1}(\tau(d)-1)$.

Around a common return $R$ (all $d\le N$ divide $R$) the discrepancy reflects with defect
$\mathcal H_N(c)-\sum c(d)$; the window $[R-(N-2),R+(N-1)]$ of length $2N-3$ detects every
non-constant row, while on the window of length $2N-4$ the kernel is one-dimensional, spanned by
the normalized second-difference weight supported on $\{1,N-2,N-1,N\}$. The least period of
the signal of a row is the lcm of its active divisors; signed cancellation never shortens it.
For the full row this is $L_N=\operatorname{lcm}(1,\dots,N)$, whose logarithm is $\psi(N)$, not
$\log N!$. In the dual picture
$L_N(M,c)^2\le V\cdot\sum_{e\ge 2}\operatorname{Re}R_e(M)^2/\varphi(e)$, attained by an explicit
row, and the right-hand energy vanishes iff every $e\le N$ divides $M$.

### 3.5 Translation, compression, and visibility

True translation of the signal by $h$ is not an operator on rows. Its compression to rows is
the self-adjoint operator with eigenvalues $\lambda_q(h)$ in Selberg coordinates; it is the
optimal divisor-sieve predictor of the shifted signal, and its one-step case is the
**coprimality predictor** $c\mapsto\mu(d)\sum_{d\mid m\le N}c(m)/\varphi(m)$, which retains exactly
the squarefree coordinates. The residual is orthogonal to every response, and the loss is
exact: one-step prediction loses between three quarters and all of the variance above parity,
with equality at the lower endpoint only for the modes $3$ and $6$. Iterating the predictor
contracts the variance above parity by $4^{-m}$. Exact closure of the row space under
succession happens only for rows supported on the divisors $1$ and $2$.

Compressed lags do not compose: $\lambda_q(h_1+h_2)\ne\lambda_q(h_1)\lambda_q(h_2)$ in general. At
the mode $p^{a+1}$ every lag below $p^a$ is erased, yet two sub-clock lags adding to $p^a$ revive
the mode with defect $-1/(p-1)$. A schedule of true shifts recovers exactly the modes whose
visibility clock divides some lag in the schedule; each uncovered mode has an explicit
invisible signal. Averaging over the orbit of a stride $h$ is the Selberg-orthogonal projection
onto the modes $q\mid h$ and transports mass at $d$ to $\gcd(d,h)$; the projected row has
primitive energy at most $h^2V/16$, independently of the cutoff. Cross-coprime moduli and lags factor the multiplier as
a tensor, and sampling the composite clock wavelet at the transverse clock isolates adjacent
valuation shells $v_p(q)\in\{a,a+1\}$ with amplitudes $\pm p^a$.

All two-point data see only $Y(q)^2$. Third translated moments recover the sign of $Y(q)$ for
odd $q$; on the even pair $\{6,10\}$ every moment of degree $\le 5$ is blind to the relative sign
and the zero-lag sixth moment recovers it.

### 3.6 Pronic duality and the Gram calculus

The pronic readout $\sum_M L_N(M,c)/(M(M+1))=-\sum_{e\ge 2}\Lambda(e)Y(e)$ is the first exact
prime-power statement obtained from a divisor row without a period. Its square is the Gram form
$\sum Y(e_1)Y(e_2)\mathcal G(e_1,e_2)$, and the decomposition
$\mathcal G=\Lambda\Lambda^\top+\mathcal G^{\mathrm{ec}}$ gives the lower bound
$\bigl(\sum_e\Lambda(e)Y(e)\bigr)^2\le\sum_M L_N(M,c)^2/(M(M+1))$. Finite horizons are controlled
by the pronic tail: a bounded sequence has pronic remainder $\le B/(H+1)$ beyond $H$, and a
sequence with bounded partial sums has remainder $\le 2B/((H+1)(H+2))$, so after subtracting the
first-order tail $\frac{\varphi(e)}{2(H+1)}$ of the mean the von Mangoldt readout holds to second
order.

The Gram matrix obeys exact prime-dilation laws. For $p\nmid q,r$,
$$
\mathcal G^{\mathrm{ec}}(pq,pr)+\mathcal G^{\mathrm{ec}}(pq,r)+\mathcal G^{\mathrm{ec}}(q,pr)
=(p-1)\mathcal G^{\mathrm{ec}}(q,r)+(p-1)\Lambda(q)\Lambda(r),
$$
in the mean-centered form the von Mangoldt term is replaced by $\frac{p(p-1)}4\varphi(q)\varphi(r)$,
and for primes $p,q\nmid r$
$$
\mathcal G(pr,qr)+\mathcal G(pr,r)+\mathcal G(qr,r)+\mathcal G(r,r)=\sqrt{pq}\,\Phi_r(p/q),\qquad
\lim_{p\to\infty}\sqrt p\,\Phi_r(p)=\tfrac12\varphi(r)\Lambda(r).
$$
For the power-damped Ramanujan weight $Y_\varepsilon(q)=\operatorname{Re}\sum_{m\ge 1}\mu(qm)(qm)^{-1-\varepsilon}$
one has $Y_\varepsilon(pr)=-Y_\varepsilon(r)/(p^{1+\varepsilon}-1)$, and the pair $\{r,pr\}$ of adjacent
depths combines into the single Euler factor $\frac{p^{1+\varepsilon}}{p^{1+\varepsilon}-1}$ times the
scale difference $f_r-p^{-1/2-\varepsilon}D_{1/p}f_r$. Iterated over all divisors of a squarefree
$P$ coprime to $r$ this gives the **hypercube factorization**
$$
\sum_{m_1,m_2\mid P}Y_\varepsilon(m_1r)Y_\varepsilon(m_2r)\,\mathcal G(m_1r,m_2r)
=\Bigl(\prod_{p\mid P}\tfrac{p^{1+\varepsilon}}{p^{1+\varepsilon}-1}\Bigr)^2Y_\varepsilon(r)^2
\sum_{d_1,d_2\mid P}\mu(d_1)\mu(d_2)(d_1d_2)^{-1/2-\varepsilon}\,\Phi_r(d_1/d_2),
$$
with the finite cancellation $\prod_{p\mid P}\frac{p^{1+\varepsilon}}{p^{1+\varepsilon}-1}\sum_{d\mid P}\mu(d)d^{-1-\varepsilon}=1$
removing the undilated singularity across all depths at once. This is the exact finite form of
$\zeta(1+\varepsilon)\cdot\zeta(1+\varepsilon)^{-1}=1$; the cancellation that a fixed-depth prime star
cannot produce (§4) is produced coherently across depths.

### 3.7 The sawtooth martingale calculus of the power-damped energy

This is the physical-space analysis of $E_T(\varepsilon)$. Every step is an identity valid for
all $\varepsilon$ and $T$; only the logarithmic limits need $\varepsilon>0$.

**Pronic Abel summation.** For any sequence $A$,
$$
\sum_{n=1}^{T}\frac{A(n)^2}{n(n+1)}+\frac{A(T)^2}{T+1}
=A(1)^2+\sum_{n=1}^{T-1}\frac{A(n+1)^2-A(n)^2}{n+1},
\qquad
A(n+1)^2-A(n)^2=(\Delta A)(n)^2+2(\Delta A)(n)A(n),
$$
so the energy is a diagonal square sum plus twice a predictable martingale sum, both against
the compensated kernel $w_T(n)=\frac1{n+1}-\frac1{T+1}$.

**Active-deleted identity.** The active modulus flips sign at its jump, its square is
invariant, and the squared jump is cancelled pointwise by twice its martingale product. Absorbing
the pre-jump active part into the diagonal replaces the divergent square $\tau_\varepsilon(m)^2$
by the **shifted product** $\tau_\varepsilon(m)\tau_{1+\varepsilon}(m)$, whose local Euler defect is
divided by an extra factor $p$ and is summable down to $\varepsilon=0$. Absorbing also the
post-jump peak of the predecessor removes the diagonal square entirely:
$$
A_\varepsilon(n+1)^2-A_\varepsilon(n)^2
=\tilde\tau_\varepsilon(n)\tilde\tau_\varepsilon(n+1)
+\tilde\tau_\varepsilon(n+1)\,\Delta\tau_{1+\varepsilon}(n)
+2\,\tilde\tau_\varepsilon(n+1)\,I_\varepsilon(n),
$$
and the same identity holds for every row and cutoff with $W_{N,c}$, $s_{N,c}-Y(1)$ and the
interior sum in place of $A_\varepsilon$, $\tilde\tau_\varepsilon$ and $I_\varepsilon$. The energy therefore
splits as
$$
E_T=D^{\mathrm{act}}_T+2P^{\mathrm{pred}}_T+2M^{\mathrm{int}}_T,
\qquad
M^{\mathrm{int}}_T=\sum_{n=1}^{T-1}I_\varepsilon(n)\,\tilde\tau_\varepsilon(n+1)\,w_T(n),
$$
into an active-deleted diagonal, a predecessor-peak martingale, and the **Bézout interior
martingale**. The interior is supported on moduli $d\ge 3$ dividing neither $n$ nor $n+1$;
peeling the second shell $\{n-1,n+2\}$ transfers lag $1$ to lag $2$, and the shell of depth $r$
telescopes to $2r-1$ boundary values.

**Drifts.** Each bracket has an explicit logarithmic drift. The active-deleted diagonal grows
like $\kappa(\varepsilon)\log T$ with $\kappa(\varepsilon)/\varepsilon\to 1-1/\zeta(2)$; the
predecessor-peak martingale has a drift for every $\varepsilon>0$; the active-pair pronic energy
is bounded by $1/4$ and the pronic series of $\tilde\tau_\varepsilon S_\varepsilon$ by $1/8$, with
$S_\varepsilon=\frac12(\tau_{1+\varepsilon}-\tau_\varepsilon)$ the active component. After subtracting the
canonical drifts the first two brackets are $o(\log T)$, so the compensated interior bracket
tracks $\frac12E_T$ to within $o(\log T)$. The required interior cancellation rate has
small-damping slope $(1-A)/2\ge 7/24$, where $A=\prod_p(1-\frac1{p(p-1)})\le 5/12$.

**Non-circularity.** Summation by parts along $n$ in $M^{\mathrm{int}}$ returns $E_T$ with
coefficient one and cannot produce a contraction; what it does produce, after cancelling
$E_T$ and $2M^{\mathrm{int}}_T$ from both sides, is the conservation law
$$
\mathrm{Grad}_T+2\,\mathrm{Local}_T
=D^{\mathrm{act}}_T+2P^{\mathrm{pred}}_T-\mathrm{ActivePair}_T-O(1),
$$
whose left side divided by $\log T$ tends to an explicit positive constant for every
$\varepsilon>0$ with no admission hypothesis. The pure interior energy and the complete energy
control each other: $E_T\le 2E^{\mathrm{int}}_T+\frac12$ and $E^{\mathrm{int}}_T\le 2E_T+\frac12$.
A strict contraction $2M^{\mathrm{int}}_T+2\,\mathrm{Counterterm}\cdot H^{\mathrm{comp}}_T\le(1-\delta)E_T+C$
is equivalent to $\sup_TE_T<\infty$ at that damping.

**Conditional centering.** Along the progression $n\equiv -1\ (d)$ the interior atom of
modulus $e$ with both endpoint residues deleted has conditional mean $0$ if $\gcd(d,e)=1$ and
$(e-g)/(2e^2)$ otherwise, $g=\gcd(d,e)$. Subtracting it gives a zero-sum periodic sequence with
horizon-uniform bounds $e/(d\,g)$, improved to $1/d+2/g$ by delaying the centering until the
atom is born. Shared proper factors of composite interior moduli are the resonant
contribution; summing the compensated bounds over all moduli with absolute coefficients is not
uniform in the cutoff.

### 3.8 Dilation profiles and the Bézout seed

The continuous profile $\Phi_r(p/q)$ equals the reciprocal pairing of the integer jump streams
of $pr$ and $qr$; finite Diophantine lag sectors approximate it with error $\le B_r^2/Q$ at the
quadratic horizon $Q^2$. A pair contributes at the gap $h=pa-qb$ only if
$\tau_{\mathrm{vis}}(r)\gcd(p,q)\mid h$. For coprime scales every positive solution of
$pa=qb+1$ is $(a+qt,\,b+pt)$, so the complete successor sector is a weighted reciprocal
progression with exact digamma finite part; a complete modulus period of it has signed mass
$r\mu(r)$ when both scales are coprime to $r$ and $0$ otherwise. The **least seed** appears in
the profile with normalized error at most $r\varphi(r)^2/\sqrt{pq}$, every other lag staying in
the signed complement at the same physical horizon. The profile reduces to its radical:
$\Phi_r=v\,\Phi_s$ with $s=\operatorname{rad}(r)$, $v=r/s$, and the radical's successor sector
transports to physical lag $v$ at an aligned cutoff. Along nearby prime pairs the complement
approaches the positive diagonal Gram while the single clock-successor sector tends to zero.

This is the point at which additive structure enters the spectral half of the theory: the
profile is treated as a sum over solutions of a linear Diophantine equation, not only as an
inner product.

### 3.9 The literal Möbius source on linear windows

For $c=\mu$ the trans-horizon band formula gives unconditional laws on every window
$M\le(B+1)N$ with $B$ fixed.

- **Uniform first-moment cancellation.** For every $\varepsilon>0$ there is $K$ with
  $|L_N(M,\mu)|\le\varepsilon M$ and $|\sum_{k\le M}s_{N,\mu}(k)|\le\varepsilon M$ for all $N,M\ge K$,
  the two scales growing independently. The finite inequality behind it is
  $|\sum_{k\le M}s_{N,\mu}(k)|\le 1+2B\sup_{x\le(B+1)N}|M(x)|$, fed by the unconditional Mertens
  limit, and quantitatively by the Vinogradov–Korobov rate.
- **Quadratic profile.** $\frac1N\sum_{k\le(B+1)N}s_{N,\mu}(k)^2$ converges to an explicit finite
  Euler-product profile, monotone in $B$, equal to $6/\pi^2$ at $B=1$. Odd moments vanish in
  the limit; all moments have finite profiles; the source takes values in a finite alphabet
  determined by the primorial through $B+1$, every value is attained cofinally, and the value
  frequencies converge to a symmetric law whose support is exactly that alphabet. Both signs
  have positive frequency, at least $\frac{\text{profile}}{4C^2}N$ at horizon $(C+1)N$.
- **Gradient coercivity.** Every odd squarefree integer in $(N,2N]$ selects an adjacent edge
  ending at a multiple of four with gradient square $1$, so eventually, uniformly on
  $2N\le M\le N^A$, $R_N(M;\mu)\le -N/(2\pi^2)$, while on a fixed linear window
  $(2/\pi^2)N\le\mathcal E_N(M;\mu)\le 4A^3N$.

These are statements about the actual arithmetic source with no receiver hypothesis. They are
first-moment and fixed-ratio second-moment laws; none is a square-root bound.

### 3.10 Fermi cells and the trans-horizon octaves

On the cell $I_n$ the response of a row is twice its half-scale prefix minus its prefix, and
across a cell boundary it changes by $2\cdot\mathbf 1_{2\mid n+1}s(\frac{n+1}2)-s(n+1)$; by
Bézout no two consecutive boundaries both carry the dyadic term. For $c=\mu$ on the first octave
the half-scale prefix is frozen at $1$, the response is $1+\sum_{k=N+1}^{n}\mu(k)$, each jump is
$\mu(m)$, consecutive jump products are the successor correlations, and the cell energy is
$(1+\sum\mu)^2/(n(n+1))$. Uniform bounds for $M(n)-M(N)$ on $(N,2N]$ at every strict half-power
exponent are equivalent to the corresponding Mertens bounds, hence to RH. The sibling cells
$(2m,2m+1)$ satisfy an exact polarization identity, and the dyadic wavelet
$A\mapsto 2A(\lfloor n/2\rfloor)-A(n)$ reconstructs any prefix by multiscale telescoping.

### 3.11 General classes and ceilings

The algebra of §3.1 and §3.7 is not special to $\tau_\varepsilon$. Every GCD–LCM modular function
satisfies the pronic law $F(k)F(k+1)=F(k(k+1))$, the shifted law $F(k)F(k+h)=F(k(k+h))$ for
$\gcd(k,h)=1$, and the conservation law $(\Delta F)(n)^2+2F(n(n+1))=F(n)^2+F(n+1)^2$. For
$F=\prod_{p\mid n}(1-w(p))$ with $w\in[0,1]$ on primes one has divisor antitonicity,
submultiplicativity, the two-step ceiling $1-w(2)$, the three-step ceiling $(1-w(2))(1-w(3))$
from $6\mid k(k+1)(k+2)$, and for even $k$ the sharp cubic ceiling $(1-w(2))^2(1-w(3))$ from
$24\mid k(k+1)(k+2)$. The totient ratio $\varphi(n)/n$ and the Dedekind ratio $J_2/\varphi$ are
instances; at every prime $J_2(p)=(\varphi(p)-\mu(p))^2-1$ and $(q+1)\varphi(q)\le J_2(q)$ with
equality exactly at primes.

### 3.12 Bridges to classical sieve estimates

The response of the Möbius row is, up to sign, the Vaughan Type-II short coefficient:
$\mathbf 1_{k=1}-s_{N,\mu}(k)$. This identifies the prefix $L^2$ energy with Type-II short
energy and transfers in both directions: polylogarithmic all-horizon bounds into BVI, and the
log-free band bound $\sum_{m\le L}|{\rm typeIIShort}_V(m)|^2\le B^2(L-V)$ on $L\le(B+1)V$ into the
hybrid Vaughan assembly, where it confines every active dyadic block to a linear band and halves
the logarithmic exponent of the Kubalalika envelope. Distinct-modulus Kloosterman correlations
reduce to a terminal block with gcd-fibre multiplicity $\le\gcd(q+1,r+1)$. The Barban–Vehov
mollifier $\mu(d)\log(X/d)$ vanishes in Selberg coordinates beyond $X$ and has normalized
variance $O(1/\log X)$; the $\ker P$ projection annihilates the harmonic mode so that variance
equals the Selberg form and the discrepancy is drift-free.

---

## 4. Traps and sharp boundaries

| trap | correct statement |
|---|---|
| Pronic reach is cancellation. | $d\mid n(n+1)$ for some $d\in(M,M(M+1)]$ says nothing about $L_N(M,c)$: a single modulus $d>M$ contributes only the drift $-Mc(d)/d$. |
| A symmetric return window determines the row. | The window $[R-(N-2),R+(N-3)]$ of length $2N-4$ has a one-dimensional kernel; the asymmetric window of length $2N-3$ is needed. |
| Compressed lags form a semigroup. | $\lambda_q(h_1+h_2)\ne\lambda_q(h_1)\lambda_q(h_2)$; at $p^{a+1}$ all lags below $p^a$ are erased and two of them revive the mode with defect $-1/(p-1)$; even on squarefree support $\lambda_q(2)-\lambda_q(1)^2=-3/4$ at $q=3,6$. |
| Quadratic or odd data determine the row. | All two-point data see $Y(q)^2$; on $\{6,10\}$ every moment of degree $\le 5$ is blind to the relative sign. |
| Short windows read valuation phase. | Observing $t\mapsto\gcd(k+t,p^a)$ on fewer than $\varphi(p^a)$ points cannot distinguish $k=1$ from $k=1+p^{a-1}$; the threshold $\varphi(p^a)$ is sharp. |
| The raw Möbius defect is small. | The unrenormalized combined defect at $M=N$ exceeds every $CN^\alpha$, $\alpha<1$; only the renormalized defect, which keeps the diagonal main term, is bounded. |
| Multiplicative identities can close the problem. | Möbius inversion, Euler products, Gibbs log-submodularity and one-large-prime splits hold for every Beurling system, some of which violate RH. Closure needs $pa-qb=1$. |
| Fixed-depth cancellation. | Within a prime star $\{pr\}$ the Möbius sign is constant and nearby-prime terms $Y(pr)Y(qr)\mathcal G^{\mathrm{ec}}(pr,qr)$ are all positive; the depth-$k$ truncation of $1/\zeta(s+\varepsilon)$ still has the singularity at $1-\varepsilon$. Cancellation is coherent across depths only (§3.6). |
| Summation by parts is an estimate. | Along $n$ it is the product rule in reverse and returns $E_T$ with coefficient $1$; it never yields $(1-\delta)E_T$. |
| Changing the kernel is harmless. | Replacing $w_T(n)=\frac1{n+1}-\frac1{T+1}$ by $H_T-H_n$, or dropping the second difference of the active component from $\tilde\tau_\varepsilon(n+1)=\Delta I_\varepsilon(n)+\Delta^2S_\varepsilon(n)$, changes the target. |
| Misreading the damping quantifiers. | The receiver asks: for every $\delta>0$ some $\varepsilon<\delta$ and some $B_\varepsilon<\infty$ with $E_T(\varepsilon)\le B_\varepsilon$ for all $T$. The constant may depend on $\varepsilon$; divergence of constants as $\varepsilon\downarrow 0$ is no obstruction. Conversely $\prod_p(1+p^{-1-2\varepsilon})=\zeta(1+2\varepsilon)/\zeta(2+4\varepsilon)$ is not an estimate of the energy. |
| First-octave exactness is cofinal control. | $s_{N,\mu}=-\mu$ on $(N,2N]$ and the cell energies there are exact identities; they bound nothing beyond the octave. |
| Period statements bound prefixes. | Variance, covariance and reserve are period quantities; a prefix of length $N$ carries the signed defects and endpoint squares in addition. |
| Absolute values early. | Bounding the signed modulus sum of compensated interior atoms by absolute coefficients is not uniform in the cutoff; signed coupling must be retained. |

**Lean conventions.** Capstones are stated on data parameters and carry no analytic premise;
where a finite statement has hypotheses they are arithmetic side conditions on the data
(a prime, a coprimality, a horizon inequality, a damping range). Theorems that conclude `RiemannHypothesis` are
implications whose premise is one explicit finite inequality on $E_T(\varepsilon)$ or on an
equivalent bracket; the corpus never asserts such a premise. Analytic inputs (Mertens,
Vinogradov–Korobov, the prime number theorem, divisor moments) are proved corpus theorems, not
assumptions. Every module says in its header what its bounds do not prove.

---

## 5. The frontier

**The receiver.** For every $\delta>0$ exhibit $\varepsilon\in(0,\delta)$ with
$\sup_TE_T(\varepsilon)<\infty$. Equivalently, exhibit such $\varepsilon$ with $\sup_TE^{\mathrm{int}}_T(\varepsilon)<\infty$,
or with the strict interior contraction of §3.7. Known for every $\varepsilon\ge\frac12$, open
for every $\varepsilon<\frac12$; a bound at one fixed $\varepsilon<\frac12$ is already a zero-free
half-plane statement, so no routine bookkeeping can supply it.

**What the energy is made of.** After the canonical drifts are subtracted, the active-deleted
diagonal and the predecessor-peak bracket are bounded for every positive damping; the whole
obligation sits in the Bézout interior martingale $M^{\mathrm{int}}_T$, whose required
cancellation rate per $\log T$ has small-damping slope $\ge 7/24$. The interior is a sum of
signed atoms along progressions $n\equiv-1\ (d)$ with exactly known conditional means; what is
missing is the signed sum over moduli.

**The four tools.** Each known obstruction names a tool.

1. *Cross-depth cancellation.* Built at the level of exact identities (hypercube factorization,
   finite $\zeta\cdot\zeta^{-1}=1$ cancellation, natural-cutoff head/mean/tail split). Missing: a
   bound on the resulting Dirichlet form of the profile that is uniform in the cutoff.
2. *Bézout coupling at high scale.* The least seed $pa=qb+1$ is isolated inside the profile
   with inverse-scale error, and its complete fibre has mass $r\mu(r)$. Missing: control of the
   signed complement of all other lags, or of a signed prime packet, not only of a cofinal
   family of nearby prime pairs.
3. *Internal bilinear dispersion.* The reciprocity $\{N/pq\}\leftrightarrow\bar p/q+\bar q/p$
   converts correlations between moduli into exponential sums with modular inverses. The
   corpus has terminal-block and gcd-fibre reductions and log-free band bounds for Type-II
   sums; it does not have a dispersion estimate on $\sum a_pb_q\mathcal G^{\mathrm{ec}}(p,q)$
   without an external character average.
4. *A coercive contraction.* An inequality
   $2M^{\mathrm{int}}_T+2\,\mathrm{Counterterm}\cdot H^{\mathrm{comp}}_T\le(1-\delta)E_T+C_\varepsilon$
   with $\delta>0$, equivalent to the receiver. Identities cannot produce it; a signed
   arithmetic input across moduli must.

**Other open boundaries.** The sharp observability horizon at arbitrary phase $M_0$ for
$N\ge 5$ (the $2N-3$ law is proved at common returns and for $N=3,4$ everywhere); the sign of a
general signed prime packet in the energy-centered Gram; rates in the cofinal Möbius laws that
are uniform in the band ratio $B$; mixed-level covariances of centered pronic residue cells,
which are positive when the cells share a factor and start together.

---

## 6. Working in the theory

- **Name the coordinates and the regime first.** Raw, response, or Selberg; period, prefix,
  octave, or linear band. Most false claims in this area are category errors between these.
- **Search before building.** The corpus already holds the exact identities for most finite
  objects of §2; a new estimate is a new rearrangement of an existing identity more often than
  a new object.
- **Identity before asymptotics.** Every logarithmic drift in §3.7 and every density in §3.9
  is a limit of an exact finite formula that retains boundary terms and signed defects. Prove
  the finite formula, then pass to the limit.
- **Keep cancellation with the main term.** Never bound a signed defect in absolute value
  before the diagonal main term has been subtracted (§3.3); never sum compensated atoms with
  absolute coefficients (§3.7).
- **Test against Beurling.** If a proposed mechanism would hold verbatim for a Beurling
  system, it cannot close the frontier. The additive input must be visible: $\gcd(n,n+1)=1$, a
  solution of $pa-qb=h$, a residue class omitted modulo $p$.
- **State what a bound does not prove.** A first-moment law is not a square-root law; a
  fixed-$B$ profile is not uniform in $B$; a bound for $\varepsilon\ge\frac12$ is not a bound
  below $\frac12$; an exact octave is not a cofinal estimate.
