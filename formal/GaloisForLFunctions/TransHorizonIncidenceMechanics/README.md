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

## The shared target: the sign of the critical arithmetic form

Nine programmes of this corpus work on one object. The Riemann Hypothesis is the nonnegativity of
one critical arithmetic form, and the form can be read in three equivalent faces:

- the **incidence face** (Arithmetic Incidence Positivity, `ArithmeticIncidencePositivity`):
  conductance by conductance, on pairs of points `(x, y)` of the logarithmic line, with the
  arithmetic edges indexed by divisibility (`a ∣ b`) and by products (`ab` a prime power), and the
  pole as the only positive source on crossing pairs;
- the **lag face** (Square-Root Threshold, `SquareRootThreshold`): one window inequality `P_v ≥ 0`
  per scale on the prime side, for the difference tests of one generic width, at height `T` and
  bandwidth `λ = log X / log T`;
- the **aperture face** (Arithmetic Criticality Theory, `ArithmeticCriticalityTheory`; Arithmetic
  Positivity Theory, `ArithmeticPositivityTheory`; the odd Weil-weight route OWU in `RHTower`): the
  ground-energy path `μ(A)` of the restricted Weil form at aperture `A`, which must never cross zero,
  and the gauge and source theories that would prove it.

The finite arithmetic programmes (Bézout–Valuation Incidence, `BezoutValuationIncidence`;
Trans-Horizon Incidence Mechanics, `TransHorizonIncidenceMechanics`; Bi-Scale Uncertainty,
`BiScaleUncertainty`) supply the additive, single-modulus structure of the integers that the three
faces cannot see on their own: Bézout relations, residue classes, pronic Gram matrices, horizon
mechanics, and the two-scale constraint of the integer grid against the hyperbolic weight.

The continuation layer (Arithmetic Continuation and Critical Energy,
`ArithmeticContinuationAndCriticalEnergy`) supplies what no face states on its own: the transport
of a finite critical energy along a parameter — damping, coefficient cutoff or aperture — so that a
certificate at one parameter becomes a certificate at another, with the observation horizon
quantified uniformly throughout.

The admissibility layer (Scale-Signed Incidence Criticality, `ScaleSignedIncidenceCriticality`)
supplies the price list. A mechanism is not the arithmetic it studies but a *reading* of it — a map
from its data to the observables it actually uses — and each reading has an exact resolution limit:
the best bound on the target invariant that any method reading it can prove. The layer computes
those limits, so a route can be priced before it is built, and states the separations a reading must
perform to be admissible at all.

**Why one theory.** Each existing layer stops where the corpus proves it stops. Sieve and bilinear
methods see the additive structure of `ℕ` only after averaging over a family, and below half
damping no sign-blind datum decides the receiver. Multiplicative, spectral and explicit-formula
methods hold verbatim for Beurling systems with off-line zeros. Dirichlet-form and criticality
identities hold for every even positive kernel, and positivity on restricted families is paid by an
archimedean gain that is absent on the RH-complete cone. A closing theorem must at once see both
operations of `ℕ` at a single modulus, carry a sign structure (one negative square, the pole plane,
the signs of the Möbius row), and be resolved at the zero spacing, at square-root precision at every
scale. No existing field has its basic objects built with all three; the nine programmes build
them.

**The mechanisms the shared target needs**, with the programme that owns each:

1. A prime-side inequality with no slack: payment of each anti-diagonal atom `Λ(n) n^{−1/2}` by
   same-side atoms and the variance, on all even profiles, in sign-changing gauges, with a
   Harnack-type propagation across the prime shifts `log 2, log 3, …`
   (`ArithmeticIncidencePositivity` with `ArithmeticCriticalityTheory`).
2. Single-modulus bilinear dispersion on the pronic Gram, through the reciprocity
   `{N/pq} ↔ p̄/q + q̄/p`, for the actual Möbius or prime row; it reduces exactly to the
   single-modulus statistics `Σ_p |Λ_p(c')|/p` of that row (`BezoutValuationIncidence`).
3. A no-crossing law for the ground-energy path, equivalently the absence of a first negative lag
   for `ζ` (`ArithmeticCriticalityTheory`, `ArithmeticPositivityTheory` and OWU on the aperture side;
   `SquareRootThreshold` on the lag side).
4. A definite spectral realization with a prime modification as large as `S(T)`: a Hilbert space
   and a self-adjoint operator whose spectral measure is the critical-zero measure, with
   non-unit-modulus Euler factors (`ArithmeticPositivityTheory` for the source class and the
   realization problem; the operators of the routes HF, CHMD and Connes–Consani–Moscovici in
   `RHTower`). Every certificate of positivity is the critical-zero measure, so this is mechanism 3
   seen from the other side.
5. A sign-reading additive input at a single modulus: below half damping a bound on the receiver
   must read the signs of the coefficients, through first-order data at prime moduli (`k ↦ pk`) or
   odd-degree additive moments (`k ↦ k + v`) (`TransHorizonIncidenceMechanics` with
   `BezoutValuationIncidence`; `BiScaleUncertainty` for the node criticality `log 4` against
   `log 6`).
6. A continuation theorem transporting a finite critical energy from the unconditionally admitted
   end of a parameter range towards the critical end: a horizon-free bound on the negative part of
   one complete signed pairing on each compact subinterval, which is weaker than a bound on the
   corresponding norm and already yields an explicit zero-free strip when it covers only part of
   the range (`ArithmeticContinuationAndCriticalEnergy`).
7. An admissible reading: a mechanism presented as a reading of its own data whose fibres fail to
   realise the maximum of the invariant it claims to bound. On the zero side this forces the
   aperture past the Nyquist aperture of the configuration addressed and forces the *size* of the
   Weil deficit to be estimated rather than its sign; on the prime side it forces `Λ` to be
   separated from each of its single-index perturbations
   (`ScaleSignedIncidenceCriticality`).

**Criteria every contribution to the shared target must meet.**

- *Selectivity.* State what the result gives for `ζ(s−a)ζ(s+a)`, for a Beurling system with an
  off-line zero, and for the Liouville-twisted weight; a statement surviving all three is not
  about RH (test models: `BiScaleUncertainty`).
- *No family average.* One character, modulus one, shift zero. This is an exact floor and not a
  preference: the worst width inside a joint certificate over a family of any cardinality is the
  trivial one, because the extremal datum is already uniform across the family.
- *Square-root precision beyond the diagonal.* Prime sums of length at least the height,
  controlled beyond the mean-value regime: one inequality per window at every scale on the lag
  family, `θ = 2` on the Gram. On the aperture face the same demand is a theorem: a method
  controlling the Weil deficit of a configuration of scale `L` to precision `η` resolves depths
  only down to `√(η/L³)`, so excluding depth `β` costs precision `β²L³`.
- *Every scale, not almost every.* A statement about an exceptional set, a proportion or a typical
  member is infrastructure (the every-height problem: `SquareRootThreshold`). The two monotone
  faces may be verified along an unbounded sequence of apertures or radii, with nothing proved in
  between; the incidence face admits no sampling at all, since every prime power is individually
  necessary.
- *Node criticality.* The mechanism distinguishes `log 4` from `log 6`; sampling-density and
  generic uncertainty arguments are excluded in advance.
- *Signs read.* Below half damping the mechanism uses first-order data at prime moduli or
  odd-degree additive moments; magnitude, two-point and translated-moment data are blind, since the
  parity pairs exist at every damping `ε ≤ 1/2`.
- *Complete expression, no margin, no archimedean subsidy.* Mean, diagonal, mixed terms, Gamma and
  polar charges, endpoints and history are retained; a gain of size `log(1/w)` or `log M` at the
  archimedean place against a bounded prime cost is nonselective by construction. The dividing line
  is growth, not size: a subsidy growing with the frequency of the test is satisfied by the
  all-ones weight and removes the criterion outright, while a subsidy constant or linear in the
  aperture leaves it intact.
- *Units.* Positivity is measured by the aperture `A` or the support through which the inequality
  holds for all profiles; cancellation by the exponent `θ` obtained or the lag `V` beyond which
  `P_v ≥ 0` is proved; localization by the depth `δ(n, R)` excluded below height `T(n, R)` and by
  the visibility lag `V₀(w, η, δ₀)`; damping by the smallest `ε` at which the receiver is bounded;
  admissibility by the pair (class of readings, exact resolution limit). Identities, finite
  classifications and nonselective positivity count as zero in these units.
- *Grading.* A sign criterion with no partial value is incomplete. Every face of the target now has
  a one-parameter family whose endpoint is RH and whose interior is an explicit zero-free strip:
  the graded odd-sector floor and the graded incidence allocation at rate `2σ`, the graded pole
  cross entry at rate `1 + 2α`, and the partial damping continuation above `a₀`. State which member
  of the family a partial result reaches.
- *Calibration.* Reproduce the corresponding theorem over `F_q[T]`, or say why it cannot be done
  (`BiScaleUncertainty`).
- *Pairs.* Every invisibility theorem comes with a visibility witness, every identity with the
  estimate it enables or the sharp boundary it proves, every obstruction with its replacement
  hypothesis proved sufficient.

### This programme's role

THIM is the mechanics face of the finite theories. It owns the trans-horizon response of divisor
sieves, the conservation and dissipation laws under `k ↦ k+1`, `N ↦ N+1` and `k ↦ pk`, the transfer
to the continuous energies (the signed energies of `BezoutValuationIncidence`, the Fermi–Nyman traces,
the odd-sector prime-chain energies), and the exact collar cancellation of the odd sector. It owns
mechanism 5: the parity pairs (two weights with identical divisor-sum, Ramanujan and pronic data and
opposite trans-horizon growth, constructed at every damping `ε ≤ 1/2`), the parity barrier, the
classification of the observables that read the parity (first-order data at prime powers, the
logarithmic moments, the pole value of a kernel) and the receiver-preserving critical Wiener
algebra. Its odd-sector low-prime diagonal potential is the sieve-side reading of the unpaid axis
intervals of `ArithmeticIncidencePositivity`.

### How the programme connects to the other programmes

THIM is the dynamical layer over the static incidence algebra of Bézout–Valuation Incidence, and
the two are one theory with two folders. Its outward connections run through the receiver
`E_T(c)` and the parity involution.

- **Bézout–Valuation Incidence is the algebra THIM moves.** The exact prefix-discrepancy duality
  and return times, the renormalized defect and pronic ceiling, the cofinal Möbius gradient
  coercivity, the phase-uniform window Poincaré law (the long-window regime of §3.4), the
  prime-tail calibration, the Jordan and primitive energies, the quotient–octave reciprocity, the
  Euler deletion remainder, the cyclotomic incidence recurrence, the dilation-pair densities behind
  the energy profile and the Hardy–Littlewood singular series are BVI theorems consumed here; the
  horizon filtration, the Buchstab and band calculus, the damped observer, the Fermi schedules,
  the radical states and the parity pairs are THIM theorems consumed by BVI, where the pairs are
  separated on the Vinogradov–Korobov band and the receiver of a multiplicative weight is decided
  at the primes on that band. The Type-II window no-go of BVI (no `ℓ²` class reaches `θ > 1` at
  one modulus) and the parity barrier of §3.16 are the two halves of mechanism 5: the Gram side
  and the receiver side of the same sign-blindness.
- **Bi-Scale Uncertainty supplies the continuous coordinates and the producer–consumer duality.**
  The Nyman–Beurling bridge, the Lorentz boost and light cone, the stationary resolvent's Markov
  positivity, the Euler–Poisson chiral drift, the `ker P` centred sieve and the universal Ramanujan
  covariance are BiScale theorems used in §3.6, §3.13 and §3.17; BiScale's arithmetic observation
  theory uses THIM's radical checkpoint rigidity and finite multiplicative observation state.
  BiScale's sign-character classification (which moments recover a sieve signal, up to which
  translation) and THIM's parity pairs (which observables decide the receiver) are the same
  phenomenon read from the recovery side and from the receiver side; the half-damping threshold
  of §3.8 and §3.16 is the square-root barrier of BiScale's band in the receiver's coordinates.
- **Arithmetic Criticality Theory and Arithmetic Incidence Positivity meet THIM in the odd
  sector.** The Markov operator, the theta ground state, the odd eigenvector criterion of §3.13
  and the collar transport of §3.14 are the chain-side reading of ACT's odd-sector criticality;
  the shifted ground state's folded representation and its combination failure are ACT theorems
  used in the collar duality of §3.17. The low-prime diagonal potential left after exact collar
  cancellation (§3.15) is the sieve-side counterpart of AIP's unpaid axis intervals and its nine
  atom-dominated moduli: the same prime atoms `Λ(d)d^{−1/2}` that AIP pays pair by pair on the
  jump form are the ones the chain variances must absorb.
- **Square-Root Threshold and Arithmetic Positivity Theory see the same zeros from the other
  side.** The poles of `1/ζ(s+ε)` right of `Re s = 1/2` that a bound on the Möbius receiver must
  exclude (§3.16) are the off-line zeros SRT's lag family makes visible; THIM's "uniform in the
  horizon at fixed damping" is the receiver form of SRT's every-height problem, and the damping
  `ε` plays the role of SRT's bandwidth and APT's envelope exponent. The critical-scale receiver
  `D(T) ≤ B(1+T)e^{T/2}` of APT is the Chebyshev-level statement whose finite-modulus form is the
  interior pronic energy of §1.2.
- **Arithmetic Continuation and Critical Energy owns the parameter direction of the receiver.**
  THIM proves what a bound at one damping is worth and which observables could produce it; the
  continuation layer proves how a bound travels from an admitted damping towards the critical end,
  with the horizon quantified uniformly. The two meet in one identity: the derivative of the
  critical energy in the damping is twice a complete signed pairing, which is the flux–jump–forcing
  balance of the arithmetic chain, so THIM's dissipation laws are exactly what the continuation
  must lose. The accumulation criterion of §3.16 is the endpoint statement of that transport.
- **Scale-Signed Incidence Criticality turns the parity barrier into a floor on methods.** The
  barrier is, verbatim, failure of resolution for the amplitude reading; the admissibility layer
  adds the closure of the class (no amplitude-derived family of any cardinality resolves the
  receiver) and the number `½` in the damping unit, and records that the same `½` is the trivial
  width of the zero side. In the other direction THIM supplies the weights and the pairs that the
  admissibility layer uses as witnesses — the floors there are not models but this programme's
  arithmetic.
- **RHTower supplies the analytic inputs**: the PM lane (power-damped Möbius Ramanujan weights,
  second moment, small-damping variance, cofactor rows), the sieve library (Levinson's gcd form,
  Möbius harmonic log rate, Gallagher's range, prime-window levels, Matomäki–Teräväinen
  coefficients), the zero-density exponents, the CHMD prime-chain source factorization and
  balanced nodal graph, the Liouville summatory criterion, the floor-transform harmonic inverse
  and the zeta-residue calculus.

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

### 3.17 Bridges

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

## 4. Traps and sharp boundaries

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

## 5. The frontier

**The complete signed trans-horizon energy.** The PM receiver needs
$\sup_T\sum_{n\le T}I_\varepsilon(n)^2/(n(n+1))<\infty$ at arbitrarily small fixed
$\varepsilon$. The receiver row is now understood on the period torus: it observes
the complete damped divisor function, its renormalized defect is eventually
nonpositive at every prefix, its period variance is a partial Parseval sum
bounded by $V(\varepsilon)$ uniformly in the horizon, and its primitive energy
diverges for $\varepsilon\le1/2$, so complete-period averages cannot supply the
bound. What is missing is the pronic-weighted interior energy below the first
period: cancellation in the coefficient-weighted energy with means, endpoints,
mixed covariance and growing cutoffs retained, at fixed $\varepsilon\in(0,1/2)$,
where the small arguments carry the weight $1/(n(n+1))$ and the Ramanujan
truncation error $Q^{-\varepsilon}\tau(n)$ is not small.

**Small horizons.** The long-window law is explicit and quadratic at every
horizon $N\ge2$ (threshold $10N^2+8N$ for Möbius), but the polynomial-window
sign is proved only eventually in the horizon, through prime counts in octaves.
Whether the renormalized defect is nonpositive at every prefix for every
horizon $N\ge2$, and the exact constant of the window observability law (its
order $N^2$ is exact), are open.

**Buchstab calculus.** The band averages $A(1),\dots,A(4)$ are negative and the
profile values $P(1),\dots,P(4)$ are known; the sign of $A(B)$ for every band,
the monotonicity and concavity of the profile, and the classification of the
squarefree cores with negative slope in each band are open. The damped
crossover is located to second order with an additive window $\pm\varepsilon$;
the sign of the slope for prime horizons inside that window,
$\lvert\log p-\Lambda(\varepsilon)\rvert<\varepsilon$, is open, as is every term of
$V(\varepsilon)$ and $R(\varepsilon)$ beyond the second order.

**The odd sector.** After exact collar cancellation the remaining obligation is
an independently quantified bound on the low-prime diagonal potential, or an
actual-source nodal estimate paying the primitive ground-projection defect. The
cosh/sinh ratio cannot be made $\le1$ on compact profiles; the minimal local
correction must be paid by jump energy, or the source class restricted so that
the confinement law suffices. The coordinates are now canonical: the polar risk is
rank one, read by the single shift-independent moment $\langle q,\tanh_L\rangle$ with
$\mathrm{sourceEnergy}=\mathrm{weilForm}+2\langle q,\tanh_L\rangle^2$ exactly, so the question is
nonnegativity of $\mathrm{sourceEnergy}$ on the kernel of one functional, and the shift can no
longer be tuned. Two unconditional lobe inequalities are available — the cross-lobe Rayleigh
excess at positive eigenvalue and the chiral drift bound on both lobes — and neither closes the
four-term excess. What a new mechanism must add is a *cross-lobe* estimate: both tightenings are
lobe-local, and the obstruction is the pairing between the lobes.

**Fermi–Nyman.** Origin and bulk tightness on one explicit approximation
sequence; the observation theory of dyadic schedules is complete for one gap,
and the conditioning of schedules with two or more gaps, which are not
injective, is a least-squares question: which rows are recovered and at what
price. Non-dyadic schedules (levels of an odd prime) and weighted traces have no
classification yet.

**The parity pair.** Below half damping the receiver of a weight is not a function of its
sign-blind data, and every known pair is decided by a pole at $s=1-\varepsilon$. The equivalence
half of the lane is settled: the damping threshold of the Möbius receiver is the zero width, so RH
is admission along any sequence of dampings tending to $0$ and nothing weaker than an accumulation
is worth anything. What remains is one unconditional bound at one fixed $\varepsilon<\tfrac12$, and
by the closure of the blind class it must be read from signed data. Open: the pole law
for kernels outside the critical Wiener algebra, where floor sums lose a logarithm; whether a
completely multiplicative $\pm1$ sign whose $-1$-primes have relative density $\delta$ is paid at
half damping exactly when $\delta>1/4$ (the heuristic $F\approx\zeta^{1-2\delta}$; only the sparse
necessary condition is proved); whether signed rows can be uniformly bounded while their pointwise
limit is unpaid, or conversely (positivity forces commutation); and a quantitative form of the
logarithmic hierarchy, bounding the receiver by finitely many logarithmic moments with an explicit
loss.

### Research topics toward the shared target

1. **From separation to a bound.** The parity pairs exist at every damping `ε ≤ 1/2` and the
   observables that separate them are classified: first-order data at prime powers, the logarithmic
   moment hierarchy, the pole value `K(1 − ε)` and its Taylor coefficients (mechanism 5). Find an
   estimate that turns one of them into a bound on the actual Möbius receiver at one fixed
   `ε < 1/2`, with its exact loss; this is the Type-II input the shared target needs.
2. **The complete signed trans-horizon energy** at fixed small damping, with means, endpoints,
   mixed covariance and growing cutoffs retained.
3. **The odd-sector low-prime diagonal potential**, matched term by term with the unpaid axis
   intervals and the nine moduli of `ArithmeticIncidencePositivity`: one obstruction read from the
   sieve side and from the pair side.
4. **Selectivity of the transfer laws.** Which conservation and dissipation laws hold for a
   Beurling system or the shifted pair, and which are specific to `ℕ`.

---

## 6. Working in the theory

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
