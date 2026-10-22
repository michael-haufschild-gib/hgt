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
conclusion of criteria whose premise is one explicit finite inequality, or inside exact
equivalences; the theory never asserts such a premise.

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

BVI is the additive finite face. It owns the Bézout relation `pa − qb = h`, the valuation structure of
moduli, the pronic Gram, the Vasyunin reciprocity law, and the interior martingale whose signed sum
over moduli is the receiver. It owns mechanism 2 (single-modulus bilinear dispersion) and shares
mechanism 5 with `TransHorizonIncidenceMechanics`. It supplies the additive window structure
(consecutive integers, residue classes omitted modulo `p`, the spacing of the jumps of `{N/p}` and
`{N/q}`) that the incidence face of `ArithmeticIncidencePositivity`, built on divisibility and
products alone, does not see.

### How the programme connects to the other programmes

BVI is the static incidence algebra of the finite side; everything it proves is an exact
rearrangement of the bilinear form of a row against the incidence matrix `𝟙_{d∣n}`, and the other
programmes either move that algebra (THIM), observe it (BiScale) or read its receiver in their own
units (the three faces).

- **Trans-Horizon Incidence Mechanics is the dynamics of this algebra**; the two programmes are
  one theory in two folders. BVI's prefix-discrepancy duality, renormalized defect, gradient
  coercivity, window Poincaré and long-window dissipation (§3.4), Jordan and primitive energies,
  quotient–octave reciprocity, dilation-pair densities and singular series are consumed by THIM's
  horizon filtration, band calculus and damped observer; THIM's horizon steps, radical states,
  clock wavelets, Fermi schedules, parity pairs and the receiver classification of multiplicative
  weights are consumed here, where the pairs are separated on the zero-free bands (§3.15). BVI's
  coherent-block Type-II ceiling (§3.13) and THIM's parity barrier are the Gram side and the
  receiver side of mechanism 5.
- **Bi-Scale Uncertainty observes the rows BVI builds.** BiScale's sieve phase recoveries (cubic,
  sixth), affine spectrum and translation anchoring, highest-mode stability, two-lag moment cone,
  universal Ramanujan covariance, `ker P` centred sieve, Barban–Vehov pinch, signed lcm defect and
  Vasyunin tail-Gram producer are used in §3.2, §3.5, §3.6 and §3.14; BVI's translation prediction
  and exact compression, six-mode stability, gcd-orbit projection, Ramanujan lag coefficient,
  pronic Bézout split and successor moment region are used in BiScale's arithmetic observation
  theory. The passage from complete periods to windows at unknown phases (§3.4) is owned here and
  consumed there; the pronic measure of §2.7 is Lebesgue measure on `(0, 1]` read through
  BiScale's Fermi–Nyman cells.
- **Arithmetic Incidence Positivity classifies the multiplicative incidence that BVI complements
  additively.** AIP's lattice pairs `(−log a, log b)` with `a ∣ b` or `ab` a prime power are the
  divisor edges of one dyadic window; BVI's successor incidence `d₁ ∣ k`, `d₂ ∣ k + 1`, the
  Bézout seeds `pa − qb = 1` and the residue classes omitted modulo `p` (§3.13) are the additive
  edges of the same window, which the incidence face cannot see. The omitted-class law of the
  prime row is the first statement of this programme written in AIP's window.
- **The three faces read BVI's receiver in their own units.** The receiver `E_T(ε)` is bounded
  for `ε ≥ 1/2` and on the zero-free bands below it (§3.15); every band is a zero-free region,
  which `SquareRootThreshold` reads as a zero width and `ArithmeticCriticalityTheory` as the rate
  of the ground-energy path. The pronic Báez-Duarte criterion of §3.7 is the Nyman–Beurling form
  of the one critical form the three faces state through lags, apertures and incidence; the
  critical-scale receiver `D(T) ≤ B(1+T)e^{T/2}` of `ArithmeticPositivityTheory` is the
  Chebyshev-level form of the same square-root barrier that §1.3 states for rows.
- **Arithmetic Continuation and Critical Energy differentiates the receiver in the damping.** BVI
  owns the receiver at a fixed damping and the chain whose time parameter the damping is; the
  continuation layer owns the transport in that parameter, and the two meet in one identity: the
  derivative of the critical energy is twice a complete signed pairing, equal to BVI's
  flux-minus-jump-minus-forcing balance of the arithmetic chain. The damping threshold of the
  receiver is exactly the zero width, so the chain's small-time limit is the critical end of the
  transport, and the entrance-tail barrier says which norm cannot carry it there.
- **Scale-Signed Incidence Criticality prices the Gram and the dispersion.** A new dispersion
  estimate is admissible only if the reading it uses separates the gate pairs; for the cross-scale
  form of §3.13 the relevant reading is the pronic Gram at one modulus, and its exact limit in the
  exponent unit $\theta$ is the quantity a route should report. The coherent prime block of the
  Type-II no-go is the witness that fixes it.
- **RHTower supplies the analytic inputs**: the PM lane (power-damped Möbius Ramanujan weights,
  cofactor rows, the receiver's zero-translation converse), the sieve library (Farey-point large
  sieve infrastructure, Kuzmin–Landau, Vinogradov–Korobov, Mertens rates, Selberg and
  Barban–Vehov diagonals, Dirichlet's theorem in Chebyshev form), the Báez-Duarte criterion with
  its dual sequence, Estermann's `D(s, a/q)` and the Montgomery–Vaughan cosecant inequality of
  `HTGeometry`.

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

A row $c$ has four coordinate systems.

- **Raw weights** $c(d)$, $1\le d\le N$.
- **Responses** $s_{N,c}(k)=\sum_{d\le N,\,d\mid k}c(d)$, the signal at position $k$.
- **Selberg multiples coordinates** $Y_{N,c}(e)=\sum_{e\mid d\le N}c(d)/d$, $1\le e\le N$.
- **Spectral form.** Character orthogonality $\sum_{\zeta^d=1}\zeta^k=d\,\mathbf 1_{d\mid k}$
  writes the response as a finite exponential sum over the **response frequencies**
  $T_N=\{\zeta:\zeta^d=1\text{ for some }d\le N\}$, the roots of unity of order at most $N$,
  graded by order:
  $$
  s_{N,c}(k)=\sum_{\zeta\in T_N}Y_{N,c}(\operatorname{ord}\zeta)\,\zeta^k .
  $$
  The coefficient depends only on the order of the frequency (Galois invariance under
  $\zeta\mapsto\zeta^u$, $u$ a unit), the characters $n\mapsto\zeta^n$ are linearly independent,
  and distinct response frequencies are $1/N^2$-separated on the circle.

Raw and Selberg coordinates are related by a triangular bijection; the inverse is finite
Ramanujan inversion, $c(d)=d\sum_{m\le N/d}\mu(m)\,a(dm)$, which realizes any prescribed
$Y$ on $[1,N]$. The coordinate $Y_{N,c}(1)=\mathcal H_N(c)=\sum_{d\le N}c(d)/d$ is the
**harmonic mode**, the mean of the response over a period; the subspace $\mathcal H_N(c)=0$
is written $\ker P$. The period mean square of the centered response is
$\sum_{e\ge 2}\varphi(e)\,Y_{N,c}(e)^2$, and totient-normalized Selberg coordinates are an
isometry from rows to $\ell^2$. The **Selberg support** of a row is $\{q:Y_{N,c}(q)\ne0\}$, and
its **recurrence complexity** is $\sum_{Y(q)\ne0}\varphi(q)$; the **cyclotomic incidence
polynomial** $Q_N=\prod_{q\le N}\Phi_q$ has degree $\Phi(N)=\sum_{q\le N}\varphi(q)$, with
$N^2/8+N-\tfrac N2H_N\le\Phi(N)\le N(N+1)/2$.

A fifth coordinate system sits on top of the Selberg one and explains where the totient weight
comes from. The **Witt ghost coordinates** are the ghost components $g_w(q)$ of a real Big-Witt
vector $w$ — the coefficients of the logarithmic series of its defining power series, the
Deninger presentation. Ramanujan inversion of the data $q\mapsto\sqrt{\varphi(q)}\,g_w(q)$ produces a
row whose Selberg coordinates are exactly the ghosts, $Y_{N}(q)=g_w(q)$ for $1\le q\le N$, so
$$
\lVert c_w\rVert^2=\sum_{q\le N}\varphi(q)\,g_w(q)^2 :
$$
the sieve norm of the row *is* the totient-weighted ghost energy, and $w\mapsto c_w$ is additive.
In these coordinates the two Witt operations become finite, explicit coordinate moves on rows.
**Frobenius at two** reads the ghosts at doubled index, $g_{F_2w}(q)=g_w(2q)$, so the row at
horizon $N$ built from $F_2w$ has the Selberg coordinates of the row at horizon $2N$ built from $w$,
read at the even indices: Frobenius does not invent data beyond the cutoff, it *consumes a larger
cutoff*. **Verschiebung at $m$** is the substitution $T\mapsto T^m$ on the defining series and acts
as the exact dilation
$$
g_{V_mw}(q)=\begin{cases}m\,g_w(q/m)&m\mid q\\0&\text{otherwise,}\end{cases}
$$
a sparsification onto the multiples of $m$ with a factor $m$ — the same up-set structure the
divisibility edges of §2.5 carry. The native lag compression of §3.5 acts diagonally on the same
ghosts, multiplying the $q$-th by the lag multiplier $\lambda_q(h)$, so translation, Frobenius and
Verschiebung are three commuting families of explicit operations on one coordinate vector. This
identifies the finite sieve receiver as a *finite-cutoff truncation of the Big-Witt ring*, with the
cutoff retained in every statement: whether the Witt ring structure supplies an estimate the
Selberg coordinates do not already give is open, but the dictionary is exact and the arithmetic of
the operations is finite.

The first discipline of the theory: say in which coordinates a statement lives, and whether it
concerns the period, a prefix, or a window at an arbitrary phase. A statement about the period
mean square says nothing about a prefix of length $N$; a window law says nothing below its
horizon. The Witt dictionary does not relax this: Frobenius changes the cutoff, so a ghost
statement at horizon $N$ is a Selberg statement at horizon $2N$, not at $N$.

### 2.2 Horizons and windows

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

A **window** is a block $A<k\le A+K$ of $K$ consecutive positions at an arbitrary **phase** $A$.
The theory distinguishes four horizons for windows: the period $L_N$, the **cyclotomic horizon**
$\Phi(N)$, the **quadratic horizon** $N^{2\pm o(1)}$ of mean-square transfer, and the
**degree-$m$ horizon** $N^{m\pm o(1)}$ of $m$-point statistics. A **window sandwich constant**
at level $N$ is a number $S$ with
$\bigl\lvert\sum_{A<k\le A+K}(s(k)-\kappa)^2-KQ\bigr\rvert\le SQ$, $Q=(H-\kappa)^2+V$, for every
row, phase, length and offset; a **degree-$m$ transfer constant** bounds the window error of
every translated moment of degree $m$ by $S\,Q_{\mathrm{Sel}}^{m/2}$. The **observability
constant** is $S_N=\sum_{q\le N}\sigma(q)^2/\varphi(q)$.

### 2.3 Discrepancy, sawtooth, primitive, and the interior

The **centered sawtooth** of modulus $d$ is $\tilde B_1(d,n)=\{n/d\}-\frac{d-1}{2d}$, with step law
$\tilde B_1(d,n+1)-\tilde B_1(d,n)=\frac1d-\mathbf 1_{d\mid n+1}$. The **weighted centered sawtooth
sum** $W_{N,c}(n)=-\sum_{d\le N}c(d)\tilde B_1(d,n)$ therefore has forward difference
$$
W_{N,c}(n+1)-W_{N,c}(n)=s_{N,c}(n+1)-Y_{N,c}(1),
$$
so it is the zero-mean **canonical primitive** of the centered response, $L_N(M,c)=W_{N,c}(M)-W_{N,c}(0)$,
and on the response frequencies integration is division by $\zeta-1$:
$$
W_{N,c}(k)=\sum_{\zeta\in T_N,\ \zeta\ne1}Y_{N,c}(\operatorname{ord}\zeta)\frac{\zeta}{\zeta-1}\,\zeta^k .
$$
Across the step $n\mapsto n+1$ the moduli split three ways:

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
| Bézout successor covariance $C$ | $\mu(e)$ | period covariance of $s(k)$ and $s(k+1)$; equals $V-R$ |
| successor reserve $R$ | $\varphi(e)-\mu(e)$ | half the period mean square of the gradient $s(k+1)-s(k)$ |
| one-step phase loss | $\varphi(e)-\mu(e)^2/\varphi(e)$ | variance not predictable from the present |
| primitive energy $E\times 12$ | $J_2(e)$ | period mean square of $W_{N,c}$; equals the coefficient energy $\sum_{\zeta\ne1}Y(\operatorname{ord}\zeta)^2/\lvert\zeta-1\rvert^2$ |
| lag-$h$ covariance $\mathrm{Cov}(h)$ | $c_e(h)=\varphi(e)\lambda_e(h)$, $\lambda_e(h)=\dfrac{\mu(e/g)}{\varphi(e/g)}$, $g=\gcd(e,h)$ | period covariance at lag $h$; $c_e(h)$ is the power sum of the primitive $e$-th roots |
| consecutive triple $(0,1,2)$ variance | $3\varphi(e)+4\mu(e)+2\lambda_e(2)\varphi(e)$ | variance of $s(k)+s(k+1)+s(k+2)$ |
| tuple variance $\mathrm{Var}_H$ | $S_e(H)=\sum_{\zeta\text{ prim. of order }e}\lvert\sum_{h\in H}\zeta^h\rvert^2$ | variance of $\sum_{h\in H}(s(n+h)-H_c)$; $S_e(H)$ is the **structure factor** of the tuple |

The harmonic mode $e=1$ cancels between the Selberg and Bézout forms, $\varphi(1)-\mu(1)=0$,
even off $\ker P$. The successor covariance is the period main term of the finite successor
correlation; its diagonal weight $\mu(e)$ separates $4$ from $6$ where the totient does not
($\varphi(4)=\varphi(6)=2$, $\mu(4)=0\ne 1=\mu(6)$). The **multi-lag covariance cone** at lag
horizon $h$ is the cone of all vectors $(\mathrm{Cov}(0),\dots,\mathrm{Cov}(h))$ over all rows
and cutoffs. Higher moments are **translated moments** $M_m(c;v)$, the period averages of
$\prod_{i<m}s(k+v_i)$; in spectral form they are sums over the **zero-product tuples**
$\prod_i\zeta_i=1$ of the **relation coefficients** $A_c(\zeta)=\prod_iY(\operatorname{ord}\zeta_i)$,
and an order tuple $(q_1,\dots,q_m)$ is **layer admissible** when for every prime $p$ and every
$a\ge1$ with no $q_i$ divisible by $p^{a+1}$, the number of $q_i$ divisible by $p^a$ is not one,
and is even when $p=2$.

### 2.5 Incidence objects

- **Successor incidence count** $\mathcal I(M;d_1,d_2)=\#\{k\le M:d_1\mid k,\ d_2\mid k+1\}$. It is
  zero unless $\gcd(d_1,d_2)=1$, and for coprime moduli every block of $d_1d_2$ consecutive
  integers contains exactly one hit, so $\lfloor M/d_1d_2\rfloor\le\mathcal I\le\lfloor M/d_1d_2\rfloor+1$.
  For a family $d_i\mid k+h_i$ the set of positions is empty or one residue class modulo
  $\operatorname{lcm}(d_i)$ (Chinese remainder), so on every window its count is within one of
  $K/\operatorname{lcm}(d_i)$.
- **Bézout sawtooth defect** $\delta(M;d_1,d_2)=\mathcal I(M;d_1,d_2)-M/d_1d_2\in[-1,1]$ for
  coprime moduli, zero otherwise and zero at common returns.
- **Combined and renormalized defects.** The successor correlation is
  $\sum_{k\le M}s(k)s(k+1)=M\,Q_{\mathrm{Bez}}(c)+\sum c(d_1)c(d_2)\delta(M;d_1,d_2)$ with
  $Q_{\mathrm{Bez}}=\sum_{e\ge 1}\mu(e)Y(e)^2$. The renormalized defect is
  $R_N(M;c)=\sum_{k\le M}s(k)\bigl(s(k+1)-s(k)\bigr)$; its short-window version lives on
  $[M_0+1,M_0+M]$ and its window version $R_W$ on a window of length $K$ at any phase.
- **Prefix $L^2$ energy** $\mathcal E_N(M;c)=\sum_{k\le M}s_{N,c}(k)^2$; **window Dirichlet
  energy** $D_W=\sum_W(s(k+1)-s(k))^2$.
- **Tuple residue occupancy** $\nu_H(p,r)=\#\{i:h_i\equiv r\ (p)\}$ and the prime structure
  factor $S_p(H)=p\sum_r\nu_H(p,r)^2-k^2$ of a $k$-tuple $H$; for squarefree $q$ the structure
  factor $S_q(H)$ of §2.4 is the Montgomery sum of $H$ at $q$.

### 2.6 Valuation objects

- **Visibility clock** $\tau_{\mathrm{vis}}(q)=q/\operatorname{rad}(q)$, the least lag at which
  the mode $q$ is visible to compressed translation.
- **Lag multiplier trichotomy** at a prime power: $\lambda_{p^{a+1}}(h)=1$ if $p^{a+1}\mid h$,
  $=-1/(p-1)$ if $p^a\mid h$ but $p^{a+1}\nmid h$, $=0$ otherwise.
- **Smooth and rough parts of a mode** relative to a lag horizon $h$: $e=gr$ with
  $g=\gcd(e,(h!)^e)$ its $h$-smooth part and $r$ coprime to $h!$; lags $j\le h$ see $r$ only
  through $\mu(r)$.
- **Layers** of an order tuple: the $p^a$-layer is the set of indices whose order is divisible
  by $p^a$; the **top layer** at $p$ is the highest nonempty one.
- **GCD–LCM modular functions**: $F(1)=1$ and $F(j)F(k)=F(\operatorname{lcm}(j,k))\,F(\gcd(j,k))$.
  Every function $n\mapsto\prod_{p\mid n}(1-w(p))$ is of this kind; it is radical-invariant,
  divisor-absorbing ($d\mid m\Rightarrow F(dm)=F(m)$), and satisfies $F(k)F(k+1)=F(k(k+1))$.
  The cases $w(p)=p^{-\varepsilon}$ and $w(p)=1/p$ are $\tau_\varepsilon$ and $\varphi(n)/n$.
- **Shifted exponent**: $\tau_{1+\varepsilon}(n)=\sum_{d\mid n}\mu(d)d^{-1-\varepsilon}$, equal to
  $c_\varepsilon(d)/d$ summed over $d\mid n$, and to $\varphi(n)/n$ at $\varepsilon=0$.

### 2.7 The pronic measure, the Gram, and its cotangent form

The **pronic measure** puts mass $w(M)=\frac{1}{M(M+1)}$ on each $M\ge 1$; it has total mass $1$
and tail mass $\frac1{H+1}$ beyond $H$. It replaces period averaging. The **Ramanujan primitive**
$R_e(M)=\sum_{n\le M}c_e(n)$ has period $e$ and mean $-\varphi(e)/2$, with
$\operatorname{Re}R_p(M)=-(M\bmod p)$ at primes, and
$$
L_N(M,c)=\sum_{e=2}^{N}\operatorname{Re}R_e(M)\,Y_{N,c}(e).
$$
On the primitive roots of order $e$ the primitive is the pure exponential sum
$R_e(M)=\sum_\zeta a_\zeta(\zeta^M-1)$ with $a_\zeta=\zeta/(\zeta-1)$ and $\sum_\zeta a_\zeta=\varphi(e)/2$.
Pronic averaging turns the primitives into the von Mangoldt function and the residues into
logarithms:
$$
\sum_{M\ge 1}\frac{\operatorname{Re}R_e(M)}{M(M+1)}=-\Lambda(e),\qquad
\sum_{M\ge1}\frac{M\bmod m}{M(M+1)}=\log m,\qquad
\sum_{M\ge 1}\frac{L_N(M,c)}{M(M+1)}=-\mathcal R(c),\quad \mathcal R(c)=\sum_{e=2}^{N}\Lambda(e)\,Y_{N,c}(e),
$$
the last being the **von Mangoldt readout** of the row. The pronic weight sums against
characters in closed form: $\sum_{M\ge1}z^M/(M(M+1))=1+Q(z)$ with $Q(z)=(1-z)\log(1-z)/z$ on the
closed disk.

The **pronic Gram matrix** $\mathcal G(e_1,e_2)=\sum_M R_{e_1}(M)R_{e_2}(M)/(M(M+1))$ represents
the pronic-weighted squared discrepancy. Its **energy-centered** form uses
$F^{\mathrm{ec}}_e=R_e+\Lambda(e)$, has pronic mean zero, and satisfies
$\mathcal G=\Lambda\Lambda^{\top}+\mathcal G^{\mathrm{ec}}$ with $\mathcal G^{\mathrm{ec}}\succeq 0$;
its **mean-centered** form $\mathcal G^{\mathrm{mc}}$ uses $R_e+\varphi(e)/2$, and with
$D(e)=\varphi(e)/2-\Lambda(e)$ the three are related by
$\mathcal G^{\mathrm{ec}}=\mathcal G^{\mathrm{mc}}-D\otimes D$ and
$\mathcal G=\mathcal G^{\mathrm{mc}}-D\otimes D+\Lambda\otimes\Lambda$. The energy-centered
**Gram form** of a row is $Q^{\mathrm{ec}}(c)=\sum Y(e_1)Y(e_2)\mathcal G^{\mathrm{ec}}(e_1,e_2)$.
The **cotangent–sawtooth form** is, with $((t))$ the sawtooth vanishing at integers,
$$
C(p,q)=\frac{\varphi(p)\varphi(q)}4-\frac\pi2\sum_{(a,p)=1}\sum_{(b,q)=1}\Bigl(\cot\frac{\pi a}p+\cot\frac{\pi b}q\Bigr)\Bigl(\Bigl(\frac ap+\frac bq\Bigr)\Bigr),
$$
the **Vasyunin sums** are $V(h,k)=\sum_{a=1}^{k-1}\cot(\pi a/k)\,((ha/k))$, and the **Vasyunin
prime kernel** is $K(p,q)=\mathcal G^{\mathrm{ec}}(p,q)$ written in them. The **discrete
Báez-Duarte Gram** is $\mathrm{bdGram}(1/m_1,1/m_2)=\frac1{m_1m_2}\sum_M(M\bmod m_1)(M\bmod m_2)\,w(M)$,
and the **Báez-Duarte residual** of a row is
$\bigl\|\mathbf 1_{(0,1]}-\sum_{n\le N}c(n)\rho_{1/n}\bigr\|^2$ with $\rho_\alpha(x)=\{\alpha/x\}$.

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
counterparts. The **cofactor row** $w_{\varepsilon,Q}$ carries the power-damped Ramanujan weights
$Y_\varepsilon(q)=\operatorname{Re}\sum_{m\ge1}\mu(qm)(qm)^{-1-\varepsilon}$ as its Selberg
coordinates at level $Q+1$; the pronic mean of its prefix discrepancy is the **energy mean**
$m(\varepsilon,Q)$ and the pronic variance the **energy variance** $V(\varepsilon,Q)$.

**The damping chain.** The same damped source has a probabilistic reading, and it is exact. The
Cesàro transform of the damped divisor transition,
$$
P_\eta(n,k)=\frac kn\Bigl(k^{-\eta}\,\mathcal A_\eta\!\left(\lfloor n/k\rfloor\right)
-(k+1)^{-\eta}\,\mathcal A_\eta\!\left(\lfloor n/(k+1)\rfloor\right)\Bigr),
$$
with $\mathcal A_\eta$ the damped divisor prefix, is a **stochastic kernel on the positive states**
at every $\eta\ge0$: its rows are nonnegative, supported on $k\le n$, of total mass one, with
diagonal $P_\eta(n,n)=n^{-\eta}$, and they compose exactly, $P_sP_t=P_{s+t}$ — an algebraic
identity for all real parameters and a Markov semigroup law for nonnegative ones. As the starting
state grows the rows converge to the **entrance law**
$$
e_\eta(k)=\rho_\eta\,k\bigl(k^{-1-\eta}-(k+1)^{-1-\eta}\bigr),\qquad \sum_{k\ge1}e_\eta(k)=1,
\quad\rho_\eta=\operatorname{Re}\frac1{\zeta(1+\eta)} ,
$$
the discrete derivative of the zeta power law, size-biased by $k$. Its **entrance tail**
$\sum_{k>N}e_\eta(k)$ and the row's **total variation** against it are the absolute observables of
the chain; the **reciprocal observable** divides out the size bias and telescopes exactly. The
damping is the chain's time parameter, so the receiver's damping limit $\varepsilon\to0^+$ is the
chain's small-time limit.

The **Fermi–Nyman cells** $I_n=(\frac1{n+1},\frac1n]$ have Lebesgue measure $\frac1{n(n+1)}$: the
pronic measure is Lebesgue measure on $(0,1]$ read through the cells. The cell response of a row
is $2\sum_{k\le n/2}s_{N,c}(k)-\sum_{k\le n}s_{N,c}(k)$, and the power-damped Fermi–Nyman source
of the Mellin picture equals minus this response on each sub-horizon cell. In this way the
$L^2(0,1]$ energy of the analytic source and the pronic energy of the arithmetic prefix are one
quantity.

### 2.9 Cross-scale objects

The bilinear form of the receiver between a **small-scale row** $c$ (moduli $\sim P$) and a
**large-scale row** $c'$ (moduli $\sim Q$) is the **cross-scale form**
$$
B(c,c')=\sum_{M\ge1}\frac{V_c(M)V_{c'}(M)}{M(M+1)},\qquad V_c(M)=\mathcal R(c)-\sum_nc(n)\frac{M\bmod n}{n},
$$
so that $B(c,c)=Q^{\mathrm{ec}}(c)$ and $B(\delta_p,\delta_q)=\mathcal G^{\mathrm{ec}}(p,q)/(pq)$ at primes.
Split $V_c=m(c)+F_c$ into the **mean** $m(c)=\mathcal R(c)-\sum_nc(n)(n-1)/(2n)$ and the
**fluctuation** $F_c$, and $V_{c'}(M)=\mathcal R(c')-MH(c')+\sum_nc'(n)\lfloor M/n\rfloor$ into ramp
and steps, $H(c')=\sum_nc'(n)/n$; put $\beta(c)=\sum_MF_c(M)/(M+1)$. The **rank-two part** is
$-m(c)\mathcal R(c')-\beta(c)H(c')$ and the **remainder** is $B+m\mathcal R'+\beta H'$.

The **residue potential** $\Phi_d(M)=\frac{d^2-1}{12}-\frac{\rho(d-\rho)}2=\frac{d^2}2B_2(\rho/d)-\frac1{12}$,
$\rho=M\bmod d$, is the second primitive of the centred residue; the **Bernoulli kernel**
$\mathfrak B(d,n)=\sum_{j\ge1}\Phi_d(jn)/j^2$ depends only on $n\bmod d$, has maximum
$\mathfrak B(d,0)=\pi^2(d^2-1)/72$ and **kernel mean** $m_d=\frac1d\sum_r\mathfrak B(d,r)=\sum_j(\gcd(j,d)^2-1)/(12j^2)$.
The **cubic potential** $\Psi_d$ ($\Psi_d(M+1)-\Psi_d(M)=\Phi_d(M+1)$, period sum zero) gives the
**cubic kernel** $\mathfrak B_3(d,n)=\sum_j(2\Psi_d-\Phi_d)(jn)/j^3$, odd under $\rho\mapsto d-\rho$. For the
large-scale row put $S'=\sum_nc'(n)/n^2$, the **residue masses** $\rho_{c'}(d,r)=\sum_{n\equiv r\,(d)}c'(n)/n^2$,
the **residue discrepancy** $\Delta_d(c')=\sum_r\lvert\rho_{c'}(d,r)-S'/d\rvert$, and the **kernel
statistic**
$$
\Lambda_d(c')=\sum_n\frac{c'(n)}{n^2}\bigl(\mathfrak B(d,n)-m_d\bigr)+\sum_n\frac{c'(n)}{n^3}\mathfrak B_3(d,n),
$$
whose sum $\sum_{d\in S}\lvert\Lambda_d(c')\rvert/d$ is the **dual norm** of the cross-scale functional on
the modulus set $S$. **Type-II** inputs are arbitrary bounded small-scale coefficients; **Type-I**
large-scale rows are flat (sharp cutoff) or smooth, measured by the smoothness norm
$\mathcal S_L(c')=\sum_{t\le L}\sum_n\lvert\Delta^tc'(n)\rvert/n^{L+2-t}$. A bound is of **diagonal
quality** when the remainder is at most the Cauchy–Schwarz diagonal; the cross-scale exponent is
$\theta=2\log P/\log Q$, and the receiver sits at $\theta=2$.

### 2.10 Glossary

| object | formula | Lean |
|---|---|---|
| response | $s_{N,c}(k)$ | `sieveSeq N c k` |
| harmonic mode | $\mathcal H_N(c)=Y_{N,c}(1)$ | `finiteHarmonicSum N c` |
| Selberg coordinate | $Y_{N,c}(e)$ | `selbergMultiplesCoord N c e` |
| Ramanujan inverse | row realizing prescribed $Y$ | `pmRamanujanResidueCoeff` |
| response frequencies, Selberg support, recurrence complexity | $T_N$, $\{Y\ne0\}$, $\sum\varphi$ | `responseRoots`, `selbergSpectralSupport`, `selbergRecurrenceComplexity` |
| cyclotomic incidence polynomial and order | $Q_N$, $\Phi(N)$ | `cyclotomicIncidencePolynomial`, `cyclotomicIncidenceOrder` |
| variance, successor covariance, reserve | §2.4 | `sieveVariance`, `sieveSuccessorCovariance`, `sieveSuccessorReserve` |
| phase loss, primitive energy, primitive spectral coefficient | §2.4 | `successorPhaseLoss`, `sievePrimitiveEnergy`, `primitiveSpectralCoeff` |
| lag multiplier, visibility clock, lag sign | $\lambda_q(h)$, $q/\operatorname{rad}q$, $\pm1$ | `sieveLagMultiplier`, `lagVisibilityClock`, `lagSign` |
| lag cone generators, cone membership | $G_h$ | `lagConeGenerators`, `InLagCovarianceCone` |
| tuple response, variance, structure factor | §2.4 | `tupleResponse`, `tupleVariance`, `tupleStructureFactor` |
| zero-product tuples, relation coefficient, layer admissibility, layer count | §2.4, §2.6 | `zeroProductTuples`, `relationCoeff`, `IsLayerAdmissible`, `layerCount` |
| prefix discrepancy | $L_N(M,c)$ | `sievePrefixDiscrepancy N M c` |
| centered sawtooth, its weighted sum | $\tilde B_1(d,n)$, $W_{N,c}(n)$ | `centeredDiscreteSawtooth`, `weightedCenteredSawtoothSum` |
| interior sawtooth sum, interior prefix | §2.3 | `bezoutInteriorSawtoothSum`, `pmBezoutInteriorPrefix` |
| successor incidence count, sawtooth defect | §2.5 | `bezoutIncidenceCount`, `bezoutSawtoothDefect` |
| renormalized defect | $R_N(M;c)$ | `sieveRenormalizedPrefixDefect` |
| observability constant, sandwich and transfer constants | $S_N$ | `sieveWindowObservabilityConstant`, `IsWindowSandwichConstant`, `IsTranslatedMomentTransferConstant` |
| pronic sequence | $n(n+1)$ | `pronicSeq` |
| power-damped row and coefficient | $c_\varepsilon$, $\tau_\varepsilon$ | `pmPowerDampedRealWeight`, `pmPowerDampedDivisorCoeff` |
| centered prefix, discrete energy | $A_\varepsilon$, $E_T(\varepsilon)$ | `pmPowerDampedCenteredDivisorPrefix`, `pmPowerDampedDivisorDiscreteEnergy` |
| interior energy | $E^{\mathrm{int}}_T(\varepsilon)$ | `pmBezoutInteriorPronicEnergy` |
| Ramanujan primitive, pronic Gram | $R_e(M)$, $\mathcal G$, $\mathcal G^{\mathrm{ec}}$ | `pmRamanujanPrimitive`, `pmRamanujanPrimitiveGram`, `pmRamanujanEnergyCenteredGram` |
| sawtooth, Vasyunin sum, prime kernel | $((t))$, $V(h,k)$, $K(p,q)$ | `sawtooth`, `vasyuninSum`, `vasyuninPrimeKernel` |
| von Mangoldt readout | $\mathcal R(c)$ | `vonMangoldtReadout` |
| dilation profile | $\Phi_r(c)$ | `pmRamanujanDilationProfile` |
| least Bézout seed | least $(a,b)$ with $pa=qb+1$ | `leastSuccessorSeed p q` |
| Fermi cell response | §2.8 | `fermiCellResponse` |
| GCD–LCM modular class | §2.6 | `IsGcdLcmModular`, `radicalPrimeProd` |
| cross-scale form, residue potential, Bernoulli kernel | $B(c,c')$, $\Phi_d$, $\mathfrak B$ | `rowBilinear`, `residuePotential`, `bernoulliKernel` |
| Witt ghost coordinate, ghost row, Frobenius, Verschiebung | $g_w(q)$, $c_w$, $F_2$, $V_m$ | `nativeWittGhost`, `wittSieveReceiver`, `deningerBigWittFrobeniusTwoRingHom`, `nativeWittVerschiebung` |
| cubic potential and kernel, residue discrepancy, kernel statistic | $\Psi_d$, $\mathfrak B_3$, $\Delta_d$, $\Lambda_d$ | `cubicPotential`, `cubicKernel`, `residueDiscrepancy`, `kernelStatistic`, `kernelStatisticAll` |

---

## 3. How: the mechanisms

The mechanisms are listed in logical order. Each is an exact identity or a sharp finite
inequality; the asymptotic statements of §3.8 and §3.10 all rest on one of them.

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

**Every lag horizon has a finite cone.** The lag weight $c_e(j)$ is multiplicative in the mode
and vanishes when $e/\gcd(e,j)$ is not squarefree. Splitting $e=gr$ into $h$-smooth and rough
parts, lags $1\le j\le h$ see $c_e(j)=\mu(r)c_g(j)$ while $c_e(0)=\varphi(g)\varphi(r)$; a smooth
part not dividing $(h!)^2$ is invisible to every lag in $[1,h]$; and with $p_h<p_h'$ the first two
primes beyond $h$ the rough part is absorbed, $v_e=av_g+bv_{gp_h}$ with
$b=(\varphi(r)-\mu(r))/p_h$ and $a=\mu(r)+b$, both nonnegative. Hence for every $h$ the cone of all
$(\mathrm{Cov}(0),\dots,\mathrm{Cov}(h))$ is generated by the explicit modes
$G_h=\{g\ge2:g\mid(h!)^2\}\cup\{gp_h:g\mid(h!)^2\}\cup\{p_hp_h'\}$, all realized once the cutoff
contains them, and a linear lag inequality $\sum_{j\le h}\alpha_j\mathrm{Cov}(j)\ge0$ is universal
iff it holds on the generators: $G_1=\{2,6\}$ gives the lag-one law above, $G_2$ contains
$\{2,3,4,6,12\}$ and gives $0\le\mathcal V_{(0,1,2)}\le4V$.

Adding the primitive energy, the least energy at prescribed $(V,C)$ is
$\max\bigl(5V+2C,\ 6V+4C,\ 6V+12C\bigr)/12$ for $N\ge 6$, with edges supported on the mode pairs
$\{2,3\},\{3,4\},\{4,6\}$; the four modes $\{2,3,4,6\}$ realize every boundary point, and
prime modes escape every upper bound of the energy by the variance ($J_2(p)/\varphi(p)=p+1$).
For a $k$-tuple $H$ the structure factor obeys $p\,S_p(H)=\sum_r(p\,\nu_H(p,r)-k)^2$ at primes,
and **Montgomery's inequality** $S_q(H)\ge k^2\prod_{p\mid q}(p-c_p)/c_p$ for squarefree $q$ when
$H$ occupies $c_p$ classes modulo each $p$ (Parseval over the $p$-th roots and Cauchy–Schwarz at
a prime, multiplicative along coprime factors because the primitive roots of order $pq$ are the
products of those of orders $p$ and $q$). A Hardy–Littlewood admissible tuple therefore has
$\mathrm{Var}_H(c)\ge k^2\sum_{q\text{ squarefree}}Y(q)^2/\varphi(q)$. Translation by $h$ maps the
row space to itself exactly when every active order $q$ has $q/\gcd(q,2)\mid h$ (then
$\zeta^h$ is constant on the primitive $q$-th roots and the translated coordinates are $\pm Y(q)$);
at $h=1$ this is closure only on $\{1,2\}$.

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

### 3.4 Observability at every phase: the cyclotomic recurrence and the quadratic horizon

**Prefix inversion.** The discrepancy on the initial prefix $M\in[1,n]$ at level $N=n+1$ determines
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
$\frac{2d}{d-1}(\tau(d)-1)$. Around a common return $R$ (all $d\le N$ divide $R$) the discrepancy
reflects with defect $\mathcal H_N(c)-\sum c(d)$; the window $[R-(N-2),R+(N-1)]$ of length
$2N-3$ detects every non-constant row, while on the window of length $2N-4$ the kernel is
one-dimensional, spanned by the normalized second-difference weight supported on
$\{1,N-2,N-1,N\}$. The least period of the signal of a row is the lcm of its active divisors;
signed cancellation never shortens it. In the dual picture
$L_N(M,c)^2\le V\cdot\sum_{e\ge 2}\operatorname{Re}R_e(M)^2/\varphi(e)$, attained by an explicit
row, and the right-hand energy vanishes iff every $e\le N$ divides $M$.

**The cyclotomic recurrence.** Each indicator $k\mapsto\mathbf 1_{d\mid k}$ is $d$-periodic, so
$E^d-1=\prod_{q\mid d}\Phi_q$ kills it ($E$ the unit shift); hence every level-$N$ response and
every prefix discrepancy satisfy the same linear recurrence $Q_N(E)s=0$ of order $\Phi(N)$,
whatever the row, and $Q_N$ is the shortest universal recurrence, because the shifts of
$\mathbf 1_{d\mid\cdot}$ are the $d$ residue-class indicators and distinct cyclotomics are
coprime. A monic recurrence propagates vanishing forward and responses are $N!$-periodic, so at
**every** phase $A$: the response vanishes on $[A,A+\Phi(N))$ iff the row vanishes on $[1,N]$,
and the discrepancy vanishes there iff the variance vanishes. In spectral form $P(E)$ kills a
response iff $\prod_{Y(q)\ne0}\Phi_q\mid P$, so the shortest recurrence of a row has order equal
to the totient mass of its Selberg support, and a class of rows with Selberg support in $S$ is
determined at every phase by $\sum_{q\in S}\varphi(q)$ consecutive values. The universal
horizon $\Phi(N)\le N(N+1)/2$ is quadratic with no logarithm; the common-return horizon $2N-3$
shows it is not sharp for the discrepancy at special phases.

**The window sandwich at quadratic order.** The response frequencies are $1/N^2$-separated, since
a nontrivial $m$-th root of unity is at distance at least $1/m$ from $1$. Smoothing a window by a
trapezoid, the average of $L$ box windows of length $K'$, makes the off-diagonal kernel of an
exponential sum $u(k)=\sum_{\zeta\in T_N}a(\zeta)\zeta^k$ a product of two geometric sums of size
at most $4/\lvert z-1\rvert^2$, and squared reciprocal distances of a $\delta$-separated family sum
to at most $4/\delta^2$, so
$\bigl\lvert\sum_{i<L}\sum_{j<K'}\lvert u(T_0+i+j)\rvert^2-LK'\sum\lvert a\rvert^2\bigr\rvert\le N^4\sum\lvert a\rvert^2$.
Squeezing a box between trapezoids with ramps $L=N^2$ gives, at every phase, length and offset,
$$
\Bigl\lvert\sum_{A<k\le A+K}(s(k)-\kappa)^2-K\bigl((H-\kappa)^2+V\bigr)\Bigr\rvert\ \le\ (2N^2-1)\bigl((H-\kappa)^2+V\bigr).
$$
The constant is sharp in order: at a common return every modulus divides $k$, so the **flat
Selberg row** ($Y(q)=1$ for $2\le q\le N$, $Y(1)=0$) has mean zero, variance $\Phi(N)-1$ and the
spike $s(N!)=\Phi(N)-1$; it attains the pointwise bound $(s(k)-H)^2\le(\Phi(N)-1)V$ with
equality, and its one-point window forces every sandwich constant to be at least $\Phi(N)-2$.
The optimal sandwich constant lies in $[\Phi(N)-2,\ N(N-1)]$, the upper end from the two-sided
Montgomery–Vaughan window bound over the $1/(N(N-1))$-separated response frequencies
(`WindowSandwichWithTheMontgomeryVaughanConstant`): exact order $N^2$, ratio at most $\pi^2/3+o(1)$.
The all-ones row shows the same for every inverse $\ell^1$ constant, $\|c\|_1^2\le C\,Q_{\mathrm{Sel}}$
needs $C\ge\Phi(N)$, and finite Ramanujan inversion gives $\|c\|_1\le\sum_q\sigma(q)\lvert Y(q)\rvert$,
hence $\|c\|_1^2\le S_NQ_{\mathrm{Sel}}$ with $S_N=\sum_{q\le N}\sigma(q)^2/\varphi(q)\le e^{19/2}N^2$
(from $\sigma(q)\varphi(q)\le q^2$ and $\sum_{q\le N}(q/\varphi(q))^3\le e^{19/2}N$). Quantitative
window–period transfer starts at length $N^{2\pm o(1)}$ and no mean-square comparison reaches a
linear horizon.

**Window laws at quadratic order.** With $S=2N^2-1$, polarization of the lagged sums
$s'(k)\pm s'(k+g)$ (coefficients $Y(\operatorname{ord}\zeta)(1\pm\zeta^g)$, and
$\sum_{\zeta\text{ prim. }q}\zeta^g=c_q(g)$) gives the window covariance at every lag,
$\bigl\lvert\sum_W(s(k)-H)(s(k+g)-H)-K\,\mathrm{Cov}(g)\bigr\rvert\le SV$, uniformly in $g$. Hence
$\lvert D_W-2KR\rvert\le4SV$ for the window Dirichlet energy, the **window Poincaré inequality**
$\sum_W(s-H)^2\le D_W+5SV$ (the torus constant one survives on every window longer than $N^2$,
not only on complete periods), the pointwise bound $(s(k)-H)^2\le(\Phi(N)-1)V$, and the
**long-window dissipation**
$$
2R_W\ \le\ 4H^2-(K-10N^2)\,V:
$$
in $\ker P$ every window longer than $10N^2$ is strictly dissipative at every phase, whatever
the endpoint states. The canonical primitive obeys the same sandwich,
$\lvert\sum_WW(k)^2-KE\rvert\le SE$ with $E$ the primitive energy, and $W(k)^2\le(\Phi(N)-1)E$,
so the prefix discrepancy has its period energy on every window longer than $N^2$ up to a
relative error $N^2/K$. Abel summation against the decreasing pronic weight turns this into the
second-order **pronic tail law**
$\bigl\lvert\sum_{k>H}W(k)^2/(k(k+1))-E/(H+1)\bigr\rvert\le SE/((H+1)(H+2))$: beyond $H\ge4N^2-4$
the pronic tail lies between $E/(2(H+1))$ and $3E/(2(H+1))$.

**Moments and the degree hierarchy.** By the Chinese remainder theorem a product
$\prod_is(k+h_i)$ expands over moduli families whose joint incidence count on a window is within
one of $K/\operatorname{lcm}(d_i)$, so every translated moment of degree $m$ satisfies
$\bigl\lvert\sum_W\prod_is(k+h_i)-K\,M_m(c;h)\bigr\rvert\le\|c\|_1^m\le(e^{19/4}N\sqrt{Q_{\mathrm{Sel}}})^m$
at every phase. The exponent is exact: the flat Selberg row is bounded by $\Phi(N)$, has period
$m$-th moment at most $\Phi(N)^{m-1}$ and value $\Phi(N)$ at $N!$, so every degree-$m$ transfer
constant is at least $\Phi(N)^{m/2}/2$. Observations of degree $m$ reach their period values
only on windows of length $N^{m\pm o(1)}$; the sixth-moment protocols of the arithmetic
observation theory need windows of length $N^{6-o(1)}$. Within that horizon the period theory
transfers whole: Möbius inversion in the lag variable, $\sum_{ab=f}\mu(a)c_e(b)=f\mu(e/f)\mathbf 1_{f\mid e}$,
recovers every Selberg energy from the lags $1,\dots,N$,
$Y(q)^2=\sum_{u\le N/q}(qu)^{-1}\sum_{ab=qu}\mu(a)\mathrm{Cov}(b)$, with stability constant $H_N^2$;
one window at arbitrary phase therefore gives all Selberg energies within $H_N^2SV/K$, and the
up-to-translation recovery theorems lift to windows at unrelated unknown phases. The moment
arrays are isometric to the relation spectrum: the multi-characters of distinct zero-product
tuples are orthogonal over $[0,N!)^m$, so
$(N!)^{-m}\sum_v(M_m(c;v)-M_m(c';v))^2=\sum_{\prod\zeta_i=1}(A_c(\zeta)-A_{c'}(\zeta))^2$, and
degree-$m$ window averages within $\eta$ at shift-dependent phases give
$\|A_c-A_{c'}\|_2\le\eta+(e^{19/4}N)^m(Q_c^{m/2}+Q_{c'}^{m/2})/K$, with constants independent of
$N$ once $K$ exceeds a fixed multiple of $N^m$; at degree two the relation spectrum is the
Selberg magnitude profile $\sum_q\varphi(q)(Y_c(q)^2-Y_{c'}(q)^2)^2$.

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

**Sign visibility is a valuation law.** All two-point data see only $Y(q)^2$, since
$\zeta_1\zeta_2=1$ forces equal orders. Rescaling the coordinates by signs $\varepsilon(q)$
multiplies the relation coefficient of a zero-product tuple by $\prod_i\varepsilon(\operatorname{ord}\zeta_i)$,
and the multi-characters of distinct tuples are independent, so the degree-$m$ moments of $Y$
and $\varepsilon Y$ agree for all shifts iff every zero-product $m$-tuple of active frequencies
has $\prod\varepsilon=1$. The sign of $Y(q)$ at odd $q\ge3$ is seen at degree three through
$\zeta\cdot\zeta\cdot\zeta^{q-2}=1$. Which order tuples carry relations is decided by layers:
raising a relation $\prod\zeta_i=1$ to the power $p^{a-1}R$, with $R$ the product of the
prime-to-$p$ parts of the orders, kills every frequency off the top $p^a$-layer and sends each
frequency on it to a nontrivial $p$-th root of unity ($-1$ when $p=2$), so the top layer has
cardinality different from one, and even when $p=2$. Conversely every layer-admissible tuple of
orders is realized by primitive roots with product one, constructed prime by prime and glued
along coprime orders. Hence **a degree-$m$ moment distinguishes $Y$ from $\varepsilon Y$ iff some
layer-admissible active $m$-tuple has $\prod\varepsilon\ne1$**: the signs on the top dyadic layer
are invisible to moments of every degree, two modes sharing their top dyadic layer with private
odd layers are relatively invisible through degree five, and $\{2p,2r\}$ for distinct odd primes
has visibility degree exactly six, through $\zeta\zeta\zeta^{p-2}\xi\xi\xi^{r-2}=1$. The cost of a
sign pattern is measured as well as decided: the mean square of the moment-array difference is
four times the energy of the zero-product relations of odd $\varepsilon$-weight.

**The ambiguity is exactly one involution.** The visibility laws close into a classification. The
relation spectrum of a row in all degrees — equivalently, by the Parseval isometry of §3.4, the
full array of translated moments in all degrees — determines the row up to a single explicit
**companion**: the reflection by the canonical half period, which flips the signs on the top
dyadic layer and fixes everything else. Two rows have the same relation spectra in degrees five
and six if and only if they have them in every degree, if and only if they agree on $[1,N]$ or one
is the companion of the other. So degrees five and six are not a convenient truncation but the
exact closure point of the hierarchy: nothing above degree six is informative, and nothing below
degree five is sufficient. The theory's observation problem therefore has a complete answer —
*additive moment data of a divisor row determine it up to one half-period involution* — and the
invisibility of the top dyadic layer is not a residual gap but the whole of the kernel. Any
mechanism that must separate a row from its companion has to leave the additive-moment coordinates
altogether; labelled moments, which break the half-period symmetry by construction, are the
corpus's instance of that.

### 3.6 Pronic duality and the Gram calculus

The pronic readout $\sum_M L_N(M,c)/(M(M+1))=-\sum_{e\ge 2}\Lambda(e)Y(e)$ is the first exact
prime-power statement obtained from a divisor row without a period. Its square is the Gram form
$\sum Y(e_1)Y(e_2)\mathcal G(e_1,e_2)$, and the decomposition
$\mathcal G=\Lambda\Lambda^\top+\mathcal G^{\mathrm{ec}}$ gives the lower bound
$\bigl(\sum_e\Lambda(e)Y(e)\bigr)^2\le\sum_M L_N(M,c)^2/(M(M+1))$. Finite horizons are controlled
by the pronic tail: a bounded sequence has pronic remainder $\le B/(H+1)$ beyond $H$, and a
sequence with bounded partial sums has remainder $\le 2B/((H+1)(H+2))$, so after subtracting the
first-order tail $\frac{\varphi(e)}{2(H+1)}$ of the mean the von Mangoldt readout holds to second
order; for the energy the second-order tail law of §3.4 applies.

**The Gram is a finite cotangent–sawtooth sum.** Since the mean-centered primitive is the pure
exponential sum $\sum_\zeta a_\zeta\zeta^M$ and the pronic weight sums characters to $1+Q(z)$,
$$
\mathcal G^{\mathrm{mc}}(p,q)=\frac{\varphi(p)\varphi(q)}4+\sum_{\zeta\text{ prim }p}\sum_{\xi\text{ prim }q}a_\zeta a_\xi\,Q(\zeta\xi),
$$
the infinite pronic series being replaced by logarithms of cyclotomic numbers $1-\zeta\xi$. The
kernel collapses: $a_\zeta a_\xi Q(\zeta\xi)=\kappa(\zeta,\xi)\log(1-\zeta\xi)$ with
$\kappa=\frac1{1-\zeta}+\frac1{1-\xi}-1$, whose real part vanishes on the circle, so the
log-moduli cancel and only arguments survive; with $\operatorname{Im}\frac1{1-e(x)}=\tfrac12\cot\pi x$
and $\arg(1-e(t))=\pi((t))$ this is $\mathcal G^{\mathrm{mc}}(p,q)=C(p,q)$ for all moduli
$p,q\ge2$. Hecke's distribution relation $\sum_{b<q}((y+b/q))=((qy))$ collapses the inner sums at
primes: $\mathcal G^{\mathrm{mc}}(p,q)=\frac{(p-1)(q-1)}4-\frac\pi2\bigl(V(q,p)-V(1,p)+V(p,q)-V(1,q)\bigr)$
and $\mathcal G^{\mathrm{mc}}(p,p)=\frac{(p-1)^2}4+\pi V(1,p)$. The same calculus evaluates the
discrete Báez-Duarte Gram for all moduli: $M\bmod m=-\sum_{0<a<m}\alpha_a(\zeta_a^M-1)$ with
$\sum\alpha_a=(m-1)/2$ and $\prod_a(1-\zeta_a)=m$, so
$$
m_1m_2\,\mathrm{bdGram}(1/m_1,1/m_2)=\frac{(m_1-1)\log m_2+(m_2-1)\log m_1}2-\frac\pi2\bigl(V(m_2,m_1)-V(1,m_1)+V(m_1,m_2)-V(1,m_2)\bigr),
$$
Vasyunin's formula, with the cross tail $\int_1^\infty\{v/m\}\{v\}v^{-2}dv$ explicit as well.

**Positivity reads cotangent sums.** $\mathcal G^{\mathrm{ec}}$ is a pronic inner product, so the
Vasyunin prime kernel $K(p,q)=\mathcal G^{\mathrm{ec}}(p,q)$ is positive semidefinite on every
finite set of primes, and the pronic covariance $S(m_1,m_2)-\log m_1\log m_2$ of residues is
positive semidefinite for all moduli. A head/tail split at $M=m$ bounds the diagonal, and
nonnegativity bounds it below:
$$
\log^2p\ \le\ \pi V(1,p)+(p-1)\log p\ \le\ 2\log^2p+p+\frac{(p-1)^2}p ,\qquad
\log^2m\le\pi V(1,m)+(m-1)\log m\le\frac{2(m-1)^2}m ,
$$
so $\sum_{a<p}a\cot(\pi a/p)=-\frac{p(p-1)}\pi\log p+O(p^2)$ with explicit constants, and the
off-diagonal bound $\lvert K(p,q)\rvert\le(K(p,p)+K(q,q))/2$ gives the **reciprocity law**
$$
(\log q-\log p)^2\ \le\ \pi\bigl(V(q,p)+V(p,q)\bigr)+(q-p)(\log q-\log p)\ \le\ (\log q-\log p)^2+O(p+q),
$$
for all moduli, with explicit error terms: the reciprocity pair of Vasyunin sums is determined up
to $O(m_1+m_2)$ by elementary terms, from pronic positivity alone. The defect is exactly the
residue-difference energy $E(p,q)$, and with $h=q-p$ it has exact order
$h(1+\log^+(p/h))/18\le E(p,p+h)\le12h(1+\log^+(p/h))$
(`ExactOrderOfTheVasyuninReciprocityDefect`): it is $o(p+q)$ exactly when $h=o(p)$, and no bound
below $O(p+q)$ holds for moduli of different sizes.

**Dilation laws.** The Gram matrix obeys exact prime-dilation laws. For $p\nmid q,r$,
$$
\mathcal G^{\mathrm{ec}}(pq,pr)+\mathcal G^{\mathrm{ec}}(pq,r)+\mathcal G^{\mathrm{ec}}(q,pr)
=(p-1)\mathcal G^{\mathrm{ec}}(q,r)+(p-1)\Lambda(q)\Lambda(r),
$$
in the mean-centered form the von Mangoldt term is replaced by $\frac{p(p-1)}4\varphi(q)\varphi(r)$,
and for primes $p,q\nmid r$
$$
\mathcal G(pr,qr)+\mathcal G(pr,r)+\mathcal G(qr,r)+\mathcal G(r,r)=\sqrt{pq}\,\Phi_r(p/q),\qquad
\lim_{p\to\infty}\sqrt p\,\Phi_r(p)=\tfrac12\varphi(r)\Lambda(r),
$$
so with $\mathcal G=C-D\otimes D+\Lambda\otimes\Lambda$ the dilation profile is explicit at every
prime ratio as a finite cotangent–sawtooth sum. For the power-damped Ramanujan weight one has
$Y_\varepsilon(pr)=-Y_\varepsilon(r)/(p^{1+\varepsilon}-1)$, and the pair $\{r,pr\}$ of adjacent
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

### 3.7 The Báez-Duarte criterion in the theory's coordinates

The Báez-Duarte residual of a row is
$1-2\sum_nc(n)\log n/n+\sum_{n,m}c(n)c(m)\,\mathrm{bdGram}(1/n,1/m)$; by Vasyunin's formula and
the pronic mean $\sum_M(M\bmod n)w(M)=\log n$ it is the pronic energy of the shifted prefix
discrepancy,
$$
\Bigl\|\mathbf 1_{(0,1]}-\sum_{n\le N}c(n)\rho_{1/n}\Bigr\|^2=\sum_{M\ge1}\frac{(1+L_N(M,c))^2}{M(M+1)}
=\bigl(1-\mathcal R(c)\bigr)^2+Q^{\mathrm{ec}}(c),
$$
the second form because the pronic mean of $L_N$ is $-\mathcal R(c)$ and $w$ has mass one. Hence
$$
\text{RH}\iff\forall\varepsilon>0\ \exists N,c:\ \sum_M\frac{(1+L_N(M,c))^2}{M(M+1)}<\varepsilon
\iff\forall\varepsilon>0\ \exists N,c:\ (1-\mathcal R(c))^2+Q^{\mathrm{ec}}(c)<\varepsilon ,
$$
an exact equivalence of RH with a statement purely about rows: steer the von Mangoldt readout to
one while the energy-centered pronic energy vanishes. The receiver of §1.3 bounds the pronic
energy of a centered prefix; the criterion asks the opposite extremal problem, approximating the
constant $-1$ by prefix discrepancies in pronic energy. The two quantities are coupled
unconditionally: there is $\kappa>0$ with
$$
(1-\mathcal R(c))^2+Q^{\mathrm{ec}}(c)\ \ge\ \frac\kappa{\log N}\qquad\text{for every row on }[1,N],\ N\ge2,
$$
from the critical zeros through the Báez-Duarte dual sequence. Since $\mathcal R(tc)=t\mathcal R(c)$
and $Q^{\mathrm{ec}}(tc)=t^2Q^{\mathrm{ec}}(c)$, minimizing over the scale gives the
scale-invariant **readout–energy uncertainty principle**
$\kappa\,\mathcal R(c)^2\le(\log N-\kappa)\,Q^{\mathrm{ec}}(c)$, and RH is equivalent to the
unboundedness of $\mathcal R(c)^2/Q^{\mathrm{ec}}(c)$ over finite rows. For the power-damped
cofactor row the residual of $-w_{\varepsilon,Q}$ is $(1-m(\varepsilon,Q))^2+V(\varepsilon,Q)$, so RH
follows if this can be made arbitrarily small, while unconditionally it is at least
$\kappa/\log(Q+1)$.

### 3.8 The sawtooth martingale calculus of the power-damped energy

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

### 3.9 Dilation profiles and the Bézout seed

The continuous profile $\Phi_r(p/q)$ equals the reciprocal pairing of the integer jump streams
of $pr$ and $qr$; finite Diophantine lag sectors approximate it with error $\le B_r^2/Q$ at the
quadratic horizon $Q^2$, and the cotangent–sawtooth form of §3.6 evaluates it exactly at every
prime ratio. A pair contributes at the gap $h=pa-qb$ only if
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

### 3.10 The literal Möbius source on linear windows

For $c=\mu$ the trans-horizon band formula gives unconditional laws on every window
$M\le(B+1)N$ with $B$ fixed.

- **Uniform first-moment cancellation.** For every $\varepsilon>0$ there is $K$ with
  $|L_N(M,\mu)|\le\varepsilon M$ and $|\sum_{k\le M}s_{N,\mu}(k)|\le\varepsilon M$ for all $N,M\ge K$,
  the two scales growing independently. The finite inequality behind it is
  $|\sum_{k\le M}s_{N,\mu}(k)|\le 1+2B\sup_{x\le(B+1)N}|M(x)|$, fed by the unconditional Mertens
  limit, and quantitatively by the Vinogradov–Korobov rate.
- **Quadratic profile.** $\frac1N\sum_{k\le(B+1)N}s_{N,\mu}(k)^2$ converges to an explicit finite
  Euler-product profile $P(B)$, monotone in $B$, equal to $6/\pi^2$ at $B=1$ and $11/\pi^2$ at
  $B=2$. Odd moments vanish in the limit; all moments have finite profiles; the source takes
  values in a finite alphabet determined by the primorial through $B+1$, every value is
  attained cofinally, and the value frequencies converge to a symmetric law whose support is
  exactly that alphabet. Both signs have positive frequency, at least
  $\frac{\text{profile}}{4C^2}N$ at horizon $(C+1)N$.
- **Gradient coercivity.** Every odd squarefree integer in $(N,2N]$ selects an adjacent edge
  ending at a multiple of four with gradient square $1$, so eventually, uniformly on
  $2N\le M\le N^A$, $R_N(M;\mu)\le -N/(2\pi^2)$, while on a fixed linear window
  $(2/\pi^2)N\le\mathcal E_N(M;\mu)\le 4A^3N$. Combined with the long-window dissipation of
  §3.4, which starts at the explicit polynomial scale where a Bertrand prime bounds the
  variance below, the renormalized Möbius defect is nonpositive at every prefix for all large
  cutoffs.

These are statements about the actual arithmetic source with no receiver hypothesis. They are
first-moment and fixed-ratio second-moment laws; none is a square-root bound.

### 3.11 Fermi cells and the trans-horizon octaves

On the cell $I_n$ the response of a row is twice its half-scale prefix minus its prefix, and
across a cell boundary it changes by $2\cdot\mathbf 1_{2\mid n+1}s(\frac{n+1}2)-s(n+1)$; by
Bézout no two consecutive boundaries both carry the dyadic term. For $c=\mu$ on the first octave
the half-scale prefix is frozen at $1$, the response is $1+\sum_{k=N+1}^{n}\mu(k)$, each jump is
$\mu(m)$, consecutive jump products are the successor correlations, and the cell energy is
$(1+\sum\mu)^2/(n(n+1))$. Uniform bounds for $M(n)-M(N)$ on $(N,2N]$ at every strict half-power
exponent are equivalent to the corresponding Mertens bounds, hence to RH. The sibling cells
$(2m,2m+1)$ satisfy an exact polarization identity, and the dyadic wavelet
$A\mapsto 2A(\lfloor n/2\rfloor)-A(n)$ reconstructs any prefix by multiscale telescoping.

### 3.12 General classes and ceilings

The algebra of §3.1 and §3.8 is not special to $\tau_\varepsilon$. Every GCD–LCM modular function
satisfies the pronic law $F(k)F(k+1)=F(k(k+1))$, the shifted law $F(k)F(k+h)=F(k(k+h))$ for
$\gcd(k,h)=1$, and the conservation law $(\Delta F)(n)^2+2F(n(n+1))=F(n)^2+F(n+1)^2$. For
$F=\prod_{p\mid n}(1-w(p))$ with $w\in[0,1]$ on primes one has divisor antitonicity,
submultiplicativity, the two-step ceiling $1-w(2)$, the three-step ceiling $(1-w(2))(1-w(3))$
from $6\mid k(k+1)(k+2)$, and for even $k$ the sharp cubic ceiling $(1-w(2))^2(1-w(3))$ from
$24\mid k(k+1)(k+2)$. The totient ratio $\varphi(n)/n$ and the Dedekind ratio $J_2/\varphi$ are
instances; at every prime $J_2(p)=(\varphi(p)-\mu(p))^2-1$ and $(q+1)\varphi(q)\le J_2(q)$ with
equality exactly at primes.

### 3.13 Cross-scale dispersion of the pronic Gram

This is the theory of mechanism 2 of the shared target: the bilinear form
$\sum_{p\sim P}\sum_{q\sim Q}a_pb_q\mathcal G^{\mathrm{ec}}(p,q)$ at one modulus, organised by how far apart
the two scales are.

**Rank two across scales.** Abel summation of the fluctuation $F_c$, whose interval sums are at most
$K_c=\sum_n\lvert c(n)\rvert n/2$, against the steps $\mathbf 1[jn\le M]$ of the large-scale row gives
$\lvert B(c,c')+m(c)\mathcal R(c')+\beta(c)H(c')\rvert\le2K_c\sum_n\lvert c'(n)\rvert/n^2$ for all rows
(`abs_rowBilinear_add_mean_add_beta_le`): across scales the receiver Gram is the rank-two form plus a
remainder smaller by $P/Q$. For two single moduli $e<q$,
$eq\,B(\delta_e,\delta_q)=D_e\log q-e\beta(\delta_e)+O(e^2/q)$ with $D_e=(e-1)/2-\log e$, and $D_e<0$
exactly for $e\in\{2,3\}$: the moduli $2$ and $3$ couple negatively to every large modulus, every
$e\ge4$ positively. For primes $\mathcal G^{\mathrm{ec}}(p,q)=(p/2)\log(q/p)+O(p)$ once $q\ge p^2$. The
unbalanced regime $Q\ge P^2$ is solved for arbitrary coefficients; the open regime is $P\le Q\le P^2$.

**Large-sieve dispersion of the remainder.** On the Farey roots the fluctuation is
$F_c(M)=\sum_{\zeta}\kappa(\zeta)\zeta^M$, and summing the pronic weight by parts turns the remainder into
the residues of the large moduli modulo the small ones. The log-free large sieve of §3.14 and the
Farey bound $\sum_{\zeta\text{ prim }p}\lvert\zeta-1\rvert^{-4}\le p^4/64$ give, for $c$ on primes $\le Q_0$
and $c'$ on a window of length $L$,
$$
\lvert B+m\mathcal R'+\beta H'\rvert\le\tfrac12\sqrt{\textstyle\sum c(p)^2p^2}\sqrt{L+2Q_0^2-1}\sqrt{\textstyle\sum c'(n)^2/n^4}+\tfrac12\textstyle\sum\lvert c(p)\rvert p^2\sum\lvert c'(n)\rvert/n^3
$$
(`abs_rowBilinear_add_mean_add_beta_le_largeSieve`), and in Selberg coordinates the same with the
Jordan weight $e^4$ for every small-scale row. For prime packets the loss is $P^{5/2}/Q^{3/2}$: the
rank-two law holds at diagonal quality with arbitrary coefficients once $Q\ge P^{5/3}$ ($\theta\le6/5$).
The cubic layer disperses the same way, because the spectral weights of the cubic potential sum to
zero at every modulus.

**The expansion of every order.** At second order the remainder is
$\sum_{n,d}c'(n)c(d)\mathfrak B(d,n)/(dn^2)$ up to $\frac34\sum\lvert c\rvert d^2\sum\lvert c'\rvert/n^3$
(`abs_rowBilinear_add_mean_add_beta_sub_bernoulli_le`), at third order the cubic kernel enters with
$1/n^3$, and at every order the potential chain of centred periodic primitives meets the
rising-factorial pronic weights $u_i(A)=(i+1)!/(A(A+1)\cdots(A+i+1))$, which satisfy
$u_i-u_i(\cdot+1)=u_{i+1}$, with error $2^L(L+1)!\sum\lvert c\rvert d^{L+1}\sum\lvert c'\rvert/n^{L+2}$. The
cosine form of $\Phi_d$ makes the kernel finite,
$\mathfrak B(d,n)=\frac{\pi^2}4\sum_{k=1}^{d-1}B_2(k/d)/\sin^2(\pi k\bar n/d)$ for $n\bar n\equiv1\ (d)$
(`bernoulliKernel_eq_reciprocity`): beyond rank two, $\sum a_pb_q\mathcal G^{\mathrm{ec}}(p,q)$ is a bilinear
form in the Kloosterman fractions $k\bar q/p$ with cosecant–Bernoulli weights, the reciprocity
$\{N/pq\}\leftrightarrow\bar p/q+\bar q/p$ at second order. The second-order coupling oscillates in sign
with $q\bmod p$ at amplitude $\asymp p^2/q$, positive near residue $0$ and negative near $p/2$; its sharp
constant $\pi^2/72$ is attained by the Bézout seeds $q\equiv1\ (\mathrm{mod}\ p)$.

**The Type-II barrier.** Double counting gives, for every modulus set $S$ and every $Q$, a point
$n_0\in[Q,Q+2D)$ near which a fixed share of $S$ nearly divides, where $\mathfrak B(d,n_0)\ge d^2/25-1/4$.
Nonnegative small-scale coefficients on that share and a large-scale row on a short window at $n_0$
attain the rank-two remainder bound up to a constant, a loss $\asymp P^{5/2}/(Q^{3/2}\sqrt{\log P})$
against the diagonal (`coherent_configuration_exceeds_diagonal`): the threshold $Q\ge P^{5/3}$ is sharp
for Type-II inputs, and it survives the side conditions $\mathcal R(c')=H(c')=0$
(`exists_readout_free_barrier`). On pronic windows $M\sim X$ the same coherence is the coherent-block
law: $k$ primes in a short interval act as one affine packet on clean regions, the large-sieve loss
$P^2/X$ is attained at every window below $P^2$, and no $\ell^2$ Type-II input reaches a window
exponent $2\log P/\log X>1$ (`exists_primeBlock_typeII_window_loss`).

**The exact loss at one modulus and parity blindness.** In residue form,
$\sum_nc'(n)\mathfrak B(d,n)/n^2=\sum_r\mathfrak B(d,r)\rho_{c'}(d,r)$, and since the kernel mean is
explicit,
$$
\Bigl\lvert B+m\mathcal R'+\beta H'-\tfrac{\pi^2}{72}S'\sum_pc(p)\tfrac{p^2-1}{p^3}\Bigr\rvert\le\tfrac{\pi^2}{72}\sum_p\lvert c(p)\rvert\tfrac{p^2-1}p\Delta_p(c')+\tfrac34\sum\lvert c\rvert p^2\sum\lvert c'\rvert/n^3
$$
(`abs_rowBilinear_add_mean_add_beta_sub_equidistributed_le`): a Type-II gain at one modulus is exactly
smallness of the $\ell^1$ residue discrepancies, at the attained rate $\pi^2/72$. Consequently the
cross-scale form sees the large scale only through its residue masses modulo the small moduli and
two readouts (`abs_rowBilinear_sub_of_residueMass_eq`): it is parity-blind, it cannot tell the primes
from matched almost-primes or $\lambda$ from $1$ on rough numbers, and parity-breaking input must come
from the large-scale self-Gram or from near-diagonal scales.

**The dual norm.** By the third-order law the remainder minus its main term is
$\sum_p(c(p)/p)\Lambda_p(c')$ up to $6\sum\lvert c\rvert p^3\sum\lvert c'\rvert/n^4$, and the sign pattern
$c(p)=\operatorname{sign}\Lambda_p(c')$ attains it (`exists_rowBilinear_sub_main_ge`): for arbitrary
bounded small-scale coefficients the cross-scale problem is exactly the size of
$\sum_{p\in S}\lvert\Lambda_p(c')\rvert/p$, one linear statistic of the large-scale row per small modulus,
with no bilinear structure left; on all moduli the same holds with the kernel mean
$0\le m_d\le(\pi^2/72)(\tau(d)-1)$. For an arithmetic row these statistics are low-frequency exponential
sums $\sum_aW_p(a)\sum_n(c'(n)/n^2)e(an/p)$. Two replacement hypotheses are proved sufficient: block
equidistribution of $c'$ at scale $o(P/\log^2P)$ (`abs_rowBilinear_add_mean_add_beta_le_block`), and, on
pronic windows, square-root cancellation of twisted prime sums over short intervals, after a discrete
Gallagher inequality shows that the window energy is the clustering energy of the row's Farey
spectrum and only numerators $a\lesssim P^2/X$ matter (`window_energy_le_twisted_short_sums`). The twisted cancellation is a
statement of the strength of the square-root barrier; block equidistribution is not, for the prime
row: the centred row $\Lambda(n)-1$ on $[Q,2Q]$ is block-equidistributed at $H\asymp Q^{\alpha}$,
$\alpha>7/12$, by Huxley's theorem in short intervals, so for every row on $(P,2P]$ its cross-scale
remainder is $16\varepsilon$ times the rank-two remainder bound throughout
$P^{1+\delta}\le Q\le P^{12/7-\delta}$, that is at every exponent $\theta\in(7/6,2)$
(`CentredPrimeRowPassesTheCoherentBlockObstruction`, with Huxley uniform in the window length,
`eventually_abs_psi_window_sub_le`); only the balanced regime $Q\asymp P$ remains.

**Type I passes the barrier one order at a time.** A flat large-scale row has
$\lvert\sum_{n\in I}\zeta^n/n\rvert\ll1/(A\lvert\zeta-1\rvert)$, and a flat small-scale row is controlled by
Kuzmin–Landau; either gives diagonal quality for $Q\ge P^{3/2}$ ($\theta\le4/3$), and sharp cutoffs stop
exactly there (`exists_sharp_cutoff_configuration`). Smooth large-scale rows cancel both kernels,
because $\mathfrak B-m_d$ and $\mathfrak B_3$ have zero residue means and periodic zero-sum sequences have
bounded primitives: a row smooth to order $K-1$ gives diagonal quality for $Q\ge P^{(K+1)/K}$, that is
$\theta=2K/(K+1)$, the sequence $4/3,3/2,8/5,\dots\to2$
(`abs_rowBilinear_add_mean_add_beta_le_smoothnessNorm`). The receiver is the limit of infinite
smoothness; the Möbius and prime rows are not smooth at any order.

**The single-modulus statistic of the actual prime row is an omitted residue class.** For a fixed
prime $p$ and the von Mangoldt row $c'_Q=\Lambda\mathbf 1_{(Q,2Q]}$ the kernel statistic depends on
$n$ only through $n\bmod p$. The coprime classes carry equal mass $W(Q)/(p-1)+o(1/Q)$ by
Dirichlet's theorem in Chebyshev form, and since the centred kernel has zero residue mean they
contribute $-(\mathfrak B(p,0)-m_p)W(Q)/(p-1)$; the class $0$ holds at most one prime power in
$(Q,2Q]$ and contributes $O(\log Q/Q^2)$. Hence
$$
Q\,\Lambda_p(c'_Q)\ \longrightarrow\ -\frac{\mathfrak B(p,0)-m_p}{2(p-1)}=-\frac{\pi^2(p^2-1)^2}{144\,p^2(p-1)}
$$
(`tendsto_mul_kernelStatistic_primeWindowRow`): the statistic of the prime row is not small, it is
the sieve term of the residue class the primes omit, of relative size $\asymp1/p$ against the
trivial bound, while a row equidistributed in every class, such as the Möbius row by the prime
number theorem in progressions, has statistic $o(1/Q)$. This is a law for fixed moduli; the dual
norm at moduli $p\sim P$ growing with $Q$ is the open question of §5.

### 3.14 Bridges to classical sieve estimates

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

**The large sieve, log-free.** The window sandwich bounds the dual large-sieve sums over the
roots of unity of order at most $Q$, $\sum_{A<k\le A+K}\lvert\sum_{\zeta\in T}a(\zeta)\zeta^k\rvert^2\le(K+2Q^2-1)\sum\lvert a\rvert^2$,
and the duality principle carries the constant to the primal Farey-point sums:
$$
\sum_{q\le Q}\sum_{(a,q)=1}\Bigl\lvert\sum_{n<N}x(n)e(an/q)\Bigr\rvert^2\le(N+2Q^2-1)\sum\lvert x(n)\rvert^2,
$$
with unit main coefficient and no logarithm, within a factor two on $Q^2$ of the
Montgomery–Vaughan constant. Gauss sums turn it into the multiplicative large sieve
$\sum_{q\le R}\frac q{\varphi(q)}\sum_{\psi\text{ prim. mod }q}\lvert\sum_{n<N}c_n\bar\psi(n)\rvert^2\le(N+2R^2-1)\sum\lvert c_n\rvert^2$,
Montgomery's combinatorial inequality gives $\lvert A\rvert\sum_{p\in P}(p-\omega_p)/\omega_p\le N+2Q^2-1$
for a set occupying $\omega_p$ classes modulo each prime, and Montgomery's inequality at
squarefree moduli gives the arithmetic large sieve
$\lvert A\rvert\sum_{q\le Q\text{ squarefree}}h(q)\le N+2Q^2-1$ with $h(q)=\prod_{p\mid q}(p-c_p)/c_p$.
The Montgomery–Vaughan cosecant inequality $\bigl\lvert\sum_{r\ne s}z_r\bar z_s/\sin\pi(\alpha_r-\alpha_s)\bigr\rvert\le\delta^{-1}\sum\lvert z_r\rvert^2$
(`HTGeometry/MontgomeryVaughanCosecantInequality`) gives the dual sums over $\delta$-separated
frequencies with constant $K+\delta^{-1}$; distinct Farey fractions and distinct roots of unity of
order at most $Q$ are $1/(Q(Q-1))$-separated, so all four statements hold with $N+Q^2-1$
(`LargeSieveWithTheMontgomeryVaughanConstant`, `ArithmeticLargeSieveWithTheMontgomeryVaughanConstant`).
The window laws of §3.4 are consumed outside the theory as well: the long-window dissipation,
with its variance bounded below by a Bertrand prime, is what makes the renormalized defect of
Möbius and damped rows nonpositive at every prefix for large horizons in the trans-horizon
theory, and the polynomial-window transfer of moments is what lifts the arithmetic observation
theory from complete periods to windows at unknown phases.

### 3.15 The receiver below half damping: the zero-free bands

The receiver $E_T(\varepsilon)$ is bounded for $\varepsilon\ge\tfrac12$ by size alone (§1.3, and the
universal law of the damped class in the trans-horizon theory). Below one half it is bounded
exactly where $1/\zeta$ is known to be zero-free, and the mechanism is a rate transfer.

**Rate transfer.** If a sign pattern $s$ with $\lvert s\rvert\le1$ has partial sums
$\lvert S(x)\rvert\le Lx$ from $D$ on, summation by parts against the antitone weights $d^{-\varepsilon}$
and $d^{-1-\varepsilon}$ in the hyperbola split of the centred prefix at $D$ gives, for
$\tfrac14\le\varepsilon\le\tfrac12$,
$$
\lvert A(n)\rvert\ \le\ 3D^{1-\varepsilon}+31\,L\,n\,D^{-\varepsilon}
$$
(`abs_weightCenteredPrefix_dampedSign_le_of_linear`): any Mertens rate becomes a prefix bound.
Fed with the de la Vallée Poussin rate $\lvert M(x)\rvert\le Bxe^{-\sqrt{\log x}/12}$ at
$D=ne^{-\sqrt{\log n}/20}$ this is $\lvert A_\varepsilon(n)\rvert\le Kn^{1-\varepsilon}e^{-\sqrt{\log n}/40}$,
and the factor $n^{1-2\varepsilon}$ is absorbed for all $n\le T$ once
$\varepsilon\ge\tfrac12-1/(80\sqrt{\log T})$; fed with the Vinogradov–Korobov rate
$\lvert M(x)\rvert\le Bxe^{-\kappa\sigma(x)/24}$, $\sigma(x)=(\log x)^{3/5}(\log\log x)^{-5/3}$, at
$D=ne^{-\kappa\sigma(n)/120}$ it is $\lvert A_\varepsilon(n)\rvert\le Kn^{1-\varepsilon}e^{-\kappa\sigma(n)/240}$.
Hence **the receiver and the Bézout interior energy are bounded uniformly in $T$ and in
$\varepsilon$ on the band**
$$
\tfrac12-\frac{\kappa\,\sigma(T)}{480\log T}\ \le\ \varepsilon\ \le\ \tfrac12
$$
(`exists_receiver_le_on_vinogradovKorobovBand`, `exists_receiver_le_on_zeroFreeBand`): the damping
unit moves from $\tfrac12$ to $\tfrac12-c/\sqrt{\log T}$ and then to
$\tfrac12-c(\log T)^{-2/5}(\log\log T)^{-5/3}$ at horizon $T$. The band is exactly the zero-free
region, in both directions: a band of fixed width would be a zero-free strip, and the corpus's
converse (zero translation of the power-damped receiver) turns any receiver bound below one half
into a zero-free half-plane. No bound reaches a fixed $\varepsilon<\tfrac12$.

**The band reads the signs.** The damped Möbius row and its parity twin $c'_\varepsilon$ (nonnegative,
squarefree-supported, with Ramanujan coefficients of equal absolute value) have identical
sign-blind data at every damping; on the band the twin's receiver is at least
$c(\log(T+1)-\log100)$ with one $c>0$ (the drift of the squarefree moduli beyond the prefix, made
uniform in $\varepsilon\in[\tfrac14,\tfrac12]$ by monotonicity of $\rho_\varepsilon$ and of the twin's
local factors), while the Möbius receiver is bounded (`parityPair_separated_on_vinogradovKorobovBand`).
The parity barrier of the trans-horizon theory therefore has its visibility witness on the band:
the bound is paid by the zero-free region of $1/\zeta$, that is by the signs of $\mu$. In the same
way the receiver of a multiplicative weight with $\lvert f\rvert\le1$ is decided at the primes on
the band: $f(p)=-1$ at every prime gives a bounded receiver uniformly on the band (through the
critical Wiener factorization $f=(f\star1)\star\mu$ and the finite convolution law of the
trans-horizon theory), $f(p)=+1$ with $f\ge0$ gives $E_T\ge(\log(T+1)-\log100)/1024$ at every
$0<\varepsilon\le\tfrac12$ (`exists_receiver_le_on_vinogradovKorobovBand_of_primes_neg_one`,
`receiver_ge_log_of_primes_one`).

**The pronic weighting carries exactly the Vinogradov–Korobov factor.** At fixed
$\varepsilon\in[\tfrac14,\tfrac12)$ the period energy of the damped row grows like $N^{1-2\varepsilon}$
(the top octave of moduli acts as $N^{1-2\varepsilon}$ independent unit steps, §3.4 and the
trans-horizon growth law), while the receiver, the pronic energy of the prefix below the first
period, satisfies
$$
E_T(\varepsilon)\ \le\ C_\varepsilon\,T^{1-2\varepsilon}e^{-\kappa\sigma(T)/270},\qquad
\frac{E_N(\varepsilon)}{\mathcal E_{\mathrm{prim}}(N)}\ \le\ Ce^{-\kappa\sigma(N)/270}\to0
$$
(`eventually_receiver_le_growth`, `eventually_receiver_le_mul_periodEnergy`; split at $\sqrt T$,
where above it $\sigma(n)\ge\tfrac49\sigma(T)$). The prefix below the period carries a cancellation
the period torus does not have, and its unconditional size is the zero-free region. A growth
exponent below $1-2\varepsilon$ at one fixed $\varepsilon<\tfrac12$ would be a zero-free strip.

**Selectivity.** The de la Vallée Poussin width $(\log T)^{-1/2}$ is the most a Beurling system
can guarantee (Diamond–Montgomery–Vorhauer); the Vinogradov–Korobov band is wider by the factor
$(\log T)^{1/10}(\log\log T)^{-5/3}$, and the extra width is paid by Vinogradov's mean value
theorem, that is by the additive structure of $\mathbb N$. The band is the first receiver
statement of this programme that is selective against Beurling systems.

### 3.16 The damping chain: compactness, the entrance tail, and the residual cusp

The chain of §2.8 gives the damped source an operator calculus, and the calculus locates the
obstruction precisely where the martingale analysis puts it: in the signed source, not in the
absolute size of the rows.

**Centering, compactness and the semigroup.** Coordinatewise convergence of the stochastic rows to
the entrance law upgrades to convergence in absolute sum, by the counting form of Scheffé's
theorem: $\sum_k\lvert P_\eta(n+1,k+1)-e_\eta(k+1)\rvert\to0$. Hence the **centered operator**
$\mathring P_\eta=P_\eta-e_\eta$, acting on sequences vanishing at infinity, is bounded with norm at
most two — only positivity and the two unit masses are used — and truncating its output coordinates
converges to it in operator norm, so $\mathring P_\eta$ is a **compact operator on $c_0$** at every
positive damping. Centering is compatible with composition: the finite transition composes with no
hypothesis on the input, the centering discrepancy is a coordinate-constant, and both outputs vanish
at infinity, so the constant is zero and the centered operators form the exact positive-time
semigroup $\mathring P_s\mathring P_t=\mathring P_{s+t}$. The argument never interchanges two
infinite sums, which is why the positive-state convention is kept explicit.

**The entrance tail is the absolute barrier, and only the absolute one.** Size bias converts the
exact reciprocal tail into a lower bound for the probability tail,
$$
\rho_\eta\,(N+1)^{-\eta}\ \le\ \sum_{k>N}e_\eta(k),
$$
so the entrance tail — and with it the $\ell^1$ row error and the total variation, which dominate it
— has **non-square-summable** decay at every damping $\eta\le\tfrac12$. The reciprocal observable
behaves oppositely: its omitted tail is square-summable at every positive damping, with the
damping-free majorant $1/N$. The threshold $\tfrac12$ of the chain is therefore a statement about
absolute row control, not about the source the receiver reads: total variation is the wrong norm
below half damping, and the observable that survives is the one with the size bias removed.
Compactness, likewise, is a statement on $c_0$ and not on the pronic $\ell^2$ where the critical
energy lives.

**The residual has a linear cusp.** The Báez-Duarte residual of the damped source at finite horizon,
$R(\varepsilon,T)=\sum_{n\le T}(\tilde{\mathcal A}_\varepsilon(n)-1)^2/(n(n+1))$, admits an
unconditional positive floor linear in the damping: there are $\kappa>0$ and $\delta>0$ with
$$
\kappa\,\varepsilon\ <\ R(\varepsilon,T)\quad\text{for some finite }T,\qquad
\text{every }0<\varepsilon<\delta,
$$
and the constant is supplied by a critical zero, $\kappa=1/(4\lvert\rho\rvert^2)$. The mechanism is
a step-source Mellin identity for the residual read on the reciprocal unit interval: the step
correction contributes $-r\,\zeta(s)/s$ rather than the continuous pole term, and evaluating at
$s=\rho+\varepsilon$ makes a critical zero detect the residual **at distance exactly the damping**.
Neither RH nor admission is assumed, and the statement is about finite horizons. So the approach to
the Báez-Duarte infimum cannot be faster than linear in the damping: any route that needs
$R(\varepsilon,T)=o(\varepsilon)$ is refuted, and the zeros on the line are what refutes it.

---

## 4. Traps and sharp boundaries

| trap | correct statement |
|---|---|
| Pronic reach is cancellation. | $d\mid n(n+1)$ for some $d\in(M,M(M+1)]$ says nothing about $L_N(M,c)$: a single modulus $d>M$ contributes only the drift $-Mc(d)/d$. |
| A symmetric return window determines the row. | The window $[R-(N-2),R+(N-3)]$ of length $2N-4$ has a one-dimensional kernel; the asymmetric window of length $2N-3$ is needed. |
| Observability needs a period or a common return. | At every phase, $\Phi(N)\le N(N+1)/2$ consecutive responses determine the row and $\Phi(N)$ discrepancies decide the variance; a support class needs only its totient mass. |
| A sharper window sandwich reaches the linear horizon. | The optimal sandwich constant has exact order $N^2$ (flat Selberg row at a common return); linear observability, if true, is an incidence-algebraic statement no mean-square comparison sees. |
| Degree-$m$ statistics transfer at the quadratic horizon. | The degree-$m$ transfer horizon is $N^{m\pm o(1)}$; sixth-moment protocols need windows of length $N^{6-o(1)}$. |
| Window constants carry a logarithm. | The sandwich constant $2N^2-1$, the inverse $\ell^1$ constant $e^{19/2}N^2$ and the window covariance bound at every lag are log-free. |
| Compressed lags form a semigroup. | $\lambda_q(h_1+h_2)\ne\lambda_q(h_1)\lambda_q(h_2)$; at $p^{a+1}$ all lags below $p^a$ are erased and two of them revive the mode with defect $-1/(p-1)$; even on squarefree support $\lambda_q(2)-\lambda_q(1)^2=-3/4$ at $q=3,6$. |
| Quadratic or bounded-degree data determine the row. | All two-point data see $Y(q)^2$; sign visibility is a valuation law: the top dyadic layer is invisible at every degree, $\{2p,2r\}$ needs degree six, and every layer-admissible relation is realized. |
| Higher-degree moments narrow the ambiguity further. | Degrees five and six already close the hierarchy: equal relation spectra there are equal in every degree, and the residual ambiguity is exactly the half-period companion. More degrees buy nothing. |
| Universal lag inequalities need infinitely many checks. | For every lag horizon the covariance cone is finitely generated by explicit modes; an inequality is universal iff it holds on the generators. |
| Short windows read valuation phase. | Observing $t\mapsto\gcd(k+t,p^a)$ on fewer than $\varphi(p^a)$ points cannot distinguish $k=1$ from $k=1+p^{a-1}$; the threshold $\varphi(p^a)$ is sharp. |
| The raw Möbius defect is small. | The unrenormalized combined defect at $M=N$ exceeds every $CN^\alpha$, $\alpha<1$; only the renormalized defect, which keeps the diagonal main term, is bounded. |
| Multiplicative identities can close the problem. | Möbius inversion, Euler products, Gibbs log-submodularity and one-large-prime splits hold for every Beurling system, some of which violate RH. Closure needs $pa-qb=1$. |
| Fixed-depth cancellation. | Within a prime star $\{pr\}$ the Möbius sign is constant and nearby-prime terms $Y(pr)Y(qr)\mathcal G^{\mathrm{ec}}(pr,qr)$ are all positive; the depth-$k$ truncation of $1/\zeta(s+\varepsilon)$ still has the singularity at $1-\varepsilon$. Cancellation is coherent across depths only (§3.6). |
| The pronic Gram is an infinite, analytic object. | It is a finite cotangent–sawtooth sum in two moduli; its positivity alone yields the cotangent moment law and the Vasyunin reciprocity law with explicit errors. |
| The three Grams are interchangeable. | $\mathcal G$, $\mathcal G^{\mathrm{ec}}$ and $\mathcal G^{\mathrm{mc}}$ differ by rank-one terms in $\Lambda$ and $\varphi/2-\Lambda$; positivity holds for $\mathcal G^{\mathrm{ec}}$, the dilation laws change their inhomogeneous term with the centering. |
| The Báez-Duarte criterion is foreign to the theory. | Its residual is the pronic energy of $1+L_N(M,c)$, equal to $(1-\mathcal R(c))^2+Q^{\mathrm{ec}}(c)$; RH is an exact statement about rows. |
| The damped Báez-Duarte residual can be made $o(\varepsilon)$. | It cannot: a critical zero gives the unconditional floor $\kappa\varepsilon$ with $\kappa=1/(4\lvert\rho\rvert^2)$ at arbitrarily small damping and some finite horizon (§3.16). The approach to the infimum is at best linear in the damping. |
| Total-variation convergence of the chain's rows controls the receiver. | The entrance tail is at least $\rho_\eta(N+1)^{-\eta}$, so neither it nor the total variation is square-summable for $\eta\le\tfrac12$; what is square-summable at every positive damping is the reciprocal observable's omitted tail, majorant $1/N$. The obstruction is absolute row control, not the signed source. |
| Compactness of the centered transition bounds the critical energy. | Compactness holds on $c_0$; the receiver is a pronic $\ell^2$ quantity and no $c_0$ statement reaches it. |
| A small readout defect or a small centered energy alone is progress. | They are coupled by the unconditional floor $\kappa/\log N$ and the uncertainty principle $\kappa\mathcal R^2\le(\log N-\kappa)Q^{\mathrm{ec}}$; only their simultaneous decay is RH. |
| Summation by parts is an estimate. | Along $n$ it is the product rule in reverse and returns $E_T$ with coefficient $1$; it never yields $(1-\delta)E_T$. |
| Changing the kernel is harmless. | Replacing $w_T(n)=\frac1{n+1}-\frac1{T+1}$ by $H_T-H_n$, or dropping the second difference of the active component from $\tilde\tau_\varepsilon(n+1)=\Delta I_\varepsilon(n)+\Delta^2S_\varepsilon(n)$, changes the target. |
| Misreading the damping quantifiers. | The receiver asks: for every $\delta>0$ some $\varepsilon<\delta$ and some $B_\varepsilon<\infty$ with $E_T(\varepsilon)\le B_\varepsilon$ for all $T$. The constant may depend on $\varepsilon$; divergence of constants as $\varepsilon\downarrow 0$ is no obstruction. Conversely $\prod_p(1+p^{-1-2\varepsilon})=\zeta(1+2\varepsilon)/\zeta(2+4\varepsilon)$ is not an estimate of the energy. |
| First-octave exactness is cofinal control. | $s_{N,\mu}=-\mu$ on $(N,2N]$ and the cell energies there are exact identities; they bound nothing beyond the octave. |
| Period statements bound prefixes. | Variance, covariance and reserve are period quantities; a prefix of length $N$ carries the signed defects and endpoint squares in addition, and the window laws start at length $N^2$. |
| Absolute values early. | Bounding the signed modulus sum of compensated interior atoms by absolute coefficients is not uniform in the cutoff; signed coupling must be retained. |
| Far-apart scales decouple. | Only for $Q\ge P^{5/3}$ with arbitrary coefficients; below, coherent near-multiples attain the rank-two remainder bound, and the barrier survives $\mathcal R(c')=H(c')=0$. |
| The cross-scale form can break parity. | It sees the large scale only through residue masses modulo the small moduli and two readouts; matched almost-primes and $\lambda$ against $1$ on rough numbers have the same form. |
| Flat or smooth rows model the prime row. | Type-I gains are exactly one order per order of smoothness ($\theta=2K/(K+1)$); sharp cutoffs stop at $\theta=4/3$; Möbius and prime rows are not smooth. |
| The second-order coupling has a sign. | It oscillates with $q\bmod p$ at amplitude $\asymp p^2/q$: positive near residue $0$, negative near the half. |
| $\Lambda_d(c')$ is the von Mangoldt function. | In the cross-scale theory it is the kernel statistic of the large-scale row at the modulus $d$. |
| The window exponent and the cross-scale exponent are one unit. | On a pronic window $\theta=2\log P/\log X$ and no $\ell^2$ Type-II input passes $1$; across two scales $\theta=2\log P/\log Q$ and Type II reaches $6/5$. Name the coordinates. |
| A Mertens rate bounds the receiver at a fixed $\varepsilon<\tfrac12$. | It moves the damping unit only to $\tfrac12-(\text{rate})/\log T$ at horizon $T$; a band of fixed width is a zero-free strip, and every receiver bound below one half is a zero-free region. |
| The single-modulus statistics of the prime row are small. | At fixed $p$ they are $\asymp p/Q$, the sieve term of the omitted residue class $0$; only rows equidistributed in every class modulo $p$ have $o(1/Q)$. |
| Dilation $k\mapsto pk$ alone reads enough of the signs. | A Kátai-type single-modulus law saves only $(\log\log)^{-1/2}$ and is dominated by the $\ell^2$ large-sieve dispersion except at $P\asymp Q$. |
| Frobenius on Witt ghosts is a free operation at a fixed horizon. | $g_{F_2w}(q)=g_w(2q)$, so a ghost statement at horizon $N$ is a Selberg statement at horizon $2N$; the cutoff is consumed, not preserved. |
| The Witt ring structure is an extra estimate. | It is an exact dictionary: the ghost row's sieve norm is the totient-weighted ghost energy and the operations are finite coordinate moves. Whether it yields a bound the Selberg coordinates do not already give is open. |

**Lean conventions.** Capstones are stated on data parameters and carry no analytic premise;
where a finite statement has hypotheses they are arithmetic side conditions on the data
(a prime, a coprimality, a horizon inequality, a damping range, a layer condition). Theorems
that conclude `RiemannHypothesis` are implications whose premise is one explicit finite
inequality on $E_T(\varepsilon)$ or on an equivalent bracket, or equivalences of the Báez-Duarte
type; the corpus never asserts such a premise. Window statements are universally quantified
over the phase. Analytic inputs (Mertens, Vinogradov–Korobov, the prime number theorem, divisor
moments, the Báez-Duarte criterion and its dual sequence) are proved corpus theorems, not
assumptions. Every module says in its header what its bounds do not prove.

---

## 5. The frontier

**The receiver.** For every $\delta>0$ exhibit $\varepsilon\in(0,\delta)$ with
$\sup_TE_T(\varepsilon)<\infty$. Equivalently, exhibit such $\varepsilon$ with $\sup_TE^{\mathrm{int}}_T(\varepsilon)<\infty$,
or with the strict interior contraction of §3.8. Known for every $\varepsilon\ge\frac12$ and on
the zero-free bands $\varepsilon\ge\tfrac12-\kappa\sigma(T)/(480\log T)$ below it (§3.15), open at
every fixed $\varepsilon<\frac12$; a bound at one fixed $\varepsilon<\frac12$ is a zero-free
half-plane statement and every band of fixed width a zero-free strip, so no routine bookkeeping
can supply it. On the period torus the primitive energy of the damped row grows like
$N^{1-2\varepsilon}$ for $\varepsilon<1/2$, and the receiver is smaller than it by exactly the
Vinogradov–Korobov factor, so the bound, if it exists, is carried by the pronic weighting of
small arguments below the first period, and its unconditional size is the zero-free region.

**The dual problem.** RH is also the statement that rows exist whose shifted prefix discrepancy
has arbitrarily small pronic energy, equivalently with readout near one and vanishing centered
energy, equivalently with unbounded ratio $\mathcal R(c)^2/Q^{\mathrm{ec}}(c)$. The unconditional
floor is $\kappa/\log N$. Whether rows attain $O(1/\log N)$, which would be a quantitative form
of RH, and whether the power-damped cofactor rows have $(1-m(\varepsilon,Q))^2+V(\varepsilon,Q)\to0$
along some path $\varepsilon\to0$, $Q\to\infty$, are the open questions on this side; both
require signed input across moduli.

**What the energy is made of.** After the canonical drifts are subtracted, the active-deleted
diagonal and the predecessor-peak bracket are bounded for every positive damping; the whole
obligation sits in the Bézout interior martingale $M^{\mathrm{int}}_T$, whose required
cancellation rate per $\log T$ has small-damping slope $\ge 7/24$. The interior is a sum of
signed atoms along progressions $n\equiv-1\ (d)$ with exactly known conditional means; what is
missing is the signed sum over moduli.

**The four tools.** Each known obstruction names a tool.

1. *Cross-depth cancellation.* Built at the level of exact identities (hypercube factorization,
   finite $\zeta\cdot\zeta^{-1}=1$ cancellation, natural-cutoff head/mean/tail split), and the
   Gram is now explicit as a cotangent–sawtooth sum. Missing: a bound on the resulting Dirichlet
   form of the profile that is uniform in the cutoff.
2. *Bézout coupling at high scale.* The least seed $pa=qb+1$ is isolated inside the profile
   with inverse-scale error, its complete fibre has mass $r\mu(r)$, and the profile is evaluated
   exactly at every prime ratio. Missing: control of the signed complement of all other lags, or
   of a signed prime packet, not only of a cofinal family of nearby prime pairs.
3. *Internal bilinear dispersion.* The reciprocity $\{N/pq\}\leftrightarrow\bar p/q+\bar q/p$
   converts correlations between moduli into exponential sums with modular inverses, the
   Vasyunin reciprocity law holds with $O(p+q)$ error, and the cross-scale form is explicit to
   every order (§3.13): rank two at diagonal quality for $Q\ge P^{5/3}$ with arbitrary
   coefficients, sharply; exact loss the $\ell^1$ residue discrepancy; dual norm
   $\sum_p\lvert\Lambda_p(c')\rvert/p$. At fixed moduli the statistics are known: $o(1/Q)$ for the
   Möbius row, and for the prime row the omitted-class value $-\pi^2(p^2-1)^2/(144p^2(p-1)Q)$,
   which is not small. Missing: a bound on these single-modulus statistics for the actual Möbius
   or prime row at moduli $p\sim P$ growing with $Q$ in the balanced regime $P\le Q<P^{5/3}$, that
   is on low-frequency exponential sums of an arithmetic row at the rationals $k/p$, without an
   external character or modulus average; for the prime row the omitted class must be subtracted
   first.
4. *A coercive contraction.* An inequality
   $2M^{\mathrm{int}}_T+2\,\mathrm{Counterterm}\cdot H^{\mathrm{comp}}_T\le(1-\delta)E_T+C_\varepsilon$
   with $\delta>0$, equivalent to the receiver. Identities cannot produce it; a signed
   arithmetic input across moduli must.

**The damping chain.** The chain is a Markov semigroup in the damping with a compact centered
generator on $c_0$, an exactly computed entrance law, and an entrance tail that is not
square-summable below half damping while the reciprocal observable is. What the spectrum of the
centered compact operator is, whether its eigenvalues or its small-time expansion read the zeros,
and whether the chain has a version acting on the pronic $\ell^2$ — where compactness would bear on
the receiver instead of on $c_0$ — are open. The residual's linear cusp fixes the rate on the other
side: the approach to the Báez-Duarte infimum is at best linear in the damping, with an explicit
constant from one critical zero, so a quantitative form of RH in these coordinates must be a
statement about the constant, not about the exponent.

**Other open boundaries.** The sharp observability horizon at arbitrary phase: $\Phi(N)$ is the
shortest universal recurrence and $2N-3$ holds at common returns and for $N=3,4$ everywhere; the
gap between a quadratic universal horizon and a linear special one is open, and any linear law
must be incidence-algebraic. The exact window sandwich constant in $[\Phi(N)-2,N(N-1)]$. The sign of a general signed prime packet in the energy-centered Gram.
The relation-spectrum question is closed — the spectrum in all
degrees, equivalently degrees five and six, determines a row up to the half-period companion — so
what remains there is quantitative: an explicit stability constant for that recovery on windows at
unknown phase, and the corresponding law for rows that are only approximately equal in degrees
five and six. Rates in the cofinal Möbius
laws that are uniform in the band ratio $B$; mixed-level covariances of centered pronic residue
cells, which are positive when the cells share a factor and start together.

### Research topics toward the shared target

1. **Single-modulus statistics of arithmetic rows.** The bilinear dispersion of
   `Σ_{p∼P} Σ_{q∼Q} a_p b_q 𝒢^{ec}(p, q)` (mechanism 2) is reduced exactly to the dual norm
   `Σ_p |Λ_p(c')|/p` of the large-scale row; bound it for the Möbius and prime rows at moduli
   growing with the window, through the reciprocity `{N/pq} ↔ p̄/q + q̄/p` and without an external
   character or modulus average, after subtracting the omitted-class term of the prime row
   (§3.13). The unit is the cross-scale exponent `θ = 2 log P/log Q`: Type II stands at `6/5`,
   sharp cutoffs at `4/3`, rows smooth to order `K − 1` at `2K/(K + 1)`, the receiver at `θ = 2`.
   On the damping side the unit is the band: the receiver is bounded through
   `ε = 1/2 − κσ(T)/(480 log T)` (§3.15), and every wider band is a zero-free region.
2. **The signed sum over moduli** of the interior martingale, equivalently the coercive
   contraction; identities cannot produce it.
3. **Additive window structure for the incidence face.** Bézout incidence inside a dyadic window
   `(X/2, 2X)`: which consecutive integers, residue classes and jump spacings of `{N/p}` couple the
   divisor edges that `ArithmeticIncidencePositivity` classifies multiplicatively.
4. **The parity pair** with `TransHorizonIncidenceMechanics`: what the pronic Gram and the
   divisor-sum data cannot see (mechanism 5).
5. **Selectivity.** Each exact law is arithmetic and fails for Beurling systems by construction; say
   for each estimate whether it still distinguishes `ζ` from `ζ(s−a)ζ(s+a)`.
6. **The chain on the right norm.** Carry the compactness and the semigroup law of the centered
   damped transition from `c₀` to the pronic `ℓ²`, or show no such version exists. The entrance-tail
   barrier closes the absolute norms below half damping, so whatever carries the receiver there must
   be built from the signed source; the chain's small-time expansion is the natural place to look,
   since the damping is its time.

---

## 6. Working in the theory

- **Name the coordinates and the regime first.** Raw, response, Selberg, or spectral; period,
  prefix, octave, linear band, or window at arbitrary phase, and at which horizon
  ($\Phi(N)$, $N^2$, $N^m$). Most false claims in this area are category errors between these.
- **Pass to the spectral form for window questions.** A response is an exponential sum over
  $1/N^2$-separated frequencies with Galois-invariant coefficients; separation, Parseval over
  the period and multi-character orthogonality are what the window, moment and visibility laws
  use.
- **Search before building.** The corpus already holds the exact identities for most finite
  objects of §2, and the neighbouring programmes consume this theory's window laws; a new
  estimate is a new rearrangement of an existing identity more often than a new object.
- **Identity before asymptotics.** Every logarithmic drift in §3.8 and every density in §3.10
  is a limit of an exact finite formula that retains boundary terms and signed defects. Prove
  the finite formula, then pass to the limit.
- **Keep cancellation with the main term.** Never bound a signed defect in absolute value
  before the diagonal main term has been subtracted (§3.3); never sum compensated atoms with
  absolute coefficients (§3.8).
- **Test against Beurling.** If a proposed mechanism would hold verbatim for a Beurling
  system, it cannot close the frontier. The additive input must be visible: $\gcd(n,n+1)=1$, a
  solution of $pa-qb=h$, a residue class omitted modulo $p$, a layer condition on valuations.
- **State what a bound does not prove.** A first-moment law is not a square-root law; a
  fixed-$B$ profile is not uniform in $B$; a bound for $\varepsilon\ge\frac12$ is not a bound
  below $\frac12$; an exact octave is not a cofinal estimate; a window law says nothing below
  its horizon; a floor of $\kappa/\log N$ is not a rate.
