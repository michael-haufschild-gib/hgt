# Arithmetic Resonance Theory (ART)

Namespace `GaloisForLFunctions.ArithmeticResonanceTheory`; umbrella `ArithmeticResonanceTheory.lean`.

**Question.** The zeros of $\zeta$ are *resonances*: poles of a meromorphic continuation, of
$\zeta'/\zeta$, of a scattering matrix, of a dynamical zeta function. Every positive object the corpus
owns — Haar measure, Laplacians, Dirichlet forms, Gram matrices, KMS states — has a *spectrum*, and a
resonance is a spectral point only of an operator built from the zeros. Outside positivity mathematics
knows two mechanisms that control resonances: **amplification**, which sharpens a bound that is
uniform over a family into the sharp bound at one member, and **oscillation**, which produces
resonance-free strips from cancellation in twisted transfer operators. Which realizations of the
primes can carry these mechanisms, what does each yield, and what exactly is missing over $\mathbb Z$?

ART is the theory of **realizations, resonances and amplifiers** for Euler products. Its basic object
is a *realization*: a symbolic or graph dynamical system whose primitive periodic orbits have lengths
$\log p$, so that its dynamical zeta function is $\zeta$. Its basic distinction is between a
*spectral pole* (an eigenvalue of a transfer operator crossing $1$) and a *resonance* that no
operator of the realization sees. Every statement is unconditional; RH and zero-free strips appear
only as conclusions of implications or inside equivalences.

---

## 1. Place in the research

The corpus has proved that the three walls Σ, Π, Γ are one fact read three ways: the explicit formula
is the argument principle with a holomorphic weight, it computes reflection pairings and never
same-point sums, and every positive object sees spectra. Most of what a theory of resonances needs is
already owned by programmes; two items are not: a **non-envelope amplifier**, and an **oscillation
mechanism on a realization of the primes** that escapes the Ruelle no-go. ART owns these two items and
the realization theory they require.

| Programme | Interface |
|---|---|
| ArithmeticCriticalityTheory (ACT) | Ground states and supersolutions: the positive (spectral) side ART contrasts with |
| ScaleSignedIncidenceCriticality, SquareRootThreshold, ArithmeticOrientationGeometry | Visibility, depth as a rate, rate = depth of the deepest seen zero; ART's amplifier uses the AOG self-upgrade in the iteration parameter |
| ConjugateDiagonalGeometry (CDG), HilbertianExplicitFormulas (HEF) | Same-point sums, collision quantum, explicit-image rigidity: why the explicit formula cannot see resonances as spectra |
| ArithmeticCastelnuovoSeveri (ACS) | Scaling surface, finite-field calibration, golden datum, infinite genus; ART's rank obstruction is the counting form of infinite genus |
| ArithmeticPositiveDuality | Bost–Connes temperature = Hecke exponent; the BC partition function is the commutative realization's zeta |
| DilutionCrystallizationPincer | Kronecker and Baker on the prime torus; ART uses the same independence to show oscillation fails on additive realizations |
| TransThresholdPairCorrelation (TTPC) | Tensor powers of a scale trace are prime correlations; the amplifier survivor is a signed Hardy–Littlewood moment |
| HeckeKreinToeplitz, ArithmeticKreinLangerTheory | Krein index of the Weil kernel: the resonance count as a negative-square count |
| `RHTower` dynamical zetas | `RuelleZetaNuclearZeroFree`: nuclear analytic expanding Markov zetas are zero-free on $\Re s>\sigma_0-1$, $\zeta$ is not one of entropy $\le1$ |
| `HTGeometry` symbolic dynamics | `SymbolicRuellePollicott`: Hölder suspensions of mixing subshifts continue as reciprocals of holomorphic functions to $\Re s>1-\varepsilon$ |
| `RHTower` envelopes and Landau | `DensityEnvelopeNoGo`, `ZetaMultipleLandauZeroFree`, Chen–Gupta–Li modules: the existing amplifier attempts |

---

## 2. Why

**Resonances, not spectra.** A self-adjoint operator has real spectrum and a positive form has a
sign; the zeros of $\zeta$ are neither. They are poles of the continuation of $-\zeta'/\zeta$, which is
not the resolvent of any operator built without the zeros. The explicit formula, the only bridge from
primes to zeros, is holomorphic and rigid: a holomorphic weight agreeing with $|F|^2$ on the critical
line equals $F\cdot F^\#$, so no test function makes it compute a same-point (spectral) sum. Hence
positivity arguments meet the zeros only at the endpoint, where the sign is RH itself.

**Two mechanisms that do not need positivity.** (i) *Amplification.* Deligne's proof of the Weil
conjectures bounds one Frobenius eigenvalue by a moment over a family of tensor powers: each family
member contributes non-negatively, the total is bounded with a loss that does not grow with the tensor
power, and taking roots removes the loss. (ii) *Oscillation.* Dolgopyat's estimate contracts twisted
transfer operators $\mathcal L_{\sigma+it}$ uniformly in $|t|$, which pushes resonances of a dynamical
zeta off a strip. Both act on resonances directly. ART asks what each needs over $\mathbb Z$.

**Realizations.** Oscillation needs a transfer operator, so it needs a *realization*: a dynamical
system whose primitive periodic orbits have lengths exactly $\log p$. Two realizations exist for free.
The *commutative* one (one loop of length $\log p$ for each prime) has zeta
$\prod_p(1-p^{-s})^{-1}=\zeta(s)$, but its transfer operator is diagonal, not mixing, and its pole at
$s=1$ is a breakdown of nuclearity, not an eigenvalue crossing. The *free* one (one vertex, a loop for
each prime) is mixing, but its zeta is $1/(1-P(s))$, $P(s)=\sum_p p^{-s}$, with entropy
$\sigma^\ast>1$: it overcounts. Every realization lies between commutativity (right zeta, no dynamics)
and freeness (dynamics, wrong zeta). Unique factorization forbids concatenating orbits additively;
integrality forbids concatenating them too smoothly. ART makes both statements sharp.

**The payoff and its price.** A realization by a Hölder suspension of a mixing finite-type subshift
would make $\zeta$ the reciprocal of a holomorphic function on $\Re s>1-\varepsilon$, i.e. give a
zero-free strip; no such strip is known. A realization by a nuclear analytic expanding map would give
too much (zero-freeness on $\Re s>0$), and the corpus excludes it. ART locates the admissible
regularity between these, by arithmetic rather than by analysis.

**Amplifiers.** Over $\mathbb F_q$ the family loss in Deligne's argument is $q^{\dim\text{base}}$ per
iteration, independent of the tensor power, because a curve has finite genus: the degree-$k$
monomials in $2g$ Frobenius eigenvalues number $\binom{2g+k-1}{k}$, polynomial in $k$. Over
$\mathbb Z$ the rank is infinite: at scale $x$ the monomials in $\pi(x)$ prime phases number
$\binom{\pi(x)+k-1}{k}$, and an orthogonal family must be at least that large. ART proves that this
size exactly cancels the gain, so orthogonality alone is an envelope; a non-envelope amplifier over
$\mathbb Z$ must obtain its moment bound from an identity, not from counting.

---

## 3. Objects and language

| Object | Meaning |
|---|---|
| Length spectrum | primitive lengths $\ell_\gamma>0$ with multiplicity; for $\zeta$: $\{\log p\}$, each once |
| Dynamical zeta | $Z(s)=\exp\sum_{n\ge1}n^{-1}Z_n(s)$, $Z_n(s)=\sum_{\sigma^nx=x}e^{-sS_n\varphi(x)}$ |
| Realization | a shift space (finite or countable alphabet) with roof $\varphi>0$ whose primitive periodic orbits have $e^{S\varphi}$ prime, each prime once |
| Additive realization | weighted directed graph: the roof is locally constant (an edge weight) |
| Commutative realization | disjoint loops of length $\log p$; transfer operator diagonal with eigenvalues $p^{-s}$ |
| Free realization | one vertex with a loop of length $\log p$ for every prime; zeta $1/(1-P(s))$ |
| Spectral pole | a pole of $Z$ at which $1$ is an eigenvalue of $\mathcal L_s$ (Perron–Frobenius crossing) |
| Nuclearity pole | a pole created by divergence of $\sum\|\text{eigenvalues}\|$, with spectral radius $<1$ |
| Even / odd part | $Z=\det(1-\mathcal L^-_s)/\det(1-\mathcal L^+_s)$; poles from the even part, zeros from the odd part |
| Junction distortion | $\varepsilon_n(u,v)=S\varphi(u^nv)-nS\varphi(u)-c(u,v)$ along a cycle family $u^nv$ |
| Conformal defect | $m_n=p_{n+1}-p\,p_n$ for $p_n=e^{S\varphi(u^nv)}$, $p=e^{S\varphi(u)}$; an integer in a realization of the primes |
| Conformal threshold | distortion of size $e^{-nS\varphi(u)}=p^{-n}$; *super-conformal* below it, *sub-conformal* above it |
| Dolgopyat modulus | $\rho(\sigma,T)=\sup_{|t|\ge T}$ spectral radius of $\mathcal L_{\sigma+it}$, relative to $t=0$ |
| Amplifier | a family $(a_x(n))_{x\in X}$ of real traces, an iteration parameter $n$, a tensor power $k$, and moment bounds $\sum_x a_x(n)^{2k}\le C_kB^{2kn}D_k^{\,n}$ |
| Fixed-loss / envelope | $D_k^{1/2k}\to1$ / $D_k^{1/2k}\not\to1$ |
| Brauer family at level $k$ | the degree-$k$ monomials of the family's phases are orthogonal over the family |
| Rank | number of independent phases a family must separate: $2g$ over $\mathbb F_q$, $\pi(x)$ over $\mathbb Z$ at scale $x$ |

**Words.** *Realizes*: has the primes as primitive length spectrum. *Mixing*: some power of the
transition matrix is positive. *Super-conformal*: junction distortion $o(p^{-n})$. *Pole-killing*:
removing the trivial (pole) contribution from a family moment. *Loss exponent*:
$\lambda=\liminf_k (2k)^{-1}\log D_k$.

---

## 4. Mechanisms

1. **Euler product = commutative realization.** $\exp\sum_n n^{-1}\sum_p p^{-ns}=\zeta(s)$ on $\Re s>1$. The
   diagonal transfer operator has spectral radius $2^{-\sigma}<1$ for every $\sigma>0$ and trace norm
   $P(\sigma)$, finite exactly for $\sigma>1$: the pole of $\zeta$ is a nuclearity pole.
2. **Renewal = free realization.** Words in the primes give $Z_n=P(s)^n$ and $Z=1/(1-P)$; $P$ decreases
   from $+\infty$ at $1^+$ to $P(2)<\pi^2/6-1<1$, so the free realization has a spectral pole at a unique
   $\sigma^\ast\in(1,2)$: free dynamics has the wrong entropy.
3. **Unique factorization forbids additive concatenation.** In a weighted graph, two first-return loops
   at a vertex concatenate to a closed walk of weight $\log(pq)$, which is not the logarithm of a prime.
   Additive realizations are commutative.
4. **Even realizations have no zeros.** For a finite graph with edge weights,
   $Z(s)=1/\det(I-M(s))$, $M(s)_{ij}=A_{ij}e^{-sr_{ij}}$: poles only. Zeros need an odd part. Over $\mathbb F_q$ the
   odd part is $H^1$, finite dimensional, and its eigenvalues are the zeros (calibration).
5. **Integrality forbids smooth concatenation (Pisot).** If $p_n=e^{S\varphi(u^nv)}$ are integers and
   $p_{n+1}/p_n=p\,e^{\delta_n}$ with $p\,\delta_n\cdot p^{n}\to0$, the integers $p_{n+1}-p\,p_n$ tend to $0$, so
   $p_{n+1}=p\,p_n$ eventually: composite. A θ-Hölder roof has $|\delta_n|\le K\theta^{n|u|}$.
6. **Affine recurrences meet a member (Cunningham).** If $p_{n+1}=a\,p_n+m$ for large $n$ with $a\ge1$,
   then modulo the prime $\ell=p_N$ the map $x\mapsto ax+m$ is a permutation; its orbit returns to $0$, so
   $\ell$ divides a later, larger member. Primes obey no eventual affine recurrence, nor an eventually
   periodic conformal defect.
7. **Pollicott continuation.** A Hölder suspension of a mixing subshift has
   $Z=1/F$ with $F$ holomorphic on $\Re s>1-\varepsilon$: no zeros there. A realization of $\zeta$ of this type is a
   zero-free strip.
8. **Simultaneous approximation defeats oscillation on additive data.** For finitely many lengths, Dirichlet's
   theorem returns all phases $e^{-it\ell_i}$ to $1$ at arbitrarily large $t$, so the twisted sum returns to the
   untwisted one: the Dolgopyat modulus at the abscissa is $1$ for every $T$. For the free prime realization
   the same holds with a tail estimate (the prime torus is Kronecker-dense).
9. **Amplification.** Positivity of each member plus a moment bound with loss $D_k$ gives
   $\max|\alpha|\le B\inf_kD_k^{1/2k}$ by the rate–depth law for finite exponential sums; fixed loss gives the
   sharp bound, loss exponent $\lambda$ gives a strip of width $\lambda$.
10. **Orthogonality costs its gain.** A Brauer family at level $k$ on $r$ phases has at least $\binom{r+k-1}{k}$
    members (orthogonal nonzero vectors), and by Cauchy–Schwarz with the multinomial theorem the bound it
    yields for $\sum_pa_pw_x(p)$ is never below the trivial bound $\sum_pa_p$. At finite rank the loss
    $\binom{r+k-1}{k}^{1/2k}\to1$; at rank $\pi(x)$ it is the whole gain.

---

## 5. Pillar theorems

1. **The two realizations.** The commutative realization realizes $\zeta$, is not mixing, and its pole is a
   nuclearity pole; the free realization is mixing with a spectral pole at $\sigma^\ast\in(1,2)$.
2. **Additive rigidity.** Every additive realization of the primes is commutative: no vertex carries two
   first-return loops.
3. **Parity.** Finite even realizations are zero-free; $\zeta$ and every curve zeta of genus $\ge1$ need an odd part.
4. **Conformal threshold.** No realization of the primes has a super-conformal cycle family; at the conformal
   rate, an eventually periodic conformal defect is impossible. For a θ-Hölder roof:
   $\theta^{|u|}e^{S\varphi(u)}\ge1$ along every cycle $u$ with a re-entry $v$.
5. **Realization ⇒ strip.** A realization of $\zeta$ by a Hölder suspension of a mixing finite-type subshift
   implies $\zeta(s)\ne0$ on $\Re s>1-\varepsilon$.
6. **Oscillation fails on additive and free realizations.** Their Dolgopyat modulus at the abscissa is $1$.
7. **Amplifier law.** Fixed loss ⇒ sharp individual bound; loss exponent $\lambda$ ⇒ bound $Be^{\lambda}$; the
   bound is attained, so envelope losses are strip widths.
8. **Rank law.** Orthogonality amplifiers never beat the trivial bound; their loss tends to $1$ exactly at
   finite rank.

---

## 6. Traps

| Trap | Truth |
|---|---|
| $\zeta$ is the zeta of the prime dynamics | Of the commutative realization only, which has no dynamics |
| Mixing the prime orbits keeps $\zeta$ | Free mixing gives $1/(1-P)$ with entropy $\sigma^\ast>1$ |
| The pole at $1$ is a Perron–Frobenius eigenvalue | In the commutative realization the spectral radius is $\le\tfrac12$; the pole is a nuclearity breakdown |
| Oscillation gives the strip | In a finite-type Hölder realization the strip comes from the continuation itself; the zeros of $\zeta$ are not transfer-operator resonances there. The difficulty is the realization |
| A smoother roof is a better realization | Integrality forbids super-conformal roofs; smoothness beyond the conformal threshold is excluded |
| Analytic expanding maps fail only for entropy reasons | They are conformal with an asymptotic expansion along $u^nv$, which Cunningham excludes (inference) |
| Independent lengths help oscillation | Kronecker independence returns all phases at once; additive data never contract uniformly |
| A family moment with a small constant amplifies | Only the growth of the loss in $k$ matters; envelope losses give strips at best |
| Orthogonality is the amplifier's engine | Orthogonality pays for itself exactly; gains need an identity |
| Big monodromy is the missing structure | At the level of counting the missing structure is finite rank; $\mathbb Z$ has infinite genus |
| Realization obstructions are analytic | ART's obstructions use integrality of $e^{\ell}$; they fail for Beurling systems, as they must |

---

## 7. Questions the programme answers

1. **Realization.** Which dynamical systems realize $\zeta$, and what does each class yield (strip, too much,
   nothing)? Classify by regularity of the roof along cycle families.
2. **Oscillation.** On which realizations does a twisted transfer operator contract uniformly, and is
   oscillation needed for a strip at all?
3. **Amplification.** What converts a family bound into the sharp individual bound; which structure replaces
   big monodromy over $\mathbb Z$; what does an envelope loss yield?
4. **Resonance–spectrum dictionary.** When is a pole of a dynamical zeta spectral, when is it a nuclearity
   pole, where do zeros come from (parity), and how does the $\mathbb F_q$ calibration read each entry?
5. **Graded versus critical.** Which conclusions of each mechanism are strips (rates) and which are the line
   (exact), and where the two meet.

## 8. Tools to build

- A realization calculus: periodic data, cycle families $u^nv$, junction distortion, conformal defects.
- Arithmetic obstructions to realizations: Pisot (integrality) and Cunningham (affine recurrence modulo a member).
- The realization–strip bridge through the Pollicott continuation.
- Oscillation diagnostics: Dolgopyat modulus, simultaneous-approximation returns on the prime torus.
- The amplifier calculus: rate–depth for finite exponential sums, loss exponents, pole-killing.
- The rank law for orthogonal families: minimal family size, Cauchy–Schwarz cancellation of the gain.

## 9. Open research topics

1. **The Mills boundary.** At the conformal rate with bounded, non-periodic conformal defect the arithmetic
   obstructions stop: does a prime sequence $p_n=Cp^n+O(1)$ exist? A realization of $\zeta$ by a Hölder
   finite-type suspension needs such sequences along every cycle family.
2. **Sub-conformal realizations.** Construct or exclude realizations whose junction distortion decays more
   slowly than $p^{-n}$ along every cycle family; relate the slowest admissible rate to the strip width
   Pollicott would give.
3. **Countable alphabets.** Realizations over the infinite prime alphabet (the Bost–Connes classical system):
   Gurevich pressure, continuation and the role of oscillation when the transfer operator is not quasi-compact.
4. **Identity amplifiers over $\mathbb Z$.** Family moments computed by an explicit formula on a single total
   space, whose loss is fixed in $k$; the signed Hardy–Littlewood moment of TTPC as the level-2 instance.
5. **The odd part.** A virtual realization $\zeta=\det(1-\mathcal L^-_s)/\det(1-\mathcal L^+_s)$ with both determinants
   defined on a region containing the critical line; its relation to the Krein index and to Σ6.
6. **Amplifier audit of Chen–Gupta–Li.** Classify its loss: fixed, envelope, or rank-limited.

## 10. Success criteria and contributions

**Success.** A strip or the line from a mechanism of ART, or a classification that closes a mechanism with a
sharp boundary and a formalized positive survivor: the realization classes that remain, the amplifier
losses that remain, and the exact arithmetic statement each would need.

**A contribution** is unconditional and formalized; is stated in realizations, cycle families, transfer
operators, families and losses; says what it gives over $\mathbb F_q$ (curves: lattice lengths $d\log q$,
finite odd part), on the golden datum, on Beurling systems and on the free realization; uses integrality or
unique factorization where it claims selectivity for $\mathbb Z$; separates graded conclusions (rates, strips)
from critical ones (the line); and records the positive survivor of every no-go.

**Battery.** Curves over $\mathbb F_q$ (calibration); the golden datum $1-5X+5X^2$ (fake curve); Beurling
systems with zeros near $\Re s=1$ (non-integral lengths); the free prime realization; locally constant roofs.

**Principles.** Resonances are not spectra; a realization is a theorem, not a picture; integrality is margin;
only the growth of a loss matters; orthogonality is not amplification; calibrate over $\mathbb F_q$.
