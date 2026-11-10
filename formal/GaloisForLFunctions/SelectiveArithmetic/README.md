# Selective Arithmetic (SA)

Namespace `GaloisForLFunctions.SelectiveArithmetic`; umbrella `SelectiveArithmetic.lean`.

## 1. Motivation

Every route of the corpus to the Riemann hypothesis ends at one statement, a sign with no positive
margin, and every route is a *receiver*: it converts the sign into zeros on the line, or the zeros
into the sign. For each mechanism that proves a statement of this type elsewhere (Weil, Deligne,
Stepanov, Lee–Yang, Hermite–Biehler, heat flow, Turán, duality, recurrence) the corpus holds a
theorem that fixes what the mechanism gives over $\mathbb Z$. What no programme contains is a
*producer*: a theorem that yields the sign, the count or the bound at a contact, at unbounded
scale, for a reason that is not a transport of the classical zero-free region, of a density
theorem, of rigidity or of a verified height.

Selective arithmetic is the theory of producers. It does not add an equivalent of RH. It asks,
for a candidate inequality and a candidate mechanism:

* **Is the inequality selective?** Does it fail for a system that shares all structures of $\zeta$
  but one? An inequality that holds for every system of a class carries no information about the
  member of the class.
* **What is its price?** Up to which scale does a mechanism that sees only one structure (sizes
  of the contacts, positivity of counts, the functional equation, the Euler product) prove it?
* **Where is the smallest instance beyond the price?** The first scale at which the inequality
  holds for the true object and fails for a fake.

The answer is organised by *aspects*. A system has a mass (the logarithm of its conductor, or of
the height of a packet) and an aperture (half the logarithmic length of a window). In each aspect
there is a *trivial aperture* below which the sign holds for every system with contacts of the
same size, and a fake that fails immediately beyond it. The programme locates these boundaries
exactly, shows that they carry no gap, and classifies what a statement beyond them must use.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Weight system | `w : ℕ → ℝ`; `RHTower.weilAtomSymbol w N` | contacts $w(n)$ at $\pm\log n$ against the archimedean symbol |
| Packet | `f : ℝ → ℝ`, $C^2$, support in $[c-a,c+a]$ | a real divisor of a window of aperture $a$ in the scale limit |
| Contact form | `contactForm w f N` | $\sum_{2\le n\le N} w(n)\,n^{-1/2}\cdot 2\,(f\star\tilde f)(\log n)$ |
| System form | `systemForm w q f a` | $\frac1{2\pi}\int|\hat f|^2\,(S_\infty+\log q)-$ contact form: jets, counterterm $\log(qn/2\pi)$, contacts $w$, no pole plane |
| Twisted part | `AbsoluteGeometryOfSpecZ.twistedZeroSum` | the system form of $w=\Lambda\operatorname{Re}\chi$ with the conductor of $\chi$; equals $Z_\chi(f)$, the sum over the zeros of $L(s,\chi)$ |
| Dominated box | `Dominated w` | $|w(n)|\le\Lambda(n)$: the systems with contacts of the size of the primes |
| Feasible set | `RHTower.WeilPositiveFullUpTo w a` ($\mathscr A(a)$, with pole plane); `Feasible q a w` (conductor $q$, no pole plane) | weight systems whose form is nonnegative at aperture $a$ |
| Price | `price w a` | the least $\log q$ at which $w$ is feasible at aperture $a$ |
| Trivial aperture | `trivialAperture q` | the supremum of the apertures at which the whole dominated box is feasible |
| Fakes | `liouvilleWeight`, `fun n => -Λ n`, `fun n => Λ n` | completely multiplicative signs without a conductor; the system of $1/\zeta$; the contacts of $\zeta$ without its pole plane |
| Exceptional square | — | one negative square of a twisted part: a real zero $\beta>\tfrac12$ contributes $2\tilde f(\beta)\tilde f(1-\beta)$ |
| Chart | — | a receiver read on the plane of depth and mass: which zeros a sign at aperture $a$ excludes |

## 3. Language

- **Structure**: one of the properties of $\zeta$ that a fake may drop: the sizes of the contacts,
  their signs, complete multiplicativity, the conductor (periodicity, the functional equation),
  the pole plane, the constant $2\pi$ of the counterterm, the jets.
- **Selective**: an inequality that holds for $\zeta$ (or for a true $L$-function) and fails for a
  system sharing all structures but one. **Selective at unbounded scale**: selective on windows
  whose aperture is unbounded in the aspect.
- **Source**: the input from which an unconditional selective inequality is proved: exponential
  sums, mean values, rigidity, the additive identity of the fractional part, nonnegativity of the
  ideal counts.
- **Price** of a mechanism: the largest aperture, as a function of the mass, to which it proves
  the sign. **Slack** of a statement: the weakest form in which it still implies its conclusion.
- **Aspect**: the parameter that carries the mass: the conductor $q$ of a character (mass
  $\log q$); the height $t$ of a modulated packet (mass $\log t$).
- **Trivial aperture**: where the mass pays every dominated contact system. **Ladder**: the
  apertures $\kappa\cdot\log(\text{mass})$, $\kappa>0$, of an aspect.
- **Exceptional square**: a negative square of the form of a true object beyond the trivial
  aperture. **Removable**: excluded by a mechanism that fails on the fake.
- **Receiver / producer**: a theorem that converts the sign into information on zeros or back / a
  theorem that proves the sign.

## 4. Mechanisms

**The form of a system.** On a packet $f$ supported in $[-a,a]$ the form of the system $(w,q)$ is
$$\mathfrak W_{w,q}(f)=\frac1{2\pi}\int|\hat f(\tau)|^2\Big(S_\infty(\tau)+\log q\Big)\,d\tau
-\sum_{2\le n\le e^{2a}}\frac{w(n)}{\sqrt n}\cdot2\,(f\star\tilde f)(\log n),$$
with $S_\infty(\tau)=\operatorname{Re}\psi(\tfrac14+\tfrac{i\tau}2)-\log\pi\ge\psi(\tfrac14)-\log\pi$.
For a primitive character $\chi$ of conductor $q$ and $w=\Lambda\operatorname{Re}\chi$ it is the sum
over the zeros of $L(s,\chi)$ (plus a nonnegative energy when $\chi$ is odd): GRH for $\chi$ is its
nonnegativity at every aperture. The system of $\zeta$ has $q=1$ and a pole plane.

**The mass pays the sizes: the Schur price.** The contact form is the quadratic form of the
operator $f\mapsto\sum_n w(n)n^{-1/2}\big(f(\cdot+\log n)+f(\cdot-\log n)\big)$ on $L^2[-a,a]$. For
$w=\Lambda$ its kernel is, by the prime number theorem, $e^{|u-v|/2}$: semi-separable, with top
eigenfunction $\cosh(u/2)$ and top eigenvalue $e^{a}(1+o(1))$
(`BiScaleUncertainty.tendsto_windowCeiling_div_exp`). The pointwise bound of the symbol,
$2\sum_{n\le e^{2a}}\Lambda(n)n^{-1/2}\approx4e^{a}$, loses the factor $4$: a packet supported in
$[-a,a]$ cannot correlate with itself at lags close to $2a$. With the weight $\cosh(u/2)$ the
Schur test gives, for every dominated system,
$|\text{contact form}|\le\big((1+\varepsilon)e^{a}+O_\varepsilon(1)+(1+2a)^2\big)\int f^2$.

**The trivial aperture.** Hence $\mathfrak W_{w,q}\ge0$ on every packet of aperture $a$ as soon as
$(1+\varepsilon)e^{a}+(1+2a)^2+K_\varepsilon\le\log q$: the whole dominated box is feasible up to
the aperture $\log\log q-o(1)$. In particular the twisted part of the square of a quadratic ring
is nonnegative there, with a margin of the order of $\log q$, for every primitive character.

**The fake beyond it.** The Liouville twist $w(p^k)=(-1)^k\log p$ has the sizes of a real
character, is completely multiplicative and has values $\pm1$; it has no conductor. On the odd
polar packet $\sinh(u/2)$, cut off smoothly, its contact form is $\le-(1-\varepsilon)e^{a}\int f^2$:
its form with any conductor $q$ has a negative square at aperture $\log\log q+o(1)$. The same
holds for $w=-\Lambda$ (the system of $1/\zeta$, a zero at $s=1$) and, on the even polar packet
$\cosh(u/2)$, for $w=\Lambda$ without pole plane. So the ladder of the conductor has **no gap**:
the trivial aperture is $\log\log q+o(1)$, sizes prove nothing beyond it, and the first statement
beyond it — the sign at aperture $\log\log q+C$, $C>0$ — is selective: it separates a character
from the Liouville twist by the periodicity of $\chi$ on the integers between $\log q$ and
$e^{2C}\log^2q$.

**The exceptional square.** A real zero $\beta=\tfrac12+d$ of $L(s,\chi)$ and its reflection
contribute $2\tilde f(\beta)\tilde f(1-\beta)$ to the twisted part: a form of rank two and
signature $(1,1)$ on $L^2[-a,a]$ with smallest eigenvalue $-(\sinh(2da)/d-2a)$, attained on
$\sinh(du)$. The Liouville twist is the limit case $\beta=1$.

**The ladder of an aspect.** At the aperture $\kappa\log(\text{mass})$ an isolated zero of depth
$d$ is visible when $2d\kappa>1$. Below $\kappa=1$ every zero of the strip is invisible and the
sign is trivial; a zero-free strip of width $\delta$ is the sign at $\kappa=1/(1-2\delta)$; the
classical zero-free regions lie at $\kappa=1+o(1)$.

**Feasible sets.** With the pole plane, $\mathscr A(a)$ is convex, closed, depends on the weights
$w(n)$, $n\le e^{2a}$, only, is bounded in these coordinates, decreases in $a$, and RH holds iff
every $\mathscr A(a)$ is nonempty; a common point is $\Lambda$
(`RHTower.riemannHypothesis_iff_forall_level_exists_weilPositiveFullUpTo`). A window of ratio
$\le2$ does not see the weights (`HodgeTheoryOfAFixedPart.combFormW_eq_combForm_of_window`).

## 5. Questions

| # | Question | State |
|---|---|---|
| Q1 | Which unconditional theorems of the corpus are selective at unbounded scale, and from which sources? | the atlas of §7; in the conductor and the height aspect every unconditional sign statement lies below the trivial aperture |
| Q2 | Is there a source beyond exponential sums, mean values, rigidity and the additive identity of the fractional part? | open; a source must pass the trivial aperture of an aspect and fail on its fake |
| Q3 | Can a feasible weight system be constructed at every aperture? | with a conductor: the dominated box, to the trivial aperture, and no further for the box; with the pole plane: RH |
| Q4 | Is the exceptional square removable? | the gap of the conductor ladder is closed from both sides; what remains is the sign at $\log\log q+C$, which is the Landau–Siegel problem on the comb |
| Q5 | What is the first selective window? | every window of ratio $>2$: the feasible interval of $w(2)$ is bounded at every aperture $>\tfrac12\log2$ |

## 6. Tools

- **The contact operator and its Schur test**: polar weights $\cosh$, the semi-separable kernel
  $e^{|u-v|/2}$, row sums by $\psi$ and Mertens.
- **Polar packets**: the even packet $\cosh(u/2)$ and the odd packet $\sinh(u/2)$ with a smooth
  cutoff; their correlations add up to an explicit kernel.
- **The conductor ladder**: system forms with a free conductor; the trivial aperture; the price
  of a weight system.
- **Calibration**: on fakes (the Liouville twist, $\pm\Lambda$ without pole plane, a doubled weight,
  a wrong constant, integer-norm one-offs, the golden datum) and on true $L$-functions (the
  twisted part of a quadratic ring).
- **Feasible sets and their duality**: finite determinacy, compactness, prime-blind duality.
- **The slack map and the exchange atlas**: for each form of the sign its weakest sufficient
  version; for each receiver its chart on the plane of depth and mass.

## 7. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| The prime side on a window of length $2a$ has ceiling $e^{a}(1+o(1))$ | `BiScaleUncertainty.tendsto_windowCeiling_div_exp` | corpus |
| RH iff every feasible set $\mathscr A(a)$ is nonempty | `RHTower.riemannHypothesis_iff_forall_level_exists_weilPositiveFullUpTo` | corpus |
| Comb Bézout selects $\Lambda$ | `AbsoluteGeometryOfSpecZ.combBezout_iff` | corpus |
| Short windows do not see the contacts | `HodgeTheoryOfAFixedPart.combFormW_eq_combForm_of_window` | corpus |
| The twisted part is the zero sum of $L(s,\chi)$ with the conductor as a density | `AbsoluteGeometryOfSpecZ.integral_weilAtomSymbol_twist_packet` | corpus |
| The Schur price of sizes: dominated contact forms are $\le((1+\varepsilon)e^{a}+\dots)\int f^2$ | this folder | target |
| The trivial aperture of a conductor is at least $\log\log q-o(1)$, with a margin | this folder | target |
| The Liouville twist has a negative square at aperture $\log\log q+o(1)$: the ladder has no gap | this folder | target |
| The exceptional square: rank, signature and smallest eigenvalue of a real pair | this folder | target |
| The trivial aperture of the height aspect | this folder | target |
| The first selective window | this folder | target |

## 8. Open research topics

1. The sign of the twisted part at aperture $\log\log q+C$ for one $C>0$ (Landau–Siegel on the
   comb): which property of a character, absent from the Liouville twist, enters at the integers
   between $\log q$ and $e^{2C}\log^2q$.
2. The sign at $\kappa\log(\text{mass})$ for one $\kappa>1$ in one aspect: a zero-free strip in
   that aspect.
3. A source of pointwise information at square-root precision.
4. The exact feasible interval of the first contact as a function of the aperture.
5. The price function of a true character between the trivial aperture and the scale at which
   Deuring–Heilbronn repulsion acts.

## 9. Traps

| Trap | Truth |
|---|---|
| The trivial aperture is $\log\log q-\log4$ and the gap $\log4$ needs the signs of $\chi$ | The gap comes from bounding the symbol pointwise; the quadratic form closes it with sizes alone |
| A sign statement at unbounded aperture in the conductor aspect is information on $\chi$ | Below $\log\log q$ it holds for every dominated system, the Liouville twist included |
| Completely multiplicative signs suffice beyond the trivial aperture | The Liouville twist has them and fails at $\log\log q+o(1)$ |
| Nonemptiness of the feasible sets with a conductor is a statement of RH type | $w=0$ is feasible at every aperture for a large conductor; only the pole plane makes nonemptiness RH |
| The classical zero-free region is the sign at some aperture $\kappa\log\log t$, $\kappa>1$ | It lies at $\kappa=1+o(1)$; every fixed $\kappa>1$ is a zero-free strip |
| A new equivalent of RH is a contribution | The programme prices mechanisms; it adds no equivalent |

## 10. Context

| Neighbour | Interface |
|---|---|
| AbsoluteGeometryOfSpecZ, HodgeTheoryOfAFixedPart | the comb pairing, the square of a quadratic ring and its twisted part, packets, the forced weights and constant |
| BiScaleUncertainty | the Schur test on a window, polar weights and polar tests, the ceiling of the prime side |
| RHTower | Weil's functional and symbol, the archimedean symbol, feasible weights at finite level, Dirichlet explicit formulas |
| SquareRootThreshold, CriticalHardyTheoryOfTheWindowCone | resolution laws, margins of the window cone |
| ExceptionalLayerTheory | Deuring–Heilbronn repulsion for a real zero |
| ArithmeticCastelnuovoSeveri | the index law of a tempered configuration, positivity at typical heights |

In the corpus the receivers are complete and every known producer has a price. SA is the place
where the prices are compared on one scale, the ladder of an aspect, and where a candidate
mechanism is tested before it is run on $\zeta$: on the fakes, which it must reject, and on the
twisted part of a quadratic ring, where the number of squares to remove is one.

## 11. Success criteria and criteria for a contribution

**The programme succeeds** if it exhibits a selective inequality at unbounded scale whose proof
is not a transport of the classical region (milestones: the atlas of sources; the exceptional
square; a zero-free strip in one aspect; RH), or if it proves for each class of mechanisms the
exact scale at which it stops.

**A contribution** is one of:

1. a *price*: the exact aperture, in an aspect, to which a named structure proves the sign, with
   the matching fake;
2. a *selectivity theorem*: an inequality together with a system that shares all structures but
   one and violates it;
3. a *chart*: what a sign at a point of the ladder excludes, with sharp exchange rate;
4. a *producer step*: an unconditional sign beyond a trivial aperture, in any aspect.

**A candidate producer must** (P1) prove the two-block inequality at one prime ratio at fixed
width; (P2) fail with a doubled weight at $2$ and with a constant other than $2\pi$; (P3) prove no
margin; (P4) use the functional equation and the Euler product jointly: fail on the integer-norm
one-off, the $\cosh$ models, the heat family and the Liouville twist; (P5) not be a family, a
section count, a stable approximant or a positive ground state; (P6) run on the twisted part of a
quadratic ring pass the aperture $\log\log q+C$ for some $C>0$, or use the pole plane in a way
that the twisted part does not have; (P7) over a curve reproduce the Toeplitz statement; (P8) be
pointwise.

Not contributions: equivalents of RH; statements that hold on the whole dominated box presented
as information on a character; finite verifications; improvements of constants that do not move a
boundary of the ladder.
