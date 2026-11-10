# Selective Arithmetic (SA)

Namespace `GaloisForLFunctions.SelectiveArithmetic`; umbrella `SelectiveArithmetic.lean`; 8 modules.

## 1. Motivation

Every route of the corpus to the Riemann hypothesis ends at one statement, a sign with no positive
margin, and every route is a *receiver*: it converts the sign into zeros on the line, or the zeros
into the sign. For each mechanism that proves a statement of this type elsewhere (Weil, Deligne,
Stepanov, Lee–Yang, Hermite–Biehler, heat flow, Turán, duality, recurrence) the corpus holds a
theorem that fixes what the mechanism gives over $\mathbb Z$. What no programme contains is a
*producer*: a theorem that yields the sign at unbounded scale for a reason that is not a transport
of the classical zero-free region, of a density theorem, of rigidity or of a verified height.

Selective arithmetic is the theory of producers. It adds no equivalent of RH. For a candidate
inequality and a candidate mechanism it asks three questions.

* **Is the inequality selective?** Does it fail for a system that shares all structures of $\zeta$
  but one? An inequality that holds for every system of a class carries no information on a member.
* **What is its price?** Up to which scale does a mechanism that sees one structure prove it?
* **Where is the first statement beyond the price**, and what must a proof of it use?

The answers are organised on a *ladder*. A system has a mass $m$ — the logarithm of its conductor,
or of the height of a packet — and is tested on windows of aperture $a=\kappa\log m$. The rung
$\kappa=1$ is the *trivial aperture*: below it the sign holds for every system with contacts of
the size of the primes, and beyond it there are fakes. A zero of depth $\delta$ and a power saving
$n^{1/2+\delta}$ in the contacts both sit at the rung $\kappa=1/(2\delta)$. All classical
zero-free regions sit at $\kappa=1+o(1)$.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Weight system | `w : ℕ → ℝ`; `RHTower.weilAtomSymbol w N` | contacts $w(n)$ at $\pm\log n$ against the archimedean symbol |
| Dominated box | `Dominated` | $|w(n)|\le\Lambda(n)$: contacts of the size of the primes |
| Contact form | `contactForm w F N` | $\sum_{2\le n\le N}w(n)n^{-1/2}\,\mathrm{Re}\big(k(\log n)+k(-\log n)\big)$, $k=F\star\tilde F$ |
| System form | `systemForm w q a F` | $\frac1{2\pi}\int|\hat F|^2(S_\infty+\log q)-$ contact form: jets, counterterm of a comb of density $q$, contacts $w$, no pole plane |
| Twisted part | `AbsoluteGeometryOfSpecZ.twistedZeroSum` | the system form of $w=\Lambda\,\mathrm{Re}\,\chi$ with the conductor of $\chi$, plus a nonnegative energy for odd $\chi$; the sum over the zeros of $L(s,\chi)$ |
| Feasible set | `Feasible q a w`; with pole plane `RHTower.WeilPositiveFullUpTo` | systems whose form is nonnegative on tests supported in $[-a,a]$ |
| Trivial aperture | `trivialAperture q` | supremum of the apertures at which the whole dominated box is feasible |
| Polar packets | `cutoff`, `evenPolar`, `oddPolar` | $\cosh(u/2)\chi(u)$ and $\sinh(u/2)\chi(u)$: the positive and the negative square of the polar kernel $e^{|u-v|/2}$ |
| Fakes | `liouvilleWeight`, `fun n => -Λ n`, `fun n => Λ n`; `SquareRootThreshold.isolatedPairConfig` | completely multiplicative signs without conductor; the contacts of $1/\zeta$; the contacts of $\zeta$ without pole plane; a lattice with functional equation and one off-line pair |
| Height | `RHTower.modulatedTest t f` | the packet $e^{-itu}f(u)$; its mass is $\log(2+|t|)$ |
| Cancellation | `partialSum`, `HasCancellation w C γ` | $|\sum_{2\le k\le n}w(k)|\le C\,n^{1/2+\gamma}$ |
| Mass at a zero | `A₀ * Real.log (|ρ₀.im| + 3)` | the local zero density of a configuration at a zero |

## 3. Language

- **Structure**: a property of $\zeta$ that a fake may drop: the sizes of the contacts, their
  signs, complete multiplicativity, the conductor (the functional equation), the pole plane, the
  constant $2\pi$ of the counterterm, the jets.
- **Selective**: an inequality that holds for $\zeta$ or a true $L$-function and fails for a system
  sharing all structures but one. **At unbounded scale**: on apertures unbounded in the aspect.
- **Source**: the input of an unconditional selective inequality: exponential sums, mean values,
  rigidity, the additive identity of the fractional part, nonnegativity of ideal counts.
- **Aspect**: the parameter carrying the mass: the conductor $q$ (mass $\log q$); the height $t$
  of a packet (mass $\log|t|$); in a configuration, the local zero density at a zero.
- **Ladder, rung**: the apertures $a=\kappa\log m$ of an aspect; $\kappa$ is the rung.
- **Price** of a structure: the highest rung to which it proves the sign. **Trivial aperture**:
  the rung $\kappa=1$, the price of the sizes.
- **Exchange rate**: the relation $2\delta\kappa=1$ between a depth or a saving $\delta$ and its rung.
- **Exceptional square**: a negative square of the form of a true object beyond the trivial
  aperture. **Removable**: excluded by a mechanism that fails on the fakes.
- **Bounded shape**: packets with $\int f'^2\le M\int f^2$.
- **Receiver / producer**: a theorem converting the sign into information on zeros or back / a
  theorem proving the sign.

## 4. Mechanisms

**The form of a system.** On a test $F$ supported in $[-a,a]$,
$$\mathfrak W_{w,q}(F)=\frac1{2\pi}\int|\hat F(\tau)|^2\big(S_\infty(\tau)+\log q\big)d\tau
-\sum_{2\le n\le e^{2a}}\frac{w(n)}{\sqrt n}\,\mathrm{Re}\big(k(\log n)+k(-\log n)\big),$$
$S_\infty(\tau)=\mathrm{Re}\,\psi(\tfrac14+\tfrac{i\tau}2)-\log\pi\ge-A_0$,
$A_0=\gamma+3\log2+\tfrac\pi2+\log\pi$. It is affine in $w$, increasing in $q$, and sees only
$w(n)$, $n\le e^{2a}$. For $w=\Lambda\,\mathrm{Re}\,\chi$ and the conductor of $\chi$ it is the sum
over the zeros of $L(s,\chi)$.

**1. The mass pays the sizes (Schur price).** The contact form is the form of the operator
$f\mapsto\sum_nw(n)n^{-1/2}(f(\cdot+\log n)+f(\cdot-\log n))$ on $L^2[-a,a]$. For $w=\Lambda$ its
kernel is on average $e^{|u-v|/2}$: semi-separable, top eigenfunction $\cosh(u/2)$, top eigenvalue
$e^a(1+o(1))$. The Schur test with the weight $\cosh$ gives for every dominated system
$|\text{contact form}|\le((1+\varepsilon)e^a+B_\varepsilon+(1+2a)^2)\int|F|^2$. The pointwise
bound of the symbol, $2\sum_{n\le e^{2a}}\Lambda(n)n^{-1/2}\approx4e^a$, is four times larger: a
packet supported in $[-a,a]$ does not correlate with itself at lags near $2a$.

**2. The trivial aperture.** Hence $\mathfrak W_{w,q}\ge\tfrac12(1-e^{-\eta/2})\log q\int|F|^2$ at
every aperture $a\le\log\log q-\eta$, for every dominated system and every large conductor; in
particular for the twisted part of the square of a quadratic ring, for real and complex
characters.

**3. The fakes beyond it.** The polar kernel has a negative square on $\sinh(u/2)$. On the odd
polar packet the correlations satisfy $(O\star\tilde O)(y)\le2ae^{a-y/2}-(E\star\tilde E)(y)$,
and the even packet sees half the Riesz mean $\sum_{n\le Y}\Lambda(n)\log(Y/n)\sim Y$. So the forms
of $-\Lambda$ and of the Liouville twist are negative on the odd packet, and the form of $\Lambda$
without pole plane on the even packet, as soon as $a\ge\log\log q+\eta$. The Liouville twist is
dominated, completely multiplicative with values $\pm1$, and has no conductor: an Euler product
without functional equation.

**4. No gap.** `trivialAperture q` $=\log\log q+o(1)$; the dominated box is feasible below it and
some dominated system is infeasible above it, for every conductor. The feasible sets are convex,
increase with $q$, decrease with $a$. A uniform floor $-K\int|F|^2$ is feasibility at the
conductor $qe^K$, which has the same trivial aperture up to $o(1)$: floors do not move the ladder,
and beyond the trivial aperture the Liouville twist violates every floor.

**5. The height is a mass.** For $F=e^{-itu}f(u)$ the transform moves to $t$, where
$S_\infty\ge\log(2+|t|)-c_0$; moving back costs $1+(\tau-t)^2$, which is the energy of $f'$. The
pole term at the points $\pm i/2-t$ is $\ge-4\int f'^2$ once $e^a\le|t|$, by one integration by
parts. So Weil's form of every dominated system with pole plane, $\zeta$ included, is at least
$\tfrac12(1-e^{-\eta/2})\log|t|\int f^2-5\int f'^2$ at every aperture $a\le\log\log|t|-\eta$.

**6. Cancellation buys the ladder (prime side of the exchange rate).** If
$|\sum_{k\le n}w(k)|\le Cn^{1/2+\gamma}$, summation by parts gives
$|2\sum_{n\le N}w(n)n^{-1/2}\cos(\tau\log n)|\le2CN^\gamma(2+\log N)(1+|\tau|)$: the prime part of the
symbol has size $N^\gamma$. Hence $\mathfrak W_{w,q}(f)\ge\tfrac12\log q(\int f^2-\int f'^2)$ at
every aperture $a\le\kappa\log\log q$ with $2\gamma\kappa<1$.

**7. A zero shows at the rung of its depth (zero side of the exchange rate).** A reflected pair
of depth $\delta$ is a form of rank two and signature $(1,1)$ with smallest eigenvalue
$-(\sinh(2\delta a)/\delta-2a)$ on $L^2[-a,a]$ (corpus). In a lattice of zeros on the line with the
density of a conductor it is invisible at $a\le\kappa\log\log q$ for $2\delta\kappa<1$ and visible
for $2\delta\kappa>1$. In an arbitrary configuration with a logarithmic local count, positivity at
the aperture $\kappa\log m$, $m$ the mass at the zero, forces another off-line zero within the
ordinate distance $m^\kappa$ whenever $2\delta\kappa>1$. For $L(s,\chi)$ the mass is
$A(\log q+1)\log(|\gamma_0|+3)$; for $\zeta$ it is $A_0\log(|\gamma_0|+3)$.

**8. Both structures are needed beyond $\kappa=1$.** The Liouville twist (Euler product, no
functional equation) and the lattice with a pair at $0$ and $1$ (functional equation, no Euler
product) both fail at the rung $1$.

## 5. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| Schur price of sizes | `abs_contactForm_le_of_psi` | unconditional |
| Form of a dominated system; feasibility of the box | `systemForm_ge_of_dominated`, `feasible_of_dominated`, `exists_systemForm_margin` | unconditional |
| Twisted part = system form; trivial aperture of a conductor with margin | `twistedZeroSum_eq_systemForm`, `exists_twistedZeroSum_ge`, `exists_trivialAperture_margin` | unconditional |
| Polar packets: correlations add up to the polar kernel | `packetAutocorr_evenPolar_ge`, `packetAutocorr_oddPolar_le` | unconditional |
| Upper bound of a form on a smooth packet | `systemForm_le_of_packet` | unconditional |
| The Liouville twist, $-\Lambda$, $\Lambda$ without pole plane fail at $\log\log q+\eta$ | `exists_systemForm_polar_neg`, `exists_not_feasible`, `liouvilleWeight_prime_pow` | unconditional |
| The ladder of the conductor has no gap | `exists_abs_trivialAperture_sub_le`, `tendsto_trivialAperture_sub_log` | unconditional |
| The trivial aperture is a threshold; feasible sets convex and monotone | `feasible_of_lt_trivialAperture`, `exists_not_feasible_of_trivialAperture_lt`, `convex_feasible`, `Feasible.anti`, `Feasible.mono_conductor`, `feasible_congr` | unconditional |
| A floor is a conductor; the Liouville twist violates every floor beyond the trivial aperture | `feasible_mul_exp_iff`, `exists_not_floor` | unconditional |
| The height is a mass; the pole plane does not reach a height | `integral_arch_modulated_ge`, `systemForm_modulated_ge`, `re_weilPoleTerm_modulated_ge` | unconditional |
| Weil's form of $\zeta$ at a height, aperture $\le\log\log|t|-\eta$ | `re_weilFullFunctional_modulated_ge`, `exists_height_margin` | unconditional |
| Exchange rate, prime side | `abs_sum_contact_cos_le`, `systemForm_ge_of_cancellation`, `exists_cancellation_margin` | unconditional |
| Exchange rate, zero side, lattice with a pair | `isolatedPair_nonneg_of_rung`, `isolatedPair_neg_of_rung` | unconditional |
| Positivity on a rung forces companions; $\zeta$ in the height aspect | `exists_companion_of_rung`, `zeta_companion_of_rung` | unconditional |
| The zeros of $L(s,\chi)$ on the ladder of the conductor | `dirichletZeros_local_count`, `dirichlet_companion_of_rung` | unconditional |

Corpus pillars the field stands on: the ceiling $e^a(1+o(1))$ of the prime side on a window
(`BiScaleUncertainty.tendsto_windowCeiling_div_exp`); RH iff every feasible set with pole plane is
nonempty (`RHTower.riemannHypothesis_iff_forall_level_exists_weilPositiveFullUpTo`); Bézout on the
comb selects $\Lambda$ (`AbsoluteGeometryOfSpecZ.combBezout_iff`); windows of ratio $\le2$ do not
see the contacts (`HodgeTheoryOfAFixedPart.combFormW_eq_combForm_of_window`); the isolated pair law
(`SquareRootThreshold.isolatedPairConfig_weil_nonneg_iff`); the isolation inequality
(`RHTower.re_W_modulatedTest_le_of_isolated`); Deuring–Heilbronn on the twisted comb and the
one-square law (`AbsoluteGeometryOfSpecZ.TheTrivialApertureAndTheExceptionalSquare`).

## 6. Questions

| # | Question | Answer |
|---|---|---|
| Q1 | Which unconditional theorems are selective at unbounded scale, and from which sources? | See the atlas below. In the aspects of conductor and height every unconditional pointwise sign lies below the rung $1$ and holds for the whole dominated box; the classical regions lie at $1+o(1)$ |
| Q2 | Is there a source beyond exponential sums, mean values, rigidity and the fractional part? | Open. A source passes the rung $1$ only by a power saving of the contacts on the integers up to $m^{2\kappa}$ (prime side) or by excluding isolated zeros of depth $>1/(2\kappa)$ (zero side); sizes, multiplicativity and the functional equation alone do not |
| Q3 | Can a feasible weight system be constructed at every aperture? | With a conductor: the dominated box up to the trivial aperture and not beyond; systems with cancellation $\gamma$ up to $\kappa<1/(2\gamma)$ on bounded shapes. With the pole plane: this is RH |
| Q4 | Is the exceptional square removable? | The ladder of the conductor has no gap: the sign at $\log\log q-\eta$ is a theorem for every dominated system, and at $\log\log q+\eta$ it fails for the Liouville twist. Removal at $\log\log q+C$ is a statement on $\chi$ at the integers between $\log q$ and $e^{2C}\log^2q$ that uses conductor and Euler product jointly: Landau–Siegel on the comb |
| Q5 | What is the first selective window? | For $\zeta$: every window of ratio $>2$ (corpus: ratio $\le2$ is blind, and visible weights are bounded). In an aspect: the rung $1$ |

**Atlas (where a statement sits on the ladder).**

| Statement | Rung | Selective against | Source |
|---|---|---|---|
| Sign of the twisted part, $a\le\log\log q-\eta$ | $\kappa<1$ | systems with larger contacts | sizes: prime number theorem and the mass |
| Weil's form of $\zeta$ at height $t$, bounded shape, $a\le\log\log|t|-\eta$ | $\kappa<1$ | systems with larger contacts | sizes and the Gamma factor |
| Classical zero-free regions, Landau–Page, Siegel: depth $\le\tfrac12-\varepsilon(m)$, $\varepsilon\to0$ | $1+o(1)$ | the Liouville twist; the lattice with a pair at depth $\tfrac12$ | nonnegativity of counts; exponential sums |
| Sign at $\log\log q+C$ | $1+C/\log\log q$ | Liouville twist | none known |
| A zero-free strip of width $\varepsilon$ in an aspect | $1/(1-2\varepsilon)$ | fakes of depth $>\tfrac12-\varepsilon$ | none known |
| Positivity at typical heights (corpus, in law) | apertures $c\log T$ | — | density theorems |
| GRH, RH | every rung | every fake | — |

## 7. Tools

**Developed.**
- The contact operator of a system and its Schur test with polar weights, for dominated systems
  and complex tests.
- Polar packets with an explicit smooth cutoff: masses, derivative energies, correlation
  inequalities; the upper bound $(5+\log q)\int f^2+\int f'^2-$ contacts for a form on a packet.
- The conductor ladder: system forms with a free conductor, feasible sets and their structure,
  the trivial aperture as a threshold.
- Calibration on fakes (Liouville twist, $\pm\Lambda$, lattice with a pair) and on true
  $L$-functions (twisted part with margin; companions of the zeros of $L(s,\chi)$ and of $\zeta$
  on a rung).
- The slack map of a system form: a floor is a conductor; a saving is a rung.
- The height aspect: modulated packets, the archimedean energy at a height, decay of the pole term.
- Summation by parts on the symbol: the exchange rate between cancellation and rungs.

**To build.**
- A fake for the height aspect in the dominated class (block-aligned phases), to show that the
  rung $1$ is sharp there for sizes.
- The exchange rate on packets without shape condition: bounds for $\sum w(n)n^{-i\tau}$ uniform
  in $\tau$.
- The exact feasible interval of the first contact as a function of the aperture.
- The rung law for an exceptional zero with Deuring–Heilbronn isolation in place of the
  companion alternative.

## 8. Open research topics

1. **The exceptional square.** The sign of the twisted part at $\log\log q+C$ for one $C>0$.
2. **A rung above one.** The sign at $\kappa\log m$ for one $\kappa>1$ in one aspect: a zero-free
   strip of width $\tfrac12-\tfrac1{2\kappa}$ there.
3. **A producer step.** An unconditional power saving of the contacts of a true object on the
   integers up to a power of its mass; known savings start at $q^{1/4}$ and at
   $\exp((\log t)^{2/3})$.
4. **Rough packets.** Whether cancellation of the partial sums alone pays the sign on all packets
   of an aperture, or only on bounded shapes.
5. **The margin side.** The rate at which the feasible sets with pole plane shrink to $\Lambda$.

## 9. Traps

| Trap | Truth |
|---|---|
| The trivial aperture is $\log\log q-\log4$ and the gap needs the signs of $\chi$ | The pointwise bound of the symbol loses a factor $4$; the quadratic form closes it with sizes alone |
| A sign at unbounded aperture in the conductor aspect is information on $\chi$ | Below $\log\log q$ it holds for every dominated system, the Liouville twist included |
| Complete multiplicativity with values $\pm1$ is enough beyond the trivial aperture | The Liouville twist has it and fails at $\log\log q+o(1)$ |
| The functional equation with the right density of zeros is enough | The lattice with a pair at $0$ and $1$ has it and fails at the same rung |
| Nonemptiness of feasible sets with a conductor is of RH type | $w=0$ is feasible at every aperture for a large conductor; only the pole plane makes nonemptiness RH |
| The classical zero-free region is the sign at some rung $\kappa>1$ | It sits at $\kappa=1+o(1)$; every fixed $\kappa>1$ is a strip |
| Positivity at a height is positivity on all packets modulated to it | Only on bounded shapes; all modulated packets are all tests |
| Cancellation of the partial sums bounds the contact operator | It bounds the symbol with a factor $1+|\tau|$: the bound is for bounded shapes |
| A uniform floor is easier than the sign on the ladder | A floor $-K$ is the sign at the conductor $qe^K$; the fakes violate every floor at the same rung |
| A new equivalent of RH is a contribution | The programme prices mechanisms; it adds no equivalent |

## 10. Context

| Neighbour | Interface |
|---|---|
| AbsoluteGeometryOfSpecZ, HodgeTheoryOfAFixedPart | comb pairing, square of a quadratic ring and its twisted part, packets, forced weights and constant, one-square law, Deuring–Heilbronn on the comb |
| BiScaleUncertainty | Schur test on a window, polar weight, ceiling of the prime side, Riesz mean of $\Lambda$ |
| RHTower | Weil's functional and symbol, archimedean symbol and its bounds, feasible weights at finite level, isolation inequality, local counts |
| SquareRootThreshold, WindowVisibilityLaw | isolated pair law, visibility thresholds, resolution laws |
| ExceptionalLayerTheory | Deuring–Heilbronn repulsion |
| ArithmeticCastelnuovoSeveri | positivity at typical heights (in law) |

In the corpus the receivers are complete and every known producer has a price. SA puts the prices
on one scale, the ladder of an aspect. A candidate mechanism is tested there before it is run on
$\zeta$: it must reject the fakes, and on the twisted part of a quadratic ring the number of
squares to remove is one.

## 11. Success criteria and criteria for a contribution

**The programme succeeds** if it exhibits a selective inequality at unbounded scale whose proof is
not a transport of the classical region (milestones: the atlas of sources; the exceptional square;
a zero-free strip in one aspect; RH), or if it proves for each class of mechanisms the exact rung
at which it stops.

**A contribution** is one of:

1. a *price*: the exact rung to which a named structure proves the sign, with the matching fake;
2. a *selectivity theorem*: an inequality with a system that shares all structures but one and
   violates it;
3. a *chart*: what a sign at a point of the ladder excludes, with the sharp exchange rate;
4. a *producer step*: an unconditional sign beyond a trivial aperture, in any aspect.

**A candidate producer must** (P1) prove the two-block inequality at one prime ratio at fixed
width; (P2) fail with a doubled weight at $2$ and with a constant other than $2\pi$; (P3) prove no
margin; (P4) use the functional equation and the Euler product jointly: fail on the integer-norm
one-off, the $\cosh$ models, the heat family, the Liouville twist and the lattice with a pair;
(P5) not be a family, a section count, a stable approximant or a positive ground state; (P6) on
the twisted part of a quadratic ring pass the aperture $\log\log q+C$ for some $C>0$, or use the
pole plane in a way that the twisted part does not have; (P7) over a curve reproduce the Toeplitz
statement; (P8) be pointwise.

Not contributions: equivalents of RH; statements that hold on the whole dominated box presented as
information on a character; finite verifications; improvements of constants that do not move a
boundary of the ladder.
