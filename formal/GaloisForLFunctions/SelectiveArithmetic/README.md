# Selective Arithmetic (SA)

Namespace `GaloisForLFunctions.SelectiveArithmetic`; umbrella `SelectiveArithmetic.lean`; 15 modules.

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
| Feasible with pole plane | `PoleFeasible a w` | real weight systems whose Weil functional, with the pole plane and the archimedean place of $\zeta$ and no conductor, is nonnegative on real packets supported in $[-a,a]$ |
| Trivial aperture | `trivialAperture q` | supremum of the apertures at which the whole dominated box is feasible |
| Polar packets | `cutoff`, `evenPolar`, `oddPolar` | $\cosh(u/2)\chi(u)$ and $\sinh(u/2)\chi(u)$: the positive and the negative square of the polar kernel $e^{|u-v|/2}$ |
| Fakes | `liouvilleWeight`, `fun n => -Λ n`, `fun n => Λ n`; `SquareRootThreshold.isolatedPairConfig` | completely multiplicative signs without conductor; the contacts of $1/\zeta$; the contacts of $\zeta$ without pole plane; a lattice with functional equation and one off-line pair |
| Height | `RHTower.modulatedTest t f` | the packet $e^{-itu}f(u)$; its mass is $\log(2+|t|)$ |
| Contacts seen from a height | `twistedWeight w t`, `alignedWeight t` | $w(n)\cos(t\log n)$; the system aligned with $t$ is $\Lambda(n)\cos(t\log n)$, half the contacts of $\zeta(s+it)\zeta(s-it)$ |
| Two-bump packet | `twoBump s h r` | two bumps of width $r$ at $\pm h$: lags $0$ and $2h$ only |
| Contact polynomial | `contactPoly N u`, `contactMass`, `contactEnergy`, `contactSlope` | $D_N(u)=\sum_{2\le n\le N}\Lambda(n)n^{-1/2}\cos(u\log n)$: the primes in the symbol at the height $u$; its sup bound, mean-square bound and Lipschitz constant |
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

**4′. Between a ball and a box.** A pair of narrow bumps at distance $\log n$ has the lags $0$
and $\log n$ only, so it isolates the contact $n$; a bump of width $r$ costs $\log(1/r)+O(1)$ times
its mass. Hence every system feasible at an aperture $a\ge\tfrac12\log n+r$, $0<r\le\tfrac1{4n}$,
has $|w(n)|\le\sqrt n(\log q+\log(1+1/r)+C)$. Conversely
$A_0+2\sum_{n\le e^{2a}}|w(n)|n^{-1/2}\le\log q$ is sufficient. Below the first contact,
$2a<\log2$, the weights do not enter. So selectivity starts at the aperture $\tfrac12\log2$, where
the weight at $2$ is confined to an interval of half-length of the order of the mass; a single
weight may reach $\sqrt n$ times the mass, and what the ladder constrains beyond the trivial
aperture is the Riesz mean of all contacts together (6′).

**4″. The first selective window of $\zeta$.** With the pole plane and no conductor
(`PoleFeasible`), below the aperture $\tfrac12\log2$ every real weight system is feasible: Weil's
functional on such tests has no contact. At the aperture $\tfrac12\log2+r$ the two-bump packet
confines the weight at $2$: its pole term is at most $12$ times the mass of one bump, so
$|w(2)|\le\sqrt2(\log(1+1/r)+C)$, and in general $|w(n)|\le\sqrt n(\log(1+1/r)+C)$. The weight
of $\zeta$ is interior: up to the aperture $181/500$ every system with
$\sqrt2\,|w(2)-\log2|\le1/5000$ is feasible, by the margin of Weil's form on short windows
(corpus). So the first selective window of $\zeta$ has ratio $2$, and there the feasible weights at
$2$ form an interval around $\log2$ whose length is at most of the order $\log(1/r)$.

**5. The height is a mass.** For $F=e^{-itu}f(u)$ the transform moves to $t$, where
$S_\infty\ge\log(2+|t|)-c_0$; moving back costs $1+(\tau-t)^2$, which is the energy of $f'$. The
pole term at the points $\pm i/2-t$ is $\ge-4\int f'^2$ once $e^a\le|t|$, by one integration by
parts. So Weil's form of every dominated system with pole plane, $\zeta$ included, is at least
$\tfrac12(1-e^{-\eta/2})\log|t|\int f^2-5\int f'^2$ at every aperture $a\le\log\log|t|-\eta$.

**5′. A height is a conductor of the twisted contacts.** On a packet modulated to the height $t$
a contact $w(n)$ is seen with the phase $\cos(t\log n)$: the contact form of $w$ on
$e^{-itu}f$ is the contact form of $w_t(n)=w(n)\cos(t\log n)$ on $f$. The archimedean symbol is
subadditive, $S_\infty(\tau+t)\le S_\infty(\tau)+\log(2+|t|)+A_2$. Hence the height transfer
$$\mathfrak W_{w_t,q}(f)+(\log(2+|t|)-A_3)\!\int\! f^2-2\!\int\! f'^2\ \le\ \mathfrak W_{w,q}(e^{-itu}f)
\ \le\ \mathfrak W_{w_t,q}(f)+(\log(2+|t|)+A_2)\!\int\! f^2:$$
the form at the height $t$ is the form of the twisted contacts at the conductor $q(2+|t|)$, exactly
from above and up to the shape from below.

**5″. The fake of the height.** The system aligned with $t$, $w(n)=\Lambda(n)\cos(t\log n)$, is
dominated and its poles sit at the heights $\pm t$, where the pole plane does not reach. On its own
height it is seen with $\cos^2(t\log n)$, whose mean over $t\in[T,2T]$ is at least
$\tfrac12-\tfrac1T$ at every $n\ge2$. So at some height of every dyadic window the even polar
packet sees half the Riesz mean of the primes, against the mass $\log t\cdot e^a/2$: at every
aperture $\log\log T+\log2+\eta\le a\le\log T$ Weil's form of the aligned system, with pole
plane, is below $-C\int f'^2$. The trivial aperture of the height is $\log\log|t|+O(1)$, between
$-\eta$ and $\log2+\eta$.

**5‴. Mean values buy every rung in the mean.** The primes enter the symbol at the height $t$
through $D_N(t)=\sum_{n\le N}\Lambda(n)n^{-1/2}\cos(t\log n)$, $N=e^{2a}$, of size up to $2e^a$.
Distinct logarithms below $N$ differ by at least $1/(2N)$, so an off-diagonal pair integrates to at
most $4N$ over any interval:
$\int_A^BD_N^2\le(B-A)\sum\Lambda(n)^2/n+4N(\sum\Lambda(n)/\sqrt n)^2$. If
$4e^{4a}(2+2a)^4\le T$ the mean square over $[T,2T]$ is at most $2a(2+2a)^2+1$: polylogarithmic in
the window against the mass $\log T$, up to apertures of about $\tfrac14\log T$. The sizes are
attained at aligned heights only. Maximising $G-\lambda B$ over a window gives one height at which
a positive sum keeps half of itself while $D_N$ is small on a grid, and the Lipschitz constant
$\sum\Lambda(n)n^{-1/2}\log n$ extends the grid to an interval of heights.

**6. Cancellation buys the ladder (prime side of the exchange rate).** If
$|\sum_{k\le n}w(k)|\le Cn^{1/2+\gamma}$, summation by parts gives
$|2\sum_{n\le N}w(n)n^{-1/2}\cos(\tau\log n)|\le2CN^\gamma(2+\log N)(1+|\tau|)$: the prime part of the
symbol has size $N^\gamma$. Hence $\mathfrak W_{w,q}(f)\ge\tfrac12\log q(\int f^2-\int f'^2)$ at
every aperture $a\le\kappa\log\log q$ with $2\gamma\kappa<1$. At a height $t$ the same holds
for the twisted contacts $w_t$ and the mass $\log q+\log(2+|t|)$, by the height transfer. On all
packets the form is a Fourier multiplier: it is nonnegative as soon as the symbol plus $\log q$ is,
and this follows from a saving in the partial sums of $w_\tau$ at every height $\tau$, with a
constant that may grow like $S_\infty(\tau)$. No uniform constant exists: the logarithms of the
primes are independent, so some height aligns any finite set of contacts.

**6′. The sign is cancellation (the converse).** With $E=\cosh(u/2)\chi$, $O=\sinh(u/2)\chi$:
$E(u)E(u+y)-O(u)O(u+y)=\cosh(y/2)\chi(u)\chi(u+y)$, so the difference of the contact forms of the
two polar packets is $\sum w(n)(1+\tfrac1n)\Phi(\log n)$, $\Phi=\chi\star\tilde\chi$,
$2a-2\delta-y\le\Phi(y)\le2a-y$; their sum is $O(ae^a\sum\Lambda(n)/n)$. A packet with a cutoff of
margin $\delta$ has archimedean energy $\le(\log(1+1/\delta)+5)\int f^2+\delta^2\int f'^2$. With
$\delta=e^{-a}$: if the form of a dominated system is nonnegative on the two polar packets, then
$|\sum_{n\le e^{2a}}w(n)(2a-\log n)|\le\log q\,(e^a+2a)+C(1+a)^3e^a$. The Riesz mean of the
contacts at $Y=e^{2a}$ is at most $\sqrt Y(\log q\,(1+o(1))+C\log^3Y)$, with the constant one in
front of the mass; a dominated system whose Riesz mean is $\ge cY$ is infeasible beyond the
aperture $\log\log q+\log(1/c)+o(1)$. The three fakes are the systems without cancellation
($c=1$): for them this is the trivial aperture. By the height transfer the same holds at every
height: a feasible dominated system has
$|\sum_{n\le e^{2a}}w(n)\cos(t\log n)(2a-\log n)|\le(\log q+\log(2+|t|))(e^a+2a)+C(1+a)^3e^a$
for all $t$. Feasibility is square-root cancellation of the Riesz means of $w(n)n^{-it}$ at every
height, against the analytic conductor $q(2+|t|)$; the sign on packets of bounded shape reads the
height zero only.

**6″. Bounded shapes do not decide feasibility.** The symbol of the system aligned with $t_0$
at the frequency $\tau$ is $S_\infty(\tau)-D_N(t_0-\tau)-D_N(t_0+\tau)$. Take
$a=\log\log q+\log2+\eta$ and heights of size $e^{8a}$. The mean values of 5‴ give a $t_0$ at
which $D_N$ is at most $\tfrac18\log q$ on the interval of radius $\tau_1=4e^{\eta/2}(2+2a)$
around $t_0$ and at which the Riesz mean of $\Lambda(n)\cos^2(t_0\log n)$ keeps half of that of
the primes; beyond $\tau_1$ the size $2\sum\Lambda(n)/\sqrt n\le\tfrac14\log q\,\tau_1^2$ is
paid by $\tau^2$. So the symbol plus $\log q$ is at least
$(\tfrac34\log q-A_0)-\tfrac14\log q\,\tau^2$: the aligned system satisfies
$\mathfrak W\ge\tfrac12\log q(\int f^2-\int f'^2)$ on every packet at the aperture $a$. At the
height $t_0$ its twisted Riesz mean has no cancellation, so by 6′ it is not feasible at the same
aperture. The sign on bounded shapes and feasibility are different statements already at the
rung $1+o(1)$.

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
| The box law of a conductor; an $\ell^1$ ball is feasible; no weight enters below the first contact | `packetAutocorr_twoBump`, `exists_abs_weight_le_of_feasible`, `feasible_of_sum_abs_le`, `feasible_iff_of_lt_half_log_two` | unconditional |
| The first selective window of $\zeta$: blind below ratio $2$; the weight at $2$ confined beyond it; $\Lambda$ interior up to $181/500$ | `poleFeasible_iff_of_lt_half_log_two`, `exists_abs_weight_le_of_poleFeasible`, `poleFeasible_of_abs_sub_le`, `poleFeasible_vonMangoldt` | unconditional |
| The height is a mass; the pole plane does not reach a height | `integral_arch_modulated_ge`, `systemForm_modulated_ge`, `abs_re_weilPoleTerm_modulated_le` | unconditional |
| Weil's form of $\zeta$ at a height, aperture $\le\log\log|t|-\eta$ | `re_weilFullFunctional_modulated_ge`, `exists_height_margin` | unconditional |
| The fake of the height: the aligned system fails at $\log\log T+\log2+\eta$ at some height of $[T,2T]$ | `weilTest_modulatedTest`, `exists_height_contactForm_aligned_ge`, `re_weilFullFunctional_modulated_le`, `exists_aligned_height_neg`, `exists_dominated_height_neg` | unconditional |
| The height transfer: a height is a conductor of the twisted contacts | `archimedeanWeilSymbol_add_le`, `contactForm_modulatedTest_eq`, `systemForm_modulatedTest_le`, `systemForm_modulatedTest_ge` | unconditional |
| Feasibility is square-root cancellation of the twisted Riesz means at every height | `exists_twisted_riesz_le_of_feasible` | unconditional |
| Twisted cancellation buys the ladder of the analytic conductor; the symbol criterion on all packets | `systemForm_modulated_ge_of_twisted_cancellation`, `exists_height_cancellation_margin`, `feasible_of_symbol_nonneg`, `feasible_of_twisted_cancellation` | unconditional |
| Mean values over the heights: mean square of the contact polynomial; a quiet height with half of a positive sum | `integral_sq_sum_cos_le`, `integral_contactPoly_sq_le`, `integral_contactPoly_window_sq_le`, `exists_height_of_means`, `exists_height_contactPoly_small`, `abs_contactPoly_le_of_grid` | unconditional |
| Bounded shapes do not decide feasibility: a dominated system with the sign on every packet of bounded shape, infeasible at the same aperture | `two_mul_sum_twisted_aligned`, `systemForm_aligned_ge`, `grid_budget`, `receiver_budget`, `exists_shape_positive_not_feasible` | unconditional |
| Exchange rate, prime side: cancellation buys rungs | `abs_sum_contact_cos_le`, `systemForm_ge_of_cancellation`, `exists_cancellation_margin` | unconditional |
| Exchange rate, prime side, converse: the sign is square-root cancellation of the Riesz mean | `packetAutocorr_evenPolar_sub_oddPolar`, `systemForm_le_of_packet_scaled`, `exists_riesz_le_of_polar_nonneg`, `exists_riesz_le_of_feasible`, `exists_not_feasible_of_riesz_ge` | unconditional |
| The sign of the twisted part at an aperture bounds the Riesz mean of the character | `exists_riesz_twist_le_of_nonneg` | unconditional |
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
| Q2 | Is there a source beyond exponential sums, mean values, rigidity and the fractional part? | None is known, and the field fixes what one must deliver. The sign at aperture $a$ *is* a saving: feasibility forces the Riesz means of $w(n)n^{-it}$ at $Y=e^{2a}$ to be $O(\sqrt Y(\log q+\log(2+|t|)+\log^3Y))$ at every height, and a power saving of the twisted partial sums gives the sign back. A source passes the rung $1$ only by a power saving of the contacts on the integers up to $m^{2\kappa}$, uniform in the height against the analytic conductor, or by excluding isolated zeros of depth $>1/(2\kappa)$; sizes, multiplicativity and the functional equation alone do not |
| Q3 | Can a feasible weight system be constructed at every aperture? | With a conductor: the dominated box up to the trivial aperture and not beyond; an $\ell^1$ ball of the size of the mass at every aperture; systems whose twisted contacts have cancellation $\gamma$ up to $\kappa<1/(2\gamma)$. With the pole plane: every system below the aperture $\tfrac12\log2$, a neighbourhood of $\Lambda$ up to $181/500$, and at every aperture exactly when RH holds (corpus) |
| Q4 | Is the exceptional square removable? | The ladder of the conductor has no gap: the sign at $\log\log q-\eta$ is a theorem for every dominated system, and at $\log\log q+\eta$ it fails for the Liouville twist. Removal at $\log\log q+C$ is a statement on $\chi$ at the integers between $\log q$ and $e^{2C}\log^2q$ that uses conductor and Euler product jointly: Landau–Siegel on the comb |
| Q5 | What is the first selective window? | The first contact, ratio $2$. Below the aperture $\tfrac12\log2$ no weight enters, with a conductor and with the pole plane. At $\tfrac12\log n+r$ the weight at $n$ of a feasible system is at most $\sqrt n(\log q+\log(1+1/r)+C)$, and for $\zeta$ with its pole plane at most $\sqrt n(\log(1+1/r)+C)$; the weight $\log2$ of $\zeta$ is interior up to the aperture $181/500$. On the ladder the first aperture that is selective inside the dominated box is the rung $1$, in the aspect of the conductor and of the height |

**Atlas (where a statement sits on the ladder).**

| Statement | Rung | Selective against | Source |
|---|---|---|---|
| Sign of the twisted part, $a\le\log\log q-\eta$ | $\kappa<1$ | systems with larger contacts | sizes: prime number theorem and the mass |
| Weil's form of $\zeta$ at height $t$, bounded shape, $a\le\log\log|t|-\eta$ | $\kappa<1$ | systems with larger contacts | sizes and the Gamma factor |
| Weil's form at height $t$, $a\ge\log\log t+\log2+\eta$ | $1+O(1/\log\log t)$ | the system aligned with $t$ | none known |
| Classical zero-free regions, Landau–Page, Siegel: depth $\le\tfrac12-\varepsilon(m)$, $\varepsilon\to0$ | $1+o(1)$ | the Liouville twist; the lattice with a pair at depth $\tfrac12$ | nonnegativity of counts; exponential sums |
| Sign of a dominated system at aperture $a$ $\Rightarrow$ Riesz means of $w(n)n^{-it}$ at $e^{2a}$ are $\le e^a(\log q+\log(2+|t|)+O(a^3))$ at every height | every rung | systems without cancellation at one height | — (a receiver) |
| Sign at $\log\log q+C$ | $1+C/\log\log q$ | Liouville twist | none known |
| A zero-free strip of width $\varepsilon$ in an aspect | $1/(1-2\varepsilon)$ | fakes of depth $>\tfrac12-\varepsilon$ | none known |
| Mean square of the contact polynomial over $[T,2T]$ is $\le2a(2+2a)^2+1$ | apertures up to $\approx\tfrac14\log T$, in the mean | — | mean values |
| Positivity at typical heights (corpus, in law) | apertures $c\log T$ | — | density theorems |
| GRH, RH | every rung | every fake | — |

## 7. Tools

**Developed.**
- The contact operator of a system and its Schur test with polar weights, for dominated systems
  and complex tests.
- Polar packets with an explicit smooth cutoff: masses, derivative energies, correlation
  inequalities; the upper bound $(5+\log q)\int f^2+\int f'^2-$ contacts for a form on a packet.
- The conductor ladder: system forms with a free conductor, feasible sets and their structure
  (between an $\ell^1$ ball and a box of the size of the mass), the trivial aperture as a threshold.
- Two-bump packets: isolation of a single contact.
- Calibration on fakes (Liouville twist, $\pm\Lambda$, lattice with a pair) and on true
  $L$-functions (twisted part with margin; companions of the zeros of $L(s,\chi)$ and of $\zeta$
  on a rung).
- The slack map of a system form: a floor is a conductor; a saving is a rung.
- The height aspect: modulated packets, the archimedean energy at a height from both sides, decay
  of the pole term, the mean of the phases over a window of heights, the aligned system.
- The height transfer: a system at a height is its twisted contacts at the analytic conductor.
- Summation by parts on the symbol: the exchange rate between cancellation and rungs, at the
  height zero and at every height; the symbol criterion for all packets; the receiver on the prime
  side: sum and difference of the two polar packets read the Riesz mean, at every height.
- Feasible sets with the pole plane: the first selective window of $\zeta$.
- Mean values over the heights: the mean square of a cosine polynomial on separated frequencies,
  the contact polynomial with its three sizes on a window, a common height for two means, the
  passage from a grid of heights to an interval.
- The product formula for the symbol of an aligned system, and the two budgets that reduce all
  sizes of a construction on the ladder to one inequality $Ka^{12}<e^a$.

**Aimed at.**
- A calibration bench: the criteria P1–P8 of §11 as predicates on a candidate mechanism, with the
  fakes of this folder as test objects.
- The feasible sets with pole plane beyond the aperture $181/500$: their shrinking rate to
  $\Lambda$ in terms of the margin of Weil's form.

## 8. Open research topics

1. **The exceptional square.** The sign of the twisted part at $\log\log q+C$ for one $C>0$.
2. **A rung above one.** The sign at $\kappa\log m$ for one $\kappa>1$ in one aspect: a zero-free
   strip of width $\tfrac12-\tfrac1{2\kappa}$ there.
3. **A producer step.** An unconditional power saving of the contacts of a true object on the
   integers up to a power of its mass; known savings start at $q^{1/4}$ and at
   $\exp((\log t)^{2/3})$.
4. **The separation on a rung.** The sign on bounded shapes and feasibility are separated at the
   aperture $\log\log q+\log2+\eta$. A dominated system with the sign on bounded shapes on a
   whole rung $\kappa>1$ and infeasible at the rung $1+o(1)$: second moments over the heights
   reach $\kappa<7/3$ by the same proof; every rung needs higher moments of the contact
   polynomial.
5. **The margin side.** The rate at which the feasible sets with pole plane shrink to $\Lambda$.
6. **The constant of the height.** The trivial aperture of the height lies between
   $\log\log|t|-\eta$ and $\log\log|t|+\log2+\eta$; the aligned system with signs
   $\mathrm{sgn}\cos(t\log n)$ would give $\log(\pi/2)$.

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
| The pole plane protects every height | It decays like $1/|t|$; a dominated system with its pole at the height $t$ fails there at $\log\log t+\log2+o(1)$ |
| A saving in the partial sums of the contacts is a saving at every height | The twist $w(n)\cos(t\log n)$ is another system; feasibility needs all of them, each against the analytic conductor $q(2+|t|)$ |
| Cancellation of the partial sums bounds the contact operator | It bounds the symbol with a factor $1+|\tau|$: the bound is for bounded shapes |
| The sign on every packet of bounded shape at an aperture is feasibility there | The system aligned with a quiet height of size $e^{8a}$ has the first at $\log\log q+\log2+\eta$ and is infeasible there |
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
