# Height-sector Ward graph contraction

- **ID:** `height-sector-ward-graph-contraction`
- **Stage:** `5-failed`
- **Type:** `[RETIRED CONJECTURE] [NO-GO WITH POSITIVE SURVIVOR]`
- **Scientific status:** `[THEATRE REMOVED] [TWO-CHART OBSTRUCTION PAPER-PROVED]`
  `[LEAN SOURCE PRESENT; CHECK PENDING] [NOT RH]`
- **Parents:**
  - `mobius-incidence-curvature-gamma-sonin-pole-divisor-transfer-rh.md`
  - `xi-source-completion-polarization-architecture.md`
  - `../2-fully-proven/not_new_scientific_knowledge/07-functional-analysis-operator-theory/prime-poisson-superselection-screen.md`
  - `../2-fully-proven/not_new_scientific_knowledge/11-rh-zero-divisor-geometry/euler-pole-four-unit-anti-causal-budget-law.md`

## Retirement verdict

The conjecture below is retained only as the exact autopsy of a dead route.  It is not the current
RH target.

1. `HSW-1` has no independently constructed intermediate graph domain.  In the strict Euler
   half-plane ordinary division is routine; at the critical boundary Hardy-range membership
   already requires cancellation at the squarefree zeros, while a maximal meromorphic graph makes
   the quotient tautological.
2. `HSW-2` does not define its external graph norm before seeing the response.  Together with
   `HSW-3` it is the four-unit RH estimate in renamed form.
3. `HSW-3` mixes the already-formalized identity `P_anti Q_sq = ell_E` with the genuinely missing
   prime-cofinal/critical continuation theorem.
4. Source modulation and translated aperture both encode the same physical height; the card never
   supplied the pairing which would prevent double counting.

The widening strip nevertheless exposes a sharp positive obstruction.  Put `epsilon=sigma-1` and

```text
B_sigma(z)=Z_sq(sigma+epsilon z)/Z_sq(sigma).
```

For `delta>=0`, fixed `gamma!=0`, and microscopic coordinate `eta`,

```text
B_(1+epsilon)(delta+i gamma/epsilon)
  ~ epsilon zeta(2) Z_sq(1+i gamma),

B_(1+epsilon)(delta+i eta)
  -> 1/(1+delta+i eta).
```

Thus this specific overlap has two inequivalent critical charts.  It stays nondegenerate on the
contact scale `gamma=epsilon eta`, but collapses linearly at every fixed nonzero physical height.
The forced `epsilon^(-1)` macroscopic normalization is singular at height zero.  This refutes the
single uniformly nondegenerate widening-strip trivialization demanded by `HSW-2`; it does not rule
out every other source gauge or prove that every RH route needs two-chart gluing.

The positive survivor is the **squarefree height Rees blow-up**: a microscopic Cauchy chart and a
renormalized fixed-height chart with their source transition.  The dependency-closed Lean source
is `formal/GaloisForLFunctions/RHTower/SquarefreeHeightReesBlowup.lean`; its direct check is pending
because another shared Lean build owns the only allowed foreground slot.

The direct declaration-backed target is now the positive-frequency sign of the explicit continued
prime--archimedean source response.  A concrete Gamma--Möbius characteristic colligation on the
globally summable valuation-difference source is only a candidate producer for that sign, not the
theorem-forced replacement.  Its first finite coefficients must equal the already-formalized
Euler--Gamma anomaly before any two-chart completion or graph closure is attempted.  A mismatch
kills the candidate immediately.

## The conjectural object

For `sigma > 1`, put `epsilon = sigma - 1` and let

```text
psi_sigma(d) = Z(sigma)^(-1/2) mu(d) d^(-sigma/2)
```

be the normalized squarefree Mobius source line.  For a real height `gamma`, define the source
modulation

```text
(M_gamma f)(d) = d^(-i gamma) f(d),
psi_(sigma,gamma) = M_gamma psi_sigma,
Pi_(sigma,gamma) = |psi_(sigma,gamma)><psi_(sigma,gamma)|.
```

Let `P_(sigma,u)` be the source cutoff `epsilon log d <= u`.  Since `M_gamma` commutes with this
cutoff, the pointed Fisher--Ward edge

```text
W_(sigma,u,gamma)
 = [P_(sigma,u), 2 sqrt(2) epsilon partial_sigma Pi_(sigma,gamma)]
```

is defined entirely from the signed all-prime source.  Its source Hilbert--Schmidt energy is
independent of `gamma`; the existing critical cutoff calculation gives the candidate limiting
budget

```text
E_W(u)
 = 4 ((2+u^2) exp(-u) - 2 (1+2u^2) exp(-2u)),
E_W(u) <= 8 (1-exp(-u)),
E_W(u)/(2u) -> 4 as u -> 0+.
```

The proposed RH-bearing object is **not** `W` alone.  It is the closed graph quotient obtained only
after applying, in order,

```text
complementary floor--Mobius packet
  -> calibrated Gamma multiplier
  -> Sonin cutoff/resolvent
  -> charged squarefree-overlap multiplication graph.
```

For the complementary packet path `B_h` from the parent card, the finite source kernel is explicitly

```text
K^B_(sigma,gamma)(d,e)
 =2 psi_sigma(d) psi_sigma(e)
   exp(i gamma (log e-log d))
   (B_(log e)-B_(log d)).
```

Its completed finite numerator is, entry by entry,

```text
N_(sigma,omega,tau,D,gamma)(d,e)
 =Q_tau^Sonin mathcalG_(omega,gamma)
    K^B_(sigma,gamma)(d,e),
```

where the height-covariant completion is the conjugated source family

```text
mathcalG_(omega,gamma)
 =T_(-gamma) mathcalG_omega T_gamma,
Q_(tau,gamma)=T_(-gamma)Q_tau T_gamma.
```

Equivalently, its Gamma symbol is evaluated at the translated boundary height.  A fixed unshifted
Gamma/Sonin operator is not height covariant and is not admissible.  Conjugation preserves every
finite operator norm and the four-unit source budget; the unresolved step is the charged quotient
and its cofinal continuation.

Write `B_(sigma,gamma)` for the completed squarefree overlap acting by multiplication on the
resulting boundary carrier.  Neither this overlap nor the numerator may be defined from an Xi zero,
an Xi leakage norm, or a target Gram factorization.

## The necessary two-scale domain

The source overlap already has a complex aperture parameter

```text
B_sigma(z)=Z_sq(sigma+(sigma-1)z)/Z_sq(sigma),
Re z>=0.
```

A fixed physical height `gamma` is the widening-strip point

```text
z_(sigma,delta,gamma)=delta+i gamma/(sigma-1),
sigma+(sigma-1)z_(sigma,delta,gamma)
 =(sigma+delta(sigma-1))+i gamma.                       (WS)
```

Thus every fixed bounded `z`-window collapses to height zero as `sigma -> 1+`.  Exact height
resolution requires uniform control on imaginary aperture of order `(sigma-1)^(-1)`.  The
contraction conjecture below is therefore a widening-strip estimate, not a fixed-aperture limit.

## Conjecture HSW-1: height-sector graph divisibility

For every `sigma > 1`, `delta > 0`, `omega > 0`, finite squarefree aperture `D`, cutoff `u > 0`,
and height `gamma`, evaluate the completed Ward numerator at the source point `(WS)`.  Then

```text
N_(sigma,delta,omega,tau,D,u,gamma)
 = (Q_(tau,gamma) mathcalG_(omega,gamma))
     (K^B_(sigma,gamma)|_(D x D))
```

belongs to the range of the closed multiplication operator `M_(B_(sigma,gamma))` on the
source-selected doubled graph core.  Thus there is a graph quotient `Q` satisfying

```text
M_(B_(sigma,gamma)) Q_(sigma,delta,omega,tau,D,u,gamma)
 = N_(sigma,delta,omega,tau,D,u,gamma).                 (HSW1)
```

This is a divisibility/range conjecture, not a declaration that `N/B` exists meromorphically.
Zeros of `B` are precisely where ordinary pointwise division loses the strict anti-causal charge.
The source graph must prove divisibility before any divisor expansion.

## Conjecture HSW-2: sharp graph-quotient contraction

The quotient in `(HSW1)` is holomorphic for `delta>0` and obeys the source-framed widening-strip
estimate

```text
limsup_(D -> all, delta -> 0+, omega -> 0+)
  ||Q_(sigma,delta,omega,tau,D,u,gamma)||_(HS,ext)^2
 <= ||W_(sigma,u,gamma)||_HS^2,                         (HSW2a)
```

uniformly for `gamma` in every bounded real interval, with a bound independent of the widening
factor `1/(sigma-1)`, and therefore

```text
limsup_(sigma -> 1+)
  ||Q_(sigma,delta,omega,tau,D,u,gamma)||_(HS,ext)^2
 <= E_W(u).                                             (HSW2b)
```

The norm is the graph norm fixed by the packet/Gamma/Sonin construction.  Rescaling the quotient,
choosing a polar factor after seeing the target, or assuming bounded inversion of `B` is forbidden.
The one-pole capacity law proves that no ordinary fixed-line Hardy norm can satisfy `(HSW2)` as a
horizontal displacement tends to zero.

## Conjecture HSW-3: height-local contour-jump identification

For each fixed `u > 0` and real `gamma`, the ordered cofinal limit of the graph quotients is the
height-localized strict anti-causal Ward commutator of the completed Xi current:

```text
D -> all, then delta -> 0+, then omega -> 0+, then sigma -> 1+,

Q_(sigma,delta,omega,tau,D,u,gamma)
  -> [P_(u,gamma), D_Xi]                                (HSW3)
```

weakly in the extended Hilbert--Schmidt carrier and strongly on the source graph core.  The right
side is characterized as the contour jump between the Euler-line continuation and the critical
boundary continuation of the same completed source.  It may not be defined by first expanding the
Xi divisor.

The `gamma`-family is fiberwise rather than a graph inside one common critical Hilbert space.
The prime-Poisson theorem proves that distinct critical heights are mutually disjoint sectors.
Thus `(HSW3)` uses the all-prime source to localize height exactly and does not take a finite
aperture limit inside one saturating graph.

## RH consequence

Assuming `(HSW1)`--`(HSW3)`, lower semicontinuity and `(HSW2b)` give

```text
limsup_(u -> 0+) (1/(2u))
  ||[P_(u,gamma),D_Xi]||_(HS,ext)^2 <= 4
```

at every height.  The existing pole-to-divisor Cauchy-energy theorem says that one right-half Xi
layer has energy strictly greater than four.  Hence no right-half layer exists, and functional
equation symmetry gives RH.

This implication is a consumer.  The new mathematical content would be the explicit range theorem
`(HSW1)`, the source-derived inequality `(HSW2)`, and the pre-divisor continuation identity
`(HSW3)`.

## Anti-theatre audit

1. **The height-twisted Mobius coisometry is not the conjecture.**  It is a direct unitary twist of
   an existing source contraction.
2. **Critical height orthogonality is not the conjecture.**  It is already the prime-Poisson
   superselection theorem and is classified as a bridge.
3. **An abstract contraction from the pole vector to `ell_E` is rejected.**  Its existence is the
   desired RH bound in operator language.
4. **A common ambient graph for all heights is rejected.**  HT graph saturation would make the
   positive/transverse graph dense, while the critical prime sectors are actually disjoint.
5. **A fixed `sigma`, finite prime set, or fixed `u` is rejected.**  It retains only finite
   resolution and cannot see arbitrarily small horizontal displacement.
6. **A multiplier depending only on absolute squarefree weights is rejected.**  It is invariant
   under centered rational quartet insertion and therefore misses the required residue charge.
7. **Pointwise division by `B` is rejected.**  The missing theorem is exactly graph divisibility at
   its possible zeros.

## Mandatory falsifiers

- **Quartet covariance.**  Replacing the completed source by `A Xi`, for a centered FE--Schwarz
  rational quartet polynomial `A`, must change the quotient by the explicit anti-causal residue
  packet of `A`.  If the construction is invariant, it is source-gauge blind and dead.
- **One-pole capacity.**  In the formal one-pole model the graph-domain budget must grow like the
  inverse horizontal displacement.  A uniform ordinary-Hardy bound falsifies the claimed graph.
- **Order of limits.**  Any exchange of the prime-cofinal and critical limits needs an explicit
  uniform graph estimate.  Pointwise convergence is insufficient.
- **Widening strip.**  A proof only for bounded complex aperture `z` has height resolution tending
  to zero and does not address the conjecture.  The estimate must reach `Im z=gamma/(sigma-1)`.
- **Sector covariance.**  Source modulation by `gamma` must become height translation after
  Gamma/Sonin completion.  Failure of this intertwining kills height localization.
- **No target normalization.**  Every finite entry and norm must be fixed before evaluating Xi or
  its divisor.

## Gates

- [x] source line, Fisher connection, cutoff commutator, and four-unit source budget exist
- [x] Gamma/Sonin entrywise passivity exists
- [x] exact floor--Mobius packet and Euler-current weld exist
- [x] critical height sectors are source-derived and mutually disjoint
- [x] conjectures and falsifiers stated without defining the operator from Xi leakage
- [x] identify the necessary widening-strip scale `Im z=gamma/(sigma-1)`
- [ ] prove source modulation/Gamma--Sonin height covariance on the common finite graph core
- [ ] prove the completed finite numerator is holomorphic with uniform graph control on widening
      strips
- [ ] construct the closed multiplication graph and prove `(HSW1)`
- [ ] prove the sharp nonexpansive quotient estimate `(HSW2)`
- [ ] prove the pre-divisor contour-jump limit `(HSW3)`
- [ ] formalize only unconditional, dependency-closed survivors
- [ ] external specialist novelty audit
- [ ] RH
