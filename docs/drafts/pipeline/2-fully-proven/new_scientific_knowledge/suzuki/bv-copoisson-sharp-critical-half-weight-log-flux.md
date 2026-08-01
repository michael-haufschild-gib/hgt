# Sharp BV co-Poisson critical-half-weight logarithmic flux

- **ID:** `bv-copoisson-sharp-critical-half-weight-log-flux`
- **Stage:** 2 — fully proven on paper
- **Type:** EXACT SOURCE NO-GO + POSITIVE LOG-FLUX SURVIVOR
- **Scientific status:** `[PAPER-PROVED] [CANDIDATE NEW NO-GO] [POSITIVE SURVIVOR] [NOT RH PROGRESS]`
- **Parent:**
  `../../../3-formalized/not_new_scientific_knowledge/bv-copoisson-principal-normal-connection-law.md`
- **RH used:** no
- **Computation used:** no
- **Lean:** Theorems A--C and E--G formalized unconditionally; Theorem D remains a paper-only,
  non-load-bearing boundary supplement

## Frontier changed

`BVPrimeWindowCoPoissonNormalConnection.lean` already proves that the pole-cancelled BV source
defines the normal derivative of the completed co-Poisson multiplier ideal and has the correct
forward/inverse dilation characters. The remaining metric question in the parent card is whether
Burnol's standard co-Poisson Hilbert norm supplies the missing critical-half-weight calibration.

The theorem below answers this for the canonical sharp dyadic seed:

```text
ordinary Burnol co-Poisson vector:       in L2,
critical-half-weight lift:               not in L2,
critical energy through height T:        (1/4) log T + o(log T).
```

Thus the standard quotient norm cannot be the critical BV conormal metric even on the first sharp
source. A surviving completion must be singular or renormalized and must explicitly carry the
nonzero logarithmic boundary flux.

This is a route closure, not a positive step toward RH.

## Exact source

Let

```text
g(x)=1_[1,2](x).
```

Burnol's right co-Poisson sum is

```text
P(t)=sum_(n>=1) g(t/n)/n - integral_1^2 dx/x
    =sum_(t/2<=n<=t) 1/n - log 2.                       (1)
```

Endpoint conventions change only a null set. For `m>=1`, put

```text
delta_m=log 2-(H_(2m)-H_m).                             (2)
```

Then, almost everywhere,

```text
P(t)=-delta_m,                    2m<t<2m+1,
P(t)=1/(2m+1)-delta_m,            2m+1<t<2m+2.          (3)
```

## Theorem A: sharp harmonic error bounds

For every `m>=1`,

```text
1/(8m) <= delta_m <= 1/(4m),                            (4)
0 < 1/(2m+1)-delta_m <= 1/(2m+1).                      (5)
```

### Proof

Since `x |-> 1/x` is decreasing,

```text
delta_m
 =sum_(k=m+1)^(2m) integral_(k-1)^k (1/x-1/k) dx
 =sum_(k=m+1)^(2m) integral_(k-1)^k (k-x)/(kx) dx.      (6)
```

On `[k-1,k]`,

```text
(k-x)/k^2 <= (k-x)/(kx) <= (k-x)/(k(k-1)).
```

After integration and summation,

```text
delta_m
 >=sum_(k=m+1)^(2m) 1/(2k^2)
 >=m/(2(2m)^2)=1/(8m),

delta_m
 <=sum_(k=m+1)^(2m) 1/(2k(k-1))
 =(1/2)(1/m-1/(2m))=1/(4m).
```

Because `1/(4m)<1/(2m+1)`, equation `(5)` follows.

## Theorem B: ordinary `L2` survives, critical half-weight fails

One has

```text
integral_0^infinity |P(t)|^2 dt < infinity,             (7)
integral_0^infinity t |P(t)|^2 dt = infinity.           (8)
```

### Proof

The bounded interval `(0,2)` is harmless. Equations `(3)`--`(5)` give

```text
integral_(2m)^(2m+2) |P(t)|^2 dt
 <=1/(16m^2)+1/(2m+1)^2,
```

whose sum converges. This proves `(7)`.

On only the even unit interval,

```text
integral_(2m)^(2m+1) t |P(t)|^2 dt
 >=2m delta_m^2
 >=1/(32m).
```

The harmonic series diverges, proving `(8)`.

Equivalently, the physical half-weight multiplication `P(t) |-> sqrt(t)P(t)` is outside Burnol's
standard `L2(0,infinity;dt)` carrier even though `P` itself is inside it.

## Theorem C: exact logarithmic boundary flux

As `T -> infinity`,

```text
integral_0^T t |P(t)|^2 dt / log T -> 1/4.              (9)
```

### Proof

From `(6)`, after writing `u=k-x`,

```text
m delta_m
 =sum_(k=m+1)^(2m) integral_0^1 m u/[k(k-u)] du.
```

This is a Riemann sum with limit

```text
integral_1^2 dx/x^2 * integral_0^1 u du = 1/4.          (10)
```

Hence

```text
m delta_m -> 1/4,
m(1/(2m+1)-delta_m) -> 1/4.                             (11)
```

Let `E_m` be the critical energy on `(2m,2m+2)`. By `(3)`,

```text
E_m
 =(2m+1/2) delta_m^2
  +(2m+3/2)(1/(2m+1)-delta_m)^2.
```

Equation `(11)` gives

```text
m E_m -> 1/4.                                           (12)
```

The standard harmonic Cesaro/Stolz consequence of `(12)` yields

```text
sum_(m<=M) E_m / log M -> 1/4.
```

Changing `2M` to arbitrary `T` affects at most one nonnegative block and does not change the
limit, proving `(9)`.

## Consequence for the RH route

The algebraic normal class and its dilation character do have a concrete ordinary Hilbert
realization for the sharp seed, but the half-unit shift needed by the BV residue orientation
lands exactly at a logarithmic domain wall. Therefore none of the following can close the route:

1. reuse Burnol's standard `L2` quotient norm unchanged;
2. apply the physical half-weight as a bounded graph map;
3. infer critical contractivity from ordinary co-Poisson square integrability;
4. ignore the boundary term as a null or compact error.

The strongest positive survivor is the canonical flux `(9)`. Any source-bornology proposed next
must either:

- subtract or represent the `(1/4) log T` principal boundary current before taking a finite part;
- enlarge the carrier to a singular graph in which this current is an explicit boundary
  coordinate; or
- prove that a coupled Gamma/prime channel cancels this exact coefficient before the norm is
  taken.

A scalar positive finite-part declaration is not admissible: corpus already rules out positive
cofinal finite parts for the full sharp source. The cancellation or singular coordinate must be
constructed from the source.

## Theorem D: Rademacher boundary mode and the failed singular graph

The logarithmic flux has an exact dyadic boundary mode.  Put, almost everywhere on the positive
axis,

```text
epsilon(t)=(-1)^(floor(t)+1),
Q_j(t)=2^j sqrt(t) P(2^j t),
b_j(t)=epsilon(2^j t)/(2 sqrt(t)),
R_j(t)=Q_j(t)-b_j(t),                    j in Z.          (13)
```

Then

```text
R_j in L2(1,infinity),
R_(j+2)(t)=2 R_j(4t),                                    (14)

lim_(T->infinity) 1/log(T) integral_1^T
  b_i(t) conjugate(b_j(t)) dt
  =(1/4) delta_(i,j).                                    (15)
```

Indeed, identity `(6)` gives the sharper elementary expansion

```text
delta_m
 =(1/2) sum_(k=m+1)^(2m) 1/k^2+O(sum_(k=m+1)^(2m)1/k^3)
 =1/(4m)+O(1/m^2).                                      (16)
```

On each of the two unit intervals in `(3)`, equation `(16)` gives

```text
sqrt(t)P(t)=epsilon(t)/(2sqrt(t))+O(t^(-3/2)).            (17)
```

This proves the first assertion in `(14)`; the covariance there is literal from `(13)`.
For `(15)`, the product

```text
epsilon(2^i t)epsilon(2^j t)
```

is periodic.  It has ordinary mean zero when `i!=j`, by dyadic Rademacher orthogonality, and equals
one almost everywhere when `i=j`.  A zero-mean periodic function has a bounded primitive, so
integration by parts shows its integral against `dt/t` is bounded.  This proves `(15)`.

Consequently every finite expression `Q=sum_j c_j Q_j` has the source-defined candidate norm

```text
||Q||_G^2
 =||sum_j c_j R_j||^2_(L2(1,infinity))
  +(1/4)sum_j |c_j|^2.                                  (18)
```

The representation is unique.  If `sum_j c_j Q_j=0`, then `sum_j c_j b_j` is in `L2(1,infinity)`;
equation `(15)` forces every `c_j=0`.  Under the orbit shift `D Q_j=Q_(j+2)`, equations
`(14)` and `(18)` give the exact positive Stein defect

```text
||Q||_G^2-||D Q||_G^2
 =integral_1^4 |sum_j c_j R_j(u)|^2 du >=0.              (19)
```

Thus the fixed physical cutoff restores a genuine contraction; using the full positive axis
instead would make the same construction dilation-unitary and erase the one-sided defect.

This graph nevertheless loses the RH-bearing principal part.  For `j->+infinity`,

```text
||R_j||^2_(L2(1,infinity))
 =integral_(2^j)^infinity |R_0(u)|^2 du ->0,
||Q_j||_G^2 ->1/4.                                      (20)
```

Any functional assigned the required BV conormal character

```text
L_s(Q_j)=C(s) 2^(j(s-1/2)),    C(s)!=0,                 (21)
```

is therefore unbounded whenever `Re(s)>1/2`.  In particular `(18)` cannot be the missing
BV-to-co-Poisson graph: it supplies positivity and contractivity but subtracts exactly the
boundary coordinate that carries the uncensored Laurent/conormal growth.

The positive survivor is `(19)`, not a route to RH.  Any viable successor must establish
covariance only modulo the completed co-Poisson multiplier ideal and recover `(21)` only on its
annihilator fibres.  Merely adding the Rademacher boundary coordinate cannot do so.

## Theorem E: multiplier-ideal density kills the logarithmic boundary quotient

The failure is class-level for this logarithmic boundary topology.  Let

```text
c_j(t)=1_(t>=2^(-j))/(2sqrt(t)),
beta_j(t)=1_(t>=2^(-j)) epsilon(2^j t)/(2sqrt(t)),
u_j=beta_j+c_j.                                         (22)
```

Compact initial intervals do not change logarithmic boundary classes, so every `c_j` represents
one constant class `e_0`, while `(15)` identifies `beta_j` with an orthogonal class `e_j`.
For `alpha=s-1/2` and `Re(alpha)>0`, direct interval integration gives

```text
integral_0^infinity u_j(t)t^(-s)dt
 =2^(j alpha) sum_(m>=0) integral_(2m+1)^(2m+2) x^(-alpha-1)dx
 =2^(j alpha) eta(alpha)/alpha.                         (23)
```

Thus `u_j` is exactly a dyadic character times the eta, hence zeta, multiplier ideal; no divisor
was selected.  Its logarithmic boundary class is

```text
[u_j]=e_0+e_j                                           (24)
```

in `C e_0 direct-sum ell2(Z)`.  The closed span of these ideal vectors is the whole space.  Indeed,
a vector `(a,x)` orthogonal to every `e_0+e_j` satisfies `x_j=-a` for every `j`; square
summability forces `a=0` and `x=0`.

Therefore the completed multiplier ideal is dense and its ordinary Hilbert quotient is zero in
this logarithmic-current topology.  Passing from `(18)` to the value quotient cannot recover the
normal class; a stricter jet/distribution topology is mandatory.  This is an explicit sharp-seed
witness of the broader corpus warning that bare Hilbert completion makes the zeta-multiplier
range dense and erases distributional zero classes.  It narrows the failed provider but is not a
new RH-bearing mechanism.

## Theorem F: the critical eta seed is excluded from Burnol's extended-property-S topology

The stricter topology does not rescue this particular seed.  Let `eta` denote the analytically
continued Dirichlet eta function and put

```text
F(s)=eta(s-1/2)/(s-1/2).                                (25)
```

By `(23)`, `F` is the positive-half-line Mellin transform of `u_0`.  It is meromorphic moderate,
with one simple pole at `s=1/2` and residue `eta(0)=1/2`.

Burnol's extended-property-S theorem gives an exact obstruction.  In even parity its Fourier-side
Mellin transform would have to be

```text
chi(s)F(1-s),
chi(s)=pi^(s-1/2) Gamma((1-s)/2)/Gamma(s/2).             (26)
```

The factor `chi` has a pole at every positive odd integer `s=1+2n`.  At these points

```text
F(1-s)=eta(-1/2-2n)/(-1/2-2n) !=0.                     (27)
```

Indeed `eta(z)=(1-2^(1-z))zeta(z)`; the elementary factor is nonzero at
`z=-1/2-2n`, while the zeta functional equation reduces nonvanishing there to
`zeta(3/2+2n)>0`.  Thus `(26)` has infinitely many poles.  It is not meromorphic moderate in
Burnol's sense, because no nonzero polynomial can clear its poles.

Odd parity fails identically.  Here

```text
chi_sin(s)=i pi^(s-1/2) Gamma((2-s)/2)/Gamma((s+1)/2)    (28)
```

has a pole at every positive even integer `s=2+2n`, whereas

```text
F(1-s)=eta(-3/2-2n)/(-3/2-2n) !=0.                     (29)
```

The same functional-equation argument proves the nonvanishing.  Hence no even or odd tempered
distribution with Burnol's extended property S has Mellin transform `(25)`.  Since
quasi-homogeneous corrections have zero Mellin transform in Burnol's normalization, they cannot
repair the failure.  Applying a polynomial in the Euler operator can cancel only finitely many of
the infinitely many Fourier-side poles.

This is a half-density resonance obstruction.  More generally, the odd-cell power seed

```text
u_gamma(t)=t^(-gamma) 1_(t in union_(m>=0)[2m+1,2m+2))
F_gamma(s)=eta(s+gamma-1)/(s+gamma-1)                   (30)
```

can pass the necessary even-parity pole-cancellation test only when
`gamma in 1+2 Z`, and the necessary odd-parity test only when `gamma in 2+2 Z`.  For all
sufficiently large reflected gamma poles, zeta has no left-half-plane zeros except the negative
even integers, so these congruence conditions are forced.  The Haar-weighted case `gamma=1`
therefore has the correct even resonance:

```text
chi(s) F_1(1-s)
  =(1-2^s) zeta(s)/(1-s),                               (31)
```

which has only finitely many poles.  The critical Hilbert half-weight `gamma=1/2` misses both
parity lattices.

The positive survivor is exact but negative for the route: the critical renormalization needed
for the logarithmic boundary Gram is incompatible with the additive Fourier gap defining
Burnol's extended Sonine topology.  Burnol's abstract theorem still realizes arbitrary finite
Laurent principal parts by starting from an unrelated strict-property-S distribution, but the
sharp eta seed does not source such a realization.  A successor must change the seed or couple
the half-density twist to an archimedean Fourier correction before completion; merely strengthening
the topology cannot work.

## Theorem G: no compact co-Poisson seed can repair the half-density resonance

The most direct source correction is impossible.  Let `g` be integrable and supported in a compact
interval `[a,b]` with `0<a<b`, and let

```text
A(s)=integral_0^infinity g(t)t^(-s)dt.                  (32)
```

Multiplicative convolution by `g` changes `(25)` to `A(s)F(s)`.  For an even extended-property-S
completion, every positive odd pole `s=1+2n` of `chi(s)` must be cancelled.  Since `(27)` is
nonzero, this forces

```text
A(-2n)=integral_a^b g(t)t^(2n)dt=0    for every n>=0.   (33)
```

Polynomials in `t^2` are uniformly dense in `C([a,b])`: the map `t -> t^2` is a homeomorphism
from `[a,b]` onto `[a^2,b^2]`, followed by Weierstrass approximation.  Hence `(33)` makes the
finite signed measure `g(t)dt` annihilate every continuous function, so `g=0` almost everywhere.

For odd parity, cancellation of the positive even poles in `(28)` instead forces

```text
A(-1-2n)=integral_a^b g(t)t^(1+2n)dt=0    for every n>=0. (34)
```

Apply the same density argument to the signed measure `t g(t)dt`; positivity of `t` on `[a,b]`
again gives `g=0` almost everywhere.

Thus no nonzero compact multiplicative seed, nor any finite linear combination of such
corrections, can turn the critical eta vector into an even or odd extended-property-S vector.
Any viable archimedean correction must be noncompact or must alter the seed before the critical
half-density twist.  The former leaves Burnol's compact co-Poisson source category and needs a new
bornology; the latter no longer preserves the exact Rademacher/logarithmic Gram `(15)`.

## Hostile audit

- [x] source formula `(1)` taken directly from Burnol's co-Poisson sum;
- [x] endpoint conventions confined to a null set;
- [x] no Euler--Maclaurin expansion needed for divergence;
- [x] ordinary and critical norms distinguished;
- [x] half-unit shift stated as physical multiplication by `sqrt(t)`;
- [x] no zero, divisor norm, RH sign, or numerical computation used;
- [x] leading logarithmic mode isolated as the dyadic Rademacher family;
- [x] fixed-cutoff graph proved contractive with exact defect `(19)`;
- [x] required Laurent/conormal functional proved unbounded on this graph by `(20)`--`(21)`;
- [x] multiplier-ideal boundary modes identified by the exact eta transform `(23)`;
- [x] ordinary logarithmic boundary quotient proved zero by dense ideal span `(24)`;
- [x] broader corpus collision found: bare Hilbert multiplier range already known to be dense;
- [x] Burnol extended-property-S criterion applied in both parities;
- [x] critical half-weight excluded by infinitely many uncancelled Fourier gamma poles;
- [x] strongest survivor extracted as the parity/weight resonance law `(30)`--`(31)`;
- [x] compact co-Poisson convolution repair ruled out by the all-moments density theorem;
- [x] independent audit of normalization and half-weight direction;
- [x] primary-literature priority audit against Burnol's co-Müntz and extended-property-S theorems;
- [x] completion-only question decided: the Gamma--Gaussian envelope realizes arbitrary moderate
  data, including off-line models, so existence of a coupled completion is nonselective;
- [x] formalize load-bearing Theorems A--C and E--G and wire the resulting modules;
- [ ] formalize supplementary analytic Rademacher Gram Theorem D; it is not used by any terminal
  no-go or by the provider disposition below.

## Independent audit and novelty boundary

Burnol's co-Müntz formula uses the right Mellin convention `integral f(x) x^(-s) dx` and the
source sum `sum_n f(x/n)/n`; this confirms `(1)` and confirms that multiplication by `sqrt(t)` is
the required positive half-unit shift.  Burnol's extended-property-S classification uses exactly

```text
chi(s)=pi^(s-1/2) Gamma((1-s)/2)/Gamma(s/2),
chi_sin(s)=i pi^(s-1/2) Gamma((2-s)/2)/Gamma((s+1)/2),
```

so the positive odd/even Gamma pole lattices in Theorem F have the stated orientation.  His
classification also permits only finitely many poles after multiplication by one polynomial;
the infinite uncancelled pole families therefore give a genuine obstruction.

Targeted searches of the co-Poisson, property-S, harmonic-error, and Rademacher-boundary
literature found no prior statement of the sharp `1/4` logarithmic flux, the dyadic boundary Gram,
or the compact-seed half-density resonance no-go.  Priority remains provisional, so result is
labelled candidate-new rather than externally certified new knowledge.  Classical inputs—Müntz,
Burnol's property-S theorem, harmonic estimates, Rademacher orthogonality, and polynomial
density—are not claimed as new.

## Lean closure and provider disposition

The unconditional formal boundary is now dependency-closed:

- `BVCoPoissonSharpCriticalFluxCore.lean` proves the sharp harmonic sandwich, a summable
  `O(m^-2)` block-energy error, exact cell integrals, and cutoff flux;
- `BVCoPoissonSharpCriticalFlux.lean` upgrades the cutoff result to arbitrary real `T`, proves
  `P in L2(0,infinity)`, and proves `t |P(t)|^2` is not integrable;
- `BVCoPoissonLogBoundaryQuotient.lean` proves the span of the ideal classes `e_0+e_j` is dense;
- `BVCoPoissonHalfWeightResonance.lean` proves the two reflected eta lattices are nonzero and no
  nonzero polynomial cancels either infinite pole family;
- `BVCoPoissonCompactSeedRigidity.lean` proves, for arbitrary finite measures on a positive compact
  interval, that vanishing of all even or odd moments forces the density to vanish almost
  everywhere.

`#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound` for all exported
terminal theorems. No theorem assumes RH, a zeta-zero hypothesis, a source sign, or a numerical
certificate.

This closes the proposed compact BV/co-Poisson completion provider, not RH. Alternatives are
exhaustive for this provider family:

```text
ordinary Burnol L2 completion       -> critical half-weight leaves the carrier;
logarithmic boundary quotient       -> multiplier ideal is dense, quotient is zero;
extended property-S, sharp eta      -> infinite parity-resonance obstruction;
compact multiplicative correction  -> all-moments rigidity forces zero seed;
noncompact Gamma--Gaussian repair   -> exists for arbitrary moderate data, hence is nonselective.
```

What remains is not another completion theorem. It is source-generated causal-dagger positivity
on the completed principal conormal. Contractivity of that source-selected dagger, combined with
the already proved conormal dilation character, is precisely the RH-bearing implication. Treating
it as routine functional analysis would assume desired orientation. This provider family is
therefore terminalized. At this card's historical checkpoint Route G remained open at Suzuki's
source-coefficient, chord-mass, and global Pick/Ward mechanism. The later gauge-complete
target-category theorem in `suzuki-holomorphic-gauge-characteristic-limit.md` retires Suzuki's
published one-angle limit without changing this provider proof or closing Route G. Its two-angle
meromorphic survivor remains the route's live core, not a fourth topology or graph completion.

Theorem D records a genuine analytic positive survivor—an exact Rademacher logarithmic Gram and
Stein defect—but its conormal is unbounded. Its remaining Lean formalization cannot change the
terminal implication and is deliberately not represented by an abstract `ell2` surrogate.
