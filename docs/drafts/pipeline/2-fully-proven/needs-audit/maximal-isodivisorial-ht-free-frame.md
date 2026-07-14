# Maximal isodivisorial hypertranscendental free-frame law

- **ID:** `maximal-isodivisorial-ht-free-frame`
- **Stage:** 2-fully-proven / needs independent novelty audit
- **Type:** THEOREM CANDIDATE / GENERAL HT LANDSCAPE LAW / RH ROUTE CONSTRAINT
- **Scientific status:** `[PROVED ON PAPER] [SIGNIFICANCE PASSES] [NOVELTY HOLD]`
- **Parent:** `finite-euler-gauge-critical-divisor-tail-charge.md`

## Constraint

For a unimodular completely multiplicative phase `chi`, put

```text
Z_chi(s) = product_p (1-chi(p)p^(-s))^(-1),
P_chi(s) = sum_p chi(p)p^(-s),                         Re(s)>1.
```

The first function carries the continued zero/pole divisor.  The second is its logarithmic
prime-layer source and carries the differential matroid seen by prime derivations.  The question
is whether fixing a critical-strip divisor, even together with arbitrary finite prime data,
restricts the hypertranscendental source geometry.

## Theorem

Let

```text
Scrit = {s : 0 < Re(s) < 1}
```

and let `D` be a signed divisor locally finite on the positive half-plane, with support contained
in `Scrit`.  Let `C` be any nonempty basic cylinder in the prime-phase torus.  There exists a
family

```text
{chi_alpha : alpha < 2^aleph_0} subset C
```

with the following properties.

1. Every `Z_(chi_alpha)` extends meromorphically to `Re(s)>0` and

   ```text
   div(Z_(chi_alpha)) on {Re(s)>0} = D.
   ```

2. Every `Z_(chi_alpha)` is hypertranscendental on its initial half-plane.

3. For every finite set of distinct indices and every finite shift--jet rectangle, the
   corresponding prime-layer sources `P_(chi_alpha)` are differentially algebraically independent
   over the finite-prime Dirichlet differential field `E_fin`.

4. The cardinal `2^aleph_0` is maximal: the space of holomorphic functions on a half-plane itself
   has cardinality `2^aleph_0`.

Thus every positive-half-plane divisor fiber is locally saturated, in every finite-prime cylinder,
by a maximal free hypertranscendental frame.

## Construction

### 1. A divisor realizer in the prescribed cylinder

`[CLASSICAL INPUT]` Andersson's theorem, applied with `U={Re(s)>0}`, gives a Helson phase `chi_D`
meromorphic on the positive half-plane with divisor `D` there.  The cylinder fixes only finitely
many prime coordinates.  Overwrite those coordinates by values in the prescribed arcs.  The finite
Euler ratio is a holomorphic unit on `Re(s)>0`, so the resulting phase `eta` lies in `C`, remains
meromorphic there, and still has positive-half-plane divisor `D`.

### 2. The canonical exponent-zero Euler gauge group

Define

```text
G_0 = {omega in product_p S^1 :
         sum_p abs(1-omega(p)) p^(-sigma) < infinity for every sigma>0}.
```

This is a subgroup of the phase torus: closure under products follows from
`abs(1-omega psi) <= abs(1-omega)+abs(1-psi)`, and inversion preserves
`abs(1-omega)`.  It is canonical and does not depend on a divisor or a chosen Helson phase.

If `eta` has meromorphic continuation to `Re(s)>0` and `omega in G_0`, then

```text
Z_(eta omega)(s) / Z_eta(s)
  = product_p (1-eta(p)p^(-s))/(1-eta(p)omega(p)p^(-s))
```

converges normally on every compact subset of `Re(s)>0` to a holomorphic nonvanishing function.
Indeed, on a compact with `Re(s)>=sigma>0`, every sufficiently large local ratio differs from one
by at most a fixed multiple of `abs(1-omega(p))p^(-sigma)`.  Consequently `G_0` acts freely on the
phase torus by isodivisorial transformations: every positive-half-plane divisor fiber is a union
of canonical `G_0`-orbits.

### 3. An exponent-zero sparse prime reservoir

Choose an infinite prime set `S_*`, disjoint from the cylinder coordinates, such that

```text
sum_(p in S_*) p^(-sigma) < infinity       for every sigma>0.
```

For example, choose its `n`-th prime recursively larger than `2^(n^2)`.  The complement of `S_*`
is infinite because the sum of reciprocal primes diverges while the reciprocal sum over `S_*`
converges.

Choose a continuum-sized almost-disjoint family `{A_alpha}` of infinite subsets of `S_*`, with
every pairwise intersection finite.  Define signs

```text
epsilon_alpha(p) = -1  if p in A_alpha,
                     1  otherwise,
chi_alpha(p)     = eta(p) epsilon_alpha(p).
```

Every sign gauge belongs to `G_0`, and all phases remain in `C`.

### 4. Exact isodivisoriality

For `Re(s)>1`,

```text
Z_(chi_alpha)(s) / Z_eta(s)
  = product_(p in A_alpha)
      (1-eta(p)p^(-s))/(1+eta(p)p^(-s)).                 (1)
```

On every compact subset of `Re(s)>0`, the logarithms of the factors in `(1)` are bounded by a
constant times `p^(-sigma)` for some `sigma>0`.  The sparse-prime hypothesis gives normal
convergence.  Hence `(1)` defines a holomorphic nonvanishing function on `Re(s)>0`.  Multiplication
by it preserves the entire divisor there, proving property 1.  This is the sign-gauge
specialization of the canonical `G_0` action.

### 5. Maximal differential freedom

Take distinct `alpha_1,...,alpha_m` and suppose

```text
c_1 epsilon_(alpha_1) + ... + c_m epsilon_(alpha_m)
```

has finite prime support.  Outside the finite union of the `A_(alpha_j)`, on the infinite
complement of `S_*`, its value is `C=sum_j c_j`; hence `C=0`.  For a fixed `k`, the set

```text
A_(alpha_k) minus union_(j != k) A_(alpha_j)
```

is infinite by almost-disjointness.  On that set the displayed combination equals
`C-2c_k=-2c_k`, so `c_k=0`.  Therefore every finite subfamily of the sign classes is linearly
independent modulo finite support.  Multiplication by the nowhere-zero common phase `eta(p)` does
not change this tail rank.

The Shapiro--Sparer/Pong prime-derivation criterion, with the shifted jet-rank extraction already
proved for tail-independent prime coefficients, makes every finite shift--jet rectangle of the
sources `P_(chi_alpha)` differentially algebraically independent over `E_fin`.  Pong's
Theorem 5.3, applied to the coefficient function `chi_alpha` and the injective logarithmic
multiplier, gives property 2: `chi_alpha` has full support and therefore is not supported on any
finitely generated prime semigroup.

### 6. Cardinal maximality

The construction supplies `2^aleph_0` distinct phases, hence that many distinct prime-layer
sources.  Conversely a holomorphic function on a half-plane is determined by its values on any
fixed countable dense subset.  The set of all such value sequences has cardinality
`card(C^N)=2^aleph_0`.  No holomorphic frame can therefore have larger cardinality.

## Full rectangular law

The theorem realizes, simultaneously,

```text
arbitrary finite prime chamber,
arbitrary admissible positive-half-plane divisor supported in the critical strip,
maximal continuum-rank HT source frame.
```

None of these three coordinates constrains either of the other two.  The scientific object is the
local saturation geometry of the divisor fiber, not the standard ingredients used in its proof.

Combined with the universal free-field/arbitrary-divisor theorem, this gives both directions of
source--divisor orthogonality:

```text
fixed abstract HT field type  + arbitrary divisor,
fixed exact divisor           + maximal HT source freedom.
```

The canonical object behind the second line is not merely a large set: it is the exponent-zero
Euler gauge group `G_0`, acting inside every divisor fiber, with each local orbit containing a
maximal free frame.

## Positive RH necessity

The Riemann critical-strip zero divisor is therefore compatible, inside every finite Euler chamber,
with a maximal family of independent hypertranscendental prime sources.  A route to RH cannot
characterize the zeta source using any combination of:

- finite prime coordinates;
- the critical-strip divisor alone;
- abstract differential-field type or differential transcendence degree;
- the complete finitary differential matroid of the prime layer.

> **Sparse-gauge-sensitive polarization law.**  An RH-capable carrier must contain a coupling that
> changes under exponent-zero sparse Euler gauges even though the entire critical divisor does
> not.  The scale-one functional equation, its archimedean reflection cocycle, and positive Euler
> orientation are therefore load-bearing incidence data, not optional decorations.

## Attacks

1. **Grosswald--Schnitzer attack.**  Preservation of the Riemann divisor under large Euler
   deformations is classical.  The new candidate is not same-zero deformation alone, but maximal
   differential-matroid saturation of every prescribed divisor fiber inside every finite chamber.
2. **Andersson attack.**  Arbitrary divisors are classical.  Andersson does not identify the local
   topology or differential-algebraic size of each divisor fiber.
3. **Pong/Shapiro attack.**  Differential independence from tail rank is classical infrastructure.
   It does not supply an isodivisorial family or the continuum local-saturation statement.
4. **Set-theory attack.**  Continuum almost-disjoint families are standard.  Their role is to make
   the differential freedom maximal, not to provide novelty by themselves.
5. **Domain attack.**  Sparse Euler gauges need only continue to `Re(s)>0`; they may have a natural
   boundary at `Re(s)=0`.  The theorem claims an exact positive-half-plane divisor supported in the
   critical strip, not global meromorphicity of every frame member.
6. **Functional-equation attack.**  The sparse gauges generally destroy the Riemann functional
   equation.  This is the positive conclusion: reflection coupling is precisely what the divisor
   and HT matroid fail to retain.
7. **Routine-corollary attack.**  The proof is short after four parent results are assembled.  The
   novelty gate passes only if the maximal local rectangular saturation and its incidence
   consequence are absent from the literature and judged mathematically substantive.
8. **General fixed-divisor-freeness attack.**  The project already proves that arbitrary entire
   divisor fibers support full complex-translation free families after unrestricted exponential
   gauging.  The extra content here is narrower but arithmetically rigid: the family stays inside
   the Helson Euler-product class, inside every finite Euler chamber, and inside one canonical
   exponent-zero Euler-gauge orbit.
9. **Boundary-local-finiteness attack.**  Local finiteness only in the open critical strip is not
   sufficient, because a sequence could accumulate on `Re(s)=1`, which is interior to the claimed
   continuation half-plane.  The theorem therefore assumes local finiteness on all of `Re(s)>0`
   and support in the critical strip.

## Gates

- [x] exact theorem and maximal-cardinality claim stated
- [x] complete paper proof of sparse-gauge isodivisoriality
- [x] complete paper proof of continuum tail independence
- [x] complete paper proof of local cylinder saturation
- [x] exact positive RH necessity stated
- [x] canonical exponent-zero Euler gauge group and its isodivisorial action proved on paper
- [x] formalize the almost-disjoint tail-independence core
- [x] formalize the abstract isodivisorial-unit transfer
- [x] primary audit of Grosswald--Schnitzer, Seip/Bohr, Bochkov--Romanov, Andersson, and Pong
- [x] dual-gate decision: significance passes; novelty held for independent specialist review

## Novelty verdict

The proof and significance gates pass at paper level.  The theorem identifies a precise
RH-relevant blindness class inside the arithmetic Euler-product category, not merely among
unrestricted meromorphic functions.  Exact searches and inspection of the primary parents found
prescribed divisors, construction freedom, same-zero modified Euler products, and differential
independence separately, but not the canonical `G_0`-orbit law or maximal differential free frames
inside every local divisor fiber.

The novelty gate remains provisional.  Seip's constructions already retain considerable choice,
and the present proof becomes short once four parent results are assembled.  Independent
specialist review is required before applying a new-scientific-knowledge label.

## Primary literature

- E. Grosswald and F. J. Schnitzer, *A class of modified zeta and L-functions*, Pacific J. Math.
  74 (1978), 357--364.
- W. Y. Pong, *Applications of differential algebra to algebraic independence of arithmetic
  functions*, Acta Arith. 172 (2016), 149--173.
- K. Seip, *Universality and distribution of zeros and poles of some zeta functions*, J. Anal.
  Math. 141 (2020), 331--381.
- I. Bochkov and R. Romanov, *On zeroes and poles of Helson zeta functions*, J. Funct. Anal. 282
  (2022), 109398.
- J. Andersson, *Mittag-Leffler type theorems for Helson zeta-functions*, arXiv:2408.15713.
