# Exponent-zero Euler-gauge foliation and rigid reflection transversal

- **ID:** `exponent-zero-euler-gauge-foliation-reflection-transversal`
- **Stage:** 3-formalized / needs independent novelty audit
- **Type:** THEOREM / GENERAL HT LANDSCAPE LAW / RH CARRIER GEOMETRY
- **Scientific status:** `[PROVED ON PAPER] [FORMALIZED IN LEAN 4] [SIGNIFICANCE PASSES] [NOVELTY HOLD]`
- **Parents:** `maximal-isodivisorial-ht-free-frame`,
  `finite-euler-gauge-critical-divisor-tail-charge`,
  `euler-support-transverse-divisor-rigidity`

## Constraint

Let

```text
Omega = product_(p prime) S^1
```

be the Helson prime-phase torus.  For `chi in Omega`, write

```text
Z_chi(s) = product_p (1-chi(p)p^(-s))^(-1),   Re(s)>1,
P_chi(s) = sum_p chi(p)p^(-s).
```

Define the canonical exponent-zero gauge group

```text
G_0 = {omega in Omega :
         sum_p abs(1-omega(p))p^(-sigma) < infinity
         for every sigma>0}.
```

The question is whether the exact continued divisor, the complete HT source matroid, and a
scale-one reflection law are three unrelated labels, or parts of one forced geometry.

## Theorem

### A. Dense principal foliation

`G_0` is a subgroup of `Omega`.  Its multiplication action is free, and every orbit is dense in
the product topology.  Hence the orbit space `Omega/G_0`, equipped with its quotient topology, is
indiscrete.  There are exactly `2^aleph_0` distinct orbits, every one dense and codense.

### B. Isodivisorial maximal HT leaves

Suppose `Z_eta` has meromorphic continuation to the positive half-plane.  Then the complete
`G_0`-orbit of `eta` remains meromorphic there and has the same signed divisor at every point of
`Re(s)>0`.

More strongly, inside every finite prime cylinder the orbit contains a family

```text
{eta_alpha : alpha < 2^aleph_0}
```

such that:

1. every `Z_(eta_alpha)` has the same complete positive-half-plane divisor as `Z_eta`;
2. every `Z_(eta_alpha)` is hypertranscendental;
3. every finite family of prime-layer sources `P_(eta_alpha)`, with every finite shifted-jet
   rectangle, is differentially algebraically independent over the finite-prime Dirichlet
   differential field.

Thus every continuable `G_0`-leaf is simultaneously topologically dense, divisor-rigid, and of
maximal differential rank.

### C. Reflection is a rigid transversal

Fix one order-one completed Euler class: common conductor, common Gamma factor, normalized first
Dirichlet coefficient, and a functional equation centred on `Re(s)=1/2`.  Among members satisfying
the standard finite-order continuation hypotheses, every `G_0`-orbit meets this completed
reflection class in at most one point.

In particular, the orbit through the positive phase has the exact geometry

```text
dense maximal-rank same-divisor HT leaf
                 intersect
fixed Riemann completion and reflection class
                 =
the positive zeta phase.
```

The equality in the last display is a source-selection statement, not RH: it selects `zeta` inside
its isodivisorial leaf but does not locate the selected member's zeros.

## Proof

### 1. `G_0` is a group

For unimodular phases,

```text
abs(1-omega(p)psi(p))
  <= abs(1-omega(p))+abs(1-psi(p)),
abs(1-omega(p)^(-1))=abs(1-omega(p)).
```

Summability at every positive exponent is therefore preserved under multiplication and inversion;
the identity has zero gauge cost.

### 2. Every orbit is dense and the quotient is indiscrete

Every finite-support phase change belongs to `G_0`.  Given `eta` and a basic cylinder prescribing
finitely many prime coordinates, choose the finite gauge that changes exactly those coordinates.
Thus `G_0 eta` meets every cylinder and is dense.

The action is free because `eta omega=eta` pointwise and `abs(eta(p))=1` imply `omega(p)=1` for
every prime.  If a nonempty proper subset of `Omega/G_0` were open, its inverse image would be a
nonempty proper open saturated subset of `Omega`.  A dense orbit from the complement would have to
meet it, a contradiction.  Hence the quotient topology is indiscrete.

For each `theta in S^1`, let `c_theta(p)=theta` at every prime.  If `theta!=phi`, then

```text
sum_p abs(1-c_theta(p)^(-1)c_phi(p))p^(-sigma)
```

is a nonzero constant multiple of `sum_p p^(-sigma)`, which diverges for `0<sigma<=1`.
Therefore the constant phases lie in pairwise distinct `G_0`-orbits, giving continuum many.
The phase torus itself has cardinal continuum, so this is exact.  A second dense orbit proves that
every orbit is codense.

### 3. The action preserves the complete positive-half-plane divisor

For `omega in G_0`, initially on `Re(s)>1`,

```text
Z_(eta omega)(s)/Z_eta(s)
 = product_p (1-eta(p)p^(-s))/(1-eta(p)omega(p)p^(-s)).       (1)
```

Fix a compact set in `Re(s)>0` and choose `sigma>0` below its minimum real part.  After deleting
finitely many primes, both local denominator moduli are uniformly bounded away from zero and the
local ratio in `(1)` differs from one by at most

```text
C abs(1-omega(p))p^(-sigma).
```

The defining `G_0` sum gives normal convergence.  The logarithmic form converges normally as well,
so `(1)` is a holomorphic nonvanishing function on `Re(s)>0`.  Multiplication by this unit preserves
every local meromorphic order, hence the complete divisor.

### 4. Every leaf contains a maximal differential frame locally

First use a finite gauge to move `eta` into the prescribed cylinder.  Outside its finite support,
choose a super-sparse prime reservoir `S_*` satisfying

```text
sum_(p in S_*) p^(-sigma) < infinity    for every sigma>0.
```

On a continuum almost-disjoint family of infinite subsets `A_alpha` of `S_*`, flip the signs.
Each sign gauge belongs to `G_0`.  In every finite subfamily, each `A_alpha` has an infinite private
block and the complement of the reservoir is infinite.  The sign columns are therefore linearly
independent modulo finite support.  Multiplication by the common nowhere-zero phase `eta(p)` does
not change this tail rank.

The Shapiro--Sparer/Pong prime-derivation criterion transfers this exact tail rank to differential
algebraic independence for every finite shifted-jet rectangle.  Pong's individual theorem makes
each resulting Helson zeta hypertranscendental.  The family has continuum cardinality, which is
maximal for holomorphic functions on a half-plane.

### 5. Reflection transversality

Let `eta` and `eta omega` in one `G_0`-orbit both belong to the fixed completed reflection class.
The logarithmic Euler discrepancy has coefficients

```text
c(p,k)=eta(p)^k(1-omega(p)^k).
```

Since

```text
abs(1-omega(p)^k) <= k abs(1-omega(p)),
```

for every `v>0`,

```text
sum_p sum_(k>=1) abs(c(p,k))p^(-kv)/k
 <= sum_p abs(1-omega(p)) p^(-v)/(1-p^(-v)) < infinity.      (2)
```

Thus the Euler-discrepancy abscissa is at most zero.  The common functional equation reflects the
zero-free quotient from `Re(s)>0` to `Re(s)<1`; the two regions overlap and cover the plane.  The
completed quotient is consequently entire and zero-free.  The standard Hadamard quotient theorem
for order-one meromorphic functions makes it `exp(As+B)`.  Normalized Euler products tend to one on
the positive real axis, so `A=0` and `exp(B)=1`.  Hence the two Dirichlet series are equal, uniqueness
of coefficients gives `eta omega=eta`, and freeness gives `omega=1`.

This proves the transversal law.

## Exact geometry

The phase landscape is not a product of three ordinary separated coordinates.  It has the form

```text
Omega
  = union of dense G_0 leaves,

continuable leaf
  = fixed complete divisor + maximal HT differential freedom,

fixed completed reflection class
  = a rigid partial transversal to those leaves.
```

The divisor is constant along each leaf, but neither the leaf nor its divisor label has a separated
finite-prime quotient.  Reflection does not vary along the leaf: it cuts the leaf at at most one
point.  This is the positive geometric replacement for the statement that finite-prime or
field-only routes cannot select zeta.

## Positive RH necessity

For the zeta phase, the entire positive-half-plane divisor, including the pole at `s=1`, is shared
by a dense `G_0`-leaf containing maximal differential-rank HT frames in every finite chamber.
Therefore an RH-capable carrier must be a **transversally polarized leaf**, retaining all three of:

1. the singular global divisor charge;
2. the positive Euler pointing inside the dense gauge leaf; and
3. the scale-one archimedean reflection datum that cuts the leaf rigidly.

Any carrier omitting item 2 or 3 remains on an indiscrete same-divisor leaf and cannot identify the
zeta source.  Any carrier omitting item 1 may select zeta as a source but still cannot state RH.
The route architecture forced by the theorem is therefore

```text
dense HT gauge leaf --rigid reflection/positivity transversal--> zeta source
                    --singular continued-divisor reader-------> RH question.
```

## Attacks

1. **Dense-subgroup attack.**  Dense cosets and indiscrete quotients are standard topology.  They
   are not the novelty claim.  The candidate is their exact arithmetic realization together with
   isodivisorial maximal differential rank and a rigid completed-reflection transversal.
2. **Grosswald--Schnitzer attack.**  Same-zero modified zeta functions are classical.  They do not
   identify the canonical exponent-zero gauge group, dense principal foliation, maximal HT source
   matroid on every leaf, or reflection transversality.
3. **Andersson attack.**  Arbitrary divisors and maximal continuation domains are classical.  The
   present theorem fixes one exact divisor and describes the internal topology and differential
   rank of its canonical gauge leaves.
4. **Strong multiplicity-one attack.**  The last uniqueness step is an analytic rigidity theorem,
   not new by itself.  Its role is to prove that reflection is transverse to, rather than constant
   on, the newly identified dense isodivisorial foliation.
5. **Wrapper attack.**  Merely juxtaposing three theorems would not pass.  The new object must be
   judged as the foliation/transversal geometry and its forced three-part RH carrier, not the list
   of ingredients.
6. **RH upcast attack.**  The theorem selects the zeta source inside one orbit but does not locate
   its zeros.  It is a route constraint and architectural positive statement, not an RH proof.
7. **Order attack.**  The reflection transversal is claimed only in the standard finite-order
   completed class.  No uniqueness is claimed for arbitrary infinite-order continuations.

## Lean formalization

The complete project-specific theorem surface is formalized as follows:

- `HTGeometry.ExponentZeroEulerGaugeFoliation` proves the subgroup law, free multiplication
  action, dense gauge classes, and indiscrete coinduced orbit topology;
- `HTGeometry.ExponentZeroEulerGaugeCardinality` proves that the phase torus and orbit quotient
  both have continuum cardinality and that every gauge class is codense;
- `HTGeometry.ExponentZeroEulerGaugeUnit` and
  `HTGeometry.ExponentZeroIsodivisorialContinuation` prove local uniform convergence of the Euler
  ratio, holomorphic nonvanishing, meromorphic continuation of the changed source, and equality of
  every positive-half-plane meromorphic order;
- `HTGeometry.MaximalIsodivisorialHTFreeFrame` proves continuum-sized maximal differential frames
  in every finite prime chamber of a fixed leaf, including arbitrary common unimodular base phases;
- `HTGeometry.ExponentZeroEulerGaugeReflectionTransversal` packages the full dense/codense
  foliation geometry, defines the exact analytic multiplicity-one interface
  `ExponentZeroGaugeSeparatedReflectionClass`, and proves both the at-most-one intersection theorem
  and the pointed singleton intersection theorem for every completed reflection class satisfying
  that interface.

The standard finite-order Hadamard quotient plus normalized Dirichlet uniqueness supplies the
named analytic separation interface for the order-one completed Euler class, exactly as in the
paper proof.  No axiom or placeholder is introduced; the external classical theorem is an
explicit hypothesis at the formal boundary, while every foliation, leaf, divisor, rank,
cardinality, and transversal deduction is theorem-checked in Lean.

## Gates

- [x] three distinct moves attacked: completed-FE slice, critical-corona incidence, and
  divisor/domain geometry
- [x] completed-FE slice retired as a standalone novelty claim
- [x] linear critical-corona incidence retired by the existing trilemma
- [x] exact dense gauge foliation and reflection-transversal theorem stated
- [x] complete paper proof
- [x] actual `G_0` group law, dense classes, and indiscrete orbit quotient formalized
- [x] exact continuum orbit cardinality, codensity, maximal differential frame, and local
  divisor-unit theorem formalized
- [x] reflection separation interface and exact partial/pointed transversal theorems formalized
- [x] positive RH carrier law stated without an RH upcast
- [x] primary searches found same-zero deformations and arbitrary divisors, but not the combined
  foliation/transversal law
- [ ] independent specialist novelty review

## Status

`[FORMALIZED IN LEAN 4] [NOVELTY HOLD]` The dense principal foliation, exact isodivisorial
maximal-rank leaves, and rigid partial-transversal consequence are complete in Lean, with the
finite-order completed-Euler multiplicity-one theorem retained as the explicitly named classical
analytic input.  The scientific novelty verdict remains reserved for independent specialist
review.

## Primary literature

- E. Grosswald and F. J. Schnitzer, *A class of modified zeta and L-functions*, Pacific J. Math.
  74 (1978), 357--364.
- W. Y. Pong, *Applications of differential algebra to algebraic independence of arithmetic
  functions*, Acta Arith. 172 (2016), 149--173.
- K. Seip, *Universality and distribution of zeros and poles of some zeta functions*, J. Anal.
  Math. 141 (2020), 331--381.
- I. Bochkov and R. Romanov, *On zeroes and poles of Helson zeta functions*, J. Funct. Anal. 282
  (2022), 109398.
- J. Andersson, *Mittag--Leffler type theorems for Helson zeta-functions*, arXiv:2408.15713,
  especially Theorem 5.
