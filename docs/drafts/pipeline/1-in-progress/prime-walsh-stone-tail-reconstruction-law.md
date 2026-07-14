# Prime-Walsh Stone reconstruction and entropy of the hypertranscendental tail constraint

- **ID:** `prime-walsh-stone-tail-reconstruction-law`
- **Stage:** 1-in-progress
- **Type:** THEOREM CANDIDATE / GENERAL HT CARRIER LAW / RH ROUTE CONSTRAINT
- **Scientific status:** `[CONJECTURE] [FINITE CORE FORMALIZED] [NOVELTY UNVERIFIED]`
- **Parent:**
  `../2-fully-proven/not_new_scientific_knowledge/prime-corona-constraint-opacity-law.md`

## Constraint

Let `J` be countable, enumerate the primes as `p_0,p_1,...`, and let

```text
theta_n = (epsilon_j(p_n))_(j in J) in {+1,-1}^J.
```

The compact tail constraint is

```text
K_epsilon = intersection_N closure {theta_n : n >= N}.
```

The linear differential matroid sees only cylinder-linear functions on `K_epsilon`.  The question
is which canonical source algebra sees the entire nonlinear constraint, without choosing a path,
a representative at infinity, or a selector.

## Theorem candidate: finite-observable constraint law

For a finite set `I subset J` and arbitrary functions

```text
f,g : {+1,-1}^I -> A,
```

one has

```text
f(theta_n|I) = g(theta_n|I) for all but finitely many n
  <->
f(x|I) = g(x|I) for every x in K_epsilon.                 (1)
```

No algebraic or topological structure on `A` is required.  Moreover,

```text
x in K_epsilon
  <->
for every finite I, theta_n|I = x|I for infinitely many n. (2)
```

Thus `K_epsilon` is the canonical inverse limit of its recurring finite pattern chambers.

## Theorem candidate: Prime-Walsh Stone reconstruction

Let `Cyl_J` be the complex algebra of finite-cylinder functions on the Boolean cube.  Evaluation
along the prime sequence gives

```text
Ev_epsilon : Cyl_J -> C^N / C^(N),
f |-> [n |-> f(theta_n)],
```

where `C^(N)` is the ideal of finitely supported sequences.  Let

```text
I(K_epsilon) = {f in Cyl_J : f|K_epsilon = 0}.
```

Then `(1)` gives the exact kernel, and restriction gives a canonical algebra isomorphism

```text
Cyl_J / I(K_epsilon)  ~=  LC(K_epsilon,C),                 (3)
```

where `LC` denotes the locally constant complex functions.  The idempotents of this quotient are
exactly characteristic functions of clopen subsets of `K_epsilon`.  Consequently its Boolean
idempotent spectrum is `Clop(K_epsilon)`, and Stone duality reconstructs `K_epsilon` canonically.

This is a complete positive carrier law:

> The full compact prime-tail constraint is fixed by its finite nonlinear observation algebra.

It is not propagated by a flow and does not require a canonical point of the constraint.

## Finite Prime-Walsh rank law

For finite `I`, let

```text
R_I = projection_I(K_epsilon) subset {+1,-1}^I
```

be the recurring pattern chamber.  For every subset `B subset I`, define the Walsh orientation

```text
w_B(p_n) = product_(j in B) epsilon_j(p_n)
```

and its prime-layer carrier

```text
P_B(s) = sum_p w_B(p) p^(-s).
```

The tail span of the `2^card(I)` Walsh coefficient vectors has dimension exactly

```text
card(R_I).                                                   (4)
```

Indeed, Walsh characters span every function on the finite cube, so their restrictions span every
function on `R_I`; equation `(1)` identifies the restriction kernel with finite prime support.
After the established Dirichlet-series Jacobian transfer, every finite nonempty shift set `A`
satisfies

```text
dtrdeg_(E_fin) E_fin<P_B(s+a) : B subset I, a in A>
  = card(A) * card(R_I).                                    (5)
```

The ordinary differential matroid of the original coordinate carriers records only the degree-one
shadow `dim Span(R_I)`.  The Prime-Walsh palette records the complete finite pattern chamber and,
cofinally over `I`, reconstructs the full inverse-limit constraint.

## HT--Stone entropy law

Take `J=N`, let `I_n={0,...,n-1}`, and put

```text
C_epsilon(n) = card(projection_(I_n)(K_epsilon)).
```

For a fixed finite nonempty shift set `A`, let `D_epsilon(n,A)` be the differential transcendence
degree of the full Prime-Walsh palette on `I_n` and `A`.  Equation `(5)` gives the exact identity

```text
D_epsilon(n,A) = card(A) C_epsilon(n).                    (6)
```

Equip the Boolean cube with its standard prefix ultrametric.  The length-`n` cylinders meeting
`K_epsilon` are exactly its `C_epsilon(n)` distinct prefix patterns.  Therefore

```text
upper_box_dim(K_epsilon)
  = limsup_(n->infinity) log_2 D_epsilon(n,A)/n,

lower_box_dim(K_epsilon)
  = liminf_(n->infinity) log_2 D_epsilon(n,A)/n.           (7)
```

The constant factor `card(A)` disappears after normalization.  If `K_epsilon` is shift invariant,
its prefix patterns are its length-`n` language and the limit exists by subadditivity.  Hence

```text
h_top(K_epsilon)
  = lim_(n->infinity) log D_epsilon(n,A)/n.                (8)
```

Thus fractal dimension and symbolic entropy of the nonlinear constraint are exact asymptotic
growth laws of differential transcendence after the canonical primewise Hadamard closure.  The
ordinary coordinate matroid can be maximally free for every `n` while the quantity in `(7)` varies;
the Prime-Walsh growth spectrum detects that variation exactly.

## Proof

### 1. Exact finite-observable kernel

If two finite observations disagree infinitely often, one disagreeing finite pattern occurs
infinitely often.  Compactness supplies a tail-cluster extension of that pattern, where the two
observations still disagree.  Conversely, the set of disagreeing patterns is finite.  If the
observations agree on the tail cluster, each disagreeing pattern has finite fibre, so their union
has finite fibre.  This proves `(1)`.

### 2. Canonical inverse limit

Every cluster point has every finite cylinder recurrent.  Conversely, if every finite cylinder at
`x` recurs, then every neighbourhood of `x` is visited infinitely often, because product
neighbourhoods contain a finite cylinder.  This is exactly the cluster-point criterion and proves
`(2)`.

### 3. Locally constant quotient

Equation `(1)` identifies the kernel of `Ev_epsilon` with `I(K_epsilon)`.  Every restriction of a
cylinder function is locally constant.  Conversely, a locally constant function on the compact
zero-dimensional space `K_epsilon` has a finite clopen fibre partition.  Each clopen fibre is cut
out on `K_epsilon` by finitely many Boolean coordinates, so the function extends to a cylinder
function.  This proves `(3)`.

### 4. Stone reconstruction

An idempotent complex-valued function takes only the values `0` and `1`; local constancy makes its
one-fibre clopen.  Every clopen subset gives such an idempotent.  Hence the quotient algebra
recovers `Clop(K_epsilon)`, and the classical Stone representation theorem recovers the compact
Boolean space itself.

### 5. Walsh rank

On a finite Boolean cube the Walsh characters form a basis.  Restriction onto `R_I` is surjective
onto all complex functions on `R_I`; its rank is therefore `card(R_I)`.  Equation `(1)` identifies
its kernel with tail-zero prime coefficients.  The established shifted prime-Dirichlet tail
theorem then gives `(5)`.

## Attacks

1. **Stone-duality attack.**  Stone reconstruction from a locally constant algebra is classical.
   The candidate contribution cannot be that parent theorem; it must be the exact identification
   of the prime-tail quotient and the resulting HT carrier law.
2. **Walsh-analysis attack.**  Walsh completeness on a finite cube is classical.  The possible new
   content is the cofinal rank law `(5)` and its source-specific inverse-limit interpretation.
3. **Repackaging attack.**  The linear corona-span law is already equivalent to the recurring
   pattern theorem.  The present theorem is stronger only because primewise products add every
   finite nonlinear observation and make the carrier faithful to the constraint.
4. **Hadamard-operation attack.**  Ordinary differential-field multiplication convolves Dirichlet
   coefficients and does not produce the pointwise products `w_B`.  The Prime-Walsh palette is a
   genuine carrier enrichment, not notation for operations already present in the differential
   field.
5. **RH upcast attack.**  Reconstructing a prime-tail constraint does not locate continued zeros.
   A viable RH route must still couple the reconstructed Stone constraint to the scale-one
   functional equation or continued divisor.
6. **Entropy-parent attack.**  Prefix complexity computes box dimension, and language complexity
   computes subshift entropy, by classical symbolic dynamics.  The candidate contribution is not
   either parent formula but their exact equality with source-specific differential-transcendence
   growth in `(6)--(8)`.
7. **Pong pointwise-product attack.**  Pong studies pointwise multiplication operators on
   arithmetic functions and proves strong algebraic-independence theorems when the multiplier has
   sufficiently rich prime values.  Boolean orientations have finite prime-value range, so those
   results do not give `(6)`; the recurring-pattern Jacobian and Walsh restriction rank are the
   load-bearing source-specific inputs.

## Positive RH necessity

The opacity interval proves that the complete finitary differential matroid can remain maximal
while the nonlinear compact prime-tail constraint varies arbitrarily.  Equations `(3)`--`(5)`
identify the missing positive datum exactly:

> **Prime-Walsh completeness law.**  An RH-capable hypertranscendental carrier must retain the
> primewise nonlinear observation algebra, or an equivalent Stone spectrum, and couple that
> spectrum to reflection or continuation.  Linear differential rank is only its degree-one
> shadow.

This does not assert that the Prime-Walsh algebra proves RH.  It proves that it is the minimal
canonical finitary enrichment that completely remembers the Boolean tail constraint which the
ordinary differential matroid forgets.

## Gates

- [x] exact finite-observable kernel proved on paper
- [x] canonical inverse-limit characterization proved on paper
- [x] finite-observable kernel formalized unconditionally
- [x] inverse-limit characterization formalized unconditionally
- [x] locally constant quotient reduced to the formal finite-observable kernel after the classical
  finite-coordinate/Stone boundary
- [x] finite Walsh inversion, tail-annihilator, and exact restriction-rank theorems formalized
- [x] derive box-dimension and subshift-entropy identities from the exact finite rank
- [ ] primary literature audit across Stone duality, Boolean harmonic analysis, Dirichlet-series
  Hadamard products, and arithmetic-function differential algebra
- [ ] compare against all project constraint inverse limits and nonlinear Euler-corona results
- [ ] dual-gate verdict

## Status

`[OPEN CORE]` Verify that the Prime-Walsh quotient and cofinal rank profile are absent from the
Dirichlet-series and HT literature, then close the algebraic reconstruction and analytic transfer.
