# Isodivisorial Prime-Walsh Stone saturation of hypertranscendental Euler fibres

- **ID:** `isodivisorial-prime-walsh-stone-saturation-law`
- **Stage:** 2-fully-proven / needs independent novelty audit
- **Type:** THEOREM CANDIDATE / GENERAL HT FIBRE GEOMETRY / RH ROUTE CONSTRAINT
- **Scientific status:** `[PROVED ON PAPER] [SIGNIFICANCE PASSES] [NOVELTY HOLD]`
- **Parents:**
  `maximal-isodivisorial-ht-free-frame.md`,
  `prime-walsh-stone-tail-reconstruction-law.md`

## Constraint

Fix a countable carrier set `J` with anchor `j_0`.  Let

```text
H_(j_0) = {x in {+1,-1}^J : x_(j_0)=+1},
S_(j_0) = {all-positive pattern}
          union {single-negative pattern at j : j != j_0}.
```

Let `K` be any closed Boolean constraint with

```text
{all-positive pattern} subset K subset H_(j_0).             (1)
```

For the maximal ordinary linear-matroid conclusion, assume in addition that the coordinate sign
functions are linearly independent on `K`; the anchored skeleton condition
`S_(j_0) subset K` is a simple explicit sufficient condition.

Let `D` be any signed divisor locally finite on `Re(s)>0`, supported in the critical strip, for
which the classical Helson-zeta divisor theorem supplies a unimodular Euler-product realizer.  The
question is whether fixing the exact continued divisor restricts the nonlinear compact tail
constraint of a maximally hypertranscendental prime-source family.

## Theorem: rectangular Stone saturation and Stone universality

There exists a countable family of unimodular completely multiplicative phases

```text
{chi_j : j in J}
```

such that:

1. every Euler product

   ```text
   Z_(chi_j)(s)=product_p (1-chi_j(p)p^(-s))^(-1)
   ```

   extends meromorphically to `Re(s)>0` with exact divisor `D` there;
2. every `Z_(chi_j)` is hypertranscendental on its initial half-plane;
3. the anchor `chi_(j_0)` is the fixed base divisor realizer;
4. the tail-cluster set of the relative prime orientations

   ```text
   epsilon_j(p)=chi_j(p)/chi_(j_0)(p) in {+1,-1}
   ```

   is exactly `K`;
5. if the coordinate sign functions are linearly independent on `K`---in particular, if
   `S_(j_0) subset K`---then every finite family of the prime-layer sources and every finite
   shift--jet rectangle is differentially algebraically independent over the finite-prime field;
6. for every finite `I subset J` and finite nonempty shift set `A`, the full Prime-Walsh palette
   satisfies

   ```text
   dtrdeg_(E_fin)
     E_fin<P_B(s+a) : B subset I, a in A>
       = card(A) card(projection_I(K)),                    (2)
   ```

   where `P_B` has the pointwise product of the relative signs as its prime coefficients.

Thus the exact product geometry

```text
admissible positive-half-plane divisor D
  x anchored compact Boolean Stone constraint K            (3)
```

is realized inside the Helson Euler-product class.  The first coordinate fixes the complete
continued divisor; the second fixes the complete nonlinear prime-tail observation algebra and its
differential-transcendence rank growth.

More intrinsically, every pointed compact metrizable Stone space occurs as the nonlinear tail
spectrum inside every admissible divisor fibre.  Indeed, a countable clopen family separating
points from the distinguished point embeds such a space as a closed `K` satisfying `(1)`.  Hence a
fixed divisor fibre is universal for pointed metrizable Stone spectra, while the Prime-Walsh
observation algebra reconstructs each embedded spectrum canonically.

## Proof

### 1. Base divisor realizer

Use the classical Helson-zeta divisor theorem to choose a unimodular phase `eta` whose Euler
product has divisor `D` on `Re(s)>0`.  For the Riemann-zeta specialization, take `eta(p)=1`, so the
anchor is exactly `zeta` and `D` is its actual positive-half-plane divisor.

### 2. Exponent-zero sparse reservoir

Choose an infinite prime set `S_*` satisfying

```text
sum_(p in S_*) p^(-sigma) < infinity for every sigma>0.    (4)
```

It may avoid any prescribed finite Euler chamber.  Enumerate `S_*={q_0,q_1,...}`.  Since `J` is
countable, its Boolean cube is compact metrizable.  Choose a sequence

```text
theta_m in K
```

whose tail-cluster set is exactly `K`: repeat every member of a countable dense subset of `K`
infinitely often.

### 3. Encode the complete constraint sparsely

Define

```text
epsilon_j(q_m)=theta_m(j),
epsilon_j(p)=+1 for p not in S_*,
chi_j(p)=eta(p) epsilon_j(p).                              (5)
```

Condition `(1)` makes `epsilon_(j_0)` identically positive, so `chi_(j_0)=eta`.  The full prime
pattern sequence equals `theta_m` on `S_*` and the all-positive pattern off `S_*`.  Because the
all-positive pattern belongs to `K`, adding its infinite constant subsequence does not enlarge the
tail-cluster set.  Hence the exact cluster constraint is `K`.

### 4. Exact isodivisoriality

For every `j`, the ratio

```text
Z_(chi_j)(s)/Z_eta(s)
  = product_(p in S_*)
      (1-eta(p)p^(-s))/(1-eta(p)epsilon_j(p)p^(-s))        (6)
```

converges normally on compact subsets of `Re(s)>0` to a holomorphic nonvanishing function.  This
follows from `(4)` and the uniform first-order bound on the logarithm of each local ratio.  Thus all
members have precisely divisor `D`.

### 5. Ordinary differential freedom

The tail-cluster annihilator law identifies the ordinary tail matroid exactly with the linear
matroid of the coordinate sign functions on `K`.  Hence coordinate-function independence gives
coefficient independence modulo finite prime support; the anchored skeleton is one explicit
sufficient condition.  The established Shapiro--Sparer/Pong Jacobian transfer then gives
differential algebraic independence of every finite shift--jet rectangle.  Pong's
hypertranscendence theorem gives item 2, specifically Theorem 5.3 with the injective logarithmic
multiplier: each phase has full support and is outside the finitely prime-generated subalgebra.

### 6. Complete nonlinear Stone rank

On a finite coordinate set `I`, the pointwise products of the signs are the Walsh characters.
Walsh inversion spans every function on the recurring chamber `projection_I(K)`.  The exact
finite-observable kernel identifies equality on that chamber with equality modulo finite prime
support.  Hence their tail rank is `card(projection_I(K))`; the same Jacobian transfer gives `(2)`.
The cofinal locally constant quotient reconstructs `K` by Stone duality.

The source-side realization is exact at the inverse-limit level: the canonical infinite
repetition of a dense sequence has tail cluster precisely the finite-cylinder closure of that
sequence.  Adding the all-positive complement of the sparse reservoir does not enlarge the cluster
because the all-positive point already lies in `K`.

## Quantitative corollary

For `J=N` and prefix chambers `I_n`, set

```text
D_K(n,A)=dtrdeg_(E_fin)
  E_fin<P_B(s+a):B subset I_n,a in A>.
```

Then

```text
D_K(n,A)=card(A) card(projection_(I_n)(K)).                 (7)
```

Consequently the normalized logarithmic growth of `D_K(n,A)` is the upper/lower box dimension of
`K` in the prefix ultrametric; when `K` is shift invariant, its limit is the topological entropy.
All of these complexity profiles occur without changing `D`.

## Positive RH necessity

Take `D` to be the actual positive-half-plane divisor of the Riemann zeta function and choose the
base realizer `eta=1`.  Then the anchor is exactly `zeta`, while every compact constraint in `(1)`
and every associated Prime-Walsh rank-growth profile occurs among auxiliary Euler carriers with the
same exact divisor.

Therefore an RH-capable HT architecture must contain more than either marginal:

- the complete continued divisor;
- the full linear differential matroid;
- the full nonlinear primewise Hadamard/Stone tail algebra;
- the entropy or box-dimension profile of that algebra.

> **Divisor--Stone incidence law.**  A viable carrier must retain a source-defined coupling between
> the Stone tail spectrum and the scale-one functional equation or continued divisor.  Both
> marginals can be fixed or prescribed independently inside the Euler-product class; only their
> incidence can carry rigidity relevant to RH.

This is a positive architecture theorem, not an RH proof.  It identifies the next invariant that
must be constructed: a coupling class, pairing, or polarization which changes under sparse
exponent-zero Stone deformations even when the complete divisor does not.

## Attacks

1. **Parent-product attack.**  Sparse isodivisorial gauges and Stone reconstruction are separate
   parent results.  The candidate-new content is the exact simultaneous rectangle `(3)`, including
   every pointed metrizable Stone spectrum and exact nonlinear differential-rank profile in every
   divisor fibre.
2. **Grosswald--Schnitzer/Helson attack.**  Same-zero Euler deformations and arbitrary divisor
   realization are classical.  They do not classify or prescribe the full compact pattern
   constraint and its Walsh rank growth.
3. **Symbolic-dynamics attack.**  Cluster-set realization and entropy from word complexity are
   classical.  They do not embed every such system isodivisorially into hypertranscendental Euler
   products.
4. **Functional-equation attack.**  Auxiliary sparse gauges generally destroy the Riemann
   functional equation.  This is the theorem's positive conclusion: source--reflection incidence,
   not divisor or Stone marginal data, is load-bearing.
5. **Anchor attack.**  In the zeta specialization the distinguished member is not merely
   isomorphic or same-field: it is exactly the original all-positive Euler product.
6. **Routine-corollary attack.**  The proof is short once the parents exist.  Novelty passes only if
   the divisor-fibre Stone rectangle and its incidence consequence are absent from the literature
   and materially strengthen the prior maximal free-frame theorem.

## Gates

- [x] exact rectangular theorem stated
- [x] complete paper construction of sparse compact-constraint encoding
- [x] exact divisor preservation proved on paper
- [x] exact anchor and tail-cluster identification proved on paper
- [x] ordinary and Prime-Walsh rank formulas reduced to proved formal cores and classical analytic
  transfer
- [x] formalize the sparse-background exact recurring-pattern realization, anchored maximal rank,
  and exact positive anchor
- [x] formalize exact whole-tail-cluster realization by canonical infinite repetition
- [x] primary literature audit of the combined divisor-fibre Stone rectangle
- [x] compare against all project isodivisorial, completed-corona, and constraint-product laws
- [x] significance verdict: passes; the theorem classifies the full nonlinear internal geometry of
  every divisor fibre and forces a new incidence datum for RH carriers
- [x] project novelty search: no exact divisor-fibre Stone-universality or Prime-Walsh rank law found
- [ ] independent specialist novelty verdict

## Status

`[NOVELTY HOLD]` The mathematical proof and the source-side internal theorem surface are complete.
The result strictly strengthens the prior dense-leaf and maximal-free-frame laws: a fixed divisor
fibre contains every pointed metrizable Stone spectrum, and its finite Prime-Walsh differential
ranks recover that spectrum.  Primary searches across Helson zeta functions, arithmetic-function
differential algebra, Walsh analysis, Stone duality, and symbolic dynamics found the parent
ingredients but not this combined universality law.  Because the proof becomes short after those
ingredients are assembled, final placement as new scientific knowledge remains reserved for an
independent specialist novelty audit.
