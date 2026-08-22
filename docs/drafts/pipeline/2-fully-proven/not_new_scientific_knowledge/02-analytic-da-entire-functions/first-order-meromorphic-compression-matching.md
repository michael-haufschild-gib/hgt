# First-order meromorphic composition compression is separable matching

- **ID:** `first-order-meromorphic-compression-matching`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Scientific status:** `[BRIDGE] [PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lane:** general hypertranscendence; exact boundary between entire unit cost and meromorphic compression
- **Statement:** If transcendental first-order DA functions `f` and `g` compose globally and `f o g` is again first-order DA, then, after finite algebraic covers, the outer derivative and inner velocity admit complementary rank-one factors. Every first-order collapse is therefore a separable chain-rule matching.

## Goal

Classify the sharp failure boundary of the entire unit-cost theorem.  Entire first-order factors always contribute one minimal differential order.  Meromorphic order-zero factors can compress: Liao--Yang records an explicit two-layer example whose chain-rule denominators cancel.  The target is to prove that this cancellation mechanism is universal.

RH is not used.  Only after the general classification is proved should one ask whether a finite-order HT function such as completed zeta can arise from an infinite sequence of these zero-charge matchings.

## Analytic theorem `[BRIDGE] [PROVED HERE]`

Let `f` be a transcendental meromorphic function on `C` and `g` a transcendental entire function.  Assume

- `f` is first-order DA over `C(u)`;
- `g` is first-order DA over `C(z)`;
- `h=f o g` is first-order DA over `C(z)`.

Then there are nonzero algebraic functions

`a in C(u)^alg`, `b in C(z)^alg`, `c in C(y)^alg`

such that, on compatible finite algebraic covers,

`f'(u)=a(u)c(f(u))`,

`g'(z)=b(z)/a(g(z))`,

and consequently

`h'(z)=b(z)c(h(z))`.

Conversely, any such matching makes `h` first-order DA.

The theorem classifies compression, not the individual solutions of the three separated first-order equations.

## Step 1 — state independence `[PROVED]`

The functions `z`, `g(z)`, and `h(z)=f(g(z))` are algebraically independent over `C`.

Certainly `z,g` are independent because `g` is transcendental.  If a polynomial relation among `z,g,f(g)` existed, expand it into finitely many monomials in `z` with coefficients of the form `w^j f(w)^k` evaluated at `w=g(z)`.  The polynomial-in-`z` coefficients have characteristic `O(log r)`, hence `O(T(r,g))`.  Steinmetz reduction produces polynomials `Q_(j,k)(w)`, not all zero, such that

`sum_(j,k) Q_(j,k)(w) w^j f(w)^k=0`.

After collecting equal powers this is a nonzero polynomial relation between `w` and `f(w)`, making the transcendental meromorphic function `f` algebraic over `C(w)`, a contradiction.  This is exactly the reduction lemma used by Liao--Yang in their pseudo-primality proof; no growth property of the outer `f` is required.

Thus `x=g`, `y=h`, and `z` may be treated as three independent variables in the generic state field.

## Step 2 — derivative branches

First-order differential algebraicity gives algebraic derivative branches

`A(x,y)=f'(x) in C(x,y)^alg`,

`B(z,x)=g'(z) in C(z,x)^alg`,

`C(z,y)=h'(z) in C(z,y)^alg`.

The chain rule is the exact three-face identity

`A(x,y) B(z,x)=C(z,y)`.

The hidden state `x` disappears from the product.

## Step 3 — three-field rank-one factorization `[PROVED HERE]`

Let `k` be algebraically closed of characteristic zero and let `x,y,z` be algebraically independent.  In a common algebraic closure of `k(x,y,z)`, suppose

`0 != A in k(x,y)^alg`,

`0 != B in k(x,z)^alg`,

`0 != C in k(y,z)^alg`,

and `AB=C`.  Prove that there exist

`a in k(x)^alg`, `b in k(z)^alg`, `c in k(y)^alg`

with

`A=ac`, `B=b/a`, `C=bc`.

### Proof

Let `E_xy`, `E_xz`, and `E_yz` be the relative algebraic closures of the indicated rational function fields in a common algebraic closure.  Algebraic independence of `x,y,z` and the exchange property in algebraically closed fields give the regular-intersection identities

`E_xy intersect E_xz = k(x)^alg`,

`E_xy intersect E_yz = k(y)^alg`,

`E_xz intersect E_yz = k(z)^alg`.

Equivalently, these follow from linear disjointness of two independent one-variable extensions over their common one-variable field.

Extend the commuting partial derivations uniquely through the algebraic closures.  Elements algebraic over a field fixed by one partial derivation are also fixed by that derivation.  From `AB=C`,

`partial_x A/A = -partial_x B/B`.

The left side lies in `E_xy`, the right side in `E_xz`; hence their common value belongs to `k(x)^alg`.  Similarly,

`partial_y A/A = partial_y C/C in k(y)^alg`.

Choose a finite normal subextension containing `A` and the two logarithmic derivatives.  At a generic algebraic specialization `x=x_0`, the specialized nonzero branch

`c(y)=A(x_0,y)`

satisfies the same equation

`partial_y c/c=partial_y A/A`.

Thus `partial_y(A/c)=0`.  The `partial_y`-constant field of `E_xy` is `k(x)^alg`, so

`A=a(x)c(y)`

for some `a in k(x)^alg`.  Now

`a(x)B(z,x)=C(z,y)/c(y)`.

The left side lies in `E_xz` and the right side in `E_yz`.  Their common value therefore lies in `k(z)^alg`; call it `b(z)`.  Then

`B=b/a`, `C=bc`,

which proves the factorization. ∎

The generic-specialization step may be replaced by the same argument on normalized finite covers: restrict the algebraic function and its logarithmic differential to a generic fiber over the `x`-curve.  It introduces no analytic assumption.

## Step 4 — conclusion `[PROVED HERE]`

Apply the factorization lemma to the derivative branches from Step 2.  It gives

`A(x,y)=a(x)c(y)`, `B(z,x)=b(z)/a(x)`, `C(z,y)=b(z)c(y)`.

Substituting `x=g(z)` and `y=h(z)` is exactly the asserted matching normal form.  Conversely the three displayed equations multiply by the chain rule, so `h` satisfies the first-order algebraic equation obtained by eliminating the algebraic branch `b(z)c(h)`.

## Known compression example recovered exactly

Liao--Yang records a zero-order meromorphic function `H` satisfying

`(u^2-4) H'(u)^2 = 4(H-e_1)(H-e_2)(H-e_3)`

and an entire function `g` satisfying

`g'(z)^2=g(z)^2-4`.

Take

`a(u)=1/sqrt(u^2-4)`,

`b(z)=1`,

`c(y)=2 sqrt((y-e_1)(y-e_2)(y-e_3))`.

Then `H'=ac`, `g'=b/a(g)`, and

`(H o g)'^2=4((H o g)-e_1)((H o g)-e_2)((H o g)-e_3)`.

The two-layer state collapses to one because the inner velocity cancels the outer base denominator.  This is the model the theorem claims is universal.

## Relation to the entire unit-cost law

If both factors are transcendental entire, Liao--Yang pseudo-primality already forbids a first-order composite.  The all-depth Wiman/Bell theorem strengthens this to exact additive order.  The present theorem explains the complementary meromorphic side: compression, when it occurs, is not mysterious loss of state but descent of a chain-rule product through a rank-one matching.

The zero-Wiman-charge wall is where such base denominators can survive.  Entireness and Strelitz positivity exclude that wall.

## Attack-as-false

1. Search for algebraic three-field products `A(x,y)B(x,z)=C(y,z)` that do not split after finite covers.  A counterexample would kill the classification at its algebraic core.
2. Test non-regular intersections caused by shared algebraic constants or non-linearly-disjoint covers.  The theorem may require choosing the algebraic closures to be relatively algebraically closed over the one-variable intersections.
3. Test analytic state dependence: a special `f,g` pair might make `z,g,f(g)` algebraically dependent and evade Steinmetz reduction.
4. Compare with Isidori--Krener cascade matching and classical Fuchsian differential-field pullbacks.  If either parent already gives this exact factorization after algebraic covers, downgrade to `[BRIDGE]`.

## RH pressure test

The classification would identify the only compositional regime still compatible with finite-order HT after the positive-charge entire cascade is excluded: repeated meromorphic base-factor matching.  This is not yet an RH route.  A route would additionally need:

- a canonical matched cascade attached to zeta or xi;
- control of its infinite algebraic covers and singularities;
- an independent theorem turning that constraint geometry into critical-line zero selection.

Without those ingredients, the result is a landscape theorem and a route discriminator only.

## Parent-theory verdict

The classification is the scalar first-order algebraic realization of the standard partial-matching
criterion for loss of observability in a nonlinear cascade.  Isidori--Krener--Gori-Giorgi--Monaco
identify partial matching as the general mechanism; Wang--Sontag identify output differential order
with observable state dimension.  Once the present first-order hypotheses reduce the chain rule to

`A(x,y)B(x,z)=C(y,z)`,

the displayed separable normal form is a direct rank-one factorization over the three pairwise
algebraic function fields.  The algebraic-cover statement is useful and appears not to be stated in
this notation by the parent papers, but it is mechanically derivable from their mechanism plus
standard regular-intersection facts.  It therefore fails the anti-theatre novelty/significance gate
and is retained only as bridge infrastructure.

## Gates

- [x] 0 -> 1: exact theorem, explicit parent counterexample, algebraic core, and falsification tests.
- [x] Close the algebraic-closure intersection and rank-one factorization lemma.
- [x] Make the Steinmetz state-independence step citation-exact at theorem level; pin final bibliographic numbering during literature audit.
- [x] Compare with nonlinear cascade matching and Fuchsian pullback literature.
- [x] 1 -> 2: proof complete; dual gate gives `[BRIDGE]`, not new scientific knowledge.
- [ ] Lean only after the paper theorem survives; the current tree lacks the required algebraic-closure intersection framework.

## Log

- 2026-07-11 — Created from the sharp zero-charge wall exposed by the universal entire unit-cost theorem.  The candidate turns the Liao--Yang meromorphic counterexample from an exception into the proposed universal normal form for first-order compression.
- 2026-07-11 — Closed the algebraic core by regular intersections of the three algebraic function fields plus logarithmic partial derivatives.  Steinmetz reduction proves state independence.  The analytic classification theorem is now proved; novelty and parent comparison remain open.
- 2026-07-11 — Parent comparison identifies the theorem as the scalar algebraic form of standard nonlinear-cascade partial matching.  The three-field separation is a short regular-intersection consequence, so the claim is downgraded to `[BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`.
