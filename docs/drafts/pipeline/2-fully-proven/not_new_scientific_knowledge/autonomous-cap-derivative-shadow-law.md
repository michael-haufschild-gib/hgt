# Derivative-shadow law for autonomous first-order entire caps

- **ID:** `autonomous-cap-derivative-shadow-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Scientific status:** `[BRIDGE] [PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lane:** general hypertranscendence; differential-order geometry under composition
- **Statement:** An autonomous first-order entire outer function transfers the positive-derivative jet rank of its inner function exactly, adds one outer state, and forgets the inner primitive state.

## Goal

Find the higher-order replacement for the scalar Wiman observability charge without assuming that differential orders always add under composition.

The answer in this class is not another scalar growth exponent. It is a flag of algebraic ranks of successive derivative shadows. The first entry already detects a genuine compression phenomenon invisible to minimal ADE order alone.

RH is not used to select or prove the result.

## Definitions

For a meromorphic function `u` and `n>=0`, define its finite jet rank

`H_u(n)=trdeg_(C(z)) C(z)(u,u',...,u^(n)).`

For `n>=1`, define its positive-derivative shadow rank

`S_u(n)=trdeg_(C(z)) C(z)(u',...,u^(n)).`

Their difference

`pi_u(n)=H_u(n)-S_u(n)`

lies in `{0,1}`. Call `pi_u(n)` the **primitive defect at level n**. It records whether the zeroth jet `u` contributes an algebraic state not visible in its first `n` positive derivatives.

If `u` is DA, put

`r_k(u)=trdeg_(C(z)) C(z)<u^(k)>=ord_DA(u^(k))`

and

`pi_k(u)=r_k(u)-r_(k+1)(u) in {0,1}`.

The nonincreasing staircase

`R(u)=(r_0(u),r_1(u),r_2(u),...)`

is the **derivative-shadow signature** of `u`. Minimal ADE order is only its first entry.

The general field-geometric background is separated as the proved bridge `3-formalized/not_new_scientific_knowledge/ht-infinite-additive-torsor-staircase.md`: HT is equivalent to an inexhaustible all-ones tower of primitive derivative-shadow extensions.

## Finite-jet shadow theorem

`[BRIDGE] [PROVED HERE]` Let `f` and `g` be transcendental entire functions. Assume that `f'` is algebraic over `C(f)`; equivalently for the present class, `f` satisfies an autonomous first-order ADE. Put

`h=f o g`.

Then for every `n>=1`,

`H_h(n)=1+S_g(n).`

Equivalently,

`H_h(n)=H_g(n)+1-pi_g(n).`

Thus the outer autonomous first-order cap adds one state but is blind to the primitive defect of its input.

### Algebraic jet equivalence

Choose the analytic branch

`a=f'(g).`

An autonomous polynomial relation for `(f,f')` makes `a` algebraic over `C(h)`. Differentiating that relation shows inductively that every `f^(j)(g)` is algebraic over `C(h,a)`. The chain rule therefore gives

`C(z)(h,h',...,h^(n))^alg`

`=C(z)(h,g',...,g^(n))^alg`

inside a common algebraic closure.

The reverse containment is triangular. From

`h'=a g'`

one recovers `g'` algebraically after adjoining the algebraic element `a`. Differentiating this identity recovers `g''`, then `g^(3)`, and so on. Adjoining `a` and its derivatives changes no transcendence degree because they remain algebraic over the output-jet field.

### The outer state is independent

It remains to prove that `h` is transcendental over

`C(z)(g',...,g^(n)).`

If it were algebraic, the Nevanlinna root estimate would give

`T(r,h)=O(log r+sum_(j=1)^n T(r,g^(j))).`

Standard derivative estimates reduce the right side to `O(T(r,g)+log r)` outside the usual exceptional set. Clunie's composition-growth theorem for two transcendental entire functions gives

`T(r,f o g)/T(r,g) -> infinity`

along radii outside an exceptional set of finite measure. This is a contradiction. Hence `h` contributes exactly one further algebraic transcendence degree, proving the formula.

## DA order law and the primitive compression ledger

Assume now that `g` is DA. Let

`K_g=C(z)<g'>.`

Because `C(z)<g>=K_g(g)`,

`pi(g):=trdeg_(K_g) K_g(g)=ord_DA(g)-ord_DA(g') in {0,1}.`

Taking the union of the finite-jet equivalences and using the same growth argument gives the exact order law

`ord_DA(f o g)=1+ord_DA(g')`

`=ord_DA(g)+1-pi(g).`

Therefore composition by an autonomous first-order transcendental entire function has exactly two regimes:

1. `pi(g)=0`: the nominal order is additive;
2. `pi(g)=1`: precisely one differential state is compressed.

There is no larger compression in one cap.

For a sequence of autonomous first-order entire caps

`h_0=g`, `h_k=f_k o h_(k-1)`,

the recursion is

`ord_DA(h_k)=ord_DA(h_(k-1))+1-pi(h_(k-1)).`

Hence

`ord_DA(h_N)=ord_DA(g)+N-sum_(k=0)^(N-1) pi(h_k).`

This is the **primitive compression ledger**. The cost of a composition chain is not the sum of the scalar minimal orders of its factors; it is the nominal sum minus the primitive defects encountered by the successive inputs.

## Exact entire counterexample to universal additivity

Let

`E(z)=exp(-z^2)`,

`G(z)=integral_0^z E(t) dt`,

and `H(z)=exp(G(z))`.

Then

`ord_DA(exp)=1`, `ord_DA(G)=2`, but `ord_DA(H)=2`.

Indeed, `E'=-2zE`, so `C(z)<E>=C(z,E)` has transcendence degree one. The standard Liouville criterion for a hyperexponential integral says that `G` is not algebraic over `C(z,E)`: otherwise the Gaussian exponential would have an elementary primitive, which would require a rational solution of

`r'-2zr=1.`

No such rational function exists. A finite pole would create an unmatched pole of higher order in `r'`; hence `r` would be a polynomial, and comparison at infinity then makes the term `-2zr` impossible. Thus `G` contributes one primitive state and

`ord_DA(G)=2`, `pi(G)=1`.

On the other hand,

`H'/H=E`,

so `H` satisfies

`H H''-(H')^2+2z H H'=0.`

The shadow theorem gives the matching lower bound and therefore `ord_DA(H)=2`. The expected sum `1+2=3` fails by exactly the primitive defect.

This example kills the conjecture that minimal ADE order is universally additive for compositions of transcendental entire DA functions.

## Same scalar order, opposite cap behavior

The derivative-shadow signature distinguishes functions that minimal ADE order cannot.

Let

`A(z)=exp(z)+sin(z).`

Put `a=exp(z)`. From

`A'=a+cos(z)`,

`A''=a-sin(z)`,

`A'''=a-cos(z)`

one obtains

`a=(A'+A''')/2`,

`sin(z)=a-A''`,

`cos(z)=A'-a`.

The exponentials `exp(z)` and `exp(iz)` are algebraically independent over `C(z)`, while the displayed identities show that the differential fields generated by `A` and by `A'` both recover them. Hence

`ord_DA(A)=ord_DA(A')=2`, `pi(A)=0`.

The cap law gives

`ord_DA(exp o A)=3`.

By contrast, the Gaussian primitive `G` above has

`ord_DA(G)=2`, `ord_DA(G')=1`, `pi(G)=1`,

and therefore

`ord_DA(exp o G)=2`.

Thus two entire DA inputs of the same minimal order have opposite composition costs under the same outer function. The primitive defect is not a renamed scalar order; it contains information the scalar provably loses.

## Breaking autonomy restores the primitive state

The Gaussian primitive also isolates the role of the outer symmetry. Keep `G` and `E=G'` as above, but replace the autonomous outer exponential by the nonautonomous first-order entire function

`B(w)=w exp(w).`

It satisfies

`w B'(w)-(w+1)B(w)=0`

and has minimal ADE order one. Put

`Y=exp(G)`, `Q=B o G=G Y`.

The three states `E,G,Y` are algebraically independent over `C(z)`: `E,G` are independent by the Gaussian-primitive argument, and Clunie growth makes `Y` transcendental over every field generated by finitely many derivatives of `G`, in particular over `C(z,E,G)`.

They are all algebraic over the output differential field. Set

`q=Q'/Q=E(G+1)/G`

and

`r=-(q'/q+2z)=E/(G(G+1)).`

Then

`q/r=(G+1)^2`,

so `G` is algebraic over `C(z)<Q>`. It follows successively that

`E=qG/(G+1)`

and

`Y=Q/G`

are algebraic over the same field. Therefore

`ord_DA(B o G)=3.`

For the identical inner input `G`, the autonomous outer `exp` gives order two while the nonautonomous outer `w exp(w)` gives order three. The compression is therefore caused by the outer constraint's loss of the input primitive, not by first-order composition alone.

## Relation to the first-order Wiman charge

The universal first-order cascade theorem says that two transcendental entire first-order DA factors have composition order two. Applying the shadow law with an autonomous outer factor forces

`ord_DA(g')=ord_DA(g)=1`

for every transcendental entire first-order DA inner factor covered there. Thus its primitive defect is zero.

The quantized Wiman charge and the derivative-shadow signature measure different obstructions:

- the Wiman charge proves that a first-order state cannot disappear;
- the derivative-shadow signature detects higher-order primitive states that a cap never sees.

This is why a scalar higher-order Wiman charge cannot govern composition cost.

## HT consequence

If `g` is HT, then for every `n`, the functions

`g',...,g^(n)`

are algebraically independent, so `S_g(n)=n`. The finite-jet theorem gives

`H_(f o g)(n)=n+1`.

Hence `f o g` is HT, but the stronger statement is the exact transfer of every finite derivative-shadow rank. At the HT stratum, the primitive defect persists at every finite level:

`pi_g(n)=1` for all `n`.

The DA/HT boundary is therefore visible as follows:

- a DA derivative-shadow signature eventually stabilizes at a finite staircase;
- an HT function has the unsaturated shadow staircase `S_g(n)=n` at every level, while its full jet rank is the saturated value `n+1`.

## Attack

1. `[FALSIFIED]` Universal order additivity fails for `exp o G`, with `G` the Gaussian primitive.
2. `[PROVED]` One autonomous first-order cap can compress at most one state because `C(z)<g>=C(z)<g'>(g)`.
3. `[PROVED]` The exact lost state is the primitive defect, not a Wiman slope or Nevanlinna-order magnitude.
4. `[PROVED]` The law is finite-jet and therefore remains meaningful on the HT stratum, where scalar differential order is infinite.
5. `[PROVED]` The Gaussian primitive and `exp(z)+sin(z)` have the same minimal order but different primitive defects and different cap costs.
6. `[PROVED]` Breaking autonomy with the outer function `w exp(w)` restores the Gaussian primitive state and changes the order from two to three.
7. `[OPEN]` Determine which binary staircases occur as `pi_k(g)` for entire DA functions and whether a zero-free entire DA function can have persistent primitive defect one.
8. `[OPEN]` Extend the cap law from autonomous first-order outer functions to a conormal shadow module for nonautonomous and higher-order outer equations.

## RH pressure test, not research selector

For a zero-free local branch, writing a function as an exponential of a primitive shows that its differential information splits into one primitive state plus the derivative-shadow field. The completed zeta functions have logarithmic derivatives, so this law says what kind of differential datum an RH mechanism would have to constrain: not merely the function's scalar ADE order, but the full shadow flag together with one primitive state.

`[CONJECTURE]` A possible downstream RH route would seek a reflection-compatible positivity constraint that forces an off-critical-line zero configuration to create a finite-level rank defect in the logarithmic-derivative shadow flag. No such rank defect or RH implication is proved here, and divisor or zero-localization work is outside this lane.

## Parent-theory verdict

- **Current label:** `[BRIDGE] [PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE]`.
- **Known parent:** standard differential-field closure gives upper bounds and makes the algebraic jet equivalence plausible.
- **Known parent:** Ait El Manssour--Sattelberger--Teguia Tabuguia and Teguia Tabuguia give composition algorithms and sum-of-orders bounds for generic D-algebraic inputs.
- **Known parent:** Reinhart gives minimal-order results for Schanuel functions.
- **Verdict:** the exact finite-jet identity, primitive-defect dichotomy, compression ledger, and explicit failure of scalar order additivity are useful, but their proof is a direct combination of standard differential-field closure, the chain rule, and Clunie growth. The anti-theatre gate therefore forbids a scientific-novelty claim.
- **Targeted search:** searches for derivative-shadow order, minimal order of `exp(g)`, and exact composition order found generic elimination algorithms and upper bounds but no statement of this exact law.

## Gates

- [x] 0 -> 1: invariant well-posed; additive conjecture attacked and falsified.
- [x] 1 -> 2: finite-jet theorem, DA order law, compression ledger, and exact entire example proved on paper.
- [x] Parent theories and current D-algebraic composition algorithms checked.
- [x] Parent-theory audit; downgraded to bridge.
- [x] Audit the hyperexponential-integral citation at primary-source level.
- [ ] Lean only after novelty and numerical-precertification instructions can be reconciled.

## Primary references checked

1. J. Clunie, *The composition of entire and meromorphic functions* (1970), 75--92.
2. R. Ait El Manssour, A.-L. Sattelberger, and B. Teguia Tabuguia, *D-Algebraic Functions*, J. Symbolic Comput.; arXiv:2301.02512.
3. B. Teguia Tabuguia, *Arithmetic of D-algebraic functions*, J. Symbolic Comput. 126 (2025), 102348.
4. G. M. Reinhart, *Schanuel Functions and Algebraic Differential Equations*, PhD dissertation, University of Illinois (1993).
5. M. Rosenlicht, *Integration in Finite Terms*, Amer. Math. Monthly 79 (1972), 963--972.
