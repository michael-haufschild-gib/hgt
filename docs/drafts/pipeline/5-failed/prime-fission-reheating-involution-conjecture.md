# Prime-fission reheating involution conjecture

- **ID:** `prime-fission-reheating-involution-conjecture`
- **Stage:** 5-failed
- **Type:** FAILED ROUTE; one-prime-to-two-prime bounded-edit matching
- **Scientific status:** `[RETIRED AS AN INDEPENDENT MECHANISM]`; the graph conjecture is not
  disproved, but every proposed source mechanism either fails or returns to its Hall target
- **Source:** scalar-field / pre-Big-Bang ideation after the process, game, and discrete-Morse
  mechanisms failed, 2026-07-11

## Statement

Let

```text
Q_x = {n <= x : n is squarefree}.
```

There should exist a source-canonical partial involution `I_x` on `Q_x` with all of the following
properties:

1. `I_x(I_x(n))=n` and `I_x(n)!=n` wherever it is defined;
2. `mu(I_x(n))=-mu(n)`;
3. the prime supports differ in exactly three places, normally through a reaction

   ```text
   c*p <-> c*q*r
   ```

   with `c,p,q,r` squarefree and pairwise coprime in the evident sense;
4. for every `epsilon>0`, the exceptional set where `I_x` is undefined has size
   `O_epsilon(x^(1/2+epsilon))`; and
5. the rule is constructed from the ordered primes, factorization, and the cutoff `x`, without
   querying `M(x)`, ranking the two parity classes, or solving a global optimization whose deficit
   is the desired Mertens bound.

The pregeometric configurations are squarefree prime occupations. Reheating is not a time flow but
a static decomposition into reversible one-prime/two-prime reaction channels. A one-prime state and
a two-prime state differ in fermion parity, while the common core `c` represents spectator prime
sectors.

## Conditional RH theorem `[PROVED; BRIDGE]`

Every two-cycle of `I_x` contributes zero to the Möbius sum. Therefore

```text
|M(x)|
  = |sum_(n in Q_x) mu(n)|
  <= #{n in Q_x : I_x(n) is undefined}
  = O_epsilon(x^(1/2+epsilon)).
```

The classical Mertens criterion then implies RH.

The mathematical load is entirely in constructing the involution and proving the exceptional-set
bound. The displayed implication is bookkeeping, not evidence for the conjecture.

## Why three support changes are the first possible interaction

A one-toggle matching uses edges `c <-> c*p` in the face-inclusion graph. It cannot have
square-root defect. Let `A_x` be the odd vertices consisting of primes `p` with `x/2<p<=x`. Every
such vertex has only one one-toggle neighbor in `Q_x`, namely the vacuum `1`: adding any prime
exceeds `x`, and deleting `p` leaves `1`. Hence Hall deficiency for `A_x` is at least

```text
pi(x)-pi(x/2)-1,
```

which is of order `x/log x`, much larger than `x^(1/2+epsilon)` for small fixed `epsilon`.

The three-change reaction replaces one occupied prime by two unoccupied primes. It lets a boundary
prime `p` pair with a semiprime `q*r<=x` rather than forcing every boundary prime through the same
vacuum. Thus three is the smallest support distance that escapes the elementary Hall bottleneck.

This also explains why the retired discrete-Morse route was too rigid: a Morse matching permits
only one-face incidence moves and additionally requires acyclicity. The present conjecture is a
nonlocal parity involution, not a chain contraction.

## Anti-vacuity rules

The route is invalid if any of the following occurs.

1. Pair the `k`-th even squarefree integer with the `k`-th odd squarefree integer. The number left
   over is `|M(x)|`, so this reads the target.
2. Compute a maximum matching and then assert its unmatched set is small without a source-side Hall
   theorem. Cardinality imbalance already lower-bounds every matching deficit.
3. Allow arbitrary parity-reversing pairs with no bounded support change. Complete bipartite
   matching contains no arithmetic mechanism.
4. Use randomness and prove only an expected cancellation. RH needs a deterministic uniform bound.
5. Hide a zero oracle, Mertens oracle, or cumulative parity rank in the choice of reaction.
6. Claim that the previously defined simplicial boundary supplies the involution. The natural
   prime-product complex has `Omega(x)` total Betti number by the explicit missing-simplex cycles in
   `../5-failed/prime-occupation-discrete-morse-reheating.md`.

## Prime-fission block

Fix distinct primes `p,q,r` and a squarefree core `c` coprime to `p*q*r`. The formal reaction

```text
c*p <-> c*q*r                                           (R)
```

is an exact parity-reversing involution on the two displayed configurations whenever both products
are at most `x`. A family of disjoint blocks `(R)` would prove the conjecture if it covered all but
the required exceptional set.

The multiplicative energies are `log p` and `log q+log r`. Exact energy conservation would require
`p=q*r`, impossible for primes by unique factorization. Every reaction therefore has a nonzero
energy mismatch

```text
Delta(p;q,r) = |log p-log(q*r)|.
```

This is not decorative. A reaction with `q*r>p` is available for cores

```text
c <= x/(q*r),
```

but the one-prime configuration remains below the cutoff throughout the unmatched shell

```text
x/(q*r) < c <= x/p.                                    (S)
```

For a fixed reaction whose ratio `q*r/p` is bounded away from `1`, shell `(S)` has linear width in
`x`. Consequently that block cannot simply declare its mismatch shell exceptional. A finite,
cutoff-independent library could survive only by reassigning each such shell to other blocks in a
globally compatible way; the width calculation alone does not rule that out. A live construction
must be cutoff-adaptive, use increasingly close multiplicative near-resonances, or prove a
cross-block shell absorption theorem without double-using states.

## First construction target

`[CONJECTURE]` There is a deterministic hierarchical partition of prime supports into a spectator
core and a terminal cluster of size one or two such that:

- terminal clusters are paired by `p <-> q*r`;
- the rule is involutive from either side and uses no cumulative parity count;
- reactions at scale `y` have multiplicative mismatch small enough that their cutoff shells have
  total squarefree mass `O_epsilon(x^(1/2+epsilon))` after summing all scales; and
- every state not in a mismatch shell receives exactly one terminal cluster.

The hierarchy may depend on `x`. Cutoff dependence is legitimate because `M(x)` itself is a cutoff
observable; target dependence on the sign or size of `M(x)` is not.

## Construction attempt A: largest-terminal-cluster lanes

`[REFUTED AS A COMPLETE GRAMMAR]` There is a canonical way to prevent endpoint collisions, but it
leaves far too much unmatched mass.

For an even-parity squarefree core `c`, put `L=P(c)`, with `P(1)=1`, and `y=x/c`. Define

```text
A_c = {c*p : p prime, L<p<=y},
B_c = {c*q*r : L<q<r primes, q*r<=y}.
```

Every odd squarefree `n<=x` belongs to exactly one `A_c`: remove its largest prime. Every non-vacuum
even squarefree `n<=x` belongs to exactly one `B_c`: remove its two largest primes. In both cases the
remaining core has even parity. Hence these lanes give the exact identity

```text
M(x) = 1 + sum_(c even squarefree) (#B_c-#A_c).          (L)
```

Pairing `A_c` with `B_c` independently is an explicit common-core fission grammar. It fails already
at `c=1`: `A_1` is the set of primes at most `x`, while `B_1` is the set of squarefree semiprimes at
most `x`. The latter outnumbers the former by much more than square-root scale. Thus canonical
largest-cluster lanes cannot be paired independently.

The failure identifies a necessary new operation: **core migration**. A surplus even state `q*r`
from the `c=1` lane may instead be paired through core `q` with an odd state `q*a*b`, using the
reaction `q*r <-> q*a*b`. A successful involution must therefore route surplus endpoints through
an explicit system of augmenting paths across different divisor cores. Independent
prime-to-semiprime near-resonance blocks are insufficient.

## Replacement graph and the exact Hall target

Let `O_x` and `E_x` be the odd- and even-parity parts of `Q_x`. Define a bipartite graph `G_x` by
joining `c*p in O_x` to `c*q*r in E_x` whenever `p,q,r` are distinct primes absent from the
squarefree core `c`. Equivalently, the two prime supports have symmetric difference three and their
cardinalities differ by one.

For a family `S` on either side, let `N_x(S)` be its neighborhood in `G_x`, and define

```text
d_O(x) = max_(S subset O_x) (#S-#N_x(S)),
d_E(x) = max_(T subset E_x) (#T-#N_x(T)).
```

The deficiency form of Hall's theorem gives

```text
minimum number of vertices left unmatched by G_x
  = d_O(x)+d_E(x).                                      (H)
```

Thus the matching conjecture is equivalent to the concrete isoperimetric estimate

```text
d_O(x)+d_E(x) = O_epsilon(x^(1/2+epsilon)).              (HI)
```

Equation `(HI)` is the exact nonconstructive target. An explicit involution requires more: a
source-described matching achieving the bound. Proving `(HI)` by first estimating `#E_x-#O_x`
would be circular, but proving it from a replacement-shadow theorem for every subfamily would be a
genuinely different mechanism.

### Compression proposal `[SHARPENED; ORDINARY VERSION REFUTED]`

The product-quota family is shifted: replacing an occupied prime by a smaller absent prime can only
decrease the product. The initial proposal was that Hall-deficient families for the one-to-two
replacement shadow could be compressed, without decreasing deficiency, to controlled families
determined by finitely many multiplicative threshold profiles.

This is not the ordinary Kruskal--Katona theorem. Its shadow deletes one label and inserts two, it
mixes adjacent cardinalities, and the ambient complex has nonuniform weights `log p`. General
compression operations need not commute with generalized shadows, so monotonicity of deficiency
must be proved for this exact graph rather than imported by analogy.

The direct implementation by ordinary prime shifts is refuted below. A more global operation may
still exist, but calling an undefined global rearrangement "compression" supplies no content. The
replacement operation and its neighborhood monotonicity must be stated explicitly before this
proposal can become live again.

### Ordinary prime compression fails `[PROVED; COUNTEREXAMPLE]`

The natural interpretation of the compression conjecture is false. Let `P` be a sufficiently large
prime, set `x=6*P`, and consider the singleton families generated by the odd supports

```text
A  = {2,3,P},
A' = {2,3,5}.
```

Thus `A'` is obtained from `A` by replacing the large occupied prime `P` by the smaller absent prime
`5`. The replacement shadow of `A'` is strictly larger.

Indeed, for every prime `ell<=6*P/5` outside `{2,3,5,P}`, the even support `{5,ell}` is adjacent to
`A'`: retain the common core `{5}` and replace `{2,3}` by `ell`. It is not adjacent to `A`, since
its intersection with `A` is empty. These give

```text
pi(6*P/5)-4
```

new neighbors. The neighbors of `A` which cease to be neighbors after compression are exactly:

- the two rank-two supports `{2,5}` and `{3,5}`; and
- the rank-four supports `{2,3,5,ell}` with prime `ell<=P/5` outside `{2,3,5}`.

There are `pi(P/5)-1` lost neighbors in total. Consequently

```text
#N_x({A'})-#N_x({A})
  >= pi(6*P/5)-pi(P/5)-3 > 0                           (C)
```

for all sufficiently large `P`, by the prime number theorem. Hence ordinary compression can
decrease Hall deficiency. Kruskal--Katona-style monotonicity toward initial prime segments is not
available for `G_x`.

The direction suggested by `(C)` is the reverse: pushing occupied support toward the product quota
removes reaction slack and may shrink neighborhoods. Any surviving isoperimetric theorem must be a
**boundary polarization** theorem, not a standard compression theorem. It must also control the
cardinality change caused by pushing a whole family outward; arbitrary upward shifts need not stay
inside `Q_x` or preserve distinctness.

## Attacks

### Cardinality tautology

`[OPEN ATTACK]` Even with support distance three, existence of an almost-perfect matching may be no
more accessible than the parity imbalance it bounds. The route survives only if the hierarchical
reaction grammar yields expansion or an explicit involution from prime-distribution input strictly
weaker than RH.

### Boundary polarization

`[ORDINARY VERSION REFUTED]` The compression counterexample suggests pushing supports outward, but
elementary upward shifts are not neighborhood-monotone either. For a singleton prime support,

```text
N_x({p}) = {{q,r} : q<r primes, q*r<=x, q,r!=p}.
```

Consequently, for all sufficiently large `x`,

```text
#N_x({3})-#N_x({2}) = pi(x/2)-pi(x/3) > 0.              (U)
```

The upward shift `2 -> 3` enlarges the replacement shadow: freeing the cheaper label `2` creates
more semiprime reactions than are lost by occupying `3`. Thus neither inward compression `(C)` nor
outward polarization `(U)` has a uniform deficiency monotonicity law.

Any surviving rearrangement must balance two opposed effects simultaneously:

1. moving occupied primes downward creates quota slack and can add neighbors;
2. moving them downward also excludes cheap labels from the inserted pair and can remove neighbors.

A nonlocal, quota-preserving exchange might still balance these effects, but no such operation has
been defined. Ordinary shifted-family extremal theory no longer supplies a route to `(HI)`.

### Missing-pair saturation lemma `[PROVED; LOCAL BRIDGE]`

Let `n<=x` be squarefree and let `P=P(n)` be its largest prime factor. If two distinct primes
`q,r<=sqrt(P)` are absent from the support of `n`, then

```text
n = (n/P)*P  <->  (n/P)*q*r                            (MP)
```

is an edge of `G_x`: the new primes are absent, `q*r<=P`, and therefore the right endpoint is at
most `n<=x`.

Consequently, if no fission edge of form `(MP)` exists, the support of `n` contains every prime at
most `sqrt(P)` with at most one exception. Writing `theta` for Chebyshev's function gives

```text
log n >= theta(sqrt(P))-(1/2)*log P.
```

Since `theta(y)~y`, every such blocked state satisfies

```text
P <= (1+o(1))*(log x)^2.                                (PS)
```

Thus all states whose largest prime lies beyond the polylogarithmic range possess a
product-nonincreasing three-prime reaction. The lemma does not give a matching. If several states
have the same core `c=n/P`, the two smallest missing primes of `c` may be identical for all of them,
so the canonical map can collapse many inputs onto the single endpoint `c*q*r`.

The surviving problem is therefore **missing-pair allocation**: assign distinct available prime
pairs to the eligible largest primes over each core, then migrate any surplus between cores, while
retaining the product bound and involutivity. Existence of individual reactions is no longer the
main obstruction.

### Fixed-core reciprocal allocation `[PROVED; LOCAL BRIDGE]`

Fix a squarefree core `c`. Choose a finite set `R` of primes not dividing `c` such that

```text
H_R = sum_(q in R) 1/q > 1.
```

Such an `R` exists because deleting the finitely many prime divisors of `c` does not destroy the
divergence of the prime harmonic series. Restrict target pairs to

```text
q*r,  q in R,  r>max R prime,  r not dividing c.
```

These pair families are disjoint. The prime number theorem, applied to each fixed `q`, gives

```text
#{q*r<=z : q in R, r>max R, r prime, r not dividing c}
  = (H_R+o(1))*z/log z.                                 (RA)
```

The eligible terminal primes `p<=z` not dividing `c` number `(1+o(1))*z/log z`. Since `H_R>1`,
there is a threshold `Z_c` such that for every `z>=Z_c`, the number of available target pairs of
product at most `z` exceeds the number of eligible source primes in the corresponding tail.

Because the target neighborhoods are nested by the inequality `q*r<=p`, ordering both source
primes and target semiprimes increasingly now gives an injection

```text
p |-> {q(p),r(p)},  q(p)*r(p)<=p                       (RAI)
```

for all source primes beyond a finite core-dependent prefix. Multiplication by `c` turns `(RAI)`
into distinct valid reactions `c*p <-> c*q(p)*r(p)`.

This solves allocation over each fixed core only. It is not uniform as `c` varies with `x`:
`Z_c` can be enormous when `c` contains many small primes, and independently matching fixed-core
lanes leaves large semiprime surpluses that require core migration. The new quantitative target is
to trade late reciprocal availability against the primorial cost forced into `c`, then sum that
cost over every varying core without reintroducing the Mertens imbalance.

### Uniform reciprocal reservoir and its exponent barrier `[PROVED FOR THIS METHOD]`

Fix `delta>0`. For a sufficiently large constant `C=C(delta)`, set

```text
L = (C*log x)^(exp(1+delta)).
```

Then every squarefree `c<=x` satisfies

```text
sum_(q<=L prime, q not dividing c) 1/q > 1+delta.        (UR)
```

To prove this, suppose the missing reciprocal mass were at most `1+delta`. Among subsets of the
primes at most `L` having the required contained reciprocal mass, the least possible logarithmic
product is obtained by taking the smallest primes first, since the cost-to-mass ratio `p*log p` is
increasing. Mertens' prime-harmonic theorem then places the endpoint at

```text
y = L^(exp(-(1+delta))+o(1)),
```

and Chebyshev's theorem gives

```text
log c >= theta(y) = (1+o(1))*y.
```

The definition of `L`, with `C>1`, makes the right side larger than `log x`, contradicting `c<=x`.

Combining `(UR)` with the fixed-core count `(RA)`, uniformly for terminal primes

```text
p >= L^(2+eta)
```

for any fixed `eta>0`, gives enough distinct available semiprimes of product at most `p` to inject
all such terminal primes over every core. The square on `L` is necessary in the worst case: the
missing reciprocal mass in `(UR)` may be concentrated near `L`, so the pair reservoir cannot be
used uniformly until products of two `L`-scale primes fit below `p`. Taking `q<=L`, the second prime
`r>L`, and `p>=L^(2+eta)` makes the prime-number-theorem main term dominate both the finite
small-pair loss and the pairs using a prime divisor of `c`.

This method alone cannot reach RH scale. Letting `delta,eta` tend to zero leaves terminal primes
below approximately `(log x)^(2*e)`, where `e=exp(1)`. The standard smooth-number asymptotic

```text
Psi(x,(log x)^A) = x^(1-1/A+o(1))  for fixed A>1
```

therefore leaves a possible unresolved population of size

```text
x^(1-1/(2*e)+o(1)),
```

and `1-1/(2*e)>1/2`. This is a no-go for **reciprocal-reservoir allocation as the sole coverage
argument**, not a counterexample to `(HI)`: core migration or a separate cancellation of the smooth
population could still improve the exponent.

### Boundary-shell accumulation

`[PROVED LOCAL OBSTRUCTION]` Every fixed nonresonant block creates a positive-width multiplicative
shell. This does not prove a global no-go, because another block may consume the first block's
shell. The central quantitative question is whether a compatible collection of near-resonant
blocks can cover those shells recursively without regenerating comparable mass at the next scale.

### Sieve parity barrier

`[OPEN ATTACK]` A construction based only on upper-bound sieve counts or on the distribution of
`omega(n)` may hit the classical parity problem: those tools deliberately forget the sign
`(-1)^omega(n)` that the involution must reverse. The route needs an explicit bijection, not an
asymptotic assertion that adjacent occupation levels have similar size.

### Fake multiplicative sources

The reaction grammar depends only on ordered prime labels and the hard product cutoff. The same
grammar may apply to broad Beurling or phase-twisted multiplicative systems. This is acceptable only
if the proof uses an integer-specific ingredient such as exact unique factorization plus quantified
prime/semiprime near-resonance. A universal abstract matching theorem would risk proving false RH
analogues for sources with known off-line zeros.

## Preliminary literature boundary

Focused searches found:

- the classical Mertens parity criterion;
- supersymmetric/primon-gas interpretations of `mu`;
- Euler-characteristic formulations through divisibility complexes; and
- proposed recurrences and probabilistic parity arguments for the Mertens function.

They did not locate a bounded symmetric-difference involution, a `p <-> q*r` reaction tiling, or a
square-root exceptional-set theorem of this form. The closest parent theories are quota/threshold
complexes and Kruskal--Katona-type compression for ordinary or increasing-monoid shadows; neither
source inspected treats the multiplicatively weighted one-to-two replacement graph. This is only a
preliminary no-match result, not a scientific novelty verdict.

## Exact open cores

`[OPEN CORE 1: REACTION GRAMMAR]` Give a closed deterministic rule assigning at most one reaction
`c*p <-> c*q*r` to every state.

The rule must include core migration; the largest-terminal-cluster lane decomposition `(L)` is
proved insufficient.

It must also refine the local reaction supplied by `(MP)` into a collision-free allocation; choosing
the first two missing primes is many-to-one.

`[OPEN CORE 2: INVOLUTIVITY]` Prove the rule selects the same block when read from either endpoint.

`[OPEN CORE 3: COVERAGE]` Bound the union of resonance shells, collision states, and terminal tails
by `O_epsilon(x^(1/2+epsilon))`.

Equivalently, prove the Hall-isoperimetric bound `(HI)`. Ordinary inward compression and outward
polarization are both refuted by `(C)` and `(U)`. A live proof now requires a genuinely two-sided,
quota-aware replacement operation or a different mechanism entirely.

`[OPEN CORE 4: NONCIRCULARITY]` Derive coverage from explicit prime/semiprime distribution and
matching estimates that do not imply the Mertens bound by a hidden equivalent step.

## Current verdict

`[ROUTE RETIRED; THE ONE-TO-TWO RESTRICTION HAS NO SURVIVING SOURCE MECHANISM]`

The one-to-two replacement graph remains a well-defined stronger conjectural criterion, but its
mechanisms have been exhausted:

1. independent largest-terminal-core lanes leave a super-square-root semiprime surplus;
2. ordinary inward compression and outward polarization both fail neighborhood monotonicity by
   the explicit counterfamilies `(C)` and `(U)`;
3. individual high-prime reactions always exist by `(MP)`, but the canonical choice is many-to-one;
4. fixed-core reciprocal allocation is eventually injective, yet its uniform form leaves the
   `x^(1-1/(2e)+o(1))` smooth population, much larger than RH scale; and
5. allowing arbitrary augmenting paths across cores merely invokes a maximum matching in `G_x`.
   By bipartite matching-polytope integrality, replacing the matching by fractional reaction rates
   does not weaken the Hall-deficiency target `(HI)`.

Thus the only remaining sentence is "prove `(HI)` by a new global theorem." No invariant,
monotonicity, allocation law, or boundary classifier remains behind that sentence. The route is
retired rather than kept live as an RH-strength wish.

The failure also exposes the overrestriction. A parity-reversing support move of distance three has
two forms:

```text
one occupied <-> two occupied,    used here;
zero occupied <-> three occupied, omitted here.
```

On a full Boolean prime sector, toggling a fixed triple is a perfect involution. The next route must
use the full antipodal three-toggle graph and isolate only the multiplicative-quota boundary, rather
than force every cancellation through a one-to-two spectator core.

## Gates

- [x] 0 -> 1 in-progress: conditional RH implication, minimal support distance, one-toggle Hall
  obstruction, shell obstruction, anti-vacuity rules, and preliminary collision search recorded.
- [x] terminal attack: all proposed one-to-two mechanisms reduced to failed shifting, a
  super-square-root smooth remainder, or the Hall target itself.
- [ ] 1 -> 2 fully-proven: no reaction grammar or square-root coverage theorem exists; route retired.
- [ ] 2 -> 3 formalized: intentionally deferred until a noncircular paper theorem exists.
- [ ] 3 -> 4 publication-ready: ineligible before proof and dual novelty/significance audit.

## Parent references

- Spector, *Supersymmetry and the Möbius Inversion Function*, Communications in Mathematical
  Physics 127 (1990), 239--252.
- Pakianathan--Winfree, *Threshold complexes and connections to number theory*, Turkish Journal of
  Mathematics 37 (2013), 511--539.
- Le--Römer, *A Kruskal--Katona type result and applications*, arXiv:1903.02998.
- The classical equivalence `M(x)=O_epsilon(x^(1/2+epsilon)) for every epsilon>0` iff RH.
