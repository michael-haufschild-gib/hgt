# Fixed-divisor maximal translation-HT genericity

- **ID:** `fixed-divisor-maximal-translation-ht-genericity`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) — `[PROVED HERE] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lane:** general hypertranscendence; fixed-divisor fibers; countable translation matroids
- **Statement:** For every nonzero entire function `W` and every countable set of shifts `H`, a
  comeager set of zero-free entire gauges `exp(g)` makes the complete differential-translation
  family `{W(z+h)exp(g(z+h)) : h in H}` differentially algebraically independent over `C(z)`.
  Consequently every prescribed entire divisor supports maximal countable translation-jet
  complexity.

## Medalist lens

The binary statement "HT does not determine the divisor" is too weak.  The relevant question is
whether the *complete differential-algebraic matroid of a countable translation orbit* constrains
the divisor.  Fix the divisor first, then ask how large the orbit matroid can be inside that one
fiber.

The answer is maximal: the divisor and the countable translation-jet matroid can be prescribed
independently.  This is not a rational-gauge statement.  The divisor may be arbitrary and infinite.

## Theorem `[PROVED HERE]`

Let `H subset C` be countable and let `W` be a nonzero entire function.  Give `O(C)` its compact-open
Frechet topology.  For `g in O(C)`, put

`F_g(z)=W(z) exp(g(z))`.

There is a comeager set `G(W,H) subset O(C)` such that, for every `g in G(W,H)`, every finite list
of distinct shifts `h_1,...,h_m in H`, and every nonzero differential polynomial

`P in C(z){Y_1,...,Y_m}`,

one has

`P(F_g(z+h_1),...,F_g(z+h_m)) != 0`

as a meromorphic function of `z`.  Equivalently, every finite subfamily of

`{T_h F_g : h in H}`

is differentially algebraically independent over `C(z)`.

Every `F_g` has exactly the zero divisor of `W`, with the same multiplicities.  Since every locally
finite effective divisor on `C` is the divisor of a nonzero entire function, every entire divisor
supports a residual exponential-gauge family with the maximal differential-translation matroid on
any prescribed countable shift set.

Taking `H=Q+iQ` gives a dense countable translation orbit with this property.  Taking `H={0}`
recovers ordinary hypertranscendence.

## Free differential-translation field corollary `[PROVED HERE]`

Assume now that `H` is a countable additive subgroup.  Let `W_0,W_1` be any two nonzero entire
functions and choose `g_i in G(W_i,H)`.  Put `F_i=W_i exp(g_i)`.

The assignment

`(T_h F_0)^(n) |-> (T_h F_1)^(n)`, for `h in H`, `n>=0`,

extends uniquely to an isomorphism of differential `H`-fields over `C(z)`:

`C(z)<T_h F_0 : h in H>_D  ~=  C(z)<T_h F_1 : h in H>_D`.

Indeed, both sides are fraction fields of the free differential polynomial algebra on the
`H`-indexed generators: maximal differential independence says that the displayed jets satisfy no
algebraic relation, differentiation raises `n`, and translation by `a in H` sends the generator
indexed by `h` to the generator indexed by `h+a`.  The universal property gives the isomorphism and
its inverse.

Thus arbitrary entire divisors occur on analytically realized objects whose complete generated
countable differential-translation fields are indistinguishable up to structure-preserving
isomorphism.  The loss is categorical, not merely equality of a list of transcendence degrees.

## Proof

### 1. Countable normal forms for all complex-coefficient relations

Fix distinct `h_1,...,h_m in H`.  After clearing denominators, a differential polynomial relation
over `C(z)` becomes a nonzero complex linear relation among finitely many distinct expanded
differential monomials

`M_(k,alpha)(z,j^r F_g)`

`  = z^k prod_(i=1)^m prod_(ell=0)^r (F_g^(ell)(z+h_i))^(alpha_(i,ell))`,

where `k,r` and all entries of `alpha` are nonnegative integers.  Although the coefficients are
arbitrary complex numbers, the finite *supports* of these monomials form a countable set.  Because
`H` is countable, all finite shift lists and all finite supports form one countable family.

For a finite support `S={M_1,...,M_N}`, let `L_S` be the set of `g in O(C)` for which the `N`
entire functions

`M_1(z,j^r F_g),...,M_N(z,j^r F_g)`

are linearly dependent over `C`.

The complement of the required set is exactly the union of the `L_S`.

### 2. Each dependence locus is closed

The functions in the support are linearly dependent precisely when every `N by N` evaluation
determinant

`det(M_j(z_a,j^r F_g))_(1<=a,j<=N)`

vanishes, as `(z_1,...,z_N)` ranges over `C^N`.  Compact-open convergence of `g` implies
compact-open convergence of `exp(g)`, of `F_g`, and of every derivative of `F_g`.  Each evaluation
determinant is therefore continuous in `g`.  Hence `L_S`, an intersection of their zero sets, is
closed.

### 3. Finite jets inside a fixed-divisor fiber are free away from the divisor

Fix a point `u` with `W(u)!=0`.  For any `r>=0`, the jet map

`j_u^r g |-> j_u^r (W exp(g))`

has image exactly

`C^x times C^r`.

Indeed, choose a logarithm of the desired nonzero value divided by `W(u)`.  After the value and
the derivatives of `g` below order `ell` have been chosen, the formula for

`(W exp(g))^(ell)(u)`

is affine in `g^(ell)(u)` with nonzero coefficient `W(u)exp(g(u))`.  The derivatives of `g` can
therefore be solved recursively.  Thus the fixed divisor imposes no finite jet restriction away
from its support except nonvanishing of the value.

### 4. A support determinant can be made nonzero arbitrarily near any gauge

Let `U` be a nonempty neighborhood of `g_0` in `O(C)`.  After shrinking, membership in `U` is
guaranteed by uniform approximation to `g_0` on a closed disk `D`.

Choose distinct evaluation points `z_1,...,z_N` so far outside `D` that:

1. all points `z_a+h_i` are pairwise distinct;
2. every `W(z_a+h_i)` is nonzero.

This is possible because only finitely many translation collisions and discrete zero sets must be
avoided.

As abstract polynomials in

`z` and the jet variables `Y_(i,ell)`,

the distinct expanded monomials in `S` are linearly independent.  Restricting every value variable
`Y_(i,0)` to `C^x` preserves that independence.  The standard evaluation lemma therefore allows
the `z_a` and target jet vectors, still subject to the two avoidance conditions, to be chosen so
that

`det(M_j(z_a,Y_a)) != 0`.

By Step 3, these target jets of `F_g` lift to arbitrary finite jets of `g` at the pairwise distinct
points `u_j=z_a+h_i`.  The required approximation-interpolation step is elementary.  Let `H_0` be
the Hermite polynomial with the prescribed jets at the `u_j`, choose exponents `m_j+1` larger than
the prescribed jet depths, and put

`A(z)=prod_j (z-u_j)^(m_j+1)`.

The function `(g_0-H_0)/A` is holomorphic on a neighborhood of `D`, because every `u_j` lies outside
`D`.  Approximate it uniformly on `D` by a polynomial `q` and set

`g=H_0+Aq`.

Then `g` has exactly the prescribed exterior jets, while

`g-g_0=A(q-(g_0-H_0)/A)`

is arbitrarily small on `D`.  Thus `g in U`.  For this `g`, the displayed evaluation determinant is
nonzero, so `g notin L_S`.

Thus every `L_S` has empty interior and, being closed, is nowhere dense.

### 5. Baire conclusion and divisor statement

The Frechet space `O(C)` is Baire.  The union of the countably many `L_S` is meagre, so its
complement `G(W,H)` is comeager.  Every `F_g=W exp(g)` has the same divisor as `W` because the
exponential gauge is entire and zero-free.  This proves the theorem.

## Sharp boundaries and attacks

1. **Countability is used.**  Baire intersects the complements of countably many finite-support
   conditions.  The theorem does not claim simultaneous independence for all uncountably many
   complex shifts.
2. **The complete divisor is fixed.**  This is stronger than finite quartet surgery and stronger
   than merely producing one HT function on a prescribed divisor.
3. **The matroid is maximal, not merely HT.**  Every finite tuple of chosen translates, with all
   derivative orders, is algebraically independent over `C(z)`.
4. **A full germ is excluded from the observation channel.**  Prescribing all derivatives at one
   ordinary point fixes an entire function by analytic continuation.
5. **No Euler normalization is retained.**  Multiplication by `exp(g)` generally destroys a
   Dirichlet series, Euler product, positivity structure, or canonical normalization.  Those are
   precisely the possible gauge-breaking data.

## Exact RH-route consequence

Let a proposed implementation of an RH route consume an entire function only through:

1. its complete zero divisor; and
2. the differential-algebraic dependence matroid of translates belonging to some fixed countable
   shift set.

Then those two data are independent coordinates: every divisor, including divisors with arbitrary
off-critical zeros, supports the same maximal orbit matroid.  Therefore maximal countable
translation hypertranscendence cannot supply an additional zero selector after the divisor has
been forgotten or coarsened.

More sharply, if the implementation factors through the isomorphism class of the generated
differential `H`-field, choose one divisor supported on a critical line and another containing an
off-line zero.  The two realized fields are isomorphic by the corollary, while their RH-type divisor
predicates differ.  No isomorphism-invariant sentence in that differential-translation language
can select the RH divisor.

This excludes HT-only finite/countable shift-state implementations within Li, Weil,
Nyman--Beurling, Hilbert--Polya, Connes, and de Branges programs.  It does not exclude the full
criteria, which retain exact divisor-sensitive positivity, spectral, norm-closure, or Euler data.

## Candidate competition

1. **Euler-normalized rational-gauge rigidity:** correct but a routine asymptotic identity theorem;
   `[BRIDGE]`.
2. **Bounded-complexity translation-defect accumulation:** already proved locally and reduced to
   Mahler normalization plus analytic determinantal loci; `[BRIDGE]`.
3. **Fixed-divisor maximal translation matroid:** correct and strictly strengthens both ordinary
   Baire-generic HT and fixed-divisor HT saturation, but the proof remains a direct combination of
   their parent mechanisms; `[BRIDGE]`.

## Scientific status and novelty gate

`[BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`.

- **Proof gate:** passes.  The exterior Runge--Hermite step is proved explicitly by the factor
  `A` construction above.
- **Significance gate:** passes as a structural boundary.  The complete prescribed divisor and the
  maximal countable transformal-differential matroid are independent coordinates.
- **Parent-theory gate:** fails.  After erasing the terminology, the proof is the finite-support
  Baire argument already used for generic HT, applied to the open finite-jet map of the fixed
  exponential-gauge fiber.  The extra translation indices are countable bookkeeping, and the
  divisor constraint is absorbed by a triangular jet coordinate change.
- **Literature gate:** exact searches in English, French, and German found no identical
  fixed-divisor/all-jet/countable-translate statement.  Nearby parents include van den Dries's
  generic DA-interpolation theory, Rubel's DA-entire-function program, Birkhoff/MacLane
  universality, and modern hypercyclic-algebra Baire arguments.  Absence of the exact wording does
  not overcome the routine-parent failure.
- **Rediscovery gate:** fails for the same reason: the mechanism is immediately generated from the
  established genericity and interpolation parents.

Primary adjacent sources checked:

1. L. van den Dries, *Parametrizing the solutions of an analytic differential equation*, Illinois
   J. Math. 39 (1995), 450--462, DOI `10.1215/ijm/1255986390`.
2. L. A. Rubel, *On the ring of differentially-algebraic entire functions*, J. Symbolic Logic 57
   (1992), 449--451, DOI `10.2307/2275279`.
3. J. Bes, J. A. Conejero, and D. Papathanasiou, *Hypercyclic algebras for convolution and
   composition operators*, arXiv `1706.08022`, for residual free-algebra mechanisms in `H(C)` and
   the sharp distinction for translation operators.

## Lean status

Complete unconditional formalization:

- `FixedDivisorTranslationFreeness.lean` proves one dense residual gauge phase simultaneously
  excludes every finite differential relation for every injective finite complex-shift packet and
  preserves the zero set.
- `FixedDivisorDifferentialFieldUniversality.lean` upgrades that functional statement to genuine
  differential independence over `ℂ(z)` in the upper-end meromorphic field, preserves every
  analytic zero multiplicity, and constructs the canonical labelled generated-field equivalence
  for any two prescribed entire divisors.  The equivalence carries every labelled jet to its
  counterpart and commutes with derivation.

The formal endpoint is stronger than the countable-`H` statement: one residual phase works for the
full complex translation palette, so restriction to every countable subset or subgroup is
immediate.

## Gates

- [x] 0 -> 1: exact theorem, complete proof architecture, failure modes, and route scope
- [x] 1 -> 2: complete paper proof, explicit interpolation lemma, and final bridge verdict
- [x] 2 -> 3: complete unconditional theorem formalized in Lean
- [ ] 3 -> 4: standalone paper and independent novelty review

## Log

- 2026-07-11 -- Opened after DA-gauge divisor blindness showed that finite rational surgery is too
  weak.  Replaced it by a fixed arbitrary divisor and proved residual maximal differential
  independence along every prescribed countable shift set.
- 2026-07-11 -- Closed the interpolation hinge explicitly and downgraded the result to a bridge:
  the exact packaging was not located, but the proof is a routine fixed-divisor extension of known
  Baire-genericity machinery.
- 2026-08-26 -- Completed object-level Lean bridge and exact generated differential-field
  universality in `FixedDivisorDifferentialFieldUniversality.lean`; targeted module build passed
  and every new endpoint has only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`
  dependencies.
