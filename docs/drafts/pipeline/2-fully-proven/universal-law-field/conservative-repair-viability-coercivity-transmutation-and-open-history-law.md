# Conservative repair, viability--coercivity transmutation, and open-history law

- **ID:** ULF-ALM-1
- **Stage:** 2-fully-proven
- **Type:** ROUTE-INDEPENDENT MECHANISM THEOREM / THIRD AUTOPOIETIC-LAW LABORATORY
- **Statement:** Adjoining one semantically dependent repair preserves the represented state space
  but creates one new history direction.  In the positive minimal-circuit chamber this repair
  changes a strictly progressive system into a uniquely self-maintaining one, destroys every
  strictly progressive scalar certificate, and generates arbitrarily long positive-cost histories
  with stationary semantic endpoint.
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [MECHANISM NOT OBJECT]
  [CONSERVATIVE REPAIR] [POSITIVE CARRIER BIRTH] [COERCIVITY LOSS]
  [ENDOGENOUS NEXT CHALLENGE] [LEAN REQUIRED] [NOT AUTOCATALYSIS] [NOT RH]

## 1. Founding question

The first two Autopoietic Law Mechanics laboratories prove that conservative repair can create new
execution without changing semantic closure, and that repair outputs can become the witnesses of a
later repair layer.  They do not couple law production to viability or coercivity.

The present theorem asks for a mechanism rather than another carrier:

> What must happen when a missing execution is repaired by a rule whose semantic effect was already
> representable, but whose admission closes a positive execution cycle?

The answer is an exact transmutation.  Semantic image stays fixed.  Kernel history gains one
direction.  A positive carrier is born.  Strict scalar progress becomes impossible.  Repetition of
the new carrier is then an endogenous next challenge invisible to endpoint semantics.

## 2. General conservative-extension law

Let `V` be a real vector space.  Let

\[
 B:\mathbb R^d\longrightarrow V
\]

be a linear semantic-boundary map for the old execution rules.  Choose `c in R^d` and adjoin the
repair rule

\[
 r=-B(c).
\tag{1}
\]

The enlarged execution map is

\[
 \widetilde B:\mathbb R^d\oplus\mathbb R\longrightarrow V,
 \qquad
 \widetilde B(x,t)=B(x)-tB(c)=B(x-tc).
\tag{2}
\]

The old and new coordinates record execution multiplicities.  Their images record net semantic
effects.  Their kernels record histories with zero semantic endpoint displacement.

### Theorem 2.1 -- conservative repair transfers freedom to history

The repair `(1)` obeys:

1. **stationary semantics**
   \[
   \operatorname{im}\widetilde B=\operatorname{im}B;
   \tag{3}
   \]
2. **split history birth**
   \[
   \ker\widetilde B
   =\{(k+tc,t):k\in\ker B,\ t\in\mathbb R\};
   \tag{4}
   \]
3. the map
   \[
   \ker B\oplus\mathbb R\longrightarrow\ker\widetilde B,
   \qquad (k,t)\longmapsto(k+tc,t)
   \tag{5}
   \]
   is a linear isomorphism with inverse `(x,t) -> (x-tc,t)`;
4. in finite dimension,
   \[
   \dim\ker\widetilde B=\dim\ker B+1
   \tag{6}
   \]
   although the semantic image is unchanged.

#### Proof

Equation `(2)` factors through `B`, so `im Btilde subset im B`.  Conversely
`B(x)=Btilde(x,0)`, proving `(3)`.  Further,

\[
 \widetilde B(x,t)=0
 \Longleftrightarrow B(x-tc)=0
 \Longleftrightarrow x-tc\in\ker B,
\]

which is exactly `(4)`.  The displayed maps in `(5)` are inverse by direct substitution.  Equation
`(6)` follows from the direct-sum isomorphism.  QED.

This is not a rank slogan.  It identifies where the missing degree goes: conservative semantic
extension necessarily produces a lineage coordinate.

## 3. Positive minimal-circuit chamber

Assume now that `v_1,...,v_d` is a basis of `V`, and let

\[
 B(x)=\sum_{i=1}^d x_i v_i.
\tag{7}
\]

Choose positive numbers `a_i>0` and the repair

\[
 r=-\sum_{i=1}^d a_i v_i.
\tag{8}
\]

Thus `c=(a_1,...,a_d)` and `B` is injective.

Call a vector of rule multiplicities **feasible** when all coordinates are nonnegative.  A
nonzero feasible element of the semantic kernel is a **self-maintaining circulation**: it executes
rules with no net loss or gain in semantic state.  It is **full-support** when every rule occurs
strictly positively.

### Theorem 3.1 -- exact viability cone and minimality

For the enlarged rule family `(v_1,...,v_d,r)`:

1. the old feasible kernel is `{0}`;
2. the enlarged feasible kernel is exactly the ray
   \[
   \ker\widetilde B\cap\mathbb R_{\ge0}^{d+1}
   =\{t(a_1,...,a_d,1):t\ge0\};
   \tag{9}
   \]
3. every nonzero feasible circulation has full support;
4. after the normalization `sum_i x_i+t=1`, there is one and only one feasible circulation,
   \[
   \frac{1}{1+\sum_i a_i}(a_1,...,a_d,1);
   \tag{10}
   \]
5. deleting any one rule destroys every nonzero feasible circulation.

#### Proof

Injectivity of the basis map gives the old kernel `{0}`.  Theorem 2.1 gives every enlarged kernel
vector uniquely as `t(a_1,...,a_d,1)`.  Feasibility is equivalent to `t>=0`; strict positivity of
all `a_i` gives full support when `t>0`.  The normalization fixes

\[
 t=(1+\sum_i a_i)^{-1},
\]

proving `(10)`.  Finally, every nonzero kernel vector has every coordinate nonzero, so it cannot be
supported after any column is deleted.  QED.

The repair does not merely add a positive vector.  It creates the unique extreme ray of a new
viability cone, and every admitted rule is load-bearing.

## 4. Dual coercivity transition

A **strict progress certificate** is a linear functional `ell:V->R` satisfying

\[
 \ell(v_i)>0
\]

for every admitted rule vector.

### Theorem 4.1 -- strict progress and positive circulation are incompatible

1. The old basis rules admit a strict progress certificate.
2. The enlarged family `(v_1,...,v_d,r)` admits none.

#### Proof

Define `ell(v_i)=1` on the basis and extend linearly.  This proves the first clause.

For the second, suppose `ell(v_i)>0` for every old rule and `ell(r)>0`.  Equation `(8)` gives

\[
 \ell(r)=-\sum_i a_i\ell(v_i)<0,
\]

a contradiction.  QED.

This is the minimal strict chamber of the Gordan alternative.  The field-level law is its repair
interpretation:

\[
\boxed{
\text{semantically conservative repair}
\quad\Longrightarrow\quad
\text{positive circulation birth can destroy strict progress}.}
\tag{11}
\]

The theorem does not say that every conservative repair is viable.  Sign of the dependence
coefficients is load-bearing.  Mixed signs create a history direction without a nonnegative
carrier.

## 5. Repair-generated next challenge

Suppose the coefficients `a_i` are positive integers.  Let

\[
 h_n=n(a_1,...,a_d,1),\qquad n\in\mathbb N.
\tag{12}
\]

### Theorem 5.1 -- stationary endpoint, open lineage, and nonintegrable positive cost

1. Every history `h_n` has the same semantic endpoint displacement:
   \[
   \widetilde B(h_n)=0.
   \tag{13}
   \]
2. Its execution size is
   \[
   \|h_n\|_1=n\left(1+\sum_i a_i\right),
   \tag{14}
   \]
   hence is unbounded.
3. If every rule has a strictly positive cost `q_i>0`, then
   \[
   \operatorname{Cost}(h_n)
   =n\left(q_{d+1}+\sum_i a_iq_i\right)\longrightarrow\infty.
   \tag{15}
   \]
4. No endpoint potential `Phi:V->R` can represent that positive execution cost as
   `Phi(final)-Phi(initial)` on these histories, since every endpoint difference is `0` while every
   nonzero history has positive cost.

#### Proof

Equation `(13)` is `(9)`.  Equations `(14)` and `(15)` follow by summing nonnegative coordinates.
For clause 4, both endpoints are the same semantic state, so any state-function difference
telescopes to zero.  The positive rule cost is nonzero for `n>0`.  QED.

The new circulation is therefore the repair's endogenous next challenge.  No external
counterexample is needed.  Once the repair is admitted, its repeated legal execution creates
unbounded lineage invisible to terminal semantics.  A later law must do at least one of the
following:

1. forbid or orient the cycle;
2. retain a history/cost coordinate;
3. quotient the cycle and explicitly accept lineage erasure;
4. add a resource law limiting repetition.

This is autopoietic failure production in a finite linear laboratory: repair output becomes a legal
input to the next failure mechanism.

## 6. Canonical two-resource cell

Take `V=R^2`, old rules

\[
 v_1=(1,0),\qquad v_2=(0,1),
\]

and repair

\[
 r=(-1,-1).
\]

Then

\[
 \widetilde B(x,y,t)=(x-t,y-t).
\tag{16}
\]

The image remains all of `R^2`; the kernel is the line `(t,t,t)`; the feasible kernel is its
nonnegative ray; the normalized carrier is `(1/3,1/3,1/3)`; deleting any rule kills the cycle.  The
old certificate `ell(u,v)=u+v` is positive on both old rules and negative on the repair.  No
functional can be positive on all three.  Histories `(n,n,n)` have zero endpoint and size `3n`.

This concrete cell will be the unconditional Lean capstone.  The general theorem explains why it
is not a fitted example.

## 7. Hostile conjecture loops

### Loop A -- semantic conservativity preserves operational acyclicity

**False.**  The image is stationary while the kernel gains one split direction by Theorem 2.1.

**Survivor.**  Every dependent added rule produces one new linear history coordinate.

### Loop B -- every new kernel direction creates a viable carrier

**False.**  If `c` has mixed signs, `(c,1)` is not nonnegative and the new line may miss the
positive orthant except at zero.

**Survivor.**  Positive-circuit birth is exactly a signed dependence chamber, not a consequence of
rank alone.

### Loop C -- closure and self-maintenance are the same

**False.**  Image equality `(3)` is semantic closure; positive kernel existence `(9)` is
self-maintenance.  They change independently.

**Survivor.**  Repair can leave closure fixed while crossing the viability wall.

### Loop D -- the positive cycle proves autocatalysis

**False.**  Stoichiometric circulation does not provide an explicit catalyst, replication law, or
kinetic growth rate.  Recent explicit-catalysis work shows that stoichiometric matrices alone can be
inconclusive about catalytic cores.

**Survivor.**  The theorem proves self-maintaining circulation and open execution history only.

### Loop E -- a positive metric selects the repair

**False.**  The repair was supplied before the positive circuit.  Moreover the corpus's repair
torsor theorem shows that a fitted metric can make any chosen splitting least-work.

**Survivor.**  Positivity tests viability after a source-derived repair; it does not select that
repair.

### Loop F -- positive circulation and strict scalar progress can coexist

**False on the same directed support.**  Summing a positive progress functional around a positive
zero-boundary circulation gives a strict positive number and zero simultaneously.

**Survivor.**  Their incompatibility is a theorem-of-alternatives phase boundary.  Reversing or
removing rules changes the support and can change the chamber.

### Loop G -- the new cycle is harmless because its semantic endpoint is zero

**False.**  Positive per-rule cost grows linearly along histories `(12)` and cannot descend to an
endpoint potential.

**Survivor.**  Endpoint semantics is complete only after explicitly discarding lineage and cost.

## 8. Parent mathematics and exact field residue

The linear ingredients are classical:

- Gordan's theorem identifies the alternative between a nonzero nonnegative kernel vector and a
  strictly positive dual potential;
- Petri-net `T`-invariants and stoichiometric flux cones encode nonnegative zero-boundary cycles;
- chemical organization theory separates closure from self-maintenance;
- reaction-network thermodynamic soundness excludes positive futile cycles in an irreversible
  support.

Primary parents include Müller et al., *What makes a reaction network chemical?* (2022), which
uses Gordan/Minty alternatives to characterize futile-cycle obstruction to thermodynamic
soundness, and Dittrich--Speroni di Fenizio, *Chemical organisation theory* (2007), which defines
organizations by closure plus self-maintenance.  Hordijk--Steel-style self-generating networks add
food and catalysis.  Golnik--Gatter--Stadler--Vassena (2026) warns that explicit catalysis is not
recoverable from stoichiometry alone.

The field residue is not priority for those ingredients.  It is the exact feedback interpretation
of their conjunction:

1. conservative law repair moves freedom from semantic image to history kernel;
2. sign of the born relation decides whether a viable carrier nucleates;
3. viable cycle birth can destroy strict scalar progress;
4. the carrier's repeatability manufactures the next challenge automatically;
5. terminal semantics then loses an unbounded positive-cost lineage.

This is a law set governing a transition, not a proposal for one universal geometric object.

## 9. Scope

1. The theorem is finite-dimensional and linear.
2. It proves no kinetics, catalyst, persistence theorem, compactness, or cofinal estimate.
3. It does not choose the repair.  Source production remains a separate law.
4. It does not assert that viability is always desirable: the same cycle obstructs strict
   irreversible thermodynamic orientation.
5. It does not identify positive-carrier existence with whole-space coercivity in every corpus
   route.  It proves a minimal mechanism where repairing one deficit creates the other.
6. It has no RH implication.

## 10. Formalization target

Formalize the canonical cell `(16)` in
`GaloisForLFunctions.HTGeometry.ConstitutiveViabilityCoercivityTransmutation` with an unconditional
capstone certifying:

1. old/new image equality;
2. exact new kernel and unique normalized nonnegative carrier;
3. minimal support;
4. old strict progress and impossibility of new strict progress;
5. zero semantic endpoint and unbounded execution size for the integer history family;
6. impossibility of endpoint integration of positive unit rule cost.

No project axiom, `sorry`, `admit`, `opaque`, `unsafe`, or computational decision procedure is
permitted.

## Log

- 2026-08-10 -- static positive-circuit conjecture strengthened to a repair-transmutation law;
  explicit-catalysis and selection overclaims removed; general paper proof closed.
