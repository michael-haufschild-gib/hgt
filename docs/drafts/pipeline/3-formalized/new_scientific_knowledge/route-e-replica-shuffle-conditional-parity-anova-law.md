# Route E replica-shuffle conditional-parity ANOVA law

- **ID:** `ROUTE-E-REPLICA-SHUFFLE-PARITY-ANOVA-001`
- **Stage:** 3-formalized
- **Type:** `[THEOREM (paper)]` / `[NEW ROUTE-E PRODUCER]` / `[SHARP FIREWALL]`
- **Source:** read-only use of
  `HTGeometry/ReplicaHistoryFactorizationLaw.lean`,
  `HTGeometry/ComponentReplicaCollisionLaw.lean`, and
  `HTGeometry/ComponentProjectiveIndependenceWitness.lean`
- **Statement:** Independent component-history shuffles form an exact bistochastic projection.
  After forcing opposite anchor parity, their inverse-load energy is exactly conditional parity
  ANOVA over component-histogram cells.  On a common physical aperture, equal prime histograms
  distort the full replica Gibbs weight by at most
  `m H^2 / (X (X-H))`.  Hence a rate-sharp orbitwise parity-mixing estimate at some
  `m <= X^(1/2+o(1))` implies Route E's strict-half endpoint.  Raw arrangement entropy, even of
  power size, does not imply that estimate.

## Goal

Test whether the grown all-order replica-history corpus repairs the subpower cardinality failure
of pairwise component switching.  It does expose a new exact producer, but not through collision
cardinality.  The useful object is the squared conditional Möbius bias remaining after one forgets
all information except the prime-incidence histogram of an entire finite history.

## Gates

- [x] 0 → 1 in-progress: physical replica aperture and hostile cardinality test stated
- [x] 1 → 2 fully-proven: Theorems A--G below are dependency-closed finite mathematics
- [x] 2 → 3 formalized: exact finite laws are closed in umbrella-wired Lean
- [ ] 3 → 4 publication-ready: requires arithmetic orbit-parity estimate `(29)`

## 1. Component-history shuffle

Let `C` be a finite component set, `R` a finite replica set of cardinality `m>0`, and `I_c` a
finite alphabet for component `c`.  A history is

\[
 x=(x_{r,c})_{r\in R,c\in C}\in\Omega
   :=\prod_{r\in R}\prod_{c\in C} I_c.
\tag{1}
\]

Write

\[
 h_{c,a}(x)=\#\{r:x_{r,c}=a\}.
\tag{2}
\]

Two histories are component rearrangements, written `x~y`, when all numbers `(2)` agree.  Let
`O(x)` be the equivalence class and `N(x)=|O(x)|`.  Define the uniform component-shuffle kernel

\[
 K(x,y)={\mathbf 1_{x\sim y}\over N(x)}.
\tag{3}
\]

### Theorem A — exact bistochastic projection

The kernel `K` is symmetric, row-stochastic, column-stochastic, and idempotent:

\[
 K(x,y)=K(y,x),\qquad K\mathbf 1=K^T\mathbf 1=\mathbf 1,
 \qquad K^2=K.
\tag{4}
\]

Consequently its column load is identically one.  If `(3)` is inserted as a full-row Route E
kernel before imposing parity, then

\[
 \ell_x=1,\qquad q_x=1,
 \qquad \mathcal E_\ell=\mathcal E_q=0.
\tag{5}
\]

#### Proof

Equivalence-class cardinality is constant on each class, so `(3)` is symmetric.  Every row is the
uniform probability on one class; symmetry gives the column assertion.  Averaging twice over the
same class equals averaging once.  Equation `(5)` follows from the definitions of column load and
inverse-load energy. ∎

This is genuine zero-energy transport, but it is not yet a Möbius transport: `(3)` includes
self-edges and both anchor parities.

## 2. Exact slot productization

Fix an anchor replica `r_0`.  Let `Y` be uniform on `O(x)`.  For a joint component label
`a=(a_c)_c`, independent component rearrangement gives

### Theorem B — orbit slot marginal

\[
 \boxed{
 \Pr(Y_{r_0}=a)=\prod_{c\in C}{h_{c,a_c}(x)\over m}.}
\tag{6}
\]

More generally, for component characters `chi_c:I_c->{+1,-1}` and
`s(a)=prod_c chi_c(a_c)`,

\[
 \boxed{
 \mathbb E\,s(Y_{r_0})
 =\prod_{c\in C}
   \left({1\over m}\sum_{a\in I_c}h_{c,a}(x)\chi_c(a)\right).}
\tag{7}
\]

For binary prime-presence components, put `k_c=h_{c,1}` and
`chi_c(u)=(-1)^u`.  Then

\[
 \boxed{\theta(x):=\mathbb E(-1)^{\sum_cY_{r_0,c}}
 =\prod_{c\in C}\left(1-{2k_c\over m}\right).}
\tag{8}
\]

#### Proof

The component-arrangement class is the Cartesian product of the individual component
arrangement classes.  In the class for component `c`, permutation symmetry makes the number of
arrangements having value `a` at `r_0` independent of the chosen slot.  Summing this count over all
`m` slots counts every arrangement exactly `h_{c,a}` times.  Its probability is therefore
`h_{c,a}/m`.  The component choices are independent under the uniform measure on the Cartesian
product, proving `(6)`.  Summing `s(a)` against `(6)` factorizes and proves `(7)` and `(8)`. ∎

Thus all-order shuffling erases intercomponent correlations at one slot exactly.  Whether this
survives the physical aperture is the arithmetic question.

## 3. Aperture restriction preserves bistochasticity

Let `A` be any nonempty subset of histories.  For `x in A`, put

\[
 O_A(x)=O(x)\cap A,\qquad N_A(x)=|O_A(x)|,
\tag{9}
\]

and

\[
 K_A(x,y)={\mathbf 1_{y\in O_A(x)}\over N_A(x)}.
\tag{10}
\]

### Theorem C — conditional orbit projection

`K_A` is again symmetric, bistochastic, and idempotent on `A`.

#### Proof

For `x,y in A`, membership in the same unrestricted orbit implies
`O_A(x)=O_A(y)`.  The proof of Theorem A applies verbatim to these restricted cells. ∎

Therefore restricting every replica to one common aperture does **not** itself create column-load
roughness.  Roughness appears only when every live edge is also forced to reverse the anchor
Möbius sign.

## 4. Opposite-parity rows are exactly conditional parity ANOVA

Give each anchored history a sign `s(x)=s(x_{r_0}) in {+1,-1}`.  In one restricted orbit `O`, put

\[
 a_O=\#\{x\in O:s(x)=+1\},\qquad
 b_O=\#\{x\in O:s(x)=-1\},
\tag{11}
\]

and assume first that both are positive.  From every positive history send uniformly to all
negative histories in the same orbit, and conversely.  This is a full-row, reverse-supported,
parity-flipping recurrence kernel.

### Theorem D — replica-orbit inverse-load identity

On orbit `O`, the incoming loads and reciprocal symmetric degrees are

\[
 \ell_+={b_O\over a_O},\qquad
 \ell_-={a_O\over b_O},\qquad
 q_+={2a_O\over a_O+b_O},\qquad
 q_-={2b_O\over a_O+b_O}.
\tag{12}
\]

At unit vertex weight its inverse-load energy is exactly

\[
 \boxed{
 \mathcal E_q(O)={2(a_O-b_O)^2\over a_O+b_O}.}
\tag{13}
\]

Pure-sign orbits are exactly the orbits on which a full parity-reversing row is impossible; their
whole mass is an explicit isolated boundary term.

#### Proof

The mixed orbit is the complete bipartite row kernel `K_(a_O,b_O)`.  Direct row and column counting
gives `(12)`.  Its `a_Ob_O` edges have symmetric weight
`(a_O+b_O)/(2a_Ob_O)` and reciprocal-degree difference
`2(a_O-b_O)/(a_O+b_O)`, which gives `(13)`.  If one sign class is empty, no opposite-sign target
exists. ∎

Let the restricted orbits partition `A`, set `N=|A|`, and define

\[
 \mathfrak D_A
 ={1\over N}\sum_O{(a_O-b_O)^2\over a_O+b_O}.
\tag{14}
\]

For uniform `X_A in A` and orbit label `H_A`, this is exactly

\[
 \mathfrak D_A
 =\mathbb E\left[\mathbb E(s(X_A)\mid H_A)^2\right].
\tag{15}
\]

Moreover

\[
 \boxed{
 {\left|\sum_{x\in A}s(x)\right|\over |A|}
 \le \sqrt{\mathfrak D_A},
 \qquad
 \sum_O\mathcal E_q(O)=2N\mathfrak D_A.}
\tag{16}
\]

The first bound is conditional Cauchy--Schwarz; the second is `(13)`.  This identifies exact
non-circular content of the all-order shuffle: **conditional parity bias**, not orbit size.

There is an exact scalar firewall:

\[
 \mathfrak D_A
 =\operatorname{Var}\!\left(\mathbb E(s(X_A)\mid H_A)\right)
 +\left({\sum_{x\in A}s(x)\over|A|}\right)^2.
\tag{16a}
\]

Thus `(14)` is a stronger positive producer, not cancellation already proved.  An argument that
controls only its centered variance and then assumes the scalar term is small is circular.  The
lane advances Route E only if `(14)` or `(29)` is proved by source-local signed enumeration of the
histogram cells, without importing the endpoint current.

## 5. Exact aperture-loss comparison

Let `O^*` be an unrestricted component-arrangement orbit, let
`O=O^* \cap A`, and set

\[
 \varepsilon_O=1-{|O|\over|O^*|}.
\tag{17}
\]

Write `theta_O^*` for unrestricted sign mean `(7)` and `theta_O` for sign mean on `O`.

### Theorem E — shell-admission defect

\[
 \boxed{|\theta_O-\theta_O^*|\le2\varepsilon_O.}
\tag{18}
\]

Consequently

\[
 \mathfrak D_A
 \le {2\over|A|}\sum_O |O|(\theta_O^*)^2
     +{8\over|A|}\sum_O |O|\varepsilon_O^2.
\tag{19}
\]

#### Proof

Under the uniform law on `O^*`, condition on `A`.  If `theta_bad` is the sign mean on the
complement, then

\[
 \theta_O^*=(1-\varepsilon_O)\theta_O
             +\varepsilon_O\theta_{bad}.
\]

Both conditional means lie in `[-1,1]`, proving `(18)`.  Square
`|theta_O|<=|theta_O^*|+2 epsilon_O`, use `(u+v)^2<=2u^2+2v^2`, and average. ∎

This is an exact location of the source burden.  Full-orbit productization transfers to the
physical aperture only if component rearrangements retain enough shell mass, or if the signed
restricted-orbit count is estimated directly.  Arrangement theory alone proves neither.

## 6. All-order physical Gibbs curvature

The pair-switch Gibbs estimate has an all-order strengthening.  Let `X>0`, `0<=H<X`, and

\[
 n_r,n'_r\in[X-H,X+H]\quad(r\in R),\qquad
 \prod_r n_r=\prod_r n'_r.
\tag{20}
\]

### Theorem F — product-history Gibbs stability

\[
 \boxed{
 \left|\sum_r n_r-\sum_r n'_r\right|
 \le {mH^2\over X-H}.}
\tag{21}
\]

For product Gibbs weights

\[
 W(n)=\prod_r e^{-n_r/X}=e^{-\sum_rn_r/X},
\tag{22}
\]

one therefore has

\[
 \boxed{
 \left|\log{W(n)\over W(n')}\right|
 \le \eta_{X,H,m}:={mH^2\over X(X-H)}.}
\tag{23}
\]

#### Proof

Write `n_r=X+A_r`, `n'_r=X+B_r`, and `h=H/X`.  For `|u|<=h<1`,

\[
 |\log(1+u)-u|
 =\left|\int_0^u{t\over1+t}\,dt\right|
 \le {u^2\over2(1-h)}.
\tag{24}
\]

Taking logarithms in the product identity `(20)`, applying `(24)` to both histories, and summing
gives

\[
 {1\over X}\left|\sum_r(A_r-B_r)\right|
 \le {mH^2\over X^2(1-H/X)}.
\]

This is `(21)`; `(23)` follows from `(22)`. ∎

At strict-half aperture `H=X^(1/2+o(1))`, any

\[
 m\le X^{1/2+o(1)}
\tag{25}
\]

has `eta_(X,H,m)<=X^(-1/2+o(1))`.  Thus all-order replica lifting up to square-root order does not
lose the physical Gibbs rate.

## 7. Direct Gibbs endpoint theorem

Let `V` be a finite set of squarefree positive integers in `[X-H,X+H]`, let

\[
 \nu(n)={e^{-n/X}\over Z},\qquad Z=\sum_{n\in V}e^{-n/X},
 \qquad \sigma(n)=\mu(n)\in\{+1,-1\},
\tag{26}
\]

and take `A=V^m`, anchored at the first replica.  Partition `A` by the complete prime-incidence
histogram: two histories share a cell when every prime occurs in equally many replica slots.
Unique factorization makes their total products equal.

For a cell `O`, let

\[
 \theta_O={1\over|O|}\sum_{x\in O}\sigma(x_1),
 \qquad
 \pi_O=\nu^m(O),
 \qquad
 \mathfrak D_{V,m}^{\nu}=\sum_O\pi_O\theta_O^2.
\tag{27}
\]

### Theorem G — replica-orbit Route E endpoint

\[
 \boxed{
 {\left|\sum_{n\in V}\mu(n)e^{-n/X}\right|\over Z}
 \le
 \sqrt{2\mathfrak D_{V,m}^{\nu}
       +2\bigl(e^{\eta_{X,H,m}}-1\bigr)^2}.}
\tag{28}
\]

#### Proof

Under `nu^m`, the normalized current is `E sigma(x_1)`.  Condition on orbit `O` and apply
Cauchy--Schwarz to the conditional means.  Theorem F says the largest and smallest product Gibbs
weights in one orbit have ratio at most `e^eta`.  Relative to the uniform law on that orbit, the
normalized density therefore lies in `[e^(-eta),e^eta]`; its signed mean differs from `theta_O` by
at most `e^eta-1`.  Squaring with `(u+v)^2<=2u^2+2v^2` and averaging proves `(28)`. ∎

Hence a new sufficient Route E producer is: for some replica schedule satisfying `(25)`, prove

\[
 \boxed{\mathfrak D_{V,m}^{\nu}\le X^{-1+o(1)}.}
\tag{29}
\]

Then `(28)` gives

\[
 {|J_V(1/X)|\over Z_V(1/X)}\le X^{-1/2+o(1)}.
\tag{30}
\]

### Exact multiplicative component-history specialization

There is no remaining equal-product premise for multiplicative component histories.  If a slot
receiver factorizes as

\[
 n_r(x)=\prod_{c\in C}v_c(x_{r,c}),
\]

then every component-histogram cell satisfies the identity

\[
 \boxed{
 \prod_{r=1}^{M}n_r(x)
 =\prod_{c\in C}\prod_{a\in I_c}v_c(a)^{h_{c,a}},}
\tag{30a}
\]

so the product is literally constant on the cell.  For binary components, with
`k_c=h_{c,1}`, the physical product-Gibbs anchored parity mean therefore obeys

\[
 \boxed{
 \left|\theta_O^\nu-
   \prod_{c\in C}\left(1-{2k_c\over M}\right)\right|
 \le e^{MH^2/[X(X-H)]}-1.}
\tag{30b}
\]

Define exact balanced incidence mass

\[
 B_M(k)=\sum_{c\in C}
  \min\left({k_c\over M},1-{k_c\over M}\right).
\tag{30c}
\]

The scalar inequality
`|1-2u| <= exp(-2 min(u,1-u))` gives the new physical endpoint

\[
 \boxed{
 |\theta_O^\nu|
 \le e^{-2B_M(k)}+left(e^{MH^2/[X(X-H)]}-1\right),}
\tag{30d}
\]

and, equivalently, its squared energy is at most twice the squared exact histogram bias plus twice
the squared curvature defect.  This removes orbit cardinality from the producer completely.
At strict-half curvature, `B_M(k)>=(1/4-o(1)) log X` is a transparent sufficient
square-root-rate condition.  Singleton cells have `B_M(k)=|C|/M`; Proposition H shows that
power-size orbit entropy can still leave this quantity far below logarithmic scale.

This retains the literal Gibbs weight, prime-component history, one common physical aperture, and
every finite-volume Möbius sign.  It is compatible with a prime-dilation construction only after
that construction proves its histories land in this aperture; no such interval-incidence theorem
is hidden here.  Mixed orbit cells carry the explicit full-row recurrence of Theorem D; pure cells
remain visible in `(29)` with maximal bias.

## 8. Sharp entropy firewall

### Proposition H — power-size orbit with asymptotically maximal parity bias

Let every component be binary.  Choose `q` components and a history in which each component is
active in exactly one of the `m` replica slots.  Then

\[
 |O(x)|=m^q,
 \qquad
 \theta(x)=\left(1-{2\over m}\right)^q.
\tag{31}
\]

Thus one may have `m^q>=X` and simultaneously `theta(x)->1`.  For example, take
`q=ceil(log log X)` and `m=ceil(X^(1/q))`; then `m=X^(o(1))`, `m^q>=X`, and `q/m->0`, so `(31)`
tends to one.

#### Proof

Each singleton component independently chooses its one active slot, giving `m^q` arrangements.
Equation `(8)` gives the second identity.  Since
`q log m >= log X` while `q/m -> 0`, logarithming the second expression shows it tends to zero in
the logarithm and hence to one. ∎

Raw all-order collision multiplicity can therefore supply an entire power of nominal entropy
while supplying essentially no parity mixing.  Cardinality, recurrence entropy, form-factor
factorization, and exact prime-log projective independence do not imply `(29)`.

## 9. Heavy conjecture → proof/failure loop

### Loop A — replace pair switches by all-order component-history shuffles

`[PROVED STRUCTURAL SURVIVOR]`  Theorems A--C.  Full component shuffling is an exact bistochastic
projection, survives arbitrary vertex-aperture restriction, and has zero column energy before
parity conditioning.

### Loop B — use all-order arrangement entropy as the missing power

`[FAILED SHARPLY]`  Proposition H.  Power-size orbit multiplicity can coexist with anchor parity
bias tending to one.

### Loop C — retain the component shuffle but condition on opposite Möbius parity

`[PROVED NEW PRODUCER]`  Theorem D.  Its full-row inverse-load energy is exactly conditional
parity ANOVA, with pure-sign cells exposed as isolated mass.

### Loop D — transfer unrestricted slot productization through the common aperture

`[PARTIAL SURVIVOR / ADMISSION FAILURE]`  Theorems B and E.  Full-orbit parity bias is the explicit
product `(8)`, but aperture conditioning costs exactly the restricted-orbit signed enumeration;
small raw rejection is sufficient, not known and not implied by orbit entropy.

### Loop E — all-order recombination destroys physical Gibbs weights

`[FAILED AS OBSTRUCTION]`  Theorem F.  Product-history Gibbs distortion is only
`mH^2/[X(X-H)]`; replica order through `X^(1/2+o(1))` retains strict-half accuracy.

### Loop F — does the grown corpus close Route E?

`[NO]`  Theorem G creates a new exact endpoint lane, but `(29)` is new arithmetic knowledge still
missing.  Neither the HTGeometry history theorems nor the RHTower Wold profile estimates the
aperture-conditioned prime-incidence parity cells.

### Loop G — use cofinal orthogonal replication to erase the remaining energy

`[FAILED PRODUCER / EXACTLY CLASSIFIED]`  `MobiusCofinalReplicaOneCorner.lean` proves a different
replica law: copying each source atom `k` times and dividing its mass by `k` leaves the complete
Möbius score unchanged and divides only the omitted diagonal collision by `k`.  Its cofinal limit
therefore reconstructs the unchanged score.  It neither component-recombines physical integers
nor changes the orbit biases in `(27)`.  This is valuable collision packaging, but using the
vanishing `2/k` term as endpoint cancellation would be replica theatre.

## 10. Revised frontier

Route E now has two non-circular sufficient producers sharing the same arithmetic core:

1. two-sided ordinary column-load edge roughness
   `E_ell<=X^(o(1))`, refined to hydrodynamic residual plus cross-seam energy;
2. replica-orbit conditional parity ANOVA `(29)` for some
   `m<=X^(1/2+o(1))`.

The second is not a relabeling of the first: it averages over complete prime-incidence history
cells and may exploit all-order contingency switching invisible to pairwise edge counts.  Its hard
theorem is

`ENTROPY-COMPLEMENT-APERTURE-CONDITIONED-REPLICA-PARITY-ANOVA`:

- construct source-faithful common-aperture histories across the zero/one-large-prime seam;
- prove square-root-rate cancellation of anchored Möbius sign inside weighted prime-histogram
  cells, or prove enough shell-admissible component switches to compare them with `(8)`;
- keep the same recurrence orientation when passing from replica cells back to physical integers.

This is a genuine new avenue.  It remains open.  No RH statement, orbit estimate `(29)`, seam
theorem, or physical kernel descent is claimed.

## Honest status

Theorems A--G and Proposition H are dependency-closed paper proofs and their exact finite content
is formalized.  Orthogonal replication explicitly preserves the score and therefore still does
not supply `(29)`.  Route E remains open at aperture-conditioned prime-histogram parity energy and
seam descent, not at finite shuffle, counting, Gibbs distortion, or measure-change packaging.

## Log

- 2026-08-11 — originated after read-only audit of grown all-order HTGeometry replica corpus.
- 2026-08-11 — formalized in `RouteEUniformFibreShuffle.lean`,
  `RouteEComponentHistoryShuffle.lean`, `RouteEPhysicalFibreCoarea.lean`,
  `RouteETwoSidedColumnLoadGradient.lean`, `RouteEGibbsProductHistoryStability.lean`,
  `RouteEUniformComparisonEndpoint.lean`, and `RouteEGibbsUniformCellComparison.lean`.
- 2026-08-11 — closed the multiplicative component-history splice and balanced-incidence endpoint
  in `RouteEComponentHistoryGibbsParity.lean`.
- 2026-08-12 — propagated the sharp square-root likelihood defect through arbitrary-multiplicity
  component histograms, balanced-incidence absolute means, singleton histories, and both squared
  parity-energy endpoints.

## Lean implementation and verification

- Exact product-multinomial orbit cardinality, arbitrary-anchor joint marginals, product-character
  means, and binary hostile identities are unconditional Lean theorems.
- Pairwise logarithmic weight oscillation gives the stronger physical-versus-uniform mean defect
  `2 tanh(eta/4)` (with `exp(eta)-1` retained as a coarse corollary); equal-product histories
  instantiate `eta=|R| H^2/(X(X-H))`; physical-fibre conditional energy gives the endpoint.
- Component histograms now discharge equal-product histories exactly.  Arbitrary binary
  multiplicities give the physical bias `prod_c(1-2k_c/M)`, balanced-mass exponential bound
  `(30d)`, and sharp `2 tanh(eta/4)` conditional parity-energy inequalities.
- Targeted builds of `RouteEComponentHistoryShuffle`, `RouteEGibbsUniformCellComparison`, and
  `RouteEPhysicalProductFibreReplica` pass.  Targeted build of
  `RouteEComponentHistoryGibbsParity` also passes.  No umbrella or full build was run.
- Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Sharp square-root likelihood-ratio strengthening

Let `Omega` be finite and nonempty, let `w_x>0`, and suppose

\[
 \left|\log{w_x\over w_y}\right|\le\eta
 \qquad(x,y\in\Omega).
\tag{31}
\]

For every `|f_x|<=1`, write `a=|Omega|^{-1} sum_x w_x`.  Then

\[
 \boxed{
 \left|{\sum_xw_xf_x\over\sum_xw_x}
       -{\sum_xf_x\over|\Omega|}\right|
 \le 2\tanh(\eta/4).}
\tag{32}
\]

Indeed, put `L=min_x w_x`, `s=exp(eta/2)`, and `U=s^2L`.  Pairwise oscillation gives
`L<=w_x<=U`.  Since the centered deviations sum to zero,

\[
 \sum_x|w_x-a|=2\sum_x(w_x-a)_+.
\]

The interval bounds imply pointwise

\[
 (w_x-a)_+
 \le {U-a\over U-L}(w_x-L),
\]

and hence

\[
 {1\over |\Omega|a}\sum_x|w_x-a|
 \le {2(U-a)(a-L)\over a(U-L)}.
\]

The entire improvement over `exp(eta)-1` is the exact square identity

\[
 aL(s-1)^2-(U-a)(a-L)=(a-sL)^2\ge0.
\]

Using `U-L=(s-1)(s+1)L` gives `(32)` because

\[
 {2(s-1)\over s+1}=2\tanh(\eta/4).
\]

Combining `(23)` with `(32)`, equal-product histories in one common aperture satisfy

\[
 \boxed{
 |\mathbb E_{\rm Gibbs}f-\mathbb E_{\rm unif}f|
 \le 2\tanh\!\left({mH^2\over4X(X-H)}\right).}
\tag{33}
\]

The physical-fibre endpoint correspondingly strengthens to

\[
 |\mathbb E_{\rm physical}\sigma|
 \le
 \sqrt{2\mathfrak D_{\rm uniform}
       +2\left(2\tanh(\eta/4)\right)^2}.
\tag{34}
\]

All statements `(31)`--`(34)` are formalized unconditionally in
`RouteEGibbsUniformCellComparison.lean`.  This removes the exponential blow-up of the old coarse
defect while leaving the genuine Route E producer unchanged: prime-histogram bias/energy,
common-aperture admission, and recurrence-compatible seam descent.
