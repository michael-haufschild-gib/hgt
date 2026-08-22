# The `O(N)` exchange cocycle admits a uniformly conditioned Coxeter--Cartan frame

- **ID:** `quantitative-coxeter-cartan-hardy-trivialization`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / QUANTITATIVE COMPLEX ANALYSIS / COMPACT-LOCAL QFT GATE
- **Scientific status:** `[CONJECTURE] [PUBLISHED OPEN PROBLEM SHARPENED]`
  `[NOT A NEW CONJECTURE] [NEW ATTACK UNVERIFIED]`
- **Scope:** the standard regular `O(N)` identity-zero adjacent-braid scattering family,
  `N>=3`; no RH and no distinguished scalar special-function input
- **Parent:**
  `../2-fully-proven/not_new_scientific_knowledge/06-integrable-qft-yang-baxter/fixed-particle-holomorphic-acyclicity-identity-zero-yang-baxter.md`
- **Real-frame theorem:**
  `../2-fully-proven/not_new_scientific_knowledge/06-integrable-qft-yang-baxter/collision-regular-relative-yang-baxter-chamber-frame.md`
- **Statement:** On the Alazzawi--Lechner particle tubes, the standard `O(N)` braid cocycle has
  exact holomorphic frames `J_n` satisfying

  ```text
  J_n(z) B_k(z_(k+1)-z_k)=-J_n(z^tau_k)                    (1)
  ```

  and constants `gamma,gamma_tilde` independent of `n` such that

  ```text
  sup_(z in Omega_n) ||J_n(z)|| <= gamma^n,
  sup_(theta in R^n) ||J_n(theta+i lambda_(pi/2))^(-1)||
    <= gamma_tilde^n.                                       (2)
  ```

## Why this is the exact open theorem

The fixed-particle parent theorem proves `(1)` abstractly by sign-corrected equivariant descent
and Oka--Grauert.  It kills ordinary holomorphic and topological obstruction classes.  The
identity-zero componentwise-Pauli theorem proves that `(2)`, combined with the already established
Hardy continuation, gives the factorial improvement needed for modular nuclearity and compact
locality.

Thus the `O(N)` problem is neither existence of some holomorphic frame nor permutation-cocycle
coherence.  It is the uniform condition number `(2)` on a noncompact family of shrinking tubes.
This is Alazzawi--Lechner's published open intertwiner problem, now stripped of its qualitative
cohomology shell.

## SOTA and parent-theory audit

1. Alazzawi--Lechner Definition 5.2 is exactly `(1)`--`(2)` plus the central subspace mapping.
   Their diagonal construction has the bounds; the `O(N)` construction reaches only particle
   number two.
2. Ordinary and equivariant Oka principles give holomorphic triviality and compact-open
   approximation, not a global supremum bound on the unbounded tube.
3. Berndtsson--Rosay obtain bounded factorization in one complex variable.  Several-variable
   quantitative Cartan lemmas require a cocycle uniformly close to the identity.  The `O(N)`
   cocycle is unitary on the central real slice but is not uniformly close to `I` for arbitrary
   real rapidity differences.
4. Coordinatewise strip-to-disc maps identify the tube with `D^n` and its quotient with the
   symmetrized polydisc.  Generic matrix-corona or bounded-bundle results do not provide the
   required equivariance, square completion, and constants uniform in both rank and particle
   number.  Treil--Wick's polydisc theorem is an `H^p`, `p<infinity`, matrix-corona result; the
   `H-infinity` completion theorems found in the audit are one-variable.
5. Finite-group/additive bounded-cohomology averaging proves a bounded linear projection onto
   equivariant sections.  It does not produce an invertible section with a lower singular-value
   bound.

No SOTA theorem found in the audit implies `(2)`, and no counterexample specific to the regular
`O(N)` cocycle was found.  Generic claims about the status of the multidimensional corona problem
are not used as evidence either way.

## Upper exponential scale `[PROVED REDUCTION]`

On

```text
Omega_n=R^n+i(lambda_(pi/2)+(-kappa/(2n),kappa/(2n))^n),    (3)
```

every rapidity difference lies at imaginary distance at most `kappa/n` from the real axis.
Real-axis unitarity and the three-lines theorem therefore give a loss `M^(O(1/n))` for each
adjacent scattering factor.  A longest permutation word has `n(n-1)/2` factors, so the complete
permutation cocycle satisfies

```text
sup_(pi,z) ||A_n^pi(z)|| <= exp(C n),
sup_(pi,z) ||A_n^pi(z)^(-1)|| <= exp(C_tilde n).             (4)
```

Hence the upper scale in `(2)` is dimensionally compatible with the full noncommuting cocycle.
The `O(n^2)` pair count is not the obstruction.

## Canonical rectangular regular frame `[PROVED REDUCTION]`

Let `G=S_n`, `m=|G|=n!`, and define the stacked holomorphic operator

```text
T_n(z):V -> l2(G) tensor V,
(T_n(z)v)_pi=m^(-1/2) A_n^pi(z)^(-1)v.                     (5)
```

If `P_sigma` is left translation of the `G` block index, the cocycle identity gives

```text
T_n(z_sigma)=P_sigma T_n(z) A_n^sigma(z).                  (6)
```

On the central real slice every `A_n^pi` is unitary, so the factorial number of blocks cancels
the normalization exactly:

```text
T_n(theta)^* T_n(theta)=I.                                 (7)
```

Thus `T_n` has central lower singular value one, with no `n!` loss.  On the full tube, `(4)` gives

```text
exp(-C n)||v|| <= ||T_n(z)v|| <=exp(C_tilde n)||v||.        (8)
```

The lower bound follows because every block obeys
`||A_n^pi(z)^(-1)v||>=||A_n^pi(z)||^(-1)||v||`, and the normalized sum of the `n!` squared block
norms cancels the factorial exactly.  Hence equations `(5)`--`(8)` solve the full exponential
condition-number problem after stabilization to the regular block representation.  The remaining
step is **square compression**: find a holomorphic family

```text
L_n(z):l2(G) tensor V -> V                                 (9)
```

with the matching block equivariance and `exp(O(n))` bounds such that `L_n(z)T_n(z)` is invertible
and uniformly well-conditioned on the central slice.  No inverse away from that slice is required
by Definition 5.2. The constant invariant coisometry
`m^(-1/2) sum_pi` turns `L_n T_n` into the normalized Reynolds average.  Hence the determinant and
least-singular-value failure below is precisely failure of the obvious square compression, not
failure of a controlled rectangular frame.

The exact covariance required of the compressor is

```text
L_n(z_sigma) P_sigma=L_n(z).                               (9a)
```

Then `J_n=L_n T_n` satisfies `(1)` automatically.  The square-compression formulation is therefore
equivalent to the remaining construction problem once the bounds and invertibility are included;
it is not merely an analogy with matrix completion.  Conversely, any frame `J_n` satisfying
`(1)` gives such a compressor by the block formula

```text
(L_n(z))_pi=m^(-1/2) J_n(z) A_n^pi(z),                    (9b)
```

and `(4)` preserves the exponential upper scale.

## Controlled continuous square frame `[PROVED REDUCTION]`

The square-compression obstruction is purely holomorphic, not topological or metric.  Define the
Hermitian metric on the sign-corrected exchange bundle by

```text
H_n(z)=m^(-1) sum_(pi in G)
  A_n^pi(z)^(-*) A_n^pi(z)^(-1).                           (9c)
```

The cocycle identity gives

```text
H_n(z_sigma)=A_n^sigma(z)^* H_n(z) A_n^sigma(z),           (9d)
```

which is exactly the descent law for the right action `(z,v).sigma=(z_sigma,A_sigma^(-1)v)`.
By `(4)`, this metric is uniformly comparable with the standard fiber metric:

```text
exp(-2 C n) I <= H_n(z) <= exp(2 C_tilde n) I.             (9e)
```

On the central real slice every cocycle matrix is unitary, hence `H_n=I`.

The quotient is contractible, so its descended Hermitian bundle has a global continuous
orthonormal frame.  Pulling that frame back and taking its inverse gives a continuous exact
intertwiner `J_n^cont` satisfying `(1)` and

```text
sup ||J_n^cont|| <=exp(C_tilde n),
sup ||(J_n^cont)^(-1)|| <=exp(C n),                         (9f)
```

with `J_n^cont` unitary on the central real slice.  Thus all topology, square selection, and
condition-number control are already solved in the continuous category.  The remaining theorem
is precisely a bounded holomorphization of this frame that retains `(9f)` up to `exp(O(n))` loss.
Ordinary equivariant Oka holomorphizes it only in the compact-open topology.

## Explicit chamber frame and approximation reduction `[PROVED]`

There is a more rigid continuous frame on the central real slice, which we identify with `R^n`
by suppressing the common imaginary shift.  For a generic `theta in R^n`, let `p(theta)` be the
unique permutation for which `theta_(p(theta))` is ordered,
and set

```text
J_n^ch(theta)=A_n^(p(theta))(theta)^(-1).                  (9g)
```

At a collision, two sorting permutations differ by a point stabilizer.  Stabilizer triviality
therefore makes `(9g)` independent of the choice and extends it continuously across every
collision hyperplane.  It is unitary and satisfies the exact central cocycle equation.

Let

```text
C_B=sup_(x in R) ||B'(x)||<infinity.                       (9h)
```

Regular strip analyticity gives the finiteness in `(9h)`.  In an inversion-factor expression for
`A_n^p`, each rapidity coordinate occurs in at most `n-1` two-body factors.  All other factors are
unitary on the real slice, so on every chamber

```text
||partial_(theta_j) J_n^ch|| <=(n-1) C_B.                  (9i)
```

Continuity across the finitely many walls crossed by a line segment turns `(9i)` into a global
Lipschitz estimate.  The frame is not real analytic at a generic wall; the one-sided derivative
jump is already visible at particle number two.

The wall singularity has an exact one-variable normal form.  Suppose two adjacent chambers use
sorting permutations `p` and `p tau_k`, put

```text
u=(z_p)_(k+1)-(z_p)_k,
H_p(z)=A_n^p(z)^(-1).                                    (9i-a)
```

The cocycle identity gives the two chamber formulas

```text
J_n^ch(z)=H_p(z),
J_n^ch(z)=A_k(u)^(-1) H_p(z),                             (9i-b)
```

on the respective sides.  Since `A_k(0)=I`, they glue continuously on `u=0`.  Their normal
derivative jump there is

```text
-A_k'(0) H_p(z).                                         (9i-c)
```

Thus every generic collision seam is a one-dimensional matrix hinge multiplying a holomorphic
background.  Multiple-collision strata are where these hinges must satisfy the braid and
shifted-basepoint coherence simultaneously.  Formula `(9i-b)` is elementary cocycle algebra, not
a novelty claim, but it localizes the possible special cancellation needed by `(9o)`.

The first jet at the total collision does not itself supply that cancellation.  After
sign normalization, linearization along `theta=t x` has the braid-fan spline form

```text
J_n^ch(t x)
  =I+t[L(x)+sum_(i<j) (x_i-x_j)_+ K_(i j)]+O(t^2),        (9i-d)
```

for a chamber-independent affine gauge term `L` and embedded two-leg infinitesimal crossing
operators `K_(i j)`.  Every inverted pair crosses once and all ordering commutators vanish to
first order.  Thus `(9i-d)` is ordinary type-`A` braid-fan spline geometry, not a new obstruction.
At higher order, partition-lattice cumulants, connected label graphs, Magnus/BCH terms, and
iterated conormal symbols are likewise established parent languages.

More importantly, a germ at the total collision cannot prove `(9l)`.  The approximation is
uniform on the complete unbounded real slice, hence it must control every translated partial
collision stratum with arbitrary spectator separations and both rapidity ends.  A scientifically
meaningful connected-symbol attack would therefore require a **uniform stratified majorant** over
all collision flats and noncompact tangential directions.  Standard polymer estimates require
activity small enough to compensate an incompatibility degree of order `n`; the present central
wall factors are order one.  Until a Yang--Baxter cancellation supplies that compensation,
"collision cumulants" are bookkeeping rather than a solution.

Now let `F_n` be any bounded holomorphic matrix on `Omega_n`, with no equivariance assumption,
and define its twisted Reynolds projection

```text
P_n(F_n)(z)=m^(-1) sum_(pi in G)
  F_n(z_pi) A_n^pi(z)^(-1).                               (9j)
```

The cocycle identity gives

```text
P_n(F_n)(z_sigma)=P_n(F_n)(z) A_n^sigma(z).                (9k)
```

If, for one fixed `0<delta<1`,

```text
sup_(theta in R^n) ||F_n(theta)-J_n^ch(theta)|| <=delta,
sup_(z in Omega_n) ||F_n(z)|| <=exp(C_F n),                (9l)
```

then central unitarity of the cocycle and `(4)` yield

```text
sup_theta ||P_n(F_n)(theta)-J_n^ch(theta)|| <=delta,
sup_Omega ||P_n(F_n)|| <=exp((C_F+C_tilde)n).              (9m)
```

Hence `P_n(F_n)` is centrally invertible with inverse norm at most `(1-delta)^(-1)` and solves
`(1)`.  The full conjecture is reduced to the boundary approximation problem `(9l)`: approximate
the explicit Coxeter-chamber unitary by a bounded holomorphic seed on the `1/n` tube with only
exponential growth.  No holomorphic invertibility or equivariance is required of the seed.

## Generic holomorphic smoothing audit and route kill

The reduction `(9l)` is not closed by inserting a standard multivariate mollifier.  The Euclidean
Lipschitz constant following from `(9i)` is

```text
Lip_2(J_n^ch) <= C_B n sqrt(n-1).                         (9n)
```

A product band-limited kernel has a typical Euclidean displacement of order `sqrt(n)/sigma`.
Constant real-slice error therefore requires coordinate bandwidth at least order `n^2`.  But the
product tube has `||Im z||_1=O(1)`, so its complex growth is then `exp(O(n^2))`, not
`exp(O(n))`.  A spherical-spectrum kernel has typical displacement of order `n/sigma`; `(9n)`
then requires `sigma=O(n^(5/2))`, while `||Im z||_2=O(n^(-1/2))`, again giving
`exp(O(n^2))`.  Gaussian smoothing at the scale forced by `(9n)` gives the still worse bound
`exp(O(n^3))`.

This dimension loss is not merely an artefact of one proof.  The classical Newman--Shapiro and
Ganzburg Jackson estimates have explicit dimension dependence; Ganzburg notes sharp dimension
dependence even for the ball, cube, and octahedron.  Consequently the tempting dimension-free
entire Jackson lemma for an arbitrary bounded Lipschitz map is not an available parent theorem.
The exact useful successor must be special to the Coxeter--Yang--Baxter chamber frame:

```text
[CONJECTURE: COXETER JACKSON LEMMA]
J_n^ch admits a bounded entire approximation of spherical type O(n^(3/2)),
or another spectrum whose support function is O(n) on the AL tube,
with one fixed real-slice error delta<1.                  (9o)
```

If `(9o)` holds, Bernstein growth gives exactly `exp(O(n))` on `Omega_n`, and `(9j)`--`(9m)`
finish the intertwiner property.  Generic Jackson theory does not support `(9o)`; a proof must use
braid compatibility, collision strata, or another special cancellation.  Logistic sorting gates
do not do this: slope `O(n)` keeps their poles outside a `1/n` tube but gives only `O(1/n)`
per-gate resolution across `O(n^2)` gates, whereas slope `O(n^2)` moves poles into the tube.
SoftSort and NeuralSort retain absolute values or order statistics and are not holomorphic.

Song-Ying Li's sup-norm `dbar` theorem on product domains has the promising estimate

```text
||S f||_infinity
  <= n C_Omega (1-gamma)^(-n)
     sum_k ||d_Omega(z_k)^gamma f_k||_infinity,  0<gamma<1,       (9p)
```

which has the correct exponential dimension scale.  It still does not prove `(9l)`: smoothing the
chamber frame has no known sufficiently small `dbar` defect, the correction in `(9p)` need not be
smaller than the fixed central invertibility margin, and conformally moving the unbounded strip to
the disk creates inverse-distance growth at the two rapidity ends, while `(9p)` permits only a
strictly subcritical distance weight.  This is a precise near miss, not a bounded Oka theorem.

## Corona and maximal-ideal-space audit

The compressor problem is not presently a matrix-corona corollary.  Central conditioning is
strictly weaker than a corona hypothesis: a bounded holomorphic scalar can be bounded away from
zero on the real diameter of a disk and still vanish off that diameter.  Conversely, exact
unitarity on an open real cube would be far stronger than needed: if
`J(x)^* J(x)=I` there, the holomorphic reflection `J^sharp(z)=J(conj z)^*` satisfies
`J^sharp J=I` everywhere by the identity theorem.  Definition 5.2 asks only for a central lower
singular-value bound and allows complex-tube determinant zeros.

Known matrix-corona estimates also have the wrong rank scale.  Treil constructed globally
corona-bounded rectangular matrices for which every bounded left inverse has norm exponential in
the column rank.  Here the rank is `N^n`, so a generic matrix-corona bound can be doubly
exponential in `n`.  The disk analytic-projection and bounded-factorization theorems, the
`H^p`, `1<p<infinity`, polydisk theorem, and the symmetrized-bidisk Toeplitz criterion all require
global domain hypotheses and do not retain the finite-group covariance or rank-uniform constants.
The scalar `H^infinity(D^n)` corona problem for `n>=2` also remains open; the 2021 claim and its
2025 successor were withdrawn, the latter in March 2026 with gaps acknowledged.

There is qualitative projective freeness for the symmetric polydisc algebra continuous on the
closed polydisc, whose geometric maximal ideal space is contractible.  That is the wrong algebra:
symmetric `H^infinity` has non-geometric maximal-ideal fibres, and no corresponding quantitative
projective-freeness theorem is known.  The exact open core remains `(9l)`, not a hidden standard
completion theorem.

## Reynolds attempt and exact failure

Twisted Reynolds averaging sends a bounded holomorphic seed to an exact equivariant section.  By
`(4)`, a normalized average can retain an `exp(O(n))` upper norm.  At the total collision it is the
identity after normalization, so it is invertible near that point.

The attempt fails globally for a precise reason:

```text
unitary matrices can cancel in their average on the central slice;
the available estimates do not exclude determinant zeros there;
even without zeros, they do not prevent the least singular value
from tending to zero at real rapidity infinity.                       (10)
```

Oka theory supplies a different everywhere-invertible holomorphic section, but no bound on its
condition number.  The raw Reynolds estimate therefore fails as a proof; `(10)` is not evidence
that the `O(N)` average actually becomes singular. Additive bounded-cohomology vanishing does not
control this nonlinear square-selection problem.

## Radial Oka homotopy and exact uniform failure

The equivariant contraction used in the qualitative theorem suggests scaling every rapidity
difference to zero and integrating the infinitesimal cocycle.  For a two-body factor this
differentiates

```text
t |-> B(t u),
d/dt B(t u)=u B'(t u).                                     (11)
```

This route cannot supply a rapidity-uniform estimate.  If `B` is nonconstant, choose a real
`x_0 != 0` with `B'(x_0) != 0`.  Since `u` ranges over the complete real line,

```text
sup_(u in R) ||u B'(t u)||
  =(1/t) sup_(x in R) ||x B'(x)||
  >=||x_0 B'(x_0)||/t.                                    (12)
```

The resulting `dt/t` majorant is non-integrable at `t=0`.  Finite-group averaging can cancel
parts of the infinitesimal cocycle, so `(12)` is not a no-go for every homotopy construction; it is
an exact kill of the naive uniform contraction estimate.  A successful proof must localize in
rapidity differences or glue at finite scale instead of transporting the complete unbounded real
axis through the total collision.

## Coxeter--Cartan matching attack `[RETIRED AS STATED]`

Edge-colouring the complete graph on `n` particle labels gives `O(n)` matchings, but it does not
give `O(n)` constant-cost analytic layers.  The attempted scheme was

```text
collision-normalized local frames
  -> simultaneous Cartan split on each commuting matching
  -> Coxeter braid correction between consecutive matchings
  -> uniformly conditioned global frame.                           (13)
```

Four exact gaps invalidate that inference:

1. a label transposition `(i,j)` has adjacent Coxeter length `2(j-i)-1`, so arbitrary matching
   edges are conjugated braid words rather than elementary two-leg gates;
2. disjoint transpositions satisfy shifted-basepoint coherence
   `A^t(z)A^s(z_t)=A^s(z)A^t(z_s)`, not ordinary pointwise commutation;
3. errors of the `O(n)` gates in one matching can add in operator norm, so scalar parallel depth
   gives no constant layer condition number;
4. networks using nonadjacent comparators hide exactly the adjacent word length and shifted
   evaluations that the cocycle must control.

The exact route kill and its parent-theory audit are recorded in
`../5-failed/naive-matching-layer-coxeter-cartan-trivialization.md`.  Maillet--Sanchez de Santos
factorizing `F`-matrices impose precisely the missing partial-`F` cross-layer equations, but their
standard frames are singular at spectral collisions.  The positive successor is a
**collision-regular relative factorizing `F`-matrix for `(S,S(0))`** with the shifted coherence and
`exp(O(n))` bounds.  Its first serious test is the full `n=3` `O(N)` Brauer basis with genuine
three-body coefficients; a pure pairwise half-factor is already ruled out.

## Hypertranscendental physics payoff

Proving `(2)` constructs the missing compact-local `O(N)` net in the identity-zero convention.
Regular scalar HT CDD dressing is neutral for `(2)`, so the theorem would immediately admit
nonabelian local QFTs with a physically measurable HT scattering delay and relative modular
carrier.  It would not yet create projective HT mixing, because the undressed `O(N)` projective
ratios are DA.  Its larger value is to supply the locality mechanism that any future intrinsically
mixing projective-HT Yang--Baxter family must clear.

## Anti-theatre and novelty gates

1. **The conjecture called new.**  Rejected.  It is the published `O(N)` intertwiner conjecture in
   a controlled-descent formulation.
2. **The Oka theorem cited as evidence for `(2)`.**  Rejected.  It proves only fixed-`n`
   qualitative existence.
3. **The controlled continuous frame `(9f)` called the solution.**  Rejected.  Hardy
   multiplication requires a bounded holomorphic frame; compact-open Oka approximation is not a
   global supremum estimate.
4. **Generic corona language called a reduction theorem.**  Rejected.  The exact equivariant
   matrix-completion equivalence and constants must be proved.
5. **The radial contraction called quantitative Oka.**  Rejected by the exact `1/t` loss `(12)`.
6. **The edge-colouring schedule called a proof.**  Rejected and retired as stated.  Matching
   depth omits adjacent Coxeter length, shifted partial-`F` coherence, and within-layer norm
   accumulation.
7. **Generic Jackson smoothing called the seed.**  Rejected by the `exp(O(n^2))` dimension loss
   above.  Only the special Coxeter Jackson lemma `(9o)` remains viable.
8. **Product-domain sup-norm `dbar` called a proof.**  Rejected.  Its norm scale is compatible,
   but no centrally small defect with the required rapidity-end decay has been constructed.
9. **Collision jets or connected cumulants called the obstruction theory.**  Rejected.  The
   first jet is a standard braid-fan hinge spline and higher connected expansions have established
   linked-cluster and conormal parents.  Local total-collision data do not control translated
   strata or rapidity infinity.
10. **The optimized exponential constant renamed an entropy.**  Rejected.  Minimizing the
    product of the tube norm and central inverse norm merely repackages Definition 5.2.  It becomes
    new mathematics only after a non-tautological lower-bound formula, a cross-particle assembly
    law, or a necessity theorem for locality.

The possible new contribution is the collision-regular relative factorizing `F`-matrix, not the
published intertwiner conjecture or its physical significance.  Factorizing `F`-matrices and their
partial coherence equations are parent theory.  Focused searches found no collision-regular
relative `O(N)`/Brauer construction with analytic Hardy bounds.  This is negative search evidence
only; novelty and significance remain uncleared until the `n=3` Brauer test produces a genuine
three-body correction and a scalable estimate.

## Primary literature

- S. Alazzawi and G. Lechner, *Inverse Scattering and Locality in Integrable Quantum Field
  Theories*, <https://arxiv.org/abs/1608.02359>.
- P. Heinzner and F. Kutzschebauch, *An equivariant version of Grauert's Oka principle*,
  <https://eudml.org/doc/144259>.
- B. Berndtsson and J.-P. Rosay, *Quasi-isometric vector bundles and bounded factorization of
  holomorphic matrices*, <https://doi.org/10.5802/aif.1964>.
- J. Leiterer, *Splitting of Holomorphic Cocycles with Estimates. Several Variables*,
  <https://doi.org/10.1090/conm/550/10869>.
- S. Treil and B. D. Wick, *Analytic projections, corona problem and geometry of holomorphic
  vector bundles*, <https://arxiv.org/abs/math/0702756>.
- S. Treil and B. D. Wick, *The Matrix-Valued `H^p` Corona Problem in the Disk and Polydisk*,
  <https://arxiv.org/abs/math/0409494>.
- S.-Y. Li, *Solving Kerzman's Problem on the Sup-Norm Estimate for `dbar` on Product Domains*,
  <https://doi.org/10.1090/tran/9208>.
- M. I. Ganzburg, *The theorems of Jackson and Bernstein in `R^m`*,
  <https://doi.org/10.1070/RM1979v034n01ABEH002878>.
- D. J. Newman and H. S. Shapiro, *Jackson's theorems in higher dimensions*, in *On
  Approximation Theory* (1964), pp. 208--219.
- A. Sasane, *Banach Algebras of Symmetric Functions on the Polydisc*,
  <https://arxiv.org/abs/2201.00183>.
- J. M. Maillet and J. Sanchez de Santos, *Drinfel'd Twists and Algebraic Bethe Ansatz*,
  <https://arxiv.org/abs/q-alg/9612012>.
- A. Postnikov, *Permutohedra, associahedra, and beyond*,
  <https://arxiv.org/abs/math/0507163>.
- C. Brouder and F. Patras, *Nonlocal, noncommutative diagrammatics and the linked cluster
  theorems*,
  <https://arxiv.org/abs/1103.2849>.
- M. Norledge and A. Ocneanu, *Hopf monoids, permutohedral cones, and generalized retarded
  functions*, <https://arxiv.org/abs/1911.11736>.
- R. Fernandez and A. Procacci, *Cluster expansion for abstract polymer models*,
  <https://arxiv.org/abs/math-ph/0605041>.

## Lean boundary

No Lean edit or build is justified.  The missing theorem is a several-variable bounded
holomorphic factorization with uniform operator estimates.  The existing `HTGeometry` bounded
gauge API records the correct conceptual distinction but cannot express the analytic tube,
Cartan splitting, or Hardy multiplier norm.  Formalizing edge colouring or the estimate `(4)`
alone would not formalize the load-bearing theorem.

## Gates

- [x] corpus-first audit
- [x] SOTA parent-theory audit
- [x] fixed-particle ordinary holomorphic obstruction killed
- [x] upper cocycle scale reduced to `exp(O(n))`
- [x] canonical regular-representation frame is globally `exp(O(n))`-conditioned and
  central-isometric
- [x] continuous exact square frame is globally `exp(O(n))`-conditioned and central-unitary
- [x] Reynolds averaging failure isolated to invertibility/conditioning
- [x] naive radial contraction killed by non-integrable `1/t` loss
- [x] pure pair-word lift killed at three particles
- [x] naive matching-layer implication retired
- [x] local collision-jet/cumulant route reduced to standard parent theory and rejected as a
  global Hardy argument
- [ ] collision-regular relative partial-`F` equations solved for `O(N)`, `n=3`
- [ ] coherent relative factorizing `F`-matrix with `exp(O(n))` control
- [ ] uniform control on every translated collision stratum and at rapidity infinity
- [ ] uniform lower singular-value bound
- [ ] Alazzawi--Lechner intertwiner property for `O(N)`
- [ ] modular nuclearity and compact-local `O(N)` net
