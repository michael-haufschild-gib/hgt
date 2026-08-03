# Stokes--Cartan contact-complexity tomography

## Metadata

- **Status:** Stage 2 -- dependency-closed paper proof complete; manuscript integration in progress
- **Area:** irregular nonabelian Hodge theory; Stokes geometry; Eggers--Wall trees
- **Created:** 2026-08-03
- **Primary object:** ramification-decorated core nonabelian Hodge diagram of a type-A irregular class at infinity
- **Novelty posture:** contact-complexity formula is a bridge between known results; strict skeleton tomography and metric consequences are candidate new results

## 1. Primitive and law

Let
\[
 \Theta=\sum_{i\in N}n_i I_i
\]
be a finite irregular class at infinity, with pairwise distinct Stokes circles and
ramification orders `r_i`.  Put
\[
 K_{ij}:=
 \begin{cases}
  1+B_{ij}/(r_ir_j),&i\ne j,\\
  1+(B_{ii}-1)/r_i^2,&i=j.
 \end{cases}
\]

For a common truncation branch, let `e` be raw Puiseux exponent height and let
`R(e)` be the least common denominator of mandatory exponents strictly above
`e`.  Thus `R` is the ramification-index function on the branch.  Choose any
integer `eta` above every relevant exponent and define the contact coordinate
\[
 \kappa(v):=\eta-\int_{e(v)}^\eta \frac{du}{R(u)}.
\]
The value is independent of the choice of sufficiently large `eta`.

`[BRIDGE; PROVED IN SOURCE FORMULAS]` **Complementary contact-complexity law.**  After replacing
the metrised fission tree by its common-truncation/contact skeleton (branches glue
at their fission exponents),
\[
                     K_{ij}=\kappa(i\wedge j).                 \tag{CC}
\]
For `i=j`, the meet is the height-zero endpoint of the `i`th branch.  Equivalently,
if `lambda_0>...>lambda_t>f` are the mandatory exponents of the common part and
`D_a=lcm(den(lambda_0),...,den(lambda_a))`, then
\[
 K_{ij}=\lambda_0(1-D_0^{-1})+
 \sum_{a=1}^t\lambda_a(D_{a-1}^{-1}-D_a^{-1})+fD_t^{-1}.
\]
The diagonal has `f=0` and terminal denominator `r_i`.

This is the proposed universal law.  It is not itself claimed as new: it is the
telescoped form of Doucot's rescaled loop/edge formula.  With the usual
Eggers--Wall orientation `e_EW=eta-e`, the integral is the standard contact
complexity `c_EW`, while `kappa=eta-c_EW` is its affine complement.  Calling
`kappa` itself the standard Eggers--Wall coordinate would reverse the typed
orientation and is deliberately avoided below.

## 2. Exact new conjectures

`[PROVED HERE U1 -- STRICT TOMOGRAPHY]` If two pairwise meets are nested strictly
in the common-truncation skeleton, their contact coordinates are strictly ordered.
Consequently, for pairwise distinct leaves,
\[
  (ij\mid k)\quad\Longleftrightarrow\quad
  K_{ij}<K_{ik}=K_{jk}.                                      \tag{RT}
\]
Thus the hierarchy of equality classes of `K` reconstructs, functorially, the
labelled rooted multi-leaf branching skeleton of the fission tree after suppressing
unary vertices and forgetting mandatory/inconsequential/empty decorations.

`[PROVED HERE U2 -- FIBRE LOCALISATION]` Fix `(B,r)`.  Every fission tree in its
decorated fibre has the same labelled rooted branching skeleton.  All ambiguity is
confined to raw rational heights, ramification-index profiles, vertex types, and
sibling decorations on that fixed skeleton.  In particular, no two different
labelled branching hierarchies can be graph twins after ramification decoration.

`[PROVED HERE U3 -- STOKES ENERGY TREE]` Define
\[
 d_{ii}=0,\qquad
 d_{ij}=2K_{ij}-K_{ii}-K_{jj}
 =\frac{2B_{ij}}{r_ir_j}-\frac{B_{ii}-1}{r_i^2}
  -\frac{B_{jj}-1}{r_j^2}.
\]
Then `d` is the path metric on the contact-coordinate tree reconstructed in U1.
In particular it is an additive tree metric and is of strict negative type:
\[
 \sum_{i,j}x_ix_jd_{ij}<0
 \quad\text{for every nonzero }x\text{ with }\sum_i x_i=0.
\]

`[OPEN CORE]` Determine whether U2 admits a canonical recursive product/decomposition
theorem for the full finite fibre.  U1--U3 no longer depend on this stronger question.

## 3. Why all previous findings are shadows

| Previous result | Shadow of (CC) |
|---|---|
| Airy-tower loop sign law | diagonal endpoint crosses critical contact value `K_ii=1-1/r_i^2` |
| Airy towers classified by divisor chains | possible step functions `R(e)` at critical contact integral are subgroup-index chains |
| Ordered multiplicative factorizations | jumps of `R` are successive cyclic stabiliser indices |
| Leading-separated core formula | common branch has no mandatory jump, so (CC) is one affine contact segment |
| Elementary pair spectra | allowed branch-meet contact values are quantised by cyclic sibling separation |
| Rescaled ultrametricity | cophenetic matrices of rooted trees are ultrametric |
| Fixed-decoration finite fibre | inverse contact problem has finitely many rational index profiles |
| Elementary recognition | local contact spectra plus global cophenetic consistency |

## 4. Risky consequences and falsifiers

1. **Topology recovery.** Produce two realised irregular classes with the same `(B,r)`
   but nonisomorphic labelled branching skeletons.  One example kills U1 and U2.
2. **Strict nested order.** Find a triple with strictly nested fission meets but
   `K_ij=K_ik`.  This kills the claimed tomography even though weak ultrametricity survives.
3. **Energy metric.** Find a realised decorated diagram for which `d_ij<=0` for
   distinct vertices or a four-point tree-metric identity fails.  This kills U3.
4. **Rediscovery.** Find a primary source proving that ramification-decorated twisted
   diagrams reconstruct the branching skeleton, or explicitly identifying the above
   `d` as the fission-tree path metric.  Then reclassify U1--U3 as rediscovered.
5. **Wrong quotient.** Check carefully the shift from a fission vertex at
   `succ(f_ij)` to the contact gluing height `f_ij`.  Confusing these two trees is a
   fatal typed-object error.

## 5. Prior-art boundary

- Doucot, *Diagrams and irregular connections on the Riemann sphere*, defines
  `B=Irr(Hom)-rr^T+I` and proves the sheet-slope sum for `Irr(Hom)`.
- Boalch--Doucot--Rembado, *Twisted local wild mapping class groups*, classifies
  admissible deformation classes by fission trees, proves realisation, and proves
  fission data completeness.
- Doucot, *New nonabelian Hodge graphs from twisted irregular connections*, proves
  weak rescaled ultrametric and diagonal inequalities and notes the Eggers--Wall/Płoski
  analogy.  Its proof gives the non-strict comparison that U1 must sharpen.
- Garcia Barroso--Gonzalez Perez--Popescu-Pampu, *The valuative tree is the
  projective limit of Eggers--Wall trees*, defines contact complexity
  `c=int de/i`, proves the tripod formula, and proves inversion.  Therefore the
  integral coordinate is standard singularity theory, not a novelty claim; the
  Stokes coordinate here is its affine complement because pole height has the
  opposite orientation.
- Boalch, *Counting the fission trees and nonabelian Hodge graphs*, gives a bijection
  between untwisted fission trees and fission graphs.  U1 concerns the ramified/twisted
  decorated setting and only the multi-leaf branching skeleton.
- The existing Airy-tower manuscript proves a general decorated finite-fibre theorem
  and exact elementary recognition, but does not state skeleton recovery or the
  contact-coordinate/path-metric law.

## 6. Proof route

1. Rewrite each pair formula by summation by parts as
   `K_ij=eta-int_(f_ij)^eta du/R_ij(u)`.
2. Build the common-truncation skeleton directly from fission data, gluing at
   `f_ij`, and prove `R` is well defined on shared arcs.
3. Since `R` is a finite positive integer, `d kappa/de=1/R>0` on every open arc.
   Deduce strict preservation of nested meets and (RT).
4. Apply the rooted-triple reconstruction theorem, or prove its finite hierarchy
   version directly, to identify the canonical dendrogram of `K` with the branching
   skeleton.
5. For leaves at contact heights `K_ii`, the unique tree path has length
   `2K_ij-K_ii-K_jj`.  Prove positivity and four-point/additivity.
6. Decompose a tree path metric into positive edge-cut metrics to prove strict
   negative type unconditionally.
7. Audit whether equality/zero-length pendant arcs can identify distinct leaves;
   use distinctness of Stokes circles and the positive fission interval to exclude it.

## 7. Stage gates

- [x] Exact conjectures stated
- [x] Known bridge separated from novelty claim
- [x] Falsifiers stated
- [x] Paper proof of U1
- [x] Paper proof of U2
- [x] Paper proof of U3
- [x] External novelty audit complete
- [x] Move to Stage 2
- [ ] Lean theorem surface frozen

## 8. Dependency-closed paper proof

### 8.1 Pair formula as a contact integral

Fix two distinct circles `I_i,I_j`.  Write the levels of their common part as
\[
 \lambda_0>\lambda_1>\cdots>\lambda_t>f_{ij}
\]
(the list may be empty), and put
\[
 D_a=\operatorname{lcm}(\operatorname{den}\lambda_0,\ldots,
                         \operatorname{den}\lambda_a),\qquad D_{-1}=1.
\]
Choose an integer `eta>lambda_0`.  Along the common branch set `R(u)=1` on
`(lambda_0,eta)`, `R(u)=D_a` on `(lambda_(a+1),lambda_a)`, and
`R(u)=D_t` on `(f_ij,lambda_t)`.  Directly,
\[
\begin{aligned}
 \eta-\int_{f_{ij}}^\eta\frac{du}{R(u)}
 &=\lambda_0-\frac{\lambda_0-\lambda_1}{D_0}-\cdots
   -\frac{\lambda_t-f_{ij}}{D_t}\\
 &=\lambda_0(1-D_0^{-1})+
   \sum_{a=1}^t\lambda_a(D_{a-1}^{-1}-D_a^{-1})
   +f_{ij}D_t^{-1}.
\end{aligned}
\]
By the established rescaled edge formula, this is `K_ij`.  If the common
level list is empty, `R=1` and both sides are `f_ij`.

For the diagonal, use all levels of `I_i`, terminal denominator `r_i`, and
terminal height zero.  The same calculation and the established rescaled loop
formula give
\[
 K_{ii}=\eta-\int_0^\eta\frac{du}{R_i(u)}.
\]
This proves (CC), including its independence of `eta`.

### 8.2 Strict diagonal--edge separation

`[PROVED HERE]` **Lemma 8.1.**  For distinct circles `I_i,I_j`,
\[
                       K_{ii}<K_{ij},\qquad K_{jj}<K_{ij}.       \tag{8.1}
\]

**Proof.**  Distinct Stokes circles have `f_ij>0`.  Above `f_ij`, the
ramification-index profile of `I_i` agrees with the profile on the common
branch.  Hence the two integral formulae give
\[
 K_{ij}-K_{ii}=\int_0^{f_{ij}}\frac{du}{R_i(u)}>0.
\]
The same argument with `j` proves the second inequality.  Equivalently, one may
subtract the two finite sums: the tail weights have total `1/D_t`, every tail
height is at most `f_ij`, and the terminal height zero has positive weight
`1/r_i`; the inequality is therefore strict. `QED`

In diagram coordinates, Lemma 8.1 is the pair of strict arithmetic obstructions
\[
 r_iB_{ij}>r_j(B_{ii}-1),\qquad
 r_jB_{ij}>r_i(B_{jj}-1).                                    \tag{8.2}
\]
Since both sides are integers, each left side is at least the corresponding
right side plus one.

### 8.3 Strict separation of nested meets

`[PROVED HERE]` **Lemma 8.2.**  Let `i,j,k` be distinct leaves.  If the
common-truncation meet of `i,j` is strictly below the common meet of `i,k` and
`j,k`, then
\[
                       K_{ij}<K_{ik}=K_{jk}.                    \tag{8.3}
\]
If all three pairwise meets coincide, all three `K`-values coincide.

**Proof.**  Pairs whose leaves lie in different children of the same branch
vertex have the same common levels and the same fission exponent, hence the
same pair formula.  This proves each equality.

For strictness, let the higher/common pair formula have prefix levels
`lambda_0>...>lambda_t` and fission exponent `f`.  The lower meet adds possible
common levels `lambda_(t+1)>...>lambda_u` at heights at most `f` and ends at a
strictly smaller fission exponent `g<f`.  If `D_a` is the cumulative denominator,
then, after cancelling the common prefix, the higher value contributes `f/D_t`,
whereas the lower value contributes
\[
 \sum_{a=t+1}^u\lambda_a(D_{a-1}^{-1}-D_a^{-1})+gD_u^{-1}.
\]
The coefficients are nonnegative and sum to `1/D_t`.  Every sampled height is
at most `f`, while the final coefficient `1/D_u` is positive and samples the
strictly smaller value `g`.  The latter convex combination is therefore strictly
less than `f/D_t`. `QED`

### 8.4 Tomography

Let `S(Theta)` be the labelled rooted tree obtained from the common-truncation
tree by suppressing unary vertices and forgetting whether a retained vertex is
mandatory, inconsequential, or empty.  For an internal vertex `v`, choose leaves
in two different children and set `kappa(v)=K_ij`.  Lemma 8.2 shows this is
well-defined.  Set `kappa(i)=K_ii` at a leaf.

`[PROVED HERE]` **Theorem 8.3 (strict contact tomography).**  The function
`kappa` is strictly increasing from every leaf towards the root.  For distinct
leaves,
\[
                         K_{ij}=\kappa(i\wedge j).
\]
The matrix `K`, and therefore `(B,r)`, uniquely reconstructs `S(Theta)` as a
labelled rooted tree.

**Proof.**  Strictness on leaf edges is Lemma 8.1 and strictness between nested
branch vertices is Lemma 8.2.  The meet formula holds by construction.

For a direct reconstruction, list the distinct off-diagonal values of `K`.  For
each such value `a`, define
\[
                       i\sim_a j\quad\Longleftrightarrow\quad K_{ij}\le a,
\]
with reflexive diagonal understood.  Lemma 8.2 (or the usual strong triangle
argument) makes `sim_a` an equivalence relation.  As `a` increases, its classes
form a nested hierarchy.  Make these classes the internal nodes, attach each
class to the least strictly larger class containing it, and attach singleton
leaves at the bottom.  Strictness ensures that every branching cluster of
`S(Theta)` occurs at its own value along each root path; conversely every
non-singleton class is the descendant set of a branch vertex.  This constructs a
label-preserving isomorphism with `S(Theta)`. `QED`

`[PROVED HERE]` **Corollary 8.4 (fibre localisation).**  Any two fission trees
with the same decorated diagram `(B,r)` have isomorphic labelled rooted branching
skeletons.  Thus graph twins in a decorated fibre may differ only in the data
forgotten by `S`: rational exponent heights, unary vertices, ramification-index
profiles, and mandatory/inconsequential/empty sibling decorations on the fixed
skeleton. `QED`

### 8.5 The Stokes energy metric

`[PROVED HERE]` **Theorem 8.5 (energy-tree law).**  Define
\[
 d_{ii}=0,\qquad d_{ij}=2K_{ij}-K_{ii}-K_{jj}\quad(i\ne j).
\]
Then `d` is the path metric of the rooted tree `S(Theta)` when each edge is
assigned its positive contact-coordinate length.  Hence:

1. `d` is a positive additive tree metric;
2. among the three four-point sums
   \[
    d_{ij}+d_{kl},\quad d_{ik}+d_{jl},\quad d_{il}+d_{jk},
   \]
   the two largest are equal;
3. `d` has strict negative type;
4. there is an explicit Hilbert embedding with squared distance `d`.

**Proof.**  Give an edge from child `v` to parent `p(v)` length
`kappa(p(v))-kappa(v)`.  Theorem 8.3 makes every length positive.  The path from
`i` to `j` rises from `K_ii` to `K_ij` and descends to `K_jj`, so its length is
exactly `d_ij`.  This proves (1); the standard edge cancellation in a tree proves
the four-point identity in (2).

For completeness, cut the leaf set at every edge `e`, choose either side `A_e`,
and let `ell_e>0` be its length.  Then
\[
 d_{ij}=\sum_e\ell_e
 \left|\mathbf1_{A_e}(i)-\mathbf1_{A_e}(j)\right|.
\]
If `x` is nonzero and `sum_i x_i=0`, then
\[
 \sum_{i,j}x_ix_jd_{ij}
 =-2\sum_e\ell_e\left(\sum_{i\in A_e}x_i\right)^2<0.
\]
Indeed, equality would force the sum on every pendant cut `{i}` to vanish, so
all `x_i=0`, a contradiction.  This proves (3).  Finally set
\[
 \Phi(i)_e=\sqrt{\ell_e}\,\mathbf1_{A_e}(i).
\]
Then `||Phi(i)-Phi(j)||^2=d_ij`, proving (4). `QED`

In original diagram coordinates,
\[
 d_{ij}=\frac{2B_{ij}}{r_ir_j}
 -\frac{B_{ii}-1}{r_i^2}
 -\frac{B_{jj}-1}{r_j^2}.                                   \tag{8.4}
\]

### 8.6 Status of the open core

U1, U2, and U3 are proved.  No plane-curve existence theorem is used: only the
established type-A fission data and exact loop/edge formulae enter.  The remaining
research question is stronger than the theorem surface needed here: whether the
finite decorated fibre admits a canonical recursive product formula over the
recovered skeleton.
