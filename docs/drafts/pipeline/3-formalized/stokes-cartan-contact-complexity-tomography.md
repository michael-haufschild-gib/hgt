# Stokes--Cartan contact-complexity tomography

## Metadata

- **Status:** Stage 3 -- dependency-closed paper proof complete; Lean surface closed unconditionally
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
- [x] Lean theorem surface frozen

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

## 9. Lean certificate

All modules live in `formal/GaloisForLFunctions/HTGeometry/` and are wired into
`GaloisForLFunctions/HTGeometry.lean`.

### 9.1 Skeleton, tomography and energy (U1, U2, U3)

| Paper object | Lean declaration | Module |
|---|---|---|
| rooted contact skeleton with strictly antitone `kappa` | `IrregularStokes.RootedContactTree` | `StokesContactTomography` |
| `K_ij = kappa(i ∧ j)` | `RootedContactTree.contact` | `StokesContactTomography` |
| Lemma 8.1 strict diagonal separation | `RootedContactTree.contact_diagonal_lt` | `StokesContactTomography` |
| Lemma 8.2 acute-isosceles / repeated maximum | `RootedContactTree.contact_acute`, `RootedContactTree.contact_maxTwice` | `StokesContactTomography` |
| (RT) rooted-triple law | `RootedContactTree.rootedTriple_iff`, `.contact_lt_of_inf_lt_inf`, `.contact_eq_of_inf_lt_inf` | `StokesRootedTripleLaw` |
| Theorem 8.3 threshold recovery of the labelled hierarchy | `RootedContactTree.hierarchy_eq_visibleHierarchy`, `.clusters_laminar`, `.hierarchy_eq_of_contact_eq` | `StokesContactTomography` |
| (8.2) strict integral obstruction on `(B,r)` | `DecoratedStokesCore.strictDiagonal_iff`, `RootedRealization.strictCoreObstruction` | `StokesDecoratedCore` |
| Corollary 8.4 fibre localisation | `DecoratedStokesCore.RootedRealization.hierarchy_unique`, `CertifiedFissionDatum.hierarchy_unique` | `StokesDecoratedCore`, `StokesUniversalContactLaw` |
| Theorem 8.5(1) additive tree metric | `RootedContactTree.energy_pos_of_ne`, `.energy_eq_zero_iff`, `.energy_triangle` | `StokesRootedCutConstruction` |
| **Theorem 8.5(1) as a path metric**: `d_ij` is the root-path length through the meet, with positive edge lengths | `RootedContactTree.energy_eq_pathLoss`, `.vertexLength_pos` | `StokesRootedCutConstruction` |
| **§8.5 displayed cut decomposition**: `d_ij = Σ_e ℓ_e \|1_{A_e}(i) - 1_{A_e}(j)\|` | `RootedCutContact.energy_eq_absDist`, `RootedContactTree.energy_eq_canonicalCut_absSum`, `RootedCutContact.side_eq_zero_or_one` | `StokesEnergyTree`, `StokesRootedCutConstruction` |
| **§8.5 displayed negative-type identity**: `Σ x_i x_j d_ij = -2 Σ_e ℓ_e (Σ_{i∈A_e} x_i)²` on the zero-sum hyperplane | `RootedContactTree.energy_qform_eq_neg_cut_squares` (tree), `CutFamily.qform_eq_negative_edge_squares` (abstract) | `StokesRootedCutConstruction`, `StokesEnergyTree` |
| Theorem 8.5(2) four-point law | `RootedContactTree.energy_fourPoint`, `CertifiedFissionDatum.core_energy_fourPoint` | `StokesContactTomography`, `StokesUniversalContactLaw` |
| Theorem 8.5(3) strict negative type | `RootedContactTree.energy_strict_negative_type`, `PositivePendantCutFamily.strict_negative_type` | `StokesRootedCutConstruction`, `StokesEnergyTree` |
| Theorem 8.5(4) explicit Hilbert embedding | `RootedContactTree.energy_has_canonical_sqEmbedding` | `StokesRootedCutConstruction` |
| (8.4) energy in diagram coordinates | `DecoratedStokesCore.energy_eq_diagram` | `StokesRootedTripleLaw` |
| master law | `CertifiedFissionDatum.universal_contact_master_law` | `StokesUniversalContactLaw` |
| §8.1 contact integral and its `eta`-independence | `ContactTower.contact_eq_top_sub_analyticLoss`, `etaAnalyticContact_independent` | `StokesContactIntegral` |

### 9.2 Realization: the surface is not vacuous

The tomography layer had been stated for a supplied `RootedRealization`.  That input is now
constructed from the contact matrix itself, so no realization is ever assumed.

| Statement | Lean declaration | Module |
|---|---|---|
| contact balls, their laminarity and centre-freeness | `ContactMatrix.ball_eq_ball_of_le`, `.set_subset_or_subset` | `StokesContactRealization` |
| skeleton vertices, reverse-inclusion order, meet, root, parent | `ContactMatrix.Vtx` with its `SemilatticeInf`, `OrderBot`, `PredOrder`, `IsPredArchimedean` instances | `StokesContactRealization` |
| contact diameter is a strictly antitone height | `ContactMatrix.kappaV_eq_rad`, `.kappaV_strictAnti` | `StokesContactRealization` |
| **acute matrix ⇒ rooted skeleton with that exact contact matrix** | `ContactMatrix.exists_realization`, `.realization_contact` | `StokesContactRealization` |
| **exact realizability criterion for decorated cores** | `DecoratedStokesCore.nonempty_rootedRealization_iff` | `StokesContactRealization` |
| integral contact hierarchies are realizable | `IntegerContactHierarchy.nonempty_rootedRealization`, `.certifiedDatum` | `StokesFissionRealizationExistence` |
| two-level partition hierarchies | `twoLevelHierarchy` | `StokesFissionRealizationExistence` |
| **certified fission data exist for every label set with `1 < n`** | `nonempty_certifiedFissionDatum` | `StokesFissionRealizationExistence` |
| **unconditional master law with an existence witness** | `exists_certifiedFissionDatum_master_law` |
| the reconstructed skeleton's energy, read off the matrix | `ContactMatrix.realization_energy` |
| **U3 stated on the contact matrix itself** | `ContactMatrix.energy_tree_law` |
| **U1 `(RT)` stated on the contact matrix itself** | `ContactMatrix.rootedTriple_iff` |
| **the reconstruction is unique**: two skeletons with the same contact matrix have the same hierarchy | `ContactMatrix.hierarchy_unique` | `StokesFissionRealizationExistence` |
| **every rooted skeleton is a contact matrix** | `RootedContactTree.toContactMatrix` | `StokesContactRealization` |
| **Theorem 8.3 as a round trip**: a skeleton and the skeleton reconstructed from its own matrix have the same contact matrix and the same hierarchy | `RootedContactTree.realization_contact_eq`, `.hierarchy_realization_eq` | `StokesContactRealization` |

`DecoratedStokesCore.nonempty_rootedRealization_iff` is an equivalence: a decorated core `(B,r)`
carries a rooted fission skeleton exactly when its rescaled contact matrix is acute and its
integral diagonal obstruction `r_j(B_ii-1) < r_i B_ij` is strict.  Both directions are proved,
so U1--U3 hold for precisely the realizable cores and for no others.

All headline declarations report `[propext, Classical.choice, Quot.sound]` under `#print axioms`.
`lake build GaloisForLFunctions.HTGeometry` is green.

- 2026-08-05 — realization layer added; Lean surface closed with no assumed realization; card advanced to Stage 3.

### 9.3 The displayed weighted form of §8.1

`[LEAN-PROVED]` `formal/GaloisForLFunctions/HTGeometry/StokesContactWeightedForm.lean` (wired into
`GaloisForLFunctions/HTGeometry.lean`; axiom-clean).

§8.1 evaluates the contact integral into a single weighted sum

```text
K = λ_0(1 - 1/D_0) + Σ_a λ_a(1/D_{a-1} - 1/D_a) + f/D_t .
```

The Lean surface had the recursive contact and the genuine interval integral; the displayed
weighted form itself is now proved, together with the fact that its coefficients are a probability
vector.

| Card object | Lean declaration |
|---|---|
| terminal height and total ramification of a branch | `ContactTower.terminalHeight`, `.totalRamification`, `.totalRamification_pos` |
| the weighted level sum with reciprocal-ramification weights | `ContactTower.weightedLevelSum`, `.weightedLevelSum_step`, `.weightedLevelSum_leaf` |
| **§8.1 displayed form**: contact is that weighted sum | `ContactTower.weightedLevelSum_eq_mul_contact`, `ContactTower.contact_eq_weightedLevelSum` |
| the same for the genuine path integral | `ContactTower.top_sub_analyticLoss_eq_weightedLevelSum` |
| the weights add to one | `ContactTower.weightTotal`, `.weightTotal_eq` |
| every level weight and the residual weight are positive | `ContactTower.level_weight_pos`, `.residual_weight_pos` |
| **contact is a convex combination**: terminal height ≤ contact ≤ top | `ContactTower.terminalHeight_le_contact`, `.contact_le_top`, `.le_weightedLevelSum`, `.weightedLevelSum_le` |
| **the terminal height carries weight `1/D_t`** | `ContactTower.setTerminal`, `.contact_setTerminal`, `.terminal_weight_pos` |
| contact is strictly increasing in the terminal height | `ContactTower.contact_setTerminal_strictMono` |
| **§8.3 strict convex undercut**: levels below a bound and terminal strictly below it force contact strictly below it | `ContactTower.weightedLevelSum_lt`, `.contact_lt_of_terminalHeight_lt` |
| **§8.2 integral sharpening**: the strict obstruction holds with a `+1` | `DecoratedStokesCore.RootedRealization.strictCoreObstruction_add_one_le` |
| **`(8.2)` as displayed**: *both* strict obstructions, with the same off-diagonal entry | `DecoratedStokesCore.RootedRealization.strictCorePairObstruction`, `.strictCorePairObstruction_add_one_le` |

`contact_setTerminal` is the exact statement behind the §8.2 remark that "the terminal height zero
has positive weight `1/r_i`": contact is affine in the terminal height with slope exactly the
reciprocal of the accumulated ramification, so raising the terminal height strictly raises the
contact.  That is the alternative, purely arithmetic route to Lemma 8.1, independent of the
integral cancellation.


`contact_lt_of_terminalHeight_lt` is the profile-level mechanism of Lemma 8.2 as the card proves it:
after cancelling the common prefix the lower branch distributes weight `1/D_t` over heights at most
`f`, and its final positive weight `1/D_u` samples the strictly smaller `g`, so the convex
combination is strictly below `f/D_t`.  The tree-model form of the same lemma
(`RootedContactTree.contact_lt_of_inf_lt_inf`) was already in place; both routes are now
machine-checked.

The threshold-equivalence step of §8.4 is also owned in the graph and dendrogram encodings
(`ElementaryDecoratedGraph.thresholdSetoid` with `thresholdSetoid_mono`,
`FiniteContactDendrogram.strictThresholdSetoid`); it is now proved for `ContactMatrix` itself in
`StokesContactThreshold` (§9.5), so the card's own reconstruction recipe -- read the matrix at a
threshold -- is machine-checked on the matrix the card names.

- 2026-08-06 — §8.1's displayed weighted form proved, with positivity and total one of its weights,
  the convex bounds it implies, and the exact terminal weight `1/D_t`; §8.3's strict convex
  undercut and §8.2's integral `+1` sharpening added.

### 9.4 The branch continuation of §8.2

`[LEAN-PROVED]` `formal/GaloisForLFunctions/HTGeometry/StokesBranchContinuation.lean` (wired into
`GaloisForLFunctions/HTGeometry.lean`; axiom-clean).

§8.2 proves Lemma 8.1 by an integral identity rather than by the convexity argument: the diagonal
branch is the common branch *continued* below the fission height, and

```text
K_ij - K_ii = ∫_0^{f_ij} du / R_i(u) > 0 .
```

The corpus had the arithmetic route (contact is affine in the terminal height) and the tree-model
inequality; the continuation itself, and this identity, are now proved.

| Card object | Lean declaration |
|---|---|
| continuing a branch below its terminal height | `ContactTower.graft` |
| the continuation keeps the top, moves the terminal height, multiplies ramification | `ContactTower.top_graft`, `.terminalHeight_graft`, `.totalRamification_graft`, `.valid_graft` |
| the loss of a continued branch | `ContactTower.loss_graft` |
| **contact drops by the rescaled loss of the continuation** | `ContactTower.contact_graft` |
| **§8.2 displayed identity**: the drop is the genuine reciprocal-ramification interval integral | `ContactTower.contact_sub_contact_graft_eq_analyticLoss` |
| a branch reaching strictly below its top has positive loss | `ContactTower.loss_pos_of_terminalHeight_lt` |
| **Lemma 8.1, analytic route** | `ContactTower.contact_graft_lt_of_terminalHeight_lt`, `.contact_graft_lt` |
| **the diagonal branch of a pair**: same top, terminal height zero, strictly smaller contact, gap equal to the integral | `ContactTower.diagonal_graft_law` |

- 2026-08-06 — §8.2's own proof mechanism formalized.  Lemma 8.1 was available in the tree model and
  through the convexity of the weighted form; the card derives it from the integral identity
  `K_ij - K_ii = ∫_0^{f_ij} du/R_i(u)`, which needs the notion of a branch continued below its
  terminal height.  Grafting is now defined, its top/terminal-height/ramification laws proved, and
  the contact drop identified with the analytic path integral of the continuation, rescaled by the
  ramification accumulated above it.  Both routes to Lemma 8.1 are therefore machine-checked, and
  the "diagonal has `f=0` and terminal denominator `r_i`" clause of §1 is a proved consequence.

### 9.5 §8.4's threshold reconstruction, on the contact matrix

`[LEAN-PROVED]` `formal/GaloisForLFunctions/HTGeometry/StokesContactThreshold.lean` (wired into
`GaloisForLFunctions/HTGeometry.lean`; axiom-clean).

§8.4 reconstructs the skeleton by reading `K` at a threshold: `i ~_a j` iff `K_ij ≤ a`, with the
diagonal reflexive.  The claims are that this is an equivalence relation, that its classes nest as
`a` grows, and that every nonsingleton class is the descendant set of a branch vertex.

| Card object | Lean declaration |
|---|---|
| the threshold relation `i ~_a j` | `ContactMatrix.ThresholdRel`, `.thresholdSetoid` |
| **the acute inequality makes it transitive** | `ContactMatrix.thresholdRel_trans` |
| threshold classes | `ContactMatrix.thresholdClass`, `.mem_thresholdClass` |
| **classes grow with the threshold** | `ContactMatrix.thresholdClass_mono` |
| classes at one threshold are equal or disjoint | `ContactMatrix.thresholdClass_eq_of_mem`, `.thresholdClass_eq_or_disjoint` |
| **the family across thresholds is laminar** | `ContactMatrix.thresholdClass_laminar` |
| below the diagonal value a label is alone | `ContactMatrix.thresholdClass_eq_singleton` |
| **every nonsingleton class is a cluster** | `ContactMatrix.isCluster_thresholdClass` |
| **every cluster occurs as a threshold class** | `ContactMatrix.thresholdClass_val_eq_ball` |

- 2026-08-06 — §8.4's threshold recipe proved on `ContactMatrix`.  It had been available only in the
  graph and dendrogram encodings; the card states it for the matrix `K`, and that is now the object
  it is proved of.  The nonsingleton classes and the contact balls are the same family in both
  directions, so "make these classes the internal nodes" is the vertex set the realization module
  already uses.

### 9.4a Full audit re-run (2026-08-06, after the day's additions)

Every backticked Lean name in the four cards of this group was resolved against a fresh index of
all corpus declarations, built by parsing every `theorem`/`lemma`/`def`/`abbrev`/`instance`/
`structure`/`inductive`/`class` header (attributes stripped, every partial namespace prefix
generated).  Two stale citations were found and corrected: the Mobius card had prefixed `(6)`'s
coefficient-derivative theorem with `RHTower.` although its module declares no namespace, and this
card had abbreviated `DecoratedStokesCore.RootedRealization.hierarchy_unique`.  Every other
unresolved token is a mathlib name, a module name, a file path, or a prose symbol.

A single `#print axioms` sweep was then run over all 232 names cited in headline table rows across
the four cards.  Every one that is a declaration reports `[propext, Classical.choice, Quot.sound]`;
`ContactTower.setTerminal` reports no axioms at all, being a plain recursion.  The remaining
entries are module names and prose symbols, not declarations.

### 9.4 Cross-card audit (2026-08-06)

Every Lean declaration name cited anywhere in this card was resolved against the corpus by an
automated scan of all `theorem`/`def`/`instance` headers: no name drift, no dangling citation.  The
same scan was run on the other three cards of the eternity/Stokes/Groskin/Möbius group with the
same result — the only unresolved backticked tokens are mathematical prose symbols (`d_ij`, `p_T`,
`ell_E`, …), module names, and one mathlib declaration.

A single `#print axioms` sweep over the headline theorems of all four cards
(`exists_certifiedFissionDatum_master_law`, `ContactTower.contact_eq_weightedLevelSum`,
`exists_isHermitian_commuting_gapRank_uniform_horizon`, `…_orbitDimension_…`, `…_returnExponent_…`,
`…_completedTimeTorus_…`, `norm_trace_densityMatrix_heisenberg_sub_le`,
`RHTower.groskinArchTailIncrement_posSemidef`, `…_mono`, `…_rank_le_two`,
`tendsto_integral_monotoneCoupling_criticalClocks`, `tendsto_criticalPacketEdgeCost`,
`tendsto_criticalEulerEdgeEnergy`, `RHTower.hasDerivAt_completedSuzukiPacket`) reports
`[propext, Classical.choice, Quot.sound]` for every one.
- 2026-08-06 — U3 restated on the contact matrix.  Its clauses were proved of a *supplied* rooted
  tree, whereas the card states U3 for `d` built from `K` (equivalently from `(B,r)`).  Since an
  acute matrix reconstructs its own skeleton, `d_ij = 2K_ij - K_ii - K_jj` is that skeleton's energy,
  so positivity, the vanishing criterion, the triangle inequality, the four-point law, strict
  negative type and the explicit squared-Euclidean embedding all hold of the matrix directly.
- 2026-08-06 — U1 also restated on the contact matrix, together with uniqueness of the
  reconstruction.  U1--U3 are now each available in two forms: on a supplied rooted skeleton, and on
  the matrix `K` (equivalently the decorated core `(B,r)`) that the card actually names.  U2 needed
  no restatement -- `DecoratedStokesCore.RootedRealization.hierarchy_unique` was already stated on `(B,r)`.
- 2026-08-06 — U3(1) stated as the card words it.  The card says `d` *is the path metric* of the
  skeleton with each edge carrying its contact drop; the corpus had positivity, the vanishing
  criterion and the triangle inequality, which are consequences, plus the cut representation.  The
  path identity itself, `d_ij = pathLoss(i) + pathLoss(j) - 2 pathLoss(i ∧ j)`, follows from the
  potential-drop law `pathLoss v = κ(root) - κ(v)`, and `vertexLength_pos` supplies the positivity
  of the edge lengths.
- 2026-08-06 — the displayed cut decomposition of §8.5 proved in the card's own absolute-value form.
  The corpus carried the squared cut distance `Σ ℓ_e (1_A(i) - 1_A(j))²`; since the sides are
  idempotent they take only the values zero and one, so squares and absolute values agree and the
  card's `Σ ℓ_e |1_A(i) - 1_A(j)|` — the total length of the cuts separating the two leaves — is the
  same number.
- 2026-08-06 — the negative-type identity of §8.5 exposed at the tree level.  The abstract cut form
  `qform_eq_negative_edge_squares` was already there and strict negativity was derived from it, but
  the identity itself -- the reason the form is negative -- was not stated for a rooted skeleton's
  energy.  It is now, so §8.5's proof reads in Lean the way the card writes it: identity first,
  strictness as its consequence.
- 2026-08-06 — the two encodings closed into a round trip.  The corpus had matrix → skeleton
  (`exists_realization`) and uniqueness of the hierarchy given the matrix, but never skeleton →
  matrix, so "the matrix `K` uniquely reconstructs `S(Theta)`" was only half stated.  A rooted
  skeleton's own contact function satisfies the three contact-matrix axioms verbatim
  (`contact_symm`, `contact_acute`, `contact_diagonal_lt`), so it *is* a contact matrix; the
  skeleton reconstructed from it has the same contact matrix and hence the same labelled hierarchy.
  Nothing that `S(Theta)` retains is lost in passing to `K`.
- 2026-08-06 — `(8.2)` completed to the pair the card displays.  The corpus proved one obstruction,
  `r_j(B_ii - 1) < r_i B_ij`; the card states both, the second being `r_i(B_jj - 1) < r_j B_ij`
  *with the same off-diagonal entry*.  That is the swapped instance together with the core's own
  symmetry `B_ji = B_ij`, and both now carry the integral `+1` sharpening the card asserts of each.
