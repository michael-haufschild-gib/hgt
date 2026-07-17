# Hypertranscendental rigidification--source-face conservation

- **ID:** `hypertranscendental-source-face-vanishing-cycle-conservation`
- **Stage:** 1-in-progress
- **Type:** FOUNDATIONAL HT CONJECTURE / DEGENERATION AND OBSTRUCTION UNIFIER
- **Scientific status:** `[CONJECTURE] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
  `[SIGNIFICANCE TARGET: FIELDS-SCALE] [NOVELTY PRELIMINARY] [NOT AN RH RESULT]`
- **Exact algebraic seed:**
  `../3-formalized/not_new_scientific_knowledge/elliptic-gamma-source-face-fracture.md`
- **Exact inertia seed:**
  `../3-formalized/not_new_scientific_knowledge/source-rigidification-face-inertia.md`
- **Natural analytic seed:**
  `../2-fully-proven/new_scientific_knowledge/irrational-elliptic-gamma-pointed-bi-anomaly-fracture.md`
- **Obstruction interval parent:**
  `hypertranscendental-normalization-horizon-uniformization.md`

## Discriminator

The problem is to identify what can carry one obstruction through a natural HT degeneration.  Four
candidate objects make different predictions.

1. **Unlabelled period subgroup with Chabauty or derived topology.**  It predicts that degeneration
   deletes or merges periods while the source action remains group-like.
2. **Projective normalization horizon alone.**  It records escaping gauges and singular values but
   does not identify which structural source direction degenerates or how its multiplier
   specializes.
3. **Coefficient cohomology alone.**  It records the DA anomaly at a fixed parameter but has no
   intrinsic specialization map when a source automorphism becomes noninvertible.
4. **One-sided compactified labelled source monoid acting on a stack-valued defect object.**  It
   predicts that a group generator becomes a boundary endomorphism, its vanishing ideal records
   positive lost orbit modes, and the solution stabilizer is retained as inertia.
5. **A two-faced self-dual Tate gauge stack with an independently supplied counterface.**  It
   predicts opposite source lattices at zero and infinity, a residue pairing between opposite
   weights, exact/approximate transversality strata for the residual gauge, and a
   nearby/vanishing-cycle map on their relative-position object rather than on a chosen solution.

Three exact theorems decide among them.  A unit coordinate cannot be scaled by a nonunit under any
endomorphism, while its polynomial compactification specializes to boundary evaluation with
kernel `(X)`.  The elliptic-gamma product simultaneously collapses to its coordinate-deletion
Pochhammer face.  Independently, every reporter obtained by postprocessing the bare source has
exactly the same fibres as that source, while deleting one nonreal translation creates boundary
gauge spaces of arbitrarily large finite rank.  Finally, the negative periodic mode `X^(-1)` is
invisible to every positive normal layer, whereas the zero and infinity Laurent faces jointly
retain only the scalar gauge and inversion exchanges them.  More strongly, every
inversion-invariant condition contained in one face collapses to scalars, so no nontrivial
presentation-invariant rule can select an oriented half.  Candidates 1--3 forget either the source
face or its jumping inertia; candidate 4 retains both but is one-sided and cannot be the full
inertia carrier; candidate 5 is the first survivor of all three discriminators.

## Decisive no-go and strong positive successor

```text
[NO-GO]
No invariant factoring only through the topology of the unlabelled period subgroup can reconstruct
the full labelled, coefficient-bearing HT degeneration, even if orientation and derived topology
are added.
```

The obstruction is categorical, not merely topological: an automorphism on the punctured orbit
does not extend through the singular parameter.  The action loses invertibility, the negative
orbit directions cease to exist, and the multiplier cocycle acquires a boundary value.

```text
[POSITIVE]
The minimal source datum forced by the tested degeneration is the labelled source-monoid face
together with its boundary ideal and coefficient specialization.  For multiple elliptic gamma,
every zero-nome atomic face is canonically the coordinate-deletion lower-rank source.
```

This positive statement is exact at the algebraic and finite-product levels and Lean-formalized.
It is not yet the sought conservation theorem for the HT anomaly.

The reconstruction no-go adds a second exact boundary:

```text
[NO-GO]
If every added reporter factors through the complete bare-source boundary, the augmented
observation has exactly the same fibres as the bare source and is injective exactly when the bare
source was already injective.
```

Its nontrivial positive successor is a theorem, not a metaphor:

```text
[POSITIVE]
For every k and every nonreal deleted shift tau, the surviving unit-shift source acquires a
k-dimensional positive Fourier packet V_k such that V_k intersects the generic tau-fixed gauge
only at zero.  Hence a codimension-one source face can create normalization inertia of unbounded
finite rank.
```

Thus the source-face object must retain not only a class and a boundary ideal but the comparison
between the generic and boundary stabilizers.

## `[CONJECTURE -- RIGIDIFICATION--SPECIALIZATION COMMUTATOR]`

Let `X_T` be the solution stack of a regular source-minimal HT family and let `G_T` be its normalized
joint-fixed inertia.  There are two operations:

```text
Rig: remove the chosen source inertia without choosing a solution;
Sp:  specialize the labelled source action to a compactified source-monoid face.
```

They need not commute.  The canonical comparison between `Sp(Rig(X_eta))` and `Rig(Sp(X)_0)` has a
derived homotopy fibre `C_T`, the **rigidification--specialization commutator**.  On its linear
source-gauge chart it is represented by

```text
C_T^lin = [G_eta -> G_0],                                   (R1)
H^(-1)(C_T^lin)=ker(G_eta -> G_0)       (gauge death),
H^(0)(C_T^lin)=coker(G_eta -> G_0)       (gauge birth).      (R2)
```

The full coefficient-filtered object couples `(R1)` to the source-face vanishing cycle by a
canonical transgression

```text
kappa_T:C_T -> Phi_T(D_T).                                  (R3)
```

It is constrained by four laws.

1. **Endogenous blindness.** Every realization derived solely from the coarse source boundary
   annihilates `C_T`; detecting `(R1)` requires a genuinely transverse channel or retention of the
   stack inertia itself.
2. **Two-faced normal-character conversion.** For a multiplicative source face, the zero-face
   normal layers and infinity-face normal layers map under `(R3)` to opposite born-gauge
   **character lines**.  After choosing an oriented uniformizer the predicted charts are

   ```text
   gr_0^m       <->  line(exp( 2 pi i m z)),   m>=1,          (R4+)
   gr_infty^m   <->  line(exp(-2 pi i m z)),   m>=1.          (R4-)
   ```

   Inversion exchanges `(R4+)` and `(R4-)`.  No canonical vector-level identification is claimed:
   changing the pointing rescales a weight vector.  The canonical target is the graded character
   line and its opposite-weight residue pairing.  Without external orientation even the sign of
   the weight cone is not selectable; only the unordered pair of opposite face lattices is
   canonical.

3. **Conservation.** A generic obstruction may change degree or move from source incidence to
   stabilizer inertia, but it cannot vanish simultaneously from `C_T` and every conservative
   coefficient vanishing cycle.
4. **Presentation invariance.** Replacing a functional-equation presentation by an equivalent
   source presentation gives an equivalent commutator and the same weightwise transgression.

`(R4+)`--`(R4-)` are deliberately stronger than noticing the same integer labels on two bases.
The theorem target is a canonical two-lattice associated-graded duality, compatible with the DA
connecting class and iterated transverse faces.  The original one-sided vector statement is
false: `exp(-2 pi i z)` is a valid source-fixed gauge but corresponds to `X^(-1)`, outside every
positive normal layer, and a change of pointing rescales every nonzero weight vector.  If no
canonical character-line duality and opposite-weight residue pairing exist, the corrected
conjecture is false; an arbitrary chosen pairing is not acceptable.

## `[CONJECTURE -- POLARIZED INERTIA TATE FIELD]`

The bare-source reconstruction theorem changes the domain of the unified theory.  The object
cannot be assigned to a source alone.  It is assigned to a typed pair

```text
(source constraint S, genuinely transverse normalization/reporter R),       (T0)
```

where `R` is not allowed to factor through the boundary data already forgotten by `S`.

For every regular source-minimal pair `(S,R)`, the completed normalized residual gauge carries a
presentation-invariant analytic Tate object `V_(S,R)` with two opposite lattices
`L_S^+` and `L_R^-` and a perfect self-dual seam pairing.  Its fundamental obstruction is the
relative-position field

```text
I_(S,R) = RPos(L_S^+,L_R^-).                                  (T1)
```

The following are different receivers of `(T1)`, not separate obstructions:

```text
exact gauge ambiguity       = L_S^+ intersect L_R^-;
attainment/cokernel defect  = V_(S,R)/(L_S^+ + L_R^-);
spectral incompleteness     = closure(L_S^+ + L_R^-)/(L_S^+ + L_R^-);
positivity failure          = degeneracy/signature of the seam crossing form;
monodromy                   = holonomy of the determinant/normalization line of the pair;
noncanonical boundary       = failure to choose a global opposite lattice;
continuation failure        = failure of the two lattices and their graph domains to extend
                              across a source face.             (T2)
```

The kernel/attainment/strictness part of `(T2)` is now an exact theorem, not conjectural
terminology.  For every linear reporter `A:E -> F`, the horizontal lattice `H=E x {0}` and reporter
graph `Gamma_A` satisfy

```text
H intersect Gamma_A={0}  iff A is injective;
H + Gamma_A=E x range(A);
H + Gamma_A is closed    iff range(A) is closed.              (T2a)
```

Together with the proved approximate-unit-kernel/closed-range equivalence, `(T2a)` shows that
exact gauge ambiguity and spectral incompleteness are literally the intersection and nonclosed-sum
defects of one pair.  This is parent Grassmannian/operator algebra, but it is the first proved
cross-receiver identity demanded by the unified theory.  The HT-new obligation is to construct
`H`, `Gamma_A`, the self-dual seam, and their integral enhancements canonically from `(S,R)`.

On the finite Laurent chart, `(T1)` specializes to the now-proved zero/infinity two-face law and
the already-proved opposite-weight residue seam.  On a family, the support where the pair ceases
to be Fredholm-transverse is the **self-dual degeneracy locus**.  This locus is canonical even
when no canonical solution or complementary lattice exists.

The field-level minimality claim is:

```text
[CONJECTURE]
Every conservative source-pure realization of a regular HT pair factors through I_(S,R), while
every endogenous source-only realization annihilates its residual-inertia summand.              (T3)
```

This is stronger than the common-kernel theorem and stronger than importing a Maslov index.  It
asserts a natural HT-specific Tate completion, identifies its two lattices from independently
typed source and normalization data, and proves that the exact, bornological, positive,
continuation, and monodromy obstruction receivers are conservative images of their relative
position.

**Falsifiers.**  The conjecture fails if a natural source-minimal HT pair has no functorial Tate
completion; if equivalent source presentations produce inequivalent relative-position fields; if
one of the obstruction receivers in `(T2)` changes while `(T1)` does not; or if a source-derived
reporter canonically produces the missing counterlattice despite a nonzero joint-fixed gauge.

## `[CONJECTURE -- CONSTRAINT NEARBY-CYCLE CONSERVATION LAW]`

Let `T` be a regular one-parameter family of source-minimal HT constraints over a punctured disk.
Assume its labelled source action extends over the origin only after compactification to a source
monoid, and let

```text
D_T=(selection inertia -> source incidence -> strict/exterior production defect)              (1)
```

be the coefficient-filtered strict defect interval in the source-forced completion, formed before
rigidifying away `G_T`.

There is a canonical constructible extension of `D_T` to the source-monoid compactification and a
distinguished source-face triangle

```text
i^* D_T  ->  Psi_T(D_T)  ->  Phi_T(D_T)  ->  i^* D_T[1].                                    (2)
```

It satisfies:

1. **source purity:** `(2)` is constructed before any divisor, spectrum, or target zero set;
2. **coefficient compatibility:** it is natural for the DA, holomorphic, positive, integral, and
   ambient meromorphic coefficient channels;
3. **selection--production transgression:** the map `(R3)` identifies the failure of normalized
   selection to commute with specialization; a gauge or primitive class can disappear from the
   generic fibre only by producing born inertia or a nonzero boundary/vanishing-cycle class,
   possibly with a one-degree shift;
4. **conservativity:** every realization functor preserving `(2)` detects the same nonzero
   projective escape profile, although it may display it as a kernel, cokernel, monodromy,
   positivity, continuation, or integrality failure;
5. **no phantom cancellation:** if both the boundary class and vanishing-cycle class vanish in a
   conservative coefficient channel, the generic obstruction extends effectively across the
   face.

The proposed "conservation" is not numerical equality of dimensions.  It is functorial transport
of one class through `(R3)` and the connecting morphisms of `(2)`.

## `[CONJECTURE -- ELLIPTIC-GAMMA DA FACE-RESIDUE THEOREM]`

Let `beta_Gamma` be the pointed DA--holomorphic relative class of the irrational elliptic gamma
cochain.  Under one zero-nome degeneration,

```text
Res_(q=0)(beta_Gamma)=beta_Poch,                            (3)
partial Res_(q=0)(beta_Gamma)=Res_(q=0)(partial beta_Gamma),(4)
```

where `beta_Poch` is the nonzero relative class of the surviving q-Pochhammer/Jackson q-gamma
source.  The generic degree-two gerbe/DA-intersection anomaly transgresses to the degree-one
boundary anomaly, while the standard-wedge DA class specializes to the lower-rank q-difference
class.  Both remain effective only after passage to the ambient meromorphic coefficient theory.

Equations `(3)`--`(4)` are the first decisive theorem target.  They would prove, in one natural HT
family, that obstruction degree can change while the obstruction class is conserved.

## `[CONJECTURE -- ALL-DEPTH SOURCE-FACE RESIDUE TOWER]`

For the order-`r` multiple elliptic-gamma hierarchy, the nome-coordinate face lattice carries a
coefficient-filtered constructible defect object with the following law:

```text
k coordinate nomes specialized to zero
  -> k-fold iterated source-face residue
  -> order-(r-k) pointed HT class, shifted by k in descent height.                           (5)
```

Residues commute for transverse faces, rigidification commutators satisfy the corresponding
Beck--Chevalley interchange law, and their support matroid is the already-proved transverse
constraint matroid.  The characteristic cycle of this stack-valued constructible object is the
proposed presentation-independent carrier of hypertranscendental capacity.

If `(5)` holds, "hypertranscendence is infinite algebraic clock capacity concentrated on a thin
constraint boundary" becomes precise: the infinite differential capacity is not stored in a
time parameter, but in the exchange between boundary-normal characters, born source inertia, and
nonzero coefficient-filtered vanishing cycles of the compactified source constraint.

## Barnes discriminator: face depth is not fracture depth `[PROVED]`

The nonperiodic Barnes family now decides a question which the elliptic-gamma hierarchy alone
cannot decide.  Its exact DA-relative differential-translation module is

```text
M_N=D_N/(x_1...x_N),  x_j=T_j-1.
```

For a selected face `j`, write `p_j=product_(k!=j)x_k`.  On `M_N`, multiplication by `p_j` and
`x_j` forms the exact two-periodic matrix factorization

```text
... -> M_N --p_j-> M_N --x_j-> M_N --p_j-> M_N -> ... .       (B1)
```

More strongly, for every nonempty face set `S` and `B_S=D_N/(x_j:j in S)`, derived restriction is

```text
M_N tensor^L_(D_N) B_S = [B_S --0-> B_S],
Tor_i^(D_N)(M_N,B_S)=B_S for i=0,1 and 0 for i>=2.             (B2)
```

Thus every nonempty Barnes face has the same homological amplitude, whether one or all source
coordinates are specialized.  Relation death and capacity birth are the same boundary module in
adjacent degrees.  At the same time, `B_S` retains the free unbounded `delta` direction.

```text
[NO-GO]
No universal HT law may identify the number of deleted source directions, the length of the
obstruction complex, and the amount of hypertranscendental capacity.

[POSITIVE]
The exact source-face invariant is the derived restriction profile of the DA-relative
characteristic module.  For Barnes it is the canonical two-periodic pair (B_S[-1],B_S), while
capacity is the independent differential prolongation filtration on that pair.
```

This does not refute the family-specific elliptic-gamma residue tower `(5)`.  It refutes its use as
a universal model.  The elliptic-gamma tower must now be proved by computing the multigraded
derived face Betti table of its Stanley--Reisner characteristic module, not inferred from the
number of nomes.  The complete Barnes theorem is recorded in
`../2-fully-proven/new_scientific_knowledge/barnes-differential-source-face-matrix-factorization.md`;
its local exactness is Lean-formalized in `NormalCrossingFaceMatrixFactorization.lean`.

## Tate-theta divisor-to-winding transgression `[PROVED BRIDGE]`

The matrix factorization identifies the algebraic source of the degree `-1` class but not its
regular analytic target.  A direct Tate-theta family supplies the missing rank-two-to-rank-one
local model.

For `0<q<1`, let

```text
theta_q(y)=product_(n>=0)(1-q^n y)(1-q^(n+1)/y)
```

and define

```text
E_q(x)=-q^(1/4)
  theta_q(q^(-1/4)x) theta_q(q^(3/4)x) / theta_q(q^(1/4)x)^2.  (B3)
```

The theta transformation `theta_q(qy)=-y^(-1)theta_q(y)` gives `E_q(qx)=E_q(x)`, so `E_q` is a
meromorphic gauge on the Tate elliptic curve `C^*/q^Z`.  Its divisor in the standard annulus is

```text
2[q^(1/4)]-2[q^(3/4)].                                      (B4)
```

For compact subsets of `C^*`, the product formula gives

```text
q^(1/4)theta_q(q^(-1/4)x) -> -x,
theta_q(q^d x) -> 1 for 0<d<1,
```

locally uniformly.  Hence

```text
E_q(x) -> x.                                                (B5)
```

After dividing by `E_q(1)`, the gauges are pointed at `x=1`.  Taking positive or negative powers
realizes every pointed boundary character `x^m`, `m in Z`.  The oriented node charge of `(B4)` is

```text
chi_node = sum pole valuations - sum zero valuations
         = 2(3/4)-2(1/4)=1,                                (B6)
```

which is exactly the winding exponent of the limit `x`.  Powers give `chi_node=m` and limit
`x^m`.

Therefore the full singular divisor reporter is conservative on the generic elliptic gauge but
loses precisely a regular winding character when the divisor escapes through the node.  The
smallest repaired boundary reporter is

```text
(interior divisor, node charge, pointing),                  (B7)
```

not any postprocessing of the specialized bare source.  On the algebraic finite-character
stratum `(B7)` is injective, while omitting node charge leaves the normalized kernel `x^Z`.

This proves existence, surjectivity onto every weight, and charge conservation in the local
two-face prediction `(R4+)`--`(R4-)`.  It does not yet prove a presentation-independent canonical
character-line duality for an arbitrary HT family.  The theta construction and node-slope law are
classical Tate/generalized-Jacobian parents; the candidate-new task is their functorial coupling to
the HT characteristic module and DA filtration.  The complete bridge proof is recorded in
`../2-fully-proven/not_new_scientific_knowledge/tate-theta-divisor-to-winding-transgression.md`.

## `[CONJECTURE -- DIFFERENTIAL CHARACTERISTIC RESOLUTION FIELD]`

The Barnes theorem forces a more precise candidate for what constrains hypertranscendental
functions.  For a source-minimal HT germ `F`, let `A_S` be its commuting differential-source
operator algebra and form the DA-relative characteristic module

```text
M_F=A_S/Ann_DA^diff(F).                                     (B8)
```

The proposed intrinsic field is not merely the support of `M_F`.  It is the quadruple

```text
CR(F)=(M_F, Rees_delta(M_F), {L i_S^* M_F}_S, K_(S,R)),      (B9)
```

consisting of the characteristic sheaf, its differential prolongation filtration, all derived
source-face restrictions, and the normalized regular common-kernel sheaf for genuinely transverse
reporters.  Equivalent source-minimal presentations are required to give equivalent quadruples.

The four entries have distinct jobs:

```text
support(M_F)                  = thin constraint boundary;
Rees_delta(M_F)               = differential HT capacity;
cohomology(L i_S^* M_F)       = relation death/capacity birth and continuation fracture;
K_(S,R)                       = residual reconstruction inertia.               (B10)
```

`[CONJECTURE]` Every conservative analytic, spectral, positive, monodromic, or integral
realization of a regular source-minimal HT pair factors through a polarized realization of
`CR(F)`, and the connecting maps preserve the same classes, not only their dimensions.  The Tate
node charge `(B6)` is the first explicit regular receiver of a derived singular face class.

This is falsifiable in three immediate ways: presentation dependence of `(B9)`; failure of the
multiple elliptic-gamma face Betti table to match its analytic residue tower; or existence of a
natural obstruction receiver changing while all four entries of `(B9)` remain fixed.  Merely
naming a derived category, matrix factorization, or Rees module does not pass the anti-theatre
gate.  The next theorem must calculate the complete multigraded face resolution for the multiple
elliptic-gamma characteristic ideal and identify its first nonzero analytic connecting class.

## Why this could be Fields-scale

The field-level theorem is not the abstract existence of nearby cycles, which is parent theory,
and not the classical elliptic-gamma degeneration.  It is the construction and classification of
a new natural invariant with all of the following simultaneously:

1. defined for nonlinear source-minimal HT constraints;
2. independent of a chosen presentation by periods or functional equations;
3. constructible across automorphism-to-endomorphism source walls;
4. retains jumping source inertia and computes the rigidification--specialization commutator;
5. identifies the two boundary-normal character-line systems with opposite born inertia through
   a canonical, not chosen, duality and transgression;
6. compatible with differential-algebraic coefficient filtrations;
7. calculable on the complete multiple-gamma hierarchy;
8. conservative across genuinely different analytic, cohomological, spectral, and positive
   realizations.

A proof of `(R1)`--`(R3)`, `(R4+)`--`(R4-)`, `(T0)`--`(T4)`, and `(3)`--`(5)`, followed by a
classification theorem for regular source-minimal HT pairs, would warrant its own paper and could
found the requested unified field theory.  The current source-data-processing, Laurent two-face,
and arbitrary-rank gauge-birth theorems alone do not.

## Novelty gate

Known parent mathematics includes:

1. Felder--Varchenko: elliptic gamma, its difference equations, and trigonometric/rational
   degenerations;
2. Felder--Henriques--Rossi--Zhu: the elliptic-gamma meromorphic cochain and gamma gerbe on the
   universal triptic curve;
3. ordinary nearby and vanishing cycles, mapping cones, toric/logarithmic boundary monoids, and
   Rees constructions;
4. rigidification of algebraic stacks and jumping stabilizers in degenerating quotient problems;
5. parameterized difference Galois criteria for hypertranscendence;
6. the repo's proved elliptic-gamma DA spectrum, transverse constraint matroid, and pointed
   DA--holomorphic bi-anomaly;
7. Tate objects, their Sato Grassmannians, operator ideals, central extensions, and dualities
   (Braunling--Groechenig--Wolfson, arXiv:1402.4969 and arXiv:1508.07880);
8. Fredholm--Lagrangian Grassmannians, Maslov index, and spectral flow (Furutani,
   arXiv:math/0311495);
9. Picard--Vessiot solution torsors and the multiplicative solution-group structure of higher
   Gamma cocycle equations (Maurischat, arXiv:1304.7663; Perez-Marco, arXiv:2101.01291).

Targeted exact searches for `elliptic gamma nearby cycles`, `elliptic gamma vanishing cycles`,
`differential-algebraic elliptic gamma degeneration cohomology`, and
`q-Pochhammer gerbe transgression`, together with searches for `rigidification specialization
inertia` and `nearby cycles quotient stack inertia`, found the parents separately but no HT
rigidification--specialization commutator, no two-faced normal-character/born-gauge duality
`(R4+)`--`(R4-)`, and no coefficient-filtered source-face residue theorem of the form `(3)`--`(5)`.
This is a preliminary novelty pass, not a specialist verdict.

Further exact searches for `hypertranscendental Tate space`, `hypertranscendental Lagrangian gauge
inertia`, `hypertranscendental Maslov`, and `hypertranscendental Fredholm source constraint` found
the parent theories separately but no HT-specific construction of `(T0)`--`(T3)`.  The novelty
candidate is not Tate theory, Maslov theory, solution torsors, Laurent polarization, or Gamma
uniqueness.  It is the functorial assignment of a self-dual two-lattice relative-position field to
source-minimal HT pairs and the proof that the distinct obstruction receivers in `(T2)` are its
conservative images.  This remains `[NOVELTY PRELIMINARY]` pending a specialist audit.

## Anti-theatre gate

1. The unit obstruction, polynomial boundary ideal, and Pochhammer degeneration are parent bridge
   mathematics and are not promoted as discoveries.
2. The source-factorization no-go and finite Fourier gauge packets are parent algebra/analysis and
   are not promoted as discoveries.
3. Writing a standard rigidification or nearby-cycle triangle, Tate object, Lagrangian pair, or
   Maslov cycle is not new mathematics.  The new obligation is to construct the HT-natural
   assignment `(T0)`--`(T3)`, prove `(R4+)`--`(R4-)`, and identify the nonzero classes in
   `(3)`--`(5)`.
4. Equality of dimensions, integer labels, zero sets, or Euler characteristics is insufficient.
   The same character, class, and connecting maps must be identified.
5. No DA anomaly may be inserted as an axiom.  Nontriviality must descend from a proved HT theorem
   or an independently nonzero geometric class.
6. Failure of `(R4+)`--`(R4-)`, `(T3)`, or `(3)` must leave a positive theorem: the exact
   kernel/cokernel or strictness defect of the comparison, the coefficient channel or source face
   in which the class dies, and the resulting maximal conservative subcategory.

## Meaning for the RH-obstruction census

The seven RH terminal obstruction classes are not yet proved to be one object.  This conjecture
gives a falsifiable criterion for that claim.

The relative-position field passes the first **representation** discriminator without claiming to
solve any class:

| Census class | Required receiver of `(T1)` | Anti-theatre proof obligation |
|---|---|---|
| `O1` source sign/orientation | seam crossing form | derive its sign from the source/counterface pair, not from the divisor |
| `O2` critical all-scale estimate | closed-sum versus dense nonclosed-sum phase | prove cofinal Fredholm/strictness control, not another finite collar |
| `O3` spectral/determinant realization | determinant line of the Fredholm pair | construct both lattices and identify the determinant before reading Xi zeros |
| `O4` arithmetic multiplicity | local intersection length and crossing parity | produce the parity/divisibility from an integral source form |
| `O5` non-circular comparison | independence of the counterlattice | prove it does not factor through the bare source or Xi divisor |
| `O6` missing typed bridge | functor into the same Tate category | construct the functor; analogy of spectra or limits is insufficient |
| `O7` algebraicity/rigidity | integral/adelic lattice on the determinant and character lines | derive the lattice from arithmetic coefficients rather than zero coordinates |

This table is not unification by itself.  A successful theory must prove cross-receiver identities:

```text
zero order of determinant section = local intersection length;
crossing-form orientation         = determinant orientation;
zero essential gap                = nonclosed lattice sum;       [PROVED LINEAR CHART]
monodromy charge                  = determinant-line holonomy;
integral valuation                = arithmetic intersection multiplicity.   (T4)
```

If `(T4)` cannot be proved in a natural HT family, `(T1)` is only a vocabulary merger and fails the
anti-theatre gate.

Each RH chain must first construct, from prime--archimedean source data and before reading the Xi
divisor, both the source lattice and a genuinely independent counterlattice, then realize the same
relative-position field `(T1)`, rigidification commutator `(R1)`--`(R3)`, and triangle `(2)`.
Source orientation, critical all-scale failure, spectral incompleteness, multiplicity,
noncircular comparison, missing typed bridges, and arithmetic rigidity are representations of one
obstruction only if their comparison functors preserve the two lattices, generic and boundary
inertia, coefficient channel, cohomological degree, seam pairing, and connecting class.

This makes the practical RH warning sharper.  Any proof chain whose extra positivity, completion,
or spectral data factor only through its already-coarsened source is provably unable to recover the
missing gauge.  Conversely, a boundary degeneration may create a large new stabilizer even when
the generic source was rigid.  A viable chain must therefore exhibit a transverse reporter which
is nonzero on the born-inertia quotient or prove that its source theorem makes that quotient
vanish; merely enriching the same source invariant cannot work.

`[CONJECTURE; NOT AN RH RESULT]` If such a completed-zeta polarized inertia field exists, the
critical zeros are the common support where its source and counterface lattices cease to be
Fredholm-transverse: the self-dual degeneracy spectrum of `(T1)`.  RH would still require a new
source theorem forcing that support onto the fixed locus.  Neither Xi nor its zeros may define
either lattice.

## Where to look next: the Gamma three-realization comparison

The next theorem should not touch RH.  Gamma already supplies three exact but currently separate
views of the same residual gauge:

1. the periodic solution torsor and its zero/infinity Laurent face skeleton;
2. the injective compact factorial reporter with dense nonclosed range;
3. the nonlinear normalization-horizon cones, nontrivial at every finite horizon but jointly
   rigid cofinally.

The first possible identification is now ruled out.  Let
`b_m(n) = (2 pi i m)^(n+1)` be the positive derivative-tail clock of the `m`-th periodic Fourier
mode.  The formalized pure-mode variance-seam theorem proves

```text
b_m lies in the maximal cyclic Gamma-conormal domain for every m;
b_m has an ordinary l2 realization iff m = 0;
the full conormal domain has no coordinate-preserving map into l2,
even without requiring the map to be linear or continuous.                         (G0)
```

Thus the injective compact factorial reporter on `l2` is not yet a reporter on the actual
nonconstant periodic gauge directions.  Its injectivity cannot reconstruct a gauge population
which is absent from its domain.  The positive successor is exact: the maximal conormal domain and
the factorial Hilbert pivot are distinct variance spaces, meeting the pure Fourier spectrum only
in the constant mode.

There is also an exact positive replacement for the rejected pivot.  At radial scale `rho > 0`,
rescale the derivative clock by

```text
b_(m,rho)(n) = (gammaPeriodicFrequency(m) / rho)^(n+1).
```

The formalized variance-horizon theorem now proves the stronger law for every finite packet in the
current nonnegative-frequency chart

```text
b_(m,rho) is in l2  iff  norm(gammaPeriodicFrequency(m)) < rho;
sum_m a_m b_(m,rho) is in l2
  iff every active m has norm(gammaPeriodicFrequency(m)) < rho;
distinct unstable modes cannot cancel across the entry wall;
every packet in this one-sided finite chart enters some finite radial pivot;
crossing an actual frequency strictly enlarges the coefficient space.             (G0+)
```

Thus the correct positive topology is already forced to be a cofinal Hilbert scale: each finite
packet has a finite entry threshold, while the full periodic capacity is unbounded in the scale
parameter.  Moreover, the radial transitions compose exactly and every strict transition is
compact and injective.  The source-factorial reporters form the exact cocone

```text
D_sigma T_(rho,sigma)=D_rho,
```

and every positive-scale `D_rho` is compact injective with dense proper nonclosed range.  Hence
the one-sided finite Fourier chart and its strictness class are already pivot-compatible; what is missing is
the full relation/dual completion and the comparison with the nonlinear normalization horizon.

`[CONJECTURE -- GAMMA DUAL-POLARIZED SCALE-RELATION FIELD]` The natural Gamma object is not a
single Hilbert or Tate completion of the periodic gauge tangent.  It is a rigged
inductive/projective scale with a compatible family of closed linear relations,

```text
Phi_Gamma  subset  {H_(Gamma,rho)}_(rho>0)  subset  Phi_Gamma',
each periodic gauge mode entering at its exact variance horizon,
the full periodic gauge field present only cofinally,
factorial conormals in the projective test side,
Gamma relations Lambda_(Gamma,rho) compatible under scale transition.              (G*)
```

The opposite face lattices and normalization horizon must be carried by the relation and its dual,
not forced to be bounded operators on one common space.  Its three conservative receivers should
recover exactly the objects above.  The comparison must prove:

```text
finite Laurent characters form the common algebraic skeleton;
the full one-sided finite Fourier gauge skeleton lies in the generalized-vector side, with its intersection
with every radial Hilbert pivot classified exactly;
the opposite-face residue pairing extends perfectly to the chosen analytic duality;
the closure of every Lambda_(Gamma,rho) has a calculable kernel, multivalued part, domain, and
range, and these defect packages commute with scale transition;
each Hilbert-pivot graph has zero intersection but dense nonclosed sum with the source lattice;
its strictness scale is the proved factorial Gamma scale;
the nonlinear horizon relation has nontrivial every-finite-stage fibres and trivial cofinal fibre;
both effects arise from one relative-position pro-object, without asserting that their numerical
decay scales are equal.                                                        (G1)
```

The last qualification matters: factorial linear conditioning and nonlinear horizon escape are
not known to have the same asymptotic scale.  Forcing equality would be theatre.  The theorem is a
functorial comparison of their kernels, strictness defects, face filtrations, and transition maps.
If `(G1)` fails, the positive residue is a classification of which receiver requires a different
variance space and whether the comparison fails by non-domain, nonclosability, multivalued
closure, kernel, cokernel, or nonclosed range.  These are invariants of one linear relation rather
than analogies between unrelated failures.

## Next proof obligations

- [x] refute unlabelled period topology as the full degeneration carrier
- [x] prove the automorphism-to-boundary endomorphism fracture
- [x] formalize the zero-nome coordinate-deletion face at every multiple-gamma rank
- [x] formalize exact finite elliptic-gamma-to-Pochhammer collapse and source recurrence
- [x] formalize exact zero-gain for all source-factorized reporter families
- [x] formalize arbitrary-rank boundary-only Fourier gauge packets after deleting a nonreal shift
- [x] refute the universal one-sided normal-character chart by the negative periodic mode
- [x] formalize the finite Laurent zero/infinity two-face law, inversion exchange, and normalized
      joint rigidity
- [x] formalize the reporter-graph relative-position law: exact kernel is lattice intersection,
      reporter range is lattice sum, and nonclosed range is nonclosed sum
- [x] refute a coordinatewise identification of the Gamma conormal domain with the factorial `l2`
      pivot and classify the pure-mode intersection exactly as the constant mode
- [x] prove the exact Gamma variance horizon for every finite nonnegative-frequency packet, including no-cancellation,
      cofinal entry, and strict wall-crossing filtration
- [x] construct compositional radial transitions with compact-injective strict bonds
- [x] construct the factorial reporter cocone and prove the same dense nonclosed-range phase at
      every positive pivot
- [x] compute the nonperiodic Barnes derived source-face fracture as an exact two-periodic matrix
      factorization and prove that every nonempty face has Tor amplitude one
- [x] construct an explicit Tate-theta family whose escaping elliptic divisor realizes every
      pointed rank-one winding character with conserved node charge
- [ ] compute the complete multigraded derived face Betti table of the multiple elliptic-gamma
      Stanley--Reisner characteristic module and compare it with the conjectural residue tower `(5)`
- [ ] construct the generic-to-face stabilizer morphism for the actual elliptic-gamma family
- [ ] construct the completed inductive/projective Gamma scale and compatible closed reporter
      relations beyond the now-proved finite Fourier cocone; identify its two natural face lattices
- [ ] prove or refute the corrected character-line duality `(R4+)`--`(R4-)` and its residue pairing
- [ ] construct a genuinely transverse Gamma reporter/counterlattice without inserting Gamma as
      target data
- [ ] prove that the Gamma source/reporter relative-position field recovers the exact kernel,
      factorial nonclosed-range defect, and nonlinear normalization-horizon exchange
- [ ] calculate the rigidification--specialization kernel, cokernel, and transgression `(R1)`--`(R3)`
- [ ] construct the analytic specialization map on the pointed gamma cochain
- [ ] prove it preserves the DA--holomorphic intersection coefficient sector
- [ ] identify the boundary class with the actual q-Pochhammer/Jackson q-gamma class
- [ ] prove nontriviality of the boundary DA class without an axiom
- [ ] prove commutation of residue and connecting morphism in `(4)`
- [ ] extend the construction to two transverse zero-nome faces and test residue commutativity
- [ ] obtain independent specialist novelty review
