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

## `[CONJECTURE -- COHOMOLOGY--SPECIALIZATION TRANSMUTATION]`

Let `X_T` be the solution stack of a regular source-minimal HT family and let `G_T` be its normalized
joint-fixed inertia.  A transverse reporter supplies a two-term observation complex

```text
C_T^obs=[G_T^HT -> H_T],
H^(-1)(C_T^obs)=residual source gauge,
H^(0)(C_T^obs)=attainment defect.                              (R1)
```

Derived specialization is exact and therefore preserves the homotopy fibre defining derived
rigidification.  The literal derived commutator is zero.  The nontrivial operation is instead the
failure of ordinary cohomology to commute with derived specialization.  At one regular face
`A -> B=A/(x)`, its edge sequence is

```text
0 -> H^(-1)(C_T^obs)/x
  -> H^(-1)(C_T^obs tensor_A^L B)
  -> Tor_1^A(H^0(C_T^obs),B) -> 0.                           (R2)
```

Thus generic nonattainment can reappear one degree earlier as born reconstruction inertia without
any loss in the derived complex.  The candidate HT-specific structure couples the edge class in
`(R2)` to the independently constructed source-face vanishing cycle by a canonical transgression

```text
kappa_T:Tor_1^A(H^0(C_T^obs),B) -> Phi_T(D_T).               (R3)
```

It is constrained by four laws.

1. **Endogenous blindness.** Every realization derived solely from the coarse source boundary
   has the same fibres as that boundary; detecting the nonzero edge class in `(R2)` requires a
   genuinely transverse channel or retention of the stack inertia itself.
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

3. **Conservation.** A generic obstruction may change cohomological degree or move from attainment
   to stabilizer inertia, but the exact derived base-change complex retains it.  A conservative
   coefficient realization must carry the same edge class rather than merely reproduce its
   dimension.
4. **Presentation invariance.** Replacing a functional-equation presentation by an equivalent
   source presentation gives an equivalent observation complex and the same weightwise edge
   transgression.

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
3. **selection--production transgression:** the map `(R3)` carries the cohomology/base-change edge
   class into the boundary receiver; a gauge or primitive class can disappear from generic
   cohomology only by producing born inertia or a nonzero boundary/vanishing-cycle class, possibly
   with a one-degree shift;
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

Residues commute for transverse faces, the cohomology/base-change edge maps satisfy the
corresponding Beck--Chevalley interchange law, and their support matroid is the already-proved
transverse constraint matroid.  The characteristic cycle of this stack-valued constructible
object is the proposed presentation-independent carrier of hypertranscendental capacity.

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
`../2-fully-proven/not_new_scientific_knowledge/05-algebraic-geometry-cohomology/tate-theta-divisor-to-winding-transgression.md`.

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

## Attack result: cohomological transmutation, not a derived commutator `[PROVED BRIDGE]`

The common-kernel theorem from the independent reconstruction lane kills one remaining epicycle
in `(B9)`.  A common-kernel sheaf and a derived face module must not be adjoined as unrelated
entries.  They are adjacent cohomology of one observation-resolution complex.

First, the literal derived version of `(R1)` is false as a nonzero invariant.  If rigidification
is the homotopy fibre of an observation map and specialization is derived tensor, derived tensor
is exact and preserves homotopy fibres.  Therefore

```text
[NO-GO]
the commutator between derived rigidification and derived specialization is canonically zero.
```

The maximal positive replacement is the failure of ordinary cohomology to commute with derived
specialization.  For a two-term observation complex

```text
C_obs=[G_HT --Obs_R-> H_R],       H^(-1)=common kernel, H^0=attainment defect,
```

and a regular one-coordinate face `A -> A/(x)`, there is an exact sequence

```text
0 -> H^(-1)(C_obs)/x
  -> H^(-1)(C_obs tensor A/(x))
  -> Tor_1^A(H^0(C_obs),A/(x)) -> 0.                       (B11)
```

Thus an attainment defect becomes a born invisible gauge one degree earlier.  More generally,
the exact quotient theorem gives

```text
born gauge modulo inherited gauge
  ~= (range(Obs_R) intersect forgotten target layer)
      / Obs_R(forgotten source layer).                    (B12)
```

The right side is an excess intersection, so boundary nonconservativity is not arbitrary.

On a Hilbert realization let `A_0` be the specialized reporter and
`Delta_0=A_0^* A_0` its Gram operator.  The elementary identity

```text
ker(Delta_0)=ker(A_0)
```

combines with `(B11)` to give the exact positive-receiver form

```text
0 -> inherited Gram radical -> boundary Gram radical
  -> Tor_1^A(H^0(C_obs),A/(x)) -> 0.                       (B11+)
```

If the generic observation is injective, the complete boundary positivity radical is therefore
the specialized attainment `Tor_1` class.  Reconstruction failure and Gram-positivity failure are
not merely correlated in this regime: they are the same born class under two exact realizations of
one observation complex.  The fixed-source equality between reporter injectivity and residual
Gram injectivity is already Lean-formalized in `SourceGaugeObservabilitySpectrum.lean`; the
face-excess kernel and quotient law is Lean-formalized in `SourceFaceObservationExcess.lean`.
The combined statement remains parent homological algebra and Hilbert geometry, not an HT novelty
claim.  Its force is to remove positivity from the list of independent mysteries once a common
polarized observation complex has actually been constructed.

The smallest discriminator is multiplication by `1` versus multiplication by `x` over `k[x]`.
Both maps have zero generic kernel.  Modulo `x`, the first remains injective and the second becomes
zero because their cokernels are respectively `0` and `k[x]/(x)`.  Hence the common-kernel sheaf
alone is not face-conservative; the differential and cokernel of the observation complex are
necessary.

For Barnes, `(B11)` is exactly the already-proved matrix-factorization class.  The presentation

```text
A --product_i x_i-> A -> M_N -> 0
```

is injective before restriction and zero on every nonempty coordinate face.  Consequently

```text
boundary kernel = Tor_1^A(M_N,B_S)=B_S.                   (B13)
```

The regular phrase "reconstruction inertia" and the singular phrase "capacity birth" now denote
the same class, not two similarly sized classes.

This attack supersedes the separate common-kernel entry of `(B9)`.  The corrected candidate is a
source-face diagram of filtered perfect observation complexes

```text
OCR(F,R)=Rees_delta(U |-> C_obs(F,R;U)),                  (B14)
```

with the source presentation complex as one receiver and independently constructed analytic,
spectral, positive, monodromic, and integral reporters as other receivers.  The characteristic
module is a degree-zero cohomology object of `(B14)`; the common kernel is degree `-1`; higher
syzygies and iterated face classes occupy lower degrees.  Separate direct-sum packaging is no
longer admissible.

The complete zero-face calculation for the critical normal-crossing module now gives, for a face
of size `k`, amplitude one when `k=1` and amplitude two when `k>=2`.  On one face its degree-zero
term is the lower normal-crossing hypersurface module, while its degree-one term is precisely the
kernel of the map from that hypersurface module to the lower critical module.  Thus the born
class is the entire correction from specialization-after-criticalization to
criticalization-after-specialization.  The formulas and proof are recorded in
`../2-fully-proven/not_new_scientific_knowledge/05-algebraic-geometry-cohomology/source-face-observation-cohomology-transmutation.md`.

The algebra in `(B11)`--`(B13)` is classical and is a bridge, not new scientific knowledge.  The
candidate-new theorem is now sharply smaller and harder:

```text
[CONJECTURE -- HT BOCKSTEIN CONSERVATIVITY]
For one natural source-minimal HT degeneration and one independently typed transverse analytic
reporter, the analytic born gauge or boundary charge is the Bockstein image of the same
characteristic Tor class appearing in the source presentation complex.                (B15)
```

The explicit Tate-theta divisor-to-winding family is the first target.  Equality of the two
integer labels is insufficient; `(B15)` requires a natural map of complexes carrying the Tor
class to the analytic node-charge class and preserving the DA-relative filtration.  This is the
first point at which the theory would prove conservation across genuinely different receivers.

## Coefficient discriminator: the integral localization class `[PROVED LOCAL BRIDGE]`

Attacking `(B15)` reveals that a purely complex-linear observation complex is still too small.
The characteristic `Tor_1` class is a complex vector space, whereas winding/node charge is a
primitive integral class with orientation.  Scalar multiplication acts transitively on the
nonzero vectors of a complex line, so no construction using only that line can canonically select
`+1` rather than an arbitrary nonzero scalar or its negative.

```text
[NO-GO]
The coherent characteristic complex alone cannot recover integral charge, primitivity, or
orientation.
```

The local semistable node identifies the exact positive replacement.  Let `R` be a DVR with
uniformizer `t` and

```text
A=R[x,y]/(xy-t),       X=Spec(A),       Z=V(x),       B=A/(x).            (B16)
```

The element `x` is a unit on `X-Z`, and, with the boundary orientation in which `V(x)` is
positive, the localization boundary sends

```text
partial_K([x^m])=m[A/(x)] in K_0^Z(A).                                  (B17)
```

Equivalently, `(B17)` is represented by `m` times the Koszul complex

```text
K(x)=[A --x-> A].                                                        (B18)
```

Derived restriction of `(B18)` to the face is

```text
K(x) tensor_A^L B=[B --0-> B],                                          (B19)
```

so its two homology groups are the exact relation-death/capacity-birth pair.  The coefficient of
`V(x)` in the vertical divisor of `x^m` is `m`, which is the node charge.  Thus

```text
regular winding -> integral K_1 class -> supported Koszul class -> born Tor pair              (B20)
```

is one localization chain.  The algebraic localization theorem and Koszul calculation are
classical; `(B20)` is a bridge, not a novelty claim.

Algebraic K-theory is not itself the full unified object: distinct perfect complexes can have the
same K-class, so passing immediately to a K-theory spectrum can forget the differential that
distinguished multiplication by `1` from multiplication by `x`.  The maximal positive correction
is therefore categorical:

```text
[CONJECTURE -- POLARIZED HT CONSTRAINT-LOCALIZATION CATEGORY]
A source-minimal HT system determines a DA-filtered stable category of observation-resolution
complexes with source-face localization sequences.  Its coherent realization is `(B14)` and
produces Tor/common-kernel transmutation; its integral K-theory realization produces winding,
divisor charge, and primitivity; a self-dual hermitian realization produces orientation and
positivity.  These realizations are jointly conservative on the source-generated subcategory.
                                                                            (B21)
```

This is stronger than attaching several invariants to a function: the realization functors must
start from the same object and carry the same localization morphism.  It is also falsifiable.
Two source-generated objects with equal coherent, integral, and hermitian realizations but
different analytic obstruction behavior kill joint conservativity; a Tate-theta node charge not
equal to the localization boundary of its analytic source class kills the first cross-realization
test.

The analytic side of the semistable Tate chart can now be proved locally.  Make the base change
`q=t^4` and write the node as `xy=t`.  Direct factorization of the theta products gives

```text
E_(t^4)(x)=x u(x,y,t),       u a unit with u(0,0,0)=1.                    (B22)
```

The key identities are

```text
t theta_(t^4)(t^(-1)x)=(t-x) times a unit,
theta_(t^4)(t^3x)=(1-y) times a unit,
t-x=-x(1-y).
```

Hence the analytic localization class of `E_(t^4)` is exactly `[x]`, not merely a function with
the same limiting winding.  Separately, in any one commutative ring the chain map

```text
K(xi) -> K(p xi),       degree 1: identity,       degree 0: multiplication by p          (B23)
```

commutes because `p xi=p xi`; after restriction to `xi=0`, its degree-one map remains the
identity.  The theta factorization and this algebraic chain map are recorded in
`../2-fully-proven/not_new_scientific_knowledge/05-algebraic-geometry-cohomology/tate-theta-koszul-barnes-localization-transmutation.md`.

Attacking the composition exposes a decisive type error.  The nodal coordinate `x` in `(B22)` is
a meromorphic gauge vector.  The Barnes factor is the source operator

```text
xi_j=T_j-1.                                                              (B24)
```

They are not elements of one ring.  A valid realization must send `x` to a vector annihilated by
`xi_j`; it cannot identify the vector with the operator `xi_j`.

```text
[NO-GO]
The local theta localization class and the Barnes Koszul class cannot be identified by reusing
the symbol x.  A typed realization functor is still missing.
```

The positive replacement is now explicit at every integral charge.  For a Barnes period
`omega_j`, put

```text
lambda_(j,m)=2 pi i m/omega_j,
ell_(j,m)(z)=exp(lambda_(j,m) z),
chi_(j,m)(T_k)=exp(lambda_(j,m) omega_k),
chi_(j,m)(delta)=lambda_(j,m).                                  (B25)
```

Every `chi_(j,m)` factors through `B_j=D_N/(T_j-1)`, so the `m`-th face fibre maps `1` to the
vector `ell_(j,m)`.  Distinct charges form linearly independent analytic modes.  Thus the full
local receiver is the graded object

```text
Char_j=directSum_(m in Z) B_j tensor_(chi_(j,m)) C,               (B25+)
```

not the single primitive fibre.  Lean proves selected-period annihilation, every complementary
translation phase, the differential eigenvalue, and arbitrary finite distinct-charge
independence in `NodalChargeCharacterRealization.lean`.

Attacking face gluing gives a second exact theorem.  If `omega_j,omega_k` are rationally
independent, then

```text
lambda_(j,m)=lambda_(k,n) iff m=n=0.                              (B26)
```

Hence nonzero charge sectors on incommensurate faces cannot be glued by identifying character
lines.  The maximal positive replacement is a face-separated source-character fan: every face
retains `(B25+)`, while different independent rays meet only in the neutral sector.  Resonant
overlaps must be the exact integral commensurability sublattice.  The complete bridge theorem is
recorded in
`../2-fully-proven/not_new_scientific_knowledge/nodal-charge-character-fan-realization.md`.

The corrected open core is global, DA-relative, and typed:

```text
[OPEN CORE]
Construct a presentation-invariant face-poset character object for a source--observation double
whose stalks are `(B25+)` and whose overlaps are the exact resonance lattices `(B26)`.  Construct
a map of localization sequences carrying the Tate classes `[E^m]` through the integral nodal
boundary to the filtered charge interval with associated graded
`L_0 directSum ... directSum L_(m-1)`, then to the coherent Barnes `Tor` class and its analytic
interval realization.  The charge-`m` line is the endpoint reached, not this boundary.  Prove that
the analytic reporter is genuinely transverse to the bare source, together with DA-filtered
naturality, iterated-face coherence, and conservativity after analytic completion.             (B27)
```

Only `(B27)`, not the local Fourier/character theorems, is a candidate for new scientific
knowledge.

## `[CONJECTURE -- POLARIZED SOURCE-CHARACTER FAN]`

The new local theorem makes the proposed unified object more rigid.  It is not an unstructured
stable category plus separately attached integral and hermitian invariants.  For a regular
source-minimal HT system equipped with reporter data `(S,R)`, conjecturally there is a
presentation-invariant constructible observation-complex field

```text
PChar_HT(S,R) -> Face(S)                                               (B28)
```

whose stalk on a source face `F` decomposes by the integral annihilator characters of `F`.  In the
rank-one nodal chart this is exactly `(B25+)`.  The field carries, as structures on the same stalks
and restriction maps:

```text
coherent differential      -> kernel/cokernel and Tor transmutation;
charge involution m <-> -m -> source reflection and multiplicative duality;
integral localization      -> primitive node/divisor charge;
opposite-line pairing      -> polarization and crossing form;
strict completion          -> closed-range/spectral incompleteness;
determinant of restrictions -> monodromy and multiplicity;
positive charge chamber    -> oriented canonical boundary condition.                 (B29)
```

This is a refinement of `(B21)`, not another primitive added to it: the face poset, character
grading, and involution are now forced by `(B25)`--`(B26)`.  Only the localization, pairing,
completion, and determinant structures remain to be constructed functorially for the
source--observation double.

The orientation discriminator is exact.  By

```text
lambda_(j,-m)=-lambda_(j,m),       ell_(j,-m) ell_(j,m)=1,                (B30)
```

charge reversal is an automorphism of the unpolarized character fan.  Therefore any invariant
factoring through the underlying derived/coherent fan is blind to orientation surgery.  This is
not a defect that more derived topology can repair.

```text
[NO-GO]
An unpolarized derived source-face theory cannot canonically choose positivity or an oriented
boundary condition, even after retaining all Tor groups and all charge lines.
```

```text
[POSITIVE]
The source canonically supplies the opposite-charge involution and multiplicative duality.  The
minimal missing datum is a source-compatible nondegenerate pairing between opposite sectors plus a
chamber selected by a genuinely transverse reporter.  If that reporter is source-derived, the
bare-source nonconservativity theorem still rules it out.
```

The bare-source theorem now imposes an exact architectural constraint.  For every face `F`, let
`K_F^(S,HT)` be its normalized DA-relative source-fixed gauge and let `R_(F,r)` be the proposed
reporters.  Define the invisibility stalk

```text
I_F(S,R)=K_F^(S,HT) intersect intersection_r ker(R_(F,r)).               (B31)
```

The Lean-formalized joint reconstruction theorem and first isomorphism theorem give

```text
Obs_(F,R) conservative iff I_F(S,R)=0,
K_F^(S,HT)/I_F(S,R) ~= range(Obs_(F,R)).                                 (B32)
```

Thus a successful unified object cannot be a functor of the bare source `S` alone.  Its true input
must be a **constant-framed source--observation double** `(K,C;S,R_perp)`, where `C` is the declared
joint difference-constant field and `R_perp` contains information not factoring through the source
quotient.  Presentation invariance means invariance under equivalent presentations over the same
constant frame; it must not be misread as derivability of `R_perp` from `S`.

```text
[CONJECTURE -- POLARIZED HT INVISIBILITY FIELD]
For every regular constant-framed source--observation double `(K,C;S,R_perp)`, the facewise fibres of the complete
DA-relative observation complexes assemble into a charge-graded, self-dual constructible field
I_HT(K,C;S,R_perp) over `Face(S)`.  Its H^(-1) stalk is `(B31)`, its H^0 stalk is the attainment or
spectral defect, its face connecting maps are the Tor/Bockstein transmutations, and its determinant
line carries monodromy and the opposite-charge polarization.  A transverse double is complete
exactly when this field is acyclic and its positive chamber is fixed.                         (B33)
```

The charge-two discriminator forces a sharper object.  The localization boundary of `[x^m]` is
not the endpoint character line `L_m`: already `[x^2]` has boundary multiplicity two.  Its correct
character refinement is an oriented interval representation `B_F(m)` with consecutive graded
pieces `L_0,...,L_(m-1)` and charge-raising arrows.  Lean proves the all-power unilateral defect,
the exact interval-plus-tail decomposition, the interval concatenation cocycle, the analytic
pairing value `m`, and that the interval pairing equals the endpoint pairing exactly when `m=1`.

```text
[NO-GO]
An endpoint-labelled source-face theory cannot conserve nonprimitive localization classes.  Even
its full split associated graded remembers only the sectors and forgets the ordered extension
joining them.

[POSITIVE]
The minimal local carrier is the indecomposable oriented interval module, not a character line and
not merely its K-class.  Its arrows remember which charge crossings occurred and in what order.
```

Accordingly `(B33)` must be upgraded from a field of obstruction groups to a representation of the
oriented exit-path category of `Face(S)`:

```text
B_F(m+n)=B_F(m) concatenate shift_m(B_F(n)),
B_F(-m)=dual(B_F(m)) with reversed orientation.                              (B34)
```

Raw interval length cannot classify hypertranscendence.  The differential-algebraic solution
`exp(z)` of `f(z+1)=e f(z)` admits nontrivial differential-algebraic period-one gauges matching any
prescribed finite jet; the stronger arbitrary-jet statement is already Lean-formalized by
`existsUnique_gammaPeriodicFourierPolynomial_jet`.  Thus unbounded finite-jet invisibility can be
created entirely by enlargement of the analytic difference-constant field.

The first relative successor also fails in a precise way.  If a descended subrepresentation of
the finite-support clock is invariant under both charge raising and charge lowering, then it is
zero or the whole clock.  This all-or-nothing theorem and its positive one-sided tail-filtration
successor are Lean-formalized in `TateClockUnilateralShiftDefect.lean`.  Thus no nontrivial
constant-field descent can be a two-sided invariant subclock.

```text
[NO-GO]
D <= directSum_(n>=0) K e_n, S(D)<=D, B(D)<=D  ==>  D=0 or D=all.       (B35)

[POSITIVE]
T_m=S^m(V) is nonzero proper; S preserves T_m and B maps T_(m+1) to T_m.
Moreover T_m=range(S^m)=kernel(P_[0,m)), so V/T_m is the interval B(m).
Nontrivial descent is necessarily polarized and relative.                      (B36)
```

Nor can the complete Kolchin dimension polynomial be identified with a
presentation-independent scalar length: the full polynomial depends on the differential
generators, while only differential type and leading typical dimension are differential-birational
invariants.  Scalar length would additionally forget the interval arrows.  Kolchin growth is
therefore a decategorified algebraic shadow, not the universal obstruction object.

The cotangent--Tate cone is not a new primary invariant.  Put

```text
H_(S,R)=K^S intersect intersection_r ker(R_r),
N_(S,R)=stack of source-effectively normalized germs with stabilizer H_(S,R).
```

The universal labelled differential-field theorem now gives a decisive additional no-go.  For
equally indexed HT palettes, the algebraic differential field generated by all labelled jets is
canonically the same free differential-rational field.  Hence the algebraic prolongation tower is
a universal carrier, not a source classifier.

```text
[NO-GO]
Cone(P_alg --Phi--> P_an) is source-blind if Phi is intrinsic to the free HT carrier;
it remains nonconservative if Phi factors through the bare source;
and if Phi uses a transverse reporter, the cone is only one chart of the already required
source--reporter object.                                                   (B37-old)
```

The nontrivial positive replacement is to derive the source invariants before applying the
reporter.  In a stable source category, with `H_R` concentrated in degree zero, let

```text
C_obs^der(S,R)=Cone(RGamma(S,G_HT) --R_perp--> H_R).                   (B37a)
```

Its low-degree exact sequence is forced:

```text
H^(-1)(C_obs^der)=ker(H^0(RGamma(S,G_HT))->H_R),
0 -> coker(H^0(RGamma(S,G_HT))->H_R)
  -> H^0(C_obs^der)
  -> H^1(RGamma(S,G_HT)) -> 0.                              (B37b)
```

Thus normalized reconstruction inertia, reporter nonattainment, and first source/continuation
cohomology are not three unrelated obstructions.  They are consecutive terms of one derived
source--reporter fibre.  This exact sequence is standard homological algebra and is not a novelty
claim.

Nor is `(B37a)` complete.  It forgets approximate zero modes, nonclosed range, source-labelled
orientation, critical rescaling, integral lifting, and the boundary self-symbol.  The primary
candidate is therefore the normalized anomaly-fracture stack
`U_(F,R)^(p,q)` of `hypertranscendental-source-fracture-hypercube.md`: `(B37a)` is its
cohomological chart, while the full object additionally retains the completed reporter graph and
Gram field, complete source-anomaly boundary colligation, critical product bornology, anomaly
line/polarization, integral realization, and distinguished effective section.

The Gamma finite theorem supplies the first exact compression law inside that object:

```text
Weyl seam = - (outgoing analytic curvature)(incoming algebraic defect).       (B37c)
```

Thus seam and paired current are one oriented boundary morphism, not two coordinates.  The
balanced prime--Ising variance theorem independently forces the critical-bornological channel:
every convergent unbounded-rank source sequence must satisfy
`a_n^2 |V_n|=O(1)`, so an unscaled derived object cannot even distinguish the excluded regime from
the only surviving critically renormalized regime.

The bold universal claim is that, for source-minimal HT systems, every natural reconstruction,
continuation, spectral-completeness, positivity, monodromy, and boundary-condition obstruction is
a conservative realization of the same normalized anomaly-fracture object of `(B33)`--`(B37c)`.
This would explain the repeated
obstructions without identifying them by analogy.  It is also sharply falsifiable: one natural
obstruction not functorially obtained from `(B33)`, or two doubles with the same polarized field
but different obstruction behavior, kills the claim.

The complex/fibre formalism in `(B33)` is standard parent mathematics.  Candidate-new content is
the existence and presentation-independent classification of complete transverse HT doubles, the
double-natural conservation of one class through all face maps, and the proof that the analytic,
coherent, integral, hermitian, and spectral reporters are jointly conservative realizations of it.

The conjecture is falsified if one natural obstruction changes while `(B28)` with all structures
in `(B29)` remains unchanged, or if equivalent source presentations produce different resonance
overlaps.  Merely constructing a standard toric fan, Kato fan, Grothendieck--Witt spectrum, or
Fredholm--Lagrangian bundle does not pass the novelty gate; the candidate-new content is the
classification of complete transverse HT doubles and the proof that genuinely independent
analytic receivers carry the same localization class.

## Why this could be Fields-scale

The field-level theorem is not the abstract existence of nearby cycles, which is parent theory,
and not the classical elliptic-gamma degeneration.  It is the construction and classification of
a new natural invariant with all of the following simultaneously:

1. defined for nonlinear source-minimal HT constraints equipped with genuinely transverse data;
2. independent of a chosen presentation of the source--observation double;
3. constructible across automorphism-to-endomorphism source walls;
4. retains jumping source inertia and computes the cohomology--specialization Tor/Bockstein
   transmutation;
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
10. localization in hermitian K-theory and Grothendieck--Witt theory for categories with duality
    (Schlichting, arXiv:1209.0848, and subsequent stable-infinity-categorical refinements).
11. parameterized difference-Galois hypertranscendence for shift, q-difference, and Mahler
    equations (Adamczewski--Dreyfus--Hardouin, arXiv:1910.01874) and hypertranscendence of
    multiplicative perturbations `f exp(g)`, including partial results for `Gamma exp(h)`
    (Huang--Ng, arXiv:2007.10037).
12. inverse-problem invisibility spaces and symmetry of objects invisible to incomplete moment
    reporters (Batenkov--Golubyatnikov--Yomdin, arXiv:1205.5661).
13. finite persistence modules as equioriented type-`A` quiver representations or graded
    polynomial modules, coherent devissage by filtered subquotients, and unilateral-shift index
    defects (De Gregorio--Guerra--Scaramuccia--Vaccarino, arXiv:2106.11884; Stacks Project,
    Tag 07US; Fujikawa, arXiv:hep-th/9411066).
14. the Toeplitz algebra generated by the unilateral shift and the absence of nontrivial reducing
    subspaces in multiplicity one (Coburn, *Bull. AMS* 73 (1967), DOI
    `10.1090/S0002-9904-1967-11845-7`), together with Kolchin dimension polynomials and
    parameterized difference Galois theory (Kolchin; Hardouin--Singer, arXiv:0801.1493).

Targeted exact searches for `elliptic gamma nearby cycles`, `elliptic gamma vanishing cycles`,
`differential-algebraic elliptic gamma degeneration cohomology`, and
`q-Pochhammer gerbe transgression`, together with searches for `rigidification specialization
inertia` and `nearby cycles quotient stack inertia`, found the parents separately but no HT
cohomology-specialization transgression into a typed analytic character receiver, no two-faced
normal-character/born-gauge duality `(R4+)`--`(R4-)`, and no coefficient-filtered source-face
residue theorem of the form `(3)`--`(5)`.  This is a preliminary novelty pass, not a specialist
verdict.

Further exact searches for `hypertranscendental Tate space`, `hypertranscendental Lagrangian gauge
inertia`, `hypertranscendental Maslov`, and `hypertranscendental Fredholm source constraint` found
the parent theories separately but no HT-specific construction of `(T0)`--`(T3)`.  The novelty
candidate is not Tate theory, Maslov theory, solution torsors, Laurent polarization, or Gamma
uniqueness, nor is it the abstract availability of hermitian localization.  It is the functorial
assignment of a self-dual two-lattice relative-position field to source-minimal HT pairs, together
with a typed realization carrying the same source-face class through coherent, integral,
hermitian, and analytic receivers.  The proof that the obstruction receivers in `(T2)` are
conservative images of that single class remains `[NOVELTY PRELIMINARY]` pending a specialist
audit.

Additional exact searches for `hypertranscendental observation complex`, `hypertranscendental
gauge torsor reconstruction`, `source-observation double mathematics conservativity`, and
`invisibility complex gauge reconstruction` found the source-equation, perturbation, and inverse-
problem parents above, but no HT source--observation double, polarized invisibility field, or
classification theorem of the form `(B31)`--`(B33)`.  This is evidence for a live novelty candidate,
not a claim that the literature gate has been conclusively cleared.

Exact searches for `hypertranscendental interval module`, `hypertranscendental persistence module`,
`hypertranscendental exit-path category`, and `difference equation oriented interval sheaf` found
the interval/quiver and hypertranscendence parents separately, but no boundary-interval
classification of differential transcendence and no jointly conservative realization theorem of
the form `(B34)`.  The local interval laws are parent mathematics; only the HT classification and
cross-receiver theorem remain novelty candidates.

The standalone comparison cone `(B37-old)` no longer carries a novelty claim.  Mapping fibres and
their long exact sequences are standard; difference sheaf cohomology and torsors are developed by
Chalupnik--Kowalski (`arXiv:1912.06886`); parameterized differential torsors and cohomological
triviality criteria are treated by Leon Sanchez--Meretzky (`arXiv:2603.03658`); determinant
torsors for Tate spaces are parent theory (`arXiv:1002.4863`); and finite-rank Taylor-tail/Hankel
phenomena lie under Kronecker-type theory (`arXiv:1506.05566`).  The exact Gamma seam identity is
therefore a rigorous cross-realization bridge, not by itself new scientific knowledge.

Targeted searches still found no source-canonical HT construction of the full normalized
anomaly-fracture stack, no classification of its admissible transverse reporters, and no theorem
proving that two genuinely different analytic obstruction receivers preserve one nonzero
seam/interval class.  Those three obligations, together with a transferred analytic theorem, are
the surviving novelty candidate.  This is a preliminary literature gate, not a specialist
priority verdict.

## Anti-theatre gate

1. The unit obstruction, polynomial boundary ideal, and Pochhammer degeneration are parent bridge
   mathematics and are not promoted as discoveries.
2. The source-factorization no-go and finite Fourier gauge packets are parent algebra/analysis and
   are not promoted as discoveries.
3. Writing a standard rigidification or nearby-cycle triangle, mapping fibre, Tate object,
   Lagrangian pair, or Maslov cycle is not new mathematics.  The new obligation is to construct the HT-natural
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
relative-position field `(T1)`, cohomology-specialization edge transgression `(R1)`--`(R3)`, and
triangle `(2)`.
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
- [x] compute on paper the complete multigraded zero-face Betti table of the multiple
      elliptic-gamma Stanley--Reisner characteristic module; the one-face born class is exactly
      the correction from the lower hypersurface module to the lower critical module
- [ ] formalize the complete zero-face Betti table and compare its multigrading with the analytic
      residue tower `(5)`
- [ ] construct the generic-to-face stabilizer morphism for the actual elliptic-gamma family
- [ ] construct the completed inductive/projective Gamma scale and compatible closed reporter
      relations beyond the now-proved finite Fourier cocone; identify its two natural face lattices
- [ ] prove or refute the corrected character-line duality `(R4+)`--`(R4-)` and its residue pairing
- [ ] construct a genuinely transverse Gamma reporter/counterlattice without inserting Gamma as
      target data
- [ ] prove that the Gamma source/reporter relative-position field recovers the exact kernel,
      factorial nonclosed-range defect, and nonlinear normalization-horizon exchange
- [x] supersede the literal derived rigidification--specialization commutator by the
      cohomology/base-change observation complex and edge sequence `(R1)`--`(R3)`, `(B11)`
- [ ] construct the HT Bockstein comparison map `(B15)` from the characteristic Tor class to the
      independently defined Tate-theta node-charge class
- [x] isolate the integral-coefficient no-go for a complex-linear Tor line and identify the local
      nodal K-theory/Koszul localization chain `(B16)`--`(B20)`
- [x] prove the local Tate-theta factorization `(B22)` and, separately, the same-ring product-face
      chain map `(B23)`
- [x] reject the nodal-coordinate/source-operator symbol collision `(B24)` and construct the
      correctly typed full Barnes charge-character grading `(B25)`--`(B25+)`
- [x] prove rationally independent face-character spectra meet only in the neutral sector `(B26)`
- [x] refute endpoint localization for nonprimitive charge and Lean-formalize the all-power
      oriented interval decomposition, cocycle, pairing, and sharp endpoint exception `(B34)`
- [x] refute raw interval capacity as an HT criterion using differential-algebraic periodic gauges
- [x] rule out nontrivial two-sided clock descent and formalize the polarized tail tower
      `(B35)`--`(B36)`
- [x] rule out the full Kolchin polynomial as a presentation-independent scalar invariant
- [ ] construct the source-effective normalization stack and the strict polarized derived
      source--reporter observation complex `(B37a)` as a chart of the normalized anomaly-fracture stack
- [x] retire the standalone cotangent--Tate cone `(B37-old)` using free-field universality,
      bare-source nonconservativity, and the missing strict/bornological/orientation channels
- [ ] construct the typed global DA-relative face-poset realization and localization comparison
      `(B27)` over the actual multiple-gamma source-face diagram
- [ ] construct the analytic specialization map on the pointed gamma cochain
- [ ] prove it preserves the DA--holomorphic intersection coefficient sector
- [ ] identify the boundary class with the actual q-Pochhammer/Jackson q-gamma class
- [ ] prove nontriviality of the boundary DA class without an axiom
- [ ] prove commutation of residue and connecting morphism in `(4)`
- [ ] extend the construction to two transverse zero-nome faces and test residue commutativity
- [ ] obtain independent specialist novelty review
