# Projective-scheme reconstruction from a pretemporal hypertranscendence horizon

- **ID:** `projective-variety-hypertranscendence-realization`
- **Stage:** 1-in-progress
- **Type:** CLASSIFICATION THEOREM / DIFFERENTIAL ALGEBRA / ALGEBRAIC GEOMETRY / RIGIDITY-UNIVERSALITY DICHOTOMY
- **Scientific status:** `[ALL FINITE PROJECTIVE ZERO LOCI LEAN-PROVEN] [KAEHLER SCHEME RECONSTRUCTION LEAN-PROVEN] [ALL CYCLIC COMMUTING ANNIHILATORS CLASSIFIED] [NONLINEAR COMMUTING CLASSIFICATION OPEN] [NOVELTY PROVISIONAL]`
- **Paper lane:** *Before There Was Time: Holographic Universality of Hypertranscendence Horizons*
- **Set-level statement:** The finite-order directional differential-dependence loci of single
  observables under finite-dimensional linear pencils of derivations are exactly the projective
  algebraic sets.
- **Scheme-level strengthening `[LEAN-PROVEN]`:** With the horizon equipped with its canonical
  top-principal-symbol ideal, every finite homogeneous presentation occurs, and saturation of the
  intrinsic Kähler/minor ideal recovers the saturated projective ideal, including nonreduced
  structure away from the affine cone vertex.
- **Dichotomy:** Honest regular coefficient-flat principal geometry has empty horizon by the
  pretemporal-anchor theorem, while curved ordered-word geometry realizes arbitrary projective
  scheme structure. There is no intermediate topological restriction without extra axioms.

## 1. Known direction `[LEAN-PROVEN ELSEWHERE]`

For a finite family of derivations `delta_i`, put

```text
D_c = sum_i c_i delta_i.
```

For one observable `x`, the order-`N` dependence locus

```text
Sigma_N(x) = {[c] : x,D_c x,...,D_c^N x are algebraically dependent}
```

is a projective algebraic set. The existing directional word-polynomial and Kähler-wedge modules
prove this without assuming that the derivations commute.

## 2. Converse theorem for every finite projective zero locus `[LEAN-PROVEN]`

Let `Z` be cut out by finitely many homogeneous equations of arbitrary degrees. There exist

1. a rational function field `L/K`;
2. derivations `delta_1,...,delta_m` of `L`;
3. one element `x in L`;
4. one finite order `N`;

such that

```text
Sigma_N(x) = Z,                                             (1)
```

and, more strongly, `x` is hypertranscendental for `D_c` at every direction outside `Z`.

Thus, at set level,

```text
projective algebraic sets
  = finite-order directional hypertranscendence horizons.   (2)
```

At scheme level, the terminal coefficient vector in `(4)` has homogeneous coordinate ideal
`(P_j)`.  Retaining that ideal rather than only its common zero set recovers

```text
Proj K[c_1,...,c_m]/(P_j).                                 (2s)
```

The intended theorem is therefore essentially surjective onto finitely presented projective
schemes, not merely onto their reduced point sets.

## 2a. General principal-symbol and Kähler reconstruction `[LEAN-PROVEN]`

The scheme structure should be recoverable from the observable itself, rather than from a chosen
terminal presentation.  For the order-`d` packet, take coordinates of the universal Kähler wedge

```text
d x wedge d(D_c x) wedge ... wedge d(D_c^d x).
```

In the free disjoint-block realization, a wedge coordinate selects one coefficient from every
lower jet block and one terminal coefficient.  The lower blocks contribute all monomials of total
degree

```text
T = 0 + 1 + ... + (d-1) = d(d-1)/2.
```

The general principal-symbol product ideal has now been isolated independently of a basis choice.
For every terminal law family `P_j` and lower principal degree `T`, Lean proves

```text
J_symbol = m^T I,                                          (2k)
```

where `m=(c_1,...,c_m)` is the irrelevant ideal and `I=(P_j)` is the terminal homogeneous horizon
ideal. Lean also proves, in every graded commutative ring, that multiplying an ideal by a positive
power of the irrelevant ideal does not change its projective zero locus. The universal factor
therefore contributes only the affine cone vertex.

The general Kähler principal-symbol theorem identifies every coordinate of the top universal
Kähler wedge with the corresponding maximal Jacobian minor.  For a universal linear packet its
Kähler coefficient ideal is the base change of the scalar maximal-minor ideal.  A separate exact
block-minor theorem proves that a disjoint block matrix has maximal-minor ideal equal to the product
of its row coefficient ideals.  Applied to the ordered-word realization, the lower row of depth
`r` generates `m^r` and the terminal row generates `I`.  Therefore Lean proves

```text
J_Kaehler = map_C(J_symbol),
J_symbol = m^T I.                                          (2ki)
```

Power saturation is defined intrinsically by

```text
Sat_m(J) = sup_n (J : m^n).
```

Lean proves for every commutative ring and every `T`

```text
Sat_m(m^T I) = Sat_m(I).                                   (2r)
```

Thus the scalar Kähler/minor symbol recovers the saturated original projective ideal, including
nonreduced multiplicity structure away from the vertex.  The forced factor `m^T` is supported only at the affine cone vertex
`c=0`, where no law direction has been selected; projectivization removes precisely this
pretemporal vacuum thickening.

For two law packets `P,Q` and arbitrary jet depths, equality of the saturated scalar Kähler/minor
ideals of their free pretemporal realizations is equivalent to equality of `Sat_m(I_P)` and
`Sat_m(I_Q)`.  The construction therefore gives a faithful reduction of saturated projective
horizon-scheme classification to hypertranscendental principal-symbol classification.

## 3. Free word-tree construction

First suppose `Z` is cut out by homogeneous polynomials `P_j` of one common positive degree `d`.
Write every `P_j` as a commutative collapse of coefficients on ordered words of length `d`.

Construct a free polynomial field with two kinds of generators:

- prefix states `x_w` for words `w` of length `< d`;
- tail states `y_(j,w)` for all words `w`.

Define each basis derivation on generators by

```text
delta_i x_w = x_(iw)                         if |w| < d-1,
delta_i x_w = sum_j a_(j,iw) y_(j,empty)     if |w| = d-1,
delta_i y_(j,w) = y_(j,iw).                                (3)
```

Extend to the polynomial algebra and then to its fraction field by the quotient rule. For the root
observable `x=x_empty`, ordered-word expansion gives

```text
D_c^d x = sum_j P_j(c) y_(j,empty),                         (4)
D_c^(d+r) x = sum_(j,w:|w|=r) P_j(c)c_w y_(j,w).           (5)
```

At every depth the variables belong to a fresh disjoint block.

- If every `P_j(c)=0`, the `d`-th jet is zero, so the jet family is dependent.
- If some `P_j(c) != 0`, then `c != 0`; every coefficient block in `(3)--(5)` is nonzero.
  Nonzero linear forms on disjoint blocks of a free algebraically independent family are themselves
  algebraically independent. Hence the complete jet tower is algebraically independent.

This proves the exact equivalence

```text
x is DA for D_c  iff  P_j(c)=0 for every j.                 (6)
```

## 4. Unequal degrees

Every projective algebraic set has finitely many homogeneous defining equations. To put them in a
common degree `D`, replace a generator `P_j` of degree `d_j` by all products

```text
M P_j,  deg M = D-d_j.                                     (7)
```

At a nonzero projective point, some coordinate and hence some monomial `M` is nonzero. Therefore all
products in `(7)` vanish exactly when every original `P_j` vanishes. The common-degree construction
then applies.

## 4a. Abelian integrability barrier `[LEAN-PROVEN NO-GO]`

The naive symmetric-Fock strengthening is false with a free terminal tail. Pairwise commuting
derivations and a boundary law

```text
delta_i z = sum_j a_(i,j) y_j
```

must satisfy the first-prolongation identities

```text
sum_j a_(i,j) delta_k y_j = sum_j a_(k,j) delta_i y_j.      (8)
```

If the first tail packet `{delta_k y_j}` is algebraically independent in disjoint direction
blocks, `(8)` forces every `a_(i,j)=0` as soon as law space has at least two directions. This is
proved unconditionally in `CommutingPrincipalSymbolProlongation.lean`.

The correct abelian problem is therefore not another cyclic annihilator ideal:

```text
Classify nonlinear or formally integrable commuting differential observable structures whose
selected one-direction orbit is algebraically independent away from a prescribed nonlinear locus.
```

This is the actual integrability barrier between free noncommutative universality and a possible
QFT-compatible abelian theory. Multinomial normalization alone cannot cross it.

## 4b. Unconditional cyclic commuting classification `[LEAN-PROVEN]`

There is now an exact classification for every cyclic model attached to an arbitrary annihilator
ideal.  Put `S=K[X_i]`, `M=S/I`, let multiplication by `X_i` act on `M`, and extend those pairwise
commuting actions to derivations `delta_i` of `Sym_K(M)`.  For the single observable
`z=iota([1])`, Lean proves

```text
(sum_i c_i delta_i)^n z = iota([(sum_i c_i X_i)^n])
```

at every order.  The full jet is algebraically dependent if and only if the class of the law form
in `S/I` is algebraic over `K`.  Algebraic elements of any commutative `K`-algebra form the integral
closure of `K`, hence a `K`-subalgebra.  Therefore the complete differential-dependence horizon is
the vector subspace

```text
ellbar^(-1)({elements of S/I algebraic over K}).
```

No homogeneity, reducedness, or finite-generation assumption on `I` is used.  If `I` is homogeneous,
the algebraic-direction subspace reduces exactly to `ell^(-1)(rad(I))`, recovering the earlier
graded theorem.  This closes the gap between the finite-annihilation proxy and an actual infinite
differential orbit.  In particular the nonlinear crossing cone is impossible in every cyclic
commuting differential domain of this form, although it is exactly realizable by the free
noncommuting model.  The remaining abelian problem is no longer any cyclic annihilator: it is the
classification of genuinely nonlinear, interacting, gauge-coupled, or formally prolonged
commuting systems.

More generally, for any finite homogeneous zero cone that is not a vector subspace, Lean now proves
the two sides together: the cone is the exact complete horizon of one free noncommuting observable,
and it is unequal to the complete horizon of every cyclic commuting annihilator model.  Nonlinear
projective horizon topology is therefore a formal phase witness, not merely an illustrative example.

## 5. Significance and anti-theatre gate

The existing theorem says hypertranscendence produces projective algebraic horizons. The converse
would say it produces **all** of them. Consequently every algebraic topology permitted in projective
geometry can occur as the exact set of pretemporal laws where one observable acquires a finite
differential rule.

This is a universality/classification result comparable in form to realization theorems stating
that every projective variety occurs as a quiver Grassmannian or a rank variety, but its carrier is
ordinary differential algebraicity of one observable under a linear derivation pencil.

The free-word construction by itself may be an elementary realization trick and is not yet a
Fields-level result.  The medal-level target is the combined theorem:

1. pretemporal anchoring plus regular flatness forces the empty horizon;
2. admitting noncommuting principal curvature yields all common-degree projective algebraic sets;
3. the scheme is reconstructed canonically by saturating the Kähler principal-symbol ideal, via
   `J_Kaehler = map_C(m^T I)` and `Sat_m(m^T I)=Sat_m(I)`;
4. the entire cyclic commuting annihilator lane is exactly the linear algebraic-direction phase,
   while the enlarged commuting lane is classified by nonlinear or prolongable/involutive horizon
   structures;
5. undecidability, singularity, and moduli phenomena transfer faithfully to the resulting
   classification of hypertranscendence horizons.

Only this rigidity/maximal-universality/reconstruction package clears the significance gate.  A
renaming of quiver universality does not.

The first exact boundary inside item 4 is now formalized at the level of actual differential
algebraicity.  For every commutative cyclic law quotient, the full iterated jet of one root
observable is algebraically dependent exactly on the inverse image of the algebraic elements of the
quotient and is therefore a vector subspace.  The nonlinear crossing `c_0 c_1 = 0` is impossible in
that lane but is an exact complete-jet dependence horizon in the free noncommuting realization.
This proves that changing the annihilator, even by nonhomogeneous or nonreduced terms, cannot create
a nonlinear horizon.  A nonlinear commuting theory must instead introduce nonlinear action,
interacting sectors, gauge syzygies, or a prolonged complex; the theorem does not yet classify
those enlarged carriers.

## 6. Physics interpretation `[CONJECTURE]`

If law space is the projectivization of constraint-compatible derivations of a QFT observable
algebra, `(2)` says that hypertranscendence alone places no a priori restriction on the algebraic
shape of the holographic horizon: singular curves, higher-genus varieties, reducible phase walls,
nonreduced collision strata, and moduli-like components can all arise from linear superposition of
derivations. The attempted abelian strengthening instead identifies a sharper QFT constraint:
commuting creation shifts generated from one cyclic law element can have only a projectively linear
complete horizon, independent of the annihilator. Cross-derivative compatibility forces correlated
descendant sectors. Ward identities, gauge constraints, or equations of motion are possible
physical analogues of the required nonlinear/prolongation structure, but no such identification is
proved.

This is a mathematical realization theorem, not a claim that every projective variety is physically
realized. A physical paper must identify which derivation pencils arise from locality, gauge
constraints, positivity, and renormalization.

## 7. Novelty gate

Exact searches found realization theorems for quiver Grassmannians and rank varieties, and extensive
jet-differential literature, but no statement that every projective variety occurs as the ordinary
differential-dependence locus of one element under a linear pencil of derivations. This remains an
absence-of-hit verdict. The dangerous parent theories are:

- Reineke, *Every projective variety is a quiver Grassmannian* (2012), because `(3)` has a
  word-quiver presentation;
- Sidman--Smith, *Linear determinantal equations for all projective schemes* (2011), because the
  Kähler wedge horizon is a determinantal/Plücker degeneracy scheme;
- Jorgensen, *Rank varieties over the generic hypersurface I* (2026), which realizes every
  projective variety as a module rank variety;
- universal realization in differential algebra and differential schemes;
- noncommutative realization/recognizable-series theory;
- jet-scheme and Wronskian degeneracy loci;
- Janet--Riquier completion, Spencer symbol prolongation, and formal integrability for the commuting
  obstruction.
- locally algebraic operators and Chitayat--Daigle--Regeta, *Locally finite sets of derivations*
  (2026), because local finiteness of operator families is the closest active parent theory to the
  cyclic algebraic-direction subspace.

None of those sources found in the exact audit treats the varying-derivation ordinary
hypertranscendence locus of one field element.  Nevertheless the realization motif is emphatically
known. The free realization theorem is Fields-level only if the full converse and Kähler-ideal
reconstruction survive and consequences arise that are not obtained by translating an existing
quiver, determinantal, or rank-variety universality theorem. The abelian lane now has a different
gate: classify the prolonged modules that escape the free-tail no-go.

## 8. RH impact

The theorem would show that the geometry of a directional DA horizon alone cannot select the zeta
zero locus: arbitrary projective algebraic geometry can be engineered in a free differential field.
An RH route therefore needs arithmetic constraints on the derivations/source, not horizon topology
alone. This is a strong anti-redressing constraint, not an RH proof.

## 9. Formalization gates

- [x] formalize ordered-word coefficient realization of a common-degree homogeneous family
- [x] construct the finite prefix/terminal polynomial derivations
- [x] extend them unconditionally to the fraction field
- [x] prove the exact finite prefix and arbitrary homogeneous top-jet formulas
- [x] prove disjoint-block linear-form algebraic independence
- [x] prove the exact finite-packet dependence locus for arbitrary ordered-word coefficients
- [x] add the infinite free tail and prove the complete-jet formula `(5)`
- [x] prove the complete-jet equivalence `(6)` for arbitrary word-homogeneous equations
- [x] formalize common-degree reduction `(7)`
- [x] prove the first-prolongation identity forced by commuting derivations
- [x] prove a free algebraically independent terminal tail forces the commuting symbol to vanish
- [ ] construct a non-free formally integrable prolongation module, or prove a stronger no-go
- [x] prove the cyclic commuting finite-annihilation horizon is linear
- [x] prove homogeneous mixed-order linear relations collapse to the radical horizon
- [x] construct the induced commuting derivations on the symmetric observable domain
- [x] identify their actual complete directional orbit with the cyclic law-power observable jet
- [x] classify the full cyclic differential-algebraic horizon as the radical subspace
- [x] remove homogeneity and identify the full horizon with the algebraic-element subspace
- [x] prove the general algebraic-direction principle for arbitrary commutative algebras and linear
      law maps
- [x] exhibit a nonlinear complete-jet horizon separating free and cyclic commuting law space
- [x] prove the general free-realizable/cyclic-impossible theorem for every non-subspace finite
      homogeneous zero cone
- [ ] combine with the existing projective-algebraicity theorem for the iff classification
- [x] define the general top-principal-symbol product ideal
- [x] prove `J_symbol = m^T I` and projective removal of the irrelevant factor
- [x] identify every actual Kähler wedge coordinate with its maximal Jacobian minor
- [x] prove the exact block-minor and Kähler coefficient-ideal factorization
- [x] prove scalar saturation recovery `Sat_m(J_symbol) = Sat_m(I)`
- [ ] package saturation recovery as an explicit `Proj` scheme isomorphism
- [ ] derive the flat-rigidity/curved-universality dichotomy from pretemporal anchor rigidity
- [x] run targeted builds and axiom audit for the set theorem, symbol theorem, and commuting no-go
- [ ] complete an independent expert literature audit

Current unconditional Lean surface:

- `AlgebraicIndependentDisjointLinearForms.lean`
  - `algebraicIndependent_disjointBlockLinearForms`
- `DirectionalProjectiveVarietyRealization.lean`
  - `directionalWordDerivative_projectiveWordRoot_of_lt`
  - `directionalWordDerivative_projectiveWordRoot_of_eq`
  - `directionalJet_projectiveWordRoot_of_eq`
  - `projectiveFiniteJetPacket_algebraicIndependent_iff`
  - `projectiveFiniteJetPacket_dependent_iff`
- `DirectionalProjectiveCompleteRealization.lean`
  - `directionalJet_projectiveCompleteRoot_add`
  - `projectiveCompleteJetPacket_algebraicIndependent`
  - `projectiveCompleteJet_algebraicIndependent_iff`
  - `projectiveCompleteJet_dependent_iff_lawPolynomials_zero`
- `DirectionalWordPolynomialSurjectivity.lean`
  - `exists_wordCoefficients_sum_eq_homogeneousPolynomial`
  - `exists_projectiveWordCoefficients_lawPolynomials_eq`
  - `exists_completeJet_horizon_eq_homogeneousZeroLocus`
- `GeneralPrincipalSymbolHorizonIdeal.lean`
  - `generalPrincipalSymbolIdeal_eq_irrelevantPow_mul`
  - `eval_principalSymbolProducts_zero_iff`
  - `projective_zeroLocus_irrelevantPow_mul`
- `GeneralKaehlerPrincipalSymbol.lean`
  - `polynomialKaehlerWedge_coordinate`
  - `polynomialKaehlerCoefficientIdeal_eq_jacobianMinorIdeal`
  - `universalLinearJetKaehlerCoefficientIdeal_eq_map_minorIdeal`
- `BlockKaehlerPrincipalSymbol.lean`
  - `universalLinearJetMinorIdeal_le_prod_rowIdeals`
  - `blockDiagonalLinearJetMinorIdeal_eq_prod_rowIdeals`
  - `blockDiagonalLinearJetKaehlerCoefficientIdeal_eq_map_prod_rowIdeals`
- `FreeKaehlerHorizonScheme.lean`
  - `pretemporalPrincipalLowerRowIdeal`
  - `pretemporalPrincipalRowIdealProduct`
  - `freePretemporalPrincipalMinorIdeal_eq_generalPrincipalSymbolIdeal`
  - `freePretemporalPrincipalKaehlerCoefficientIdeal_eq_map_generalPrincipalSymbolIdeal`
  - `freePretemporalPrincipalMinorIdeal_saturation`
  - `freePretemporalPrincipal_saturatedScheme_eq_iff`
- `IdealPowerSaturation.lean`
  - `idealPowerSaturation_pow_mul`
- `CommutingPrincipalSymbolProlongation.lean`
  - `commutingDerivations_principalSymbol_firstProlongation`
  - `commutingDerivations_freeTail_forces_zeroSymbol`
  - `commutingDerivations_algebraicallyIndependentTail_forces_zeroSymbol`
- `SymmetricAlgebraAlgebraicIndependence.lean`
  - `symmetricAlgebra_ι_algebraicIndependent_iff_linearIndependent`
- `SymmetricAlgebraDerivation.lean`
  - `symmetricAlgebraDerivation_ι`
  - `symmetricAlgebraDerivation_commute`
- `CommutingCyclicObservableHorizon.lean`
  - `homogeneous_cyclicSymmetricObservableJet_algebraicIndependent_iff`
  - `not_algebraicIndependent_commutingCyclicObservableJet_iff`
- `CommutingCyclicDifferentialObservable.lean`
  - `cyclicLawDerivation_commute`
  - `cyclicDirectionalJet_eq_observableJet`
  - `not_algebraicIndependent_cyclicDirectionalJet_iff`
  - `cyclicDifferentialDependenceHorizon_eq_radicalSubspace`
  - `crossingCone_not_cyclicDifferentialDependenceHorizon`
- `AlgebraicDirectionHorizon.lean`
  - `linearIndependent_powers_iff_transcendental`
  - `symmetricPowerObservable_algebraicIndependent_iff_transcendental`
  - `symmetricPowerObservable_dependenceHorizon_eq`
- `CommutingCyclicAlgebraicHorizon.lean`
  - `not_algebraicIndependent_cyclicDirectionalJet_iff_algebraicHorizon`
  - `cyclicDifferentialDependenceHorizon_eq_algebraicSubspace`
  - `commutingCyclicAlgebraicHorizon_eq_nilpotenceHorizon`
  - `crossingHorizon_free_realizable_cyclicAlgebraic_impossible`
- `FreeCommutingHorizonPhaseBoundary.lean`
  - `nonlinearProjectiveHorizon_free_realizable_cyclicCommuting_impossible`
- `DirectionalProjectiveZeroLocusRealization.lean`
  - `commonDegreeLift_isHomogeneous`
  - `commonDegreeLift_zero_iff`
  - `exists_completeJet_horizon_eq_finiteHomogeneousZeroLocus`
