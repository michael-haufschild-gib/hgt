# Unconditional Lean capstone for the all-order multiple-elliptic-gamma structural matroid

- **ID:** `all-order-multiple-elliptic-gamma-structural-matroid-lean-capstone`
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean target)
- **Scientific status:** `[FORMALIZATION REQUIRED FOR FINAL PROOF]`
- **Parent:** `all-order-multiple-elliptic-gamma-structural-differential-matroid`
- **Statement:** Formalize without project axioms the concrete all-order additive and
  multiplicative differential-transcendence-rank formulas for generic multiple elliptic gamma.

## Completion criterion

This card closes only when the Lean tree contains the actual multiple elliptic gamma function, its
logarithmic derivative and hierarchy equations, and a theorem equivalent to

```text
dtrdeg_(C(z)) C(z)<P_1(T)Psi_r,...,P_m(T)Psi_r>_delta
  =dim_(C(delta)) span{Pbar_1,...,Pbar_m}
```

for every generic order and every finite structural operator family, together with the
multiplicative product theorem. A theorem parameterized by assumptions that merely restate
elliptic-gamma atomicity, simultaneous telescoping, or the desired independence conclusion does
not satisfy this criterion.

## Formal dependency order

1. differential polynomial evaluation, DA extensions, differential independence, and differential
   transcendence degree;
2. commuting difference-differential fields, universal Kähler differentials, and
   semilinear circuit descent;
3. the unconditional additive simultaneous telescoping theorem and its all-jet
   differential-independence contrapositive;
4. meromorphic functions with periods, nondiscrete-period constancy, elliptic curves, elliptic
   function fields, and specialization from a product;
5. theta functions, elliptic gamma, multiple elliptic gamma, and all hierarchy identities;
6. non-torsion elliptic translation orbits, principal parts, and orbital residue obstruction;
7. generic order-one defect-coset atomicity;
8. free differential-shift one-slice nonsummability and nested-star orbit gluing;
9. localized Stanley--Reisner decomposition and the differential-linear rank theorem;
10. all-order additive capstone and multiplicative logarithmic-derivative transfer.

## Current unconditional Lean evidence

`formal/GaloisForLFunctions/SimplicialConstraintTower.lean` proves:

```text
pureOfCard_uniformFacets
ridgeThick_uniformFacets
exists_two_coface_directions_of_pure_ridgeThick
```

`formal/GaloisForLFunctions/DifferentialIndependence.lean` now supplies the field-relative
definitions needed by the actual matroid theorem:

```text
DifferentialIndependent
DifferentialAlgebraicOver
HypertranscendentalOver
```

It proves injective-subfamily preservation, ordinary algebraic independence of order-zero
coordinates, stability under arbitrary per-coordinate derivative shifts, and preservation under
ordinary algebraic scalar extension. It also constructs `differentialAdjoin` as the field generated
by every jet, proves that this field is derivation-closed, and proves its minimality among
derivation-closed intermediate fields.

Both modules build under the repository toolchain. `#print axioms` for their principal theorems
reports only `propext`, `Classical.choice`, and `Quot.sound`.

`formal/GaloisForLFunctions/PeriodRigidity.lean` proves two constant-field cores. A continuous
function invariant under a dense additive subgroup is constant. More importantly, a
complex-differentiable function invariant under a sequence of nonzero periods tending to zero is
constant; this covers nondiscrete period groups whose closure is not all of `ℂ`. The remaining
meromorphic step is also proved for `MeromorphicNFOn`: translation invariance preserves
meromorphic order, isolated poles cannot recur along periods tending to zero, and the resulting
pole-free function reduces to the differentiable theorem.

`formal/GaloisForLFunctions/RankThreePeriods.lean` proves that the integer span of three
`Q`-linearly independent complex periods is nondiscrete, extracts nonzero periods converging to
zero, and composes this with normal-form meromorphic rigidity. Thus the analytic joint-constant
collapse used by the paired system is now unconditional in Lean. Normal-form function-field
packaging remains.

`formal/GaloisForLFunctions/OrbitResidueVector.lean` strengthens the earlier single-orbit integer
augmentation lemma to coefficient-valued residue vectors on every orbit of an arbitrary
translation action. Every finite translation coboundary has zero residue on every orbit, while a
lone nonzero coefficient or two opposite coefficients on distinct orbits cannot be a coboundary.
This is the exact finite principal-part obstruction required after a meromorphic elliptic function
has been mapped to its fixed-order Laurent coefficients.

`formal/GaloisForLFunctions/PrincipalPartDifferentialOperator.lean` computes the action of an
arbitrary nonzero constant-coefficient differential operator on a simple-pole principal part. In
characteristic zero the highest resulting Laurent coefficient is the original residue multiplied
by a nonzero factorial and the operator's leading coefficient. Consequently two opposite simple
poles on distinct translation orbits remain noncoboundary after every nonzero differential
operator. The finite-family strengthening is also formal: if one indexed pole orbit is disjoint
from the common base orbit and every other indexed pole orbit, its nonzero operator term prevents
the entire simultaneous family from being a coboundary. This is the exact local obstruction used
in the defect-matroid independence argument, not only the one-defect spectrum argument.

`formal/GaloisForLFunctions/EllipticOrbitQuotient.lean` now identifies the orbit quotient of
`G/H` under translation by `q` with the subgroup condition in `G`: two representatives have
distinct orbit classes exactly when their difference is outside `H ⊔ ℤq`. In particular, the
paper's elliptic nonresonance condition `h ∉ Λ + ℤq` is formally equivalent to distinctness of
the pole classes represented by `0` and `-h`. Thus the lattice-to-orbit-residue passage is no
longer an informal step. The meromorphic principal-part map and theta realization are still
missing.

`formal/GaloisForLFunctions/DifferenceDifferential.lean` defines several commuting field
automorphisms which fix the coefficient field and commute with the derivation. It proves that
constant-coefficient differential operators commute with all difference defects, that compatible
primitive systems satisfy the pairwise cocycle equations, and that one differential-linear
relation yields one common primitive in every simultaneous telescoping equation.

`formal/GaloisForLFunctions/FractionRingDerivation.lean` constructs the extension of an arbitrary
derivation through a fraction field by lifting its square-zero graph. Together with a
transcendence-basis extension and formally étale base change,
`formal/GaloisForLFunctions/KaehlerKernel.lean` proves in characteristic zero the exact field
theorem

```text
KaehlerDifferential.D K L g = 0 ↔ IsAlgebraic K g.
```

`formal/GaloisForLFunctions/ElementaryOstrowski.lean` combines this kernel theorem with the
semilinear least-support Kähler circuit descent. Algebraic dependence of additive primitives now
unconditionally produces a nonzero joint-constant finite linear combination of the increment
cocycles that is the coboundary of one and the same base element in every automorphism direction.
Applying the theorem to the full jet family gives the exact contrapositive needed here: absence of
all finite simultaneous jet telescopers implies differential algebraic independence. This closes
the algebraic several-automorphism dependence-to-telescoping gate without a PPV construction.

`formal/GaloisForLFunctions/DifferentialPolynomialOver.lean` supplies the total differential
polynomial derivation over a nonconstant differential base: coefficients are differentiated while
formal jets are shifted. Evaluation intertwines this derivation, so the relation ideal over the
base field is a differential ideal. Differential independence is now proved equivalent to
triviality of this full base-relative relation ideal.

`formal/GaloisForLFunctions/ParameterizedPrimitiveAction.lean` constructs the semilinear affine
action belonging to a compatible additive cocycle, including its inverse. The action commutes with
the total derivation; compatible cocycles give commuting actions. For an actual primitive system in
a difference-differential extension, evaluation intertwines the formal affine action with the
extension automorphism. Hence differential dependence produces a nonzero proper differential
relation ideal invariant under every affine action. No PPV or Galois conclusion is assumed in this
theorem.

`formal/GaloisForLFunctions/ParameterizedPrimitiveMaximalIdeal.lean` proves the Zorn existence
step: every proper affine differential ideal lies in a maximal proper affine differential ideal.
Applied to an actual dependent primitive tuple, its nonzero relation ideal embeds in such a
maximal ideal. `formal/GaloisForLFunctions/ParameterizedPrimitiveQuotient.lean` descends the total
derivation and all affine actions to the quotient, proves that they commute, constructs the
universal primitive tuple there, and proves the quotient is affine-differentially simple. This is
the additive unipotent PPV quotient-ring construction. Its translation torsor and Galois
correspondence remain incomplete, but they are no longer dependencies of the present route because
the elementary Kähler proof supplies the required simultaneous telescoping theorem directly.

`formal/GaloisForLFunctions/DifferentialPolynomial.lean` now constructs the constant-coefficient
differential polynomial ring as a polynomial ring on formal jets, proves that jet evaluation
commutes with derivation, and gives relation ideals their differential structure. It also defines
the additive Hopf comultiplication. The characteristic-zero primitive classification is complete:
folding `P(X+Y)` along `Y=X` gives `P(2X)=2P(X)`, coefficient comparison forces every supported
monomial to have total jet-degree one, and every primitive is reconstructed as an explicit finite
constant-coefficient sum of jets.

`formal/GaloisForLFunctions/DifferentialHopfIdeal.lean` and
`formal/GaloisForLFunctions/DifferentialHopfPrimitive.lean` close the existence direction. Additive
comultiplication makes a Hopf ideal stable under doubling. A least-total-degree nonzero relation is
homogeneous; first-order extraction at the additive identity sends its right partial derivatives
back into the same ideal. In characteristic zero a degree-at-least-two relation has a nonzero
partial derivative of smaller degree, a contradiction. Thus every nonzero additive differential
Hopf ideal contains an explicit nonzero finite constant-coefficient linear combination of jets.
This remains independent reusable PPV infrastructure; the Kähler circuit route bypasses it for the
present primitive-independence theorem.

This is the first real dependency of the strengthened theorem. It is not evidence that the
analytic capstone is already formalized.

## Gates

- [x] exact final theorem and anti-shell completion criterion recorded
- [x] first generalized combinatorial dependency implemented and built
- [x] field-relative differential independence and jet-family core implemented and built
- [x] continuous dense-period subcase implemented and built
- [x] differentiable small-period constancy theorem implemented and built
- [x] meromorphic-normal-form small-period constancy theorem implemented and built
- [x] rank-three nondiscreteness, small-period extraction, and meromorphic constancy implemented
- [x] commuting difference-differential field and common-telescoper algebraic interface implemented
- [x] total differential-polynomial derivation and base-relative relation ideal implemented
- [x] commuting affine primitive actions and invariant nontrivial relation ideal implemented
- [x] maximal proper affine differential ideal and simple universal quotient implemented
- [x] coefficient-valued multi-orbit finite coboundary obstruction implemented
- [x] nonzero differential operators preserve the top simple-pole obstruction
- [x] simultaneous distinct-orbit differential pole families are noncoboundaries
- [x] lattice-plus-shift nonresonance identified with distinct elliptic translation orbits
- [x] differential-polynomial relation ideals and characteristic-zero primitive classification
- [x] characteristic-zero additive differential Hopf-ideal primitive-existence theorem
- [ ] complete differential algebra foundation, including differential transcendence degree
- [x] unconditional multi-automorphism dependence-to-telescoping foundation
- [x] unconditional simultaneous telescoping and all-jet independence contrapositive
- [ ] meromorphic and elliptic function-field foundation
- [ ] theta and multiple-elliptic-gamma definitions and hierarchy
- [ ] orbit-principal-part obstruction
- [ ] generic order-one atomic theorem
- [ ] abstract all-order independence induction
- [ ] Stanley--Reisner differential-rank theorem
- [ ] concrete additive and multiplicative capstones
- [x] `scripts/formal_tools.py lint` passes for the current tree
- [ ] exact capstone `#print axioms` contains only standard Lean axioms

## Log

- 2026-07-10 -- Opened after the paper theorem passed adversarial audit. The user criterion makes
  full unconditional Lean formalization, rather than a paper proof or hypothesis shell, the final
  proof standard.
- 2026-07-10 -- Formalized the pure ridge-thick two-coface theorem and the uniform-skeleton
  instance as the first dependency of the stronger constraint-tower theorem.
- 2026-07-10 -- Corrected rank-three density to nondiscreteness and formalized the exact
  small-period meromorphic constant collapse.
- 2026-07-10 -- Formalized the multi-automorphism difference-differential interface and the
  common-primitive consequence of a differential-linear relation; the hard converse PPV theorem
  remains open.
- 2026-07-10 -- Formalized additive differential-polynomial Hopf structure and proved without
  project axioms that every primitive polynomial in characteristic zero is a finite
  constant-coefficient linear combination of jets.
- 2026-07-10 -- Proved the converse Hopf-ideal core without project axioms: every nonzero additive
  differential Hopf ideal in characteristic zero contains a nonzero finite
  constant-coefficient linear jet relation. The remaining simultaneous-telescoping gap is now the
  PPV ring, its Galois correspondence, fixed-field descent, and application to the compatible
  primitive system, not Cassidy's additive-subgroup classification.
- 2026-07-10 -- Exact builds of `DifferentialPolynomial`, `DifferentialHopfIdeal`, and
  `DifferentialHopfPrimitive` pass. Their capstone axiom reports contain only `propext`,
  `Classical.choice`, and `Quot.sound`; the repository formal lint also passes.
- 2026-07-10 -- Formalized the total differential-base polynomial derivation and the complete
  semilinear affine action of a compatible several-automorphism primitive system. Evaluation now
  intertwines the action in an actual extension, and a dependent primitive tuple unconditionally
  yields a nonzero proper differential relation ideal invariant under every affine action. Exact
  builds pass and the new capstones use only `propext`, `Classical.choice`, and `Quot.sound`.
- 2026-07-10 -- Completed the maximal-invariant-ideal and quotient-ring steps for the additive
  unipotent PPV construction. Zorn gives a maximal proper affine differential ideal above the
  actual relation ideal; the quotient inherits commuting difference actions and the total
  derivation, contains the universal primitive tuple, and is affine-differentially simple. The
  torsor/Galois group, joint-constant theorem, and fixed-field descent remain open.
- 2026-07-10 -- Formalized coefficient-valued orbit-residue vectors for arbitrary translation
  actions. Finite coboundaries vanish orbitwise, and one nonzero principal-part coefficient or two
  opposite coefficients on distinct orbits are formally excluded. The remaining analytic task is
  to construct the elliptic meromorphic principal-part map and realize the theta defects in it.
- 2026-07-10 -- Formalized the exact lattice/orbit bridge and the differential-operator stability
  of the principal-part obstruction. The generic hypothesis `h ∉ Λ + ℤq` now yields distinct pole
  orbits in Lean, and every nonzero constant-coefficient differential operator preserves a
  noncoboundary top Laurent coefficient. Exact targeted builds pass without project axioms.
- 2026-07-10 -- Strengthened the local obstruction from one defect to an arbitrary finite family.
  A single nonzero operator attached to a pole class distinct from the base and every other class
  forces the complete family outside the finite coboundary image. Combined with the nested orbit
  quotient theorem, pairwise distinct nonzero classes modulo `Λ + ℤq` now give the simultaneous
  obstruction required by the exact differential-transcendence-rank proof.
- 2026-07-11 -- Replaced the open PPV/Galois dependence-to-telescoping step by an elementary
  characteristic-zero Kähler proof. The fraction-field derivation, Kähler-kernel theorem,
  simultaneous several-automorphism Ostrowski theorem, and its all-jet differential-independence
  contrapositive all build unconditionally. The remaining capstone gap is analytic realization:
  meromorphic function fields, theta and multiple elliptic gamma, principal-part extraction, and
  the hierarchy/rank assembly.
