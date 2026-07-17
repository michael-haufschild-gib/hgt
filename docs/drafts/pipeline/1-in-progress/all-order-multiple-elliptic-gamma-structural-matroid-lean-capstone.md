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

`formal/GaloisForLFunctions/HTGeometry/SimplicialConstraintTower.lean` proves:

```text
pureOfCard_uniformFacets
ridgeThick_uniformFacets
exists_two_coface_directions_of_pure_ridgeThick
```

`formal/GaloisForLFunctions/HTGeometry/DifferentialIndependence.lean` now supplies the field-relative
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

`formal/GaloisForLFunctions/HTGeometry/PeriodRigidity.lean` proves two constant-field cores. A continuous
function invariant under a dense additive subgroup is constant. More importantly, a
complex-differentiable function invariant under a sequence of nonzero periods tending to zero is
constant; this covers nondiscrete period groups whose closure is not all of `ℂ`. The remaining
meromorphic step is also proved for `MeromorphicNFOn`: translation invariance preserves
meromorphic order, isolated poles cannot recur along periods tending to zero, and the resulting
pole-free function reduces to the differentiable theorem.

`formal/GaloisForLFunctions/HTGeometry/RankThreePeriods.lean` proves that the integer span of three
`Q`-linearly independent complex periods is nondiscrete, extracts nonzero periods converging to
zero, and composes this with normal-form meromorphic rigidity. Thus the analytic joint-constant
collapse used by the paired system is now unconditional in Lean. Normal-form function-field
packaging remains.

`formal/GaloisForLFunctions/HTGeometry/OrbitResidueVector.lean` strengthens the earlier single-orbit integer
augmentation lemma to coefficient-valued residue vectors on every orbit of an arbitrary
translation action. Every finite translation coboundary has zero residue on every orbit, while a
lone nonzero coefficient or two opposite coefficients on distinct orbits cannot be a coboundary.
This is the exact finite principal-part obstruction required after a meromorphic elliptic function
has been mapped to its fixed-order Laurent coefficients.

`formal/GaloisForLFunctions/HTGeometry/PrincipalPartDifferentialOperator.lean` computes the action of an
arbitrary nonzero constant-coefficient differential operator on a simple-pole principal part. In
characteristic zero the highest resulting Laurent coefficient is the original residue multiplied
by a nonzero factorial and the operator's leading coefficient. Consequently two opposite simple
poles on distinct translation orbits remain noncoboundary after every nonzero differential
operator. The finite-family strengthening is also formal: if one indexed pole orbit is disjoint
from the common base orbit and every other indexed pole orbit, its nonzero operator term prevents
the entire simultaneous family from being a coboundary. This is the exact local obstruction used
in the defect-matroid independence argument, not only the one-defect spectrum argument.

`formal/GaloisForLFunctions/HTGeometry/EllipticOrbitQuotient.lean` now identifies the orbit quotient of
`G/H` under translation by `q` with the subgroup condition in `G`: two representatives have
distinct orbit classes exactly when their difference is outside `H ⊔ ℤq`. In particular, the
paper's elliptic nonresonance condition `h ∉ Λ + ℤq` is formally equivalent to distinctness of
the pole classes represented by `0` and `-h`. Thus the lattice-to-orbit-residue passage is no
longer an informal step. Theta realization is now complete; the remaining local gap is a
functorial meromorphic principal-part map for arbitrary elliptic coboundaries.

`formal/GaloisForLFunctions/HTGeometry/DifferenceDifferential.lean` defines several commuting field
automorphisms which fix the coefficient field and commute with the derivation. It proves that
constant-coefficient differential operators commute with all difference defects, that compatible
primitive systems satisfy the pairwise cocycle equations, and that one differential-linear
relation yields one common primitive in every simultaneous telescoping equation.

`formal/GaloisForLFunctions/HTGeometry/FractionRingDerivation.lean` constructs the extension of an arbitrary
derivation through a fraction field by lifting its square-zero graph. Together with a
transcendence-basis extension and formally étale base change,
`formal/GaloisForLFunctions/HTGeometry/KaehlerKernel.lean` proves in characteristic zero the exact field
theorem

```text
KaehlerDifferential.D K L g = 0 ↔ IsAlgebraic K g.
```

`formal/GaloisForLFunctions/HTGeometry/ElementaryOstrowski.lean` combines this kernel theorem with the
semilinear least-support Kähler circuit descent. Algebraic dependence of additive primitives now
unconditionally produces a nonzero joint-constant finite linear combination of the increment
cocycles that is the coboundary of one and the same base element in every automorphism direction.
Applying the theorem to the full jet family gives the exact contrapositive needed here: absence of
all finite simultaneous jet telescopers implies differential algebraic independence. This closes
the algebraic several-automorphism dependence-to-telescoping gate without a PPV construction.

`formal/GaloisForLFunctions/HTGeometry/AutomorphismFamilyOstrowski.lean` proves that pairwise commutativity is
not needed. The same simultaneous single-base-element conclusion and all-jet criterion hold for an
arbitrary family of compatible automorphisms, even an infinite noncommuting family. The elliptic
gamma shifts are therefore a commuting specialization of a strictly stronger formal theorem.

`formal/GaloisForLFunctions/HTGeometry/MeromorphicDifferentialField.lean` reuses the genuine meromorphic germ
field `Bottcher.meroField U`, differentiates analytic germs on an open set, proves the additive and
Leibniz laws, and extends the derivation through the fraction field by the quotient rule.
`formal/GaloisForLFunctions/HTGeometry/MeromorphicTranslation.lean` then lifts every translation
`z ↦ z + q` to a field automorphism of `meroField univ` and proves that it commutes with this
derivation. Thus the concrete global meromorphic difference-differential carrier now exists. The
remaining field-level tasks are to identify the common fixed field of a generic rank-three
translation family with the constants and to realize theta and elliptic-gamma elements and their
divisors in the carrier.

`formal/GaloisForLFunctions/HTGeometry/MeromorphicTranslationFixedField.lean` now closes the first of those
tasks. A fraction of entire analytic germs fixed by arbitrarily small nonzero translations has
zero quotient-rule Wronskian: translation invariance kills its difference quotients wherever the
denominator is nonzero, and analytic continuation makes the Wronskian vanish globally. The
quotient is then locally constant and the identity theorem makes it globally constant. Combining
this with `exists_small_rankThree_periods` proves that the common fixed field of the full integer
span of three `Q`-linearly independent complex translations is exactly the embedded complex
constant field. No fixed-field assumption remains at the global meromorphic carrier level.

`formal/GaloisForLFunctions/HTGeometry/MeromorphicTheta.lean` embeds the actual Jacobi theta function and its
`z`-derivative as analytic germs and defines their logarithmic derivative in the meromorphic
fraction field. The exact translation laws are formal field identities:

```text
phi(z + 1)   = phi(z),
phi(z + tau) = phi(z) - 2*pi*i.
```

Thus theta existence, analyticity, nonvanishing as a field denominator, and its two basic
functional equations are no longer assumptions.

`formal/GaloisForLFunctions/HTGeometry/JacobiThetaDivisor.lean` and
`formal/GaloisForLFunctions/HTGeometry/JacobiThetaDivisorSimple.lean` establish the expected theta lattice
orbit and its local divisor law. The exact
evenness, period, and quasiperiod constraints force the odd half-period `(1+tau)/2` to be a zero,
and every `Z + tau Z` translate is also a zero. Simplicity is proved globally without a product
formula: pair the defining derivative series under `n -> -n-1`, isolate the leading term `2*pi*i`,
bound the remaining Gaussian tail on `im tau >= 4/5`, and transport nonvanishing from the modular
fundamental domain through the exact `S` and `T` laws. Every lattice translate is therefore simple.
The normalized punctured limit

```text
(z-z0) theta'(z,tau)/theta(z,tau) -> 1
```

is proved at the half-period and at every lattice translate.

`formal/GaloisForLFunctions/HTGeometry/JacobiThetaRectangleCharge.lean` and
`formal/GaloisForLFunctions/HTGeometry/JacobiThetaExactDivisor.lean` close the converse without a product
formula. A translated axis-aligned rectangle of width `1` and height `im tau` has zero-free
boundary. Its vertical edges cancel by period one. On the top edge, translation by
`tau-re tau` and interval invariance of a one-periodic integral turn quasiperiodicity into the
exact charge `2*pi*i`. The existing axiom-clean rectangle residue theorem and finite analytic
peeling show that the rectangle contains total zero multiplicity one. Every lattice orbit meets
its interior, so the known simple half-period zero is the unique zero there. Lean now proves

```text
jacobiTheta₂ z tau = 0
  iff exists m n : Z, z = (1+tau)/2 + m + n*tau.
```

Thus the complete theta pole orbit and residue-one law are unconditional.

`formal/GaloisForLFunctions/HTGeometry/JacobiThetaDefectPrincipalPart.lean` now defines the translated
logarithmic-derivative defect

```text
phi(z+h)-phi(z),  phi=theta'/theta,
```

and proves its exact two-orbit local data whenever `h` is outside `Z+tau Z`: residue `-1` on the
base half-period lattice and residue `+1` on its translate by `-h`. Exact zero classification proves
the opposite summand is regular at each pole, so no hidden pole orbit remains.

`formal/GaloisForLFunctions/HTGeometry/MeromorphicThetaDefect.lean` realizes this same defect as an actual
element of the global meromorphic fraction field. It proves translation composition in the germ
and fraction carriers, supplies one explicit entire cross numerator and product denominator, and
proves that the fraction is fixed by both period translations `1` and `tau`. For every nonlattice
shift the field element is not merely nonzero but unequal to every embedded complex constant;
clearing a hypothetical constant identity and evaluating at the simple theta zero leaves a
nonzero product. Thus the analytic residue theorem and the genuine elliptic field element are now
about the same named object. The remaining order-one issue is to exclude this pole pattern from
the image of an arbitrary elliptic meromorphic translation coboundary and then instantiate the
actual elliptic-gamma defect identity.

`formal/GaloisForLFunctions/HTGeometry/MeromorphicPoleOrbitBoundary.lean` removes the proposed Laurent-
coefficient extraction from the order-one obstruction. For a meromorphic `g`, assume its pole
indices on one integer translation orbit are finite. If `g(z+q)-g(z)` had exactly one pole on that
orbit, the pole-index set of `g` would be nonempty. Its least pole index produces a pole one step
before the support, and its greatest pole index produces a pole at the final support point, because
at each boundary one summand is singular and the other is regular. These are distinct, a
contradiction. Lean proves this directly with `meromorphicOrderAt`. The remaining realization is
therefore finiteness of pole indices for a lattice-periodic meromorphic coboundary primitive.

`formal/GaloisForLFunctions/HTGeometry/JacobiThetaDefectMeromorphicOrder.lean` translates the previously
proved normalized limits into exact meromorphic orders. A general lemma shows that
`(z-p)f(z) -> c != 0` for a meromorphic `f` forces `ord_p(f)=-1`. Applied to both theta-defect
lattices, it proves exact simple poles there; exact theta zero classification and analytic division
prove the converse, so Lean now knows the complete pole set of the undifferentiated defect. The
next module propagates this exact support through arbitrary nonzero constant-coefficient
differential operators.

`formal/GaloisForLFunctions/HTGeometry/MeromorphicSimplePoleDifferentialOperator.lean` proves the required
propagation generically. The `j`th derivative of any meromorphic simple pole has exact order
`-(j+1)`. Hence a nonzero `L in C[delta]` has exact order `-(deg L+1)`: its leading derivative is
strictly more singular than every lower term and cannot cancel. Analyticity is preserved off the
original poles. Applied to the theta defect, this gives an exact iff theorem saying that
`L(phi(z+h)-phi(z))` has precisely the same two pole lattices and no others. The local
singleton-support side of the order-one obstruction is now complete.

`formal/GaloisForLFunctions/HTGeometry/JacobiThetaDifferentialOrbitObstruction.lean` combines exact
differentiated support with the coefficient-free boundary theorem. Under nontorsion of `q` modulo
`Z+Z tau` and nonresonance of `h` modulo `Z+Z tau+Zq`, the differentiated theta defect has exactly
one pole on its distinguished `q`-orbit. It therefore cannot equal `g(z+q)-g(z)` whenever the pole
indices of `g` on that orbit are finite.

`formal/GaloisForLFunctions/HTGeometry/CompactEllipticPoleFiniteness.lean` discharges that finiteness
hypothesis for every genuine elliptic meromorphic primitive. Fractional coordinates reduce the
orbit into a compact fundamental parallelogram; local finiteness of the native meromorphic divisor
makes its pole set there finite; and nontorsion makes orbit reduction injective. The resulting
theorem unconditionally excludes

```text
L(phi(z+h)-phi(z)) = g(z+q)-g(z)
```

for every nonzero `L in C[delta]` and every globally meromorphic `g` with periods `1,tau`. Thus the
local analytic noncoboundary theorem needed at order one is complete without a residue extractor or
a compactness assumption shell.

`formal/GaloisForLFunctions/HTGeometry/JacobiThetaFamilyOrbitObstruction.lean` strengthens the analytic
statement from one defect to every finite separated family. Choose any member whose operator is
nonzero. Pairwise nonresonance makes all other differentiated defects analytic on its shifted pole
orbit, while exact simple-pole differentiation makes the chosen member singular at precisely the
zero index. Compact elliptic pole finiteness and the boundary theorem then exclude a single
elliptic coboundary for the entire differential combination. This is the genuine analytic
finite-family input for the defect-coset matroid; it is no longer represented only by an abstract
principal-part vector theorem.

`formal/GaloisForLFunctions/HTGeometry/FiniteTypeSpecialization.lean` proves the product-specialization
descent used after simultaneous telescoping. For a finite-type domain `R` over an algebraically
closed field `C`, every nonzero element survives under some `C`-point of `R`; the proof localizes
away from that element and applies Nullstellensatz through a maximal quotient. A basis of the left
field then shows that every nonzero denominator in `A tensor_C R` survives some specialization of
the right factor. Finally, a cross-multiplied rational identity

```text
sigma(N) D - N sigma(D) = a sigma(D) D
```

specializes to an actual `u in A` with `sigma(u)-u=a`. Thus the generic algebraic descent from a
rational product certificate to one factor is unconditional and axiom-clean. What remains is the
concrete identification of the paired elliptic compositum with the relevant fraction field and the
actual multiple-elliptic-gamma hierarchy realization.

`formal/GaloisForLFunctions/HTGeometry/EllipticGammaLogKernel.lean` begins that actual realization from the
standard double-product logarithmic derivative, not from an assumed functional equation. It
defines the forward and backward rational atoms and proves exact finite telescoping under
`x -> p*x` and `x -> q*x`. In each direction the complete rectangular slice collapses to the
expected one-dimensional theta boundary plus two explicit terminal tails. This is the algebraic
source of the paired elliptic-gamma increment equations. The same module now proves that both
terminal tails tend to zero whenever the shifted nome has norm less than one. More strongly, it
proves absolute summability of both halves of the double kernel and of the full kernel, justifies
the required Fubini decomposition, defines the absolutely convergent one-dimensional theta-product
logarithmic kernel, and passes finite telescoping to the two genuine pointwise increment equations

```text
K(p,q;p*x)-K(p,q;x)=ThetaLog(q;x),
K(p,q;q*x)-K(p,q;x)=ThetaLog(p;x).
```

These are constructed identities, not assumed hierarchy axioms.
`EllipticGammaLogNormalConvergence.lean` then supplies an explicit two-index geometric Weierstrass
majorant and uniform convergence on every closed annulus `r <= |x| <= R`, `r > 0`. Thus normal
convergence on compact subsets of the punctured multiplicative plane is closed. The remaining
analytic comparison no longer requires formalizing the Jacobi triple product.
`EllipticThetaLogCoordinate.lean` uses
`x(tau,z)=-exp(pi*i*tau) exp(2*pi*i*z)` and proves that the additive normalization of `ThetaLog`
has exactly the period-one and period-`tau` quasiperiod laws of the existing analytic Jacobi-theta
logarithmic derivative. `EllipticThetaLogComparison.lean` therefore proves their discrepancy is
doubly periodic on the common regular locus. The identification is reduced to matching the
explicit pole divisor. `EllipticThetaCoordinateDivisor.lean` now proves the location statement
exactly: `x(tau,z)` belongs to the full integer nome orbit if and only if `z` belongs to the odd
half-period lattice, if and only if `jacobiTheta2(z,tau)=0`. The remaining local theorem is equality
of the normalized principal parts on that common divisor. This is now closed at the distinguished
half-period by `EllipticThetaLogPrincipalPart.lean`: the unique singular atom is isolated, both
infinite remainders are proved analytic at the nome by uniform geometric majorants, the exponential
coordinate derivative is nonzero, and the constructed additive kernel has normalized limit `1`.
`EllipticThetaLogComparison.lean` combines this with the analytic Jacobi-theta residue-one theorem
to prove the comparison discrepancy has normalized limit `0`. The remaining analytic step is to
package the constructed kernel meromorphically on the full plane. The regular base region is now
closed: `EllipticThetaLogFundamentalAnnulus.lean` proves the full constructed theta kernel analytic
at every `x` with `|q| < |x| < 1`, using a smaller closed annulus and explicit summable bounds for
both atom families. It remains to widen across the single fundamental pole using the principal-part
decomposition. That widening and global transport are now closed. On `|q|^2 < |x| < 1` the
remainder is analytic and the full kernel is meromorphic with only the isolated `x=q` atom;
`EllipticThetaLogNomeTransport.lean` proves meromorphicity invariant under `x -> q*x`, even at the
exceptional point by working on punctured germs; and `EllipticThetaLogGlobalMeromorphic.lean` uses
a minimal-power reduction to prove the multiplicative kernel meromorphic on all `C*` and its
aligned additive pullback meromorphic on all `C`. Thus the comparison discrepancy is globally
meromorphic. `MeromorphicNormalizedRemovable.lean` converts its zero normalized principal part to
nonnegative native meromorphic order at the half-period. It remains to transport removability over
the full lattice and conclude the elliptic discrepancy is constant. The resulting equality then
packages the constructed boundary in the existing global meromorphic field.

`formal/GaloisForLFunctions/HTGeometry/JacobiThetaParallelogramCharge.lean` proves the global constraint-side
counting input. On every zero-free fundamental boundary, the integral of the theta logarithmic
derivative is exactly `2*pi*i`: the period-one edges cancel and the quasiperiodic pair contributes
the single charge. This uses no product formula and no assumed divisor classification. The separate
axis-aligned rectangle argument above supplies the argument-principle bridge with the already
formalized rectangle residue theorem.

`formal/GaloisForLFunctions/HTGeometry/JacobiThetaBoundaryRegular.lean` discharges the contour-selection gate.
The fixed-parameter theta zero set is finite in every compact disc. Real coordinates in the basis
`(1,tau)` then permit a diagonal translate of the fundamental parallelogram whose bottom and left
edges avoid the finite zero set; periodicity and quasiperiodicity make the complete boundary
zero-free. No zero-set classification is assumed.

`formal/GaloisForLFunctions/HTGeometry/DifferentialPolynomialOver.lean` supplies the total differential
polynomial derivation over a nonconstant differential base: coefficients are differentiated while
formal jets are shifted. Evaluation intertwines this derivation, so the relation ideal over the
base field is a differential ideal. Differential independence is now proved equivalent to
triviality of this full base-relative relation ideal.

`formal/GaloisForLFunctions/HTGeometry/ParameterizedPrimitiveAction.lean` constructs the semilinear affine
action belonging to a compatible additive cocycle, including its inverse. The action commutes with
the total derivation; compatible cocycles give commuting actions. For an actual primitive system in
a difference-differential extension, evaluation intertwines the formal affine action with the
extension automorphism. Hence differential dependence produces a nonzero proper differential
relation ideal invariant under every affine action. No PPV or Galois conclusion is assumed in this
theorem.

`formal/GaloisForLFunctions/HTGeometry/ParameterizedPrimitiveMaximalIdeal.lean` proves the Zorn existence
step: every proper affine differential ideal lies in a maximal proper affine differential ideal.
Applied to an actual dependent primitive tuple, its nonzero relation ideal embeds in such a
maximal ideal. `formal/GaloisForLFunctions/HTGeometry/ParameterizedPrimitiveQuotient.lean` descends the total
derivation and all affine actions to the quotient, proves that they commute, constructs the
universal primitive tuple there, and proves the quotient is affine-differentially simple. This is
the additive unipotent PPV quotient-ring construction. Its translation torsor and Galois
correspondence remain incomplete, but they are no longer dependencies of the present route because
the elementary Kähler proof supplies the required simultaneous telescoping theorem directly.

`formal/GaloisForLFunctions/HTGeometry/DifferentialPolynomial.lean` now constructs the constant-coefficient
differential polynomial ring as a polynomial ring on formal jets, proves that jet evaluation
commutes with derivation, and gives relation ideals their differential structure. It also defines
the additive Hopf comultiplication. The characteristic-zero primitive classification is complete:
folding `P(X+Y)` along `Y=X` gives `P(2X)=2P(X)`, coefficient comparison forces every supported
monomial to have total jet-degree one, and every primitive is reconstructed as an explicit finite
constant-coefficient sum of jets.

`formal/GaloisForLFunctions/HTGeometry/DifferentialHopfIdeal.lean` and
`formal/GaloisForLFunctions/HTGeometry/DifferentialHopfPrimitive.lean` close the existence direction. Additive
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
- [x] arbitrary noncommuting automorphism-family strengthening
- [x] finite-type rational product-specialization descent to one factor
- [x] genuine meromorphic fraction field with quotient-rule derivation
- [x] complex translations lifted as differential-field automorphisms
- [x] rank-three translation fixed field identified with constants in the germ carrier
- [x] Jacobi theta and logarithmic derivative realized in the meromorphic carrier
- [x] theta `1`-periodicity and `tau`-quasiperiodicity proved as field identities
- [x] theta odd-half-period zero and full lattice zero orbit
- [x] global simplicity of every theta lattice zero
- [x] residue-one normalized logarithmic-derivative limit on the full lattice orbit
- [x] theta fundamental-parallelogram logarithmic-derivative charge `2*pi*i`
- [x] existence of a zero-free translated fundamental-parallelogram boundary
- [x] exact theta zero-set classification: no zeros outside the odd-half-period lattice orbit
- [x] exact two-orbit residue law for a nonlattice translated theta logarithmic-derivative defect
- [x] translated theta defect realized as a nonconstant doubly periodic meromorphic-field element
- [x] coefficient-free singleton-pole obstruction for finite meromorphic translation orbits
- [x] exact meromorphic-order classification of the two theta-defect pole lattices
- [x] exact differentiated theta-defect pole support for every nonzero `C[delta]` operator
- [ ] meromorphic and elliptic function-field foundation
- [x] theta and genuine parity-dependent all-order multiple-elliptic-gamma products, global
  meromorphic-field logarithmic derivatives, and every coordinate-deletion hierarchy equation
- [x] exact finite telescoping of the elliptic-gamma logarithmic-derivative double kernel
- [x] terminal-tail vanishing in both elliptic-gamma nome directions
- [x] absolute summability and Fubini decomposition of the full double kernel
- [x] both pointwise elliptic-gamma increment equations with convergent theta-product boundaries
- [x] uniform convergence of the full double kernel on every closed multiplicative annulus
- [x] exponential-coordinate period and quasiperiod laws for the constructed theta boundary
- [x] ellipticity of the constructed-versus-analytic theta-log discrepancy on the regular locus
- [x] exact alignment of the multiplicative nome orbit with the analytic Jacobi-theta divisor
- [x] residue-one normalized principal part for the constructed theta boundary at the half-period
- [x] vanishing normalized principal part of the constructed-versus-analytic discrepancy
- [x] analyticity of the constructed theta kernel on the pole-free fundamental annulus
- [x] one-pole meromorphicity on the wider fundamental annulus
- [x] bidirectional meromorphic transport under multiplication by the nome
- [x] global meromorphicity on `C*` and of the aligned additive pullback on `C`
- [x] native nonnegative meromorphic order of the comparison at the half-period
- [x] nonnegative comparison order on the full theta divisor and global pole-freeness
- [x] canonical comparison is entire, doubly periodic, and constant
- [x] constructed theta boundary equals analytic theta log derivative up to a constant
- [x] additive elliptic-gamma kernel and both polarized theta hierarchy equations
- [x] exact mixed gamma-face/theta-defect identity on the regular locus
- [x] elliptic finite-pole realization for arbitrary meromorphic elliptic coboundary primitives
- [x] unconditional differentiated theta-defect noncoboundary against every elliptic primitive
- [x] unconditional finite-family theta-defect noncoboundary for separated shift classes
- [x] generic order-one differential-linear atomic theorem for the actual product, including finite
  separated families and the free `C[delta]` matroid corollary
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
- 2026-07-11 -- Removed pairwise commutativity from the dependence-to-telescoping theorem entirely.
  The arbitrary-family and all-jet differential versions build in Lean; the elliptic-gamma paired
  shift theorem is now a specialization rather than the natural endpoint of the algebraic method.
- 2026-07-11 -- Reused the existing analytic-germ fraction field to construct the actual global
  meromorphic differential field. Translation precomposition now lifts to a fraction-field
  automorphism and is formally proved to commute with the quotient-rule derivation. This removes
  the carrier/existence part of the analytic gap; fixed-field identification and theta divisor
  realization remain.
- 2026-07-11 -- Proved the exact fixed-field theorem in the genuine carrier. Any meromorphic germ
  fixed by arbitrarily small nonzero translations is constant; hence the common fixed field of a
  generic rank-three translation lattice is precisely `C`. The remaining analytic obstruction is
  theta and elliptic-gamma realization with its orbitwise principal parts.
- 2026-07-11 -- Embedded the genuine Jacobi theta function, its derivative, and logarithmic
  derivative in the meromorphic fraction field. Proved its period-one invariance and the exact
  `tau`-shift defect `-2*pi*i`. The next missing order-one input is now solely divisor-level:
  theta's simple zero class and the induced simple-pole orbit residues of its log derivative.
- 2026-07-11 -- Proved the theta fundamental-parallelogram boundary charge directly from the period
  and quasiperiod constraints. This isolates the remaining exact-divisor task to a general
  parallelogram argument principle plus a zero-free boundary selection, without using the Jacobi
  triple product.
- 2026-07-11 -- Proved existence of a zero-free translated fundamental-parallelogram boundary.
  Compact-disc finiteness of the theta zero set and explicit `(1,tau)` coordinates reduce boundary
  avoidance to choosing one real diagonal shift outside a finite forbidden set. The only remaining
  theta zero-classification input is now the parallelogram argument principle itself.
- 2026-07-11 -- Closed the exact Jacobi-theta divisor gate unconditionally in Lean. The decisive
  route is an axis-aligned fundamental rectangle of width `1` and height `im tau`, not a skew
  parallelogram argument principle: period one cancels the vertical sides, quasiperiodicity plus
  invariance of a period-one interval integral gives charge `2*pi*i`, and the existing rectangle
  residue theorem plus finite peeling gives total multiplicity one. Lattice reduction then proves
  `theta(z,tau)=0 iff z=(1+tau)/2+m+n*tau`. The principal theorem and its zero-count dependencies
  report only `propext`, `Classical.choice`, and `Quot.sound`.
- 2026-07-11 -- Used the exact divisor to close the analytic principal-part data for a translated
  theta logarithmic-derivative defect. For every nonlattice shift `h`, Lean proves normalized
  punctured limits `-1` on the base half-period lattice and `+1` on the lattice translated by
  `-h`; exact zero classification proves the other summand is regular at each pole. Both residue
  theorems are axiom-clean. What remains is packaging these coefficients in the meromorphic germ
  field's orbit-residue map and connecting them to the elliptic-gamma hierarchy equation.
- 2026-07-11 -- Closed the analytic-function-to-meromorphic-field identity for the theta defect.
  `MeromorphicThetaDefect` proves that translations compose on both carriers, represents
  `phi(z+h)-phi(z)` by an explicit entire numerator/denominator pair, proves genuine `1`- and
  `tau`-periodicity, and excludes every constant value for a nonlattice shift by evaluation at the
  simple theta zero. Exact builds and axiom reports pass with only `propext`, `Classical.choice`,
  and `Quot.sound`. The remaining local gate is no longer identification of the defect itself; it
  is functorial extraction of fixed-order principal parts from arbitrary elliptic coboundaries.
- 2026-07-11 -- Replaced the remaining Laurent-coefficient extractor by a coefficient-free pole-
  support boundary theorem. A finite pole set on an integer translation orbit has a least and a
  greatest index; the shift coboundary has a pole at both induced boundaries, so it cannot have
  singleton pole support. `MeromorphicPoleOrbitBoundary` proves this with `meromorphicOrderAt`,
  builds exactly, and reports only standard Lean axioms. The residual analytic work is compact-
  elliptic finiteness plus exact differentiated theta-defect pole support.
- 2026-07-11 -- Converted the theta-defect residue limits into exact native meromorphic orders.
  `JacobiThetaDefectMeromorphicOrder` proves both lattice orbits have order `-1` and that every
  other point is analytic, hence supplies the complete pole set of the genuine analytic defect.
  Exact source/build checks and axiom reports pass. The remaining singleton-support input is now
  only its stability under a nonzero constant-coefficient differential operator.
- 2026-07-11 -- Closed differentiated theta-defect support for every nonzero
  constant-coefficient differential operator. A generic meromorphic theorem gives
  `ord_p(f^(j))=-(j+1)` at a simple pole and shows the highest nonzero differential term cannot
  cancel. The resulting theta theorem preserves exactly the two known pole lattices and no others.
  Builds and axiom reports pass; only finite pole support for an arbitrary elliptic coboundary
  primitive remains in the local obstruction.
- 2026-07-11 -- Closed the local analytic order-one obstruction without a finiteness hypothesis.
  `JacobiThetaDifferentialOrbitObstruction` first gives singleton pole support on the distinguished
  nontorsion orbit. `CompactEllipticPoleFiniteness` then reduces that orbit to fractional
  `(1,tau)` coordinates, uses compact finiteness of the native meromorphic divisor, and proves the
  reduction injective. Consequently no nonzero constant-coefficient differential operator applied
  to a nonresonant theta defect is a translation coboundary of any globally meromorphic elliptic
  primitive. Exact source/build checks pass and the capstones use only `propext`,
  `Classical.choice`, and `Quot.sound`. The next unresolved theorem is no longer local elliptic
  analysis; it is the actual multiple-elliptic-gamma hierarchy specialization and all-order rank
  assembly.
- 2026-07-11 -- Strengthened the completed local analytic obstruction from one theta defect to an
  arbitrary finite separated family. Any nonzero operator supplies a distinguished shifted pole;
  pairwise nonresonance makes every other family term analytic on that orbit, so the complete sum
  has singleton pole support there. `JacobiThetaFamilyOrbitObstruction` combines this with compact
  elliptic pole finiteness to rule out every elliptic translation coboundary. Exact builds pass and
  both family capstones report only `propext`, `Classical.choice`, and `Quot.sound`. This supplies
  the analytic family-level input needed by the defect matroid; product specialization remains the
  next bridge to the paired elliptic-gamma system.
- 2026-07-11 -- Closed the generic product-specialization descent unconditionally.
  `FiniteTypeSpecialization` uses localization plus Nullstellensatz to find a complex point avoiding
  any prescribed nonzero coefficient, lifts this to preservation of arbitrary nonzero tensor
  denominators via a basis of the left field, proves equivariance with the left automorphism, and
  specializes a cross-multiplied rational difference identity to an actual left-field coboundary.
  Exact builds pass and all three specialization capstones report only `propext`,
  `Classical.choice`, and `Quot.sound`. The remaining application is concrete rather than generic:
  present the paired elliptic compositum as the fraction field of the tensor coordinate domain and
  instantiate the actual elliptic-gamma hierarchy.
- 2026-07-11 -- Started the actual elliptic-gamma realization from its double-product logarithmic
  kernel. `EllipticGammaLogKernel` proves exact finite telescoping under both nome shifts: every
  finite slice reduces to the correct one-dimensional boundary and two terminal tails. Both
  capstones build with only standard Lean axioms. This is not an assumed hierarchy interface; it
  is the formula from which the hierarchy will follow after normal convergence and tail vanishing.
- 2026-07-11 -- Proved both terminal tails in the finite elliptic-gamma kernel identities tend to
  zero for nomes of norm less than one. The paired shift identities are therefore analytically
  reduced to normal convergence of the double sum and identification of the surviving
  one-dimensional boundary with a theta logarithmic derivative.
- 2026-07-11 -- Closed pointwise convergence and the two infinite order-one hierarchy equations.
  `EllipticGammaLogKernel` proves a general cofinite comparison theorem for the rational log atom,
  geometric absolute summability of both two-index argument families, absolute summability of the
  full kernel, and Fubini decomposition into nome fibers. Finite telescoping plus the vanishing
  tails then gives `K(p,q;p*x)-K(p,q;x)=ThetaLog(q;x)`; nome symmetry gives the polarized equation
  with `p` and `q` exchanged. The theta boundary is itself absolutely summable. The remaining
  analytic gate is uniform-on-compact convergence away from the polar divisor and identification
  with the existing analytic theta logarithmic derivative, not existence or pointwise convergence.
- 2026-07-11 -- Closed normal convergence on multiplicative annuli. The new
  `EllipticGammaLogNormalConvergence` module constructs separate forward and backward geometric
  majorants, proves both are summable on `N x N`, and applies an eventual Weierstrass bound to the
  rational log atoms. The full double kernel converges uniformly on every closed annulus
  `r <= |x| <= R` with `r > 0`. This removes compact convergence as an open assumption; the next
  analytic step is the explicit polar-set complement and the exponential-coordinate theta
  normalization.
- 2026-07-11 -- Replaced the anticipated Jacobi triple-product bridge by a constraint-and-divisor
  uniqueness bridge. `EllipticThetaLogKernel` first proves its own exact multiplicative
  quasiperiod `T(q,q*x)-T(q,x)=-1` off the boundary pole. Under
  `x(tau,z)=-exp(pi*i*tau)exp(2*pi*i*z)`, `EllipticThetaLogCoordinate` proves the normalized boundary
  has the same `1`-period and `tau`-quasiperiod as `thetaLogDeriv`. The new comparison module proves
  their discrepancy is doubly periodic on the common regular locus. It remains to match the
  explicit pole divisors; compact ellipticity then makes the discrepancy constant, which cancels
  from every translated defect used by the matroid theorem.
- 2026-07-11 -- Closed exact divisor-location alignment. `EllipticThetaCoordinateDivisor` rewrites
  the aligned coordinate as one complex exponential, classifies equality with every integer nome
  power using the kernel of complex exponential, and proves this nome orbit is exactly the odd
  half-period lattice. Composing with `JacobiThetaExactDivisor` gives an iff with
  `jacobiTheta2(z,tau)=0`. The comparison gap is now local principal-part equality at this common
  divisor, followed by the standard constant-discrepancy argument.
- 2026-07-11 -- Closed the distinguished principal-part comparison. The new
  `EllipticThetaLogPrincipalPart` module splits the theta boundary into its unique singular atom and
  forward/backward remainders, proves the remainders analytic at the nome using explicit uniform
  geometric bounds, computes the nonzero derivative of the aligned exponential coordinate, and
  proves `(z-z0)*ThetaLogConstructed(z) -> 1` at the odd half-period. Combining this with the
  existing analytic Jacobi-theta residue-one theorem gives normalized limit zero for their
  discrepancy. The remaining comparison work is global meromorphic packaging and transport of
  removability over the complete lattice divisor, after which elliptic constancy identifies every
  translated defect.
- 2026-07-11 -- Proved analyticity on the regular fundamental multiplicative annulus.
  `EllipticThetaLogFundamentalAnnulus` takes any point with `|q| < |x| < 1`, nests it inside a
  smaller closed annulus, constructs summable forward and backward rational-atom majorants, proves
  every summand differentiable on the corresponding open annulus, and applies the complex
  Weierstrass theorem. This supplies the pole-free fundamental domain for the global meromorphic
  transport. The next exact target is the wider `|q|^2 < |x| < 1` annulus with the single `x=q`
  atom isolated, followed by transport under integer nome powers.
- 2026-07-11 -- Closed global meromorphicity of the constructed theta boundary. The wider
  fundamental annulus isolates the sole `x=q` rational atom and proves the remainder analytic.
  `EllipticThetaLogNomeTransport` shows meromorphic germs are invariant under `x -> q*x`; a
  minimal-power reduction then moves every nonzero point into the wider annulus, proving the
  kernel meromorphic on `C*`. Composition with the nonvanishing exponential coordinate proves the
  additive normalization globally meromorphic on `C`. Consequently the comparison discrepancy is
  globally meromorphic. The new generic normalized-removability lemma turns `(z-p)f(z)->0` into
  nonnegative `meromorphicOrderAt`; applied at the half-period, it closes removability there. The
  remaining theta bridge is transport of this nonnegative order over the complete period lattice
  and elliptic constancy.
- 2026-07-11 -- Closed the constraint-and-divisor uniqueness bridge. Analytic nome transport proves
  the constructed theta kernel is analytic exactly off the full nome orbit; lattice transport of
  the cancelled principal part proves the comparison has no poles anywhere. Its canonical
  meromorphic normal form is entire and doubly periodic, compact fundamental-domain reduction
  makes it bounded, and Liouville forces it constant. Therefore the constructed theta boundary
  equals the analytic Jacobi logarithmic derivative up to one parameter-dependent constant, and
  every translated defect agrees exactly. `EllipticThetaLogGlobalAnalytic` and
  `EllipticThetaLogComparisonRigidity` build without project axioms.
- 2026-07-11 -- Pulled the actual normally convergent elliptic-gamma double kernel into additive
  coordinates. `EllipticGammaAdditiveLogKernel` proves both polarized hierarchy equations; the
  second face carries the exact half-parameter recentering forced by the two theta coordinates.
  Combining the first hierarchy equation with comparison rigidity proves that every mixed
  external-translation/structural face is exactly the analytic theta logarithmic-derivative defect
  on the regular locus. The remaining order-one gap is now field-level atomicity for the gamma
  primitive, not identification of its boundary or its pole obstruction.

## Current unconditional actual-product order-one surface

The actual elliptic-gamma bridge is now formalized, rather than represented by a kernel or
functional-equation assumption.

`formal/GaloisForLFunctions/HTGeometry/EllipticGammaProduct.lean` constructs the forward and backward entire
double products, proves locally uniform convergence on the whole additive plane, proves both
products nonzero, and identifies the logarithmic derivative of their quotient with the additive
double-sum kernel on its regular locus.

`formal/GaloisForLFunctions/HTGeometry/MeromorphicEllipticGamma.lean` embeds this quotient as a nonzero element
of the global meromorphic differential field and gives an explicit one-fraction presentation of
its logarithmic derivative.

`formal/GaloisForLFunctions/HTGeometry/AnalyticSubringEvaluation.lean` and
`AnalyticSubringFractionEvaluation.lean` prove the missing identity-theorem interface: global
analytic germs admit point evaluation; local equality promotes to analytic-subring equality; and
equality of meromorphic fractions gives equality of quotient representatives on every punctured
neighborhood.

`formal/GaloisForLFunctions/HTGeometry/EllipticGammaMixedFace.lean` proves the unconditional field identity

```text
T_sigma(T_h psi - psi) - (T_h psi - psi)
  = T_h(theta'/theta) - theta'/theta,
```

where `psi` is the logarithmic derivative of the genuine elliptic-gamma double product. The proof
clears the global fractions, proves the identity on a nonempty common regular neighborhood from the
normally convergent kernel calculation, and promotes it globally by analytic continuation. No
regular-locus hypothesis remains in the theorem.

`formal/GaloisForLFunctions/HTGeometry/MeromorphicPoleOrbitBoundaryLocal.lean` strengthens the theta
pole-orbit obstruction to punctured-local meromorphic equality. Combining it with the mixed-face
theorem, `formal/GaloisForLFunctions/HTGeometry/EllipticGammaExternalDefectNonElliptic.lean` proves:

```text
T_h psi - psi
```

cannot equal any `(1,tau)`-elliptic meromorphic quotient of two entire functions whenever `sigma`
is nontorsion modulo `Z + Z tau` and `h` is nonresonant modulo
`Z + Z tau + Z sigma`.

This is an unconditional order-one elliptic-field separation theorem for the actual product. It is
strictly weaker than the atomic parent required by the matroid theorem: the remaining order-one
gate is to prove the same exclusion after every nonzero `L in C[delta]`, and then the finite-family
version. Concretely, the missing formal interface is compatibility between
`differentialOperatorApply L` in the global meromorphic fraction field and punctured-local
application of `constantCoeffDifferentialOperator L` to a quotient representative. Once that
interface is closed, the existing finite theta-family orbit obstruction supplies the analytic
noncoboundary input for Ostrowski descent.

All named capstones in these modules build under the repository toolchain. Their `#print axioms`
output is exactly `propext`, `Classical.choice`, and `Quot.sound`; the formal lint gate passes.

## Differential-linear atomicity and the finite order-one matroid

The previously named compatibility gap is now closed unconditionally.

`formal/GaloisForLFunctions/HTGeometry/MeromorphicFractionJets.lean` recursively constructs entire
numerator/denominator pairs for every differential jet of a global meromorphic fraction and proves
that their pointwise quotients are the ordinary iterated derivatives on the regular locus.
`MeromorphicPuncturedRepresentation.lean` packages this as a punctured-local representation
relation, proves closure under sums and scalar multiplication, and proves closure under every
constant-coefficient operator `L in C[delta]`.

`formal/GaloisForLFunctions/HTGeometry/MeromorphicTranslationDifferentialOperator.lean` proves that additive
translation commutes with every meromorphic-field jet and every `L in C[delta]`.
`MeromorphicThetaDefectPunctured.lean` identifies the actual field theta defect and all its
constant-coefficient derivatives with the literal pointwise differentiated theta defect on every
punctured neighborhood. `MeromorphicPuncturedTranslationEquality.lean` proves the general
field-to-function denominator-clearing theorem: a fraction-field translation-coboundary identity
forces the corresponding quotient-function identity punctured-locally at every point.

These interfaces turn the actual gamma mixed face into the theorem

```text
ellipticGammaExternalLogDerivDefect_differentialOperator_ne_ellipticFraction
```

in `EllipticGammaExternalDefectDifferentialAtomic.lean`: for every nonzero
`L in C[delta]`,

```text
L(delta)(T_h psi - psi)
```

is outside every `(1,tau)`-elliptic meromorphic quotient of entire functions. This is the full
cyclic differential-linear atomicity statement, not only the undifferentiated separation theorem.

`MeromorphicThetaFamilyPoleOrbitBoundaryLocal.lean` upgrades the existing separated theta-family
obstruction to punctured-local equality. Consequently
`EllipticGammaExternalDefectFamilyDifferentialAtomic.lean` proves that for any finite family of
external shifts separated modulo `Z + Z tau + Z sigma`, every combination

```text
sum_i L_i(delta)(T_{h_i} psi - psi)
```

with at least one nonzero `L_i` remains outside the elliptic fraction field. Its corollary

```text
ellipticGammaExternalDifferentialFamilySum_eq_zero_iff
```

states that the combination vanishes exactly when every `L_i` vanishes. Thus the separated actual
elliptic-gamma external defects form a free `C[delta]`-family. This is not yet the nonlinear
differential matroid: a differential-polynomial relation need not imply a
`C[delta]`-linear relation without applying the several-automorphism Ostrowski theorem over the
paired elliptic compositum and discharging its simultaneous telescoping hypothesis. No theorem in
the current Lean tree proves `DifferentialIndependent` for the actual elliptic-gamma defect family.

The exact family build succeeds. `#print axioms` for the jet bridge, punctured-local transport,
single-generator atomicity, finite-family elliptic exclusion, and free-matroid corollary reports
only `propext`, `Classical.choice`, and `Quot.sound`. The formal lint gate passes. The repository
root build is presently blocked by pre-existing errors in `ExponentialGaugeSelection.lean`; the
entire new dependency cone builds independently and the root import file contains all new modules.

The first remaining scientific gate is the nonlinear order-one atomicity theorem. Its local
finite-family pole obstruction and generic product-specialization mechanism are formal, but the
actual paired elliptic-compositum presentation and the resulting Ostrowski instantiation remain
open. Only after that gate can the all-order lift turn the bottom face families into genuine
`DifferentialIndependent` inputs for the gluing engine.

## Constructed all-order multiple-elliptic-gamma hierarchy

The all-order hierarchy is now represented by an actual convergent special-function kernel rather
than an assumed family of functional equations.

`formal/GaloisForLFunctions/HTGeometry/MultipleEllipticGammaLogKernel.lean` defines, for an arbitrary finite
nome index type `I`, the forward and backward product arguments on `N^I`. The backward logarithmic
atom carries the parity factor `(-1)^|I|`; this is the unique sign for which deleting one coordinate
produces the next lower-order kernel. For every chosen coordinate `q`, it proves exact finite
fiberwise telescoping. The boundary is precisely the parity-correct kernel on `I \ {q}`, plus two
explicit terminal tails.

`formal/GaloisForLFunctions/HTGeometry/FinitePiProductSummability.lean` proves the required all-dimensional
majorant theorem: a finite product of nonnegative summable sequences is summable over the finite
Cartesian power. `MultipleEllipticGammaLogConvergence.lean` applies it to the forward and backward
multi-geometric arguments, proves absolute summability after the logarithmic atom, and defines the
actual convergent kernel

```text
multipleEllipticGammaLogKernel : (I -> C) -> C -> C.
```

`formal/GaloisForLFunctions/HTGeometry/MultipleEllipticGammaHierarchy.lean` proves terminal-tail vanishing,
Fubini decomposition along every coordinate, and the unconditional all-order identity

```text
K_I(p; p_q x) - K_I(p; x) = K_(I\{q})(p|_(I\{q}); x).
```

`MultipleEllipticGammaAdditiveHierarchy.lean` pulls this kernel back by the standard exponential
coordinate and proves, for arbitrary finite `I` and upper-half-plane parameters,

```text
Psi_I(z + tau_q) - Psi_I(z) = Psi_(I\{q})(z).
```

This formula is constructed from the infinite product atoms with absolute convergence and Fubini;
it is not a hierarchy axiom or recursive wrapper. It specializes at two nomes to the earlier
elliptic-gamma logarithmic kernel and at one nome to the theta logarithmic kernel, with the correct
alternating parity.

The exact hierarchy build succeeds. `#print axioms` for finite telescoping, absolute summability,
the convergent multiplicative hierarchy, and the additive hierarchy reports only `propext`,
`Classical.choice`, and `Quot.sound`.

The remaining realization work is to package the all-order forward/backward infinite products as
entire functions, identify the parity-dependent product or quotient as the genuine multiple
elliptic gamma, and prove its meromorphic-field logarithmic derivative equals this kernel. The
subsequent matroid lift must then formalize the face-filtration independence and localized
Stanley--Reisner rank theorem; the hierarchy equations themselves are no longer an open input.

## Genuine all-order products and global field hierarchy

The remaining realization gap stated above is now closed.

`formal/GaloisForLFunctions/HTGeometry/MultipleEllipticGammaProduct.lean` defines the forward and backward
infinite factors for an arbitrary finite parameter set, proves locally uniform convergence on the
whole additive plane, and proves that both products are entire and nonzero. It defines the genuine
parity-dependent multiple elliptic gamma: for an even number of nomes the backward product occurs
in the denominator, while for an odd number it occurs in the numerator. This parity is forced by
the hierarchy and gives the standard alternating multiple-gamma product. The logarithmic
derivative of the product is proved, on its regular locus, to equal the convergent all-order kernel.

`formal/GaloisForLFunctions/HTGeometry/MeromorphicMultipleEllipticGamma.lean` embeds both entire products in
the global analytic germ domain, constructs the parity-dependent product or quotient as a nonzero
global meromorphic-field element, defines its quotient-rule logarithmic derivative, and gives an
explicit entire numerator/product-denominator fraction for that derivative.

`formal/GaloisForLFunctions/HTGeometry/MultipleEllipticGammaFieldHierarchy.lean` clears those fractions,
proves the pointwise kernel identity on a common nonempty regular neighborhood, and promotes it by
analytic continuation to the unconditional field identity

```text
T_(tau_q) Psi_I - Psi_I = Psi_(I\{q})
```

for the logarithmic derivatives of the genuine products, simultaneously for every finite index
set and every coordinate. No regular-locus assumption remains in the theorem statement.

The exact dependency cone builds. `#print axioms` for local uniform product convergence, product
logarithmic-derivative identification, nonzero meromorphic realization, explicit field fraction,
and the global all-order field hierarchy reports only `propext`, `Classical.choice`, and
`Quot.sound`.

The special-function existence and one-step hierarchy gates are therefore complete. The remaining
theorem is algebraic-differential: prove the actual nonlinear order-one defect matroid, lift it
through these field hierarchy equations, instantiate the nested-star/one-slice face-filtration
induction, and prove the localized Stanley--Reisner differential-rank and multiplicative transfer
capstones.

## Free-shift transport and intrinsic all-order faces

`formal/GaloisForLFunctions/HTGeometry/FreeShiftOneSliceNonsummability.lean` proves over an
arbitrary field that no nonzero finite constant-coefficient linear form in one translation slice
of a bilateral free differential grid is a rational coboundary for the unit shift. This is a
finite-support theorem, not a special-function assumption.

`formal/GaloisForLFunctions/HTGeometry/DifferentialIndependentOneSliceNonsummability.lean`
transports that obstruction through the canonical fraction-field parametrization attached to any
genuinely `DifferentialIndependent` bilateral palette. Its theorem
`differentialIndependent_oneSlice_ne_coboundary` is unconditional and characteristic-free: in the
differential field generated by the palette, no nonzero finite linear form in the jets of one slice
is a coboundary for the conjugated free shift.

`formal/GaloisForLFunctions/HTGeometry/MultipleEllipticGammaReindex.lean` now transports the actual
forward product, backward product, meromorphic quotient, and meromorphic logarithmic derivative
through arbitrary finite parameter reindexings. Using that invariance,
`formal/GaloisForLFunctions/HTGeometry/MultipleEllipticGammaFaceHierarchy.lean` indexes every
genuine face by an unordered finite deletion set `J` and proves in the global meromorphic field

```text
T_(tau_q) Psi_J - Psi_J = Psi_(insert q J),   q notin J.
```

It also proves that successive face insertions commute. Hence repeated deletion no longer carries
an artificial nested-subtype or deletion-order dependence.

These results isolate the exact positive frontier. The all-order hierarchy and its intrinsic face
geometry are present, and one-slice nonsummability follows from genuine differential independence.
What is not yet justified is applying that universal obstruction to the actual elliptic-gamma
bottom faces: their nonlinear differential independence remains to be proved. After that, the
concrete face filtration must discharge the gluing engine's `FreeIndepOrbit` and `CrossNeutral`
hypotheses before the localized Stanley--Reisner rank and multiplicative transfer statements can
be promoted.
