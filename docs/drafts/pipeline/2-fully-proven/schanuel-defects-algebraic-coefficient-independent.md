# Algebraic-coefficient independence of numerical exponential defects

- **ID:** schanuel-defects-algebraic-coefficient-independent
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** defect-lattice survivor + invariant-form subgroup closure + Baker
- **Statement:** Defect forms of a `Q`-linearly independent complex exponential tuple are linearly independent over `Qbar`.

## Goal

Push the unconditional coefficient floor from integers to all algebraic numbers.  This removes an
artificial part of the Ax-to-values gap: any remaining dependence has genuinely transcendental
coefficients from the tuple's value field.

## Gates

- [x] 0 -> 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 -> 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 -> 3  formalized: exact theorem requires algebraic-group/Kahler-differential layer
- [ ] 3 -> 4  publication-ready: independent novelty and proof audit pending

## Statement

Let `x_1,...,x_n` be `Q`-linearly independent complex numbers, set `y_i=exp(x_i)`, and let

\[
 K=\overline{\mathbb Q}(x_1,\ldots,x_n,y_1,\ldots,y_n).
\]

Then

\[
 \epsilon_i=dy_i/y_i-dx_i\in\Omega_{K/\overline{\mathbb Q}}
 \qquad (1\le i\le n)
\]

are linearly independent over `Qbar`.

## Proof

Assume that a nonzero vector `c=(c_i) in Qbar^n` gives

\[
  \eta(p):=\sum_i c_i(d\log y_i-dx_i)=0,
  \qquad p=(x,y).
\]

Regard `eta` as a nonzero invariant differential on
`G=Ga^n x Gm^n`, and let `V=Loc_Qbar(p)`.  The displayed equality says that `eta` restricts to zero
on `V`.  Choose `q in V(Qbar)` and translate `V` by `q^{-1}`.  Pullback of an invariant differential
under group multiplication is the sum of its pullbacks from the factors, so `eta` vanishes on every
finite product of the translated variety.  By algebraic-group indecomposability, these products
stabilize at an algebraic subgroup `H` of `G`.  Hence

\[
  V\subset qH,\qquad \eta|_H=0.
\]

Because there are no nonzero algebraic-group homomorphisms between vector groups and tori, the
identity component splits as `H_a x H_m` with `H_a <= Ga^n` and `H_m <= Gm^n`.  Restriction of
`eta` to the additive factor gives

\[
  \sum_i c_i x_i=a\in\overline{\mathbb Q}. \tag{1}
\]

Let `L <= Z^n` be the character lattice annihilating `H_m`.  Restriction of `eta` to `H_m` says
that `c` belongs to `Qbar tensor_Z L`.  Choose `Q`-linearly independent
`m_1,...,m_r in L` and `beta_j in Qbar`, not all zero, with

\[
  c=\sum_j\beta_j m_j.
\]

Since `p in qH`, each

\[
  \alpha_j=y^{m_j}=\exp(m_j\mathbin{\cdot}x)
\]

is algebraic (a character is constant on the connected torus factor and has only a root-of-unity
variation on the finite component).  Put `s_j=m_j dot x`.  Injectivity of
`Q^n -> C`, `m |-> m dot x`, makes the `s_j` `Q`-linearly independent logarithms of algebraic
numbers.  Baker's theorem makes every nonzero algebraic linear form in the `s_j` transcendental.
But (1) gives

\[
  a=c\mathbin{\cdot}x=\sum_j\beta_j s_j,
\]

a nonzero such form equal to an algebraic number.  Contradiction.  Therefore no nonzero algebraic
coefficient relation exists. **[PROVED HERE]**

## Hostile audit

- `eta(p)=0` is equality in the Kahler differentials of the exact locus field, not evaluation under
  a chosen derivation.
- Translation uses an algebraic point because `Qbar` is algebraically closed and `V` is nonempty.
- Finite components of `H_m` only introduce roots of unity, so character values remain algebraic.
- Baker is applied only after choosing a `Q`-basis of the character lattice; rational independence
  of the original `x_i` makes the resulting logarithms rationally independent.
- The conclusion is not Schanuel: `Qbar`-linear independence in a `K`-vector space does not bound
  its `K`-dimension.

## Strongest stage-two consequence

If a stage-two Schanuel counterexample existed, its value field would have transcendence degree one,
so `epsilon_2=rho epsilon_1` for a unique defect slope `rho in K`.  This theorem forces

\[
  \rho\notin\overline{\mathbb Q}.
\]

Hence `rho` itself is a transcendence basis of `K/Qbar` up to finite algebraic extension.  A first
counterexample is therefore a one-variable algebraic-function system whose only differential
dependence coefficient is necessarily transcendental.

## Novelty audit

The ingredients are classical: Rosenlicht invariant differentials, algebraic-group
indecomposability, splitting of additive/toroidal subgroups, and Baker's theorem.  Targeted review
found no published statement in this numerical defect form.  Status: **new internal theorem;
external novelty unconfirmed**, with no priority claim.

## Lean formalization progress

The algebraic-group layer now has two unconditional, kernel-checked modules:

- `AffineExponentialGroupHopf` constructs the additive symmetric-algebra antipode, the explicit
  Hopf coordinate algebra of `G_a^n x G_m^n`, primitive additive coordinates, group-like torus
  characters, and proves both cross-factor Hom groups vanish.  Its key coefficient theorem says
  every primitive Laurent polynomial is zero.
- `AffineExponentialSubgroups` proves a reusable principal Hopf-ideal criterion and applies it to
  additive linear equations and torus character equations.  The quotient coordinate rings inherit
  Hopf algebra structures, so these equations define actual closed affine subgroup schemes.
- `AffineExponentialCrossHomFinite` upgrades both cross-Hom vanishing theorems to arbitrary finite
  dimensions; its stronger core says the group algebra of any additive commutative group over a
  field has no nonzero primitive elements.
- `HopfIdealKernel` proves antipode naturality and proves that every kernel of a commutative
  Hopf-algebra morphism over a field is a Hopf ideal, including the nontrivial coideal descent.
- `AffineExponentialProjectionImages` constructs the two scheme-theoretic projection-image Hopf
  ideals of an arbitrary subgroup ideal and identifies their additive-linear and torus-character
  relations exactly as contractions of the original ideal.
- `SymmetricHopfPrimitive` proves over any characteristic-zero field, without a finite-dimensional
  hypothesis, that every primitive element of `Sym(V)` is a degree-one generator.
- `GroupGradedHopfPrimitive` proves the universal grading rigidity theorem: every primitive of
  `B[M]` is supported at the identity of `M`, with primitive coefficient in `B`.
- `TensorGroupHopfEquiv` proves the canonical algebra equivalence `k[M] tensor B ~= B[M]` is a
  bialgebra equivalence, allowing grading arguments on the tensor coordinate algebra.
- `AffineExponentialPrimitive` concludes on the project's actual coordinate algebra that every
  primitive regular function on `G_a^n x G_m^n` is exactly additive-linear and independent of the
  torus factor.

This closes construction and cross-Hom rigidity, but not yet the classification theorem needed in
the paper proof: every connected closed subgroup of `G_a^n x G_m^n` must be shown to split and its
torus factor must be recovered from a saturated character lattice.  Rosenlicht subgroup closure,
invariant-differential restriction, that classification, and general Baker for arbitrary algebraic
logarithms remain open Lean dependencies.

## Log

- 2026-08-14 -- algebraic coefficient descent proved; stage-two defect slope shown transcendental.
- 2026-08-14 -- formalized coordinate Hopf algebras, both cross-Hom vanishing theorems, and
  additive-linear/torus-character closed subgroup kernels with Hopf quotients.
- 2026-08-14 -- generalized cross-Hom rigidity to all dimensions; formalized Hopf kernels and exact
  projection-image contractions, reducing splitting to classification of the remaining mixed Hopf
  ideal above its two factor contractions.
- 2026-08-14 -- classified primitives in symmetric, group-graded, and tensor-product Hopf
  coordinates; proved every primitive regular function on `G_a^n x G_m^n` is additive-linear.

## Lean status -- the integral floor is already in the corpus

Searched before building.  The integral case of this card's statement -- independence over `ℤ`
rather than over `Q̄` -- is formalized, together with the slope machinery the algebraic upgrade
needs.

| Card item | Existing declaration |
|---|---|
| the numerical logarithmic Kähler defect of one exponential pair, relative to `Q̄` | `schanuelDefect` (`RHTower/SchanuelDefectLattice.lean`) |
| **the integral floor**: for a rationally independent tuple the defects are integrally independent | `schanuelDefect_integer_relation` (same module) |
| a slope between two defects descends to any rank-one intermediate value field | `schanuelDefect_slope_mem_intermediateField_of_finrank_one` (`RHTower/SchanuelDefectValueField.lean`) |
| the same under an integral isogeny of value fields | `schanuelDefect_slope_mem_of_integral_isogeny_field` (`RHTower/SchanuelIntegralIsogenyValueField.lean`) |

The card's own gate note -- "formalized: exact theorem requires algebraic-group/Kähler-differential
layer" -- is therefore accurate about the *upgrade* from `ℤ` to `Q̄`, not about the floor itself,
which is done.

Related and already formal: the abstract slope-uniqueness step this card feeds into
`schanuel-stage-two-defect-slope-normal-form` is `existsUnique_defectSlope`
(`HTGeometry/DefectSlopeNormalForm.lean`).

### What remains

The upgrade from integral to algebraic coefficients, which is where Baker enters.  The corpus Baker
layer is the distinct-prime specialization (`RHTower.bakerLinearIndependence_holds`) plus full
Gelfond--Schneider (`RHTower.gelfondSchneider_holds`); the general-logarithm form needed here is
exactly the open target of `baker-general-logarithms-inhomogeneous-extension`.

## Correction — the Baker gate is closed (2026-08-23)

The "What remains" note above says the general-logarithm Baker form "is exactly the open target of
`baker-general-logarithms-inhomogeneous-extension`".  That card is **closed** and sits in
`3-formalized`.  The corpus carries

```text
RHTower.bakerTheorem_holds : BakerTheorem
RHTower.baker_linearForm_transcendental
    (lambda : Fin n → ℂ) (beta : Fin n → ℂ)
    (halg : ∀ i, IsLogarithmOfAlgebraic (lambda i))
    (hind : LinearIndependent ℚ lambda)
    (hbeta : ∀ i, IsAlgebraic ℚ (beta i)) (hne : ∃ i, beta i ≠ 0) :
  ¬ IsAlgebraic ℚ (∑ i, beta i * lambda i)
```

axiom-clean, with arbitrary chosen logarithms and no principal-branch restriction — exactly the
final step of this card's proof.

So the remaining gate is **not** Baker.  It is the algebraic-group half: from a nonzero `Q̄`-relation,
produce the character lattice `L ≤ ℤⁿ` with `c ∈ Q̄ ⊗_ℤ L` and the algebraicity of the character
values `α_j = y^{m_j}`.  The corpus already has the Hopf-coordinate layer that step needs
(cross-Hom rigidity in all dimensions, Hopf kernels, and the classification of primitives on
`G_a^n × G_m^n` as additive-linear); what is left is the classification of the remaining mixed Hopf
ideal above its two factor contractions.

Note also that the *rational*-coefficient case needs none of this: clearing denominators reduces it
to `schanuelDefect_integer_relation`, which is already proved.

## Rational coefficient floor packaged (2026-08-25)

`formal/GaloisForLFunctions/RHTower/SchanuelDefectRationalIndependence.lean` now closes and packages
that reduction:

```text
schanuelDefect_rational_relation
    every ℚ-coefficient relation among defects of a ℚ-linearly independent tuple is zero

schanuelDefect_linearIndependent_rational
    LinearIndependent ℚ (fun i ↦ schanuelDefect (x i))
```

One positive common denominator turns a rational relation into the existing integral relation;
positivity ensures the scaling factor is nonzero.  Direct check and targeted leaf build pass, and
both declarations audit to `[propext, Classical.choice, Quot.sound]`.  The module is wired into the
`RHTower` umbrella without building that umbrella.

This does not promote the card: the exact `Q̄`-coefficient theorem still requires the connected mixed
Hopf-ideal/character-lattice classification already isolated above.  It removes rational
coefficient clearing from that remaining proof and exposes the maximal unconditional floor as a
standard `LinearIndependent` theorem.

The same module also proves `schanuelDefect_slope_not_rational`: any complex scalar relating the
two defects of a rationally independent pair lies outside the embedded rational field.  This is the
immediate slope consequence of the new `LinearIndependent ℚ` packaging.  Its axiom audit is again
`[propext, Classical.choice, Quot.sound]`.

## Algebraic-coefficient singleton case formalized (2026-08-25)

`formal/GaloisForLFunctions/RHTower/SchanuelDefectSingletonAlgebraicIndependence.lean` closes the
exact one-variable specialization over `Q̄`:

```text
schanuelDefect_ne_zero_of_ne_zero
    z ≠ 0 → schanuelDefect z ≠ 0

schanuelDefect_linearIndependent_algebraic_singleton
    z ≠ 0 → LinearIndependent (algebraicClosure ℚ ℂ)
      (fun _ : Fin 1 ↦ schanuelDefect z)
```

For the singleton input, rational independence is exactly `z ≠ 0`; rational defect independence
therefore gives a nonzero defect.  Over the field `Q̄`, nonvanishing is exactly linear independence
of the singleton defect family.  Direct check and targeted leaf build pass.  Both declarations
audit to `[propext, Classical.choice, Quot.sound]`, and the leaf is wired into the `RHTower`
umbrella without building that umbrella.

This is the full algebraic-coefficient theorem for `n = 1`, not the general finite-dimensional
claim.  The card remains at Stage 2 because the mixed Hopf-ideal/character-lattice classification
is still required for `n ≥ 2`.

## Arbitrary-dimensional support-one case formalized (2026-08-25)

`formal/GaloisForLFunctions/RHTower/SchanuelDefectSparseAlgebraicIndependence.lean` packages the
singleton result inside an arbitrary rationally independent tuple:

```text
schanuelDefect_algebraic_relation_of_support_card_le_one
    card {i | c_i ≠ 0} ≤ 1 →
    (∑ i, c_i • schanuelDefect (x_i) = 0) → c = 0
```

If a coefficient `c_i` were nonzero, the support bound would kill every other coefficient, so the
relation would be `c_i • schanuelDefect (x_i) = 0`.  Rational independence gives `x_i ≠ 0`, and the
singleton theorem gives a nonzero defect, forcing `c_i = 0`.  Direct check and targeted leaf build
pass; the declaration audits to `[propext, Classical.choice, Quot.sound]` and is wired into the
`RHTower` umbrella without building it.

The unresolved algebraic-group classification is now needed only to exclude relations with at
least two nonzero algebraic coefficients.  Card remains at Stage 2.

## Projection-image classification advanced (2026-08-26)

`formal/GaloisForLFunctions/HTGeometry/AffineExponentialProjectionClassification.lean` now composes
the existing projection-image Hopf ideals with the corpus's full group-algebra Hopf-ideal theorem:

```text
torusRelationLattice
mem_torusRelationLattice_iff
torusProjectionIdeal_eq_ker_quotientGroupMap
additiveProjectionIdeal_eq_bot_or_exists_nonzero_relation
```

For an arbitrary mixed Hopf ideal `I` in the coordinate algebra of `Gₐⁿ × Gₘⁿ`, the torus
projection is now recovered exactly by quotienting `ℤⁿ` by the lattice of characters `m` whose
equations `χᵐ - 1` already lie in `I`.  On the additive side, either the projection ideal is zero
or it supplies a nonzero additive-linear annihilator already lying in `I`.  These are statements
about the actual mixed subgroup ideal, not separately postulated factor subgroups.

The leaf passes direct checking and a targeted build.  All four declarations audit to
`[propext, Classical.choice, Quot.sound]`; it is wired into `HTGeometry` without an umbrella build.
Remaining exact gate is narrower: prove connected mixed ideal equals the sum of these two factor
contractions and prove connectedness saturates `torusRelationLattice`.  Only then can the invariant
differential relation be converted into the lattice/Baker contradiction.  Card remains Stage 2.

## Character-lattice saturation criterion formalized (2026-08-26)

`formal/GaloisForLFunctions/HTGeometry/CharacterLatticeSaturation.lean` now gives the exact
integral bridge needed by the torus half of that gate:

```text
integerSaturated_toIntSubmodule_iff_quotient_nsmul_eq_zero
torusRelationLattice_integerSaturated_iff_quotient_nsmul_eq_zero
```

Thus `torusRelationLattice` is saturated exactly when its quotient character group has no nonzero
class killed by a positive integer.  The proof reuses the corpus's existing `IntegerSaturated`
notion and the actual quotient group; no parallel saturation predicate or proxy lattice is
introduced.  Direct check and targeted leaf build pass.  Both declarations audit to
`[propext, Classical.choice, Quot.sound]`, and the module is wired into `HTGeometry` without an
umbrella build.

Remaining torus step is now geometric rather than lattice-theoretic: derive quotient torsion
freeness from connectedness of the actual diagonalizable projection.  Mixed-factor splitting is
still separately required.  Card remains Stage 2.

## Connected group-algebra saturation bridge formalized (2026-08-26)

Two new `HTGeometry` leaves close the algebraic core of that geometric step:

- `ConnectedPrimeSpectrumIdempotent.lean` proves that a commutative ring with preconnected prime
  spectrum has no idempotents other than zero and one.
- `GroupAlgebraConnectedSaturation.lean` constructs the normalized cyclic-orbit idempotent attached
  to a finite-order character and derives
  `eq_zero_of_nsmul_eq_zero_of_preconnected_groupAlgebra_primeSpectrum`,
  `integerSaturated_of_preconnected_groupAlgebra_primeSpectrum`, and
  `torusRelationLattice_integerSaturated_of_preconnected_groupAlgebra_primeSpectrum`.

Consequently, preconnectedness of the actual group algebra
`k[((ℤⁿ) / torusRelationLattice k I)]` now forces integral saturation of the exact torus-relation
lattice attached to the mixed Hopf ideal `I`.  This is an internal cyclic-average proof over any
characteristic-zero field, not an imported classification or a torsion-free hypothesis.

Both leaves pass direct checks; the capstone leaf passes its targeted build.  Every new declaration
audits to `[propext, Classical.choice, Quot.sound]`, and both leaves are wired into `HTGeometry`
without building that umbrella.

Remaining geometric link is to transfer connectedness of the mixed subgroup to preconnectedness of
this classified torus-projection spectrum.  Mixed-factor splitting (the mixed Hopf ideal equals the
sum of its additive and torus contractions) is still separately required.  Card remains Stage 2.

## Mixed-spectrum saturation transfer formalized (2026-08-26)

`formal/GaloisForLFunctions/HTGeometry/MixedTorusProjectionSaturation.lean` removes the need for a
separate connectedness theorem for the torus projection.  It constructs the canonical injections

```text
k[(ℤⁿ / torusRelationLattice k I)]
  ↪ k[ℤⁿ] / torusProjectionIdeal k I
  ↪ CoordinateAlgebra k n / I
```

and proves
`torusRelationLattice_integerSaturated_of_preconnected_mixed_primeSpectrum`: preconnectedness of
the actual mixed subgroup quotient's prime spectrum directly forces saturation of the exact torus
relation lattice.  A finite-order quotient character would otherwise produce a normalized cyclic
idempotent in the mixed quotient.  The module also proves every Hopf ideal over a field is proper
from its counit condition, so no extra nontrivial-quotient assumption is introduced.

The reusable group-algebra layer was factored through
`eq_zero_of_nsmul_eq_zero_of_groupAlgebra_idempotents_trivial`, avoiding a duplicate cyclic-average
argument.  Direct checks and targeted leaf build pass; every new declaration audits to
`[propext, Classical.choice, Quot.sound]`.  The leaf is wired into `HTGeometry` without building
that umbrella.

The torus saturation implication is now complete once the subgroup closure supplies
preconnectedness of `PrimeSpectrum (CoordinateAlgebra k n / I)`.  Remaining central algebraic gate
is mixed-factor splitting, plus construction of the translated connected subgroup closure and
restriction of the invariant differential to it.  Card remains Stage 2.

## Exact additive-projection classification formalized (2026-08-26)

`formal/GaloisForLFunctions/HTGeometry/MixedAdditiveProjectionClassification.lean` upgrades the
previous nonzero-relation corollary to the full factor classification.  It defines the actual
additive relation subspace of a mixed Hopf ideal and proves

```text
mem_additiveRelationSubspace_iff
additiveProjectionIdeal_eq_linearIdeal_additiveRelationSubspace
additiveRelationSymmetricAlgHomIntoSubgroupQuotient_injective
```

Thus the scheme-theoretic additive projection ideal is generated exactly by additive-linear
relations already lying in the original mixed ideal, and the resulting symmetric algebra embeds
in the actual mixed subgroup coordinate quotient.  The internal injectivity proof already present
inside `SymmetricHopfIdealClassification.eq_linearIdeal_linearPart` was factored into the reusable
public theorem `quotientBialgHom_injective`; no kernel argument was duplicated.

Direct checks and targeted builds pass.  All changed/new declarations audit to
`[propext, Classical.choice, Quot.sound]`; the new leaf is wired into `HTGeometry` without an
umbrella build.

Both factor projections are now classified exactly and embedded in the mixed quotient.  Remaining
classification gate is injectivity of their joint multiplication map (equivalently, absence of an
additional mixed Hopf kernel); connected torus saturation and subgroup-closure/differential
transport remain as stated above.  Card remains Stage 2.

## Joint mixed-projection tensor presentation formalized (2026-08-26)

`formal/GaloisForLFunctions/HTGeometry/MixedProjectionTensorPresentation.lean` constructs the exact
joint multiplication map

```text
k[(ℤⁿ / torusRelationLattice k I)] ⊗
  Sym((kⁿ) / additiveRelationSubspace k I)
    → CoordinateAlgebra k n / I
```

and proves `mixedProjectionTensorAlgHom_surjective` over every field.  The proof lifts arbitrary
mixed quotient elements to the original tensor coordinate algebra and handles every pure tensor
using the classified torus quotient map and symmetric quotient map.  No finite-dimensional,
reducedness, connectedness, or characteristic-zero premise is needed for this generation theorem.

Direct check and targeted build pass.  Every new theorem audits to
`[propext, Classical.choice, Quot.sound]`; the leaf is wired into `HTGeometry` without building
that umbrella.

The mixed-factor classification is now reduced to one exact statement: injectivity of
`mixedProjectionTensorAlgHom` for the connected mixed subgroup produced by the paper proof.  All
factor classification, factor embeddings, compatibility with original coordinates, and joint
surjectivity are closed.  Card remains Stage 2.

## Joint presentation upgraded to a bialgebra quotient (2026-08-26)

`formal/GaloisForLFunctions/HTGeometry/MixedProjectionTensorBialgebra.lean` upgrades the joint
algebra presentation to the exact Hopf-coordinate structure.  It equips both classified factor
quotients with their canonical bialgebra quotient maps, constructs

```text
CoordinateAlgebra k n →ₐc[k]
  k[(ℤⁿ / torusRelationLattice k I)] ⊗
    Sym((kⁿ) / additiveRelationSubspace k I),
```

proves this map surjective, proves that the joint multiplication presentation is a bialgebra
morphism, and proves that their composite is exactly the original subgroup quotient bialgebra
map.  Supporting reusable results expose surjectivity of the group-algebra and symmetric-algebra
bialgebra quotient maps in their natural classification modules.

The new leaf passes a direct check and targeted build.  Every new or newly exposed theorem audits
to `[propext, Classical.choice, Quot.sound]`; the leaf is wired into `HTGeometry` without building
that umbrella.

Thus the remaining mixed-factor gate is no longer compatibility or surjectivity: it is precisely
injectivity of the surjective bialgebra morphism `mixedProjectionTensorBialgHom`, equivalently the
absence of an additional mixed Hopf kernel.  Subgroup closure and invariant-differential transport
also remain.  Card remains Stage 2.

## The residual mixed relation ideal is an exact Hopf kernel (2026-08-26)

`formal/GaloisForLFunctions/HTGeometry/MixedProjectionTensorKernel.lean` names the kernel of the
surjective joint bialgebra presentation and proves:

```text
jointKernel_isHopfIdeal
tmul_one_mem_jointKernel_iff
one_tmul_mem_jointKernel_iff
```

Thus the residual relation ideal is itself a Hopf ideal and has zero intersection with each pure
factor: `x ⊗ 1` lies in it exactly when `x = 0`, and in characteristic zero `1 ⊗ y` lies in it
exactly when `y = 0`.  The proof uses the already-established injections of both classified factor
coordinate algebras into the mixed quotient.  It also resolves the tensor-product `Ring`/`Semiring`
instance diamond explicitly, so the corpus's general Hopf-kernel theorem applies without restating
or weakening it.

The leaf passes direct checking and its targeted build.  All three new theorems audit to
`[propext, Classical.choice, Quot.sound]`; the leaf is wired into `HTGeometry` without building the
umbrella.

The mixed-factor classification is now the single abstract rigidity theorem: over characteristic
zero, a Hopf ideal in the tensor product of a group algebra and a symmetric algebra, with both pure
factor contractions zero, must itself be zero.  Proving that theorem will make
`mixedProjectionTensorBialgHom` injective.  Subgroup closure and invariant-differential transport
remain after it.  Card remains Stage 2.

## Common group/symmetric Hopf subalgebras are scalar (2026-08-26)

`formal/GaloisForLFunctions/HTGeometry/CommonHopfSubalgebraTrivial.lean` proves the common-factor
rigidity needed by a Hopf-algebraic Goursat argument.  For an injective bialgebra map into an
additive group algebra, every nonzero grading coefficient exposes a group-like preimage: contract
one leg of comultiplication against that coefficient functional and normalize.  If the same Hopf
algebra also injects into a symmetric algebra, that preimage maps to a symmetric-algebra group-like
element and is therefore one.  Consequently every nonzero group-algebra grade vanishes and the
source consists only of scalars:

```text
exists_groupLike_preimage_of_coeff_ne_zero
exists_eq_algebraMap_of_injective_group_symmetric
algebraMap_surjective_of_injective_group_symmetric
```

The leaf passes direct checking and targeted build.  Every new theorem audits to only
`[propext, Classical.choice, Quot.sound]`; it is wired into `HTGeometry` without building the
umbrella.

This closes the common Hopf subalgebra obstruction between torus and additive factors.  Remaining
abstract step is to construct the common Hopf quotient/subalgebra attached to the residual kernel
and apply this scalarity theorem to prove that kernel zero.  Subgroup closure and
invariant-differential transport still follow.  Card remains Stage 2.

## Residual mixed relations have at least two torus weights (2026-08-26)

`formal/GaloisForLFunctions/HTGeometry/AddMonoidAlgebraTensorCoefficients.lean` adds the canonical
linear equivalence

```text
k[M] ⊗ N ≃ₗ (M →₀ N),
```

with its pure-tensor coefficient formula and coefficientwise zero criterion.  This is reusable
infrastructure for tensor products with any additive monoid algebra; it does not specialize the
mathematics to the Schanuel card.

`formal/GaloisForLFunctions/HTGeometry/MixedProjectionTensorKernel.lean` applies that equivalence
to the residual joint Hopf kernel.  It defines the exact finite torus support, reconstructs every
singleton-supported tensor from its unique coefficient, and proves

```text
unit_tmul_mem_jointKernel_iff
tmul_unit_mem_jointKernel_iff
single_tmul_mem_jointKernel_iff
two_le_card_torusSupport_of_mem_jointKernel
```

Hence multiplication by an invertible pure factor cannot create a residual relation, every
one-weight residual relation is zero, and every nonzero residual relation has at least two
distinct torus weights.  This is the support-minimal base case for the remaining Hopf-Goursat
elimination; no hypotheses beyond those already intrinsic to the classified mixed subgroup were
added.

Both leaves pass direct checking; the modified kernel leaf passes its targeted build.  Every new
declaration audits to only `[propext, Classical.choice, Quot.sound]`.  Both modules are wired into
`HTGeometry`; no umbrella build was run.  Remaining algebraic gate is exclusion of support size at
least two using the coideal law (equivalently, completion of the common-factor Goursat step).
Subgroup closure and invariant-differential transport still follow.  Card remains Stage 2.

## All residual skew-primitives eliminated (2026-08-26)

`formal/GaloisForLFunctions/HTGeometry/GroupGradedHopfSkewPrimitive.lean` supplies the missing
coefficientwise classification of skew-primitives in `Sym(V)[M]`:

```text
sameWeight_skewPrimitive_group_symmetric_eq_single_generator
distinctWeight_skewPrimitive_eq_smul_sub
```

If both endpoint group-like weights agree, the skew-primitive is exactly that torus monomial
times one additive-linear generator.  If the endpoint weights differ, it is exactly a scalar
multiple of their group-like difference.  The proof applies every diagonal and cross
coefficient-pair functional to comultiplication; no finite-dimensional assumption is used.

`formal/GaloisForLFunctions/HTGeometry/MixedProjectionTensorKernel.lean` applies both cases in

```text
eq_zero_of_mem_groupGradedJointKernel_of_skewPrimitive
```

and proves every skew-primitive in the residual kernel is zero.  Same-weight elements vanish by
the already-proved absence of nonzero homogeneous kernel elements.  Distinct-weight elements
vanish by injectivity of the classified torus factor embedding.  Thus the kernel contains no
group-like difference, primitive, or skew-primitive at any two weights.

The new generic leaf is wired into `HTGeometry` without building that umbrella.  Direct checks
and targeted leaf builds pass; every new declaration audits to only
`[propext, Classical.choice, Quot.sound]` (with some elementary slice lemmas needing fewer).

Remaining mixed-kernel gate is now the exact Heyneman–Radford/Taft–Wilson filtration step: a
coalgebra morphism out of the pointed cocommutative coalgebra `Sym(V)[M]` is injective once it is
injective on its coradical and all skew-primitives.  Corpus search confirms that coradical
filtration infrastructure is not yet present, so it must be built rather than wrapped as a
hypothesis.  Subgroup closure and invariant-differential transport still follow.  Card remains
Stage 2.

## Common torus/additive Hopf factor constructed and proved scalar (2026-08-26)

`formal/GaloisForLFunctions/HTGeometry/CommonHopfSubalgebraTrivial.lean` now proves the stronger
ambient-image theorem

```text
group_symmetric_image_intersection_eq_scalars
```

for arbitrary injective bialgebra morphisms `k[M] → H` and `Sym(V) → H`.  If their images of
`a` and `b` agree, then there is one `c : k` with `a = c` and `b = c`.  The proof constructs a
linear retraction of the group-algebra embedding, slices comultiplication to extract every
nonzero torus coefficient as an actual ambient group-like monomial, observes via the second
comultiplication presentation that this monomial lies in the symmetric image, reflects
group-likeness across the injective symmetric bialgebra map, and applies the characteristic-zero
symmetric group-like classification.  Supporting reusable lemmas prove slice naturality,
coefficient extraction from group-algebra comultiplication, and reflection of group-like elements
through injective bialgebra maps.

`formal/GaloisForLFunctions/HTGeometry/MixedProjectionTensorKernel.lean` upgrades both previously
classified factor algebra embeddings to actual bialgebra embeddings and applies the ambient
theorem:

```text
torusFactorBialgHom_injective
additiveFactorBialgHom_injective
factor_images_intersection_eq_scalars
```

Thus the common Hopf factor in the mixed quotient is now constructed internally and proved to be
exactly the scalar field; no hypothetical intersection Hopf structure or added premise is used.
The same leaf transports the joint quotient through `k[M] ⊗ B ≃ B[M]`, proves the transported
map surjective, identifies its kernel as a Hopf ideal, and proves that every nonzero element of
that kernel has at least two homogeneous weights.

The generic inverse homogeneous-coefficient formula was added to
`formal/GaloisForLFunctions/HTGeometry/TensorGroupHopfEquiv.lean`.  Direct checks and targeted
leaf builds pass.  Every new declaration audits to only
`[propext, Classical.choice, Quot.sound]`; no umbrella build was run.

Remaining abstract algebraic gate is now narrower: prove injectivity of the multiplication map
from two injective commutative Hopf subalgebras whose ambient intersection is scalar (equivalently,
finish Hopf-Goursat linear disjointness).  Common-factor construction and scalarity are closed.
Subgroup closure and invariant-differential transport still follow.  Card remains Stage 2.

## Current mixed-kernel frontier (2026-08-26)

The later skew-primitive result above sharpens the final paragraph immediately preceding this
section.  Common-factor scalarity and every coradical/skew-primitive obstruction are closed.  Exact
remaining theorem is the Heyneman–Radford injectivity step for the explicit pointed coalgebra
`Sym(V)[M]`; no conditional interface for that theorem has been introduced.

## Residual mixed Hopf kernel vanishing formalized (2026-08-26)

Corpus search first recovered the existing minimal-degree, exact partial-derivative, coalgebra-slice,
skew-primitive, homogeneous-kernel, and factor-image-intersection theorems.  The new work reuses
those declarations and adds only the missing group-graded filtration transport needed to pass from
an arbitrary kernel element to the already-classified affine layer.

The reusable leaves
`GroupGradedSymmetricDegree.lean`,
`AdditivePolynomialCoalgebraFiltration.lean`,
`GroupGradedSymmetricCoalgebraFiltration.lean`,
`GroupGradedSymmetricAffine.lean`, and
`GroupGradedBialgKernelDegreeOne.lean` prove that a noninjective bialgebra morphism out of
`Sym(V)[M]` over a characteristic-zero field has a nonzero kernel element of additive degree at
most one.  Exact fixed-weight counit and linear-coefficient slices then isolate its affine
coefficient.

`formal/GaloisForLFunctions/HTGeometry/MixedProjectionTensorKernelVanishing.lean` applies this to
the actual classified mixed projection and proves

```text
groupGradedJointBialgHom_injective
mixedProjectionTensorBialgHom_injective
jointKernel_eq_bot
groupGradedJointKernel_eq_bot
```

Degree zero reduces to the injective torus factor.  In degree one, the fixed-weight slice leaves a
scalar group-algebra error; the affine coefficient is a scalar plus one symmetric generator.
The resulting equality lies in both classified factor images, so
`factor_images_intersection_eq_scalars` makes the generator scalar, contradicting exact degree
one.  Thus every residual mixed Hopf relation vanishes, not only homogeneous or skew-primitive
ones.  No connectedness, finite-dimensionality, reducedness, or added theorem premise is used.

Direct checks and the targeted leaf build pass.  The new declarations audit to only
`[propext, Classical.choice, Quot.sound]`; all leaves are wired into `HTGeometry` without an
umbrella build.  The mixed-factor classification gate is closed.  Remaining card gates are now
the translated-locus subgroup closure/connectedness construction and transport of the numerical
Kähler relation to invariant-form restrictions; Baker and torus saturation are already formalized.
Card remains Stage 2.

## Additive-exponential point evaluation layer formalized (2026-08-26)

Fresh corpus search found only the complex-analytic product-torus character and a Hurwitz-specific
Laurent evaluator, not a field-generic evaluator for the finite-support character lattice used by
the mixed subgroup coordinate algebra.  `AlgebraicTorusCharacter.lean` now provides the reusable
character, its exponent-addition and point-multiplication laws, and evaluation

```text
k[ℤ⁽ⁿ⁾] →ₐ[k] L
```

at every `L`-valued split-torus point over an arbitrary field extension `k → L`.
`AffineExponentialPointEvaluation.lean` packages `L`-points of `Gₐⁿ × Gₘⁿ` as an actual
commutative group, constructs the mixed coordinate evaluation, proves its values on the canonical
additive coordinates and torus characters, and proves that both factor evaluations intertwine
point multiplication/addition with Hopf comultiplication.

Both direct checks and targeted leaf builds pass.  New declarations audit to at most
`[propext, Classical.choice, Quot.sound]`; both leaves are wired into `HTGeometry` without an
umbrella build.  This supplies the point/evaluation foundation for the translated-locus subgroup
closure still required by the card.  It does not assume that closure or promote the card.

## Point subgroup closure and Hopf vanishing ideal formalized (2026-08-26)

Repeated corpus search found the existing affine-space closure, point-separation, reduced tensor,
Hopf quotient, and factor-evaluation machinery, but no full mixed point group law, inverse law,
algebra-map representation, or subgroup-vanishing Hopf theorem.  The new layer reuses those exact
components rather than introducing a second affine-polynomial closure theory.

`AffineExponentialPointEvaluation.lean` now proves the full convolution and antipode identities

```text
eval_mul_point
eval_inv_point
```

for every mixed coordinate function.  `AffineExponentialPointRepresentation.lean` proves that
every algebra map from the mixed coordinate algebra to a field is evaluation at a concrete
additive-torus point.  `AffineExponentialPointClosure.lean` constructs the mixed-coordinate
vanishing ideal and proves, for every point subgroup over an arbitrary field,

```text
closureSubgroup
vanishingIdeal_isRadical
vanishingIdeal_isHopfIdeal
```

The coideal proof adds no finite-type or algebraic-closedness premise.  Evaluations by the original
subgroup jointly separate its quotient, a basis argument promotes that separation to the tensor
square, and subgroup multiplication kills the image of comultiplication.  Thus no missing Laurent
finite-generation instance or conditional Nullstellensatz wrapper is needed.

Direct source checks and targeted builds of
`AffineExponentialPointRepresentation` and `AffineExponentialPointClosure` pass.  All new
declarations audit to only `[propext, Classical.choice, Quot.sound]`; the leaves are wired into
`HTGeometry` without building that umbrella.

This closes same-field point-subgroup closure and its exact Hopf ideal.  Card remains Stage 2:
translated `Q̄`-locus generation still needs coefficient-field/base-change descent from complex
points to the `Q̄` Hopf ideal, followed by invariant Kähler-differential restriction and the
already-isolated character-lattice/Baker assembly.

## Exact mixed invariant-differential kernel formalized (2026-08-26)

Fresh corpus research recovered the existing mixed quotient maps, tensor presentation, factor
classification, co-Lie/Kähler comparison, and product co-Lie equivalence.  It found no theorem
identifying the joint co-Lie kernel of the actual subgroup quotient.  The added layer therefore
reuses those declarations and supplies only the missing factorwise separation and assembly.

`GroupAlgebraPointDerivation.lean` constructs point derivations of a group algebra from additive
weights.  `TorusCharacterCoLie.lean` uses them to prove that the kernel of the logarithmic
differential map for `k[ℤⁿ/L]` is exactly the `k`-linear span of the integral subgroup `L`, including
when `ℤⁿ/L` has torsion.  `SymmetricAlgebraCoLie.lean` proves that degree-one generators inject into
the co-Lie module of a symmetric algebra.  Finally,
`AffineExponentialCoLieClassification.lean` combines these results with the already-proved exact
mixed tensor presentation to establish

```text
coLieMap_subgroupQuotient_eq_zero_iff
```

for every characteristic-zero field and every Hopf ideal in the mixed coordinate algebra.  A
mixed logarithmic/additive direction vanishes in the subgroup quotient if and only if its torus
part belongs to the field-linear span of the actual integral character relations and its additive
part belongs to the actual additive relation subspace.  No connectedness, saturation,
algebraic-closedness, or extra theorem premise is used.

Direct source check and targeted leaf build pass.  Endpoint axiom audits report only
`[propext, Classical.choice, Quot.sound]`; the leaves are wired into `HTGeometry` without building
the umbrella.  This removes the previously stated need for coefficient-field descent in the
differential-to-lattice step: the theorem may be applied over `ℂ` to the same-field Hopf closure.
Card remains Stage 2 because one bridge is still open: prove that the numerical Kähler relation on
the translated exponential locus induces the corresponding zero co-Lie class for its Hopf
vanishing ideal, then complete the already-formalized character-lattice/Baker contradiction.

## Lattice descent and Baker endgame formalized (2026-08-26)

Corpus research found the existing square-family scalar-extension lemma and unconditional Baker
capstone, but not the non-square span descent or the exact mixed-lattice assembly required here.
Four small leaves close that arithmetic endgame without duplicating either component.

`LinearSpanBaseChange.lean` proves scalar-extension independence and span-membership reflection for
an arbitrary finite independent family in a finite coordinate space.  `IntegralLatticeBasis.lean`
extracts, from any finite packet of integral characters, a `ℤ`-basis made of actual integral
vectors whose rational coordinate vectors are linearly independent.  `LatticeSpanFinite.lean`
proves finite witness and independent-basis forms of membership in `latticeSpan`.

`RHTower/SchanuelLatticeBakerAssembly.lean` then proves

```text
algebraic_coefficients_eq_zero_of_latticeSpan
```

Given a rationally independent complex tuple `x`, an integral relation lattice `L`, and an
algebraic coefficient vector `c`, if `c` lies in the complex span of `L`, every exponential
character indexed by `L` is algebraic, and `c·x` is algebraic, then `c = 0`.  Span membership first
descends from `ℂ` to `Q̄`; an independent integral basis turns its characters into rationally
independent logarithms of algebraic numbers; the existing unconditional Baker theorem rules out
the resulting nonzero algebraic linear form.

All four direct checks and targeted leaf builds pass.  Endpoint axiom audits report only
`[propext, Classical.choice, Quot.sound]`; imports are wired into `HTGeometry` and `RHTower`
without building either umbrella.  Thus character-lattice descent and Baker contradiction are no
longer part of the frontier.  Card remains Stage 2 solely at the geometric differential bridge:
transport the assumed numerical Kähler relation to the co-Lie kernel of the Hopf vanishing ideal
of the translated algebraic locus and derive its algebraic character/additive coset values.

## Exact subgroup-coset relation values formalized (2026-08-26)

Fresh corpus research found the existing mixed point evaluation, Hopf zero-locus, torus-relation,
and additive-relation APIs, but no theorem transporting those relations between two points in the
same subgroup coset.  `AffineExponentialCosetRelations.lean` supplies precisely that missing glue.

For an arbitrary field, Hopf ideal `I`, and points `p,q` with `p * q⁻¹ ∈ zeroLocus I`, it proves:

```text
additiveLinearEval_eq_of_div_mem_zeroLocus
torusCharacter_eq_of_div_mem_zeroLocus
```

Every vector in the actual additive relation subspace has equal linear value at `p` and `q`, and
every character in the actual integral torus relation lattice has equal character value at `p`
and `q`.  These are direct consequences of membership in `I`; no connectedness, saturation,
algebraic-closedness, characteristic-zero, or auxiliary theorem premise is introduced.

Direct source check and targeted leaf build pass.  Endpoint axiom audits report only
`[propext, Classical.choice, Quot.sound]`; the leaf is wired into `HTGeometry` without building the
umbrella.  The card remains Stage 2 at the numerical Kähler-to-co-Lie transport.  Once that bridge
places the coefficient direction in the already-classified mixed kernel, these coset identities
supply the algebraic character and additive values consumed by the formalized Baker endgame.

## Algebraic-coset co-Lie-to-Baker assembly formalized (2026-08-26)

Fresh corpus research found no theorem joining coordinatewise algebraicity of a coset
representative to the existing relation spaces and Baker endpoint.  The new
`RHTower/SchanuelAlgebraicCosetBaker.lean` leaf supplies that exact assembly and reuses every
previous layer.

Its endpoint

```text
algebraic_coefficients_eq_zero_of_algebraic_coset_coLie
```

takes the actual exponential point `p=(x,exp x)`, a coordinatewise algebraic point `q`, membership
`p*q⁻¹` in the actual Hopf-ideal zero locus, and vanishing of the invariant direction
`(c,-c)` under the actual subgroup-quotient co-Lie map.  It concludes `c=0`.  The proof uses the
exact co-Lie kernel classification to obtain the torus lattice and additive subspace memberships,
the exact coset-value identities to make all characters and the additive form algebraic, and the
already-formalized unconditional Baker assembly to force vanishing.  Auxiliary lemmas prove
algebraicity of finite additive-linear values and Laurent characters of coordinatewise algebraic
points; no connectedness or saturation premise is introduced.

Direct source check and targeted leaf build pass.  All six new declarations audit to only
`[propext, Classical.choice, Quot.sound]`; the leaf is wired into `RHTower` without an umbrella
build.  The arithmetic, relation-classification, and coset stages are therefore closed.  Card
remains Stage 2 only at the geometric locus step: construct the algebraic coset representative and
prove that the numerical Kähler relation maps to zero in this subgroup quotient's co-Lie module.

## Exact algebraic locus point formalized (2026-08-26)

Corpus research recovered weak Nullstellensatz, mixed finite-type, and algebra-map point
representation, but no theorem applying them to the concrete `Q̄`-locus of a mixed complex point.
Two new leaves close that part of the geometric step.

`AlgebraicClosureAlgClosed.lean` proves that the relative algebraic closure of a field inside an
algebraically closed extension is itself algebraically closed.  Applied to
`algebraicClosure ℚ ℂ`, this makes the project's concrete algebraic-number field eligible for weak
Nullstellensatz without replacing it by an abstract closure.

`AffineExponentialAlgebraicLocusPoint.lean` defines the exact ideal

```text
algebraicLocusIdeal p = ker (eval over algebraicClosure ℚ ℂ at p)
```

and proves `exists_algebraic_locus_point`: every mixed complex point `p` has a point `q` with
coordinatewise algebraic additive and torus coordinates such that every `Q̄`-regular function
vanishing at `p` also vanishes at `q`.  The proof takes the finite-type quotient by that exact
kernel, applies weak Nullstellensatz over the concrete algebraic numbers, and reconstructs the
resulting algebra map as a genuine mixed point.

Both direct checks and targeted leaf builds pass.  All three new declarations audit to only
`[propext, Classical.choice, Quot.sound]`; both leaves are wired into `HTGeometry` without building
the umbrella.  Algebraic coset-point existence is no longer open.  Card remains Stage 2 only at
Kähler transport: propagate the locus differential relation through translated subgroup
generation and identify its zero class in the subgroup quotient co-Lie module.

## Translated locus subgroup and Hopf ideal formalized (2026-08-26)

Fresh corpus research found the general point-subgroup vanishing-ideal closure, but no construction
specialized to the exact algebraic-number locus and its algebraic translate.  The new
`AffineExponentialAlgebraicLocusSubgroup.lean` leaf defines the exact complex point locus, its
translate by `q⁻¹`, the subgroup generated by that translate, and the vanishing ideal of the
generated subgroup.

That vanishing ideal is an actual Hopf ideal by the existing point-subgroup closure theorem.  The
leaf proves that every translated locus point belongs to its zero locus and packages the preceding
Nullstellensatz result as

```text
exists_algebraic_coset_subgroup
```

which supplies a coordinatewise algebraic `q`, certifies that `q` lies on the exact `Q̄`-locus of
`p`, and proves `p*q⁻¹` lies in the zero locus of this actual subgroup Hopf ideal.  No finite-product
stabilization, connectedness, or saturation premise is assumed.

Direct source check and targeted leaf build pass.  All six theorem/instance declarations audit to
only `[propext, Classical.choice, Quot.sound]`; the leaf is wired into `HTGeometry` without an
umbrella build.  Thus algebraic representative, translated subgroup, Hopf ideal, and coset
membership are closed.  Card remains Stage 2 solely at one exact bridge: show the original
numerical Kähler relation induces zero of `(c,-c)` in this generated subgroup quotient's co-Lie
module.

## Exact invariant Kähler/co-Lie comparison formalized (2026-08-26)

Corpus research found general Kähler functoriality and the co-Lie-as-identity-cotangent theorem,
but no mixed invariant one-form or its point-evaluation formula.  The new
`AffineExponentialInvariantKaehler.lean` leaf defines the actual regular invariant form with torus
logarithmic coefficients `tor` and additive coefficients `add`.

It constructs pullback of Kähler differentials along the actual mixed-point evaluation map and
proves both comparison identities:

```text
kaehlerToCoLie_mixedInvariantKaehlerVector
pointKaehlerMap_mixedInvariantKaehlerVector
```

Identity pullback is exactly `mixedCoLieVector tor add`; point pullback is exactly the finite sum
of `tor_i * y_i⁻¹ dy_i` and `add_i * dx_i`.  In particular the card's coefficient direction is
literally `(c,-c)`, with no proxy class or provider hypothesis.

Direct source check and targeted leaf build pass.  All six new declarations audit to only
`[propext, Classical.choice, Quot.sound]`; the leaf is wired into `HTGeometry` without an umbrella
build.  Remaining Stage-2 gate is now only propagation: from zero point pullback on the exact
`Q̄`-locus, prove zero identity pullback after subgroup generation.  Every object on both sides of
that statement is now concrete and formalized.

## Numerical Schanuel relation identified with invariant pullback (2026-08-26)

Fresh corpus research reused the existing complex-exponential unit map; no mixed exponential point
or exact Schanuel pullback theorem existed.  `RHTower/SchanuelInvariantKaehlerForm.lean` defines the
genuine mixed point `schanuelExponentialPoint x = (x, exp x)` and proves

```text
pointKaehlerMap_schanuelInvariantVector
pointKaehlerMap_schanuelInvariantVector_eq_zero_of_relation
```

Pulling the invariant form with direction `(c,-c)` back along this point is definitionally the
finite sum `∑ c_i • schanuelDefect(x_i)`.  Consequently the card's assumed numerical relation gives
zero pullback of the exact regular invariant form, with no change of coefficient field or
derivation surrogate.

Direct source check and targeted leaf build pass.  All six new declarations audit to only
`[propext, Classical.choice, Quot.sound]`; the leaf is wired into `RHTower` without an umbrella
build.  Remaining Stage-2 gate is exactly one theorem: zero of this invariant pullback on the
exact algebraic locus propagates to zero in the co-Lie module of the subgroup generated by its
algebraic translate.

## Principal-open algebraic locus point formalized (2026-08-26)

The Kähler relation may first become a regular identity only after clearing a nonzero denominator,
so an arbitrary algebraic locus point is insufficient.  Corpus search recovered the existing
finite-type domain specialization theorem.  The new
`AffineExponentialAlgebraicLocusOpenPoint.lean` applies it to the prime kernel of mixed evaluation
and proves `exists_algebraic_locus_point_avoiding`.

For every `Q̄`-regular function `g` nonzero at `p`, the theorem chooses a coordinatewise algebraic
point `q` on the exact locus of `p` with `g(q) ≠ 0`.  Thus the eventual denominator-clearing step
can choose `q` inside the required smooth/principal open rather than silently specializing onto a
bad closed subset.

Direct source check and targeted leaf build pass.  The new theorem audits to only
`[propext, Classical.choice, Quot.sound]`; the leaf is wired into `HTGeometry` without an umbrella
build.  Remaining propagation theorem may now use an algebraic translate inside any explicitly
produced nonempty principal open.  The subgroup leaf now packages this directly as
`exists_algebraic_coset_subgroup_avoiding`; its targeted rebuild passes and the new endpoint has
the same standard axiom audit.

## Characteristic-zero field-tower Kähler injectivity formalized (2026-08-26)

Fresh corpus research found the existing ambient theorem
`algebraicIndependent_iff_kaehlerD_linearIndependent`, the transcendence-basis Kähler basis, and
the generic basis-map injectivity lemma, but no assembled theorem for an arbitrary field tower.
The new `KaehlerFieldTowerInjective.lean` leaf proves

```text
kaehlerMap_injective_of_fieldTower
```

for every characteristic-zero field tower `K → F → L`.  It chooses a transcendence basis of
`F/K`, reuses formal étaleness of the remaining separable algebraic extension to obtain a basis of
`Ω[F/K]`, and invokes the existing ambient Kähler-independence theorem to show that this basis stays
independent in `Ω[L/K]`.  This closes the function-field-to-complex injectivity needed to descend a
zero complex pullback to the generic algebraic-locus differential; no finite-generation premise or
new independence argument is introduced.

Direct source check and targeted leaf build pass.  The sole new declaration audits to only
`[propext, Classical.choice, Quot.sound]`; the leaf is wired into `HTGeometry` without an umbrella
build.  Remaining Stage-2 gate is denominator clearing followed by translation/subgroup
propagation of the resulting regular invariant differential identity.
