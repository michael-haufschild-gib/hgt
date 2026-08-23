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

