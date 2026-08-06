# Coarse/stack exactness scalar-spectrum no-go

- **ID:** `deninger-coarse-stack-exactness-spectrum-no-go`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Label:** `DAC_COARSE_STACK_EXACTNESS_SCALAR_SPECTRUM_NO_GO`
- **Parent:** `deninger-coarse-invariant-sheaf-rost-schmid-descent`
- **Statement:** if underived coarse invariants agree with derived
  quotient-stack descent, locally scalar power cohomology remains
  scalar and cannot realize the nontrivial zeta spectrum.

## Setup

Let \(G=\mathbb Q_{>0}\) act on Deninger's suspension cover
\(\widetilde X\), let
\[
 c:[\widetilde X/G]\longrightarrow X=\widetilde X/G
\]
be the map from the quotient stack to the coarse quotient, and let
\(\widetilde{\mathscr A}\) be a \(G\)-equivariant coefficient complex.
Deninger's degreewise invariant coefficient is
\[
 \mathscr A_X=c_*\widetilde{\mathscr A}
 =(\pi_*\widetilde{\mathscr A})^G.                                \tag{1}
\]
There is a canonical comparison
\[
 c_*\widetilde{\mathscr A}
 \longrightarrow
 Rc_*\widetilde{\mathscr A}.                                     \tag{2}
\]

## Theorem

`[PROVED HERE] [DAC_COARSE_STACK_EXACTNESS_SCALAR_SPECTRUM_NO_GO]`

Assume:

1. `(2)` is a quasi-isomorphism;
2. on quotient-stack cohomology, the rational power action in degree
   one is the scalar Tate action;
3. its suspension is strongly continuous.

Then Deninger's coarse invariant-sheaf \(H^1\) has scalar flow and its
generator has only the scalar Tate weight as a point eigenvalue.

## Proof

Applying \(R\Gamma(X,-)\) to `(2)` and using derived descent gives a
flow-equivariant quasi-isomorphism
\[
 R\Gamma(X,c_*\widetilde{\mathscr A})
 \simeq
 R\Gamma([\widetilde X/G],\widetilde{\mathscr A}).                 \tag{3}
\]
Thus the scalar rational-time action on stack \(H^1\) transports to
Deninger's \(H^1\).  Strong continuity and density of
\(\log\mathbb Q_{>0}\subset\mathbb R\) make the entire flow scalar.
`DAC_PURE_SUSPENSION_SCALAR_SPECTRUM_NO_GO` then implies that its
generator has no other point eigenvalue.

The nontrivial zeta divisor contains infinitely many distinct points,
so it cannot be the point spectrum of this scalar generator.

## Consequence

Any successful source construction must have a nonzero comparison
defect
\[
 \mathscr D_c
 =
 \operatorname{Cone}\!\left(
 c_*\widetilde{\mathscr A}\to
 Rc_*\widetilde{\mathscr A}\right)[-1].                            \tag{4}
\]
This conclusion does not replace Deninger's definition by derived
invariants.  It identifies the obstruction to doing so.

## Gates

- [x] dependency-closed paper proof
- [x] dense-time scalar-flow and scalar-eigenvalue core formalized in
  `DeningerArithmeticPureSuspensionNoGo.lean`
- [x] derived-topos comparison formalization in Lean

## Falsifiers and scope

- Nonzero \(\mathscr D_c\) does not prove that its cohomology contains
  zeta eigenvalues.
- Higher group cohomology alone is not Deninger's cohomology; only its
  proved interaction with `(4)` matters.
- The theorem makes no Xi, RH, positivity, or determinant assumption.

## Log

- 2026-07-26 — Isolated the canonical coarse-moduli exactness
  obstruction forced by Deninger's underived invariant sheaf.

## Lean status

### What landed

`formal/GaloisForLFunctions/RHTower/DeningerCoarseStackScalarNoGo.lean`, on top of the already
formalized dense-time core in `DeningerArithmeticPureSuspensionNoGo.lean`.  Axiom audit for all 5
declarations: `propext, Classical.choice, Quot.sound`.

- `deningerScalarFlow_transport` — **the transport step of `(3)`**: if the comparison induces an
  isomorphism intertwining the two flows, a scalar flow on the stack side is a scalar flow, with
  the same scalars, on the coarse side.  Hypothesis 1 of the theorem enters exactly here, as the
  equivariant isomorphism it provides.
- `deningerPointSpectrum`, `deningerScalarGenerator_pointSpectrum_subset` — a scalar generator has
  at most its weight in the point spectrum.
- `deningerScalarGenerator_no_two_eigenvalues`,
  `deningerScalarGenerator_not_scalar_of_two_eigenvalues` — **the conclusion**: two distinct point
  eigenvalues are impossible for a scalar generator, so a spectrum with two distinct points — in
  particular the infinite nontrivial zeta divisor — cannot be realized, and any coefficient that
  realizes it has nonzero comparison defect `(4)`.
- Hypothesis 3, strong continuity, together with the density of `log ℚ_{>0}` in `ℝ`, is
  `deningerPureSuspension_flow_eq_of_dense`; the scalar-eigenvalue step is
  `deningerPureSuspension_eigenvalue_eq_weight`.  Both were already in the tree.

### The derived-topos step `(3)` landed

The earlier record said the derived step "cannot be stated: mathlib has no derived categories of
sheaves on a site, no quotient stacks and no descent for them".  That is no longer true of the
first clause — mathlib has `DerivedCategory.Plus`, `Functor.rightDerivedFunctorPlus` and the
injective derivability structure — and the remaining two clauses are not needed: what `(3)` uses
about the quotient stack is exactly that its global sections are the coarse global sections of the
invariant pushforward, `Γ_{[X̃/G]} = Γ_X ∘ c_*`, which is Deninger's definition `(1)`.  So the
derived step is Grothendieck's composition law for right derived functors, and that law was the
one genuinely missing ingredient.  It is now built.

**The composition law**, new infrastructure, absent from mathlib:
`formal/GaloisForLFunctions/HTGeometry/DerivedFunctorPlusComposition.lean`.  Axiom audit for all 5
declarations: `propext, Classical.choice, Quot.sound`.

- `HTGeometry.derivedCompUnit` — the comparison `(G∘F)_* ⟶ Q ∘ (RF ⋙ RG)`, built from the unit of
  `RG` at the `F`-image followed by `RG` applied to the unit of `RF`.
- `HTGeometry.derivedCompUnit_app_isIso` — it is invertible on a bounded below complex of
  injectives.  This is where preservation of injectivity by `F` enters, and nowhere else: the
  `F`-image of a complex of injectives is a complex of injectives, so the unit of `RG` is
  invertible there.
- `HTGeometry.rightDerivedFunctorPlusCompIso` — **`R(G ∘ F) ≅ RF ⋙ RG`** on the bounded below
  derived categories, for additive `F : C ⥤ D`, `G : D ⥤ E` between abelian categories with `C`
  and `D` having enough injectives and `F` preserving injective objects.  Both sides are right
  derived functors of the same functor, and right derived functors are unique.

**The card's derived-topos comparison**:
`formal/GaloisForLFunctions/RHTower/DeningerDerivedToposComparison.lean`.  Axiom audit for all 5
declarations: `propext, Classical.choice, Quot.sound`.

- `deningerCoarsePushforward_preservesInjectives` — **`c_*` preserves injectives**, because it is
  right adjoint to the exact pullback `c^*`.  This is not an assumption of the card; it is the
  standard property of a coarse-moduli pushforward, and it is what licenses the composition law.
- `deningerCoarseComparison` — **equation `(2)`**, `c_* Ã ⟶ R c_* Ã`.  In the bounded below
  derived category the canonical comparison *is* the unit of the right derived functor of `c_*`,
  so hypothesis 1 of the theorem is literally the invertibility of that unit at `Ã`.
- `deningerStackGlobalSections` — `Γ_{[X̃/G]} = Γ_X ∘ c_*`, the definition `(1)` read on global
  sections.
- `deningerDerivedDescentIso` — **derived descent for the quotient stack**, `RΓ_{[X̃/G]} ≅
  RΓ_X ∘ Rc_*`.
- `deningerDerivedToposComparisonIso` — **equation `(3)`**: assuming `(2)` is a quasi-isomorphism
  at `Ã`, applying `RΓ(X,−)` to it and composing with derived descent gives
  `RΓ(X, c_* Ã) ≅ RΓ([X̃/G], Ã)`.

**Non-vacuity at an actual quotient stack**:
`formal/GaloisForLFunctions/RHTower/DeningerQuotientStackPointDescent.lean` instantiates the whole
comparison at `c : [pt/G] → pt`, where sheaves on the stack are `G`-representations and `c_*` is
the invariants functor.  Axiom audit for all 7 declarations:
`propext, Classical.choice, Quot.sound`.  Three of its facts were also missing from mathlib:
`deningerRepEnoughInjectives` (`Rep k G` has enough injectives, transported along the equivalence
with modules over the monoid algebra), `deningerTrivialFunctor_preservesFiniteLimits` (the trivial
representation is exact, being right adjoint to coinvariants), and
`deningerInvariants_preservesInjectiveObjects` (hence `(−)^G` preserves injectives — unconditional
here, not assumed).  `deningerRepHasDerivedCategory` and `deningerModuleHasDerivedCategory` record
that the derived categories exist, so the statements are not vacuous.

Together with the consequence chain already formalized — transport of scalarity, dense-time
rigidity, and the impossibility of two distinct eigenvalues — the card is complete.

- 2026-08-06 — Closed the derived-topos gate.  Built Grothendieck's composition law for right
  derived functors on the bounded below derived category, which mathlib lacked, and used it to
  prove equation `(3)`; instantiated the whole comparison at the quotient stack of a point, which
  required building enough injectives for `Rep k G` and exactness of the trivial representation.
  Card moves to `3-formalized`.
