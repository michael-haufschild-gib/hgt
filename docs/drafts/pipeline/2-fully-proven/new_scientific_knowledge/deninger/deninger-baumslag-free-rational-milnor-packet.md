# Baumslag free-rational Milnor packet

- **ID:** `deninger-baumslag-free-rational-milnor-packet`
- **Stage:** 2-fully-proven
- **Type:** SOURCE FINITE-STAGE TOPOLOGICAL THEOREM
- **Label:** `DAC_BAUMSLAG_FREE_RATIONAL_MILNOR_PACKET`
- **Parent:** `deninger-baumslag-milnor-pro-realization`
- **Lean modules:**
  `GaloisForLFunctions.RHTower.DeningerUniquelyDivisibleKernel` (clauses 1 and 2),
  `GaloisForLFunctions.RHTower.DeningerDegreeOneInflation` (the degree-one reduction of clause 3),
  `GaloisForLFunctions.RHTower.DeningerMilnorAmplitude` and
  `GaloisForLFunctions.RHTower.DeningerTwoTermFormality` (the square-zero product and the formality
  of clause 4),
  `GaloisForLFunctions.RHTower.DeningerBaumslagRationalization` (the rationalization itself, its
  universal property, and the surjection `(1)`),
  `GaloisForLFunctions.RHTower.DeningerBaumslagDegreeOne` (clause 3 and `H^1 ≅ U`),
  `GaloisForLFunctions.RHTower.DeningerBaumslagRationalProjective` (the splitting of central
  extensions, i.e. `H^2(BR_U;ℚ) = 0`),
  `GaloisForLFunctions.RHTower.DeningerBaumslagPullback` (clause 5's finite-cover consequence),
  `GaloisForLFunctions.RHTower.DeningerBaumslagFunctorial` (functoriality and `GL`/power-map
  equivariance),
  `GaloisForLFunctions.RHTower.DeningerBaumslagH2` (`H² = 0` in mathlib's group cohomology),
  `GaloisForLFunctions.RHTower.DeningerBaumslagH1` (`H¹ ≅ U` in mathlib's group cohomology),
  `GaloisForLFunctions.RHTower.DeningerBaumslagEquivariance` (equivariance under a group acting on
  the chosen family),
  `GaloisForLFunctions.RHTower.DeningerFreeGroupH2` (`H²(F_m; A) = 0` for arbitrary coefficients),
  `GaloisForLFunctions.RHTower.DeningerFreeGroupH1` (`H⁰` and `H¹` of a free group),
  `GaloisForLFunctions.RHTower.DeningerCohomologyDimensionShift` (`Hⁿ(F_m; A) = 0` for all `n ≥ 2`),
  `GaloisForLFunctions.RHTower.DeningerBaumslagComparison` (`H^*(R_U;ℚ) ≅ H^*(F_m;ℚ)` in degrees
  `≤ 2`),
  `GaloisForLFunctions.RHTower.DeningerRootAdjunction` and
  `GaloisForLFunctions.RHTower.DeningerRootAdjunctionNoGo` (root adjunction, and why the naive tower
  fails),
  `GaloisForLFunctions.RHTower.DeningerBaumslagGeneration` (generation, torsion freeness, and root
  transfer),
  `GaloisForLFunctions.RHTower.DeningerRationalPower` (rational powers in a group with unique
  roots),
  `GaloisForLFunctions.RHTower.DeningerRationalFreeDGroup` (`Bau(ℤ) ≅ ℚ`),
  `GaloisForLFunctions.RHTower.DeningerBaumslagAbelian` (root-closed centralizers; `Bau` of an
  abelian group is abelian),
  `GaloisForLFunctions.RHTower.DeningerRatVectorSpace` (an abelian group with unique roots is a
  rational vector space),
  `GaloisForLFunctions.RHTower.DeningerPermutationShapiro` (Shapiro's lemma for permutation
  representations),
  `GaloisForLFunctions.RHTower.DeningerPushoutLength` (word length in an amalgamated free product),
  `GaloisForLFunctions.RHTower.DeningerBassSerreTree` (the tree of cosets and its augmented
  complex),
  `GaloisForLFunctions.RHTower.DeningerPushoutFirstLetter` (the sharp length law),
  `GaloisForLFunctions.RHTower.DeningerTreeAcyclic` (acyclicity of the tree of cosets),
  `GaloisForLFunctions.RHTower.DeningerTreeShortExact` (the tree sequence as a short exact sequence
  of representations),
  `GaloisForLFunctions.RHTower.DeningerPermutationSum` (permutation representations of disjoint
  unions),
  `GaloisForLFunctions.RHTower.DeningerHomologyAdditive` (group homology is an additive functor),
  `GaloisForLFunctions.RHTower.DeningerTreeTwoFactor` (the tree of a two factor amalgam),
  `GaloisForLFunctions.RHTower.DeningerTreeHomology` (the homology of the tree modules),
  `GaloisForLFunctions.RHTower.DeningerTreeVanishing` (vanishing for an amalgam),
  `GaloisForLFunctions.RHTower.DeningerCyclicHomology` (the regular representation and the infinite
  cyclic group),
  `GaloisForLFunctions.RHTower.DeningerAmalgamCyclic` (the root adjunction step),
  `GaloisForLFunctions.RHTower.DeningerHomologyUnion` (homology of an increasing union),
  `GaloisForLFunctions.RHTower.DeningerPushoutConcat` (length of a product of alternating letters),
  `GaloisForLFunctions.RHTower.DeningerPushoutPower` (length of a power),
  `GaloisForLFunctions.RHTower.DeningerPushoutDecomp` (the letter decomposition of an element),
  `GaloisForLFunctions.RHTower.DeningerPushoutInv` (word length of an inverse),
  `GaloisForLFunctions.RHTower.DeningerPushoutMerge` (merging a letter into a word),
  `GaloisForLFunctions.RHTower.DeningerCyclicReduction` (cyclic reduction),
  `GaloisForLFunctions.RHTower.DeningerPushoutTorsion` (amalgams of torsion free groups),
  `GaloisForLFunctions.RHTower.DeningerPushoutNormal` (uniqueness of transversal words),
  `GaloisForLFunctions.RHTower.DeningerPushoutRoot` (equal powers of cyclically reduced elements),
  `GaloisForLFunctions.RHTower.DeningerPushoutMetric` (subadditivity of the word length),
  `GaloisForLFunctions.RHTower.DeningerPushoutOrder` (cyclically reduced elements have infinite
  order),
  `GaloisForLFunctions.RHTower.DeningerCycLenEq` (equal powers have cyclic reductions of equal
  length),
  `GaloisForLFunctions.RHTower.DeningerTransversalForm` (transversal form of a word),
  `GaloisForLFunctions.RHTower.DeningerWordMerge` (merging letters at the ends of a word),
  `GaloisForLFunctions.RHTower.DeningerConjWord` (normal word of a conjugated power),
  `GaloisForLFunctions.RHTower.DeningerConjNormalize` (normalizing a conjugator),
  `GaloisForLFunctions.RHTower.DeningerBaseLength` (the base group preserves the word length),
  `GaloisForLFunctions.RHTower.DeningerConjSplit` (splitting a conjugated power),
  `GaloisForLFunctions.RHTower.DeningerPowWord` (the normal word of a power),
  `GaloisForLFunctions.RHTower.DeningerRotate` (rotation is conjugation),
  `GaloisForLFunctions.RHTower.DeningerFlattenRotate` (dropping from a concatenation of copies),
  `GaloisForLFunctions.RHTower.DeningerFlattenDrop` (dropping whole and partial copies),
  `GaloisForLFunctions.RHTower.DeningerRotateCompare` (comparing two descriptions of a list),
  `GaloisForLFunctions.RHTower.DeningerLeadLetter` (the leading letter of an uncancelled product),
  `GaloisForLFunctions.RHTower.DeningerCancelCriterion` (when a product cancels),
  `GaloisForLFunctions.RHTower.DeningerMergeDichotomy` (the merge dichotomy),
  `GaloisForLFunctions.RHTower.DeningerLeadSurvives` (the leading letter survives a short factor),
  `GaloisForLFunctions.RHTower.DeningerPrefixConj` (the conjugator is a prefix),
  `GaloisForLFunctions.RHTower.DeningerAbsorbRight` (absorbing the base group into the last letter),
  `GaloisForLFunctions.RHTower.DeningerCycStepCases` (the two cases of a reduction step),
  `GaloisForLFunctions.RHTower.DeningerCycData` (the cyclic reduction data),
  `GaloisForLFunctions.RHTower.DeningerSuffixIndex` (suffixes of words differing in the last letter),
  `GaloisForLFunctions.RHTower.DeningerPrefixTransfer` (transferring a prefix),
  `GaloisForLFunctions.RHTower.DeningerPrefixTransferGen` (transferring a prefix across a changed
  tail),
  `GaloisForLFunctions.RHTower.DeningerCycReassemble` (reassembling the data after a step),
  `GaloisForLFunctions.RHTower.DeningerCycBase` (the base case),
  `GaloisForLFunctions.RHTower.DeningerCycDecomp` (decomposing a non cyclically reduced word),
  `GaloisForLFunctions.RHTower.DeningerCycRecursion` (the cyclic reduction recursion),
  `GaloisForLFunctions.RHTower.DeningerWordIndices` (the index sequence is an invariant),
  `GaloisForLFunctions.RHTower.DeningerHeadOnly` (words transversal except at the front),
  `GaloisForLFunctions.RHTower.DeningerPowerLength` (the length of a power),
  `GaloisForLFunctions.RHTower.DeningerTwoExponent` (the two exponent comparison),
  `GaloisForLFunctions.RHTower.DeningerRotateCycRed` (rotations of a cyclically reduced word),
  `GaloisForLFunctions.RHTower.DeningerConjLetter` (conjugating by a letter),
  `GaloisForLFunctions.RHTower.DeningerConjHead` (incomplete cancellation),
  `GaloisForLFunctions.RHTower.DeningerConjLast` (cancellation at the back)

## Statement

Let \(U\) be an \(m\)-dimensional rational vector space.  After choosing a
basis of the dual \(A=U^\vee\), let \(F_m\) be the free group on that basis
and let
\[
 R_U:=\operatorname{Bau}(F_m)
\]
be its Baumslag rationalization.  Then there is a surjective homomorphism
\[
 a_U:R_U\twoheadrightarrow A                                      \tag{1}
\]
such that:

1. \(R_U\) and \(K_U:=\ker(a_U)\) are uniquely divisible;
2. \(K_U\) has no nontrivial finite quotient;
3. the induced map
   \[
   Ba_U:BR_U\longrightarrow BA=K(A,1)                              \tag{2}
   \]
   is an isomorphism on \(H^1(-;\mathbb Q)\);
4. the rational cohomology algebra is
   \[
   H^\ast(BR_U;\mathbb Q)\cong\mathbb Q\oplus U[-1],\qquad U^2=0;   \tag{3}
   \]
   and any connected rational CDGA cochain model of \(BR_U\) is formal;
5. the homotopy fiber of `(2)` is connected and has fundamental group
   \(K_U\).  Consequently every homotopy pullback of `(2)` has a connected
   divisible \(\pi_1\)-kernel over its base and preserves finite covering
   categories by `DAC_DIVISIBLE_FIBER_FINITE_COVER_INVARIANCE`.

The packet is noncanonical because a basis of \(A\) was chosen.

## Proof

Send the free generators of \(F_m\) to the chosen basis of \(A\).  Since
\(A\) is a rational group, the universal property of Baumslag
rationalization extends this surjection uniquely to `(1)`.

By definition \(R_U\) is uniquely divisible.  If \(k\in K_U\) and
\(x^n=k\) in \(R_U\), then
\[
 n\,a_U(x)=a_U(k)=0.
\]
The rational vector space \(A\) is torsion-free, so \(a_U(x)=0\); uniqueness
of roots in \(R_U\) shows that \(K_U\) is uniquely divisible.  Its finite
quotients are trivial by
`DAC_DIVISIBLE_FIBER_FINITE_COVER_INVARIANCE`.

Casacuberta--Peschke's theorem for free groups, as summarized by Ivanov,
gives
\[
 H_\ast(R_U;\mathbb Q)\cong H_\ast(F_m;\mathbb Q).
\]
The latter is \(\mathbb Q\) in degree zero, \(\mathbb Q^m\) in degree one,
and zero above degree one.  Universal coefficients yield `(3)`, including
the square-zero product.  The map `(1)` is the rational abelianization on
degree one, giving clause 3.  `DAC_TWO_TERM_CDGA_FORMALITY` gives the final
formality assertion.

Since `(1)` is surjective, the homotopy fiber of the map of classifying
spaces is \(BK_U\), hence connected with fundamental group \(K_U\).
Homotopy pullback preserves that fiber.  Clause 5 follows from the
divisible-fiber theorem.

## Formalized statement

`GaloisForLFunctions/RHTower/DeningerUniquelyDivisibleKernel.lean` proves clauses 1 and 2 in the
generality in which the card's own proof argues them — nothing about Baumslag rationalization is
used, only unique divisibility of `R_U` and torsion-freeness of `A`:

- `DeningerUniquelyDivisible R` : every element has a unique `n`-th root for every `n ≥ 1`;
- `deningerPowerDivisible_of_uniquelyDivisible` : unique divisibility implies divisibility;
- `deningerKer_uniquelyDivisible` : for `f : R →* A` with `R` uniquely divisible and `A`
  torsion-free, `ker f` is uniquely divisible.  This is clause 1, and the proof is the card's:
  the `n`-th root `x` of `k ∈ ker f` satisfies `f(x)ⁿ = 1`, so `f(x) = 1` by torsion-freeness,
  and uniqueness in `R` gives uniqueness in `ker f`;
- `deningerKer_noFiniteQuotient` : that kernel admits no nontrivial homomorphism to a finite
  group.  This is clause 2, obtained from
  `DAC_DIVISIBLE_FIBER_FINITE_COVER_INVARIANCE` as already formalized in
  `GaloisForLFunctions.RHTower.DeningerDivisibleFiberFiniteCoverInvariance`, exactly as the card
  cites it.

### What is formalized and what is not

Formalized: clauses 1 and 2, unconditionally.  `DeningerUniquelyDivisible` and
`deningerPowerDivisible_of_uniquelyDivisible` use no axioms at all;
`deningerKer_uniquelyDivisible` uses only `propext`.

**The construction `R_U = Bau(F_m)` and the surjection `(1)` are now formalized**, in
`GaloisForLFunctions/RHTower/DeningerBaumslagRationalization.lean`.  Groups with unique roots are
the models of an equational theory — adjoin a unary `root n` for every `n`, subject to
`(root n x)^{n+1} = x` and `root n (x^{n+1}) = x`, from which uniqueness of roots *follows* — so the
theory is a variety and the forgetful functor to groups has a left adjoint.  `DeningerBau G` is that
adjoint, built as the term algebra on `G` modulo the congruence generated by the group axioms, the
homomorphism axioms for the unit, and the two root axioms.

- `DeningerBau.uniquelyDivisible` — the rationalization has unique roots (axiom audit: `propext,
  Quot.sound`, no choice).
- `deningerBauLift`, `deningerBauLift_comp`, `deningerBauLift_unique` — **the universal property**.
  Uniqueness needs no compatibility hypothesis with roots: a homomorphism between groups with unique
  roots preserves them automatically (`deningerMap_root`), so agreeing on `G` forces agreement
  everywhere.
- `deningerMultiplicative_uniquelyDivisible` — a rational vector space, written multiplicatively,
  has unique roots, so it is a legitimate target.
- `deningerBauFree_surjective` — **the surjection `(1)`**: the image of the lift is a subgroup
  closed under roots, hence (`deningerRootSubmodule`) a rational subspace, and it contains the
  spanning family, so it is everything.
- `deningerBauFreeKer_uniquelyDivisible`, `deningerBauFreeKer_noFiniteQuotient` — clauses 1 and 2
  **at the actual object** `K_U = ker(a_U)`, rather than in the abstract generality of the earlier
  record.

What the construction does not claim is that the unit `G → Bau(G)` is injective; that is Baumslag's
embedding theorem, and neither `(1)` nor clauses 1--2 use it.

Not formalized, and none of it is a mathlib gap of the ordinary kind:

- clause 4 **above degree two** — the vanishing `H^n(BR_U;ℚ) = 0` for `n ≥ 3`.  This is *statable*:
  mathlib has `groupCohomology` in every degree, so the goal is literally
  `groupCohomology (Rep.trivial ℚ R_U ℚ) n = 0` for `n ≥ 3`.  What is missing is a proof.  The
  splitting argument that gives degrees one and two does not reach degree three: dimension shifting
  reduces `H³(G;ℚ)` to `H²(G;Q)` with `Q = Fun(G,ℚ)/ℚ`, and although the norm maps on `Q` are
  surjective — so the twisted extension is divisible — they are not injective, so the extension does
  not have *unique* roots and the universal property of the rationalization does not apply.  Closing
  it needs the Casacuberta--Peschke computation or an equivalent resolution;
- clause 5's *topological* half — that the homotopy fibre of `Ba_U` is `BK_U` — which needs
  classifying spaces.

**Clause 5's consequence is proved at the actual object.**  The homotopy pullback has no mathlib
counterpart, but its group-theoretic shadow does: the fibre product of `a_U` along any homomorphism
`H → A`.  `GaloisForLFunctions/RHTower/DeningerBaumslagPullback.lean`:

- `deningerBauPullback` — the fibre product, as the equalizer subgroup of `H × R_U`;
- `deningerBauPullbackProj_surjective` — it surjects onto `H`, because `a_U` does;
- `deningerBauPullbackProj_ker_divisible` — its kernel is `K_U`, hence divisible: the `n`-th root of
  `(1, r)` is `(1, u)` with `u` the root of `r` inside `K_U`;
- `deningerBauPullbackFiniteActionEquiv`, `deningerBauPullbackProfiniteIso` — the divisible-fibre
  theorem applied verbatim: the pullback induces an equivalence of finite covering categories and an
  isomorphism of profinite completions.  This is exactly what clause 5 asserts of every homotopy
  pullback of `(2)`.

**Degrees one and two of clause 4 are proved, and neither uses Casacuberta--Peschke.**

`deningerBauFree_degreeOne_equiv` is `H^1(BR_U;ℚ) ≅ U`: first cohomology with trivial rational
coefficients is the group of homomorphisms, clause 3 identifies that with the homomorphisms out of
`A = U^∨`, additive maps between rational vector spaces are linear, and for a reflexive `U` the
double dual is `U` again.  **That identification is also stated in mathlib's group cohomology**, in
`GaloisForLFunctions/RHTower/DeningerBaumslagH1.lean`: with a trivial action the `1`-coboundaries
vanish (`deningerCoboundaries₁_trivial`), so `H¹` is the module of `1`-cocycles
(`deningerH1Equiv`), and a `1`-cocycle for a trivial action is exactly a homomorphism
(`deningerCocycles₁Equiv`); composing with clause 3 gives
`deningerBauFree_H1_equiv : groupCohomology.H1 (Rep.trivial ℚ R_U ℚ) ≃ U`.

`GaloisForLFunctions/RHTower/DeningerBaumslagRationalProjective.lean` gives degree two.  Second
cohomology with trivial coefficients classifies central extensions, and every central extension of
`R_U` by a uniquely divisible abelian group splits:

- `deningerUniquelyDivisible_of_central` — a central extension of a group with unique roots by a
  subgroup with unique roots again has unique roots.  The root of `e` is `h·κ⁻¹`, where `h` lifts
  the root downstairs and `κ` is the central root of the discrepancy `e⁻¹h^n`; uniqueness comes
  from uniqueness downstairs plus torsion-freeness of the kernel.
- `deningerBauFree_projective` — **the rationalization of a free group is projective for surjections
  from groups with unique roots**: lift the free generators arbitrarily, extend over the
  rationalization by its universal property, and the composite with the surjection agrees with the
  identity on the generators, hence is the identity.
- `deningerBauFree_centralExtension_splits` — the two combined: every central extension with
  uniquely divisible kernel splits.

**And that vanishing is now stated in mathlib's group cohomology, not paraphrased.**
`GaloisForLFunctions/RHTower/DeningerBaumslagH2.lean` closes the loop:
`deningerBauFree_H2_eq_zero` is `groupCohomology.H2 (Rep.trivial ℚ R_U M) = 0` for every rational
vector space `M` with trivial action.  mathlib has no bridge from `H²` to central extensions, so the
bridge is built here: a normalized `2`-cocycle twists `M × G` into a group (`DeningerCocycleExt`),
associativity being exactly the cocycle identity and the inverse existing because
`f(g⁻¹,g) = f(g,g⁻¹)` follows from it; the kernel is `M`, central and uniquely divisible; the
splitting supplies a `1`-cochain `b` with `f(g,h) = b(gh) - b(g) - b(h)`, which is `d₁₂` of
`g ↦ c₀ - b g` once the cocycle is normalized by subtracting `f(1,1)`.

**Clause 3 no longer needs any of that.**  With trivial rational coefficients first cohomology is
the group of homomorphisms, so the degree-one comparison along `a_U` is restriction of
homomorphisms, and that is bijective for a purely formal reason.  The target is a rational vector
space, hence has unique roots, so by the universal property homomorphisms out of `Bau(F_m)`
correspond to homomorphisms out of `F_m`, which correspond to arbitrary functions on the basis —
and those are exactly the homomorphisms out of `A`, by the basis's own universal property.  So the
adjunction does what the card's proof delegated to Casacuberta--Peschke.
`GaloisForLFunctions/RHTower/DeningerBaumslagDegreeOne.lean`:

- `deningerBauFreeHom_factors` — every homomorphism from the rationalization into a rational vector
  space factors through `a_U`;
- `deningerBauFree_degreeOne_bijective` — **clause 3**: the degree-one comparison is an
  isomorphism;
- `deningerBauFreeKer_killed` — equivalently, every such homomorphism kills `K_U`, which is the
  vanishing the card's degree-one reduction asked for.

**The free-group input of the card's proof, completely.**  The card's proof quotes `H_*(F_m;ℚ)` as
`ℚ`, `ℚ^m`, `0, 0, …`.  That computation is now proved in *every* degree, unconditionally, and for
arbitrary coefficients — `H⁰ = M`, `H¹ = (ι → M)`, and `Hⁿ = 0` for all `n ≥ 2`.

`GaloisForLFunctions/RHTower/DeningerFreeGroupH1.lean` does the first two, for an arbitrary
coefficient ring:

- `deningerTrivial_H0_equiv` — `H⁰(G; M) ≅ M` for a trivial module, so `H⁰(F_m;ℚ) = ℚ`;
- `deningerFreeGroupCocycles₁Equiv` — **`Z¹(F_ι; A) ≃ (ι → A)`** for *every* representation `A`: a
  `1`-cocycle is a section of the semidirect product, and over a free group a section is an
  arbitrary choice of values on the generators;
- `deningerCoboundaries₁_trivial'`, `deningerTrivial_H1_equiv` — with a trivial action the
  coboundaries vanish, so `H¹` is the cocycles;
- `deningerFreeGroup_H1_equiv` — **`H¹(F_ι; M) ≃ (ι → M)`**, which for `|ι| = m` and `M = ℚ` is the
  card's `ℚ^m`.

Degree two is in `GaloisForLFunctions/RHTower/DeningerFreeGroupH2.lean`:
`deningerFreeGroup_H2_eq_zero` is `H²(FreeGroup ι; A) = 0` for every representation `A`.  The
mechanism is the same twisted extension as for `R_U`, but no divisibility is needed — a section is
defined on the free generators and the composite with the projection is the identity because it is
so on generators.  `DeningerTwistedExt` carries the construction for a non-trivial action:
associativity is the cocycle identity together with `ρ(gh) = ρ(g)ρ(h)`, and the inverse needs no
extra identity.

All higher degrees follow by dimension shifting, in
`GaloisForLFunctions/RHTower/DeningerCohomologyDimensionShift.lean`:

- `deningerIsZero_coind_succ` — coinduction from the trivial subgroup is cohomologically trivial in
  positive degrees, by Shapiro's lemma and the vanishing over the trivial group;
- `deningerCoindShortComplex_shortExact` — the unit of restriction–coinduction is a monomorphism
  (it is a split mono after restriction, and restriction is faithful), so it and its cokernel form a
  short exact sequence;
- `deningerIsZero_succ_of_isZero` — the connecting map of that sequence is therefore an isomorphism
  `Hⁿ⁺¹(coker) ≅ Hⁿ⁺²(A)`;
- `deningerFreeGroup_isZero_succ_succ` — **`Hⁿ(F_ι; A) = 0` for every `n ≥ 2` and every
  representation `A`**, by induction from degree two.  This is the cohomological dimension of a free
  group, which mathlib does not have.

**The Casacuberta--Peschke comparison itself, in the degrees that are computed here.**  The card's
proof quotes `H_*(R_U;ℚ) ≅ H_*(F_m;ℚ)`.  In degrees zero, one and two that comparison is now proved
outright, with no import, in `GaloisForLFunctions/RHTower/DeningerBaumslagComparison.lean`:

- `deningerBauHomEquiv` — the adjunction as an explicit bijection `Hom(Bau G, H) ≃ Hom(G, H)` for
  any `H` with unique roots.  This is what makes the comparison a theorem rather than an import;
- `deningerBau_H0_equiv`, `deningerBau_H1_equiv`, `deningerBau_isZero_H2` — `H⁰(R_U;M) ≅ M`,
  `H¹(R_U;M) ≃ (ι → M)` — the same answer as for `F_m` — and `H²` zero on both sides.

So the imported computation is needed only from degree three on.

**The missing degrees, and a route that is now closed off.**  The remaining vanishing needs the
homology of `R_U`, which Casacuberta--Peschke compute along a tower of amalgamated free products.
The single root adjunction is built in `GaloisForLFunctions/RHTower/DeningerRootAdjunction.lean`:
`DeningerRootAdjoin g n` amalgamates `G` with an infinite cyclic group over the cyclic subgroups
generated by `g` and by the `n`-th power of the new generator.  `deningerRootAdjoin_root_pow` is the
defining property — the new generator is an `n`-th root of `g` — and
`deningerRootAdjoin_of_injective` is faithfulness, from mathlib's `PushoutI.of_injective` and the
infinite order of `g`.

**But the naive tower of such adjunctions does not converge to `Bau(G)`**, and
`GaloisForLFunctions/RHTower/DeningerRootAdjunctionNoGo.lean` proves why.  Adjoining a square root
`t` of `a²` to the free group on two generators produces a group in which `t` and `a` are *distinct*
square roots of the same element: a homomorphism onto `ℤ/2` sending `a` to `1` and `t` to `0`
separates them, and it is compatible with the amalgamation because `a²` and `t²` both go to `0`.  So
`deningerRootAdjoin_not_uniquelyDivisible` — a stage of the naive tower is not a group with unique
roots, hence does not embed in one, hence the tower's maps to `Bau(G)` are not injective.

A correct construction must adjoin roots only where they are missing, or quotient at each stage;
that is the content of Baumslag's theorem, and it is what remains.  Note that *identifying* the
eventual colimit with `Bau(G)` needs no normal-form theorem — a uniquely divisible colimit with the
universal property is the rationalization by uniqueness of adjoints — so the whole difficulty is
keeping roots unique.

**The scale of what remains.**  The *base case* is available after all: mathlib proves
`IsMulTorsionFree (FreeGroup α)` in `Mathlib/GroupTheory/FreeGroup/CyclicallyReduced.lean`, whose
content is exactly `x ^ n = y ^ n → x = y` — free groups have unique roots.  (The previous record
here said otherwise; that was wrong.)  What remains is the inductive step: that root adjunction, done
where roots are missing, preserves unique roots.  That is Baumslag's theorem, and it needs the
normal-form theory for amalgams (`PushoutI.NormalWord`, which mathlib has).

Toward it, `DeningerRationalPower.lean` proves the structural fact that makes `R`-groups
`ℚ`-powered:

- `deningerRoot_pow_root` — roots refine: the `(a+1)(b+1)`-st root of `h`, raised to `b+1`, is the
  `(a+1)`-st root, because both are `(a+1)`-st roots of `h` and roots are unique;
- `deningerRootPow_congr` — consequently `(root_d h) ^ n` depends only on the rational `n/(d+1)`;
- `deningerRatPow` — so each element carries a homomorphism `Multiplicative ℚ →* H`.

This is what makes the rank-one rationalization computable, and it is the first place the unique-root
hypothesis is used as *structure* rather than as a cancellation law.

**The rank-one packet is now computed.**  `DeningerRationalFreeDGroup.lean` proves
`deningerBauIntEquivRat : Bau(Multiplicative ℤ) ≃* Multiplicative ℚ` — the first actual computation
of a Baumslag rationalization, and the case `dim U = 1` of the packet.  The argument is that
`Multiplicative ℚ` has the *same* universal property: `deningerRatPow_unique` says a homomorphism out
of it into a group with unique roots is determined by the image of the generator, because the value
at `1/d` is forced to be the `d`-th root of the value at `1`.  Two objects with the same universal
property are isomorphic, and both composites are identified by the corresponding uniqueness
statements.

This is also a check on the term-algebra construction: it produces the classically expected object in
the one-generator case, rather than something larger.

**Centralizers in a group with unique roots are root closed**, and the abelian case follows.
`DeningerBaumslagAbelian.lean`:

- `deningerCommute_of_commute_pow` — if `x` commutes with `y^(n+1)` then it commutes with `y`,
  because conjugation by `x` sends `y` to another `(n+1)`-st root of `y^(n+1)`, and roots are
  unique.  Axiom audit: `propext` only;
- `deningerRoot_commute` — hence roots of commuting elements commute;
- `DeningerBau.commute_of_commGroup` and the `CommGroup` instance — **`Bau(G)` is abelian whenever
  `G` is**: the centralizer of any element is root closed and contains the image of `G`, so by the
  generation lemma it is everything.

This is the structural input for the packet's target side, where `A` is abelian, and it is what makes
`Bau(ℤ) ≅ ℚ` a special case rather than an accident.

**An abelian group with unique roots is a rational vector space.**  `DeningerRatVectorSpace.lean`
turns the root operations into a `ℚ`-action:

- `deningerRoot_mul`, `deningerRoot_zpow` — in the abelian case each root operation is a group
  homomorphism and commutes with integer powers, both by uniqueness of roots;
- `deningerRoot_root` — the `m`-th root of the `n`-th root is the `mn`-th root;
- `deningerRatModule` — the `ℚ`-module structure on `Additive H`, with `q • x` the rational power.
  The scalar associativity axiom is the content: it is exactly the composition law for roots
  together with the fact that `n₁n₂/(d₁d₂)` and the reduced form of `q₁q₂` give the same rational
  power;
- `deningerRatLinearMap` — every homomorphism between abelian groups with unique roots is
  automatically `ℚ`-linear, since homomorphisms preserve roots.  So the rationalization of abelian
  groups is a functor to `ℚ`-vector spaces, and `deningerBauRatLift` is the universal property in
  that category;
- `deningerRatModule_unique` — this structure is the only one, by mathlib's uniqueness of `ℚ`-module
  structures.  There is no choice being made.

mathlib knows a `ℚ`-module structure is unique when it exists but has no existence statement of this
kind, so this is new infrastructure.

### The route to clause (4) in degrees `≥ 3`

The degrees `0, 1, 2` are literal in mathlib's `groupCohomology`, which is why they are done.  For
all degrees the argument has to change shape, and the shape it has to take is this:

1. `Bau(F)` is the colimit of the tower of root adjunctions `A ↦ A *_{⟨g⟩ = ⟨t^n⟩} ⟨t⟩`.
2. Each step is an amalgamated free product over an infinite cyclic group, and `⟨g⟩ → ⟨t⟩` is an
   isomorphism on `H_*(-;ℚ)` — on `H_1` it is multiplication by `n`, invertible over `ℚ`.  So by
   Mayer–Vietoris each step is a `ℚ`-homology isomorphism.
3. Homology commutes with filtered colimits of groups, so `H_*(Bau F;ℚ) = H_*(F;ℚ)`, which vanishes
   above degree one.
4. Over a field, cohomology is the dual of homology, so `H^n(Bau F;ℚ) = 0` for `n ≥ 2`.

The argument must run in **homology**, not cohomology: cohomology does not commute with filtered
colimits.  Step 2 needs Mayer–Vietoris for amalgamated free products, which mathlib does not have;
the standard construction of it is the short exact sequence of the Bass–Serre tree,

  `0 → k[E] → k[V] → k → 0`,

with `E` and `V` disjoint unions of coset spaces, whose long exact sequence in `H_*(G;-)` becomes
Mayer–Vietoris once each `H_*(G;k[G ⧸ S])` is identified with `H_*(S;k)`.

That identification is now built.  `DeningerPermutationShapiro.lean`:

- `deningerIndTrivialIso` — `Ind_S^G(k) ≅ k[G ⧸ S]`, the induced representation of the trivial
  representation of a subgroup is the permutation representation on its cosets.  The map sends
  `⟦h ⊗ c⟧` to the basis element at the coset of `h⁻¹`; the inversion is what converts mathlib's
  right-handed coinvariants convention into left cosets;
- `deningerPermutationShapiro` — `H_n(G; k[G ⧸ S]) ≅ H_n(S; k)`, by composing that isomorphism with
  mathlib's Shapiro lemma for induced representations.

mathlib has Shapiro's lemma only for `Rep.ind`, whose underlying module is a coinvariants quotient
of `k[G] ⊗ A`; the permutation form is the one every geometric application needs, and it was
missing.

The remaining input for step 2 is the exactness of the tree sequence.  Its easy half — connectivity,
i.e. that the image of the boundary map is all of the augmentation kernel — needs no normal forms at
all: `gC` and `g·of i x·C` are both adjacent to `g·A_i`, so `PushoutI.induction_on` over the
generators collapses every vertex to the root.  The hard half is acyclicity, and the standard proof
grades the tree by distance from the root and looks at an edge of maximal distance in a supposed
cycle.  That grading is the word length of the normal form, which is now built.
`DeningerPushoutLength.lean`:

- `deningerLen` — the number of letters of the normal form of an element, relative to a transversal
  of the base group;
- `deningerLen_rcons_of_mem`, `deningerLen_rcons_of_notMem` — prepending a letter lengthens the word
  by one exactly when the letter is not already in the base group;
- `deningerLen_base_mul`, `deningerLen_eq_zero_iff` — the length is unchanged by the base group on
  the left and vanishes exactly on it;
- `deningerLen_of_mul_le`, `deningerLen_le_of_mul` — multiplying by an element of one of the factors
  changes the length by at most one in either direction.  Both bounds come from the same
  computation: multiplication by a factor rewrites the normal form as `rcons` of the same tail with
  a different head, and only the head decides whether the word gains a letter;
- `deningerCosetLen`, `deningerCosetLen_eq_zero_iff`, `deningerCosetLen_mul_of` — the induced length
  on the cosets of the base group, with the base coset as its unique zero, and its one-step bound.
  The length is invariant under the base group on the *left*, so it descends to *left* cosets only
  after inverting representatives; that inversion is the same one already used in the permutation
  form of Shapiro's lemma, and the two must be taken with the same handedness or the tree and the
  coefficients will not match.

The complex itself is now built.  `DeningerBassSerreTree.lean`:

- `DeningerTreeVertex`, `DeningerTreeEdge` — the cosets of the base group together with the cosets
  of each factor, and the pairs (factor, coset of the base group); with the `PushoutI`-actions;
- `deningerEdgeHead` — the map on cosets induced by `C ≤ A_i`, which is what makes the edge
  `(i, gC)` run from `gC` to `gA_i`;
- `deningerTreeBoundary`, `deningerTreeAug`, and their equivariance; packaged as morphisms of
  representations `deningerTreeBoundaryHom`, `deningerTreeAugHom`;
- `deningerTreeAug_surjective`, `deningerTreeAug_comp_boundary` — it is a complex, exact at `k`;
- `deningerTree_connected` — **the kernel of the augmentation is the image of the boundary.**  The
  proof is the induction over the generators of the pushout announced above: the statement is made
  multiplicative by quantifying over a left translate, the base group moves nothing, and a letter
  `of i x` moves `gC` to `g·of i x·C`, whose difference is the difference of the two edges into the
  common vertex `gA_i`.  The passage from vertices to arbitrary chains is the splitting
  `f = (f - ε(f)·root) + ε(f)·root`.

The remaining half, acyclicity, is proved as follows.

**The rank of an edge.**  Put `ρ(i, x) = 2·cosetLen(x) + (0 if the normal form attached to `x`
starts in the factor `i`, else 1)`.  This is the distance from the base coset to the endpoint of the
edge `(i, x)` that is further away.  Suppose a chain `f` has `∂f = 0` and `f ≠ 0`, and let
`e₀ = (i₀, x₀)` maximize `ρ` on the support of `f`.  Two cases, and in each one `e₀` is the only edge
of the support meeting a chosen vertex, so the vanishing of that vertex's coefficient gives
`f(e₀) = 0`:

- if the normal form of `x₀` starts in the factor `i₀`, take the vertex `x₀` itself.  Its other
  edges are `(i, x₀)` with `i ≠ i₀`, and those have rank `2·cosetLen(x₀) + 1 > ρ(e₀)`.  This case is
  free — it is only the definition of `ρ`;
- otherwise take the vertex `x₀A_{i₀}`.  Its other edges are `(i₀, x')` with `x' ⊆ x₀A_{i₀}`,
  `x' ≠ x₀`, and those have `cosetLen(x') = cosetLen(x₀) + 1`, hence rank `> ρ(e₀)`.

The second bullet is the geometric content, and it is now proved.
`DeningerPushoutFirstLetter.lean`:

- `deningerEquivPair_of_fstIdx_ne` — if the normal form of a word does not begin in the factor `i`,
  its `i`-th pair decomposition has head coming entirely from the base group and tail the whole
  word;
- `deningerLen_of_mul_eq` — hence multiplying by a letter of `i` that is not in the base group
  lengthens the normal form by **exactly** one, sharpening the two-sided bound of
  `DeningerPushoutLength`;
- `deningerFirstIdx` — the index the normal form of a coset begins in, well defined because the base
  group changes only the head of a normal word;
- `deningerCosetLen_mul_of_eq` — the second bullet above: among the cosets of the base group inside a
  fixed coset of a factor, the one already reached is strictly closest, and every other is exactly
  one step further.

**Acyclicity is proved.**  `DeningerTreeAcyclic.lean`:

- `deningerEdgeRank` — the grading `ρ` above;
- `deningerVertexCoeff`, `deningerBoundaryChar`, `deningerVertexCoeff_boundary` — the coefficient of
  a vertex in a boundary, as a sum over the support against the incidence coefficient;
- `deningerTreeBoundary_injective` — **the boundary map is injective**, by the two-case leaf argument
  run against `Finsupp.sum_eq_single`.

So the tree sequence `0 → k[E] → k[V] → k → 0` is now exact at all three places, for any pushout of
groups whose structure maps are injective.  `DeningerTreeShortExact.lean` packages it as
`deningerTreeShortComplex` together with `deningerTreeShortComplex_shortExact`, a
`ShortComplex.ShortExact` in `Rep k G` — the exact input mathlib's long exact sequence in group
homology consumes.  Exactness in the middle is transported from modules by
`reflects_exact_of_faithful` along the forgetful functor; mono and epi are `Rep.mono_iff_injective`
and `Rep.epi_iff_surjective`.

**What is left to reach Mayer-Vietoris.**  The long exact sequence of this short exact sequence has
terms `H_n(G; k[E])` and `H_n(G; k[V])`, and these have to be identified with the homology of the
factors.  `k[E]` and `k[V]` are permutation representations on disjoint unions of coset spaces:

  `E = ι × (G ⧸ C)`,  `V = (G ⧸ C) ⊔ (Σ i, G ⧸ A_i)`,

so what is needed is that the permutation representation on a disjoint union is the direct sum of
the pieces, and that group homology takes it to the direct sum.  For a **finite** index set this is
a biproduct and follows from additivity of the homology functor, which is enough for the intended
application (the tower of root adjunctions uses two factors).  For an arbitrary index set it would
need homology to commute with coproducts, which mathlib does not package.

The disjoint union half is now built.  `DeningerPermutationSum.lean`:

- `deningerPermLift`, `deningerPermHom` — a map of a `G`-set into a permutation representation
  extends to a linear map, and an equivariant one extends to a morphism of representations.  Every
  map below is built through this, so all verifications reduce to a computation on basis elements;
- `deningerPermRepIsoOfEquiv` — an equivariant bijection induces an isomorphism of permutation
  representations, which is what converts `Σ (i : Bool), Y i` into `Y true ⊕ Y false`;
- `deningerSumInl`, `deningerSumInr`, `deningerSumFst`, `deningerSumSnd` with their four composite
  identities, and `deningerSumRepIso` — **the permutation representation on a disjoint union is the
  biproduct**, `k[X ⊕ Y] ≅ k[X] ⊞ k[Y]`.

The content of the last one is the total identity `fst ≫ inl + snd ≫ inr = 1`; the four component
identities are formal.

The homology half is built too.  `DeningerHomologyAdditive.lean`:

- `deningerChainsFunctor_additive` — the functor sending a representation to its complex of
  inhomogeneous chains is additive.  mathlib registers only `PreservesZeroMorphisms` for it;
- `deningerHomologyFunctor_additive` — hence group homology in each degree is additive;
- `deningerHomologyBiprodIso` — **`Hₙ(G, A ⊞ B) ≅ Hₙ(G, A) ⊞ Hₙ(G, B)`**, assembled from the images
  of the four structure maps, with the composite identities coming from the biproduct's total
  identity together with additivity.

mathlib's route from additivity to preservation of binary biproducts does not fire by instance
search on this functor, so the isomorphism is built by hand from `biprod.lift` and `biprod.desc`.

**The two terms of the long exact sequence are now identified.**  `DeningerTreeTwoFactor.lean` gives
the equivariant decompositions for an amalgam of two factors (indexed by `ULift Bool`, so that the
index type lies in the same universe as the groups, which the group-homology machinery requires):

- `deningerEdgeEquivSum` — the edges are two copies of the cosets of the base group;
- `deningerVertexEquivSum` — the vertices are the cosets of the base group together with the cosets
  of the two factors;
- `deningerTreeEdgeRepIso`, `deningerTreeVertexRepIso` — the induced isomorphisms of
  representations onto biproducts.

`DeningerTreeHomology.lean` then reads off, using additivity and the permutation form of Shapiro's
lemma:

- `deningerTreeEdgeHomologyIso` — `Hₙ(G, k[E]) ≅ Hₙ(C, k) ⊞ Hₙ(C, k)`;
- `deningerTreeVertexHomologyIso` — `Hₙ(G, k[V]) ≅ Hₙ(C, k) ⊞ (Hₙ(A₀, k) ⊞ Hₙ(A₁, k))`.

What remains for Mayer-Vietoris proper is the diagram chase: the long exact sequence of the tree
sequence now reads

  `Hₙ(C) ⊞ Hₙ(C) → Hₙ(C) ⊞ Hₙ(A₀) ⊞ Hₙ(A₁) → Hₙ(G) → Hₙ₋₁(C) ⊞ Hₙ₋₁(C) → …`

The extra `Hₙ(C)` on both sides is the price of mathlib's pushout being a star rather than a
bipartite graph — the tree of the two factor amalgam is the barycentric subdivision of the classical
one.

**But for the packet the diagram chase is not needed at all**, and this is the observation that
closes the route.  Identifying the maps of the long exact sequence would require naturality of
Shapiro's lemma in the subgroup, which is a substantial piece of work.  It is unnecessary: exactness
at `Hₙ(G)` alone says `Hₙ(G)` is squeezed between `Hₙ(k[V])` and `Hₙ₋₁(k[E])`, so

  `Hₙ(k[V]) = 0` and `Hₙ₋₁(k[E]) = 0`  ⟹  `Hₙ(G) = 0`,

with no knowledge of any map.  For a root adjunction `A *_{⟨g⟩ = ⟨tⁿ⟩} ⟨t⟩` the base group and the
second factor are infinite cyclic, so in degrees `n ≥ 3` both hypotheses hold as soon as
`Hₙ(A;ℚ) = 0`: the vertex term is `Hₙ(ℤ) ⊞ Hₙ(A) ⊞ Hₙ(ℤ)` and the edge term is `Hₙ₋₁(ℤ)²` with
`n - 1 ≥ 2`.  So the tower induction goes through in degrees `≥ 3` with no map identification, and
degree two is already known: `H²(R_U;ℚ) = 0` is proved above, and over a field cohomology is the
dual of homology, so `H₂` vanishes with it.

`DeningerTreeVanishing.lean`:

- `deningerIsZero_of_exact` — an exact short complex with zero ends has zero middle;
- `deningerIsZero_biprod` — a biproduct of zero objects is zero;
- `deningerGroupHomology_isZero_X₃` — the long exact sequence consequence above;
- `deningerAmalgam_isZero` — **for a two factor amalgam, the homology vanishes in degree `i` as soon
  as it vanishes for the base group and both factors in degree `i`, and for the base group in
  degree `i - 1`.**

To feed that theorem the tower needs the homology of the infinite cyclic group, which mathlib has
only in the finite cyclic case.  `DeningerCyclicHomology.lean` builds the ingredients:

- `deningerTrivialHomologyIso` — homology with trivial coefficients transfers along an isomorphism
  of groups, which is what moves statements between `H`, `G i` and their images in the pushout;
- `deningerIsZero_regular`, `deningerIsZero_leftRegular` — **the regular representation has no
  homology in positive degrees**: it is the permutation representation on the cosets of the trivial
  subgroup, so the permutation form of Shapiro's lemma computes its homology as that of the trivial
  group;
- `deningerZGen`, `deningerZVal`, `deningerZBoundary`, `deningerZAug` — the standard length one
  resolution `k[Z] → k[Z] → k` of an infinite cyclic group, given as an abstract group with an
  isomorphism to `ℤ` rather than as `ℤ` itself, so that it can live in the same universe as the
  other groups; with `deningerZAug_comp_boundary` and `deningerZAug_surjective`.

Its exactness is now proved:

- `deningerZBoundary_injective` — multiplication by `t - 1` is injective, by taking the element of
  maximal exponent in the support: the coefficient of `t` times it in the image is exactly the
  coefficient there, because the next exponent up is outside the support;
- `deningerZ_exact` — the kernel of the augmentation is the image of `t - 1`.  The basis differences
  `tⁿ - 1` are boundaries by a telescoping induction over `ℤ`, and arbitrary chains reduce to those
  by the same splitting `f = (f - ε(f)·1) + ε(f)·1` used for the tree;
- `deningerZShortComplex_shortExact`, and hence **`deningerZ_isZero` : `Hₙ(Z;k) = 0` for `n ≥ 2`**,
  by the same long exact sequence lemma, both neighbouring terms being homology of the regular
  representation.

**The tower step itself is now proved.**  `DeningerAmalgamCyclic.lean`:

- `deningerAmalgam_isZero_of_infiniteCyclic` — for a two factor amalgam whose base group and second
  factor are infinite cyclic, vanishing of homology in degrees at least three passes from the first
  factor to the amalgam;
- `deningerRootFactor`, `deningerRootMap`, `deningerRootMap_injective` — the pushout data of a root
  adjunction: the two factors are the group and an infinite cyclic group, the generator of the base
  goes to `a` on one side and to the `m`-th power of the generator on the other, and both maps are
  injective exactly when `m ≠ 0` and `a` has infinite order;
- `deningerRootAdjunction_isZero` — **if `Hₙ₊₃(A;k) = 0` then `Hₙ₊₃` of `A` with an `m`-th root of
  `a` adjoined vanishes too.**

This is the inductive step of the tower.

**The limit stages are handled too.**  The tower can be taken to be an increasing chain indexed by
`ℕ`, not a transfinite one: `Bau(F)` is generated by `F` under the root operations, so it is the
union of the subgroups obtained by closing `F` under roots finitely many times.  For an increasing
union no colimit machinery is needed at all — an inhomogeneous chain has finite support, so it
involves finitely many group elements and therefore lives in one member of the chain.
`DeningerHomologyUnion.lean`:

- `deningerSubChains`, `deningerSubChains_f`, `deningerSubChains_injective` — the pushforward of
  chains along a subgroup inclusion is `mapDomain` along an injection, hence injective;
- `deningerIsZero_of_iUnion` — **if the homology of each member of an increasing chain of subgroups
  whose union is the whole group vanishes in a degree, so does the homology of the group.**  A cycle
  is pulled back to the member containing its support, is a cycle there by injectivity of the
  pushforward, bounds there, and the bounding chain is pushed forward.

What is left for clause (4) is Baumslag's theorem, which is what identifies each step of that chain
as a root adjunction in the sense above rather than merely a quotient of one.  Note that the card's
own proof does not prove this: it cites Casacuberta–Peschke for free groups.  Formalizing clause (4)
therefore means proving that theorem, which is what the whole Bass–Serre layer above is for.

The normal-form layer Baumslag's theorem needs is being built alongside.
`DeningerPushoutConcat.lean`:

- `deningerFstIdx_of_mul` — prepending a letter outside the base group, in a factor not already at
  the front, puts that factor at the front of the normal form;
- `deningerLetterProd`, `deningerLen_prepend` — **the length of a product of alternating letters**:
  prepending a reduced alternating word of `ℓ` letters to an element whose normal form does not
  begin in the last factor used adds exactly `ℓ`, and the first letter ends up at the front.  The
  two statements have to be proved simultaneously, since the induction step needs the first-letter
  claim for the tail to know the next letter does not merge.

This is the growth statement that makes powers of a cyclically reduced element have growing length.
`DeningerPushoutPower.lean` draws that conclusion:

- `deningerAbsorb` and its laws — absorbing an element of the base group into the first letter of a
  word changes neither the indices, nor the length, nor reducedness, nor alternation;
- `deningerBase_mul_letterProd` — so multiplying a nonempty word by the base group on the left is
  again a word with the same indices;
- `deningerLen_pow` — **if the reduced alternating word of `g` begins and ends in different factors,
  then `len(gⁿ) = n · len(g)`.**  The words of the powers are literally the concatenations: the
  induction carries the word together with its first and last indices, and the junction condition
  for the concatenation is exactly the hypothesis that the first and last factors differ.

This is the engine of both torsion-freeness and uniqueness of roots in an amalgam.

`DeningerPushoutDecomp.lean` supplies the input those statements need — that every element actually
has such a word:

- `deningerTransversal_notMem_range` — a transversal element other than the identity is not in the
  base group, since it would then admit two factorizations through the complement;
- `deningerOfCoprodI_prod` — the product of the letters of a normal word, read in the pushout, is
  the product of the corresponding list;
- `deningerExists_letterProd` — **every element is either in the image of the base group, or is the
  product of a nonempty reduced alternating list of letters whose length is its word length.**  The
  element of the base group sitting in front of the normal form is absorbed into the first letter,
  which is why the decomposition has no leftover factor.

`DeningerPushoutInv.lean` closes the loop between the two descriptions of the length, and opens the
right-handed direction:

- `deningerLen_letterProd` — the word length of a product of a reduced alternating list is the
  number of letters, which is the prepending lemma applied to the identity;
- `deningerInvList`, `deningerLetterProd_inv` and their laws — the word of an inverse is the
  reversed list of inverted letters, which is again reduced and alternating;
- `deningerLen_inv` — **inversion preserves the word length.**

The last one matters out of proportion to its difficulty: all the normal-form machinery is
left-handed, because mathlib's normal words carry a left action.  Conjugating to shorten a word
needs multiplication on the *right*, and `deningerLen_inv` is what converts one into the other.

`DeningerPushoutMerge.lean` gives the sharp bound conjugation needs:

- `deningerEquivPair_head_notMem` — if the normal form begins in the factor `i` then the head of its
  `i`-th pair decomposition is a genuine letter, not an element of the base group;
- `deningerLen_of_mul_le_of_fstIdx` — hence multiplying by a letter of a factor the word already
  begins in does **not** lengthen it;
- `deningerLen_mul_of_le` — the same on the right, via invariance of the length under inversion.

`DeningerCyclicReduction.lean` then gives:

- `DeningerCycRed` — the property of having a nonempty reduced alternating word beginning and ending
  in different factors;
- `deningerFstIdx_letterProd` — the normal form of a reduced alternating product begins in the
  factor of its first letter;
- `deningerExists_cycRed` — **every element is conjugate to one which either has word length at most
  one, or is cyclically reduced.**  Induction on a bound for the length: if the first and last
  letters share a factor, conjugating by the first letter strips it on the left and merges it on the
  right, so the length drops.

**First payoff of the layer.**  `DeningerPushoutTorsion.lean` proves
`deningerPushout_torsionFree`: **an amalgamated free product of torsion free groups, over a torsion
free base, with injective structure maps, is torsion free.**  Every element is conjugate to one
lying in a factor or to a cyclically reduced one; the second has powers of growing length so cannot
be trivial, and the first inherits the property from the factor.  mathlib does not have this.

Note that mathlib's `IsMulTorsionFree` is stronger than the absence of torsion: it is injectivity of
`x ↦ xⁿ`, i.e. **uniqueness of roots**, which is exactly the R-group property Baumslag's theorem is
about.  So the remaining step is stated in mathlib's own vocabulary as
`IsMulTorsionFree (PushoutI φ)`.

Reaching it needs the *letters*, not just the length, and the reduced alternating decomposition is
not unique: base group elements can be shifted between adjacent letters.  It becomes unique once the
letters are required to lie in the chosen transversal, and that is what
`DeningerPushoutNormal.lean` proves:

- `deningerEquiv_fst_eq_one` — a transversal element factors through the complement with trivial
  base part;
- `deningerNormalWord_letterProd` — **if every letter lies in the transversal, the normal form of
  the product is the word itself, with trivial head**;
- `deningerLetterProd_injective` — hence transversal words are determined by their products.

This is what makes the powers comparable: for a cyclically reduced transversal word the word of `gⁿ`
is literally the `n`-fold concatenation, again a transversal word, so `xⁿ = yⁿ` forces the
concatenations, and therefore the words, to agree.

That is now carried out.  `DeningerPushoutRoot.lean`:

- `deningerFlatten` and its laws — the concatenation of `n` copies of a word, its length, its
  members, its first letter, and `deningerLetterProd_flatten`, that its product is the `n`-th power;
- `deningerFlatten_isChain` — the concatenation is alternating, the junction between consecutive
  copies being exactly the cyclic reducedness hypothesis;
- `deningerPow_injective_cycRed` — **equal powers of cyclically reduced transversal elements have
  equal words**, hence are equal.  Equal concatenations have equal lengths, so the two words have
  equal lengths, and a prefix of a common list of the same length is determined.

What is left for Baumslag's theorem is the elements conjugate into a factor, and the passage from
cyclically reduced representatives back to arbitrary elements.  The second of these needs to compare
an element with a conjugate of it, and the tool for that is the word metric.
`DeningerPushoutMetric.lean`:

- `deningerLen_letterProd_mul_le` — prepending a word of `ℓ` letters raises the length by at most
  `ℓ`, with no reducedness hypothesis at all;
- `deningerLen_mul_le`, `deningerLen_le_mul` — hence the word length is **subadditive**, and
  satisfies the reverse triangle inequality;
- `deningerLen_conj_ge`, `deningerLen_conj_le` — **conjugation changes the word length by at most
  twice the length of the conjugator.**

The subadditive statements need no hypotheses on the word beyond its existence, which is why they
come out of the decomposition directly.

`DeningerPushoutOrder.lean` then records what the growth gives:

- `deningerPow_ne_one_cycRed` — a positive power of a nonempty cyclically reduced word is
  nontrivial;
- `deningerZpow_injective_cycRed` — **all its integer powers are distinct**;
- `deningerZpow_injective_conj` — the same for any conjugate of such an element.

**The endgame does not need the centralizer theorem.**  mathlib's own proof that free groups are
`IsMulTorsionFree` uses a different and entirely elementary device: from `xⁿ = yⁿ` one also has
`x^{2n} = y^{2n}`, and comparing the reduced words of the two powers pins down both the cyclic
reductions and the conjugators.  The same device works here, and its first half is now proved.

`DeningerCycLenEq.lean`:

- `deningerConj_zpow` — conjugation commutes with powers;
- `deningerLen_pow_conj_bounds` — the word length of `xᵐ` differs from `m` times the length of the
  cyclic reduction by at most twice the length of the conjugator;
- `deningerCycLen_eq` — **equal `n`-th powers force cyclic reductions of the same length.**  Since
  `xⁿ = yⁿ` gives `x^{kn} = y^{kn}` for every `k`, a difference in the two lengths would be
  amplified without bound, while the conjugators only ever contribute a fixed amount.

The word comparison itself has an obstruction that the free group case does not: transversal words
are the ones determined by their products, but the inverse of a transversal letter need not be a
transversal letter, so the word of `C · Lᵏ · C⁻¹` is not automatically transversal.  What repairs it
is that the base group elements can always be pushed to the left.  `DeningerTransversalForm.lean`:

- `deningerIsChain_of_map_fst` — alternation depends only on the sequence of indices;
- `deningerExists_transversal_form` — **every reduced alternating word is an element of the base
  group times a reduced alternating word with the same indices whose letters lie in the
  transversal.**  One letter at a time: the base group element accumulated so far is absorbed into
  the next letter, which is then split through the complement, sending a new base group element
  further left.

`DeningerWordMerge.lean` supplies the atomic steps of cyclic reduction at the level of words:

- `deningerLetterProd_snoc`, `deningerMerge_last`, `deningerMerge_first` — multiplying a word by a
  letter of the factor of its last (or first) letter multiplies that letter, leaving the rest alone;
- `deningerMerge_last_mem`, `deningerMerge_first_mem` — if the merged letter falls into the base
  group the word shortens instead;
- `deningerCycStep` — **one step of cyclic reduction on words**: if the first and last letters lie
  in the same factor, conjugating by the first letter deletes it and multiplies it into the last,
  strictly shortening the word.

These are group-theoretically trivial but they are the statements the word-level recursion needs;
the earlier cyclic reduction was proved with lengths only and does not expose the conjugator.

`DeningerConjWord.lean` assembles the target of that recursion:

- `deningerFlatten_getLast` — the last letter of a concatenation of copies is the last letter of the
  word;
- `deningerNormalWord_conj_pow` — **if the junctions do not cancel, the normal word of `C · Lᵏ · D`
  is the plain concatenation `C ++ Lᵏ ++ D`.**

This is the statement the two-exponent comparison consumes: taking it at `k = n` and `k = 2n` and
using that normal words are unique turns `xⁿ = yⁿ` into an equality of explicit lists, whose length
bookkeeping is the argument already proved in `DeningerCycLenEq`.  What is still missing is the
production of `C`, `L` and `D` with those junction properties from an arbitrary element.

Half of that production is now available.  A conjugator is only determined up to multiplication by
the base group on the right, and that freedom is exactly what is needed:
`DeningerConjNormalize.lean` proves

- `deningerExists_inv_transversal` — **every element can be multiplied by an element of the base
  group on the right so that its inverse becomes a transversal word**;
- `deningerConj_transversal_form` — hence any conjugate can be written with a transversal
  conjugator, the absorbed base group element reappearing as a conjugation of the conjugated element
  by the base group, which changes neither its word length nor its indices.

Without this the right hand conjugator `D` would be the inverse of a transversal word, and inverses
of transversal letters need not be transversal.  `DeningerBaseLength.lean` records that the
adjustment is free:

- `deningerLen_mul_base`, `deningerLen_base_conj` — multiplication by the base group on either side,
  and conjugation by it, leave the word length unchanged;
- `deningerLen_base_conj_pow`, `deningerLen_conj_of_len_zero` — hence so do all the powers, and a
  conjugator of word length zero changes nothing.

**A correction to the plan recorded above.**  For amalgams the word of `g^k` is *not* literally
`C ++ Lᵏ ++ D` with `D` the inverse word of `C`.  Cyclic reduction here conjugates by the first
letter, which deletes it and multiplies it into the last letter; the two ends are not inverse to
each other as they are in a free group, and the right hand junction genuinely cancels.  The word of
`g^k` is instead `C` followed by `k-1` copies of the cyclically reduced word and then the original
tail.  The right way to write it is

  `(c v c⁻¹)^{k+1} = c · vᵏ · (v c⁻¹)`,

which confines all the cancellation to the last factor: the left conjugator survives intact, the
middle is a power of the cyclically reduced part, and `v c⁻¹` is a single element whose word begins
like `v` does.  The junction conditions this needs are exactly `last(C) ≠ first(V)` and the cyclic
reducedness of `V` — no condition relating the two ends of the conjugator, which is what failed.
And the pair `(C, V)` still determines the element, since `w = letterProd C · letterProd V ·
(letterProd C)⁻¹`, so recovering `C` and `V` from the word of a power recovers the element.

`DeningerConjSplit.lean`:

- `deningerConj_pow_split` — the splitting identity;
- `deningerNormalWord_append` — the normal word of a product of two transversal words meeting
  without cancellation, which is the degenerate case of the concatenation statement needed when the
  middle power is empty.

`DeningerPowWord.lean` puts the two together:

- `deningerNormalWord_pow` — **if `x = c v c⁻¹` with `v` cyclically reduced, the left junction not
  cancelling, and `B` the word of `v c⁻¹`, then the normal word of `x^{k+1}` is `C` followed by `k`
  copies of `V` followed by `B`.**

This is the statement the two-exponent comparison is applied to.  Taking it at two different
exponents and using uniqueness of normal words turns `xⁿ = yⁿ` into an equality of explicit lists
for every multiple of `n`; the tail `B` has no reason to have the same length as `C`, so unlike the
free group case the conjugators are not immediately equal, and what comes out first is that the two
cyclically reduced words are cyclic rotations of one another.  Since a rotation is conjugation by
the corresponding prefix, that still forces the two elements to agree.  `DeningerRotate.lean` proves
that last step:

- `deningerLetterProd_take_drop` — a word is its prefix times its suffix;
- `deningerLetterProd_rotate`, `deningerLetterProd_rotate_conj` — **rotating a word by `t`
  conjugates its product by the prefix of length `t`.**

`DeningerFlattenRotate.lean` supplies the combinatorial identity that produces the rotation in the
first place:

- `deningerDrop_append` — `drop r V ++ V = rotate r V ++ drop r V`;
- `deningerDrop_flatten` — **dropping `r` letters from a concatenation of copies of `V` gives the
  concatenation of copies of `rotate r V`, followed by `drop r V`.**

So when the two conjugators have different lengths, shifting one word against the other by the
difference turns the copies of one cyclically reduced word into copies of a rotation of it, and the
rotation is read off directly.

`DeningerFlattenDrop.lean` refines that into the form the comparison uses, splitting the shift into
its whole and partial parts:

- `deningerFlatten_inj` — a concatenation of copies determines the word, given its length;
- `deningerDrop_mul_flatten` — dropping a multiple of the length removes whole copies;
- `deningerDrop_flatten_succ` — dropping a further partial amount rotates the word.

So a shift by `t = qℓ + r` removes `q` copies and rotates by `r`, and the rotation that appears is
`r`, the remainder of the difference of the conjugator lengths modulo the length of the cyclically
reduced word.

`DeningerRotateCompare.lean` carries out the comparison itself:

- `deningerFlatten_add` — concatenations of copies add;
- `deningerRotate_of_flatten_eq` — **if the same list is described twice, as a conjugator followed
  by copies of a cyclically reduced word followed by a tail, then the two cyclically reduced words
  are rotations of one another by the difference of the conjugator lengths modulo their common
  length.**

The hypothesis is that the number of copies exceeds the number consumed by the shift, which is
guaranteed by taking the exponent large — and taking the exponent large is available for free, since
`xⁿ = yⁿ` gives `x^{kn} = y^{kn}` for every `k`.

The remaining group-theoretic work is the production of the two descriptions, and it needs to know
which letters survive a product.  `DeningerLeadLetter.lean` proves the first such statement:

- `deningerFstIdx_mul_of_len` — **if a reduced alternating word is multiplied on the right by an
  element and the word length is the sum of the two lengths, then the normal form of the product
  begins in the factor of the first letter.**

The induction is on the word: the length hypothesis is inherited by the tail because the length can
drop by at most one when a letter is removed, and the alternation then keeps the next letter from
merging.

`DeningerCancelCriterion.lean` characterizes when that hypothesis holds:

- `deningerLen_mul_lt_of_fstIdx` — if the element begins in the factor of the last letter, the
  product is strictly shorter than the sum of the lengths;
- `deningerLen_mul_eq_iff` — **the word length of a product is the sum of the lengths exactly when
  the element's normal form does not begin in the factor of the last letter.**

So cancellation in an amalgam is detected by a single index comparison, and the leading letter
lemma applies whenever that comparison fails.

The recursion that produces the cyclic reduction data has to know that peeling a letter makes
progress, and the obstacle is that a merge need not shorten the word.
`DeningerMergeDichotomy.lean` resolves it:

- `deningerMerge_dichotomy` — **if the normal form of an element begins in the factor `i`, then
  multiplying by a letter of `i` either leaves the front in the factor `i`, or strictly shortens
  the word.**

Either branch is progress: in the first the next junction cannot cancel, because the surrounding
word alternates, so the prepending lemma applies and the recursion stops; in the second the length
has dropped, so the recursion continues.

`DeningerLeadSurvives.lean` runs that recursion:

- `deningerFstIdx_letterProd_mul` — **if a reduced alternating word is multiplied on the right by an
  element strictly shorter than the word, the normal form of the product still begins in the factor
  of the first letter.**

This is one route to the junction condition the shape `C · Vᵏ · B` needs on its right hand side, but
it needs the conjugator to be shorter than the cyclically reduced part, which is **not** always the
case: each cyclic reduction step that drops a letter into the base group shortens the word by two
while lengthening the conjugator by one, so a word of length six can reduce to one of length two
with a conjugator of length two.

The correct route uses the structure of the conjugator rather than its size.  The conjugator is
built by stripping letters off the *front* of the word, so it is literally a prefix of it, and the
merged letter at each step carries the index of the letter that was stripped.  So the last letter of
the cyclically reduced part has the index of the last letter of the conjugator, and the junction
follows from the alternation of the original word.  `DeningerPrefixConj.lean`:

- `deningerLetterProd_prefix_cancel` — cancelling a prefix off a word leaves the suffix;
- `deningerJunction_of_append` — **if the last letter of the cyclically reduced part carries the
  index of the last letter of the conjugator, then it differs from the first letter of the tail.**

The recursion should also be run on plain reduced alternating words rather than transversal ones:
transversality is needed only at the very end, for uniqueness of normal words, and it can be
restored there by the transversal form, which preserves the indices.  Working with plain words the
base group elements produced along the way are always absorbed into a neighbouring letter — on the
left by `deningerAbsorb`, and on the right by `DeningerAbsorbRight.lean`:

- `deningerLetterProd_mul_base_snoc` — an element of the base group multiplying a nonempty word on
  the right is absorbed into its last letter;
- `deningerAbsorbRight_reduced`, `deningerAbsorbRight_map_fst` — reducedness and the indices are
  preserved.

This is what keeps the cyclic reduction step inside the class of reduced alternating words when the
merged letter falls into the base group and the word shortens by two.

`DeningerCycStepCases.lean` states the step in both cases:

- `deningerCycStep_notMem` — the merged letter survives and the word shortens by one;
- `deningerCycStep_mem` — **the merged letter falls into the base group, the word shortens by two,
  and the base group element is absorbed into the new last letter.**

The junction condition of the power word follows in either case from the same fact: the tail `B` is
the suffix of the word after the conjugator, and both it and the cyclically reduced part `V` are
obtained from that suffix by operations at its *end*, so they begin in the same factor.  The
junction `last(V) ≠ first(B)` is then cyclic reducedness of `V`.

`DeningerCycData.lean` makes the tail's identification exact rather than approximate:

- `deningerCycData_iff` — **writing the element as `C · V · C⁻¹` is *equivalent* to identifying the
  tail of its word with `V · C⁻¹`.**  So the tail is not merely close to the suffix of the word after
  the conjugator, it *is* that suffix;
- `deningerCycData_base`, `deningerCycData_step` — the data of an already cyclically reduced word,
  and its inheritance under a conjugation step, where prepending a letter to the conjugator
  corresponds to multiplying the tail by the inverse of that letter.

This removes the need for the separate tail `B` altogether: the word of the element splits as
`C ++ R`, the power word is `C ++ Vᵏ ++ R`, and both junctions are consequences of the alternation
of `C ++ R` together with cyclic reducedness of `V`.

That leaves exactly one invariant for the recursion to carry: the cyclically reduced part and the
tail begin in the same factor.  `DeningerSuffixIndex.lean` is what propagates it:

- `deningerHead_map_fst_of_append` — **two words with a common prefix that differ only in their last
  letter have suffixes beginning in the same factor**, provided the differing letters lie in the same
  factor.

A reduction step changes only the tail of the word, so this is exactly the shape of each step, in
both of its cases.

`DeningerPrefixTransfer.lean` is the matching surgery on the conjugator side:

- `deningerPrefix_le` — a prefix leaving a nonempty suffix does not reach the last letter;
- `deningerPrefix_transfer` — **hence the conjugator produced for the reduced word is also a prefix
  of the original word**, and
- `deningerSuffix_length` — the two suffixes have the same length.

Together with the suffix index lemma this is everything the reassembly step of the recursion needs
in the first case.  The second case replaces the last letter by *two* letters rather than one, so
both statements are generalized in `DeningerPrefixTransferGen.lean` to an arbitrary changed tail:

- `deningerPrefix_take`, `deningerPrefix_transfer'` — a prefix stopping inside the common part
  transfers between the two words;
- `deningerHead_map_fst_of_append'` — **the suffixes begin in the same factor as soon as the changed
  tails do.**

With the tail allowed to be arbitrary, one statement covers both cases of a reduction step.

`DeningerCycReassemble.lean` performs the reassembly itself:

- `deningerCycData_reassemble` — **given the data of the word obtained by one reduction step, the
  data of the original word is obtained by prepending the stripped letter to the conjugator and
  taking the corresponding suffix as the tail.**

All four conclusions come out at once: the splitting, the nonemptiness of the tail, the shared first
factor, and the product identity, the last by cancelling the conjugator from both descriptions of
the element.  The statement takes the replacement tail as a parameter, so the same reassembly serves
both reduction cases.

The two ends of the recursion are also in place:

- `deningerCycData_of_cycRed` — a word that is already cyclically reduced, or is a single letter, is
  its own cyclically reduced part, with empty conjugator and itself as tail;
- `deningerNotCycRed_decomp` — **a reduced alternating word of length at least two whose first and
  last letters lie in the same factor is a first letter, a nonempty middle, and a last letter in
  that factor.**  The middle is nonempty because a two letter word alternates, so its first and last
  letters are in different factors.

`DeningerCycRecursion.lean` runs the recursion:

- `deningerExists_cycData` — **every nonempty reduced alternating word splits as a conjugator
  followed by a tail, together with a cyclically reduced part or a single letter, the tail and the
  cyclically reduced part beginning in the same factor, and the tail equal to the cyclically reduced
  part times the inverse conjugator.**

This is the production of the cyclic reduction data that the two-exponent comparison consumes.  With
it, the shape `C · Vᵏ · R` is available for an arbitrary element, its junction conditions coming
from the alternation of `C ++ R` and the cyclic reducedness of `V`.

**The remaining obstruction.**  The comparison reads off the normal word of a power, and normal words
have their letters in the transversal, whereas the words produced by the recursion do not: the
conjugator inherits the head of the element in its first letter, and each reduction step creates a
merged letter at the end.  Putting a word into transversal form pushes base group elements leftwards
through it, which changes every letter, so the transversal form of `C ++ Vᵏ ++ R` is not the
concatenation of transversal forms.  What survives the normalization is the sequence of indices:

- `deningerNormalWord_base_mul` — the base group on the left does not change the word;
- `deningerNormalWord_map_fst` — **the normal form of a product of a reduced alternating word has
  the same indices as the word**, transversal or not.

So the comparison currently yields the index sequences of the two words, which gives the rotation but
not yet the equality of the letters.  Closing that gap is what remains.

There is however one shape for which the normalization is harmless.  If every letter but the first
lies in the transversal, the base group element released by that first letter becomes the head and
never reaches the others, so the word is unchanged from the second letter on:

- `deningerNormalWord_head_only` — **the normal form of a reduced alternating word whose letters are
  transversal except at the front** is that word with its first letter replaced by its transversal
  representative, and the released base element as head.

This is the shape the comparison needs, and it is the shape the conjugator and the tail already have,
being a prefix and a suffix of the word of the element.  The cyclically reduced part is what fails
it, because each reduction step creates its merged letter at the end.

**Lengths need no transversality at all.**  What the normalization changes is the letters; the number
of them is fixed, so the length of a power can be read off the decomposition directly:

- `deningerLen_conj_pow` — for an element presented as `C · V · C⁻¹` with `V` cyclically reduced of
  at least two letters, **the `(k+1)`-st power has length `|C| + k·|V| + |R|`**;
- `deningerLen_conj_pow_sub` — **each further power adds `|V|`**.

The powers therefore grow linearly, at a rate that is exactly the length of the cyclically reduced
part.  Comparing `xⁿ = yⁿ` at the two exponents `n` and `2n` cancels the constant term and returns
`|V_x| = |V_y|`, and then the constant term returns `|C_x| = |C_y|`: the two decompositions have the
same shape, and the rotation relating them is trivial.  This is the two-exponent trick carried out on
the one invariant that survives normalization, and it is now proved:

- `deningerLen_eq_of_pow_eq` — **two elements with the same `n`-th power have cyclically reduced
  parts of the same length, and are themselves of the same length.**

Comparing at a single exponent leaves the constant term of the linear growth undetermined; comparing
at `n` and `2n` cancels it.  So the two decompositions align position by position, with no rotation.

What remains is the passage from the shape to the letters.  The natural route is the conjugacy
criterion for cyclically reduced elements — two conjugate cyclically reduced elements of at least two
letters are cyclic permutations of one another — whose proof is an induction on the length of the
conjugating element, shortening it by moving a letter across whenever the conjugate fails to be
longer.  The length bounds this needs are the ones already proved for conjugates, and the case
analysis is the merge dichotomy.  Its first ingredient is proved:

- `deningerRotate_cycRed` — **rotations of a cyclically reduced word are cyclically reduced.**  The
  junction the rotation creates is an adjacent pair of the original word, and the junction it
  destroys is the one the cyclic condition controls;
- `deningerRotate_one_conj` — conjugating by the first letter rotates by one.

Conjugating a cyclically reduced word by a single letter shortens it only when that letter is, up to
the base group, the first or the last letter of the word, and the result is then the rotation.  So an
element conjugating one cyclically reduced word to another of the same length can be shortened one
letter at a time, each step rotating the word — which is the induction the criterion runs.  The two
sides of that dichotomy are proved:

- `deningerLen_conj_letter_ne` — **conjugating by a letter whose factor occurs neither at the front
  nor at the back lengthens by two**, there being no cancellation at either end;
- `deningerConj_head_merge` — **if the letter is from the front factor and the front letter cancels
  it into the base group, the conjugate is the rotation by one**, conjugated by the base group
  element the cancellation produced.

- `deningerLen_conj_head_ne` — **if the letter is from the front factor but the front letter does not
  cancel it into the base group, the length grows by one**: the front merges but survives, and
  nothing cancels at the back.

The back of the word behaves as the mirror image:

- `deningerConj_last_merge` — **if the letter is from the back factor and the last letter cancels it
  into the base group, the conjugate is the rotation that moves the last letter to the front**, again
  conjugated by the base group element the cancellation produced;
- `deningerLen_conj_last_ne` — incomplete cancellation at the back also lengthens by one.

So a conjugation that does not lengthen must use a letter from an extreme factor, and a conjugation
that shortens by the full two must cancel completely — which is the rotation, forwards at the front
and backwards at the back.  Conjugation by the
base group alone changes no length, which the corpus already owned (`deningerLen_base_conj`), so the
base element the rotation carries never disturbs the induction.

Step 1 still needs Baumslag's inductive step (root adjunction preserves unique roots), which rests
on the same normal-form machinery.

Supporting facts that are proved, in `DeningerBaumslagGeneration.lean`:

- `DeningerBau.eq_top_of_rootClosed` — a subgroup containing the image of `G` and closed under the
  roots is everything, so the rationalization is generated by `G` as a group with roots;
- `DeningerBau.torsionFree` — the rationalization is torsion free;
- `deningerPow_injective_of_injective`, `deningerPow_injective_of_uniquelyDivisible` — equal powers
  are equal in a group with unique roots, and that transfers along any embedding.  These are the
  shape in which "has unique roots" is used downstream.

**Functoriality and equivariance.**  `GaloisForLFunctions/RHTower/DeningerBaumslagFunctorial.lean`.

- `deningerBauMap`, `deningerBauMap_id`, `deningerBauMap_comp` — the rationalization is a functor:
  a homomorphism extends over the rationalizations, uniquely, because the target has unique roots.
- `deningerBauMapEquiv` — isomorphic groups have isomorphic rationalizations.
- `deningerBauFreeMap_comp` — **the packet is equivariant on the target**: pushing the chosen family
  through an additive endomorphism of `A` composes `a_U` with that endomorphism.  Both sides are
  lifts of the same map on the free group, so uniqueness identifies them.
- `deningerBauFreeMap_linear`, `deningerBauFreeMap_smul` — the two cases the hostile audit named:
  `GL(U)`-equivariance and power-map equivariance.

**Equivariance under a group acting on the chosen family.**
`GaloisForLFunctions/RHTower/DeningerBaumslagEquivariance.lean`.  The packet depends on a family
`b : ι → A`; whenever a group `Γ` acts on `ι` and on `A` and `b` is equivariant, the packet is
equivariant.

- `deningerBauFreeAut` — the action induced on `Bau(F_m)` by the action on the index set, through
  functoriality of `FreeGroup` and of the rationalization; `deningerBauFreeAut_one` and
  `deningerBauFreeAut_mul` say it is an action.
- `deningerBauFreeMap_equivariant` — **`a_U` intertwines that action with the action on `A`.**

Applied to a Galois group acting on `A` and permuting the chosen family, this is the coherent
Galois functoriality the hostile audit asked for; it is stated for a general `Γ` because the card
fixes no Galois action of its own.

### Verification

- Direct command:
  `lake env lean GaloisForLFunctions/RHTower/DeningerUniquelyDivisibleKernel.lean`
  — passes with no errors and no warnings.
- Cached module build:
  `lake build GaloisForLFunctions.RHTower.DeningerUniquelyDivisibleKernel` completes.
- Scratch `#print axioms` on all four declarations: no axioms, `propext`, or the standard
  `propext, Classical.choice, Quot.sound`.
- Imported by the `GaloisForLFunctions.RHTower` umbrella.

## Gates

- [x] 0 → 1 in-progress: packet statement isolated
- [x] 1 → 2 fully-proven: complete paper proof
- [x] 2 → 3 formalized, clauses 1 and 2
  (`GaloisForLFunctions.RHTower.DeningerUniquelyDivisibleKernel`)
- [x] 2 → 3 formalized, the construction `Bau(F_m)`, its universal property, and the surjection
  `(1)` (`GaloisForLFunctions.RHTower.DeningerBaumslagRationalization`)
- [x] 2 → 3 formalized, clause 3 with trivial rational coefficients
  (`GaloisForLFunctions.RHTower.DeningerBaumslagDegreeOne`)
- [x] 2 → 3 formalized, clause 4 in degrees one and two
  (`GaloisForLFunctions.RHTower.DeningerBaumslagDegreeOne`,
  `GaloisForLFunctions.RHTower.DeningerBaumslagRationalProjective`)
- [x] 2 → 3 formalized, clause 5's finite-cover consequence
  (`GaloisForLFunctions.RHTower.DeningerBaumslagPullback`)
- [ ] 2 → 3 formalized, clause 4 above degree two: statable in `groupCohomology`, proof missing
- [ ] 2 → 3 formalized, the homotopy-fibre half of clause 5: blocked on classifying spaces
- [x] `GL(U)` and power-map equivariance of the packet, and functoriality of the rationalization
  (`GaloisForLFunctions.RHTower.DeningerBaumslagFunctorial`)
- [x] equivariance of the packet under any group acting on the index set and on `A`
  (`GaloisForLFunctions.RHTower.DeningerBaumslagEquivariance`)
- [ ] 3 → 4 publication-ready: instantiate the equivariance at an actual Galois action

## Hostile audit

- The packet depends on a basis.  `GL(U)` and power-map equivariance are proved
  (`deningerBauFreeMap_linear`, `deningerBauFreeMap_smul`), and so is equivariance under an
  arbitrary group acting on the index set and on \(A\)
  (`deningerBauFreeMap_equivariant`), which is Galois functoriality once a Galois action is fixed —
  the card fixes none.
- Equation `(3)` is rational only; Baumslag rationalization does not
  construct torsion-free integral Milnor cohomology.
- Pulling `(2)` back over \(X_F\) preserves finite covers, but its cohomology
  is not computed by a naïve tensor product without a twisted
  Eilenberg--Moore theorem.
- Baumslag rationalization and Malcev/\(\mathbb Q\)-completion are
  different.  Replacing the former by the latter reintroduces nonzero
  \(H_2\).

**Verdict:** `FULLY PROVEN ON PAPER`.

## References

- Gilbert Baumslag, *Some aspects of groups with unique roots*.
- Carles Casacuberta and Georg Peschke, *Localizing with respect to
  self-maps of the circle*.
- Sergei O. Ivanov, *An overview of rationalization theories of
  non-simply connected spaces and non-nilpotent groups*, Equation (5.3):
  https://arxiv.org/abs/2111.10694

## Log

- 2026-08-01 — Formalized clauses 1 and 2 unconditionally, reusing the already formalized
  divisible-fiber theorem for clause 2.  Clauses 3--5 are recorded as blocked on objects that do
  not exist yet, not on missing proofs.

## Lean status

Clauses 1 and 2 were already formalized in `DeningerUniquelyDivisibleKernel.lean`.  The remaining
clauses split as follows.

- **Clause 3.**  `DeningerDegreeOneInflation.lean` reduces it to a vanishing: restriction along a
  surjection is injective (`deningerHomRestrict_injective`), its image is exactly the homomorphisms
  killing the kernel (`deningerHomRestrict_mem_range_iff`), so the comparison is an isomorphism
  exactly when every homomorphism kills the kernel (`deningerHomRestrict_bijective_iff`).  That
  vanishing is now **proved**, in `DeningerBaumslagDegreeOne.lean`, straight from the universal
  property of the rationalization — no rational homology input.  Clause 3 is closed.
- **Clause 4.**  The square-zero product of `(3)` — degree two vanishes, so products of degree-one
  classes vanish — is `deningerGradedDegreeOne_mul_eq_zero` in `DeningerMilnorAmplitude.lean`, and
  the formality assertion is `DeningerTwoTermFormality.lean`, both already in the tree.
- **Clause 5.**  Classifying spaces, homotopy fibres and homotopy pullbacks have no mathlib
  counterpart, so this clause has no formal statement here.

The card therefore stays at stage 2 for two residual reasons only: `H^n(BR_U;ℚ) = 0` for `n ≥ 3`,
which still quotes Casacuberta--Peschke, and the identification of the homotopy fibre of `Ba_U`,
which needs classifying spaces.  Everything else — the surjection `(1)`, clauses 1, 2, 3, clause 4 in
degrees one and two, and clause 5's finite-cover consequence — is proved unconditionally.

- 2026-08-03 — Built Baumslag rationalization, which this card named as a missing construction, and
  with it the surjection `(1)`.  The point that makes it a finite construction rather than
  Baumslag's transfinite root-adjunction is that "unique roots" is *not* an extra axiom: in the
  signature with a unary `root n` for each `n`, the two equations `(root n x)^{n+1} = x` and
  `root n (x^{n+1}) = x` already force uniqueness, so groups with unique roots are a variety and the
  left adjoint is a term algebra modulo a congruence.  Uniqueness in the universal property is then
  free, because a homomorphism between two such groups preserves roots automatically.  Clauses 1 and
  2, previously proved in the abstract generality in which the card argues them, are now instantiated
  at the actual `K_U = ker(a_U)`.  What is deliberately not claimed is injectivity of the unit
  `G → Bau(G)` — Baumslag's embedding theorem — which the card does not use.
- 2026-08-03 — Closed clause 3, and removed the Casacuberta--Peschke dependency from it.  The card's
  proof deduces the degree-one isomorphism from the rational homology computation, but in degree one
  with trivial coefficients no computation is needed: homomorphisms into a rational vector space see
  only the free generators.  Explicitly, the target has unique roots, so the universal property
  turns homomorphisms out of `Bau(F_m)` into homomorphisms out of `F_m`, i.e. into functions on the
  basis; the basis turns those into homomorphisms out of `A`; and the composite of the two bijections
  is restriction along `a_U`.  The rational homology input is now needed only for the part of clause
  4 above degree one.
- 2026-08-03 — Proved clause 4 in degrees one and two, again without the Casacuberta--Peschke
  import.  Degree one is clause 3 plus finite-dimensional double duality.  Degree two is the
  splitting of central extensions, and the mechanism is that `Bau(F)` is *projective* for surjections
  from groups with unique roots: a central extension of a group with unique roots by a subgroup with
  unique roots again has unique roots, so the extension is such a surjection, and a section is built
  by lifting the free generators and extending by the universal property.  The rational-homology
  input now enters only for `H^{≥3}`.
- 2026-08-03 — Proved clause 5's consequence at the actual object.  The homotopy pullback is not
  statable, but the fibre product of `a_U` along an arbitrary `H → A` is, and it has exactly the
  property the clause uses: it surjects onto `H` with kernel `K_U`, so the divisible-fibre theorem
  already in the tree applies unchanged and gives both the equivalence of finite covering categories
  and the isomorphism of profinite completions.  The only parts of the card still unformalized are
  `H^{≥3}(BR_U;ℚ) = 0` and the identification of the homotopy fibre itself.
- 2026-08-03 — Made the rationalization a functor and proved the packet's `GL(U)` and power-map
  equivariance, two of the three items the hostile audit listed as missing.  Both follow from the
  universal property with no extra input: functoriality because the extension of a homomorphism is
  unique, and equivariance because the two composites are lifts of the same map on the free group.
  Galois functoriality remains open only because the card fixes no Galois action on `A`.
- 2026-08-03 — Turned the degree-two statement from "the content of `H² = 0`" into `H² = 0` itself.
  mathlib has `groupCohomology.H2` and its cocycle API but no bridge to central extensions, so the
  bridge is built: a normalized `2`-cocycle with values in a trivial rational module twists `M × G`
  into a central extension whose kernel is uniquely divisible, and a section of that extension is
  precisely a cochain trivializing the cocycle.  Normalization costs nothing because the constant
  `f(1,1)` is itself a coboundary.  So the card's clause 4 in degree two is now literal.
- 2026-08-03 — Made the degree-one statement literal as well, so both cohomological halves of the
  card now speak mathlib's `groupCohomology`.  With a trivial action `d₀₁` is identically zero, so
  the coboundaries vanish and the projection from cocycles to `H¹` is injective as well as
  epi; and the cocycle condition for a trivial action is precisely multiplicativity, so cocycles are
  homomorphisms.  Composing with clause 3 gives `H¹(BR_U;ℚ) ≅ U` on the nose.
- 2026-08-03 — Closed the last functoriality item.  The obstruction to "Galois functoriality" was
  never a missing proof but a missing hypothesis: the card fixes no Galois action.  Stated for an
  arbitrary group acting on the index set and on `A`, with an equivariant chosen family, the packet
  *is* equivariant — the induced action on `Bau(F_m)` comes from functoriality of `FreeGroup` and of
  the rationalization, and both sides of the comparison are lifts of the same map on the free group.
  Instantiating at a Galois action is now a hypothesis to supply, not a theorem to prove.
- 2026-08-03 — Proved `H²(F_m; A) = 0` for arbitrary coefficients, which is the degree-two half of
  the free-group homology the card's proof quotes, and corrected a stale gap description.  The
  remaining half of clause 4 is *statable* — mathlib has `groupCohomology` in every degree, so
  "needs rational homology of classifying spaces" was wrong about the objects; only the proof is
  missing.  Recorded why the splitting argument stops at degree two: dimension shifting turns
  `H³(G;ℚ)` into `H²(G;Fun(G,ℚ)/ℚ)`, whose twisted extension is divisible but not uniquely so, and
  the universal property of the rationalization needs uniqueness.
- 2026-08-03 — Completed the free-group input in degrees zero and one, again for arbitrary
  coefficients.  The degree-one computation is the useful one: a `1`-cocycle is precisely a section
  of the semidirect product, so over a free group it is an arbitrary function on the generators, and
  the bijection `Z¹(F_ι;A) ≃ (ι → A)` holds for every representation.  With trivial coefficients the
  coboundaries vanish and this is `H¹`.  Degrees zero, one and two of the free-group half of the
  card's quoted homology input are therefore all proved; only the `R_U` half above degree two
  remains.
- 2026-08-03 — Completed the free-group half of the card's homology input in *all* degrees:
  `Hⁿ(F_ι; A) = 0` for every `n ≥ 2` and every representation.  Degree two is the extension
  splitting proved earlier; the rest is dimension shifting, which mathlib now supports — Shapiro's
  lemma makes coinduction from the trivial subgroup cohomologically trivial in positive degrees, the
  adjunction unit is a split mono after restriction and restriction is faithful, so unit and
  cokernel form a short exact sequence whose connecting map is an isomorphism above degree one.  The
  universes of the coinduction API have to be pinned by hand or the constraint solver stalls.
- 2026-08-03 — Proved the Casacuberta--Peschke comparison `H^*(R_U;ℚ) ≅ H^*(F_m;ℚ)` in degrees zero,
  one and two, so the import is now needed only from degree three on.  The mechanism is that the
  universal property is a *bijection* of hom-sets — `Hom(Bau G, H) ≃ Hom(G, H)` whenever `H` has
  unique roots — and with trivial coefficients first cohomology is exactly a hom-set, so `H¹` cannot
  tell `R_U` from `F_m`.  Degree zero is the coefficient module on both sides and degree two vanishes
  on both.
- 2026-08-03 — Started Baumslag's tower, the only route to the remaining degrees.  One root
  adjunction is now built as an amalgamated free product, with faithfulness and the root property;
  mathlib supplies `PushoutI` and the injectivity of the factors, which is the Bass--Serre input.
  Recorded the structural point that no normal-form theorem is needed to *identify* the colimit with
  `Bau(G)` — a uniquely divisible colimit with the universal property is the rationalization by
  uniqueness of adjoints — so the remaining mathematical content is exactly that roots stay unique
  along the tower.
- 2026-08-03 — Closed off the naive tower, correcting the previous entry.  Adjoining a root to an
  element that already has one creates a second root: in the free group on two generators with a
  square root `t` of `a²` adjoined, `t ≠ a` because an explicit homomorphism onto `ℤ/2` separates
  them, yet both square to `a²`.  So the stages of the naive tower are not groups with unique roots
  and do not embed in `Bau(G)`; the previous log entry's framing of them as "stages of Baumslag's
  tower" was wrong and is retracted here.  The construction has to adjoin roots only where missing,
  or quotient at each stage.
- 2026-08-03 — Measured what is actually left and recorded it, rather than continuing to produce
  fragments.  The tower needs a base case — free groups have unique roots — and every standard proof
  of that (cyclic centralizers via a free group with nontrivial centre being cyclic; bi-orderability;
  the Magnus embedding) is a development mathlib does not have, on top of the Bass--Serre argument
  that root adjunction preserves unique roots.  Proved the supporting facts that are within reach:
  the rationalization is generated by `G` as a group with roots, it is torsion free, and unique roots
  transfer along embeddings.  Clause 4 above degree two is a research programme, not a pending lemma.
- 2026-08-03 — Corrected the previous entry: the base case is in mathlib.  `IsMulTorsionFree
  (FreeGroup α)` is exactly "free groups have unique roots", proved in mathlib by cyclic reduction, so
  the three routes I listed as missing were unnecessary.  Used the occasion to build the structure the
  tower needs: in any group with unique roots the roots of a fixed element refine each other, hence
  `(root_d h)^n` depends only on `n/(d+1)` and every element carries an action of `ℚ`.  What remains
  for clause 4 is the inductive step — root adjunction preserves unique roots — which is Baumslag's
  theorem and needs amalgam normal forms, which mathlib also has.
- 2026-08-03 — Computed the rationalization in rank one: `Bau(ℤ) ≅ ℚ`.  `Multiplicative ℚ` has the
  same universal property as the rationalization of `ℤ` — a homomorphism out of it into a group with
  unique roots is determined by the image of the generator, since the value at `1/d` is forced to be
  that image's `d`-th root — so the two are isomorphic, both composites being pinned by uniqueness.
  Besides being the `dim U = 1` case of the packet, this is a check that the term-algebra construction
  produces the classically expected object and nothing larger.
- 2026-08-03 — Proved that centralizers in a group with unique roots are closed under the roots, and
  deduced that `Bau(G)` is abelian whenever `G` is.  The mechanism is one line of algebra:
  conjugation by an element commuting with `y^(n+1)` sends `y` to another `(n+1)`-st root of the same
  element, and uniqueness of roots forces it to fix `y`.  Combined with the generation lemma — the
  centralizer of any element is root closed and contains the image of `G`, hence is everything —
  this gives the abelian case, of which `Bau(ℤ) ≅ ℚ` is now visibly a special case.
- 2026-08-03 — Built the rational vector space structure on an abelian group with unique roots.
  In the abelian case the root operations are homomorphisms, commute with integer powers, and
  compose (`m`-th root of `n`-th root = `mn`-th root); the rational power operation then satisfies
  the module axioms, with scalar associativity the only nontrivial one.  Homomorphisms preserve
  roots, so they are automatically `ℚ`-linear, making the abelian rationalization a functor to
  `ℚ`-vector spaces with `deningerBauRatLift` as its universal property.  mathlib has uniqueness of
  `ℚ`-module structures but no existence statement of this kind; combined with that uniqueness, the
  structure built here is canonical.
- 2026-08-03 — Settled the route for clause (4) in all degrees and built its first missing input.
  The argument cannot be run in cohomology, because cohomology does not commute with the filtered
  colimit defining the rationalization; it has to run in homology and be dualized at the end.  What
  it needs is Mayer–Vietoris for amalgamated free products, i.e. the Bass–Serre tree sequence
  `0 → k[E] → k[V] → k → 0` plus an identification of `H_*(G; k[G ⧸ S])` with `H_*(S; k)`.  The
  latter is now proved: mathlib's Shapiro lemma is stated for `Rep.ind`, whose underlying module is
  a coinvariants quotient of `k[G] ⊗ A`, so the permutation-representation form had to be built.
  The comparison map sends `⟦h ⊗ c⟧` to the coset of `h⁻¹`, the inversion converting mathlib's
  right-handed convention into left cosets.
- 2026-08-03 — Built the length function on an amalgamated free product, the grading the tree
  sequence's acyclicity argument runs on.  Both directions of the one-step bound come from a single
  observation: multiplication by an element of a factor rewrites the normal form as `rcons` of the
  *same* tail with a different head, and only the head decides whether a letter is gained, so the
  length can move by at most one.  The length is invariant under the base group on the left, so it
  descends to left cosets only after inverting representatives — the same inversion the permutation
  form of Shapiro's lemma uses, and the two have to agree in handedness.  Also recorded that the
  connectivity half of the tree sequence needs no normal forms: `gC` and `g·of i x·C` are both
  adjacent to `g·A_i`, so induction over the generators of the pushout collapses every vertex to the
  root.
- 2026-08-03 — Built the tree of cosets of a pushout of groups, its augmented complex, the
  equivariance of both maps, and the connectivity half of exactness.  Connectivity needed no normal
  forms, as expected: quantifying over a left translate makes the statement multiplicative, so
  `PushoutI.induction_on` reduces it to two cases — the base group moves no coset, and a letter
  `of i x` moves `gC` to `g·of i x·C`, whose difference is the difference of the two edges into the
  common vertex `gA_i`.  Arbitrary chains reduce to vertices by the splitting
  `f = (f - ε(f)·root) + ε(f)·root`.  What is left of the tree sequence is acyclicity, which is what
  the length function was built for.
- 2026-08-03 — Fixed the acyclicity argument for the tree sequence and proved its geometric input.
  The right rank on edges is `2·cosetLen(x) + (0 if the normal form of x starts in the factor i,
  else 1)` — the distance to the far endpoint.  Maximizing it isolates a leaf in two cases, one of
  which is free from the definition of the rank and the other of which needs a *sharp* length law:
  multiplying by a letter of a factor that is not already at the front, and not in the base group,
  lengthens the normal form by exactly one.  That is now proved, via the observation that when the
  first letter is not in the factor `i`, the `i`-th pair decomposition of the normal word has head
  entirely in the base group and tail the whole word.  The consequence for cosets — among the cosets
  of the base group inside a coset of a factor, exactly one is closest and all others are one step
  further — is what makes the far vertex a leaf.
- 2026-08-03 — Proved acyclicity, completing the Bass-Serre tree sequence: for any pushout of groups
  with injective structure maps, `0 → k[E] → k[V] → k → 0` is exact at all three places.  The leaf
  argument went through as planned, with two implementation notes worth keeping: the vertex type has
  a dependent constructor, so the summand branch needs the index destructured *before* the maximal
  edge is chosen, or the heterogeneous equality coming out of `injEq` cannot be substituted away;
  and the coefficient extraction is cleanest as a single `Finsupp.sum` against an incidence
  coefficient, reduced by `Finsupp.sum_eq_single` at the maximal edge.  Next is assembling
  Mayer-Vietoris: package the sequence as a short exact sequence of representations, feed it to
  mathlib's long exact sequence in group homology, and identify the terms with the permutation form
  of Shapiro's lemma.
- 2026-08-03 — Packaged the tree sequence as a short exact sequence of representations, the form
  mathlib's long exact sequence in group homology consumes.  What is left before Mayer-Vietoris is
  the identification of the two permutation representations with direct sums over the pieces of
  their index sets; for a finite index set that is a biproduct and follows from additivity of the
  homology functor, which suffices for the two-factor amalgams the tower of root adjunctions uses.
  For arbitrary index sets it would need homology to commute with coproducts, which mathlib does not
  package — so the Mayer-Vietoris statement will be stated for finitely many factors.
- 2026-08-03 — Proved that the permutation representation on a disjoint union is the biproduct, and
  that equivariant bijections induce isomorphisms of permutation representations.  Everything is
  built through a single lift construction — a map of a `G`-set into a permutation representation
  extends to a morphism — so each verification is a computation on basis elements.  The content of
  the biproduct statement is the total identity `fst ≫ inl + snd ≫ inr = 1`; the four component
  identities are formal.  With two factors, the tree's edge and vertex sets are `Bool`-indexed, so
  the binary statement plus the transport along equivariant bijections covers both.
- 2026-08-03 — Proved group homology additive and deduced that it takes biproducts to biproducts.
  mathlib registers only `PreservesZeroMorphisms` for the chains functor, so additivity had to be
  proved from the description of the chain map on basis elements; the instance chain from
  `Additive` to `PreservesBinaryBiproduct` then failed to fire anyway, so the biproduct isomorphism
  is assembled by hand from `biprod.lift`/`biprod.desc`, its two composite identities coming from
  `biprod.total` plus additivity.  One tactic note: the `@[simps]`-generated `functor_map` lemma
  unfolds the functor's action and defeats `← Functor.map_comp`; suppressing it with
  `simp [-groupHomology.functor_map]` is what makes the composite identities go through.
- 2026-08-03 — Identified both homology terms of the tree sequence for a two factor amalgam.  The
  index type has to be `ULift Bool` rather than `Bool`: the tree's edge and vertex types are built
  over an index type in the same universe as the groups, which is what the group-homology machinery
  needs, and `Bool` sits in universe zero.  With the decompositions in place, additivity plus the
  permutation form of Shapiro's lemma give `Hₙ(G, k[E]) ≅ Hₙ(C) ⊞ Hₙ(C)` and
  `Hₙ(G, k[V]) ≅ Hₙ(C) ⊞ (Hₙ(A₀) ⊞ Hₙ(A₁))`.  The redundant `Hₙ(C)` on both sides is because
  mathlib's pushout is a star, i.e. the barycentric subdivision of the classical bipartite tree; for
  the intended application it cancels directly, since `C → A₁` being a homology isomorphism makes
  the first map of the long exact sequence injective.
- 2026-08-03 — Found that the Mayer-Vietoris diagram chase is not needed, and proved the vanishing
  statement that replaces it.  Identifying the maps in the long exact sequence would require
  naturality of Shapiro's lemma in the subgroup — a substantial piece of work — but exactness at
  `Hₙ(G)` by itself already gives `Hₙ(k[V]) = 0` and `Hₙ₋₁(k[E]) = 0` ⟹ `Hₙ(G) = 0`.  For a root
  adjunction both the base group and the adjoined factor are infinite cyclic, so in degrees `n ≥ 3`
  both hypotheses reduce to `Hₙ(A;ℚ) = 0`, which is exactly the induction hypothesis of the tower.
  Degree two needs no separate argument: `H²(R_U;ℚ) = 0` is already proved, and over a field
  cohomology is the dual of homology.  This removes the last piece of open plumbing between the tree
  sequence and the tower induction.
- 2026-08-03 — Built the transfer of homology along group isomorphisms, the vanishing of the
  homology of the regular representation, and the maps of the length one resolution of an infinite
  cyclic group.  The regular representation costs nothing now: it is the permutation representation
  on the cosets of the trivial subgroup, so the permutation Shapiro lemma reduces it to the trivial
  group.  The resolution is stated for an abstract group with an isomorphism to `ℤ` rather than for
  `Multiplicative ℤ` itself — the latter sits in universe zero, and the representation-theoretic
  machinery needs the group in the same universe as the coefficients.  What is left is its two
  exactness statements, after which the same long exact sequence lemma gives `Hₙ(Z;k) = 0` for
  `n ≥ 2`, both neighbouring terms being homology of the regular representation.
- 2026-08-03 — Proved the exactness of the length one resolution of an infinite cyclic group, hence
  `Hₙ(Z;k) = 0` for `n ≥ 2`.  Injectivity of `t - 1` is the maximal-exponent argument: the
  coefficient at one step above the top of the support is exactly the top coefficient.  Exactness in
  the middle is a telescoping induction over `ℤ` for the basis differences `tⁿ - 1`, plus the same
  splitting `f = (f - ε(f)·1) + ε(f)·1` the tree connectivity used.  With this, every homological
  input of the tower step exists: the base group and adjoined factor of a root adjunction are
  infinite cyclic, so `deningerAmalgam_isZero` propagates vanishing in degrees `≥ 3` from a group to
  the amalgam.  What remains for clause (4) is the tower itself — presenting a root adjunction as a
  `PushoutI` over `ULift Bool`, the transfinite induction, and filtered colimits of group homology.
- 2026-08-03 — Proved the inductive step of the tower: if the homology of `A` vanishes in a degree
  at least three, then so does the homology of `A` with a root adjoined.  The statement is given
  twice, once for an abstract two factor amalgam whose base group and second factor are infinite
  cyclic, and once for the explicit root adjunction data, where the injectivity of the two structure
  maps is exactly `m ≠ 0` and `a` of infinite order.  Nothing about the maps of the long exact
  sequence is used anywhere in the chain.
- 2026-08-03 — Handled the limit stages of the tower, and found they need no colimit machinery.  The
  tower can be indexed by `ℕ`: `Bau(F)` is generated by `F` under the root operations, so it is the
  increasing union of the subgroups obtained by closing `F` under roots finitely many times.  For an
  increasing union the argument is elementary — an inhomogeneous chain has finite support, so it
  involves only finitely many group elements and lives in one member of the chain; pull the cycle
  back there, bound it there, push the bounding chain forward.  Injectivity of the pushforward, which
  is `mapDomain` along an injection, is what makes the pulled back chain a cycle.  The only thing
  still missing for clause (4) is Baumslag's theorem: it is what makes each step of the chain a root
  adjunction in the amalgam sense, rather than merely a quotient of one.
- 2026-08-03 — Recorded that the card's own proof of clause (4) cites Casacuberta–Peschke rather
  than proving it, so the formalization has to prove that theorem outright; the Bass–Serre layer is
  that proof, and Baumslag's unique-roots theorem is its last missing input.  Built the growth
  statement its normal-form layer needs: prepending a reduced alternating word of `ℓ` letters to an
  element whose normal form does not begin in the last factor used adds exactly `ℓ` to the length,
  and puts the first letter at the front.  The length and first-letter claims must be proved
  simultaneously — the induction step needs the first-letter claim for the tail in order to know the
  next letter does not merge into it.
- 2026-08-03 — Proved that the length of a power of a cyclically reduced element grows linearly:
  `len(gⁿ) = n · len(g)` whenever the reduced alternating word of `g` begins and ends in different
  factors.  Once the prepending lemmas of the previous step are in place this is pure list
  bookkeeping — the word of `gⁿ` is the concatenation of `n` copies, the element of the base group
  sitting at the end of each copy being absorbed into the first letter of the next, which changes
  neither indices nor length nor reducedness.  The induction has to carry the first and last index
  of the accumulated word, since the junction condition for each concatenation is exactly that they
  differ.
- 2026-08-03 — Built the bridge from mathlib's normal form to the list statements: every element of
  a pushout is either in the base group or the product of a nonempty reduced alternating list of
  letters, of length its word length.  Two things make it come out clean.  A transversal element
  other than the identity is automatically outside the base group — otherwise it would have two
  factorizations through the complement — which is what gives reducedness.  And the element of the
  base group that sits in front of the normal form is absorbed into the first letter by the machinery
  from the previous step, so the decomposition has no leftover factor and matches the shape the
  power lemma wants.
- 2026-08-03 — Proved that the word length of a reduced alternating product is its number of
  letters, and that inversion preserves the word length.  The second is the useful one, out of
  proportion to its difficulty: every lemma in this layer is left-handed, because mathlib's normal
  words carry a left action, whereas cyclic reduction conjugates and so needs multiplication on the
  right.  Inversion converts one into the other, so no right-handed normal-form theory has to be
  built.  The word of an inverse is the reversed list of inverted letters, which is reduced and
  alternating because the alternation relation is symmetric.
- 2026-08-03 — Proved cyclic reduction: every element is conjugate to one of word length at most one
  or to a cyclically reduced one.  The step needs a sharp merging bound, not the two-sided estimate
  built earlier: conjugating by the first letter strips it on the left, and the length only drops
  because multiplying on the right by a letter of the factor the word already ends in cannot
  lengthen it.  That sharp bound is where the head of the pair decomposition has to be shown to be a
  genuine letter — if it were in the base group the normal form would not begin in that factor at
  all.  Together with the power lemma this gives the growth statement for arbitrary elements:
  conjugate to a cyclically reduced form, whose powers have linearly growing length.
- 2026-08-03 — Proved that an amalgamated free product of torsion free groups over a torsion free
  base is torsion free — the first theorem the normal-form layer actually yields, and one mathlib
  does not have.  Cyclic reduction plus linear growth of the length of powers does it in two cases.
  Also noted that mathlib's `IsMulTorsionFree` is not the absence of torsion but injectivity of the
  `n`-th power map, i.e. uniqueness of roots — so Baumslag's theorem is stated in mathlib's own
  vocabulary as `IsMulTorsionFree (PushoutI φ)`, and the theorem proved here is the weaker statement
  that the trivial element has a unique root.
- 2026-08-03 — Proved that a reduced alternating word whose letters lie in the chosen transversal is
  literally the normal form of its product, with trivial head, so such words are determined by their
  products.  This is the missing uniqueness: the reduced alternating decomposition of an element is
  *not* unique in general, since base group elements can be shifted between adjacent letters, and
  the length alone cannot separate `x` from `y`.  Requiring the letters to lie in the transversal
  removes the ambiguity, and the concatenation describing a power of a cyclically reduced element
  stays inside that class — its base group factor is trivial, so nothing is absorbed.
- 2026-08-03 — Proved that equal powers of cyclically reduced transversal elements have equal words.
  With uniqueness of transversal words in hand this is list algebra: the word of a power is the
  `n`-fold concatenation, whose alternation at each junction is exactly the cyclic reducedness
  hypothesis; equal concatenations have equal lengths, so the two words have equal lengths, and a
  prefix of a common list of a given length is determined.  This is the cyclically reduced half of
  Baumslag's theorem.  What remains is the elements conjugate into a factor, and the passage from
  cyclically reduced representatives back to arbitrary elements.
- 2026-08-03 — Proved that the word length of a pushout is subadditive, and that conjugation moves
  it by at most twice the length of the conjugator.  Unlike everything else in this layer these need
  no reducedness or alternation hypotheses: prepending a word of `ℓ` letters raises the length by at
  most `ℓ` whatever the letters are, so the decomposition alone gives subadditivity, and inversion
  invariance turns it into the reverse triangle inequality.  This is the tool for the remaining
  passage from cyclically reduced representatives back to arbitrary elements, where an element has
  to be compared with a conjugate of itself.
- 2026-08-03 — Recorded the consequences of linear length growth: a nonempty cyclically reduced word
  has nontrivial positive powers and all its integer powers distinct, and the same holds for any
  conjugate.  The conjugated form is the shape the endgame needs.  The remaining structure of the
  argument is now visible: for `xⁿ = yⁿ` with the common power nontrivial, both `x` and `y`
  centralize it, so once the centralizer of an element not conjugate into a factor is known to be
  infinite cyclic, the equation reads `tᵃⁿ = tᵇⁿ` and distinctness of powers finishes it.  The
  centralizer theorem is the next target.
- 2026-08-03 — Found that the endgame needs no centralizer theorem, which removes what looked like
  the hardest remaining obstruction.  mathlib's own proof that free groups are `IsMulTorsionFree`
  uses an elementary device instead: from `xⁿ = yⁿ` one also has `x^{2n} = y^{2n}`, and comparing
  the reduced words of two different powers pins down the cyclic reductions and the conjugators
  together.  The first half is now proved here: equal `n`-th powers force cyclic reductions of the
  same length, because `xⁿ = yⁿ` gives `x^{kn} = y^{kn}` for every `k`, so a difference in lengths
  would be amplified without bound while the conjugators contribute a fixed amount.  What remains is
  the word comparison itself, for which the cyclic reduction has to be strengthened to produce the
  conjugator as a word that does not cancel against the cyclically reduced part.
- 2026-08-03 — Cleared an obstruction the free group case does not have.  Transversal words are the
  ones determined by their products, but the inverse of a transversal letter need not be a
  transversal letter, so the word of a conjugate `C·Lᵏ·C⁻¹` is not automatically transversal and the
  comparison of powers cannot be made directly.  The repair is that base group elements can always
  be pushed to the left: every reduced alternating word is an element of the base group times a
  transversal one with the same indices, obtained one letter at a time by absorbing the accumulated
  base element into the next letter and splitting it through the complement.  Since only the indices
  matter for alternation and for the junction conditions, the normalization costs nothing.
- 2026-08-03 — Built the atomic steps of cyclic reduction at the level of words: merging a letter
  into the first or last letter of a word, the degenerate case where the merged letter falls into
  the base group and the word shortens, and the resulting one-step cyclic reduction.  These are
  group-theoretically trivial, but the earlier cyclic reduction theorem was proved with lengths only
  and does not expose the conjugator, whereas the two-exponent comparison needs the conjugator as a
  word.  With the transversal form from the previous step these are the two ingredients the
  word-level recursion runs on.
- 2026-08-03 — Assembled the target of the word-level recursion: if the junctions do not cancel, the
  normal word of `C·Lᵏ·D` is the plain concatenation.  This is exactly what the two-exponent
  comparison consumes — taken at `k = n` and `k = 2n`, with uniqueness of normal words, it turns
  `xⁿ = yⁿ` into an equality of explicit lists whose length bookkeeping is the argument already
  proved.  What is still missing is the production of `C`, `L`, `D` with those junction properties
  from an arbitrary element, which is the recursion the merge lemmas were built for.
- 2026-08-03 — Used the freedom in the choice of conjugator to fix the transversality mismatch.  A
  conjugator is determined only up to multiplication by the base group on the right, and that
  freedom is exactly enough to make its inverse a transversal word — which is what the concatenation
  statement needs, since inverses of transversal letters need not be transversal.  The absorbed base
  group element reappears as a conjugation of the cyclically reduced part by the base group, which
  changes neither its word length nor its indices, so nothing else in the argument is disturbed.
- 2026-08-03 — Proved that the base group leaves the word length unchanged on either side and under
  conjugation, so the conjugator adjustment of the previous step costs nothing.  Also corrected the
  plan: for amalgams the word of `g^k` is not literally `C ++ Lᵏ ++ C⁻¹`.  Cyclic reduction here
  conjugates by the first letter, deleting it and multiplying it into the last letter, so the two
  ends of the conjugated element are not inverse to one another the way they are in a free group,
  and the right hand junction genuinely cancels — the word is `C`, then `k-1` copies of the
  cyclically reduced word, then the original tail.  Establishing that shape needs the cancellation
  theory for products in an amalgam, which is the next thing to build.
- 2026-08-03 — Found the right shape for a conjugated power in an amalgam:
  `(c v c⁻¹)^{k+1} = c · vᵏ · (v c⁻¹)`.  This confines all the cancellation to the last factor, and
  the junction conditions it needs are just `last(C) ≠ first(V)` together with cyclic reducedness of
  `V` — no condition relating the two ends of the conjugator, which is the one that failed for
  amalgams.  The pair `(C, V)` still determines the element, so recovering them from the word of a
  power recovers the element, which is what the two-exponent comparison requires.
- 2026-08-03 — Proved the normal word of a power in terms of the cyclic reduction data: `C`, then
  `k` copies of `V`, then the tail `B`.  This is what the two-exponent comparison is applied to.
  One difference from the free group case is now clear: there the tail is the reverse of the
  conjugator, so equal lengths force the conjugators to be equal outright, whereas here `B` has no
  reason to have the same length as `C`.  What comes out of the comparison first is instead that the
  two cyclically reduced words are cyclic rotations of one another — and since a rotation is
  conjugation by the corresponding prefix, that still forces the elements to agree.
- 2026-08-03 — Proved that rotation is conjugation: rotating a word by `t` conjugates its product by
  the prefix of length `t`.  This is the step that makes the amalgam comparison conclusive despite
  the asymmetry noted above — the comparison of powers yields only that the two cyclically reduced
  words are rotations of one another, and this turns that into a statement about the elements
  themselves.
- 2026-08-03 — Proved the combinatorial identity that produces the rotation: dropping `r` letters
  from a concatenation of copies of `V` gives a concatenation of copies of `rotate r V` followed by
  `drop r V`.  Together with the previous step this closes the conceptual gap the amalgam case has
  over the free group case — when the two conjugators differ in length, shifting one word against
  the other by the difference converts copies of one cyclically reduced word into copies of a
  rotation of it, and rotation is conjugation.
- 2026-08-03 — Split the shift into whole and partial copies: dropping a multiple of the length
  removes whole copies, dropping a further partial amount rotates the word, and a concatenation of
  copies determines the word given its length.  So a shift by `t = qℓ + r` removes `q` copies and
  rotates by `r` — the rotation that appears in the comparison is the remainder of the difference of
  the conjugator lengths modulo the length of the cyclically reduced word.  All the list ingredients
  of the comparison are now in place.
- 2026-08-03 — Proved the comparison itself at the level of lists: two descriptions of the same list
  as conjugator, copies of a cyclically reduced word, and tail force the two cyclically reduced
  words to be rotations of one another by the difference of the conjugator lengths modulo their
  common length.  The hypothesis needed is that the number of copies exceeds the number consumed by
  the shift, and that is free — `xⁿ = yⁿ` gives `x^{kn} = y^{kn}` for every `k`, so the exponent can
  always be taken past any fixed bound.  This is the whole combinatorial content of the two-exponent
  argument; what is left is the group-theoretic production of the two descriptions.
- 2026-08-03 — Proved that the leading letter of a product survives when nothing cancels: if a
  reduced alternating word is multiplied on the right and the length is additive, the normal form of
  the product begins in the factor of the first letter.  The induction works because the length
  hypothesis is inherited by the tail — removing a letter changes the length by at most one, so the
  additivity is forced all the way down — and alternation then prevents the next letter from
  merging.  This is the first statement of the cancellation theory that the production of the
  cyclic reduction data needs.
- 2026-08-03 — Characterized cancellation by a single index comparison: the word length of a product
  of a reduced alternating word with an element is the sum of the lengths exactly when the element's
  normal form does not begin in the factor of the last letter.  One direction is the prepending
  lemma, the other splits off the last letter and uses that merging cannot lengthen.  This makes the
  hypothesis of the leading letter lemma checkable, which is what the production of the cyclic
  reduction data needs.
- 2026-08-03 — Proved the merge dichotomy: multiplying an element whose normal form begins in the
  factor `i` by a letter of `i` either leaves the front in `i` or strictly shortens the word.  This
  is what makes the recursion that produces the cyclic reduction data terminate.  The difficulty it
  removes is that a merge need not shorten anything — the merged letter can survive as an ordinary
  letter — so length alone is not a termination measure.  Either branch is progress though: if the
  front stays in `i` the next junction cannot cancel, since the surrounding word alternates, and the
  prepending lemma finishes; otherwise the length has dropped.
- 2026-08-03 — Proved that the leading letter survives multiplication by a strictly shorter factor,
  running the recursion the merge dichotomy was built for.  This supplies the right hand junction
  condition of the shape `C · Vᵏ · B`: the tail `B` is the word of `v c⁻¹`, and when the conjugator
  is shorter than the cyclically reduced part it begins in the same factor as `V`, so
  `last(V) ≠ first(B)` reduces to cyclic reducedness of `V`.  Both junction conditions of the power
  word are now available from properties of the cyclic reduction rather than assumed.
- 2026-08-03 — Corrected the route to the right hand junction condition.  The previous step obtained
  it from the conjugator being shorter than the cyclically reduced part, but that is not always
  true: a cyclic reduction step whose merged letter falls into the base group shortens the word by
  two while lengthening the conjugator by one, so the conjugator can be as long as the reduced part.
  The structural route works instead — the conjugator is built by stripping letters off the front,
  so it is a prefix of the word, and the merged letter at each step carries the index of the letter
  stripped.  Hence the last letter of the cyclically reduced part has the index of the last letter
  of the conjugator, and the junction follows from the alternation of the original word, with no
  inequality involved.
- 2026-08-03 — Settled that the cyclic reduction recursion should run on plain reduced alternating
  words, not transversal ones.  Transversality is needed only at the end, for uniqueness of normal
  words, and the transversal form restores it while preserving the indices — whereas insisting on it
  throughout forces a base group element out of the front of the word at every step, which the
  conjugation then cannot absorb.  With plain words every base group element produced along the way
  is absorbed into a neighbouring letter: on the left by the existing absorption, and on the right by
  the one proved here, which is what keeps the step inside the class when a merged letter falls into
  the base group and the word shortens by two.
- 2026-08-03 — Stated the cyclic reduction step in both of its cases, the merged letter surviving or
  falling into the base group.  Also identified the invariant the recursion should carry, after
  finding that the natural-looking one fails: it is *not* true that the last letter of the
  cyclically reduced part always carries the index of the last letter of the conjugator — that fails
  exactly in the shortening-by-two case.  What is true in both cases is that `V` and the tail `B`
  begin in the same factor, because both are obtained from the suffix of the word after the
  conjugator by operations at its end, and then the junction is just cyclic reducedness of `V`.
- 2026-08-03 — Identified the tail of the power word exactly: writing an element as `C · V · C⁻¹` is
  equivalent to identifying the tail of its word with `V · C⁻¹`, so the tail *is* the suffix of the
  word after the conjugator rather than merely resembling it.  This removes the separate tail `B`
  from the argument — the word splits as `C ++ R`, the power word is `C ++ Vᵏ ++ R`, and both
  junction conditions follow from the alternation of `C ++ R` together with cyclic reducedness of
  `V`.  With the base case and the step's inheritance also proved, the algebraic bookkeeping of the
  recursion is complete; what is left is the index bookkeeping.
- 2026-08-03 — Proved the index bookkeeping of the recursion: two words with a common prefix
  differing only in their last letter have suffixes beginning in the same factor, provided the
  differing letters lie in the same factor.  This is what propagates the one remaining invariant —
  that the cyclically reduced part and the tail begin in the same factor — since a reduction step
  changes only the tail of the word, in both of its cases.  The three cases of the proof are the
  prefix ending strictly inside the common part, exactly at its end, or beyond it, the last being
  excluded because the suffix is nonempty.
- 2026-08-03 — Proved the conjugator-side surgery: a prefix leaving a nonempty suffix cannot reach
  the last letter, so the conjugator produced for the reduced word is also a prefix of the word
  before the step, and the two suffixes have the same length.  Together with the suffix index lemma
  this is everything the reassembly step needs — the recursion's outputs transfer backwards across a
  reduction step without recomputation.
- 2026-08-03 — Generalized the prefix and suffix surgery to an arbitrary changed tail.  The two cases
  of a reduction step change the end of the word differently — one letter is replaced by one, or by
  two — so the earlier statements, which assumed a single changed letter, only covered the first.
  With the tail arbitrary a single pair of statements covers both: the prefix transfers whenever it
  stops inside the common part, and the suffixes begin in the same factor as soon as the changed
  tails do.
- 2026-08-03 — Proved the reassembly of the cyclic reduction data after a step: from the data of the
  reduced word, the data of the original is obtained by prepending the stripped letter to the
  conjugator and taking the corresponding suffix as the tail.  All four conclusions come out
  together — the splitting, the nonemptiness of the tail, the shared first factor, and the product
  identity, the last by cancelling the conjugator from the two descriptions of the element.  Taking
  the replacement tail as a parameter lets one reassembly serve both reduction cases.  What is left
  is the induction that applies it.
- 2026-08-03 — Proved the two ends of the recursion: the base case, where a cyclically reduced word
  or a single letter is its own data, and the decomposition of a word that is not cyclically
  reduced into first letter, middle and last letter.  The middle is automatically nonempty, since a
  two letter word alternates and so has its first and last letters in different factors — which is
  what makes the reduction step always applicable when it is invoked.
- 2026-08-03 — Completed the cyclic reduction recursion: every nonempty reduced alternating word
  splits as a conjugator followed by a tail, with a cyclically reduced part or a single letter, the
  tail and the cyclically reduced part beginning in the same factor, and the tail equal to the
  cyclically reduced part times the inverse conjugator.  Having proved the base case, the
  decomposition, the two step cases and the reassembly separately, the recursion itself came out as
  a short wrapper.  This is the production of the data the two-exponent comparison consumes, so the
  shape `C · Vᵏ · R` is now available for an arbitrary element, with its junction conditions coming
  from the alternation of `C ++ R` and cyclic reducedness of `V`.
- 2026-08-03 — Located the remaining obstruction precisely, and proved what survives it.  The
  comparison reads off normal words, whose letters lie in the transversal, but the words the
  recursion produces do not: the conjugator inherits the head of the element in its first letter and
  each reduction step creates a merged letter at the end.  Normalizing pushes base group elements
  leftwards through the whole word, so the transversal form of `C ++ Vᵏ ++ R` is not the
  concatenation of the transversal forms and the letters cannot be compared directly.  What is
  invariant under the normalization is the sequence of indices, and that is now proved.  The
  comparison therefore yields the rotation of index sequences; recovering the letters is the
  remaining gap.
- 2026-08-03 — Proved the one shape in which normalization is harmless: a reduced alternating word
  whose letters lie in the transversal except at the front normalizes by replacing that first letter
  with its transversal representative and releasing a head, leaving the other letters untouched.
  This is exactly the shape the comparison needs, and the conjugator and the tail already have it,
  being a prefix and a suffix of the word of the element.  The cyclically reduced part is the one
  piece that fails it, because each reduction step creates its merged letter at the end.  Next: the
  length consequence, which needs no letters at all — comparing at two exponents gives the length of
  the cyclically reduced part and then the length of the conjugator, so the two decompositions align
  position by position with no rotation.
- 2026-08-03 — Proved the length of a power, which needs no transversality: normalization changes the
  letters of a word but not their number, so the length of the `(k+1)`-st power of `C · V · C⁻¹` is
  `|C| + k·|V| + |R|` and each further power adds `|V|`.  The powers grow linearly at exactly the
  length of the cyclically reduced part.  This is the two-exponent trick carried out on the one
  invariant that survives normalization: comparing at `n` and `2n` cancels the constant term and
  gives `|V_x| = |V_y|`, then the constant term gives `|C_x| = |C_y|`, so the two decompositions have
  the same shape and the rotation relating them is trivial.
- 2026-08-03 — Proved the two exponent comparison: two elements with the same `n`-th power have
  cyclically reduced parts of the same length, and are themselves of the same length.  A single
  exponent leaves the constant term of the linear growth undetermined; `n` and `2n` cancel it.  The
  two decompositions therefore align position by position and no rotation machinery is needed in the
  endgame.  What remains is the passage from the shape to the letters, for which the route is the
  conjugacy criterion for cyclically reduced elements: the induction shortens the conjugating element
  by moving a letter across whenever the conjugate fails to be longer, using the conjugate length
  bounds and the merge dichotomy, both already proved.
- 2026-08-03 — Proved that rotations of a cyclically reduced word are cyclically reduced, the first
  ingredient of the conjugacy criterion: the junction a rotation creates is an adjacent pair of the
  original word, and the junction it destroys is the one the cyclic condition controls.  Also that
  conjugating by the first letter rotates by one.  Conjugating a cyclically reduced word by a single
  letter shortens it only when that letter is, up to the base group, the first or last letter of the
  word, and the result is then the rotation; so a conjugating element between two cyclically reduced
  words of the same length can be shortened one letter at a time, each step rotating.  That is the
  induction the criterion runs, and it is the next block.
- 2026-08-03 — Proved both sides of the one-letter dichotomy that drives the conjugacy criterion.
  Conjugating by a letter whose factor occurs neither at the front nor at the back of the word
  lengthens it by two, there being no cancellation at either end; and if the letter comes from the
  front factor and the front letter cancels it into the base group, the conjugate is exactly the
  rotation by one, conjugated by the base group element the cancellation produced.  A conjugation
  that does not lengthen must therefore use a letter from an extreme factor, and one that shortens by
  the full two must cancel completely, which is the rotation.
- 2026-08-03 — Proved the middle case of the one-letter dichotomy: a letter from the front factor
  that the front letter does not cancel into the base group lengthens the word by one, the front
  merging but surviving while nothing cancels at the back.  With the other two cases this closes the
  trichotomy — grow by two, grow by one, or rotate.  A second lemma written for this cycle turned out
  to be already proved in full generality in the corpus (`deningerLen_base_conj`: conjugation by the
  base group preserves length, for an arbitrary element rather than a word), so it was dropped rather
  than duplicated; the base element the rotation carries therefore never disturbs the induction.
- 2026-08-03 — Proved the back half of the one letter trichotomy, mirroring the front: cancellation
  of the last letter into the base group makes the conjugate the rotation that moves the last letter
  to the front, and incomplete cancellation at the back lengthens by one.  The trichotomy is now
  complete on both sides — grow by two, grow by one, or rotate forwards or backwards — which is
  everything the induction of the conjugacy criterion consumes at each step.
