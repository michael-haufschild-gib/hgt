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
  `GaloisForLFunctions.RHTower.DeningerRationalFreeDGroup` (`Bau(ℤ) ≅ ℚ`)

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
