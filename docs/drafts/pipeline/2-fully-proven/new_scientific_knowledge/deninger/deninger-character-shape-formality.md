# Real formality of Deninger--Kucharczyk--Scholze character components

- **ID:** `deninger-character-shape-formality`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Parent:** `deninger-derived-mw-rational-witt-coefficient`
- **Statement:** The real shape-cochain algebra of a cyclotomic rational-Witt character
  component is the exterior algebra on its degree-one unit space; consequently the ordinary
  unit-amalgamated coefficient is the real Milnor symbol algebra.

## Setup

Let \(F\) be any field of characteristic zero containing \(\mu_\infty\), fix
\(\mu_\infty\hookrightarrow S^1\), and put
\[
 V_F=F^\times/\mu_\infty.
\]
The torsion subgroup of \(F^\times\) is exactly \(\mu_\infty\), so \(V_F\) is
torsion-free.  Divisibility and algebraic closedness are not required.

The Kucharczyk--Scholze character component is a torsor under the compact character group
\[
 T_F:=\operatorname{Hom}(V_F,S^1).
\]
Choosing one extension of the fixed character on \(\mu_\infty\) identifies the component
with \(T_F\).  The resulting cochain algebra and all conclusions below are independent of
that choice up to translation, and translation acts trivially on invariant forms.

Let \(\mathcal L_F\) be the filtered poset of finitely generated free subgroups
\(L\subset V_F\).  Restriction of characters gives
\[
 T_F\cong\varprojlim_{L\in\mathcal L_F}T_L,\qquad
 T_L=\operatorname{Hom}(L,S^1),
\]
and each \(T_L\) is a finite-dimensional torus.  Define the real shape-cochain CDGA by
\[
 C^*_{\mathrm{sh}}(T_F;\mathbb R)
 :=
 \varinjlim_{L\in\mathcal L_F}\Omega^*(T_L;\mathbb R),                 \tag{1}
\]
with transition maps given by pullback.  This model computes continuous Čech/sheaf
cohomology because Čech cohomology is continuous on inverse systems of compact Hausdorff
spaces with surjective bonding maps.

## Formality theorem

`[PROVED HERE] [DAC_CHARACTER_SHAPE_FORMALITY]`

There is a natural quasi-isomorphism of commutative DGAs
\[
 \left(\Lambda_{\mathbb R}^*(V_F\otimes_{\mathbb Z}\mathbb R),0\right)
 \xrightarrow{\;\sim\;}
 C^*_{\mathrm{sh}}(T_F;\mathbb R).                                    \tag{2}
\]

### Proof

For every lattice \(L\), let
\(\Omega^*_{\mathrm{inv}}(T_L)\) be the translation-invariant differential forms.  Evaluation
at the identity gives
\[
 \Omega^*_{\mathrm{inv}}(T_L)
 \cong
 \left(\Lambda_{\mathbb R}^*(L\otimes_{\mathbb Z}\mathbb R),0\right).
\]
The inclusion of invariant forms into all smooth forms is a multiplicative
quasi-isomorphism: it is the standard de Rham representative of the cohomology of a torus.
For a homomorphism \(T_{L'}\to T_L\), pullback preserves invariant forms, so these
quasi-isomorphisms form a natural filtered diagram.

Filtered colimits of real vector spaces are exact.  Taking the colimit of the natural
quasi-isomorphisms therefore gives a quasi-isomorphism
\[
 \varinjlim_L
 \Lambda_{\mathbb R}^*(L\otimes\mathbb R)
 \xrightarrow{\sim}
 \varinjlim_L\Omega^*(T_L).
\]
Exterior powers commute with filtered colimits, and
\(\varinjlim_LL=V_F\).  The source is consequently
\(\Lambda_{\mathbb R}^*(V_F\otimes_{\mathbb Z}\mathbb R)\), proving `(2)`.

## Free-unit identification

Let
\[
 \mathcal P_{F,\mathbb R}
 =
 \operatorname{Free}_{E_\infty,H\mathbb R}^{+}
 \bigl(\Sigma_{\mathrm{ar}}H(V_F\otimes_{\mathbb Z}\mathbb R)\bigr).
\]
Rational \(E_\infty\)-algebras are modeled by commutative DGAs.  A free commutative algebra
on generators in odd arithmetic degree one is the exterior algebra.  Hence
\[
 \pi_*\mathcal P_{F,\mathbb R}
 \cong
 \Lambda_{\mathbb R}^*(V_F\otimes_{\mathbb Z}\mathbb R).               \tag{3}
\]
The Kummer map
\[
 \mathcal P_{F,\mathbb R}
 \longrightarrow
 C^*_{\mathrm{sh}}(T_F;\mathbb R)
\]
is the map represented by invariant degree-one forms.  Equations `(2)`--`(3)` show that it
is an equivalence of \(E_\infty\) \(H\mathbb R\)-algebras.

`[PROVED HERE] [DAC_REAL_FREE_UNIT_EQUIVALENCE]`
\[
 \mathcal P_{F,\mathbb R}
 \xrightarrow{\sim}
 C^*_{\mathrm{sh}}(T_F;\mathbb R).                                    \tag{4}
\]

## Milnor-amalgamation corollary

Let
\[
 \mathcal K_{F,\mathbb R}^M
 :=
 H\!\left(K_*^M(F)_{\mathrm{tf}}\otimes_{\mathbb Z}\mathbb R\right)
\]
be the Eilenberg--Mac Lane \(E_\infty\) algebra of the real graded Milnor ring, with zero
differential.  Its symbol map gives
\(\mathcal P_{F,\mathbb R}\to\mathcal K_{F,\mathbb R}^M\).  Then
\[
 \begin{aligned}
 \mathcal C_{F,\mathbb R}^M
 &:=
 C^*_{\mathrm{sh}}(T_F;\mathbb R)
 \mathop{\otimes}^{\mathbb L}_{\mathcal P_{F,\mathbb R}}
 \mathcal K_{F,\mathbb R}^M \\
 &\simeq
 \mathcal K_{F,\mathbb R}^M.                                         \tag{5}
 \end{aligned}
\]

### Proof

Base change along the equivalence `(4)` is an equivalence.  Therefore the left side of `(5)`
is
\[
 \mathcal P_{F,\mathbb R}
 \otimes_{\mathcal P_{F,\mathbb R}}^{\mathbb L}
 \mathcal K_{F,\mathbb R}^M
 \simeq\mathcal K_{F,\mathbb R}^M.
\]

Consequently
\[
 \pi_q\mathcal C_{F,\mathbb R}^M
 \cong K_q^M(F)_{\mathrm{tf}}\otimes_{\mathbb Z}\mathbb R
 \quad(q\geq0).                                                        \tag{6}
\]
This proves the real local form of the Kucharczyk--Scholze Milnor comparison, including all
Steinberg relations and higher syzygies.  It is stronger than killing degree-two Steinberg
classes one at a time.

## Equivariance

Every field automorphism preserving the chosen cyclotomic structure acts linearly on \(V_F\),
dually on \(T_F\), and functorially on invariant forms and Milnor symbols.  Thus `(2)`--`(6)`
are equivariant for the cyclotomic Galois action.  Likewise \(a\mapsto a^n\) acts as scalar
multiplication by \(n\) on \(V_F\), and all displayed maps commute with the corresponding
Frobenius action.

This proves equivariance on the cyclotomic ordinary channel.  Verschiebung across ramified
finite correspondences and MW residue enrichment require the separate coherent Gysin
construction.

## Boundary of the theorem

- The theorem uses shape/Čech cochains `(1)`.  Identifying these with the precise completed
  leafwise complex used after Deninger's suspension remains a global comparison.
- It proves the real ordinary Milnor channel.  Integral torsion, twisted MW residue data,
  and global rank/signature descent remain open.
- It does not construct arithmetic residue gluing, archimedean regulator, Hodge positivity,
  Lefschetz trace, determinant, or RH.

## References

- Robert A. Kucharczyk and Peter Scholze,
  *Topological realisations of absolute Galois groups*, Theorem 1.8 and Question 1.10:
  https://people.mpim-bonn.mpg.de/scholze/GaloisTop.pdf
- Yves Félix and Steve Halperin,
  *Rational homotopy theory via Sullivan models: a survey*:
  https://arxiv.org/abs/1708.05245
- Jacob Lurie, *Higher Algebra*, rational commutative algebra and free algebras:
  https://www.math.ias.edu/~lurie/papers/HA.pdf

## Log

- 2026-07-26 — proved real shape formality and the ordinary unit-amalgamated Milnor
  comparison on every cyclotomic character component; the proof only needs
  \(F^\times/\mu_\infty\) torsion-free, so algebraic closedness was removed.

## Lean status

### What landed

`formal/GaloisForLFunctions/RHTower/DeningerCharacterShapeFormality.lean`, 22 declarations, axiom
audit for every one of them within `propext, Classical.choice, Quot.sound` (several need only
`propext, Quot.sound`).

**The Setup, completely.**  The card's setup asserts three things about `V_F = F^×/μ_∞` and its
lattice filtration; all three are proved.

- `DeningerUnitSpace F`, `deningerUnitSpace_isTorsionFree` — **`V_F` is torsion-free**.
  `deningerTorsion_iff_isOfFinOrder` is the sentence "the torsion subgroup of `F^×` is exactly
  `μ_∞`": a unit is torsion in the additive sense exactly when it has finite order, both signs of
  the exponent handled.  `deningerUnitClass_eq_zero_iff` is the same statement on classes.
- `deningerLatticeFree` — **every finitely generated subgroup of `V_F` is free**, so `𝓛_F` really
  is a poset of lattices.  This needs the torsion-freeness to be inherited by the subgroup, which
  is where the previous item is used.
- `deningerFGSubmodule_directed`, `deningerFGSubmodule_iSup_top` — **`𝓛_F` is filtered and
  exhausts `V_F`**, so `V_F = colim_L L`.

**The two structural consequences the proof runs on.**

- `deningerLatticeLift`, `_apply`, and `deningerLatticeHom_ext` — **`T_F = lim_L T_L`**: a
  compatible family of homomorphisms on the lattices glues to a single homomorphism on `V_F`, and
  homomorphisms agreeing on every lattice are equal.  mathlib has `Subalgebra.iSupLift` but no
  submodule analogue, so the glue is built here from `Set.iUnionLift`, with additivity and
  linearity proved by moving both arguments into a common lattice.
- `deningerExterior_iSup_adjoin` — **exterior algebras commute with the filtration**: the
  subalgebras generated by the generators coming from the lattices exhaust the exterior algebra,
  because every generator already lies in one lattice.  This is the step
  `colim_L Λ*(L ⊗ ℝ) = Λ*(V_F ⊗ ℝ)` of the proof of `(2)`.

**Equivariance.**  `deningerUnitClass_zpow` is the card's statement that `a ↦ a^n` acts as
multiplication by `n` on `V_F`; `deningerUnitClass_mul` is the additivity that makes the whole
picture a homomorphism.

**The underived shadow of `(5)`.**  `deningerUnitAmalgam` is `P ⊗_P K ≅ K` and
`deningerBaseChangeCongr` is the invariance of the amalgamated coefficient under replacing the
unit algebra by an equivalent one — the two facts that the proof of `(5)` composes, at the
1-categorical level available in Lean.

**The analytic heart of `(2)`: the de Rham complex of a torus and its cohomology.**
`formal/GaloisForLFunctions/HTGeometry/` — `PeriodicAveraging`, `AlternatingContraction`,
`PeriodicHomotopy`, `PeriodicConstantForm`, `PeriodicFullAverage`, `AlternatingFormExterior`,
`PeriodicCohomology`; every declaration axiom-audited inside `propext, Classical.choice, Quot.sound`.

A form on the torus `T_L = (L ⊗ ℝ)^∨ / L^∨` is a form on the universal cover invariant under the
lattice, so `Ω^*(T_L;ℝ)` is written down as the complex of `C^1` maps from the coordinate space to
the continuous alternating forms that are periodic in each coordinate, with mathlib's `extDeriv` as
the differential.  In that model the whole of `Ω^*_inv(T_L) ≅ Λ^*(L ⊗ ℝ)` and the quasi-isomorphism
statement are theorems, proved over any `RCLike` field and any nonzero period, hence in particular
over `ℝ` with the standard integer lattice.

- `periodCurve`, `averageOp`, `averageOp_hasFDerivAt`, `averageOp_extDeriv` — averaging a form over
  one period differentiates under the integral sign and commutes with the exterior derivative.
- `contractCLM`, `cartan_contract` — the Cartan formula for the constant vector field of a period
  direction: antisymmetrizing the contraction of a derivative is the directional derivative minus
  the contraction of the exterior derivative.
- `averageOp_sub_eq_extDeriv` — the average of a closed form over a period differs from the form by
  an exact form, the primitive being the weighted average of the contraction; the weight is what one
  integration by parts along the period produces.
- `const_of_flowInvariant`, `periodicAveragedData`, `periodic_closed_eq_const_add_exact` — averaging
  over every coordinate period in turn makes a closed periodic form invariant under all the period
  flows, hence constant, and changes it only by an exact form with a periodic primitive.
- `constantForm_eq_zero`, `periodic_const_add_exact_unique` — a constant form that is the exterior
  derivative of a periodic `C^1` form vanishes, by induction on the degree from the one-form case.
- `periodicClosedForms`, `periodicExactForms`, `periodicCohomology`, `periodicCohomologyEquiv` —
  the cohomology of the periodic de Rham complex, and the theorem that sending a constant
  alternating form to its class is an isomorphism onto it.  **This is exactly the statement that the
  inclusion of the translation-invariant forms is a quasi-isomorphism**: surjectivity is the
  averaging decomposition, injectivity the vanishing above.
- `alternatingFormExteriorEquiv`, `periodicCohomologyExteriorEquiv` — evaluation at the identity
  identifies the invariant forms with `Λ^k` of the cover, so `H^k(T_L) ≅ Λ^k(L ⊗ ℝ)`.
- `torusCohomologyEquiv`, `torusCohomologyExteriorEquiv` — the real torus `ℝ^r/ℤ^r` itself.

Supporting infrastructure built for it and reusable: `continuousAlternatingEquiv` (on a finite
coordinate space the alternating maps are exactly the continuous ones, as a linear equivalence),
and the generalisation of `multilinearMap_bound` to an arbitrary nontrivially normed field.

**Naturality in the lattice.**  `formal/GaloisForLFunctions/HTGeometry/PeriodicPullback.lean`.

- `periodLattice`, `periodic_of_mem_periodLattice` — a form periodic in every coordinate is
  invariant under the whole period lattice, by induction over the generated subgroup.
- `linearPullback`, `linearPullback_extDeriv`, `linearPullback_periodic`, `linearPullback_mem_closed`
  — pullback along a linear map of covers carrying the lattice into the lattice preserves class
  `C^1`, periodicity, closedness and exactness, and commutes with the exterior derivative.
- `periodicCohomologyMap` — the induced map of the cohomologies.
- `periodicCohomologyMap_constantClass` — **the comparison is natural**: the induced map sends the
  class of an invariant form to the class of its composition with the map of covers, which is
  exactly the pullback of invariant forms.

### What cannot be stated in Lean, and why

- `C^*_sh(T_F;ℝ)` is the filtered colimit over `L` of the complexes `Ω^*(T_L;ℝ)`.  Every ingredient
  of `(2)` is now formalized separately — each term and its cohomology, the naturality of the
  comparison in `L`, the exactness of filtered colimits (`directLimit_map_exact`), and the
  commutation of exterior powers with them (`exteriorPowerDirectLimitEquiv`,
  `deningerExterior_iSup_adjoin`).  What is not written down is the colimit of the complexes as a
  single CDGA together with its multiplicative structure, which is a statement about commutative
  differential graded algebras rather than about any one torus.
- `(3)` and `(4)` are statements about free `E_∞` `Hℝ`-algebras.  mathlib has no `E_∞`-algebras and
  no CDGA homotopy theory.  What survives is the algebraic content of "a free commutative algebra
  on generators in odd degree one is the exterior algebra": that is the universal property of
  `ExteriorAlgebra`, already used across the corpus and, in the form needed here, recorded in
  `DeningerRelativeSullivanMilnorResolution`.
- `(5)` and `(6)` are derived base change and homotopy groups.  Only the underived shadow is
  stated.

So the card stays at stage 2.  What is formalized is the entire algebraic input: the unit space is
torsion-free, its lattices are free, filtered and exhausting, characters on it are the inverse
limit of characters on lattices, exterior algebras pass to the colimit, and the power maps act by
scalars.

### Log

- 2026-08-02 — Formalized the setup and the two filtration arguments of the proof of `(2)`, and
  the equivariance.
- 2026-08-04 — Formalized the analytic heart of `(2)`: the de Rham complex of a torus in the
  periodic-forms model on the universal cover, the averaging/Cartan proof that its cohomology is the
  constant alternating forms, and the identification of those with `Λ^*` of the cover.  The
  statement "mathlib has no de Rham complex of a manifold, so this step cannot be written down" was
  wrong: the covering model needs only `extDeriv` and periodicity.  Also formalized the naturality
  of the comparison in `L`, so every ingredient of `(2)` except the CDGA structure of the colimit is
  now a theorem.
