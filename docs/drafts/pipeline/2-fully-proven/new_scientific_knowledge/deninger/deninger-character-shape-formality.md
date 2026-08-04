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

**The identification with `Λ^*(L ⊗ ℝ)`, canonically.**
`formal/GaloisForLFunctions/HTGeometry/ExteriorFormPairing.lean`,
`.../TorusExteriorComparison.lean`.

Evaluation at the identity is written down without choosing a basis: an element of
`⋀^n(L ⊗ ℝ)` — the exterior power of the dual of the covering space `Hom(L,ℝ)` — defines an
invariant `n`-form, on a product of linear forms the determinant of their values.

- `formOfExterior`, `formOfExterior_ιMulti` — the alternating form of an element of the exterior
  power of the dual, and its determinant formula.
- `pairingDual_bijective`, `formOfExteriorEquiv` — mathlib builds the pairing
  `⋀^n(M^∨) → (⋀^n M)^∨` but not its bijectivity; it is proved here for any module with a finite
  basis, because the exterior products of the dual basis go to the dual basis of the exterior
  products.
- `formOfExterior_map_dualMap` — the identification is natural: transport along the exterior power
  of the transpose is composition with the map.
- `constantFormOfExterior`, `periodicCohomologyDualEquiv` — `H^{n+1}(T_L) ≅ Λ^{n+1}(L ⊗ ℝ)`,
  canonically.
- `periodicCohomologyDualEquiv_naturality` — **the comparison of `(2)` is a map of directed
  systems**: pullback along a map of lattices on the cohomology side corresponds to the exterior
  power of the transpose on the `Λ^*` side.

**Differential forms in coordinates, and the wedge with a one-form.**
`formal/GaloisForLFunctions/HTGeometry/FormWedge.lean`.

- `exteriorConsMul`, `exteriorConsMul_ιMulti` — multiplication of an exterior power by a vector on
  the left, one degree up, inherited from the exterior algebra.
- `constantFormOfExterior_consMul` — under the identification with alternating forms this is the
  cofactor expansion of a determinant along its first column, so it is the wedge with a one-form.
- `extDeriv_smul_constantForm` — **the Leibniz rule in the case of a degree-zero factor**:
  `d(f · c) = df ∧ c` for an invariant `c`.
- `coordForm`, `coordFormBasis`, `constantForm_expansion` — the coordinate forms of the `n`-element
  sets of coordinates are a basis of the invariant forms, and every invariant form is the sum of its
  values on the corresponding tuples of basis vectors.
- `form_coeff_differentiable`, `extDeriv_finset_sum`, `extDeriv_eq_sum_consMul` — **the exterior
  derivative in coordinates**: the coefficients of a `C^1` form are `C^1`, and the exterior
  derivative is the sum of the wedges of their differentials with the coordinate forms.

**The wedge product and the Leibniz rule — the differential graded algebra.**
`formal/GaloisForLFunctions/HTGeometry/ExteriorGradedMul.lean`, `.../FormWedgeLeibniz.lean`,
`.../PeriodicCohomologyRing.lean`.  Mathlib has no wedge product of differential forms and no
Leibniz rule; both are built here.

- `exteriorMulOf` (+ bilinearity, `exteriorMulOf_assoc`) — the product of exterior powers in the
  degree prescribed by an equation, inherited from the exterior algebra.
- `ιMulti_mul_ι`, `exteriorPower_mul_ι`, `mulOf_consMul_right` — **a factor of degree one moves past
  a factor of degree `p` at the cost of `(-1)^p`**, proved from the anticommutation of the
  generators by induction and extended off the generators by linearity.
- `wedgeForm` (+ bilinearity, `wedgeForm_expansion`) — the wedge product of alternating forms,
  transported from the exterior algebra of the dual; its expansion in the coordinate forms.
- `extDeriv_wedgeForm` — **the Leibniz rule**
  `d(ω ∧ η) = dω ∧ η + (-1)^p ω ∧ dη`, for `C^1` forms of any degrees on a coordinate space.  This
  is what makes `Ω^*(T_L;ℝ)` a differential graded algebra.
- `wedgeForm_differentiable`, `wedgeForm_fderiv_continuous`, `wedgeForm_periodic`,
  `wedgeForm_mem_closed` — the wedge of two closed periodic `C^1` forms is one, so the product stays
  inside the complex.
- `wedgeForm_extDeriv_left`, `wedgeForm_extDeriv_right` — wedging with a closed form commutes with
  `d` (with the sign `(-1)^p` on the left), hence exact ∧ closed is exact.
- `wedgeForm_class_eq` — **the comparison is multiplicative**: replacing a closed form by its
  invariant representative plus an exact term changes the wedge by an exact term with a periodic
  primitive, so the class of a wedge is the wedge of the invariant representatives, and on invariant
  forms the wedge is the product of `Λ^*(L ⊗ ℝ)` by construction (`wedgeForm_constantFormOfExterior`).

**The colimit over the lattice filtration.**
`formal/GaloisForLFunctions/HTGeometry/TorusCohomologyColimit.lean`.

- `periodicCohomologyMap_id`, `periodicCohomologyMap_comp`, `map_periodLattice`,
  `linearPullback_comp` (in `PeriodicPullback.lean`) — pullback of forms is functorial, so the
  cohomologies really form a directed system.
- `TorusCoverSystem` — a directed system of tori, given by the covering spaces and the lifts of the
  homomorphisms between them, with `DirectedSystem` instances for the cohomologies, for the exterior
  powers of the duals, and for the duals themselves.
- `torusCohomologyColimitEquiv` — **the comparison passes to the colimit**: `colim_L Λ^k(L ⊗ ℝ) ≅
  colim_L H^k(T_L)`, from the stagewise isomorphism and its naturality.
- `torusCohomologyColimitExteriorEquiv` — composed with the commutation of exterior powers with
  filtered colimits along injective maps, this is
  `Λ^k(colim_L (L ⊗ ℝ)) ≅ colim_L H^k(T_L)`, which is `(2)` in cohomology.
- `coordProjectionSystem`, `coordProjectionSystem_surjective` — the tower of tori of a monotone
  family of dimensions, with the coordinate projections as lifts: the hypothesis class of the
  colimit theorem is inhabited by the systems that actually arise from a lattice filtration.

**The smooth de Rham complex of the torus.**
`formal/GaloisForLFunctions/HTGeometry/PeriodicSmoothness.lean`,
`.../SmoothPeriodicCohomology.lean`.

The `C^1` model above computes the cohomology but is not literally a complex, because `d ∘ d` needs
two derivatives.  The whole construction is therefore redone in the smooth category, which needs one
theorem mathlib does not have: **smoothness under the integral sign** for the averaging operator.

- `averageOp_continuous`, `averageOp_contDiff`, `averageOp_contDiff_infty` and the same for
  `weightHomotopy` — the derivative of the average is the average of the derivative, so the order of
  differentiability is preserved; induction on the order gives `C^n` and hence `C^∞`.
- `periodicAveragedData_contDiff`, `periodic_closed_eq_const_add_exact_smooth` — the averaging
  decomposition of a closed periodic form stays inside the smooth forms.
- `smoothPeriodicClosedForms`, `smoothPeriodicExactForms`, `smoothPeriodicCohomology`,
  `smoothPeriodicCohomologyEquiv` — **the cohomology of the smooth periodic de Rham complex is the
  space of constant alternating forms**: the inclusion of the invariant forms into the de Rham
  complex of the torus is a quasi-isomorphism.
- `smoothPeriodicForms`, `extDeriv_mem_smoothPeriodicForms`, `fderiv_periodic`,
  `smoothExtDerivMap`, `smoothExtDerivMap_comp` — `Ω^*(T_L;ℝ)` as an actual cochain complex of
  `ℝ`-vector spaces, with `d ∘ d = 0`; `mem_ker_smoothExtDerivMap` and
  `mem_range_smoothExtDerivMap` identify its kernel and image with the closed and the exact forms,
  so `smoothPeriodicCohomology` is its cohomology.

**`Ω^*(T_L;ℝ)` as a commutative differential graded algebra.**
`formal/GaloisForLFunctions/HTGeometry/ExteriorGradedMul.lean` (extended),
`.../FormWedgeLeibniz.lean` (extended), `.../SmoothPeriodicDGA.lean`.

- `ι_mul_exteriorPower`, `ιMulti_mul_comm`, `exteriorPower_mul_comm`, `exteriorMulOf_comm` — **the
  exterior algebra is graded commutative**, `x·y = (-1)^{pq} y·x` for homogeneous `x, y`; mathlib has
  neither this nor the wedge product it governs.  Proved by induction on the degree from the
  anticommutation of the generators, then extended off the generators by linearity.
- `wedgeForm_comm`, `wedgeForm_assoc` — the same for the wedge product of alternating forms.
- `form_coeff_contDiff`, `wedgeForm_contDiff`, `wedgeForm_mem_smoothPeriodicForms` — the wedge of
  smooth periodic forms is a smooth periodic form.
- `smoothWedge` and its bilinearity, `smoothWedge_assoc`, `smoothWedge_comm`,
  `smoothExtDerivMap_smoothWedge` — **all the axioms of a commutative differential graded algebra**
  for `Ω^*(T_L;ℝ)` with `smoothExtDerivMap` as the differential: bilinear, associative, graded
  commutative, and the differential is a graded derivation.

**Commutative differential graded algebras, and `(2)` as a single morphism.**
`formal/GaloisForLFunctions/HTGeometry/CDGA.lean`, `.../TorusDeRhamCDGA.lean`.

Mathlib has graded algebras and homological complexes but no commutative differential graded
algebras, so the structure is built here.

- `CDGAStructure` — a family of modules in nonnegative degrees with a bilinear, associative, graded
  commutative product adding degrees and a differential raising it by one, squaring to zero and
  satisfying the Leibniz rule.
- `CDGAStructure.cocycles`, `.coboundaries`, `.cohomology` — the cohomology in each degree.
- `CDGAHom`, `CDGAHom.cocyclesMap`, `CDGAHom.cohomologyMap`, `CDGAHom.IsQuasiIso` — morphisms, the
  induced map on cohomology, and the notion of quasi-isomorphism.
- `exteriorCDGA` — `Λ^*(L ⊗ ℝ)` with the exterior product and the zero differential.
- `torusDeRhamCDGA` — **`Ω^*(T_L;ℝ)` as an object**: the smooth periodic forms with `smoothWedge`
  and `smoothExtDerivMap`, every axiom discharged from the theorems above.
- `torusFormalityHom` — **the comparison of `(2)` as a single morphism of commutative differential
  graded algebras**.

- `torusFormality_isQuasiIso` — **the comparison is a quasi-isomorphism**: it induces an isomorphism
  on cohomology in every degree, injective because a constant form with a smooth periodic primitive
  vanishes, surjective because averaging writes every closed smooth periodic form as a constant one
  plus an exact one.

So `(2)` for a single torus is a single morphism of commutative differential graded algebras
together with the statement that it is a quasi-isomorphism, all unconditional in Lean.  (The module
family of a `CDGAStructure` is a parameter, not a field: an instance-carrying field blocks the
definitional unfolding that the coercions of a concrete algebra need.)

**The colimit of a directed system of such algebras.**
`formal/GaloisForLFunctions/HTGeometry/CDGAColimit.lean`.

- `CDGADirectedSystem` — the functoriality of a directed family of morphisms.
- `degTransition`, `colimDeg`, `directedSystem_deg` — the direct limit in each degree.
- `colimD`, `colimD_of`, `colimD_comp` — the differential on the limit and that it squares to zero.
- `mulFamily`, `mulFamily_compat`, `colimMul`, `colimMul_of` — the product on the limit, obtained
  from the bilinear lifting principle below.
- `exists_common₂`, `exists_common₃` — two or three elements of the limits in different degrees come
  from a common stage.
- `colimCDGA` — **the colimit of a directed system of commutative differential graded algebras**:
  associativity, graded commutativity and the Leibniz rule are checked by reducing to a common
  stage.
- `colimHomFun`, `colimHomFun_of`, `colimHom` — **a compatible family of morphisms induces a
  morphism of the colimit algebras**, again checked by reducing to a common stage.

**Cohomology commutes with filtered colimits of these algebras.**
`formal/GaloisForLFunctions/HTGeometry/CDGAColimitQuasiIso.lean`.

- `cocycle_at_stage` — a cocycle of the colimit is already a cocycle at some stage, by
  `Module.DirectLimit.of.zero_exact` applied to its differential.
- `colimHom_isQuasiIso` — **a family of morphisms that is a quasi-isomorphism at every stage induces
  a quasi-isomorphism of the colimits**.  Injectivity: a class killed in the colimit becomes, at a
  far enough stage, a class killed there, hence zero there, hence zero in the colimit.  Surjectivity:
  a class of the colimit comes from a cocycle at a stage, where the stagewise surjectivity applies.

**Bilinear maps out of a direct limit.**
`formal/GaloisForLFunctions/HTGeometry/DirectLimitBilinear.lean`.  Mathlib lifts linear maps out of
a direct limit but not bilinear ones; this is what the product on a colimit algebra needs.

- `ubOf`, `le_ubOf_left`, `le_ubOf_right` — a chosen upper bound of two indices.
- `directLimit_b_stage_eq` — **the value of a compatible family of bilinear maps at a common stage
  does not depend on the stage**: move both stages into a common upper bound and use the
  compatibility.
- `rightLift`, `rightLift_of`, `rightLift_of_stage`, `leftFamily` — the map on the second limit
  determined by an element of a stage of the first, and its linearity in that element.
- `directLimitBilinear`, `directLimitBilinear_of_of`, `directLimitBilinear_of_of_same` — **the
  induced bilinear map on the direct limits**, with its value on elements from a common stage.

**Pullback as a morphism of de Rham algebras.**
`formal/GaloisForLFunctions/HTGeometry/ExteriorGradedMul.lean` (extended),
`.../TorusPullbackDGA.lean`.

- `comp_finAppend`, `exteriorMulOf_ιMulti`, `exteriorMulOf_map` — **the exterior power of a linear
  map is multiplicative**, proved on products of vectors and extended by linearity in each factor.
- `wedgeForm_compContinuousLinearMap` — **the wedge product is natural under pullback**.
- `linearPullback_contDiff`, `linearPullback_mem_smoothPeriodicForms` — pullback preserves
  smoothness and periodicity.
- `torusPullbackHom` — **pullback along a map of lattices as a morphism of the de Rham algebras of
  the two tori**, so the tori of a `TorusCoverSystem` form a directed system of commutative
  differential graded algebras.

**Formality of a tower of tori — statement `(2)` assembled.**
`formal/GaloisForLFunctions/HTGeometry/TorusFormalityColimit.lean`.

- `exteriorPullbackHom` — the exterior power of the transpose, as a morphism of the exterior
  algebras with zero differential (multiplicativity is `exteriorMulOf_map`).
- `torusSystemHom`, `exteriorSystemHom`, `torusSystem_directed`, `exteriorSystem_directed` — a
  `TorusCoverSystem` gives two directed systems of commutative differential graded algebras.
- `torusFormality_compat` — the stagewise comparisons commute with the transition morphisms
  (`constantFormOfExterior_map_dualMap`).
- `torusFormalityColimit_isQuasiIso` — **the induced morphism of the colimit algebras is a
  quasi-isomorphism**: statement `(2)` for a directed system of tori, unconditional in Lean, as a
  single morphism of commutative differential graded algebras together with the proof that it is a
  quasi-isomorphism.  The hypothesis class is inhabited by `coordProjectionSystem`.
- `degTransition_exteriorSystemHom`, `colimDegExteriorEquiv`, `exteriorColimEquiv` — **the source of
  that comparison is the exterior power of the colimit of the duals of the covering spaces**, so for
  the lattice filtration of a unit space it is `Λ^n(V_F ⊗ ℝ)`.

**Towers of tori from integer matrices.**
`formal/GaloisForLFunctions/HTGeometry/IntegerCoverSystem.lean`.

- `integerVector_mem_periodLattice` — a vector with integer coordinates lies in the period lattice
  of period one.
- `IntegerCoverSystem`, `matrixCover`, `torusCoverSystemOfMatrices` — **a functorial family of
  integer matrices is a tower of tori**.  This is the form in which a filtration by lattices
  produces one: after choosing a basis of each lattice, restriction along an inclusion is an
  integer matrix, and its functoriality is matrix multiplication.

### What cannot be stated in Lean, and why

- `C^*_sh(T_F;ℝ)` is the filtered colimit over `L` of the complexes `Ω^*(T_L;ℝ)`.  Every ingredient
  of `(2)` is now formalized separately — each term and its cohomology, the naturality of the
  comparison in `L`, the exactness of filtered colimits (`directLimit_map_exact`), and the
  commutation of exterior powers with them (`exteriorPowerDirectLimitEquiv`,
  `deningerExterior_iSup_adjoin`).  Each `Ω^*(T_L;ℝ)` is now a differential graded algebra and the
  comparison with `Λ^*(L ⊗ ℝ)` is a multiplicative quasi-isomorphism, natural in `L`, and the
  comparison of the colimits is an isomorphism.  `Ω^*(T_L;ℝ)` is a commutative differential graded
  algebra in the full sense — every axiom is a theorem, the object is built, `(2)` is written down as
  a single morphism `torusFormalityHom` of such algebras, and `torusFormality_isQuasiIso` says it is
  a quasi-isomorphism.  For a single torus, `(2)` is therefore completely formalized.  Of the
  filtered colimit of these algebras, the underlying differential graded module is built
  (`colimCDGA`), a compatible family of morphisms induces a morphism of the colimits (`colimHom`),
  and a stagewise quasi-isomorphism has quasi-isomorphic colimit (`colimHom_isQuasiIso`).  So the
  whole shape of `(2)` — the two objects, the morphism, the quasi-isomorphism, and their behaviour
  under the filtered colimit — is formalized, unconditionally, in complete generality.  What is left
  is instantiated: `torusFormalityColimit_isQuasiIso` is `(2)` for a directed system of tori, and
  `exteriorColimEquiv` identifies the source of that comparison with the exterior power of the
  colimit of the duals.  What is not written down is the dictionary between the card's `𝓛_F` and a
  `TorusCoverSystem`: choosing, for each lattice `L`, a basis identifying `Hom(L,ℝ)` with `ℝ^{rk L}`,
  which turns restriction along `L ⊆ L'` into an integer matrix.  Everything after that choice is a
  theorem here — `torusCoverSystemOfMatrices` takes the matrices to the tower of tori — and
  everything before it too (`deningerLatticeFree`, `deningerFGSubmodule_directed`).  What is missing
  is only the choice itself and the identification of the restriction matrices.
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
  of the comparison in `L`, and made the identification with `Λ^*(L ⊗ ℝ)` canonical (basis-free)
  by proving that mathlib's `exteriorPower.pairingDual` is bijective for a finite basis.  Every
  ingredient of `(2)` except the assembly of the colimit is now a theorem.  Also formalized the
  wedge product of differential forms and the **Leibniz rule** `d(ω ∧ η) = dω ∧ η + (-1)^p ω ∧ dη`
  — neither is in mathlib — so each `Ω^*(T_L;ℝ)` is a differential graded algebra, and the
  comparison with `Λ^*(L ⊗ ℝ)` is multiplicative.  Finally formalized the colimit over the lattice
  filtration: `Λ^k(colim_L (L ⊗ ℝ)) ≅ colim_L H^k(T_L)`, with a concrete inhabited system of tori so
  the statement is not vacuous.  Finally redid the construction in the smooth category — which needed
  smoothness under the integral sign, absent from mathlib — so `Ω^*(T_L;ℝ)` is an actual cochain
  complex with `d ∘ d = 0` and its cohomology is `Λ^*(L ⊗ ℝ)`.  Proved graded commutativity of the
  exterior algebra and of the wedge product, and smoothness of the wedge, so every axiom of a
  commutative differential graded algebra holds for `Ω^*(T_L;ℝ)`.  Built the structure `CDGA` with
  its cohomology, morphisms and quasi-isomorphisms — mathlib has none — and `(2)` as a single
  morphism `torusFormalityHom : exteriorCDGA ⟶ torusDeRhamCDGA`, and proved
  `torusFormality_isQuasiIso`.  For a single torus, statement `(2)` is now fully formalized.  Also
  built the degreewise colimit of a directed system of such algebras with its differential, and the
  bilinear lifting principle for direct limits, the colimit algebra `colimCDGA` itself, and the
  induced morphism of colimits `colimHom`, and proved that a stagewise quasi-isomorphism has
  quasi-isomorphic colimit (`colimHom_isQuasiIso`), and assembled statement `(2)` for a directed
  system of tori as `torusFormalityColimit_isQuasiIso`, with `exteriorColimEquiv` identifying its
  source as an exterior power of a colimit, and reduced the remaining lattice-to-torus dictionary to
  a choice of bases by proving that any functorial family of integer matrices is a tower of tori
  (`torusCoverSystemOfMatrices`).
