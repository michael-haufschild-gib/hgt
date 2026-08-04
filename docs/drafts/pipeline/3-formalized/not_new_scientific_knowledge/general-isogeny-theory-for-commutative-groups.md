# General isogeny theory for commutative groups

Status: formalized.

## Statement

Mathlib contains no notion of isogeny at all.  This card records a general isogeny layer built
directly on mathlib's subgroup-index API, in a form that specialises to every classical instance.

**Definition.** A homomorphism `f : G →* H` of commutative groups is an *isogeny* when both
`ker f` and `coker f = H / im f` are finite.  Its *degree* is the positive rational

$$\deg f \;=\; \frac{\lvert\ker f\rvert}{\lvert\operatorname{coker} f\rvert}.$$

The two classical shapes are the two extremes: a surjective map with finite kernel (abelian
varieties, tori) has `deg f = |ker f|`, and an injective map with finite cokernel (lattices) has
`deg f = 1/[H : im f]`.  The reciprocal is forced, not chosen: lattices carry isogenies
contravariantly, and the reciprocal weight is exactly what makes the degree compose correctly
across the two conventions.

**Theorem (kernel–cokernel identity).** For composable homomorphisms of commutative groups,
unconditionally in `Nat.card`/`Subgroup.index` with the `0` conventions,

$$\lvert\ker(g\circ f)\rvert\cdot[H:\operatorname{im}f]\cdot[K:\operatorname{im}g]
 \;=\;\lvert\ker f\rvert\cdot\lvert\ker g\rvert\cdot[K:\operatorname{im}(g\circ f)].$$

This is the counting shadow of the six-term exact sequence
`1 → ker f → ker(gf) → ker g → coker f → coker(gf) → coker g → 1`, obtained without any
exactness machinery.  It gives closure of isogenies under composition and multiplicativity of
the degree.

**Theorem (complementary map, unconditional).** For *every* homomorphism `f : G →* H` of
commutative groups there is `f' : H →* G` with

$$f'\circ f=[n]_G,\qquad f\circ f'=[n]_H,\qquad n=\lvert\ker f\rvert\cdot\lvert\operatorname{coker}f\rvert .$$

No divisibility, torsion-freeness or finiteness hypothesis is required; only that a finite group
is killed by its own order.  For abelian varieties this is `f̂ ∘ f = [deg f]`; for lattices it is
the adjugate identity `adj(M)·M = det(M)·I`.

**Theorem (two-sided criterion).** If `[n]` is an isogeny on both `G` and `H` for that same `n`,
then `f` and `f'` are both isogenies.

**Isogeny-regular groups.** Call `G` *isogeny-regular* when `[n]` is an isogeny for every `n > 0`.
Regularity is transported along isogenies in *both* directions, so it is a property of the isogeny
class.  On isogeny-regular groups "isogenous" is an equivalence relation (reflexive and transitive
always; symmetry comes from the complementary map).  Finite groups, lattices and finitely
generated abelian groups are isogeny-regular.

**Theorem (isogeny invariant).** For an isogeny `f : G →* H` with `G` isogeny-regular,
`deg([n]_H) = deg([n]_G)` for all `n > 0`.  For abelian varieties that degree is `n^{2\dim}`, so
isogenous abelian varieties have equal dimension; for lattices it is `n^{-\mathrm{rank}}`, so
isogenous lattices have equal rank.  Both are instances of one statement.

**Lattices.** For a finite free `ℤ`-module `L`, an endomorphism is an isogeny exactly when its
determinant is nonzero, with `|ker| = 1`, `|coker| = |det|`, `deg = 1/|det|`.  Consequently
isogenous lattices have equal rank.

**Finitely generated abelian groups.** Every finitely generated abelian group is isogenous to a
lattice `Fin n → ℤ`, hence is isogeny-regular; and rank is a complete isogeny invariant — torsion
is invisible to isogeny.

**Group objects.** For commutative group objects in a cartesian monoidal category, postcomposition
is a homomorphism of point groups, and a morphism is a *pointwise isogeny* when every induced map
of point groups is an isogeny.  Pointwise isogenies compose, contain isomorphisms, and their
degree functions multiply.  This is the representable form of "isogeny of group schemes".

The whole development is stated multiplicatively and generated additively by `to_additive`, so
lattices and abelian varieties are served by the same theorems.

## Proof

The kernel–cokernel identity is a chain of index computations, each a mathlib lemma:

1. `ker(g∘f) = f⁻¹(ker g)` contains `ker f` with relative index `|im f ∩ ker g|`
   (`Subgroup.relIndex_ker`, `Subgroup.map_comap_eq`), giving
   `|ker(g∘f)| = |ker f| · |im f ∩ ker g|`.
2. `im(g∘f) = g(im f) ≤ im g` with `[im g : g(im f)] = [H : im f ⊔ ker g]`
   (`Subgroup.relIndex_map_map` with `K = ⊤`).
3. `[H : im f] = [im f ⊓ ker g : ker g]^{-1}`-style factorisation through `im f ⊔ ker g`, using
   the second isomorphism theorem in index form (`Subgroup.relIndex_sup_right`,
   `Subgroup.inf_relIndex_right`).
4. Relative Lagrange `|im f ⊓ ker g| · [im f ⊓ ker g : ker g] = |ker g|`.

Substituting 1, 3, 4 into 2 gives the identity with no cancellation, hence unconditionally.

The complementary map factors `f = ι ∘ π` through `G ⧸ ker f`.  Since `ker π = ker f` is killed by
`a = |ker f|`, the quotient property produces `π'` with `π' ∘ π = [a]`, and surjectivity of `π`
gives `π ∘ π' = [a]`.  Since `coker f` is killed by `b = |coker f|`, every `y^b` lies in `im ι`, and
injectivity of `ι` produces `ι'` with `ι ∘ ι' = [b]` and `ι' ∘ ι = [b]`.  Then `f' = π' ∘ ι'`
satisfies both identities with `n = ab`, because power maps commute with homomorphisms.

Regularity transport in both directions is the same index bookkeeping applied to
`[n]_H ∘ f = f ∘ [n]_G`.  Degree invariance follows by cancelling `deg f ≠ 0` in
`deg([n]_H)·deg f = deg f·deg([n]_G)`.

For lattices, `det ≠ 0` gives injectivity via `LinearMap.det_eq_zero_iff_ker_ne_bot`, and
`Submodule.natAbs_det_equiv` gives `|coker| = |det|`; the quotient by a submodule and by its
underlying additive subgroup are definitionally the same type.  Rank equality follows from degree
invariance at `n = 2` and injectivity of `k ↦ 2^k`.

For finitely generated abelian groups, the structure theorem splits `G ≃+ (Fin n →₀ ℤ) × F` with
`F` finite; projection off `F` is surjective with finite kernel, and `Finsupp.linearEquivFunOnFinite`
identifies the free factor with `Fin n → ℤ`.

## Lean

Modules (all under `formal/GaloisForLFunctions/HTGeometry/`):

| Module | Content |
|---|---|
| `IsogenyIndexArithmetic.lean` | `Subgroup.card_mul_relIndex`, `MonoidHom.card_ker_comp`, `MonoidHom.relIndex_range_comp`, `MonoidHom.card_ker_mul_index_range_comp`, `MonoidHom.index_range_comp_eq` |
| `IsogenyGeneral.lean` | `MonoidHom.kerCard`, `MonoidHom.cokerCard`, `IsIsogeny`, `IsIsogeny.comp`, `MonoidHom.isogenyDegree`, `MonoidHom.isogenyDegree_comp` |
| `IsogenyComplement.lean` | `MonoidHom.exists_complement`, `IsIsogeny.exists_complement`, `MonoidHom.exists_complement_isIsogeny` |
| `IsogenyRegular.lean` | `IsIsogenyRegular`, `IsIsogeny.isIsogenyRegular_target`, `IsIsogeny.isIsogenyRegular_source`, `IsIsogenous.refl/trans/symm`, `MonoidHom.isogenyDegree_pow_eq_of_isogeny` |
| `IsogenyKernel.lean` | `MonoidHom.kerCard_eq_one_iff`, `MonoidHom.cokerCard_eq_one_iff`, `QuotientGroup.isIsogeny_mk'`, `QuotientGroup.isogenyDegree_mk'`, `QuotientGroup.exists_mulEquiv_comp_mk'` |
| `IsogenyLattice.lean` | `LinearMap.isAddIsogeny_toAddMonoidHom_of_det_ne_zero`, `LinearMap.isogenyDegree_toAddMonoidHom_of_det_ne_zero`, `IsogenyLattice.isAddIsogenyRegular`, `IsogenyLattice.finrank_eq_of_isAddIsogeny` |
| `IsogenyFinitelyGenerated.lean` | `IsogenyFinitelyGenerated.exists_isAddIsogenous_fin_fun`, `isAddIsogenyRegular_of_fg`, `isAddIsogenous_iff_rank_eq` |
| `IsogenyGroupObject.lean` | `pointHom`, `IsPointwiseIsogeny`, `IsPointwiseIsogeny.comp`, `pointwiseDegree_comp` |

Every additive counterpart (`IsAddIsogeny`, `IsAddIsogenyRegular`, `IsAddIsogenous`, …) is
generated by `to_additive`.

`#print axioms` on `MonoidHom.card_ker_mul_index_range_comp`, `MonoidHom.isogenyDegree_comp`,
`MonoidHom.exists_complement`, `MonoidHom.exists_complement_isIsogeny`, `IsIsogenous.symm`,
`MonoidHom.isogenyDegree_pow_eq_of_isogeny`, `IsogenyLattice.finrank_eq_of_isAddIsogeny`,
`IsogenyFinitelyGenerated.isAddIsogenous_iff_rank_eq`, `pointwiseDegree_comp`, and
`QuotientGroup.exists_mulEquiv_comp_mk'` reports only `propext`, `Classical.choice`, `Quot.sound`.

## Relation to prior corpus work

The existing `Isogeny*` modules in `HTGeometry/` (`IsogenyKernelClosure`, `TorusIsogenyTail`,
`AbelianVarietyIsogenyTail`, `IsogenyTailMaurerCartanHolography`,
`MultiplicativeIsogenyTailHolography`, `NonautonomousIsogenyTransport`) concern stable tails of
iterated isogeny-like endomorphisms in differential and function-field settings.  They use the word
"isogeny" descriptively and do not define the notion; this layer supplies the notion itself and is
independent of them.

## Log
- 2026-08-04 — created directly in 3-formalized; all modules build, no `sorry`/`axiom`.
