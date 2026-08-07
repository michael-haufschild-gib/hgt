# CDGA-module derived tensor layer

- **Stage:** 3-formalized
- **Type:** INFRASTRUCTURE (Lean)
- **Statement:** Build, in Lean, the substitute for `E_∞`-algebra homotopy theory that the Deninger
  cards `deninger-character-shape-formality`, `deninger-derived-rank-quotient-universal-property`
  and `deninger-pro-stein-cylinder-analytic-leaf` need: differential graded modules over a
  commutative differential graded algebra, their quasi-isomorphisms, and the derived tensor product
  along a semi-free (relative cell) filtration.

## Why this and not `E_∞`

mathlib has neither `E_∞`-algebras nor CDGA homotopy theory.  Over a field of characteristic zero —
which is the only case the cards use, the coefficients being `ℝ` — commutative differential graded
algebras model rational homotopy theory, so a CDGA layer is a faithful substitute for the cards'
`E_∞` statements rather than a weakening of them.  The corpus already owns the algebra side:
`CDGAStructure`, `CDGAHom`, cocycles, cohomology, `IsQuasiIso`, the filtered colimit `colimCDGA` and
`colimHom_isQuasiIso`, the de Rham algebra of a torus, and the formality comparison
`torusFormalityHom`.  What was missing was the **module** side, which is what a derived tensor
product acts on.

## Landed (2026-08-07)

`formal/GaloisForLFunctions/HTGeometry/CDGAModule.lean`.

- `CDGAModuleStructure A M` — a family of `R`-modules in nonnegative degrees with a bilinear action
  of `A` adding degrees, associative over the product of `A`, and a differential squaring to zero
  and satisfying the Leibniz rule `d(x·m) = dx·m + (−1)^{|x|} x·dm`.
- `cocycles`, `coboundaries`, `cohomology` in each degree.
- `CDGAModuleHom` — degreewise linear, `A`-equivariant, commuting with the differential — with
  `cocyclesMap`, `cohomologyMap`, and `IsQuasiIso`.
- `CDGAModuleHom.id`, `CDGAModuleHom.comp`, `cohomologyMap_id`, `cohomologyMap_comp`,
  `isQuasiIso_id`, and **`IsQuasiIso.comp`**: quasi-isomorphisms of modules compose.
- `CDGAStructure.selfModule` — an algebra is a module over itself, with the same cocycles.

Axiom audit: `propext, Classical.choice, Quot.sound` (the self-module needs only
`propext, Quot.sound`).

## Direct sums (2026-08-07)

- `CDGAModuleStructure.prod P Q` — the degreewise direct sum of two differential graded modules;
  every axiom is componentwise.
- `mem_prod_cocycles` — a pair is a cocycle exactly when both components are; `prodFst`, `prodSnd`
  extract the components of a cocycle.
- `CDGAModuleHom.prodMap` — the direct sum of two morphisms.
- **`CDGAModuleHom.IsQuasiIso.prodMap`** — a direct sum of quasi-isomorphisms is a
  quasi-isomorphism.  Proved without any quotient-of-a-product identification: a pair is a
  coboundary exactly when both components are, so injectivity and surjectivity on cohomology are
  read off componentwise.

This is the first half of the cell attachment `M ⊕ A ⊗ V[−k]` — the underlying graded module of a
cell is a direct sum, and the theorem above is what makes attaching a cell to a quasi-isomorphism
harmless when the attaching differential is untwisted.

## The twisted cell attachment (2026-08-07)

- `CDGATwist P Q` — a **twisting cochain**: a degree-one map `τ : N n → M (n+1)`, additive and
  `R`-linear, linear over the algebra *up to the Koszul sign*
  (`τ (x · c) = (−1)^{|x|} x · τ c`), and anticommuting with the differentials
  (`d ∘ τ + τ ∘ d = 0`).  Those two conditions are exactly what the Leibniz rule and `d² = 0` of the
  attachment need — the sign condition is forced, not a convention.
- `CDGAModuleStructure.twisted P Q t` — the cell attached along `t`: the direct sum with
  `d (m, c) = (d m + τ c, d c)`.  `d² = 0` is `τ_d`, and the Leibniz rule reduces to `τ_act` after
  `act_add_right` and `smul_add`.
- `twistedIncl`, `twistedProj` — the inclusion of the base and the projection onto the cell, both
  morphisms of differential graded modules; `twistedProj_comp_incl`, `twistedIncl_injective`,
  `twistedProj_surjective`, `twistedProj_eq_zero_iff`: the attachment is an extension of the cell by
  the base, degreewise.

This is the card's "relative Sullivan algebra presented as a filtered union of finite cell stages",
one stage at a time, on the module side.

## Invariance: attaching a cell preserves quasi-isomorphisms (2026-08-07)

  `CDGAModuleHom.IsQuasiIso.twistedMap`

A quasi-isomorphism `φ` of bases which is compatible with the twists (`φ ∘ τ = τ'`) induces a
quasi-isomorphism `twistedMap t t' φ` of the cell attachments.  This is the invariance statement
that makes a derived tensor product well defined along a cell filtration.

**Proved by a direct chase, not by a long exact sequence.**  That is worth recording, because the
textbook route — build the connecting homomorphism of `0 → M → M ⊕_τ C → C → 0`, prove exactness at
three places, then apply the five lemma — is several times the work.  The chase is short because a
cocycle of an attachment is a pair `(m, c)` with `dm = −τc`, and each half of the hypothesis on the
base is used exactly once:

- *injectivity* (`twisted_mem_coboundaries`): if `(φm, c)` is the boundary of `(p, q)` then `c = dq`
  and `m − τq` is a cocycle of the base whose image is `dp`; by injectivity of `φ` on cohomology it
  is `dp₀`, and then `(m, c) = d(p₀, q)`.
- *surjectivity*: given a cocycle `(m', c)` downstairs, `τc` is a cocycle of the base whose image
  `τ'c = −dm'` is a boundary, so by injectivity again `τc = dq₀`, making `(−q₀, c)` a cocycle
  upstairs; its image differs from `(m', c)` by a cocycle of the base, which surjectivity of `φ` on
  cohomology corrects up to a boundary.

The `.symm` orientation of the sign lemmas (`eq_neg_iff_add_eq_zero`, `neg_eq_iff_add_eq_zero`) is
the only place the Koszul convention has to be tracked by hand.

Axiom audit: `propext, Classical.choice, Quot.sound`.

## Two out of three (2026-08-07)

`IsQuasiIso.of_comp_left` and `IsQuasiIso.of_comp_right`: in a composite of morphisms of
differential graded modules, any two of the three being quasi-isomorphisms forces the third.  With
`IsQuasiIso.comp` this makes "quasi-isomorphism" behave as a class of weak equivalences, which is
what a cell-by-cell induction needs — each stage of a filtration contributes one composite, and the
inductive step is exactly two out of three.

With `IsQuasiIso.prodMap` (finite direct sums), `IsQuasiIso.twistedMap` (one cell) and these, the
module-side toolkit for a finite relative cell induction is complete.  What is still missing is the
tensor product functor itself.

## The free cell (2026-08-07)

`formal/GaloisForLFunctions/HTGeometry/CDGAFreeCell.lean`.

`FreeCellCarrier X V k n := ∀ p : {a : ℕ // a + k = n}, X p.1 ⊗[R] V` — the free graded module on a
plain module `V` placed in degree `k`.  **Indexing by the subtype is the whole trick.**  The naive
`X (n − k)` forces truncated subtraction, and the degrees below `k` then need a dependent `if` whose
two branches have different types, so the additive structure has to be transported by hand.  Over
the subtype the index set is a subsingleton — empty below `k`, a singleton above — so the dependent
function type *is* the direct sum, and `Pi` already supplies `AddCommGroup` and `Module`.

`freeCellD A k n` is the differential of the algebra on the left factor, defined by matching on the
index: nothing below the bottom degree, `map (A.dₗ a) id` above it.  Matching on the *component* of
the subtype rather than on a projection is what lets Lean refine the target type, so no `Eq.mpr`
appears anywhere.  `freeCellD_add`, `freeCellD_smul`, and **`freeCellD_d`** — the differential
squares to zero, from `A.d_d` through `tensorMap_d_comp_d`.

Axiom audit: `propext, Quot.sound`.

## The action on the free cell (2026-08-07)

`freeCellAct A k h x f` multiplies on the left factor: at the component `a`, if `b ≤ a` it is
`map (A.mulₗ _ x) id` applied to the component `a − b` of the source, and otherwise zero — and when
it is zero the source component genuinely does not exist, since `a + k = b + n` with `a < b` forces
`n < k`.  `CDGAStructure.mul` takes the degree equation as an argument, so the positive branch needs
no type rewriting.  With `freeCellAct_of_le` and `freeCellAct_of_lt` as the two computation rules,
the four bilinearity axioms — `freeCellAct_add_left`, `freeCellAct_add_right`,
`freeCellAct_smul_left`, `freeCellAct_smul_right` — are each a `by_cases` and two rewrites.

Axiom audit: `propext, Quot.sound`.

## The free cell is a differential graded module (2026-08-07)

  `freeCellModule A V k : CDGAModuleStructure A (FreeCellCarrier X V k)`

complete, `sorry`-free, axioms `propext, Quot.sound`.  The two hard fields:

- `freeCellAct_assoc` — associativity, from `A.mul_assoc` after computing both sides with the
  flexible rule below;
- `freeCellD_act` — the Leibniz rule, from `A.d_mul`; the Koszul sign enters exactly once, in the
  identity `d ∘ (x ·) = (dx ·) + (−1)^{|x|} (x ·) ∘ d` of linear maps `X^i → X^c`, which is then
  tensored with the identity of `V` by `map_add_left` and `map_smul_left`.

**The technique that made the index arithmetic disappear**, and which is the reusable lesson: state
computation rules with the decomposition as a *hypothesis* rather than as a subtraction.

  `freeCellAct_apply_eq (e : b + i = c) : act x f ⟨c, _⟩ = map (A.mulₗ e x) id (f ⟨i, _⟩)`

is proved by `subst e` and then a helper that generalises the index over all `j` with `b + j = b + i`
and closes by `obtain rfl : j = i := by omega; rfl` — proof irrelevance does the rest.  Once that
rule exists, every case of every axiom is discharged by feeding `omega` the equation it needs; no
`rw` ever has to fire inside a dependent position, and no cast appears in the file.  The earlier
attempt to rewrite `b + i − b` to `i` after the fact fails exactly as predicted: `simp` cannot build
a type-correct motive.

## Arbitrary products (2026-08-07)

`CDGAModuleStructure.pi` — the product of a family of differential graded modules over an arbitrary
index type, degreewise, with `mem_pi_cocycles` and `piComp` extracting components; `piMap` the
product of a family of morphisms; and **`CDGAModuleHom.IsQuasiIso.piMap`** — a product of
quasi-isomorphisms is a quasi-isomorphism.

This subsumes `prodMap` and is the form the card's "finite direct sums of locally free coherent
sheaves" actually needs, since a finite product is a finite direct sum.  Both halves are read off
componentwise; the primitives are chosen with `choose`, which is the only place the axiom of choice
enters the layer.

## Next
2. The general tensor product `M ⊗_A N`, with `d(m ⊗ n) = dm ⊗ n + (−1)^a m ⊗ dn`.
3. Iterating the cell attachment along a filtration.  Each stage changes the carrier type, so the
   clean statement needs a dependent tower; two out of three is what makes the induction step
   itself trivial once the tower is written down.
3. The invariance theorem — a quasi-isomorphism in one variable stays one after tensoring with a
   semi-free module — which is what makes `⊗^L` well defined and is the algebraic half of the
   card's `(7)`.  The sheaf half is already closed
   (`deningerAcyclicOn_middle`, `deningerSections_surjective_of_acyclic`,
   `deningerHolomorphic_ext_eq_zero_punctured`).

## ⊗^L invariance proved

The layer is now closed on its main statement.  What was added:

1. `CDGATwist.τₗ` — the twisting cochain as a bundled linear map (CDGAModule.lean).
2. `tensorSigmaR` (CDGATensor.lean) — a degree-one family `σ : C n →ₗ N (n+1)` applied in the right
   factor of `M ⊗ −` with the Koszul sign of the left degree.  `tensorDR` is the case `σ = d`;
   `tensorDR_eq_tensorSigmaR` records that.
3. The three anticommutation laws for it, none of which needs a property of `σ` except the last:
   `tensorDL_tensorSigmaR_add`, `tensorDR_tensorSigmaR_add` (needs `d∘σ + σ∘d = 0`),
   `tensorD_tensorSigmaR_add`; plus `tensorSigmaR_tensorAct` (the Leibniz sign).
4. **`tensorTwistR P t : CDGATwist (tensorModule P Q) (tensorModule P Qc)`** — the twist induced on
   the tensor product by a twist on the right factor.  All four axioms discharged.
5. `tensorProdRight_tensorDL` / `tensorProdRight_tensorDR` / `tensorProdRight_tensorAct` — the
   distributivity comparison transports each structure map.  The middle one is the identity that
   *names* `tensorTwistR`: the off-diagonal part of the differential of a cell attachment becomes,
   after distributing, exactly the tensored twisting cochain.
6. **`tensorProdRightHom P Q Qc t`** — the comparison as a map of differential graded modules,
   together with `tensorProdRightHom_isQuasiIso`.  So: *tensoring commutes with attaching a cell.*

The invariance statement then needed a strictly stronger notion of quasi-isomorphism than the one
already in the layer, because `IsQuasiIso`'s degree-`n` component is `H^{n+1}`: the module of
cocycles in degree zero is not covered.  With a fixed cell that gap is invisible (the existing
`IsQuasiIso.twistedMap` never needs it), but when the cell also changes the chase reaches a
degree-zero cocycle of the cell and has to lift it.  Hence a new file, `CDGACellInvariance.lean`:

7. **`IsQuasiIsoFull`** = bijective on `cocycles 0` and on every `cohomology n`; `of_bijective`,
   `comp`, `of_comp_left`, `of_comp_right`, and `hom_ext`.
8. **`twistedMap₂`** — the comparison of two cell attachments moving *both* base and cell.
9. **`IsQuasiIsoFull.twistedMap₂`** — it is a full quasi-isomorphism as soon as both halves are.
   Proved by a direct chase in three parts (degree-zero cocycles, cohomology injectivity,
   cohomology surjectivity), not by a long exact sequence.  The one lemma that carries the new
   degree is `exists_twist_eq_of_cocycle`: a cocycle of the cell downstairs is, modulo a coboundary
   of the base, the twist of a cocycle of the cell upstairs — in positive degree that is
   surjectivity on cohomology, in degree zero surjectivity on cocycles.

Finally `CDGADerivedTensor.lean`:

10. `tensorMapLeft_tensorSigmaR`, `tensorTwistR_compat`, `tensorProdRightHom_naturality` — the
    distributivity comparison is natural in the tensored factor.
11. **`tensorMapLeft_twisted_isQuasiIsoFull`** — tensoring against a cell attachment preserves full
    quasi-isomorphisms whenever it does against the base and against the cell.
12. **`tensorMapLeft_tower_isQuasiIsoFull`** — the same for every stage of a tower of cell
    attachments.  This is the statement `⊗^L` names: for semi-free `S`, the functor `− ⊗ S`
    depends on its source only through cohomology.

All unconditional; axioms `propext, Classical.choice, Quot.sound`.

Note on the shape of the proof: the tensored objects `P ⊗ S_i` are *not* literally a tower —
`towerCarrier` is a strict recursion producing types, and `P ⊗ (S_i ⊕ C_i)` is only isomorphic to
`(P ⊗ S_i) ⊕ (P ⊗ C_i)`.  So `tower_isQuasiIso` does not apply directly; the induction is run again
in the tensored setting, with `tensorProdRightHom` conjugating each stage.  That is also why
two-out-of-three for `IsQuasiIsoFull` was needed.

## Next

The cell-attachment machinery is complete.  What the layer still lacks, in order of usefulness:

* Functoriality of `tensorModule` in the *right* variable, and the symmetric invariance statement.
  The left-variable functor `tensorMapLeft` exists; `tensorMapRight` does not, and the Koszul sign
  makes it a genuinely different map (it is not obtained from the left one by `tensorMapComm`).
* A construction of semi-free resolutions: given `Q`, a tower with free cells and a full
  quasi-isomorphism to `Q`.  This is what makes the invariance theorem apply to an arbitrary module
  rather than to a supplied tower.
* `FreeCellCarrier` cells are already built (`freeCellModule`); connecting them to `towerMod`
  requires only choosing the twists, which is the resolution construction above.

## Two-variable functoriality

`tensorMapRight P ψ : tensorModule P Q → tensorModule P Q'` is now built, together with
`tensorMapLeft_comp_tensorMapRight` (the two functorialities commute) and `tensorMap φ ψ` with
`tensorMap_toFun`.  Contrary to what the previous note guessed, **no Koszul sign appears in the
right-variable functor**: a morphism has degree zero, so the sign `(-1)^a` carried by the right
half-differential is the same before and after, and `tensorMapRight` is defined by
`map id (ψ.mapₗ p.1.2)` with no correction.  `CDGAModuleHom.hom_ext` moved to `CDGAModule.lean`
where it belongs.

What is still absent is the mirror of the invariance theorem — semi-free on the *left*, invariance
in the right variable.  That needs `tensorProdLeft` (distributivity in the first variable) and the
twist `tensorTwistL`, which carries *no* sign because `tensorDL` carries none; it is a direct mirror
of the work above and no new idea is involved.

## The mirror: invariance in the right variable

`CDGATensorLeft.lean` is the left-variable mirror, and the layer is now symmetric.

* `tensorSigmaL` — a degree-one family applied in the **left** factor.  It carries **no** Koszul
  sign, because `tensorDL` carries none.  The sign does not disappear, it relocates: it reappears
  as the sign in the family's compatibility with the algebra action (`tensorSigmaL_tensorAct`,
  which is exactly `CDGATwist.τ_act`), and the anticommutation with `tensorDR`
  (`tensorDR_tensorSigmaL_add`) becomes free of any hypothesis on the family, since the two terms
  differ only by the shift of the left degree by one.  Compare the right-hand theory, where it was
  the anticommutation with `tensorDL` that was free.
* `tensorTwistL t Q : CDGATwist (tensorModule P Q) (tensorModule Pc Q)`, all four axioms.
* `tensorProdLeft` (from mathlib's `TensorProduct.prodLeft`), `tensorProdLeft_bijective`, the four
  transport lemmas, and `tensorProdLeftHom` — *tensoring commutes with attaching a cell to the left
  factor*.
* `tensorMapRight_tensorSigmaL`, `tensorTwistL_compat`, `tensorProdLeftHom_naturality`,
  **`tensorMapRight_twisted_isQuasiIsoFull`** and **`tensorMapRight_tower_isQuasiIsoFull`**.

One asymmetry worth recording, because it is invisible until the proof is written: the case split in
`tensorSigmaL_tensorAct` needs **three** branches, not two.  In left degree `a' + 1` with the acting
element of degree `b`, the hypothesis `¬ b ≤ a'` does not give `¬ b ≤ a' + 1` — the boundary case
`b = a' + 1` is real, and there the right-hand side vanishes not because the action is out of range
but because `tensorSigmaL` is zero in left degree `0`.  The right-variable proof never meets this,
because there the family shifts the *right* index while the action reads the *left* one.

All unconditional; axioms `propext, Classical.choice, Quot.sound`.

## Next

* A construction of semi-free resolutions: given `Q`, a tower with free cells and a full
  quasi-isomorphism to `Q`.  This is what makes the two invariance theorems apply to an arbitrary
  module rather than to a supplied tower.  `freeCellModule` already builds the cells; what is
  missing is the choice of twists that kills cohomology, and that is a genuine construction, not
  bookkeeping.
* With a resolution in hand, `− ⊗^L −` can be defined and shown independent of the resolution, by
  applying the two invariance theorems in turn.

## The tensor product over the algebra

A gap the earlier entries did not name: `tensorModule P Q` is the tensor product over the **ground
ring**, with the algebra acting through the left factor.  That is the right object for `− ⊗_R −`,
but the card's `(5)` — derived base change — needs `− ⊗_A −`, and so does any statement in which the
free cells `freeCellModule A V k = A[−k] ⊗ V` are supposed to be cheap: over `R` they are not.

`CDGATensorSingle.lean` and `CDGARelTensor.lean` supply it.

* `tensorSingle p z` — the element of a graded tensor product supported at a single bidegree.  The
  carrier is a product over the finitely many decompositions of the total degree, so this is
  available, and each of the three structure maps sends such an element to *one* other such element
  (`tensorDL_tensorSingle`, `tensorDR_tensorSingle`, `tensorAct_tensorSingle`,
  `tensorD_tensorSingle`).  That is what makes single-bidegree elements the right generators for
  describing subobjects.
* `relTensorRelator hα hβ hn hn' x m v` — the relator `(−1)^{|x||m|} (x·m) ⊗ v − m ⊗ (x·v)`, a left
  module being a right module through `m · x = (−1)^{|x||m|} x · m`.  The two target degrees are
  supplied as separate parameters, which is what lets a *differentiated* factor be placed where the
  Leibniz rule puts it — without that the statement cannot even be typed, because `c + 1 + a` and
  `c + a + 1` are different terms and hence different types.

The two stability computations are the content:

* **`tensorAct_relTensorRelator`** — the action carries a relator to a *single* relator, with no
  sign: `y · rel(x, m, v) = rel(x, y·m, v)`.  The sign of graded commutativity in the algebra
  (`(−1)^{|x||y|}`, from moving `x` past `y`) cancels exactly against the change in the relator's own
  sign when `m` is replaced by `y·m`.
* **`tensorD_relTensorRelator`** — the differential carries a relator to a combination of three,
  `d(rel(x,m,v)) = (−1)^{|m|} rel(dx,m,v) + rel(x,dm,v) + (−1)^{|m|+|x|} rel(x,m,dv)`.  Both sides
  expand to the same six single-bidegree terms; the three signs are forced.

Hence `relTensorRel` is stable, and:

* **`relTensorModule P Q`** — the tensor product over the algebra, a differential graded module.
* `relTensorProj` — the projection from the tensor product over the ground ring, with
  `relTensorProj_relator` recording that the defining relation does hold downstairs.
* **`relTensorMapLeft`** — functoriality in the left variable, with `relTensorProj_naturality`.

All unconditional; axioms `propext, Classical.choice, Quot.sound`.

## Next

The invariance theorems proved earlier are for `⊗_R` and do **not** transfer to `⊗_A` by formal
nonsense — the quotient is not exact.  What makes `⊗_A` computable is the free cell:

1. `relTensorModule P (CDGAStructure.selfModule A) ≅ P` — the unitor.  This is the base case, and
   it is where the relation does real work: every `m ⊗ x` is rewritten to `(±x·m) ⊗ 1`.
2. `relTensorModule P (freeCellModule A V k) ≅ P[−k] ⊗_R V` — the cell case, which follows from the
   unitor and the fact that `freeCellModule A V k` is `A[−k] ⊗_R V`.
3. With 1 and 2, the `hcell` hypothesis of `tensorMapLeft_tower_isQuasiIsoFull` becomes discharegable
   for free cells, and the tower theorem becomes a statement about arbitrary semi-free modules
   rather than about a supplied tower.

## The algebra has no unit — and now it can have one

A structural fact the layer had not recorded, and which blocks the plan above as stated:
**`CDGAStructure` has no unit.**  Its fields are the product, the differential, bilinearity,
associativity, graded commutativity and Leibniz — nothing else.  It is a commutative differential
graded algebra in the *non-unital* sense, which is all the formality comparison ever needed.

That matters here, because without a unit `M ⊗_A A ≅ M` is simply false, and `freeCellModule A V k`
is free only in the non-unital sense.  So step 1 of the previous plan is not a lemma to be proved,
it is a hypothesis to be supplied.

`CDGAUnital.lean` supplies it, additively — nothing already built changes:

* `CDGAUnit A` — a degree-zero element with `one_mul` and `d_one`.  `mul_one` is then a theorem, by
  graded commutativity: the sign is `(−1)^{b·0} = 1`.
* `CDGAModuleUnital u P` — the action of the unit is the identity.  This is genuinely extra data on
  a module, not a consequence.
* `selfModule_unital`, `twisted_unital`, `tensorModule_unital`, `prod_unital` — unitality is
  inherited by the algebra over itself, by a cell attachment, by the tensor product (through the
  left factor) and by a direct sum.

Also landed, in `CDGATensorSingle.lean`: **`tensorIndexEquiv`** and the `Fintype` instance it gives.
The decompositions of a total degree `n` are indexed by their first component, so they form a finite
type equivalent to `Fin (n+1)`.  This is what allows a *sum over all bidegrees* — needed for any map
out of a graded tensor product, the unitor included.

Axioms: `propext, Quot.sound` for the unit lemmas and the index equivalence,
`propext, Classical.choice, Quot.sound` for `tensorModule_unital`.

## Next

With `CDGAUnit`, `CDGAModuleUnital` and the finite bidegree index in place, the unitor is now
writable: `unitorTo` sums the right action `m ⊗ x ↦ (−1)^{|x||m|} x · m` over the finitely many
bidegrees, kills the relators by construction, and is inverse to `m ↦ m ⊗ 1` exactly when the
action is unital.  After that the free-cell computation and the discharge of `hcell` follow as
described above.

## The unitor

`CDGAUnitor.lean` closes the base case: **a module tensored over the algebra with the algebra is the
module**, as a full quasi-isomorphism, whenever the algebra has a unit acting as the identity.

* `rightActₗ P h : M a ⊗ X c → M n` — the right action `m · x = (−1)^{|x||m|} x · m` on one
  bidegree, built by `TensorProduct.lift` from a bilinear map.
* `unitorToₗ P n` — its **sum over all bidegrees**, which is exactly what `tensorIndexEquiv`'s
  `Fintype` instance makes possible.
* `unitorToₗ_relTensorRelator` — the right action kills the relators.  Worth naming why: on the
  relator of `x, m, v` the two terms differ by moving `v` past `x` inside the algebra
  (sign `(−1)^{|v||x|}`) and by the change in the relator's own sign, and those two signs are equal
  — the exponents `|x||m| + |v|(|x|+|m|) + |v||x|` and `(|x|+|v|)|m|` differ by `2|v||x|`.
* `relUnitorTo` — hence a map out of the quotient, and `relUnitorEquiv` — a **degreewise linear
  isomorphism**, with `unitorFromₗ u n : m ↦ m ⊗ 1` as the inverse.  The non-trivial half is
  `relUnitor_single`: `m ⊗ x` is rewritten to `(±x·m) ⊗ 1` *by the relation itself*, with `v := 1`
  and `x · 1 = x` from `CDGAUnit.mul_one`.
* `unitorToₗ_tensorAct` and `unitorToₗ_tensorD` — the unitor is equivariant and a chain map.  The
  first is the same sign cancellation as in `tensorAct_relTensorRelator`; the second is Leibniz,
  with the two terms picking up `(−1)^{|x||m|}` and `(−1)^{|x||m|+|x|}`.
* **`relUnitorHom`** and **`relUnitorHom_isQuasiIsoFull`**.

A note on a constraint discovered while writing this: `TensorCarrier` is universe-monomorphic in its
two arguments, so the unitor is stated with the algebra and the module in the *same* universe.  That
is no loss in practice — the cards' algebras and modules are both over `ℝ` — but it is why
`CDGAUnitor.lean` declares `X : ℕ → Type w` rather than `Type v`.

Axioms: `propext, Classical.choice, Quot.sound`.

## Next

The remaining step of the free-cell computation is
`relTensorModule P (freeCellModule A V k) ≅ P[−k] ⊗_R V`.  With the unitor in hand this is the
statement that `freeCellModule A V k` *is* `A[−k] ⊗_R V` as a module over the algebra, so the
relative tensor product distributes: `M ⊗_A (A[−k] ⊗_R V) ≅ (M ⊗_A A)[−k] ⊗_R V`.  After it, the
`hcell` hypothesis of `tensorMapLeft_tower_isQuasiIsoFull` is dischargeable for free cells and the
tower theorem applies to arbitrary semi-free modules.

## Invariance of `− ⊗_A A`

`CDGARelTensorUnit.lean`.  The unitor is natural in the module (`unitorToₗ_tensorMapLeft`,
`relUnitorHom_naturality`), so the square

```
    M ⊗_A A  ──unitor──▶  M
       │                  │
   φ ⊗ A                  φ
       ▼                  ▼
   M' ⊗_A A ──unitor──▶  M'
```

commutes, and both horizontals are full quasi-isomorphisms.  Two out of three then gives both
directions:

* **`relTensorMapLeft_selfModule_isQuasiIsoFull`** — `− ⊗_A A` preserves full quasi-isomorphisms;
* **`isQuasiIsoFull_of_relTensorMapLeft_selfModule`** — and reflects them.

This is the base case of invariance for the tensor product over the algebra, and the first place
where the whole chain — relators, quotient, unit, unitor — is used end to end.

Axioms: `propext, Classical.choice, Quot.sound`.

## The degree shift

`CDGAShift.lean`.  Shifting a module up by `k` places its degree `a` in degree `a + k` and puts
nothing below `k`.  Indexing by the subtype `{a // a + k = n}` — the same device `FreeCellCarrier`
already used — keeps truncated subtraction out of every dependent position, and the component below
the shift is an *empty product*, so the bottom of the complex is trivial with no separate case in
the carrier.

* `ShiftCarrier`, `shiftD`, `shiftAct` and their computation rules, `shiftD_d`, `shiftAct_assoc`,
  `shiftD_act`, and **`shiftModule P k`**.
* **`shiftMap φ k`** — the shift of a morphism.
* `shiftIndexUnique`, `shiftIndex_isEmpty`, `shiftCarrier_subsingleton`, **`shiftEval`** — above the
  shift the index of a degree is unique and the component *is* the original module; below it, the
  component is trivial.
* **`freeCellCarrier_eq_shift`** — the free cell is literally the shift of the algebra tensored with
  the coefficient module: `FreeCellCarrier X V k = ShiftCarrier (fun a => X a ⊗ V) k`, by `rfl`.
  This is what makes the shift the right tool for the cell computation rather than a detour.

Axioms: `propext, Quot.sound` throughout — no choice anywhere in this file.

## Next, and the obstruction in it

The remaining statement is that `shiftMap φ k` is a full quasi-isomorphism when `φ` is.  It is true,
and the shape of the proof is clear — three regimes, matched by the three parts of
`IsQuasiIsoFull`:

* `n + 1 < k`: everything is trivial, both cohomologies vanish;
* `n + 1 = k`: `H` of the shift is `cocycles 0` of the original, matched by the degree-zero half of
  `IsQuasiIsoFull` — which is exactly why that half had to exist;
* `n + 1 > k`: `H^n` of the shift is `H^{n-k}` of the original.

The obstruction is not mathematical but syntactic, and worth recording because it will recur:
`shiftD P k (j + k)` lands in `ShiftCarrier M k (j + k + 1)`, while the statement wants
`ShiftCarrier M k ((j + 1) + k)`.  `j + k + 1` and `j + 1 + k` are propositionally but **not**
definitionally equal, so `shiftEval` cannot be applied on the nose and a transport is needed.  The
fix that generalises is the one already used for `relTensorRelator`: state the comparison with the
target degree as a *parameter* plus an equation, rather than as a computed expression.

## The shift preserves quasi-isomorphisms

`CDGAShiftQuasiIso.lean`.  The obstruction recorded above is resolved exactly as predicted — by
carrying the target degree as a parameter with an equation:

* **`shiftEvalAt k j n (h : j + k = n)`** — the component of a shift above the shift, at an
  *arbitrary* witness of the degree.  With this, `shiftEvalAt_shiftD` states
  `shiftEvalAt k (j+1) (n+1) (shiftD f) = P.d j (shiftEvalAt k j n f)` with no cast: the target
  degree is the literal `n + 1`, not the computed `j + k + 1`.  Likewise `shiftEvalAt_shiftAct` and
  `shiftEvalAt_shiftMap`.
* `shiftD_eq_zero_iff`, **`shiftCocyclesEquiv`** and its naturality — above the shift the cocycles
  are the cocycles.
* `shiftCocyclesEquiv_mem_coboundaries`, **`shiftCohomologyEquiv`** and its naturality — and the
  cohomology is the cohomology.
* `shiftCoboundaries_eq_bot`, **`shiftBottomCohomologyEquiv`** — at the bottom of the shift there
  are no coboundaries, so the cohomology there is the module of degree-zero *cocycles*.
* **`shiftMap_isQuasiIsoFull`** — the shift preserves full quasi-isomorphisms.

The proof splits into three regimes and they are matched, one each, by the three parts of
`IsQuasiIsoFull`:

| regime | cohomology of the shift | matched by |
|---|---|---|
| `n + 1 < k` | trivial | subsingleton |
| `n + 1 = k` | `cocycles 0` of the original | the degree-zero half |
| `n + 1 > k` | `H^{n-k}` of the original | `IsQuasiIso` |

This is the sharpest justification yet for having introduced `IsQuasiIsoFull` rather than working
with `IsQuasiIso`: **the shift moves what was degree-zero cocycle data into ordinary cohomology**, so
a notion of quasi-isomorphism blind to degree zero is not stable under shifting.  With `IsQuasiIso`
alone the middle regime would be unprovable.

Axioms: `propext, Classical.choice, Quot.sound` (`shiftCocyclesEquiv` needs only
`propext, Quot.sound`).

## Free coefficients, and the free cell functor

`CDGATensorConst.lean` and `CDGAFreeCoefficients.lean`.

* **`tensorConstModule P V`** — tensoring degreewise with a fixed `R`-module.  Neither the grading
  nor the roles change: differential and action work on the left factor, the second is carried
  along.  With `tensorConstMap` (functoriality in the module) and `tensorConstVMap` (functoriality
  in the coefficients).
* **`freeCellModule_eq`** — `freeCellModule A V k = shiftModule (tensorConstModule (selfModule A) V) k`,
  by `rfl`.  The free cell is exactly a shift of a constant tensor; nothing else is going on in it.
* **`tensorConstPiHom`** — tensoring with `ι → R` *is* the product of `ι` copies, as a map of
  differential graded modules, degreewise bijective.
* **`CDGAModuleHom.IsQuasiIsoFull.piMap`** — a product of full quasi-isomorphisms is one; the
  degree-zero half is read off componentwise from `mem_pi_cocycles`.
* **`tensorConstMap_isQuasiIsoFull`** — **free coefficients preserve full quasi-isomorphisms.**  A
  basis identifies `V` with `ι → R`, the comparison is natural, and two out of three does the rest.
* **`freeCellFunctor_isQuasiIsoFull`** — and so does the free cell functor `P ↦ (P ⊗ V)[−k]`, by
  composing with `shiftMap_isQuasiIsoFull`.

Axioms: `propext, Classical.choice, Quot.sound`; `tensorConstModule`, `tensorConstMap`,
`tensorConstVMap` and `freeCellModule_eq` need only `propext, Quot.sound`.

A universe note, of the same kind as the one recorded for the unitor: `IsQuasiIsoFull` compares two
modules in a *single* universe, and `ι → R` lives in `max u w`, so `CDGAFreeCoefficients.lean`
declares the ground ring in the same universe as the modules.  For the cards — everything over `ℝ` —
this is no restriction.

## Next

What is still missing to discharge `hcell` of `tensorMapLeft_tower_isQuasiIsoFull` outright is the
identification of the *cell as a tensor factor*: for the cell `constCell V k` — the module `V` placed
in degree `k` with zero action and zero differential, which is a legitimate `CDGAModuleStructure` —
one needs

  `tensorModule P (constCell V k) ≅ shiftModule (tensorConstModule P V) k`.

Both sides are `M^{n-k} ⊗ V` in degree `n`; the content is only the bookkeeping of the bidegree
index against the one-degree concentration.  With that, `freeCellFunctor_isQuasiIsoFull` *is*
`hcell`, and the tower theorem applies to any tower built from cells concentrated in single degrees
with free coefficients — which is the definition of semi-free over the ground ring.

Note that the `A`-free cells (`freeCellModule`) are the right cells for `⊗_A`, not for `⊗_R`: over
the ground ring, `M ⊗_R A[−k] ⊗ V` involves `H(M ⊗_R A)`, not `H(M)`.  The two programmes need
different cells, and both cell types are now built.

## The single-degree cell

`CDGAConstCell.lean`.  The cells of a tower semi-free over the *ground ring* are modules
concentrated in one degree with zero differential **and zero action** — and that really is a
legitimate `CDGAModuleStructure`, because every axiom becomes an identity between zeros, the Leibniz
rule included.  Indexing the concentration by `PLift (n = k)` makes the wrong-degree component an
empty product, so it is trivial with no separate case, exactly as in `ShiftCarrier`.

* `ConstCellCarrier`, **`constCellModule A V k`**, `constCellCarrier_subsingleton`.
* `constCellEvalEquiv` — in its own degree the cell is the coefficient module; `constCellConst` is
  the embedding the other way.

Axioms: `propext, Quot.sound`.

## Next

One comparison remains before `hcell` is discharged outright:

  `tensorModule P (constCellModule A V k) ≃ shiftModule (tensorConstModule P V) k`,

degreewise and naturally in `P`.  Both sides are `M^{n−k} ⊗ V` in degree `n`.  The content is only
that the bidegree components with second index `≠ k` are trivial — which follows from
`constCellCarrier_subsingleton` and the fact that a tensor product with a trivial module is trivial
— so the product over all bidegrees collapses to the product over `{a // a + k = n}`.  With that
bijection and `freeCellFunctor_isQuasiIsoFull`, two out of three gives
`(tensorMapLeft φ (constCellModule A V k)).IsQuasiIsoFull`, which is exactly the `hcell` hypothesis
of `tensorMapLeft_tower_isQuasiIsoFull`.

## `hcell` is discharged — the tower theorem is now unconditional for ground-ring semi-free towers

`CDGAConstCellTensor.lean` closes the loop.

* `tensorProduct_subsingleton_right` — a tensor product with a trivial module is trivial.
* **`constCellTensorEquiv`** — `TensorCarrier M (ConstCellCarrier V k) n ≃ₗ ShiftCarrier (M · ⊗ V) k n`.
  All bidegree components with second index `≠ k` are trivial, so the product over bidegrees
  collapses to the product over `{a // a + k = n}`.
* `tensorDR_constCell` — **the right half-differential vanishes identically** on a tensor product
  with a single-degree cell, because the cell has zero differential.  This is the whole reason the
  graded comparison upgrades to a map of *differential* graded modules: only `tensorDL` survives,
  and that is exactly `shiftD` of the constant tensor.
* **`constCellTensorHom`** and `constCellTensorHom_bijective`, `constCellTensorHom_naturality`.
* **`tensorMapLeft_constCell_isQuasiIsoFull`** — tensoring with a single-degree cell with free
  coefficients preserves full quasi-isomorphisms.  **This is the `hcell` hypothesis of
  `tensorMapLeft_tower_isQuasiIsoFull`.**
* **`tensorMapLeft_constCellTower_isQuasiIsoFull`** — hence, for a tower whose cells are modules
  concentrated in single degrees with free coefficients of finite rank, the derived tensor product
  is invariant given only invariance at the base.  A tower of such cells is what *semi-free over the
  ground ring* means.

All unconditional; axioms `propext, Classical.choice, Quot.sound` (the comparison itself needs only
`propext, Quot.sound`).

A note on process, recorded because it cost time: `⟨(c', k), by omega⟩` inside a `show` whose
expected type already fixes the proof term makes `omega` fail with "no goals to be solved" — the
proof field is unified rather than elaborated.  Naming the index proof with a `have` first avoids
it, and is what the `map_d` field does.

## The cell-attachment machinery over the quotient

`CDGARelTensorTwist.lean` — the `⊗_A` mirror of `tensorProdRightHom`, up to the comparison itself.

* `tensorSigmaR_tensorSingle` — the right-factor family on a single-bidegree element.
* **`tensorSigmaR_relTensorRelator`** — the induced twist carries a relator to a *scalar multiple of
  a relator*: `tensorSigmaR (t.τₗ) (rel(x,m,v)) = (−1)^{|m|+|x|} rel(x, m, τ v)`.  The reason is
  exact: the sign the twisting cochain picks up against the algebra (`CDGATwist.τ_act`) is precisely
  the sign the relator changes by when `v` is replaced by `τ v`, one degree up.
* `relTensorRel_tensorSigmaR` — hence the relations are stable, and
* **`relTensorTwistR P Q Qc t : CDGATwist (relTensorModule P Q) (relTensorModule P Qc)`** — the twist
  of a cell attachment **descends to the tensor product over the algebra**, with all four axioms
  inherited from `tensorTwistR` by `Quotient.inductionOn`.
* `tensorProdRight_tensorSingle` and **`tensorProdRight_relTensorRelator`** — a relator of a cell
  attachment **splits into the pair of relators of the two factors**.  This works because the action
  on `twisted Q Qc t` is componentwise — the twist enters only the differential — so nothing mixes,
  and it is the computation the comparison isomorphism will rest on.

Axioms: `propext, Classical.choice, Quot.sound`; the two splitting lemmas need only
`propext, Quot.sound`.

## Next

`relTensorProdRightHom`: the descended comparison

  `relTensorModule P (twisted Q Qc t) ≅ twisted (relTensorModule P Q) (relTensorModule P Qc)
     (relTensorTwistR P Q Qc t)`.

The map is `Submodule.liftQ` of `(mk × mk) ∘ tensorProdRight`; surjectivity is immediate.
Injectivity is where `tensorProdRight_relTensorRelator` is used, and the argument is short but worth
recording so it is not rediscovered: a relator is *linear in* `v`, so `rel(x,m,0) = 0`, hence
`tensorProdRight (rel(x,m,(v₁,0))) = (rel(x,m,v₁), 0)`.  The image of the relator submodule
therefore contains `rel₁ × 0` and `0 × rel₂` separately, so it is the full product `rel₁ × rel₂` and
not merely the diagonal-like span the generators first suggest.  With that, the quotient of the
product is the product of the quotients and the comparison is bijective.

## `relTensorProdRightHom` — the `⊗_A` mirror is complete

`CDGARelTensorTwist.lean` now carries the comparison itself.

* `relTensorRelator_zero` — a relator is linear in its cell argument, so it vanishes there.
* `mem_relTensorRel_of_fst`, `mem_relTensorRel_of_snd` — the preimage of a relator of *either*
  factor is a relator of the cell attachment, obtained by padding the cell argument with a zero in
  the other slot.
* **`relTensorRel_of_prodRight`** — hence a class of the cell attachment is trivial exactly when
  both of its components are.  This is the step where the naive guess is wrong: the generators of
  the relator submodule of `P ⊗ (Q ⊕ C)` map to *pairs* `(rel(x,m,v₁), rel(x,m,v₂))`, and the span
  of those looks smaller than `rel₁ × rel₂`.  It is not, because a relator is linear in `v`, so
  `rel(x,m,(v₁,0)) ↦ (rel(x,m,v₁), 0)` and the two factors are hit separately.
* `relTensorProdRightMap`, `relTensorProdRightMap_ker`, **`relTensorProdRightHom`** — the descended
  comparison, as a map of differential graded modules, with `relTensorProdRightHom_bijective` and
  **`relTensorProdRightHom_isQuasiIsoFull`**.

So **tensoring over the algebra commutes with attaching a cell**, and the `⊗_A` side now has the
same three pieces the `⊗_R` side has: the twist (`relTensorTwistR`), the comparison
(`relTensorProdRightHom`), and the base case (`relTensorMapLeft_selfModule_isQuasiIsoFull`).

Axioms: `propext, Classical.choice, Quot.sound`; the splitting and preimage lemmas need only
`propext, Quot.sound`.

## Next

The `⊗_A` tower theorem: with `relTensorProdRightHom` in hand, the argument that produced
`tensorMapLeft_tower_isQuasiIsoFull` runs again verbatim over the quotient — conjugate the
comparison, apply `IsQuasiIsoFull.twistedMap₂`, then two out of three, and induct up the tower.
The one new ingredient is naturality of `relTensorProdRightHom` in the tensored factor, which is the
`⊗_A` analogue of `tensorProdRightHom_naturality` and follows from `relTensorMapLeft`'s definition
on representatives.

## The `⊗_A` tower theorem

`CDGARelTensorTower.lean`.

* `relTensorTwistR_compat` — the comparison intertwines the descended twists (from
  `tensorMapLeft_tensorSigmaR`, on representatives).
* **`relTensorProdRightHom_naturality`** — the comparison is natural in the tensored factor.  It is
  obtained by applying `mk × mk` to `tensorProdRightHom_naturality`: the whole content is already
  upstairs, and descent adds nothing.
* **`relTensorMapLeft_twisted_isQuasiIsoFull`** — tensoring over the algebra against a cell
  attachment preserves full quasi-isomorphisms.
* **`relTensorMapLeft_tower_isQuasiIsoFull`** — and against a whole tower.

Axioms: `propext, Classical.choice, Quot.sound`.

Both invariance theorems now exist in parallel, with the same shape and the same three inputs:

| | `⊗_R` | `⊗_A` |
|---|---|---|
| twist | `tensorTwistR` | `relTensorTwistR` |
| comparison | `tensorProdRightHom` | `relTensorProdRightHom` |
| one cell | `tensorMapLeft_twisted_isQuasiIsoFull` | `relTensorMapLeft_twisted_isQuasiIsoFull` |
| tower | `tensorMapLeft_tower_isQuasiIsoFull` | `relTensorMapLeft_tower_isQuasiIsoFull` |
| cells discharged | `constCellModule` (done) | `freeCellModule` (open) |

## Next

The remaining asymmetry is the last row.  For `⊗_R` the `hcell` hypothesis is discharged outright
(`tensorMapLeft_constCell_isQuasiIsoFull`).  For `⊗_A` the natural cells are the `A`-free ones, and
discharging `hcell` for them needs the free-cell computation

  `relTensorModule P (freeCellModule A V k) ≅ shiftModule (tensorConstModule P V) k`,

which by `freeCellModule_eq` splits into two statements that are each worth having on their own:

1. `⊗_A` commutes with the degree shift: `M ⊗_A (N[−k]) ≅ (M ⊗_A N)[−k]`;
2. `⊗_A` commutes with a constant tensor: `M ⊗_A (N ⊗_R V) ≅ (M ⊗_A N) ⊗_R V`, for which the finite
   bidegree index (`tensorIndexEquiv`) is what makes the `Pi`-`⊗` exchange available.

Composed with `relUnitorHom` these give the free-cell case, and then the `⊗_A` tower theorem applies
to any tower of free cells — which is what semi-free over the algebra means.

## Tensoring commutes with the degree shift

`CDGATensorShift.lean`.  A bidegree of `M ⊗ N[−k]` in total degree `n` with second index below `k`
contributes nothing; one with second index `b + k` is the bidegree `(a, b)` of `M ⊗ N` in total
degree `n − k`.  So the two carriers agree.

* `tensorShiftMap` — the comparison, built from `shiftEvalAt` in the second factor.
* `tensorShift_component_subsingleton` — below the shift the tensor factor is trivial.
* **`tensorShiftMap_bijective`** — injective and surjective, proved separately rather than by
  exhibiting a two-sided inverse.

Axioms: `propext, Quot.sound` — no choice.

The technique that made it go through, and the reason it is recorded: the correspondence *has* to
mention `p.2 - k`, and truncated subtraction in a dependent index is the standard trap.  The pattern
that defuses it is to let the subtraction appear **only inside the definition**, and in every proof
to destructure the degree with `Nat.le.dest` (`obtain ⟨γ, rfl⟩ : ∃ γ, γ + k = b`) so that the
subtraction is gone before any rewriting starts.  Where a definition's subtraction must still be
matched — in the surjectivity proof — the `gen` idiom does it: generalise over the subtracted value
together with an equation, `obtain rfl` inside, and discharge the outer call with `by omega`.

Two smaller traps, both cost a cycle:
* `obtain rfl : δ = γ` substitutes `γ := δ`, not the other way round, so the rest of the proof must
  be written in the *surviving* name.
* `omega` cannot see through `(⟨n - k, _⟩ : {a // a + k = n}).1`; a `show` restating the goal in
  plain arithmetic first is what unblocks it.

## Next

`⊗_A` commutes with a constant tensor: `M ⊗_A (N ⊗_R V) ≅ (M ⊗_A N) ⊗_R V`, where the finite
bidegree index (`tensorIndexEquiv`) makes the `Pi`-`⊗` exchange available via
`TensorProduct.piRight` and `TensorProduct.comm`.  Then `tensorShiftMap` and that exchange, composed
with `relUnitorHom`, give the free-cell computation and hence `hcell` for `⊗_A`.

## Tensoring with a constant module passes through the graded tensor product

`CDGATensorConstExchange.lean`.

* **`tensorConstExchange V n : (TensorCarrier M N n) ⊗ V ≃ₗ TensorCarrier M (fun m => N m ⊗ V) n`**,
  with `tensorConstExchange_bijective`.

Unlike everything else in this layer the proof is a one-liner, because the three mathlib equivalences
compose exactly: `comm`, then `TensorProduct.piRight`, then `piCongrRight (comm ≪≫ assoc)`.  What
makes `piRight` applicable is **finiteness of the bidegree index**, which is `tensorIndexFintype` —
the instance built earlier for the unitor's sum.  Without it the map exists but is not an
isomorphism, and the whole exchange fails.

Axioms: `propext, Classical.choice, Quot.sound`.

## Next

The free-cell computation for `⊗_A` is now a composition of things that all exist:

  `M ⊗_A (A[−k] ⊗ V)`
    ─ `freeCellModule_eq` ─ `M ⊗_A Shift(A ⊗ V, k)`
    ─ `tensorShiftMap` ─ `Shift(M ⊗ (A ⊗ V), k)`
    ─ `tensorConstExchange` ─ `Shift((M ⊗ A) ⊗ V, k)`
    ─ `relUnitorHom` ─ `Shift(M ⊗ V, k)`.

What remains is to check that the relators correspond under each of the two exchanges — the same
kind of computation as `tensorProdRight_relTensorRelator`, which was short once the single-bidegree
lemmas were available.  After that `hcell` for `⊗_A` follows exactly as
`tensorMapLeft_constCell_isQuasiIsoFull` did for `⊗_R`, and the last row of the parity table closes.

## The relator correspondence under the shift

`CDGATensorShift.lean` gained **`tensorShiftMap_tensorSingle`** — the shift comparison sends a
single-bidegree element to a single-bidegree element, one degree lower — and
`CDGARelTensorShift.lean` uses it for

* **`tensorShiftMap_relTensorRelator`** — a relator of a tensor product with a shifted factor is a
  relator, one degree lower.  The shift moves the cell argument but changes neither the sign nor the
  shape, because the action on a shift *is* the action read off above the shift
  (`shiftEvalAt_shiftAct`), and that lemma is the only input beyond the single-bidegree transport.

This is the first of the two relator correspondences the free-cell computation needs, and it
confirms the pattern: once the single-bidegree transport lemma exists, the relator statement is
three rewrites.

Axioms: `propext, Quot.sound` for the transport, `propext, Classical.choice, Quot.sound` for the
relator statement.

## Next

The second correspondence, for `tensorConstExchange`: a relator of `M ⊗ (N ⊗ V)` is the image of a
relator of `M ⊗ N` tensored with `V`.  Then the two correspondences give stability of the relations
under both exchanges, the exchanges descend to the quotients, and — composed with `relUnitorHom` —
the free-cell computation for `⊗_A` follows, discharging `hcell` there.

## The relator correspondence under the constant exchange

`CDGARelTensorConst.lean` — the second of the two correspondences.

* `assoc_tmul_right` — associativity on an element tensored with a fixed vector is adjoining that
  vector; proved by induction on the element.
* `tensorConstExchange_tmul`, **`tensorConstExchange_tensorSingle`** — the exchange on a pure tensor
  and on a single-bidegree element.
* **`tensorConstExchange_relTensorRelator`** — a relator tensored with a coefficient is a relator
  with that coefficient adjoined to the cell argument: nothing else changes, because the action on
  `N ⊗ V` acts on `N` and carries `V` along, which is exactly what the exchange does.

Both relator correspondences the free-cell computation needs are now proved, and the pattern held
again: single-bidegree transport first, relator statement in three rewrites.

Axioms: `propext, Classical.choice, Quot.sound`.

## Next

With the two correspondences the relations are stable under each exchange, so each exchange descends
to the quotient — the descent is `Submodule.liftQ` plus the span induction already written twice in
this layer (`relTensorRel_tensorSigmaR`, `relTensorProdRightMap_ker`).  Composing the two descents
with `relUnitorHom` gives

  `relTensorModule P (freeCellModule A V k) ≅ shiftModule (tensorConstModule P V) k`,

and then `hcell` for `⊗_A` follows exactly as `tensorMapLeft_constCell_isQuasiIsoFull` did for
`⊗_R`, closing the last row of the parity table.

## Both exchanges preserve the relations

* **`relTensorRel_tensorShiftMap`** (`CDGARelTensorShift.lean`) — the shift comparison sends the
  relations of `M ⊗ N[−k]` into the relations of `M ⊗ N`, in every shifted degree.  The span
  induction needs one case split the earlier stability proofs did not: a relator whose cell argument
  sits *below* the shift has that argument in a trivial module, so the relator is zero
  (`relTensorRelator_zero_cell`); above the shift the correspondence applies.
* **`relTensorRel_tensorConstExchange`** (`CDGARelTensorConst.lean`) — the constant exchange sends
  `relTensorConstRel` (relators tensored with coefficients) into the relations of `M ⊗ (N ⊗ V)`.
  This one is a *nested* span induction — outer over the generators `x ⊗ w`, inner over `x` in the
  relator submodule — which is a shape that had not appeared before in this layer.

Axioms: `propext, Classical.choice, Quot.sound`.

A degree-substitution note worth keeping: after `rintro` on a relator's existential, `subst` on the
degree equations must be done in the right order and sometimes *replaced* by an `obtain rfl` in the
opposite direction.  Here `subst hβ` produces the index `c + (γ + k)` while the correspondence
lemma is stated at `c + γ + k`, and those are propositionally but not definitionally equal;
`obtain rfl : β = c + γ + k := by omega` puts the index in the form the lemma expects.

## Next

The two stability results are exactly the hypotheses of `Submodule.liftQ`, so each exchange now
descends to the quotient.  Composing the two descents with `relUnitorHom` gives the free-cell
computation for `⊗_A` and discharges `hcell` there.

## The shift descent

`CDGARelTensorDescent.lean`.

* `relTensorShiftPre`, `relTensorShiftPre_ker`, **`relTensorShiftMap`** — the shift comparison
  descends: `M ⊗_A N[−k]` maps to the shift of `M ⊗_A N`, degree by degree, by `Submodule.liftQ`
  on the stability result.
* **`relTensorShiftMap_surjective`** — surjective, because the comparison is surjective upstairs and
  the quotient maps are.

Axioms: `propext, Classical.choice, Quot.sound`.

## Next

Injectivity of `relTensorShiftMap` is the remaining half, and it is the *converse* of stability: if
`tensorShiftMap z` lands in the relations in every shifted degree then `z` was already a relation.
The route is the one that worked for `relTensorRel_of_prodRight` — exhibit the preimage of a relator
explicitly.  Here the shift index is a **subsingleton** (`shiftIndexUnique`), so an element of the
target is determined by its value at the single index, and the preimage of `rel(x, m, v₀)` is
`rel(x, m, (shiftEvalAt …).symm v₀)`; that is the one computation left.

With injectivity the shift descent is an isomorphism, and together with the same two steps for the
constant exchange (whose stability is already proved) the free-cell computation for `⊗_A` closes.

## Tensoring over the algebra commutes with the degree shift

`CDGARelTensorDescent.lean` is complete on the shift side.

* `shiftIndexSubsingleton` — the index of a shifted degree is a subsingleton.  This is what makes
  the converse direction tractable: an element of a shifted carrier is determined by its value at
  the single index.
* `tensorShiftEquiv` — the ungraded comparison packaged as an equivalence.
* **`relTensorRel_shift_of_forall`** — the converse of stability: an element whose image is a
  relation in every shifted degree was already a relation.  The proof runs a span induction whose
  motive is stated on the *preimage*, `(tensorShiftEquiv).symm ∘ (shiftEvalAt).symm`, so the zero,
  add and smul cases are pure linearity and only the generator case does work: the preimage of
  `rel(x, m, v₀)` is `rel(x, m, (shiftEvalAt …).symm v₀)`.
* `relTensorShiftMap_injective`, `relTensorShiftMap_bijective`, and
  **`relTensorShiftEquiv : M ⊗_A N[−k] ≃ₗ (M ⊗_A N)[−k]`**.

Axioms: `propext, Classical.choice, Quot.sound`.

Stating the induction motive on the preimage rather than on the image is the trick worth keeping:
it converts three of the four span-induction cases into `map_zero`/`map_add`/`map_smul`.

## Next

The same four steps for the constant exchange — its relator correspondence and stability are already
proved, so what is left is the descent (`Submodule.liftQ`), the converse, and the packaging.  Then
`relTensorShiftEquiv` and that equivalence, composed with `relUnitorHom`, give the free-cell
computation for `⊗_A` and discharge `hcell` there.

## The constant descent, and the free cell computed over the algebra

`CDGARelTensorDescent.lean` is now complete on both sides, and `CDGARelFreeCell.lean` composes them.

* `relTensorConstBil`, `relTensorConstBil_ker`, `relTensorConstBilQ`, **`relTensorConstMap`** — the
  constant exchange descends.  The map out of `(M ⊗_A N) ⊗ V` is built as `TensorProduct.lift` of a
  bilinear map whose first slot is itself a `Submodule.liftQ`; `TensorProduct.curry` is what turns
  the composite `mkQ ∘ exchange` into that bilinear map without any explicit construction.
* `relTensorConstMap_rTensor`, **`relTensorConstMap_surjective`**.
* `relTensorRelator_add_cell` — a relator is *additive* in its cell argument.  This is what lets the
  converse be proved by `TensorProduct.induction_on` on the cell argument, and it is the second time
  linearity of the relator in that slot has been the decisive fact (the first was
  `relTensorRel_of_prodRight`).
* `relTensorConstInvPre`, `relTensorConstInv`, **`relTensorConstMap_injective`**,
  **`relTensorConstEquiv : (M ⊗_A N) ⊗ V ≃ₗ M ⊗_A (N ⊗ V)`**.  Injectivity is obtained from an
  explicit left inverse rather than a kernel computation, which avoids needing right-exactness of
  the tensor product from mathlib.

And then:

* **`relTensorFreeCellEquiv : M ⊗_A (A[−k] ⊗ V) ≃ₗ (M ⊗ V)[−k]`**, degreewise — the composite of
  the shift descent, the constant descent and the unitor, exactly as the plan predicted.  Nothing new
  was needed to assemble it: `freeCellModule_eq` makes the source literally
  `M ⊗_A Shift(tensorConst (selfModule A) V, k)`, and the three equivalences chain by
  `LinearEquiv.trans` and `LinearEquiv.piCongrRight`.

Axioms: `propext, Classical.choice, Quot.sound`; `relTensorRelator_add_cell` needs only
`propext, Quot.sound`.

## Next

`relTensorFreeCellEquiv` is a degreewise linear isomorphism; to discharge `hcell` for `⊗_A` it has
to be upgraded to a `CDGAModuleHom` and shown natural in `P`.  Each of its three factors is already
known to respect the structure maps in the unquotiented setting — `relUnitorHom` is a
`CDGAModuleHom`, and the two exchanges were built from `tensorShiftMap` and `tensorConstExchange`,
whose compatibility with `d` and the action is the same computation as `constCellTensorHom`'s.  With
that, two out of three against `freeCellFunctor_isQuasiIsoFull` closes the last row of the parity
table.

## The shift comparison is a map of differential graded modules

`CDGATensorShiftHom.lean`.

* `tensorShiftMap_tensorAct` — equivariance.  The action is diagonal on both sides; the only care is
  that `b ≤ p'.1.1` implies `b ≤ r.1` but not conversely, so the boundary case where the action is
  in range for the shifted degree but not for the bidegree has to be treated separately (both sides
  are zero there).
* `tensorShiftMap_tensorDL`, `tensorShiftMap_tensorDR` — the two halves of the differential.  The
  left half is untouched by the shift; the right half is intertwined by `shiftEvalAt_shiftD`, the
  identity that already made the shift a differential graded module in the first place.
* **`tensorShiftHom`** and **`tensorShiftHom_isQuasiIsoFull`**.

Axioms: `propext, Classical.choice, Quot.sound`.

Two `Nat` traps, both new and both recorded because they will recur in the constant-exchange
version:

* `0 + (k'' + 1)` is definitionally `(0 + k'') + 1` but **not syntactically**, so `rw
  [tensorDR_succ]` fails on it; a `have hval : … = 0` proved by `show` (which works up to defeq)
  gets past it where `rw` cannot.
* `rw [zero_add]` on a goal containing an index `0 + k` rewrites the *index* and breaks the motive.
  Reordering so the summand is literally `0` first and then using `add_zero` avoids touching it.

## Next

The same upgrade for `tensorConstExchange` — a `CDGAModuleHom` from
`tensorModule P (tensorConstModule Q V)` — after which both descents are morphisms, the composite
`relTensorFreeCellEquiv` is a morphism, and naturality in `P` plus two out of three against
`freeCellFunctor_isQuasiIsoFull` discharges `hcell` for `⊗_A`.

## The free cell is invariant for the tensor product over the algebra

Four modules close the last row of the parity table.

* `CDGATensorConstHom.lean` — `tensorConstExchange_tensorAct`, `tensorConstExchange_tensorD`,
  **`tensorConstHom`**, `tensorConstHom_isQuasiIsoFull`, `tensorConstExchange_naturality`,
  `tensorConstHom_naturality`.  The action and the left half-differential act through the first
  factor, which the exchange does not touch; the right half-differential meets it in one place, and
  there `(mk v w) ∘ d = (d ⊗ 1) ∘ (mk v w)` because both send `v` to `d v ⊗ w`.
* `CDGARelTensorShiftHom.lean` — **`relTensorShiftHom`**, `_isQuasiIsoFull`, `_naturality`.
* `CDGARelTensorConstHom.lean` — **`relTensorConstHom`**, `_isQuasiIsoFull`, `_naturality`.
* `CDGARelFreeCellInvariance.lean` — **`relTensorMapLeft_freeCell_isQuasiIsoFull`** and
  **`relTensorMapLeft_freeTower_isQuasiIsoFull`**.

The assembly does not build the composite equivalence at all.  Each of the three factors carries a
naturality square with degreewise-bijective verticals, so three applications of two-out-of-three
walk the invariance from `− ⊗_A A` (already known) up through `− ⊗_A (A ⊗ V)` and then
`− ⊗_A (A[−k] ⊗ V)`.  That is strictly cheaper than upgrading `relTensorFreeCellEquiv` to a
morphism and proving *its* naturality, and it needs no inverse morphism, which would otherwise have
had to be produced from degreewise bijectivity.

Axioms throughout: `propext, Classical.choice, Quot.sound`.

## Both parities are closed

| coefficients | cell | invariance |
|---|---|---|
| `⊗_R` | `constCellModule` | `tensorMapLeft_constCellTower_isQuasiIsoFull` |
| `⊗_A` | `freeCellModule` | `relTensorMapLeft_freeTower_isQuasiIsoFull` |

So a tower of free cells is flat for `− ⊗_A −`: tensoring it with a full quasi-isomorphism is
again a full quasi-isomorphism.  This is the flatness statement the derived tensor product needs,
and it is now unconditional.

## Next

Semi-free resolutions: produce, for a given differential graded module, a tower of free cells with
a full quasi-isomorphism onto it.  The invariance theorem above is what makes such a resolution
compute a derived tensor product; the construction itself is the remaining work.

## Filtered colimits of modules, and the colimit of a tower

`CDGAModuleColimit.lean`, `CDGAModuleColimitQuasiIso.lean`, `CDGACellTowerColimit.lean`.

* `CDGAModuleDirectedSystem`, `colimModuleDeg`, `colimModuleD`, `colimModuleAct`,
  **`colimModule`**, `colimModuleOf`, `colimModuleHom`.  Every axiom of the colimit module is an
  identity between elements of a direct limit, and every element of a direct limit comes from a
  stage, so each one reduces to the same axiom at a stage.
* `moduleCocycle_at_stage`, **`colimModuleHom_isQuasiIso`**, **`colimModuleHom_isQuasiIsoFull`**.
  The degree-zero half is the same argument as the cohomology half with the quotient removed: a
  cocycle of the colimit is a cocycle at a stage, and a vanishing in the colimit is a vanishing at a
  later stage.
* `twistedInl` — the base includes into a twisted extension by padding with zero; the twist
  contributes nothing there, so it commutes with the deformed differential.
* `towerTrans` — the transitions of a tower.  These are produced by `Nat.leRec`, which eliminates
  `i ≤ j` into `Type`; the naive alternatives all fail, because `Nat.le` is a `Prop` and neither
  `Nat.le.rec` nor destructing `Nat.le.dest` may produce data, while transporting along
  `i + (j − i) = j` leaves a cast that no later proof can discharge, `i − i = 0` not being
  definitional.
* `towerDirectedSystem`, **`towerColim`**, **`towerColimHom_isQuasiIsoFull`**.

Axioms: `propext, Classical.choice, Quot.sound` (`twistedInl` needs only `propext, Quot.sound`).

## What the colimit still needs

`towerColimHom_isQuasiIsoFull` compares the colimits of two towers.  To conclude flatness of an
*infinite* semi-free module — that `− ⊗_A towerColim` preserves full quasi-isomorphisms — one more
exchange is required:

> `M ⊗_A colim N ≅ colim (M ⊗_A N)`.

Its three steps, and the state of each:

1. `M a ⊗ colim N b ≅ colim (M a ⊗ N b)` — mathlib has this as `TensorProduct.directLimitRight`.
2. a *finite* product of direct limits is the direct limit of the products — not in mathlib; true
   over a directed index because a finite family of stages has an upper bound.
3. the quotient by the relations commutes with the colimit — the relators of the colimit are a
   finite sum, so they are all visible at one stage, and what is left dies at a later one.

Until then the flatness theorem covers every finite stage of a semi-free filtration, which is what
a relative cell construction of finite length needs.

## Step 2 of the exchange is done

`DirectLimitPi.lean` — `piTransition`, `piDirectedSystem`, `directLimitPiMap`, injectivity,
surjectivity, **`directLimitPi`**: a *finite* product commutes with a filtered colimit of modules.

Both halves are the same observation: a finite family of stages has a common upper bound.  For
injectivity the bound must be taken over `insert i (image j univ)`, not `image j univ` — with an
empty index type the latter is empty and the resulting bound need not dominate the stage the element
came from.

Axioms: `propext, Classical.choice, Quot.sound`.

Remaining for `M ⊗_A colim N ≅ colim (M ⊗_A N)`: assemble step 1 (`TensorProduct.directLimitRight`,
mathlib) with step 2 over the bidegrees of a fixed total degree — which are finite, by
`tensorIndexFintype` — and then descend through the relations.

## Step 1 + 2 assembled

`CDGATensorColimit.lean` — `tensorFamilyTransition`, `tensorFamilyDirectedSystem`,
**`tensorColimEquiv`**, `tensorColimEquiv_of`: the graded tensor product commutes with a filtered
colimit, in each total degree.

Two mechanical points that will recur when the same is done over the algebra:

* mathlib's `M ◁ f` is `local notation`, so the `DirectedSystem` instance it carries is not found
  for a named definition with the same unfolding; the instance has to be re-declared by
  `inferInstanceAs`.
* the `.symm` direction of `TensorProduct.directLimitRight` cannot be rewritten with, because the
  index family of its target is spelled with the notation.  Turning the goal round with
  `LinearEquiv.symm_apply_eq` puts the forward lemma in the rewritable position, and the residual
  index mismatch is closed by `rfl`.

Universes: `TensorCarrier` is monomorphic in its two families, so the index type of the colimit must
live in the same universe as the modules — the file declares `ι : Type w`.

Axioms: `propext, Classical.choice, Quot.sound`.

## Step 3, and the flatness of semi-free modules

`CDGARelTensorRight.lean` — `tensorMapRight_tensorSingle`, `tensorMapRight_relTensorRelator`,
`relTensorRel_map_right`, **`relTensorMapRight`**: the tensor product over the algebra is functorial
in the right variable too, which is what makes a directed system of second factors into a directed
system of quotients.

`CDGARelTensorColimit.lean` — `relTensorSystem`, `relTensorColimMap`,
**`relTensorRel_colim_at_stage`**, injectivity, surjectivity, **`relTensorColimEquiv`**,
**`relTensorColimHom`**, `relTensorColimHom_naturality`, and
**`relTensorMapLeft_colim_isQuasiIsoFull`**.

The mathematical content is one observation: a relation over the colimit is a finite combination of
relators, each mentioning a single element of the colimit, so a common stage carries all of them.
Injectivity then reduces to injectivity of the *graded* comparison, which is
`tensorColimEquiv` from the previous step.

`CDGARelSemiFreeFlat.lean` — **`relTensorMapLeft_freeTowerColim_isQuasiIsoFull`**: a semi-free
module, that is the colimit of a tower of free cells, is flat for `− ⊗_A −`.

Axioms throughout: `propext, Classical.choice, Quot.sound`.

### The instance trap that runs through all of it

`TensorCarrier` and `RelTensorCarrier` are `def`s with their own `AddCommGroup` instances, while
`Module.DirectLimit` takes those instances as arguments.  Writing `Module.DirectLimit.of` by hand
re-synthesises them and produces a term that is definitionally but not syntactically the one the
comparison was built with, so every `rw` with `map_add`, `map_sub` or `map_zero` fails with an
opaque "application type mismatch".  Type ascription does **not** fix it — the instance is chosen
from the operand's own type, not from the expected type.  Two things do:

* spell the family as the bare product (`tensorColimFamily`) wherever the product instances are
  wanted, and introduce genuinely typed locals (`obtain ⟨A, hA⟩ : ∃ A : …, A = …`) before forming
  a difference;
* never write a raw `Module.DirectLimit.of` downstream — go through `colimModuleOf` and the
  `colimModuleD_colimOf` / `colimModuleAct_colimOf` / `colimModuleHomFun_colimOf` forms, which are
  stated in the file where the instances are already the right ones.

### Universes

`colimModuleDeg` lands in `Type (max v' w)` for an index in `Type v'`, and `TensorCarrier` is
monomorphic, so the index of a colimit that is going to be tensored must satisfy `v' ≤ w`.  Lean has
no such constraint, but `max 0 w = w` holds definitionally, so declaring the index in `Type 0` —
which covers `ℕ`, hence every tower — is both sufficient and universe-clean.

## Free cells of arbitrary rank

`CDGAModuleFinsupp.lean` — `pick` (a choice of witness which sends zero to zero, so that supports
stay finite), **`finsuppModule`**, `finsuppMap`, **`finsuppMap_isQuasiIsoFull`**: the direct sum of
copies of a differential graded module, and that a direct sum of full quasi-isomorphisms is one.

`CDGAFreeCoefficientsInfinite.lean` — `finsuppScalarRight_map`, **`tensorConstFinsuppHom`**,
**`tensorConstMap_isQuasiIsoFull_of_basis`**, `freeCellFunctor_isQuasiIsoFull_of_basis`.

This removes `Fintype` from the free-cell hypotheses: `relTensorMapLeft_freeCell_isQuasiIsoFull`,
`relTensorMapLeft_freeTower_isQuasiIsoFull` and `relTensorMapLeft_freeTowerColim_isQuasiIsoFull` now
hold for cells of arbitrary rank.  The finite version went through `ι → R` (a product); the general
one has to go through `ι →₀ R` (a sum), which is why a separate direct-sum layer was needed.

Every coefficientwise argument in that layer has the same shape: the condition is coefficientwise,
and a witness chosen by `pick` vanishes wherever the coefficient does, so the witness family is
again finitely supported.

## The universal properties, and the covering tower

`CDGAFreeCellExtend.lean` — **`freeCellExtend`**, `freeCellGen`, **`freeCellExtend_gen`**: a
morphism out of `A[−k] ⊗ V` is exactly a linear map `V → Z^k`.  The cocycle condition is forced: the
Leibniz rule produces the term `(−1)^a x · d(g v)`, which must vanish for the extension to commute
with the differential.

`CDGAModuleColimit.lean` gained **`colimModuleLift`** — the universal property of the colimit.

`CDGATwistedExtend.lean` — `CDGATwistedLift`, **`twistedExtend`**, `twistedExtend_comp_inl`: a
morphism out of a cell attachment is a morphism out of the base together with an equivariant map out
of the cell whose failure to commute with the differential is exactly the image of the twist — the
null-homotopy the attachment records.

`CDGAFreeCover.lean` — `CDGATwist.zero`, `CDGATwistedLift.ofHom`, **`cocycleCover`**,
`cocycleCover_gen`, `freeCellGen_mem_cocycles`.

`CDGASemiFreeCover.lean` — **`coverTower`**, `coverMap`, `coverMap_trans`, **`coverColimMap`**,
**`coverColimMap_surjective_on_cocycles`**, `coverColimMap_cocyclesMap_zero_surjective`,
**`coverColimMap_cohomologyMap_surjective`**.

> Every differential graded module receives a comparison from a semi-free module which is surjective
> on the cocycles of every degree, hence on cohomology and on the degree-zero cocycles.

Axioms: `propext, Classical.choice, Quot.sound` (`freeCellExtend`, `twistedExtend` and
`freeCellGen_mem_cocycles` need only `propext, Quot.sound`).

## Next

The other half of a resolution: make the comparison *injective* on cohomology by attaching, at each
stage, a cell along each cocycle of the tower whose image is a coboundary — the null-homotopy of
that coboundary is the `CDGATwistedLift` datum.  `twistedExtend` and `freeCellExtend` are exactly
the two universal properties that step needs; what is left is the bookkeeping of the interleaved
induction and the convergence of the colimit.

## Attaching a cell along cocycles, and carrying a comparison across it

`CDGAFreeCellTwist.lean` — `freeCellTwistₗ`, `freeCellTwistₗ_apply`, **`freeCellTwist`**: a twisting
cochain on `A[−k] ⊗ V` is exactly a linear map `V → Z^{k+1}` of the base.  The Koszul sign is not a
choice: `τ_act` forces `τ(x ⊗ v) = (−1)^{|x|} x · τ(v)`, and with that sign `τ_d` is equivalent to
`d(τ v) = 0`.

`CDGAFreeCellExtend.lean` gained `freeCellExtendₗ_act`, the equivariance of the extension, which
needs no assumption on the generators — only `map_d` does.  That is what lets the same construction
serve as the null-homotopy datum.

`CDGAFreeCellLift.lean` — **`freeCellTwistedLift`**, **`freeCellAttachExtend`**: if the images under
a comparison of the attaching cocycles are coboundaries, a choice of primitives extends the
comparison across the attachment.  The sign bookkeeping works out to an `add_comm`: the Leibniz term
`(−1)^a x · d(g v)` becomes `(−1)^a x · ε(w v)`, which is exactly the image of the twist.

So both halves of a relative cell construction are now available as universal properties:

| step | datum | construction |
|---|---|---|
| attach a cell | `w : V → Z^{k+1}(S)` | `freeCellTwist` |
| map out of the base | `g : V → Z^k(P)` | `freeCellExtend` |
| carry a comparison across | primitives for `ε ∘ w` | `freeCellTwistedLift` |
| assemble the tower | compatible family | `colimModuleLift` |

Axioms: `propext, Quot.sound`.

## Next

The killing tower: at stage `j`, attach one cell for each pair `(c, v)` with `c` a cocycle of the
stage and `v` a primitive for its image, using `freeCellTwist` for the attachment and
`freeCellTwistedLift` for the extension of the comparison.  The colimit comparison is then injective
on cohomology, because a cocycle killed in the target is already visible at some stage and was made
a coboundary at the next one; combined with `coverColimMap_cohomologyMap_surjective` that gives a
semi-free resolution.

## A structural obstruction in `towerMod`, and what it forces

The killing half cannot be expressed with the tower machinery as it stands.  `towerCarrier` takes
the family of cells `C : ℕ → ℕ → Type` as an *input*, so `towerMod` fixes every cell before the
recursion starts; only the twist at stage `i` may depend on `towerMod … i`.  But the cell that kills
the kernel at stage `i` has to be free on the cocycles *of that stage*, so its coefficient module
depends on `towerMod … i` — which the signature forbids.

The fix is a stage object carrying its own instances, so that carrier, structure and comparison are
produced by a single recursion:

```
structure DGStage (A : CDGAStructure R X) (P : CDGAModuleStructure A M) where
  carrier : ℕ → Type w
  group   : ∀ n, AddCommGroup (carrier n)
  smul    : ∀ n, Module R (carrier n)
  str     : CDGAModuleStructure A carrier
  cmp     : CDGAModuleHom str P
```

with a step which attaches the free cell on `{(c, v) | c ∈ Z(str), cmp c = d v}` using
`freeCellTwist`, and extends `cmp` across it with `freeCellTwistedLift`.  The colimit is then taken
over the sequence `step^[i] init`, and `relTensorMapLeft_freeTowerColim_isQuasiIsoFull` still
applies because each stage is still a twisted extension by a free cell — the flatness theorem never
used the fact that the cells were chosen in advance.

Everything that step needs is now built and unconditional:
`freeCellTwist`, `freeCellExtend`, `freeCellTwistedLift`, `twistedExtend`, `colimModuleLift`,
`coverColimMap_cohomologyMap_surjective`.  What is left is the bundled recursion, the two
convergence arguments (a cocycle of the colimit lives at a stage; a coboundary of the target is
killed at the next one), and the assembly.

## Semi-free resolutions exist, and they are flat

`CDGAUnitalCells.lean` — `tensorConst_unital`, `shift_unital`, **`freeCell_unital`**: a free cell
over a unital algebra is a unital module, which is what makes a generator's twist equal to its
prescribed value rather than the unit acting on it.

`CDGADGStage.lean` — **`DGStage`** (carrier, its two instances, structure and comparison, all in one
object so that a recursion can produce them), `killIndex`, **`cellIndex`** (`Z^k(P) ⊕ killIndex`),
`cellW`, `cellG`, `cellG_primitive`, **`killStep`**, `killStepHom`, **`killSeq`**, `killTrans`,
`killDirectedSystem`, **`killColim`**, **`killColimMap`**, `killSeq_unital`, **`killSeq_kills`**,
**`killSeq_covers`**, `killColimMap_surjective_on_cocycles`,
**`killColimMap_cohomologyMap_injective`**, **`killColimMap_isQuasiIso`**.

One cell per stage suffices because the covering generators and the killing generators live in the
*same* degree: the cell attached at stage `j` is free on `Z^k(P) ⊕ {(c, v) | c ∈ Z^{k+1}, ε c = d v}`
with `k = (Nat.unpair j).2`, attached by `0` on the left summand and by `c` on the right.  So a
single `freeCellTwist` and a single `freeCellTwistedLift` do both jobs, and `Nat.pair` schedules
every degree infinitely often — which is exactly what the two convergence arguments need.

`CDGAResolution.lean` — `resolutionBase`, **`resolution`**, `resolutionMap`,
**`resolutionMap_isQuasiIso`**, `resolutionMap_cocyclesMap_zero_surjective`, **`killSeq_flat`**,
`relTensorMapLeft_killColim_isQuasiIsoFull`, **`relTensorMapLeft_resolution_isQuasiIsoFull`**.

> **Every differential graded module over a unital commutative differential graded algebra has a
> semi-free resolution, and that resolution is flat for the tensor product over the algebra.**

Axioms throughout: `propext, Classical.choice, Quot.sound`.

### The one thing a cell cannot do

`IsQuasiIsoFull` asks in addition that `Z^0` map bijectively.  The resolution gives surjectivity
there, but not injectivity, and no cell can supply it: killing a degree-zero cocycle would need a
generator in degree `−1`.  In non-negative cohomological degrees that is not a gap in the
construction but a fact about it, and it is why `resolutionMap_isQuasiIso` is stated as
`IsQuasiIso` rather than `IsQuasiIsoFull`.  The flatness theorem is unaffected: it consumes a full
quasi-isomorphism in the *other* variable and says nothing about the resolution's own `Z^0`.

## The left unitor, and derived base change

`CDGALeftUnitor.lean` — `leftActₗ`, `leftUnitorToₗ`, `leftUnitorToₗ_relTensorRelator`,
`relLeftUnitorTo`, `leftUnitorFromₗ`, `leftUnitorToₗ_tensorAct`, `leftUnitorToₗ_tensorD`,
`relLeftUnitor_single`, `relLeftUnitorEquiv`, **`relLeftUnitorHom`**,
**`relLeftUnitorHom_isQuasiIsoFull`**: `A ⊗_A M ≅ M`.

The mirror is *simpler* than `M ⊗_A A ≅ M`, not merely symmetric: the left comparison carries no
sign at all.  On a relator the two terms differ by moving one algebra element past the other, and
the sign of that move is exactly the relator's own sign, so they cancel; equivariance and the
Leibniz rule then come out as `act_assoc` and `d_act` verbatim.

`CDGADerivedBaseChange.lean` — `derivedBaseChangeMap`, **`derivedBaseChange_unit`**: if a
differential graded module `C` is equivalent to the algebra, then `C ⊗^{L}_A K ≃ K`.  The proof is
the composite the argument always is — the resolution computes the derived tensor product, base
change along the equivalence is an equivalence because the resolution is semi-free, and the left
unitor identifies `A ⊗_A F` with `F`.

Axioms: `propext, Classical.choice, Quot.sound`.

## Unconditionality audit

No `sorry`, `admit`, `axiom`, `opaque` or `unsafe` occurs anywhere in the layer, and every
declaration audits inside `propext, Classical.choice, Quot.sound`.  There is no `Prop` interface
standing in for an unproved result.  What the statements do take is of exactly two kinds:

* **data** — the algebra `A`, a unit `u : CDGAUnit A`, modules, morphisms, degrees, a basis of a
  coefficient module;
* **properties of that data** — `CDGAModuleUnital u P` (the unit acts as the identity, which is part
  of what "unital module" means and is false for a general module), and `φ.IsQuasiIsoFull` (the
  given comparison is a quasi-isomorphism, which is the hypothesis of the statement).

Every intermediate invariance hypothesis is discharged at the point of use: `hbase`/`hcell` of
`relTensorMapLeft_twisted_isQuasiIsoFull` by `relTensorMapLeft_freeCell_isQuasiIsoFull`, `h₀`/`hcell`
of `relTensorMapLeft_tower_isQuasiIsoFull` inside `relTensorMapLeft_freeTower_isQuasiIsoFull`, and
`h₀` of `killSeq_flat` inside `relTensorMapLeft_resolution_isQuasiIsoFull`, where the base is the
concrete free cell on the cocycles of degree zero.

## Towards the multiplicative structure: the Koszul product on a bidegree

`CDGATensorAlgebra.lean` — `neg_one_pow_eq_of_even_add`, `tensorPairMap`, **`tensorPairₗ`**,
`tensorPairₗ_tmul`, **`tensorPair_comm`**, **`tensorPair_assoc`**, **`tensorPair_dL`**,
**`tensorPair_dR`**.

`(x₁ ⊗ y₁)(x₂ ⊗ y₂) = (−1)^{|y₁||x₂|}(x₁x₂) ⊗ (y₁y₂)`, built from
`TensorProduct.tensorTensorTensorComm` followed by the two multiplications, and the four laws it
satisfies bidegree by bidegree.  This is where all the sign bookkeeping of a tensor product of
algebras lives; the remaining work is the sum over splittings of a total degree, which is
reindexing, not signs.

Every sign identity reduces to one lemma, `neg_one_pow_eq_of_even_add`: two powers of `−1` agree
when their exponents differ by an even number.  Stating it that way turns each verification into a
single `ring` goal, which is what makes the four laws short.  Two of the four signs are not what a
first guess gives:

* graded commutativity needs `(−1)^{(a₁+a₂)(b₁+b₂)}` — the *total* degrees — and the shuffle sign
  plus the two algebra signs conspire to produce exactly that;
* the first Leibniz half carries `(−1)^{a₁+a₂}`, again the total degree of the left factor, not the
  `(−1)^{a₁}` that the `X`-differential alone would suggest.

Axioms: `propext, Quot.sound`.

## Next

The sum over splittings: for a fixed output bidegree the product is a finite sum over the ways of
splitting each of the two indices, indexed by the bidegrees of the left factor's total degree —
which `tensorIndexFintype` already knows is finite.  Associativity and commutativity of the sum are
reindexing arguments on top of `tensorPair_assoc` and `tensorPair_comm`; the Leibniz rule is
`tensorPair_dL` and `tensorPair_dR` summed, matched against `tensorD`'s two halves.

## The convolution product, indexed by splittings

`CDGATensorAlgebra.lean` — **`Splitting`**, `splittingFintype`, `splittingTerm`,
**`tensorAlgMul`**, its four bilinearity lemmas, `splittingSwap`, and
**`tensorAlgMul_comm`**.

The product of two elements of a tensor product of algebras is, at each output bidegree, a sum over
the ways of splitting that bidegree between the two factors.  The first attempt indexed the sum by a
bidegree of the *left* factor and recovered the right one by subtraction; that is fatal, because the
subtraction sits in a dependent position and the reindexing step then needs to identify
`p − (p − r)` with `r` *inside* `f (…)`, which changes the argument's type and defeats `rw` with a
motive error.

Indexing by the splitting itself —

```
Splitting a b p := {rs // rs.1.1.1 + rs.2.1.1 = p.1.1 ∧ rs.1.1.2 + rs.2.1.2 = p.1.2}
```

— removes every subtraction.  Graded commutativity is then the *swap* of a splitting, a definitional
involution, and `Finset.sum_nbij'` plus `tensorPair_comm` closes it in three lines.  This is the
same principle the shift layer records ("subtype indexing to avoid ℕ truncated subtraction in
dependent positions"), and it is worth stating as a rule: **carry the complement, never recompute
it.**

One import was missing and its absence is invisible in the error message: `Fintype (α × β)` lives in
`Mathlib.Data.Fintype.Prod`, and without it the instance search fails with no hint that an import is
the cause.

Axioms: `propext, Classical.choice, Quot.sound`.

### What remains for the tensor product of algebras

Graded commutativity **and associativity** are done — `tensorAlgMul_comm`, `splitReassoc`,
`splitReassocInv`, `splitReassoc_inv`, `splitReassocInv_inv`, **`tensorAlgMul_assoc`**.  After
`Finset.sum_sigma'` both sides are sums over triples of bidegrees adding up to the output, and the
reassociation of a triple is the bijection `Finset.sum_nbij'` wants; `tensorPair_assoc` matches the
summands.

Two things were needed to make the round-trip identities go through, and both are worth recording:

* **define the reassociation by projections, not by `match`.**  Pattern-matching on a `Sigma` of
  subtypes produces a `match` that does not iota-reduce even with the scrutinee in constructor form
  and even with the index type an `abbrev`; written with projections the round trip is closed by
  `rfl` after one substitution.
* **substitute the middle index.**  After destructuring, the two sides differ only in the middle
  bidegree, which is a *variable*; `subst`ing it against `⟨(r₁+s₁, r₂+s₂), _⟩` makes both sides
  syntactically equal.  The proof carried by that bidegree has to be produced by an `omega` that
  cannot see the hypotheses mentioning the variable — `clear` them inside the `have` — or `subst`
  refuses with "occurs at".

The external differential is built: **`zeroActModule`**, **`extTensorD`**, `extTensorD_d`.  The
signatures of `tensorDL` and `tensorDR` ask for two modules over one algebra even though their
bodies use only the two differentials; rather than duplicate them, the second algebra is made an
`A`-module with **zero action** — every module axiom is then an identity between zeros except the
two for the differential, which are the algebra's own.  So the external differential of a tensor
product of algebras *is* `tensorD` of two modules, and `d² = 0` comes for free.

**Leibniz is proved** — `tensorDL_of_fst_zero`, `tensorDR_of_snd_zero`,
**`tensorAlgMul_tensorDL`**, **`tensorAlgMul_tensorDR`**, **`tensorAlgMul_extTensorD`** — and with
it the whole structure:

> **`tensorCDGA` : the tensor product of two commutative differential graded algebras is a
> commutative differential graded algebra.**

Each half-differential is treated separately.  On the left side the differential of a sum over
splittings expands, term by term, into two by `tensorPair_dL` (resp. `tensorPair_dR`); on the right
side the two summands are sums over splittings of the two shifted degrees, and the four groups match
under the coordinate shifts.  The `tensorDR` half is the one with position-dependent signs — the
half-differential carries `(−1)^{p₁}` where `p₁` varies over the sum — and they come out right
because `p₁ = r₁ + s₁` on each splitting: the two exponents differ by an even number, which is
exactly what `neg_one_pow_eq_of_even_add` consumes.

Two mechanical points:

* the shift maps are `def`s, so `(shiftLeftSnd … rs).1.2` does not reduce to `rs.1.2` at reducible
  transparency and `rw` cannot see through it; stating the summand identity with a `show` written
  entirely in terms of `rs` — which is defeq — puts both sides in the same shape.
* pulling a scalar out of the *first* argument of a bilinear map is `LinearMap.map_smul₂`, not
  `map_smul`; out of the second it is `map_smul`.

None of the three needs a new sign identity; the signs are all in `tensorPair_comm`,
`tensorPair_assoc`, `tensorPair_dL` and `tensorPair_dR`.

The reindexing is set up: `coIndex`, `coIndex_apply`, `coIndex_fits`, **`coIndex_coIndex`** — the
complementary bidegree `p − r`, an involution on the bidegrees that fit inside `p`.  It is total
(junk outside the fitting set), which is what `Finset.sum_nbij'` needs, and `coIndex_coIndex` is the
involutivity.  Both sums restrict to the fitting set because the non-fitting summands are `0` by
the `dite`.

The one real obstacle in the summand step is dependent rewriting: identifying
`coIndex a p (coIndex b p r)` with `r` inside `f (…)` changes the *type* of the argument, so `rw`
hits a motive problem.  The way through is to destructure the indices into naturals first and
introduce the complement as a variable — `obtain ⟨c, rfl⟩ : ∃ c, p₁ = r₁ + c` — after which every
identification is a rewrite of a natural number inside `X (…)`, whose motive is type-correct.

### The reindexings the Leibniz rule needs

`shiftLeftFst`, `shiftRightFst`, their injectivity and surjectivity, and **`sum_shiftLeftFst`**,
**`sum_shiftRightFst`**: raising one coordinate of one part of a splitting is a bijection onto the
part of the target where that coordinate is positive, and the complement contributes nothing.

`Finset.sum_bij` is the right tool here rather than `sum_nbij'`: the inverse map would have to
subtract one from a coordinate, and a *total* inverse cannot be written when the source splitting
type is empty.  With `sum_bij` the preimage is produced inside an existential, where the subtraction
is harmless — it never enters a dependent position.  `Finset.sum_filter_of_ne` discards the
complement, whose terms vanish because a half-differential is zero in degree zero.

## The tensor product of algebras is functorial, and unital

`CDGATensorAlgebraMap.lean` — `tensorAlgMapₗ`, **`tensorPairₗ_naturality`**, `tensorAlgMapₗ_mul`,
`tensorAlgMapₗ_extTensorD`, **`tensorCDGAMap`**: a pair of morphisms of commutative differential
graded algebras induces one on the tensor products.  Multiplicativity is checked one splitting at a
time — the Koszul sign depends only on degrees, so it passes through untouched — and compatibility
with the differential is the module-level statement, the external differential being `tensorD` of
two modules.

`CDGATensorAlgebraUnit.lean` — `splittingZeroSubsingleton`, `tensorAlgOne`, **`tensorCDGAUnit`**:
`1 ⊗ 1` is a unit for the tensor product.  The proof of `one_mul` is a one-term sum: a splitting
whose left part has total degree zero is *unique*, its left part being `(0,0)` and its right part
the whole output, so `Finset.sum_eq_single_of_mem` applies with the other terms excluded by
`Subsingleton.elim` rather than by a vanishing argument.

Axioms: `propext, Classical.choice, Quot.sound` (`tensorPairₗ_naturality` needs only
`propext, Quot.sound`).

## The algebra layer reaches the module layer

`CDGATensorAlgebraBridge.lean` — **`zeroActHom`**, **`tensorMapLeft_zeroActHom_constCellTower`**.

Forgetting the action of an algebra on itself turns a morphism of commutative differential graded
algebras into a morphism of differential graded modules with zero action, over any base algebra
whatever.  Under that forgetting, the comparison induced on a tensor product of algebras *is* the
module-level comparison in the left variable — the differential of a tensor product of algebras
being `tensorD` of two zero-action modules — so every invariance theorem of the module layer applies
to it unchanged.  The cell-tower theorem is recorded in that form:

> if the right factor is a tower of cells for the ground ring and the comparison of left factors is
> a full quasi-isomorphism, then so is the comparison of tensor products.

Universes are the only friction: `CDGAConstCellTensor` puts the ground ring in the same universe as
the modules, so the bridge must too.

`CDGAHom.id`, **`tensorCDGAMap_isQuasiIso`**, **`tensorCDGAMap_isQuasiIso_of_isQuasiIsoFull`** close
the upgrade:

> tensoring with a quasi-isomorphism of algebras is a quasi-isomorphism **of algebras** as soon as
> it is one of the underlying complexes.

That transport is *definitional*.  The cocycles, coboundaries and cohomology of an algebra are those
of its underlying complex, and the differential of a tensor product of algebras is the differential
of the tensor product of the underlying zero-action modules, so `CDGAHom.IsQuasiIso` of the induced
map and `CDGAModuleHom.IsQuasiIso` of the module-level comparison are the *same proposition* — the
proof is the hypothesis itself.  (The corresponding statement about the underlying degreewise maps
is also true by `rfl` but too expensive to check; the `Prop`-level one is cheap.)

So the algebra layer needs no invariance theory of its own: any module-level theorem — const-cell
towers, free coefficients of any rank, semi-free towers — supplies the hypothesis.

Axioms: `propext, Quot.sound` for `zeroActHom` and `CDGAHom.id`;
`propext, Classical.choice, Quot.sound` for the invariance statements.

## The product of two single-bidegree elements

`CDGATensorAlgebraIncl.lean` — **`tensorAlgMul_tensorSingle`**: the product of two elements
supported at single bidegrees is a *one-term* sum, the surviving splitting being the pair of those
two bidegrees; every other splitting kills one of the two factors by `tensorSingle_ne`.

Uniqueness of the surviving splitting is where the subtype bookkeeping bites: with the left parts
equal, the right parts agree by cancelling the same left summand from the two splitting conditions.
`omega` will *not* do that here — it atomises the iterated `Subtype.val` projections and loses the
link — so the cancellation has to be written out, `Nat.add_left_cancel (e₁.trans e₃.symm)`.  That is
worth remembering: when a goal about splittings is pure cancellation, give the term.

Axioms: `propext, Classical.choice, Quot.sound`.

**`tensorAlgMul_tensorSingle_ne`** is the companion: off the sum of the two bidegrees the product
vanishes, because every splitting misses one of the two supports.

## The two inclusions

`tensorSingleRight_apply`, `_ne`, **`extTensorD_tensorSingleRight`**, **`tensorCDGAInclLeft`**;
`tensorSingleLeft_apply`, `_ne`, **`extTensorD_tensorSingleLeft`**, **`tensorCDGAInclRight`**.

Multiplicativity is the two product lemmas above; compatibility with the differential is that the
half-differential in the other variable kills the inclusion's image because `d1 = 0`.

The two are *not* mirror images, and the asymmetry is worth naming.  For `x ⊗ 1` the second
half-differential reads at `(p₁, β)` — the first coordinate is unchanged, so `p₁ ≠ 0` transfers
straight to the read index.  For `1 ⊗ y` the first half-differential reads at `(α, p₂)` with
`α = p₁ − 1`, and `α` may be zero even when `p₁` is not; that branch needs its own sub-case, in
which the value is nonzero but `A.d 1 = 0` kills it anyway.  Splitting on the *predecessor* before
introducing any index proof is what makes it go through.

Two mechanical points, both about `rw` picking the wrong occurrence: state the vanishing lemma with
its index proof supplied explicitly, so the rewrite is pinned to the intended bidegree; and pass the
splitting-index proofs positionally (`… h rfl`) rather than by `by simp only; omega`, which closes
some of them by `rfl` and then leaves `omega` with no goals.

Axioms: `propext, Classical.choice, Quot.sound`; the two differential computations need only
`propext, Quot.sound`.

## Restriction of scalars

`CDGARestrictScalars.lean` — **`CDGAHom.restrictModule`**, `restrictModule_act`, `restrictModule_d`,
**`CDGAHom.restrictModule_unital`**.

A morphism of commutative differential graded algebras makes the target a differential graded module
over the source: the action is the product with the image, `act_assoc` is multiplicativity of the
morphism followed by associativity of the product, and `d_act` is the Leibniz rule of the target
together with the fact that the morphism commutes with the differentials.  Unitality holds as soon
as the morphism sends the unit to the unit.

This is the datum a relative construction is defined against: with it, every algebra over a base
algebra is a module over it, so `relTensorModule` — the layer's `⊗_A`, and everything proved about
it, including flatness of semi-free resolutions — applies to algebras over a base.

Axioms: `propext, Quot.sound`.

## The relative tensor product of algebras: the sign computation

**`tensorAlgMul_tensorSingle_eq_single`** — the product of two single-bidegree elements is a
single-bidegree element, at the sum of the two bidegrees, with the Koszul pairing as its value.
That reduces the descent of the product through the relations to pure algebra on singles.

The computation it enables is worth recording, because it is the whole content of the ideal
property and the signs are not obvious.  Write `γ` for a cell of degree `c`, and let
`u = x ⊗ y` with `|x| = a`, `|y| = b`.  The relator is

  `rel(γ, x, y) = (−1)^{ca} · (γ ·_A u) − (γ ·_B u)`,

where `·_A` multiplies the `X`-component by `f γ` and `·_B` the `Y`-component by `g γ`.  Against a
second single `x' ⊗ y'` with `|x'| = a'`:

* `(γ ·_A u) * (x' ⊗ y') = γ ·_A (u * (x' ⊗ y'))` — **no extra sign**, by associativity in `A`;
* `(γ ·_B u) * (x' ⊗ y') = (−1)^{c a'} · γ ·_B (u * (x' ⊗ y'))` — the cell has to move past `x'`.

So the product of the relator with `x' ⊗ y'` is

  `(−1)^{ca} γ·_A(uw) − (−1)^{ca'} γ·_B(uw) = (−1)^{c a'} · [ (−1)^{c(a+a')} γ·_A(uw) − γ·_B(uw) ]`,

and the bracket is exactly the relator at the product bidegree, whose sign is `(−1)^{c(a+a')}`.
Including the Koszul sign `(−1)^{b a'}` of the product itself:

> **a relator times a single-bidegree element is `(−1)^{(c+b)a'}` times the relator at the
> product.**

So the relations form an ideal, and the product descends — with no condition on the algebras beyond
what is already assumed.

`CDGARelTensorAlgebra.lean` — `tensorAlgMul_sub_left`, **`tensorAlgMul_relTensorRelator`**: that
computation, in Lean.  Substituting the two degree definitions `c + a = α`, `c + b = β` before
touching the signs is what makes it short — otherwise every exponent carries an `α` that has to be
unfolded at each step.  The two associativity rewrites are `A.mul_assoc` and `B.mul_assoc` applied
to `f γ` and `g γ`, which is exactly the content of `restrictModule`'s `act_assoc`.

Axioms: `propext, Classical.choice, Quot.sound`.

**`relTensorRel_tensorAlgMul_left`**, **`relTensorRel_tensorAlgMul_right`**: the relations really
are a two-sided ideal.  The left statement is span induction over the relation submodule, with the
generator case expanding the second factor as a sum of single-bidegree elements and then inducting
on each pure tensor; the right statement is the left one composed with graded commutativity, which
costs only a scalar.

`relAlgMulPre`, `relAlgMulRight`, `relAlgMulLeftPre`, **`relAlgMul`**, and

> **`relTensorCDGA` : the relative tensor product of two algebras over a base algebra is a
> commutative differential graded algebra.**

The descent is two `Submodule.liftQ`s in sequence — first in the second variable at a fixed
representative, then in the first variable, where the quotient map being killed is an equality of
*linear maps* and so is checked by `LinearMap.ext` followed by `Quotient.inductionOn'`.  Every
algebra axiom then follows from the corresponding axiom of `tensorCDGA` by
`Quotient.inductionOn'` on each argument, and `d_mul` is `tensorAlgMul_extTensorD` — the
differential of the quotient being the descent of the same `tensorD`.

Axioms: `propext, Classical.choice, Quot.sound`.

Axioms: `propext, Classical.choice, Quot.sound`.

## Base change and the unit for the relative tensor product of algebras

`CDGARelTensorAlgebraMap.lean` — **`CDGAHom.restrictHom`**,
**`relTensorMapLeft_restrictHom_isQuasiIsoFull`**, **`relTensorCDGAUnit`**.

A morphism of algebras *over the base* — one commuting with the two structure maps — becomes, after
restriction of scalars, a morphism of modules over the base; its `map_act` is the morphism's own
multiplicativity together with that commutation.  So the comparison it induces on relative tensor
products is the module-level comparison in the left variable, and every invariance theorem of the
module layer applies to it, exactly as `zeroActHom` did in the absolute case.  The unit is the class
of `1 ⊗ 1`, both of its laws inherited from the absolute unit by induction on representatives.

The relative algebra layer is therefore complete: product, differential, unit, functoriality, and
base change, all reduced to statements already proved for modules.

Axioms: `propext, Quot.sound` for `restrictHom`; `propext, Classical.choice, Quot.sound` for the
rest.

## Derived base change over a base algebra, instantiated

`CDGARelAlgebraFlat.lean` — **`relTensorMapLeft_restrictHom_freeTower_isQuasiIso`**,
**`relTensorMapLeft_restrictHom_semifree_isQuasiIso`**.

The two flatness theorems of the module layer — a tower of free cells and its colimit — instantiated
at a morphism of algebras over a base algebra.  This is the form the statement takes when a derived
tensor product over the base is computed by a semi-free resolution: tensoring the resolution over
the base with a quasi-isomorphism of algebras over that base is again a quasi-isomorphism.

Nothing new is proved here; the point is that after `restrictHom` the algebra-level statement *is*
the module-level one, so the instantiation is a projection (`.2`) of an already-proved
`IsQuasiIsoFull`.

Axioms: `propext, Classical.choice, Quot.sound`.
