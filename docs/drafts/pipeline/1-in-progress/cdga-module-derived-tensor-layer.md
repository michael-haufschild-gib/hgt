# CDGA-module derived tensor layer

- **Stage:** 1-in-progress
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
