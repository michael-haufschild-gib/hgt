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
