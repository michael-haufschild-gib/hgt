# Geometric Milnor--Witt rank collapse

- **ID:** `deninger-geometric-mw-rank-collapse`
- **Stage:** 2-fully-proven
- **Type:** SOURCE THEOREM
- **Labels:** `DAC_GEOMETRIC_MW_RANK_COLLAPSE`
- **Parent:** `deninger-derived-mw-rational-witt-coefficient`

## Statement

Let \(F\) be an algebraically closed field of characteristic \(0\).  For every
\(n\geq 0\), the forgetful morphism
\[
 F_n:K_n^{MW}(F)\longrightarrow K_n^M(F)
 \tag{1}
\]
is an isomorphism.  More explicitly,
\[
 K_n^{MW}(F)\cong
 \begin{cases}
 \mathbb Z,&n=0,\\
 K_n^M(F),&n>0,
 \end{cases}
 \tag{2}
\]
and under \(K_0^M(F)=\mathbb Z\), \(F_0\) is the rank isomorphism.

Consequently:

1. `(1)` remains an isomorphism after quotienting by torsion or tensoring with
   \(\mathbb R\);
2. any map of connective spectra
   \[
   \mathcal K_F^{MW}\longrightarrow\mathcal K_F^M
   \]
   realizing `(1)` on all homotopy groups is an equivalence;
3. base change along any \(E_\infty\)-algebra map
   \(\mathcal P_F\to\mathcal C_F\) gives an equivalence
   \[
   \mathcal C_F\otimes_{\mathcal P_F}^{\mathbb L}\mathcal K_F^{MW}
   \xrightarrow{\;\sim\;}
   \mathcal C_F\otimes_{\mathcal P_F}^{\mathbb L}\mathcal K_F^M;
   \tag{3}
   \]
4. the connective fiber and derived rank quotient of `(3)` are trivial:
   \[
   \operatorname{Fib}(3)\simeq0,\qquad
   \left(\mathcal C_F\otimes_{\mathcal P_F}^{\mathbb L}\mathcal K_F^{MW}\right)
   \otimes_{\operatorname{Free}_{E_\infty}^{+}(0)}^{\mathbb L}\mathbbm1
   \simeq
   \mathcal C_F\otimes_{\mathcal P_F}^{\mathbb L}\mathcal K_F^M.
   \tag{4}
   \]

The conclusion concerns the untwisted nonnegative diagonal coefficient on a
geometric chart.  It does **not** trivialize twisted Milnor--Witt residues over
non-algebraically-closed arithmetic residue fields.

## Proof

Because \(F\) is algebraically closed, every element of \(F^\times\) has a
square root.  Déglise, Example 2.1.13, proves that for any field \(K\), the
following are equivalent:

- every unit of \(K\) is a square;
- the parity-rank morphism \(W(K)\to\mathbb Z/2\) is an isomorphism.

Thus the fundamental ideal \(I(F)\), the kernel of parity rank, vanishes.

Déglise, Corollary 2.3.7, identifies the Milnor--Witt ring as the cartesian
square
\[
\begin{CD}
K_*^{MW}(F) @>>> K_*^M(F)\\
@VVV              @VVV\\
I^*(F) @>>> \bar I^*(F).
\end{CD}
\tag{5}
\]
Equivalently, Example 2.3.11 specializes this square directly: whenever every
unit is a square,
\[
K_n^{MW}(F)=
\begin{cases}
\mathbb Z,&n=0,\\
\mathbb Z/2,&n<0,\\
K_n^M(F),&n>0.
\end{cases}
\tag{6}
\]
The map in positive degrees in `(6)` is the forgetful map.  In degree zero,
\(K_0^{MW}(F)=GW(F)\); since all one-dimensional forms are isometric and
hyperbolic cancellation leaves rank as the only Grothendieck--Witt invariant,
the forgetful map is \(GW(F)\xrightarrow{\sim}\mathbb Z=K_0^M(F)\).
This proves `(1)` and `(2)`.

Torsion quotient and realification preserve isomorphisms, proving consequence
1.  A map between connective spectra that is an isomorphism on every homotopy
group is an equivalence, proving consequence 2.  Derived base change preserves
equivalences, proving `(3)`.  Its fiber is therefore contractible.  The free
unital \(E_\infty\)-algebra on the zero object is the unit, so `(4)` follows.

## Arithmetic consequence

The local geometric character chart has no nonnegative Milnor--Witt rank
kernel and no degree-one Tor obstruction.  Hence local coefficient construction
must use the ordinary unit-amalgamated algebra
\[
\mathcal C_F^M
=
\mathcal C_F\otimes_{\mathcal P_F}^{\mathbb L}\mathcal K_F^M.
\]

Quadratic orientation data can only survive in parts not covered by the
untwisted geometric calculation:

1. twisted Rost--Schmid residue terms \(K_n^{MW}(\kappa(v),\omega_v)\);
2. Galois descent before passage to algebraic closure;
3. real/archimedean boundary terms.

Therefore a construction that inserts a nontrivial rank quotient separately on
every algebraically closed chart is redundant.  The correct next problem is to
construct a homotopy-coherent global residue/Galois descent system whose
geometric stalk is \(\mathcal C_F^M\) and whose arithmetic specialization maps
retain the Milnor--Witt twists.

## Boundary

This theorem does not prove:

- existence of the global Rost--Schmid descent object;
- compatibility of power maps with twisted residues and transfers;
- the three-term global cohomology calculation;
- Poincaré duality, Lefschetz trace, determinant realization, or positivity.

It removes only the local geometric rank-kernel gate.

## References

- Frédéric Déglise, *Notes on Milnor--Witt K-theory*, Example 2.1.13,
  Corollary 2.3.7, and Example 2.3.11:
  https://arxiv.org/abs/2305.18609
- Fabien Morel, *\(\mathbb A^1\)-Algebraic Topology over a Field*,
  Milnor--Witt \(K\)-theory and the fundamental square.

## Novelty audit

The algebraic identity `(1)` is standard.  The new deduction for this program
is architectural: on Deninger's algebraically closed geometric character
charts, Milnor--Witt refinement and the local derived rank quotient cannot
carry extra nonnegative information.  Quadratic data must be placed in
twisted arithmetic descent rather than in the local geometric stalk.

**Verdict:** `FULLY PROVEN ON PAPER`.

## Lean status

### What landed

`formal/GaloisForLFunctions/RHTower/DeningerQuadraticallyClosedRankCollapse.lean`, 44
declarations, axiom audit for every one of them within
`propext, Classical.choice, Quot.sound` (several need only `propext, Quot.sound`).

**The degree-zero half of `(2)`, completely: `K_0^{MW}(F) = GW(F) ≅ ℤ` by rank.**  The proof input
the card uses is that every unit of `F` is a square; that hypothesis, and nothing about algebraic
closure, is what the formalization carries.

- `deningerIsometryEquivSumSquares`, `deningerIsometryEquivSumSquaresUnits` — the sum-of-squares
  normalization over a field in which every element is a square.  mathlib had this only for
  `IsAlgClosed` fields, with an explicit `TODO: generalize to quadratically closed field` in
  `Mathlib/LinearAlgebra/QuadraticForm/AlgClosed.lean`; that generalization is what these two
  declarations are.
- `deningerEquivalent_standardForm` — every nondegenerate form on a finite-dimensional space is
  isometric to the standard sum of squares of its rank.
- `deningerEquivalent_iff_finrank_eq` — **rank is a complete isometry invariant**, which is the
  card's "all one-dimensional forms are isometric and rank is the only Grothendieck--Witt
  invariant".
- `deningerStandardForm_sum` — orthogonal sum adds ranks; `deningerFormPlus_separatingLeft` — the
  orthogonal sum of nondegenerate forms is nondegenerate.
- `DeningerWittClass`, `deningerClassRank`, `deningerClassRank_bijective` — **the monoid of
  isometry classes of nondegenerate forms is the natural numbers**, with rank as the bijection and
  orthogonal sum as the addition (`deningerClassRank_plus`).
- `deningerGrothendieckWittRank_universal` — **the group completion is `ℤ` with rank as the
  isomorphism**: every additive invariant of nondegenerate forms factors uniquely through the rank
  by a homomorphism from `ℤ`.  This is `F_0 : GW(F) ≅ ℤ = K_0^M(F)`, stated by the universal
  property so that no separate construction of the Grothendieck group is needed.
- `deningerRealificationCongr`, `deningerTorsionQuotientCongr` — **consequence 1**: an isomorphism
  of abelian groups survives tensoring with `ℝ` and survives the quotient by torsion.

Supporting infrastructure that mathlib did not have:

- `deningerSeparatingLeft_iff_polar` — nondegeneracy expressed through the polar form.  This is the
  working form throughout: mathlib's `associated_apply` puts `⅟2` in the endomorphism ring of the
  target, which blocks the ordinary cancellation lemmas, whereas `two_nsmul_associated` moves
  everything to the polar form where two is an honest field element.
- `deningerWeightedSumSquares_separatingLeft` — a weighted sum of squares with nonzero weights is
  nondegenerate.
- `deningerSeparatingLeft_of_equivalent` — nondegeneracy is an isometry invariant.

### What is still missing, and why

- The positive-degree half of `(1)`--`(2)`, `K_n^{MW}(F) ≅ K_n^M(F)` for `n > 0`, needs
  Milnor--Witt K-theory: the graded ring on generators `[u]` and `η` with the Steinberg and
  commutation relations, its fundamental cartesian square `(5)` with the Witt ring and the powers
  of the fundamental ideal, and the forgetful morphism.  Three of those four are now available:
  Milnor `K`-theory in `formal/GaloisForLFunctions/HTGeometry/MilnorKTheory.lean` (`MilnorK`,
  `milnorSymbol`, Steinberg, `{a, -a} = 0`, anticommutativity), and Milnor--Witt `K`-theory with the
  forgetful morphism in `MilnorWittKTheory.lean` — `MilnorWittK` presented by Morel's generators
  `[u]` and `η` and his four relations, with `milnorWittForget` onto `MilnorK` and its surjectivity.
  The Witt ring and its fundamental ideal are now in `WittRing.lean`: `WittRing` presented as the
  group ring of the square classes modulo the two Witt relations, with `wittClass` and its
  multiplicativity, invariance under squares, `⟨a⟩ + ⟨-a⟩ = 0` and `⟨a⟩ + ⟨b⟩ = ⟨a+b⟩ + ⟨ab(a+b)⟩`;
  `wittDim` the dimension modulo two; and `fundamentalIdeal` its kernel, whose powers
  `fundamentalIdeal F ^ n` are then available.  So all four ingredients of `(5)` can now be written
  down, and the filtration is identified: `fundamentalIdeal_eq_span` proves the fundamental ideal is
  generated by the one-fold Pfister forms `⟨⟨a⟩⟩ = ⟨1⟩ - ⟨a⟩`, which is what makes `I^n` the Pfister
  filtration the square compares against, and `pfisterOne_mul_sub_mem_sq` proves the degree-one
  comparison map itself: `⟨⟨ab⟩⟩ - ⟨⟨a⟩⟩ - ⟨⟨b⟩⟩` lies in `I²`, so `a ↦ ⟨⟨a⟩⟩` is additive modulo
  `I²`, which is the `n = 1` case of the map `K_n^M(F) → I^n/I^{n+1}` in the square.
  `pfisterOne_mul_oneSub` proves the Steinberg relation on the Witt side — the two-fold Pfister form
  `⟨⟨a, 1-a⟩⟩` is zero, not merely in `I³` — and `pfisterOne_mul_neg_self` is the counterpart of
  `{a, -a} = 0`.  So both Milnor relations are now known to hold for `a ↦ ⟨⟨a⟩⟩`.  Consequently
  `MilnorWittWittComparison.lean` builds `milnorWittToWitt`, the ring map `K^{MW}(F) → W(F)` sending
  `[u]` to `⟨⟨u⟩⟩` and `η` to `-1`; with `milnorWittForget` this gives **both** maps out of
  Milnor--Witt `K`-theory in the square, and `milnorWittToWitt_symbol_mem` says the symbols land in
  the fundamental ideal.  `milnorFirstMap` is the degree-one bottom edge `Fˣ → I/I²`, a monoid
  homomorphism because the Pfister form is additive modulo `I²`, and `square_commutes_on_symbol`
  together with `square_forget_on_symbol` say the two composites of the square agree on symbols.
  In higher degrees, `pfisterList` is the `n`-fold Pfister form, `pfisterList_mem` places it in
  `I^n`, `pfisterList_steinberg` proves it vanishes when two consecutive entries are `a` and `1-a`,
  and `pfisterList_mul_slot` proves additivity in the leading slot modulo `I^{n+1}` — jointly the
  well-definedness of the degree-`n` comparison map on the defining relations of Milnor
  `K`-theory.  `pfisterList_perm` makes the form depend only on the multiset of its entries, which
  upgrades both to arbitrary slots and positions (`pfisterList_eq_zero_of_perm`,
  `pfisterList_mul_slot_perm`) — the form the relations of `K_n^M` are actually stated in.
  Milnor `K`-theory is graded-commutative while the Pfister form is genuinely commutative, and
  `pfisterList_add_perm_mem` reconciles the two: twice a form already lies in `I^{n+1}`, because `2`
  is the one-fold Pfister form `⟨⟨-1⟩⟩`, so the transposition sign is invisible there.  With slot
  additivity and Steinberg this is the complete list of relation checks a degree-`n` comparison map
  must satisfy.  `pfisterList_mul_middle` and `pfisterList_steinberg_middle` restate the two of them
  at an interior position, which is literally the shape the multilinearity and Steinberg relations of
  `K_n^M` are written in.  `pfisterLift` is the resulting additive map on formal sums of symbols,
  and `pfisterLift_kills_relations` proves both relation families lie in its kernel — so the
  assignment `{a₁,…,aₙ} ↦ ⟨⟨a₁,…,aₙ⟩⟩ mod I^{n+1}` descends to any quotient of the free abelian
  group on symbols by the defining relations of Milnor `K`-theory.  `MilnorKDeg` is that quotient in
  degree `n` — formal sums of symbols of length exactly `n` (`MilnorSymbolDeg`) modulo the
  degree-`n` relations — and `milnorPfisterMap` is **the degree-`n` comparison map itself**,
  `K_n^M(F) → W(F)/I^{n+1}`, with `milnorPfisterMap_class` computing it on symbols.  `square_commutes` proves the square **commutes**
  on products of symbols in every degree: both routes produce the Pfister form of the same list.

  Beyond the maps, the objects themselves are now computed and structured.  `milnorDegZeroEquiv`
  is **`K_0^M(F) ≅ ℤ`** and `milnorDegOneEquiv` is **`K_1^M(F) ≅ Fˣ`**; in degree zero there is one
  symbol and no relations at all, in degree one the Steinberg relations are vacuous and
  multilinearity is the multiplicativity of the unit group.  `milnorMul` is the **graded product**
  `K_m^M(F) × K_n^M(F) → K_{m+n}^M(F)` given by concatenation of symbols, descended through both
  relation subgroups — the relations survive a prefix and a suffix, at the shifted and at the same
  slot respectively — and `pfisterList_append` makes the comparison map multiplicative for it.
  `milnorPairClass_anticomm` proves **`K_*^M(F)` is graded-commutative**: transposing two adjacent
  entries negates the class, via `milnorPairClass_neg_self` (`{a, -a} = 0` at adjacent slots).
  `WittGraded` is the honest bottom right corner `Ī^n = I^n/I^{n+1}`, realized as the image of
  `I^n` in `W(F)/I^{n+1}`, and `milnorGradedMap` is the bottom edge `K_n^M(F) → Ī^n` itself;
  `wittGradedVal_injective` and `wittGradedVal_comp` say the earlier coarse map
  `K_n^M(F) → W(F)/I^{n+1}` is exactly this one followed by an inclusion.

  **The card's quadratic hypothesis is now discharged in the Witt ring.**
  `QuadraticallyClosedWittRing.lean` proves that when every element of `F` is a square every Witt
  class of a unit is the ring unit, hence every one-fold Pfister form is zero, hence — since the
  fundamental ideal is generated by those forms — `fundamentalIdeal_eq_bot`: `I(F) = 0`.  So
  `fundamentalIdeal_pow_eq_bot` collapses the whole Pfister filtration, `wittRingEquivZMod2` is
  **`W(F) ≅ ℤ/2` with the dimension modulo two as the isomorphism** — Déglise's Example 2.1.13, the
  input the card's proof actually uses — and `wittGraded_subsingleton` gives `Ī^n = 0` for `n ≥ 1`.
  Consequently `milnorGradedMap_eq_zero` and `milnorPfisterMap_eq_zero`: the bottom edge of `(5)`
  is the zero map in every positive degree, and `milnorWittToWitt_symbol_eq_zero` says the
  Milnor--Witt symbols die in the Witt ring.  This is the entire quadratic content of the card's
  proof.

  **`(1)` and `(2)` are now proved.**  `mwForgetEquiv` is the isomorphism
  `K_n^{MW}(F) ≅ K_n^M(F)` for every `n ≥ 0` over a quadratically closed field, and with the
  degree-zero and degree-one computations of Milnor `K`-theory, `mwForgetEquivZero` and
  `mwForgetEquivOne` are `K_0^{MW}(F) ≅ ℤ` and `K_1^{MW}(F) ≅ Fˣ`.  The route is described in the
  log below; it does not use the cartesian square, which remains Morel's theorem and is not needed
  for the card's statement.
- Consequences 2, 3 and 4 are statements about connective spectra, `E_∞`-algebra base change and
  derived tensor products.  mathlib has no spectra, no `E_∞`-algebras and no derived categories, so
  `(3)` and `(4)` cannot be stated.

So the card stays at stage 2, and now for exactly one reason: consequences 2, 3 and 4 cannot be
*stated* in Lean, because mathlib has no spectra, no `E_∞`-algebras and no derived tensor products.
Everything else on the card is formalized — `(1)`, `(2)`, the full three-case computation `(6)`, and
consequence 1.

### Log

- 2026-08-02 — Formalized the degree-zero rank isomorphism and consequence 1, generalizing
  mathlib's algebraically-closed sum-of-squares classification to quadratically closed fields.

- 2026-08-03 — Milnor `K`-theory built (see `MilnorKTheory.lean`), removing one of the two named
  blockers for `(5)`.  The Witt ring and the Milnor--Witt generators remain.
- 2026-08-03 — Built Milnor--Witt `K`-theory by Morel's presentation and the forgetful morphism onto
  Milnor `K`-theory.  Killing `η` collapses twisted multiplicativity `[uv] = [u] + [v] + η[u][v]` to
  ordinary additivity, which is exactly the Milnor relation, so the morphism exists on the
  presentation and is surjective.  Two of the card's four named missing ingredients for `(5)` are now
  present; the Witt ring and the fundamental ideal are not.
- 2026-08-03 — Built the Witt ring of a field and its fundamental ideal, the last of the card's four
  named missing ingredients for `(5)`.  The presentation is the group ring of the square classes
  modulo the two Witt relations; the first Witt relation costs nothing because invariance under
  squares is already the group quotient.  The dimension modulo two descends because each relation has
  equally many generators on both sides, and its kernel is the fundamental ideal.  All four
  ingredients of `(5)` are now statable; what remains is Morel's theorem, which is mathematics rather
  than infrastructure.
- 2026-08-03 — Identified the fundamental ideal: it is generated by the one-fold Pfister forms.  The
  argument is that every Witt class is an integer multiple of the unit class modulo those forms, and
  an even-dimensional class forces that integer to be even, while twice the unit class is itself a
  one-fold Pfister form.  So `I^n` is the Pfister filtration and not merely an abstract ideal power.
- 2026-08-03 — Proved the exact identity `⟨⟨ab⟩⟩ = ⟨⟨a⟩⟩ + ⟨⟨b⟩⟩ - ⟨⟨a⟩⟩⟨⟨b⟩⟩`, which needs only
  that the class of `1` is the ring unit and that classes multiply.  Its correction term is a product
  of two elements of the fundamental ideal, so the one-fold Pfister form is additive modulo `I²`:
  the degree-one comparison map of the cartesian square exists.  Higher degrees need the Steinberg
  relation to land in `I^{n+1}`, which is Pfister's theorem.
- 2026-08-03 — Proved the Steinberg relation on the Witt side: `⟨⟨a⟩⟩⟨⟨1-a⟩⟩ = 0`.  It is the second
  Witt relation applied to the pair `a`, `1 - a`, whose sum is `1`, so the correction term cancels
  exactly; this is stronger than the `I³` membership the comparison map needs.  Also `⟨⟨a⟩⟩⟨⟨-a⟩⟩ = 0`,
  using that `-a²` and `-1` are the same square class.  Both Milnor relations therefore hold for the
  Pfister assignment, which is the input the degree-two comparison map needs.
- 2026-08-03 — Built the comparison `K^{MW}(F) → W(F)`.  All four of Morel's relations check: the
  Steinberg and hyperbolic ones are the Witt-side theorems proved in the previous two cycles, and the
  sign in `⟨⟨uv⟩⟩ = ⟨⟨u⟩⟩ + ⟨⟨v⟩⟩ - ⟨⟨u⟩⟩⟨⟨v⟩⟩` is what forces `η` to go to `-1` rather than `+1`.
  Both maps out of Milnor--Witt `K`-theory in the square now exist; what does not is that the square
  commutes with the two maps into `I^n/I^{n+1}` in every degree, and that it is cartesian.
- 2026-08-03 — Built the degree-one bottom edge of the square as a monoid homomorphism `Fˣ → I/I²`
  and checked that the square commutes on symbols.  So in degree one every edge of `(5)` exists and
  the square commutes; what is unavailable in higher degrees is the graded pieces of Milnor and
  Milnor--Witt `K`-theory, which this presentation does not carry, and cartesianness, which is
  Morel's theorem.
- 2026-08-03 — Built the `n`-fold Pfister form and proved the two facts a degree-`n` comparison map
  needs: it vanishes on the Steinberg relation, and it is additive in a slot modulo one further power
  of the fundamental ideal.  Indexing by lists rather than by `Fin n` keeps both proofs to a single
  induction.  What is still absent is the graded pieces of Milnor `K`-theory themselves — this
  presentation is the ungraded tensor-algebra quotient, so `K_n^M` is not an object here — and
  cartesianness.
- 2026-08-03 — Proved the n-fold Pfister form depends only on the multiset of its entries, since the
  Witt ring is commutative, and used that to lift the Steinberg vanishing and the slot additivity from
  the leading entry to arbitrary positions.  The relations of `K_n^M` are stated slotwise, so this is
  the form they need.  What is still missing is `K_n^M` as an object: this presentation is the
  ungraded tensor-algebra quotient, and defining the graded pieces directly by generators and
  relations is the next construction.
- 2026-08-03 — Closed the relation-check list for the degree-`n` comparison map.  The one I had not
  accounted for is the sign: Milnor `K`-theory is graded-commutative, so a transposition negates a
  symbol, whereas the Pfister form is permutation-invariant.  These agree modulo `I^{n+1}` because
  `2 = ⟨⟨-1⟩⟩` lies in the fundamental ideal, so twice any `n`-fold form lies in `I^{n+1}`.  All three
  relations of `K_n^M` — slot additivity, Steinberg, and the sign — are now verified for the Pfister
  assignment.
- 2026-08-03 — Restated the two defining relations at an interior slot, using that moving an entry
  to the front is a permutation.  Every relation of `K_n^M` is now verified for the Pfister
  assignment in exactly the form the definition states it, so constructing `K_n^M` as a quotient and
  descending the map is mechanical.  Also surveyed the rest of the folder: every other card's
  remaining gap is open research or a mathlib-scale absence (derived categories, stacks, spectra,
  coherent sheaves, log geometry, complete locally convex spaces, motivic cohomology), so this is the
  only concretely buildable line left in it.
- 2026-08-03 — Built the comparison map itself on formal sums of symbols and proved both defining
  relation families lie in its kernel.  The map into `W(F)/I^{n+1}` is therefore well defined on any
  presentation of `K_n^M` as the free abelian group on symbols modulo multilinearity and Steinberg.
  What is not built is a chosen such presentation as a named object, which is bookkeeping rather than
  mathematics; cartesianness of `(5)` remains Morel's theorem.
- 2026-08-03 — Named `K_n^M` as a quotient and descended the map, completing the bottom edge of `(5)`
  in every degree.  The degree has to sit in the relation subgroup rather than in the generators:
  multilinearity only holds within a fixed degree while the target `W(F)/I^{n+1}` varies with it, so
  the relations are filtered by degree and the generators are left unrestricted.  Every object and
  every edge of `(5)` now exists; what remains is that the square is cartesian, which is Morel's
  theorem.
- 2026-08-03 — Proved the fundamental square commutes on products of symbols in every degree.  Down
  then project, and across then compare, both give the Pfister form of the same list, so the two
  routes agree on the elements that generate.  Every object and every edge of `(5)` exists and the
  square commutes; what remains is that it is cartesian, which is Morel's theorem and not a
  construction.
- 2026-08-03 — Corrected `MilnorKDeg`.  It had been defined on symbols of *every* length modulo the
  degree-`n` relations, which relates only the length-`n` symbols and therefore is not `K_n^M`;
  calling it that was an overstatement.  Rebuilt it on the subtype of length-`n` symbols, with the
  length bookkeeping that makes the relation constructors typecheck.  The comparison map and the
  commutativity of the square carry over unchanged, since both rest on the `pfisterList` lemmas
  rather than on the generating set.
- 2026-08-03 — With the corrected object, computed the first Milnor `K`-group: `milnorDegOneHom` is
  the comparison `K_1^M(F) → Additive Fˣ`.  In degree one the Steinberg relations are vacuous —
  their index condition forces a list of length `-1` — and multilinearity is exactly the
  multiplicativity of the unit group, so the map is well defined and is the identity on symbols.
  The section is `milnorDegOneInv`, built from `milnorClassDeg_one_mul` — the multilinearity
  relation read in the quotient — and `milnorDegOneHom_surjective` records that `K_1^M(F)` surjects
  onto the unit group with that explicit section.
- 2026-08-03 — Built the section of the degree-one comparison.  The instance failure of the previous
  cycle was self-inflicted: `map_sub` will not rewrite under a bundled quotient hom applied to a
  difference, but building the goal up with `← map_sub` from the split form matches.  Injectivity followed by
  induction over the free abelian group, giving `milnorDegOneEquiv`: **`K_1^M(F) ≅ Fˣ`**, the first
  Milnor `K`-group computed.  This is the degree-one corner of the card's `(1)`--`(2)` on the Milnor
  side, and it is a theorem about the object rather than another map out of it.
- 2026-08-03 — Computed the zeroth Milnor `K`-group, `milnorDegZeroEquiv : K_0^M(F) ≅ ℤ`.  Both
  relation families are vacuous in degree zero — their index conditions ask for a list of negative
  length — and there is exactly one symbol, the empty one, so the group is free of rank one on it.
  With the previous cycle's `K_1^M(F) ≅ Fˣ` this is the whole low-degree corner of `(2)` on the
  Milnor side.
- 2026-08-03 — Discharged the card's quadratic hypothesis inside the Witt ring.  Over a field in
  which every element is a square the square classes are trivial, so every `⟨a⟩` is the ring unit,
  every one-fold Pfister form is zero, and the fundamental ideal — which those forms generate —
  vanishes.  Hence `W(F) ≅ ℤ/2` by dimension modulo two, the Pfister filtration collapses, and the
  bottom edge of `(5)` is zero in every positive degree.  This is Déglise's Example 2.1.13, the
  input the card's own proof cites, and it is now unconditional in Lean.
- 2026-08-03 — Built the honest bottom right corner of `(5)`.  The square's corner is the graded
  piece `Ī^n = I^n/I^{n+1}`, not the coarser `W(F)/I^{n+1}` the earlier comparison map targeted;
  realizing it as the image of `I^n` in `W(F)/I^{n+1}` makes the comparison with the coarse map an
  inclusion, so nothing is lost and the refined map is the unique lift.  A submodule-quotient model
  fails here for an instance reason: `HasQuotient` will not unify the `Submodule` built from the
  `RingQuot` instance path with the one its own instance builds.
- 2026-08-03 — Gave `K_*^M` its product.  Concatenation of symbols descends through both relation
  subgroups because a multilinearity or Steinberg relation stays one after a prefix (at the shifted
  slot) or a suffix (at the same slot); stating the two class-level relations up to an equality of
  lists is what makes the reassociation free.  The comparison map is multiplicative for it, since
  the Pfister form of a concatenation is the product of the Pfister forms.
- 2026-08-03 — Proved `K_*^M(F)` is graded-commutative.  The classical argument — expand
  `{ab, -(ab)} = 0` and cancel the diagonal terms `{a,-a}` and `{b,-b}` — goes through verbatim at
  two adjacent slots inside a longer symbol, once multilinearity and Steinberg are available
  slotwise.  So the presentation by symbols of fixed length carries the full graded-ring structure
  of Milnor `K`-theory, not just its additive one.
- 2026-08-03 — Proved `K^{MW}(F)/(η) ≅ K^M(F)` (`MilnorWittEtaQuotient.lean`).  The forgetful
  morphism kills `η`, and killing `η` is *all* it does: quotienting Milnor--Witt `K`-theory by the
  single relation `η = 0` gives Milnor `K`-theory on the nose, because twisted multiplicativity
  `[uv] = [u] + [v] + η[u][v]` collapses to additivity of the symbol exactly then.  The inverse is
  built by extending `a ↦ [a]` over the tensor algebra — additivity holds in the quotient, and the
  Steinberg relation is the same on both sides.  `milnorWittForget_eq_zero_iff` records that the
  kernel of the forgetful morphism is exactly what dies in that quotient.  This is the ungraded
  form of Morel's `K_n^{MW}/η ≅ K_n^M`.
- 2026-08-03 — **Proved `⟨a²⟩ = 1` in Milnor--Witt `K`-theory** (`MilnorWittFormIdentities.lean`),
  unconditionally from Morel's four relations, and with it `η[u] = 0` for every unit of a
  quadratically closed field.  The chain is: `η` is central (induction over the free algebra);
  twisted multiplicativity with a unit entry gives `[1] + η[1][b] = 0` for every `b`, and feeding
  `b = -1` into the hyperbolic relation leaves `η[1] = 0`, hence `[1] = 0` and `⟨1⟩ = 1`, so every
  `⟨a⟩` is a unit with inverse `⟨a⁻¹⟩`; the inverse law turns `[a][1-a⁻¹]` into two Steinberg
  products, so it vanishes; then `(-a)(1-a⁻¹) = 1-a` makes `[a][-a]` annihilated by the unit
  `⟨1-a⁻¹⟩`, so `[a][-a] = 0`; and `η²[a][-a] = (⟨a⟩-1)(⟨-a⟩-1)` expands, using
  `⟨a⟩ + ⟨-a⟩ = 1 + ⟨-1⟩` (the hyperbolic relation read through the forms), to
  `⟨-1⟩⟨a²⟩ = ⟨-1⟩`; `⟨-1⟩` is a unit.  This is Morel's `K_0^{MW}(F) = GW(F)` content that the
  card's degree-zero statement needs, and it is the algebraic counterpart of
  `fundamentalIdeal_eq_bot` on the Witt side.

  **This isolates exactly what is left of `(1)`--`(2)`.**  With `η[u] = 0` for every unit, every
  generator `η^k[a_1]⋯[a_{n+k}]` of `K_n^{MW}(F)` with `k ≥ 1` and `n ≥ 1` contains a symbol, hence
  vanishes; so `K_n^{MW}(F)` is generated by the `k = 0` words, twisted multiplicativity becomes
  Milnor multiplicativity (its `η`-correction is a `k = 1` word), the hyperbolic relation is
  vacuous, and `K_n^{MW}(F) ≅ K_n^M(F)`; in degree zero the same argument leaves the empty word and
  `ℤ`.  The one missing object is `K_*^{MW}` **as a `ℤ`-graded ring** — generators `η^k[l]` indexed
  by `(l.length : ℤ) - k`, the three homogeneous relation families (Steinberg, twisted
  multiplicativity with its degree-shifted correction, and the hyperbolic relation), and
  concatenation as the product.  `η` sits in degree `-1`, so the grading must be by `ℤ`, and the
  derivation above must be replayed there because it multiplies across degrees.  That construction
  is the next step; nothing in it is open research.
- 2026-08-03 — Built `K_*^{MW}` as a `ℤ`-graded ring (`MilnorWittGraded.lean`): words `η^k[l]`
  indexed by their degree `(l.length : ℤ) - k`, the three homogeneous relation families, and
  concatenation as the product, descended through both relation subgroups.  Two bookkeeping points
  made it work.  The relation families carry their degree witnesses as existential arguments, so a
  relation instance is produced by naming the witnesses rather than by re-deriving arithmetic; and
  the class-level relations are stated up to equalities of *both* the lists and the `η`-exponents,
  because a prefix shifts `k + (j+1)` (definitionally `(k+j)+1`) while a suffix shifts
  `(j+1) + k`, which is not definitional.  `rw` cannot see through the concatenation of words, so
  the twisted-multiplicativity cases close by `Eq.trans ?_ (add_assoc _ _ _)` and `exact`, which
  unify up to definitional equality.  What remains for `(1)`--`(2)` is to replay the
  `⟨a²⟩ = 1` derivation in this graded ring and read off `K_n^{MW}(F) ≅ K_n^M(F)`.
- 2026-08-03 — Replayed the `⟨a²⟩ = 1` derivation inside the graded ring and **proved the card's
  `(1)` and `(2)`**: `mwForgetEquiv` is `K_n^{MW}(F) ≅ K_n^M(F)` for every `n ≥ 0` over a
  quadratically closed field, `mwForgetEquivZero` is `K_0^{MW}(F) ≅ ℤ`, `mwForgetEquivOne` is
  `K_1^{MW}(F) ≅ Fˣ`.

  The derivation needed two operations rather than the full product: multiplication by `η`, which
  raises the `η`-exponent of a word, and multiplication by a single symbol, which appends to it.
  Both send relations to relations, and giving each a target degree fixed by an *equation* rather
  than computed is what lets them compose without coercions between `n - 1` and the degree one is
  working in.  Every relation is then stated at an interior slot, because that is the form the
  derivation uses them in: `[1] + η[1][b] = 0` at a slot, then `η[1] = 0` (feed `b = -1` into the
  hyperbolic relation), then `[1] = 0`, the inverse law, `[a][1-a⁻¹] = 0`, and `[a][-a] = 0` — the
  last by showing `[a][-a]` is annihilated by `1 + η[1-a⁻¹]` and that the inverse law makes that
  factor a unit.  In degree zero these give `η[ab] = η[a] + η[b] + η²[a][b]`,
  `η[a] + η[-a] = η[-1]`, and finally `η[a²] = 0`.

  The collapse is then immediate and needs no cartesian square: over a quadratically closed field
  every unit is a square, so `η` kills every symbol, so every word `η^k[a_1]⋯[a_m]` with `k ≥ 1` and
  `m ≥ 1` vanishes.  The forgetful map — kill every word with an `η` — is well defined
  unconditionally, its inverse is well defined because the `η`-correction of twisted
  multiplicativity is such a word, and the two composites are the identity because in every degree
  `n ≥ 0` a word with `k ≥ 1` has `m = n + k ≥ 1`.  So the card's `(1)`--`(2)` hold, and what is
  still absent is only the *cartesianness* of `(5)`, which the card's statement does not need.
- 2026-08-03 — Completed `(6)`, the three-case computation quoted from Déglise's Example 2.3.11:
  `mwNegDegreeEquiv` is **`K_n^{MW}(F) ≅ ℤ/2` for every `n < 0`** over a quadratically closed field.
  In a negative degree every word `η^k[a_1]⋯[a_m]` has `k = m - n > 0`, so every word carrying a
  symbol already vanishes and only the powers of `η` survive; the hyperbolic relation, applied with
  empty prefix and suffix, says twice such a power is zero.  What makes the group exactly `ℤ/2`
  rather than a quotient of it is the parity invariant `mwRankMod2` — one for a pure power of `η`,
  zero as soon as a symbol occurs — which descends in *every* degree: the Steinberg and twisted
  relations only involve words carrying a symbol, and the two `η`-powers of the hyperbolic relation
  cancel modulo two.  It takes the value one on the generator, so the generator is not zero.

  With this the card's own mathematical content is fully formalized: `(1)`, `(2)`, `(6)` in all
  three cases, and consequence 1.  Consequences 2, 3 and 4 are statements about connective spectra,
  `E_∞`-algebra base change and derived tensor products; mathlib has none of those objects, so they
  cannot be written down, let alone proved.  Cartesianness of `(5)` remains Morel's theorem, and the
  card's statement does not use it.
