# Two-term real Milnor amplitude on Deninger's algebraic character field

- **ID:** `deninger-algebraic-cyclotomic-milnor-amplitude`
- **Stage:** 2-fully-proven
- **Type:** SOURCE THEOREM
- **Labels:** `DAC_ALGEBRAIC_CYCLOTOMIC_MILNOR_AMPLITUDE`
- **Parent:** `deninger-derived-mw-rational-witt-coefficient`

## Statement

Let \(F/\mathbb Q\) be an algebraic field extension.  Then
\[
 K_q^M(F)\otimes_{\mathbb Z}\mathbb R=0
 \qquad(q\geq2).                                                       \tag{1}
\]
Therefore the real diagonal Milnor algebra, and hence the chartwise
derived-global-section comparison after unit amalgamation, has homotopy only
in degrees zero and one:
\[
 \pi_q\mathcal K_{F,\mathbb R}^M
 =
 \begin{cases}
 \mathbb R,&q=0,\\
 F^\times\otimes_{\mathbb Z}\mathbb R,&q=1,\\
 0,&q\geq2.
 \end{cases}                                                          \tag{2}
\]

If \(F\) contains \(\mu_\infty\), then torsion disappears in degree one and
\[
 F^\times\otimes\mathbb R
 \cong
 (F^\times/\mu_\infty)\otimes\mathbb R.                               \tag{3}
\]
Combining `(1)` with `DAC_CHARACTER_SHAPE_FORMALITY` gives
\[
 \mathcal C_{F,\mathbb R}^M
 :=
 C^*_{\mathrm{sh}}(X_F;\mathbb R)
 \otimes_{\mathcal P_{F,\mathbb R}}^{\mathbb L}
 \mathcal K_{F,\mathbb R}^M
 \simeq
 H\!\left(
   \mathbb R\oplus
   \Sigma_{\mathrm{ar}}\bigl((F^\times/\mu_\infty)\otimes\mathbb R\bigr)
 \right),                                                             \tag{4}
\]
where every product of two positive-degree classes is zero.

For Deninger's permitted choice \(F=\overline{\mathbb Q}\), the
Milnor--Witt comparison is also an integral isomorphism in nonnegative degree
by `DAC_GEOMETRIC_MW_RANK_COLLAPSE`.  Thus `(4)` is simultaneously the real
ordinary and geometric MW stalk.

## Proof

For any field \(E\), diagonal motivic cohomology is Milnor \(K\)-theory:
\[
 H_M^{q,q}(\operatorname{Spec}E,\mathbb Q)
 \cong K_q^M(E)\otimes\mathbb Q.                                      \tag{5}
\]
Equivalently, under the Adams decomposition,
\[
 H_M^{m,n}(\operatorname{Spec}E,\mathbb Q)
 \cong
 \bigl(K_{2n-m}(E)\otimes\mathbb Q\bigr)^{(n)}.                        \tag{6}
\]

Gallauer's Vanishing Hypothesis 6.6 includes
\[
 H_M^{m,n}(\operatorname{Spec}E,\mathbb Q)=0
 \quad\text{when }n\geq m\geq2.                                      \tag{7}
\]
His Remark 6.8 proves `(7)` for every algebraic extension of
\(\mathbb Q\): finite number fields satisfy it by Borel's computation of
rational algebraic \(K\)-theory and arbitrary algebraic extensions follow by
continuity over their finite subextensions.

Set \(m=n=q\geq2\) in `(7)` and use `(5)`.  This gives
\[
 K_q^M(F)\otimes\mathbb Q=0.
\]
Tensoring further with \(\mathbb R\) proves `(1)`.  The identities
\(K_0^M(F)=\mathbb Z\) and \(K_1^M(F)=F^\times\) prove `(2)`.
Every root of unity is torsion, and tensoring with \(\mathbb R\) kills torsion,
which proves `(3)`.

`DAC_CHARACTER_SHAPE_FORMALITY` identifies the real shape cochain algebra
with the free real \(E_\infty\)-algebra on
\((F^\times/\mu_\infty)\otimes\mathbb R\) in arithmetic degree one.  Derived
base change along this equivalence identifies the unit-amalgamated algebra
with \(\mathcal K_{F,\mathbb R}^M\).  Equations `(1)`--`(3)` give `(4)`.
Since its degree-two homotopy vanishes, every product of two degree-one
classes vanishes.

## Arithmetic consequence

This theorem gives a non-arbitrary source of cohomological dimension:

1. the corrected chartwise real derived-section algebra on Deninger's
   algebraic character cover has amplitude \([0,1]\);
2. a Rost--Schmid resolution over the regular arithmetic curve
   \(\operatorname{Spec}\mathbb Z\) has residue length one;
3. its total finite coefficient complex can therefore have amplitude
   \([0,2]\), once the actual two-column sheaf resolution is proved acyclic.

No Postnikov truncation is needed for this **geometric Milnor channel**.  A
separate qualification is forced at the real boundary: full realified
Milnor--Witt theory has a signature survivor in every sufficiently positive
weight.  The global arithmetic theory must therefore use the source-natural
arithmetic-curve signature window of
`DAC_ARITHMETIC_ROST_SCHMID_SIGNATURE_RESOLUTION`, retaining its degree-two
orientation without adjoining the entire higher signature tower.  The three
potential geometric/residue terms have source meaning:
\[
\begin{array}{c|c}
\text{total degree}&\text{source}\\ \hline
0&\text{constant rank}\\
1&\text{character-unit classes and generic-to-closed residues}\\
2&\text{closed-point residue cokernel / arithmetic trace}.
\end{array}
\]

This is not yet a sheaf-level amplitude theorem.
`DAC_SHEAFIFIED_UNIT_AMALGAMATION_COMPARISON` must first identify these
chartwise derived sections with the sheafified coefficient over Deninger's
\(\mathcal R_X\).  To pass from that sheaf complex to a three-term global
complex one must then prove the two-column acyclicity theorem.

## Hostile audit

- The theorem uses that Deninger's character field is algebraic over
  \(\mathbb Q\).  It fails for general characteristic-zero fields of positive
  transcendence degree, where real higher Milnor groups can be nonzero.
- It does not identify Galois invariants of the degree-one unit space.
- It does not prove that derived global sections commute with sheafified unit
  amalgamation.
- It does not imply that the global middle cohomology is finite-dimensional;
  topology of the rational-Witt flow space and its noncompact completion can
  make it infinite-dimensional.
- A two-term stalk plus a one-step residue complex bounds the internal
  coefficient degree.  Hypercohomology can exceed degree two unless the
  coefficient sheaves are acyclic for global sections.
- This theorem does not truncate the real Milnor--Witt signature tower on an
  arithmetic base.  Déglise--Feld--Jin's arithmetic calculation shows that a
  separate weight-one signature window is necessary.
- The flow remains a commuting action on the residue complex.  It is not used
  as a cohomological differential.

## References

- Martin Gallauer, *tt-geometry of Tate motives over algebraically closed
  fields*, equations (3.3)--(3.4), Hypothesis 6.6, Remarks 6.7--6.8:
  https://arxiv.org/abs/1708.00834
- Armand Borel, rational algebraic \(K\)-theory of number fields.
- Yury Nesterenko--Andrei Suslin and Burt Totaro, identification of diagonal
  motivic cohomology with Milnor \(K\)-theory.
- Christopher Deninger, *Dynamical systems for arithmetic schemes*, §2:
  the permitted radically closed Galois field can be
  \(\overline{\mathbb Q}\):
  https://arxiv.org/abs/1807.06400

## Novelty audit

The motivic vanishing is standard.  New deduction for this program is that
Deninger's algebraic character-field choice converts the full
Kucharczyk--Scholze Milnor correction into a canonical real two-term
geometric coefficient.  Combined with arithmetic-curve residue length one,
it explains the finite part of the expected \(0,1,2\) range without assuming
a finite-dimensional foliation.  Archimedean Milnor--Witt signature requires
the separate source-natural window identified above.

**Verdict:** `FULLY PROVEN ON PAPER`.

## Lean status

### What landed

`formal/GaloisForLFunctions/RHTower/DeningerMilnorAmplitude.lean`.  Axiom audit for all 5
declarations: `propext, Classical.choice, Quot.sound`.

- `deningerTorsion_tmul_real_eq_zero`, `deningerTorsionTensorReal_eq_zero`,
  `deningerRealification_torsionQuotient_bijective`, `deningerRealificationTorsionEquiv` —
  **`(3)`**: realification is insensitive to torsion.  A torsion element tensored with a real
  number vanishes because the annihilating integer is invertible on `ℝ`; hence the torsion
  submodule realifies to zero, and right exactness of the tensor product makes the quotient map by
  the torsion an isomorphism after `⊗ ℝ`.  Applied to `F^×`, whose torsion is exactly the roots of
  unity, this is `F^× ⊗ ℝ ≅ (F^×/μ_∞) ⊗ ℝ`.
- `deningerGradedDegreeOne_mul_eq_zero` — the closing assertion of `(4)`: in a graded algebra whose
  degree-two part vanishes, the product of two degree-one classes is zero, because it lands in
  degree two.  This is the square-zero structure that the two-term amplitude produces.

### What cannot be stated in Lean, and why

`(1)` and `(2)` are not formalized.  Half of the stated reason is now removed: Milnor `K`-theory is
built in `formal/GaloisForLFunctions/HTGeometry/MilnorKTheory.lean` — `MilnorK` as the tensor
algebra on `Fˣ` modulo Steinberg, with `milnorSymbol` and its additivity, the Steinberg relation
`milnorSymbol_mul_oneSub`, `{a, -a} = 0`, and anticommutativity `{a, b} = -{b, a}`.  So `K_q^M` can
now be written down.  What remains missing is motivic cohomology, so `H_M^{q,q}` still cannot be
stated.
Independently of that, `(1)` is not proved on this card — it is imported from Gallauer's Remark 6.8
together with Borel's computation of the rational algebraic `K`-theory of number fields, and
formalizing Borel's theorem is a research-scale project of its own.  `(4)` as an equivalence of
`E_∞`-algebras needs the same missing infrastructure as
`DAC_CHARACTER_SHAPE_FORMALITY` (no `E_∞`/CDGA homotopy theory in mathlib).

The card therefore stays at stage 2: its two statable algebraic ingredients are proved and audited,
its headline vanishing remains an import.

- 2026-08-03 — Built Milnor `K`-theory, which this card and `deninger-geometric-mw-rank-collapse`
  both named as a reason their statements could not be written down.  The ring is the tensor algebra
  on the unit group modulo the Steinberg relation, so the symbol is additive by construction; the
  classical consequences `{a, -a} = 0` and `{a, b} = -{b, a}` follow from Steinberg applied at `a`
  and at `a⁻¹`, using the unit identity `(-a)(1 - a⁻¹) = 1 - a`.  This does not close either card:
  the amplitude card's `(1)` is an import from Gallauer and Borel, and the rank-collapse card needs
  Milnor--Witt `K`-theory and the Witt ring on top of this.

### Milnor--Witt `K`-theory is now built — 2026-08-07

`formal/GaloisForLFunctions/HTGeometry/MilnorWittKTheory.lean`.  Axiom audit for all thirteen
declarations: `propext, Classical.choice, Quot.sound`.

The absence of Milnor--Witt `K`-theory is named here as a reason a statement cannot be written down.
Morel's presentation is elementary and is now built, in the same shape as the corpus's Milnor
`K`-theory: the free `ℤ`-algebra on a symbol `[u]` for every unit together with one further symbol
`η`, modulo the four relations.

- `MilnorWittGen`, `MilnorWittRel`, `MilnorWittK`, `mwMk` — the generators, **Morel's four
  relations** (Steinberg `[u][1-u] = 0`, twisted additivity `[uv] = [u] + [v] + η[u][v]`, the
  centrality of `η`, and the hyperbolic relation `η(η[-1] + 2) = 0`), and the ring.
- `milnorWittSymbol`, `milnorWittEta`, `milnorWittSymbol_mul`, `milnorWittSymbol_mul_oneSub`,
  `milnorWittEta_comm`, `milnorWittEta_hyperbolic` — the generators and the four relations as
  theorems about them.
- `milnorWittForget`, `milnorWittForget_symbol`, `milnorWittForget_eta` — **killing `η` gives Milnor
  `K`-theory**: twisted additivity becomes ordinary additivity, centrality and the hyperbolic
  relation become `0 = 0`, and Steinberg is Steinberg.

The corpus already held a second presentation of the same object, with the form identities, the
comparison with the Witt ring and the quotient by `η` built on it.  The two are now one: the base
module carries the names the rest of the tree uses, and `milnorWittSymbol_one` — **the symbol of `1`
vanishes** — is the *unconditional* proof from `MilnorWittFormIdentities.lean`, which multiplies the
hyperbolic relation by that symbol, rather than an earlier version that assumed the field has a unit
other than `1`.

What this does not build is the Milnor--Witt *sheaf* theory — the oriented fundamental class, its
determinant twist and the Gysin map — which is what the remaining geometric statements need.  The
ring itself is no longer a gap.

### `(1)` reduced to a single classical input, and `(2)` assembled `[NEW]`

`formal/GaloisForLFunctions/HTGeometry/MilnorKGrading.lean`,
`MilnorKFunctoriality.lean`, `MilnorKAlgebraicReduction.lean`, and
`formal/GaloisForLFunctions/RHTower/DeningerMilnorRealShape.lean`.  Axiom audit for all
declarations: `propext, Classical.choice, Quot.sound`.

The graded Milnor `K`-theory the card needs is now available: the corpus carries `MilnorKDeg F n`
with its symbol classes, its product `milnorMul`, and the two bottom identifications
`milnorDegZeroEquiv : K_0^M(F) ≅ ℤ` and `milnorDegOneEquiv : K_1^M(F) ≅ F^×`.  On top of it:

- **Degree at least two is torsion once degree two is.**  `milnorKDeg_mem_torsion_of_two` — a
  symbol of length `2+k` is the product of its first two entries with the remaining `k`
  (`milnorClassDeg_split`), so an integer annihilating the degree-two factor annihilates the whole
  class, and the symbol classes generate.  In particular `q ≥ 3` costs nothing beyond `q = 2`.
- **Functoriality.**  `milnorKMap` — a field homomorphism induces a homomorphism of Milnor
  `K`-rings sending symbols to symbols, because it preserves units and carries the Steinberg
  relation to the Steinberg relation.  Hence `milnorSymbol_mul_torsion_of_ringHom` and
  `milnorSymbol_mul_torsion_of_subfield`: torsion of a length-two symbol descends along any field
  map hitting its two entries.
- **Reduction to finite subextensions.**  `milnorSymbol_mul_torsion_of_finiteSubextension` — for an
  algebraic extension of the rationals, two units generate a finite subextension, so the torsion of
  every length-two symbol follows from the torsion of every length-two symbol of every *number
  field*.
- **`(2)` assembled.**  `deningerTorsionModule_tensorReal_eq_zero` — a torsion group realifies to
  zero; `deningerMilnorDegTensorReal_eq_zero` — therefore `K_q^M(F) ⊗ ℝ = 0` for every `q ≥ 2` as
  soon as degree two is torsion; `deningerMilnorDegZeroRealEquiv` and
  `deningerMilnorDegOneRealEquiv` — degree zero realifies to `ℝ` and degree one to `F^× ⊗ ℝ`.
  Together with `(3)`, already proved, this is exactly the shape asserted by `(2)`.

**What remains for `(1)` is one classical statement:** *every length-two Milnor symbol of a number
field is torsion*.  Through the tame symbols into the finite residue fields this is equivalent to
the tame kernel being torsion — Tate's and Garland's finiteness theorem, equivalently Borel's rank
computation.  Note that passing to `ℚ̄` does not avoid it: `K_2` of an algebraically closed field
is in general a nonzero uniquely divisible group, and `K_2(ℚ̄) = 0` precisely because it is the
filtered colimit of the number-field groups.  Mathlib carries no algebraic `K`-theory, no
localization sequence and no Borel regulator, so this input has to be built from nothing.

The reduction chain is now connected at the graded level as well:
`formal/GaloisForLFunctions/HTGeometry/MilnorKDegFunctoriality.lean` builds `milnorKDegMap`, the
map `K_n^M(F) → K_n^M(E)` induced by a field homomorphism (multilinearity goes to multilinearity,
Steinberg to Steinberg), `milnorKDeg_mem_of_gen` (the symbol classes generate), and
`milnorKDegTwo_torsion_of_finiteSubextension`.  Composing,
`deningerMilnorRealVanishing_of_finiteSubextension` in `RHTower/DeningerMilnorRealShape.lean` is
the card's `(1)` and `(2)` in full, resting on the single hypothesis that every degree-two class of
every finite subextension of `ℚ` is torsion.

### The tame symbol on `K_2^M` `[NEW]`

`formal/GaloisForLFunctions/HTGeometry/MilnorKTameSymbol.lean`.  Axiom audit: `propext,
Classical.choice, Quot.sound`.

Every known route to the remaining input passes through the tame symbol, which mathlib does not
have.  It is now built, unconditionally, for an abstract discrete valuation with residue field:

- `TameData` — a valuation `Kˣ →* Multiplicative ℤ`, the residue homomorphism on its kernel, and
  the three standard clauses describing `1 - a` (positive valuation forces `v(1-a) = 0` and
  residue one; valuation zero forces `v(1-a) ≥ 0`, with positive value forcing the residue of `a`
  to be one; negative valuation forces `v(1-a) = v(a)` and residue `-1` for `a(1-a)^{-1}`).
- `TameData.tame a b` — the residue of `(-1)^{v(a)v(b)}a^{v(b)}b^{-v(a)}`, whose argument has
  valuation zero by construction (`symbolUnit_mem`).
- `tame_mul_left`, `tame_mul_right` — **bimultiplicativity**, from the two homomorphism
  properties.
- **`tame_steinberg`** — the tame symbol kills `{a, 1-a}`, by the four-way case analysis on the
  valuations; the negative case is the one where the sign matters, and it closes because
  `v(a)² + v(a)` is even.
- `tame_eq_one_of_mem_ker` — a pair of valuation-zero units has trivial symbol, which is why a
  fixed pair has nontrivial symbol at only finitely many places.
- **`tameHom : K_2^M(K) →+ Additive k^×`** — the descent, via the degree-two relation subgroup.

This isolates the residual input exactly: the tame symbols of a number field take values in finite
groups, so they see only torsion; what is left is that the *tame kernel* is torsion, i.e. Garland's
finiteness theorem (equivalently Borel's vanishing of the rank of `K_2` of a ring of integers).

### The tame symbol of an actual valuation `[NEW]`

`formal/GaloisForLFunctions/HTGeometry/MilnorKTameValuation.lean`.  Axiom audit for all
declarations: `propext, Classical.choice, Quot.sound`.

The abstract tame-symbol data is no longer abstract: it is now constructed, unconditionally, from
an arbitrary integer-valued valuation on a field, which is exactly the shape of the valuations of a
number field at its finite places.

- `tameValHom` — the additive valuation on the units, the inverse of the multiplicative value, so
  that elements of the maximal ideal have positive integer valuation;
  `tameValHom_mem_ker_iff`, `tameValHom_pos_iff`, `tameValHom_neg_iff` read off its kernel and its
  sign.
- `tameUnit`, **`tameResHom`** — a unit of valuation zero is a unit of the valuation subring, and
  reduction modulo the maximal ideal gives the residue homomorphism; `tame_mem_maximalIdeal` and
  `tame_residue_eq_zero` are the two facts the Steinberg clauses need.
- `tameResHom_neg_one`, **`tame_oneSub_of_pos`**, **`tame_oneSub_of_zero`**,
  **`tame_oneSub_of_neg`** — the three clauses, proved from the ultrametric inequality: if
  `v(a) < 1` then `v(1-a) = 1` and `1 - a ≡ 1`; if `v(a) = 1` then `v(1-a) ≤ 1`, with equality
  failing only when `a ≡ 1`; and if `v(a) > 1` then `v(1-a) = v(a)` while
  `a(1-a)^{-1} + 1 = (1-a)^{-1}` lies in the maximal ideal, so the quotient reduces to `-1`.
- **`tameDataOfValuation`** — the assembled `TameData`, and **`tameHomOfValuation`**, the tame
  symbol as a homomorphism `K_2^M(K) → (residue field)^×`.

So for a number field the tame symbols exist unconditionally in Lean at every finite place, with
finite residue fields, hence torsion targets.  The residual input is unchanged and is exactly the
tame kernel: Garland's finiteness, equivalently Borel's vanishing of the rank of `K_2` of a ring of
integers.

### The tame symbols at the finite places `[NEW]`

`formal/GaloisForLFunctions/HTGeometry/MilnorKTameDedekind.lean`.  Axiom audit for all
declarations: `propext, Classical.choice, Quot.sound`.

The adic valuation at a height-one prime of a Dedekind domain is integer valued, so the previous
construction applies verbatim:

- `tameDataAtPlace`, **`tameHomAtPlace`** — the tame symbol at a finite place, as a homomorphism
  `K_2^M(K) → (residue field at that place)^×`.  For a number field this is the classical family
  of tame symbols, now available unconditionally in Lean.
- `finite_valuation_ne_one` — a unit of the fraction field is a unit of the valuation ring at all
  but finitely many places, since its support and the support of its inverse are finite.
- **`finite_tame_ne_one`**, **`finite_tameHomAtPlace_ne_zero`** — a fixed pair of units therefore
  has trivial tame symbol at all but finitely many places, and so does its symbol class.

Everything the reduction needs is now in place except the classical input itself.  The tame symbols
of a number field take values in the unit groups of finite residue fields, so they detect only
torsion, and by the finiteness above only finitely many of them are nontrivial on a given symbol.
What is not proved — and is not provable by these means — is that the *tame kernel* is torsion:
Garland's finiteness theorem, equivalently Borel's vanishing of the rank of `K_2` of a ring of
integers.

### The tame-kernel reduction `[NEW]`

`formal/GaloisForLFunctions/HTGeometry/MilnorKTameKernel.lean` and the new material in
`MilnorKTameDedekind.lean`.  Axiom audit for all declarations:
`propext, Classical.choice, Quot.sound`.

The card's `(1)` is imported from Borel's computation of rational algebraic `K`-theory (via
Gallauer's Remark 6.8), and the Lean record carries it as the hypothesis `hNF` — that every
degree-two Milnor class of a number field is torsion.  That hypothesis is now cut in half: its
elementary half is proved, and what is left is exactly one named classical theorem.

- **`tameKernel`** — the tame kernel of a family of tame data: the degree-two classes with trivial
  tame symbol at every place.
- `tameFiniteSupport`, **`tame_finiteSupport_of_symbols`** — vanishing of the tame symbol at almost
  every place passes from symbols to all classes, because the classes with that property form a
  subgroup and the symbol classes generate.  Combined with the already-proved
  `finite_tame_ne_one`, this gives `finite_tameHomAtPlace_ne_zero_all`: **every** degree-two class
  of the fraction field of a Dedekind domain, not only a symbol, has trivial tame symbol at all but
  finitely many finite places.
- **`exists_zsmul_mem_tameKernel`** — **every class has a nonzero multiple in the tame kernel**,
  when the residue fields have finite unit groups: the finitely many nonzero tame symbols lie in
  finite groups, and the product of their orders annihilates all of them simultaneously.
- **`milnorKDegTwo_torsion_of_tameKernel_torsion`**, and its Dedekind form
  **`milnorKDegTwo_torsion_of_tameKernelAtPlaces_torsion`** — **torsion of the tame kernel forces
  torsion of `K_2^M`.**

So the residual input behind `(1)` is no longer "the degree-two Milnor `K`-group of a number field
is torsion" but the strictly smaller and precisely named statement **the tame kernel `K_2(𝒪_K)` is
torsion** — Garland's finiteness theorem, equivalently Quillen's finite generation together with
Borel's vanishing of the rank of `K_2(𝒪_K)`.  Everything on the other side of that theorem is now
unconditional in Lean: the tame symbols at every finite place, their finite support, the reduction
of an arbitrary algebraic extension to its number-field subextensions, the passage from degree two
to all higher degrees, and the real-vanishing conclusion `(1)`--`(2)`.

### The residue fields are discharged: `(1)` now rests on Garland alone `[NEW]`

`formal/GaloisForLFunctions/HTGeometry/MilnorKTameResidueFinite.lean` and the new
`deningerMilnorRealVanishing_of_tameKernelTorsion` in
`formal/GaloisForLFunctions/RHTower/DeningerMilnorRealShape.lean`.  Axiom audit for all
declarations: `propext, Classical.choice, Quot.sound`.

The tame-kernel reduction still carried a side condition — that the residue fields at the finite
places are finite.  That is now proved, so nothing remains between the tame kernel and the card's
`(1)` except Garland's theorem itself.

- `algebraMap_surjective_of_isFractionRing_of_isUnit` — a fraction ring of a ring in which every
  nonzero element is a unit is that ring.
- **`finite_residueField_valuationSubring`** — **the residue field at a finite place of a Dedekind
  domain is finite whenever the residue ring of the prime is.**  The valuation subring at a
  height-one prime is the localization at that prime, so its residue field is the residue field of
  the prime; a nonzero prime of a Dedekind domain is maximal, so `R ⧸ v.asIdeal` is already a field,
  and a fraction field of a field is that field.
- `finite_quotient_asIdeal` — the residue rings of a number ring are finite, from mathlib's
  finiteness of quotients of a free finite `ℤ`-algebra.
- **`milnorKDegTwo_torsion_of_tameKernel_numberField`** — **for a number field, torsion of the tame
  kernel forces torsion of `K_2^M`**, with every side condition discharged.
- **`deningerMilnorRealVanishing_of_tameKernelTorsion`** — **the card's `(1)` for every algebraic
  extension of the rationals, assuming only that the tame kernel of each finite subextension is
  torsion.**

So the Lean record of this card now depends on exactly one classical statement, named and isolated:
`K_2(𝒪_K)` is torsion for a number field `K` (Garland 1971; equivalently Quillen's finite generation
together with Borel's vanishing of the rank).  This matches the card's own proof, which imports the
same fact through Gallauer's Remark 6.8 and Borel's computation; the difference is that the Lean
chain now isolates it as a single hypothesis about the tame kernel rather than about `K_2^M` itself,
with the tame symbols, the finiteness of the residue fields, the almost-everywhere vanishing, the
reduction of an arbitrary algebraic extension to number fields, the passage from degree two to all
higher degrees, and the real-vanishing conclusion all proved.

### The graded ring structure of Milnor `K`-theory `[NEW]`

`formal/GaloisForLFunctions/HTGeometry/MilnorKGradedRingAssoc.lean`.  Axiom audit for all
declarations: `propext, Classical.choice, Quot.sound`.

The card's arithmetic consequence 2 — "a Rost--Schmid resolution over the regular arithmetic curve
`Spec ℤ` has residue length one" — is a statement about the two-term Gersten complex
`K_n^M(K) → ⊕_v K_{n-1}^M(κ(v))` of a one-dimensional regular scheme, so it needs the residue maps
in all degrees, not only the degree-two tame symbol already built.  Milnor's construction of the
residue realizes it as the `ξ`-component of a ring homomorphism into
`K_*^M(k) ⊕ K_{*-1}^M(k)·ξ`, and that target has to be a graded ring.  The graded ring structure of
Milnor `K`-theory itself is the first ingredient and is now proved.

- `milnorDegCongr`, `milnorDegCongr_class` — transport along an equality of degrees, the bookkeeping
  a `ℕ`-graded product needs.
- `milnorSymbolAppend_assoc`, **`milnorMul_assoc`** — **the graded product is associative**, by
  associativity of concatenation together with a triple extensionality over the symbol classes.
- `milnorOne`, **`milnorOne_mul`**, **`milnorMul_one`** — the class of the empty symbol is a
  two-sided unit.

The corpus already had anticommutativity at adjacent slots (`milnorPairClass_anticomm`) and the full
interior-slot calculus of Milnor symbols, so what remains for the residue is the `ξ`-extension of
this ring and the Steinberg verification, which is the same four-case analysis on valuations that
the degree-two tame symbol already carries out in `MilnorKTameSymbol.lean`.

### The residue step, and multilinearity `[NEW]`

`formal/GaloisForLFunctions/HTGeometry/MilnorKResidueData.lean` and
`MilnorKResidueStep.lean`.  Axiom audit for all declarations:
`propext, Classical.choice, Quot.sound`.

Milnor's residue is the `ξ`-component of a homomorphism into `K_*^M(k) ⊕ K_{*-1}^M(k)·ξ`, where `ξ`
anticommutes with the odd part and satisfies `ξ² = {-1}·ξ`.  A unit `a` goes to `[ū_a] + v(a)·ξ`,
where `ū_a` is the residue of the unit part of `a`.  Two of the three ingredients are now built.

- **`ResidueData`** — a discrete valuation with its residue map *and a chosen uniformizer*, which is
  what the degree-two tame symbol did not need: the uniformizer splits every unit as a power of
  itself times a unit of valuation zero.  `unitPart`, **`residueUnit`**, and the three laws
  `residueUnit_mul`, `residueUnit_unif`, `residueUnit_of_mem_ker`.
- **`resStepHom`** — **multiplication by `[ū_a] + v(a)·ξ`** on the degree-`n` part, namely
  `(x, y) ↦ ([ū_a]·x, [ū_a]·y + (-1)^n v(a)·x + (-1)^{n-1} v(a)·{-1}·y)`, built as an honest
  additive map so that the later relation checks can be done on generators.
- **`resStepHom_mul`** — **the step is additive in the unit**, because `[ū_{ab}] = [ū_a] + [ū_b]`
  and `v(ab) = v(a) + v(b)`.  This is one of the two relations of Milnor `K`-theory that the residue
  must respect: multilinearity.
- **`resPair`** — the fold of the step over a symbol, giving simultaneously the specialization and
  the residue of that symbol.

What remains for the residue is the Steinberg vanishing — that the composite of the steps at `a` and
`1 - a` is zero — which is the same four-case analysis on valuations that
`TameData.tame_steinberg` already carries out in degree two, and then the descent of `resPair` to a
homomorphism out of `K_n^M(K)`.

### The residue homomorphism in every degree `[NEW]`

`formal/GaloisForLFunctions/HTGeometry/MilnorKResidueMap.lean`,
`formal/GaloisForLFunctions/HTGeometry/MilnorKResidueValuation.lean`.  Axiom audit for all
declarations: `propext, Classical.choice, Quot.sound`.

The card's reduction of `(1)` runs through the tame symbol, which the corpus had only in degree two.
Milnor's residue in *every* degree is now built, together with its input data at every finite place
of a Dedekind domain — so the Gersten complex of `K_*^M` over an arithmetic curve is available, not
only its degree-two row.

- `resPairAt` — the fold of the residue steps `x ↦ ([ū_a] + v(a)ξ)·x` over a symbol, indexed by the
  *length* of the list rather than by the list.  This is the point that makes the construction
  statable: the type of the value then does not mention the list, so the two defining relations of
  Milnor `K`-theory can be compared without transporting along `List.length`.
- **`resPairAt_mul`** — multilinearity at an interior slot, from `resStepHom_mul`.
- **`resPairAt_steinberg`** — the Steinberg relation at an interior slot, from the four-case
  `resStepHom_steinberg`.
- `resPre`, **`resPre_ker`**, **`milnorResPair`** — the fold descends from formal sums of symbols to
  `K_n^M(K)`.
- **`milnorResidue`**, **`milnorSpecialization`** — **the residue `∂ : K_n^M(K) → K_{n-1}^M(k)` and
  the specialization `K_n^M(K) → K_n^M(k)` attached to a uniformizer.**
- `milnorResidue_one` — the residue of a degree-one symbol is its valuation;
  **`milnorResidue_two`** — the residue in degree two is the tame symbol,
  `∂{a,b} = v(b)[ū_a] - v(a)[ū_b] + v(a)v(b)[-1]`.
- `residueDataOfValuation`, `placeUniformizer`, **`residueDataAtPlace`** — the residue data of an
  integer-valued valuation with a chosen uniformizer, and its instance at a finite place of a
  Dedekind domain.  The extra datum beyond the tame symbol data is the additivity of the residue on
  `1 - a`, which is automatic: the residue map is induced by the quotient map of the valuation ring
  onto its residue field.  `residueDataAtPlace_toTameData` records that the underlying tame data is
  the one the tame kernel already uses.

### Milnor `K`-theory of a finite field `[NEW]`

`formal/GaloisForLFunctions/HTGeometry/MilnorKFiniteField.lean`.  Axiom audit for all declarations:
`propext, Classical.choice, Quot.sound`.

The targets of the residue maps over an arithmetic curve are the Milnor `K`-groups of the residue
fields, which are finite.  Those groups are now computed above degree one: they vanish.

- `milnorSymTwo` with `milnorSymTwoLeft`, `milnorSymTwoRight`, `milnorSymTwo_zpow` — the degree-two
  symbol as a bilinear pairing, so `{g^i, g^j} = ij·{g,g}`.
- **`two_smul_milnorSymTwo_self`** — `{a,a} = -{a,-1}` is killed by two, over any field.
- **`exists_nonsquare_oneSub_nonsquare`** — **in a finite field of odd characteristic there is a
  nonsquare `a` with `1 - a` a nonsquare.**  If not, `a ↦ 1 - a` injects the nonsquares into the
  nonzero squares; the quadratic character sums to zero so the two sets have the same size, the
  injection is a bijection, and the preimage of `1` is `0` — which is not a nonsquare.
- **`milnorSymTwo_gen_eq_zero`** — for a generator `g` of the unit group, `{g,g} = 0`: the Steinberg
  relation at that nonsquare pair says `ij·{g,g} = 0` with `i, j` odd, and two is coprime to an odd
  number.  In characteristic two the argument is shorter: `-1 = 1`.
- **`milnorKDegTwo_eq_zero_of_finite`**, **`milnorKDeg_eq_zero_of_finite`** — **`K_n^M` of a finite
  field vanishes for every `n ≥ 2`**, since the symbol classes generate and each is a multiple of
  `{g,g}`.

### What still blocks `(1)` — the exact statement

Everything on the near side of the card's `(1)` is unconditional: the reduction of an arbitrary
algebraic extension of `ℚ` to its number subfields, the reduction of degree `2 + k` to degree two,
the tame symbol at every finite place with finite support, the finiteness of the residue fields, and
now the residue map in every degree.  The single remaining input is

> **the tame kernel of a number field is torsion** — `K_2(𝒪_K) ⊗ ℚ = 0`,

which is Garland's finiteness theorem (1971), equivalently Quillen's finite generation together with
Borel's rank computation.  The literature has no proof of it by elementary means; searches confirm
that every published route goes through Garland, or through Quillen–Borel, or through Soulé's
vanishing plus Quillen–Lichtenbaum.  The card therefore stays at stage 2, and the programme card
`garland-tame-kernel-torsion` carries the decomposition.

### The Gersten row over an arithmetic curve `[NEW]`

`formal/GaloisForLFunctions/HTGeometry/MilnorKResidueUnits.lean`,
`formal/GaloisForLFunctions/HTGeometry/MilnorKGersten.lean`.  Axiom audit for all declarations:
`propext, Classical.choice, Quot.sound`.

The residue construction is now assembled into the row it belongs to, in every degree.

- **`resPairAt_snd_eq_zero`**, `milnorResidue_eq_zero_of_units` — **the residue kills a symbol all
  of whose entries are units of valuation zero**: multiplication by `[ū_a] + v(a)ξ` is
  multiplication by `[ū_a]` alone when `v(a) = 0`, so no `ξ` is ever produced.
- **`resPairAt_fst_eq`**, `milnorSpecialization_of_units` — and the specialization of such a symbol
  is the symbol of the residues, so the specialization is the reduction map on units.
- `milnorResidueAtPlace` — the residue at a finite place of a Dedekind domain, in every degree.
- **`finite_milnorResidueAtPlace_ne_zero`** — **a class has nonzero residue at only finitely many
  places**: each entry of a symbol is a unit at all but finitely many places, and there the residue
  vanishes by the previous item; the symbol classes generate, and the almost-everywhere-vanishing
  classes form a subgroup.
- `milnorTameKernel`, `mem_milnorTameKernel_iff` — **the tame kernel in degree `n`.**
- **`exists_zsmul_mem_milnorTameKernel`** — every class has a nonzero multiple in the tame kernel,
  as soon as its finitely many residues are torsion.
- **`milnorKDeg_torsion_of_milnorTameKernel_torsion`** — **torsion of the tame kernel forces torsion
  of `K_n^M(K)`**, in every degree, given torsion residue targets.  Over a number field the targets
  are torsion for every `n ≥ 2`: they are `k(v)^×` when `n = 2` (finite) and `0` when `n ≥ 3`
  (`milnorKDeg_eq_zero_of_finite`).

This is the general-degree form of the card's degree-two reduction.  It changes nothing about the
outstanding input, which remains the torsion of the degree-two tame kernel.

## Corpus audit — the card is one classical input away, and `(3)` was already formal

A session-start audit of the formal tree against this card was **not** run before writing new code,
and the result was a duplicate module (`HTGeometry/TorsionTensorReal.lean`) reproving work the tree
already contained.  The duplicate has been deleted and unwired.  Recorded here so no later session
repeats it.

What the tree already proves, unconditionally:

```text
DeningerMilnorAmplitude.lean
    deningerTorsion_tmul_real_eq_zero          a torsion element tensored with a real vanishes
    deningerTorsionTensorReal_eq_zero          the realification of the torsion submodule vanishes
    deningerRealification_torsionQuotient_bijective
    deningerRealificationTorsionEquiv          **the realification isomorphism `(3)`**
    deningerGradedDegreeOne_mul_eq_zero        vanishing degree two makes degree one square zero
DeningerCharacterShapeFormality.lean
    deningerUnitSpace_isTorsionFree            the torsion subgroup of the units is exactly μ_∞
DeningerMilnorRealShape.lean
    deningerMilnorDegZeroRealEquiv             **degree zero realifies to ℝ**            — `(2)` q=0
    deningerMilnorDegOneRealEquiv              **degree one realifies to F^× ⊗ ℝ**       — `(2)` q=1
    deningerMilnorDegTensorReal_eq_zero        degree ≥ 2 realifies to zero once degree two is torsion
    deningerMilnorRealVanishing_of_finiteSubextension
    deningerMilnorRealVanishing_of_tameKernelTorsion
```

and, supporting these, a full Milnor `K`-theory development that mathlib does not have:
`MilnorKTheory` (the ring, the symbol, Steinberg, `{a,−a}=0`, anticommutativity), `MilnorKGrading`,
`MilnorKGradedRing(Assoc)`, `MilnorKFiniteField` (`milnorKDegTwo_eq_zero_of_finite`),
`MilnorKResidue*`, `MilnorKTame{Symbol,Valuation,Dedekind,Kernel,ResidueFinite}`, `MilnorKGersten`,
`MilnorKDegFunctoriality`, `MilnorKAlgebraicReduction`, and the Milnor–Witt comparison tower.

### The single remaining input

`deningerMilnorRealVanishing_of_tameKernelTorsion` reduces the card's `(1)` — and with it `(2)` in
degrees `≥ 2` and hence `(4)` — to exactly one classical statement:

```text
for every number field K, every element of the degree-two tame kernel of K is torsion
```

that is, Garland's theorem (finiteness of `K_2(O_K)`), or just its torsion consequence.  Everything
between that and the card's conclusion is proved: the tame symbols at the finite places, finiteness
of the residue fields, almost-everywhere vanishing of the residues, the reduction of an arbitrary
algebraic extension to its finite subextensions, and the passage from degree two to all higher
degrees.

So the accurate status of this card is **one named classical input**, not "no formalization" and not
"blocked on Borel" — the reduction past Borel's rank computation to the tame kernel is already done
here.

## The remaining input, scoped: what a formal proof of tame-kernel torsion has to contain

The reduction in this tree is complete — `milnorKDegTwo_torsion_of_tameKernel_numberField` consumes
exactly "every element of the degree-two tame kernel of a number field is torsion" — so the whole
card now rests on that one statement.  Its literature proofs and their formalization cost:

- **Garland**, and **Quillen finite generation + Borel rank zero**: both give the stronger
  `K_2(O_K)` *finite*.  Garland's proof runs through buildings and harmonic analysis on `p`-adic
  groups; Quillen's runs through the `Q`-construction and finite generation of `K_*` of rings of
  integers.  Neither has any part of its machinery in mathlib.
- **Tate's computation for `Q`** (Milnor, *Introduction to Algebraic K-theory*, Theorem 11.6) is
  elementary and self-contained: the tame kernel of `Q` is `{1, {-1,-1}}`, of order two.  It is the
  only route in the literature that a formalization can begin today.

### The Tate route, in this tree's objects

```text
MilnorKDeg Q 2                      the group             (MilnorKTheory, MilnorKGrading)
milnorResidueAtPlace Q v 2          the tame symbol at a prime      (MilnorKResidue*, MilnorKTame*)
milnorTameKernel Z Q 2              the intersection of their kernels        (MilnorKGersten)
```

The argument is a filtration by the largest prime that occurs:

1. every class is a finite sum of symbols `{a} u {b}` with `a, b` nonzero **integers** — bilinearity
   turns `{a/b, c/d}` into four integer symbols;
2. let `L_p` be the subgroup generated by integer symbols all of whose prime factors are at most
   `p`; then `K_2^M(Q) = colim_p L_p`;
3. the tame symbol at `p` maps `L_p` onto `F_p^x` and kills `L_{p-1}`;
4. **the Euclidean step** — the only substantial one — shows `ker(tame_p) ∩ L_p ⊆ L_{p-1}`, by
   reducing `{a, p}` with `0 < a < p` through the division algorithm and the Steinberg relation
   `{x, 1-x} = 0`;
5. iterating downwards leaves `L_2 = <{-1,-1}>`, which is killed by `2`.

Steps 1–3 are bookkeeping over the symbol API this tree already owns; step 4 is the mathematical
content and is where a formalization should start.  Note what the route does and does not give: it
settles `F = Q`, hence the card's `(1)` for `F = Q`, but **not** an arbitrary number field —
the division algorithm is used, so the same argument extends only to the Euclidean imaginary
quadratic fields.  The card's statement for arbitrary algebraic `F/Q` still needs Garland or
Quillen–Borel; recording this so that the ratio between "one classical input" and "one *cheap*
classical input" is not misread.

## Lean progress — the degree-two symbol calculus, the Tate route's first brick

`HTGeometry/MilnorKDegTwoSymbol.lean` (wired into the `HTGeometry` umbrella, built, axioms
`[propext, Classical.choice, Quot.sound]`).

The Euclidean reduction of step 4 is a computation with symbols, and the tree had `K_2^M` only
through the general graded API (`milnorClassDeg`, `milnorClassDeg_mul_of_eq`,
`milnorClassDeg_steinberg_of_eq`).  The degree-two calculus is now a named layer:

```
milnorSym2 F a b                    the symbol {a, b}
milnorSym2_mul_left / _mul_right    bilinearity in each slot
milnorSym2_steinberg                {a, 1 − a} = 0
milnorSym2_one_left / _one_right    {1, b} = {a, 1} = 0
milnorSym2_inv_left / _inv_right    {a⁻¹, b} = {a, b⁻¹} = −{a, b}
milnorSym2_neg_self                 ** {a, −a} = 0 **
milnorSym2_antisymm                 ** {a, b} = −{b, a} **
closure_range_milnorSym2            ** the symbols generate K_2^M(F) **
```

`{a, −a} = 0` is the classical computation `−a = (1 − a)/(1 − a⁻¹)`, done at the level of units: the
first factor dies by Steinberg at `a`, the second by Steinberg at `a⁻¹` after moving the inverse out
of the left slot.  Antisymmetry is `{ab, −ab} = 0` expanded in both slots.  `closure_range_milnorSym2`
is the free-abelian-group induction, using that a symbol of degree two is literally a two-element
list.

These are exactly the identities the Euclidean step consumes — it rewrites `{a, p}` with
`0 < a < p` by dividing `p` by `a` and applying Steinberg, and needs bilinearity, antisymmetry and
`{a, −a} = 0` to move the pieces around.  The step itself, and the filtration `L_p` by the largest
prime occurring, are the next bricks.

Recorded scope, unchanged: this route settles `F = Q` (and the Euclidean imaginary quadratics), not
an arbitrary number field.  The card's `(1)` in full generality still needs Garland's finiteness of
`K_2(O_K)` or Quillen finite generation with Borel's rank computation, neither of which has any part
of its machinery in mathlib.

## TATE'S THEOREM IS FORMAL — `(1)` and `(2)` are unconditional for `F = Q`

Six new modules (all wired into the `HTGeometry` / `RHTower` umbrellas, built, axioms
`[propext, Classical.choice, Quot.sound]`).

The card recorded the whole statement as resting on one classical input, the torsion of the
degree-two tame kernel of a number field, and recorded Tate's computation for `Q` as "the only route
in the literature that a formalization can begin today".  That computation is now done.

### 1. The residue of a rational modulo `p`

`HTGeometry/RationalPadicResidue.lean`.

```
ratRes p q = q.num / q.den  in  ZMod p
ratRes_of_eq_div        ** the presentation lemma **:  q = m/n  with  p ∤ n   ==>   res q = m̄/n̄
den_ne_zero_of_eq_div, ratRes_intCast, ratRes_natCast, ratRes_one
IsPadicUnit, ratRes_mul, ratRes_inv, isPadicUnit_of_ratRes_ne_zero
```

The residue field is taken to be `ZMod p` itself, not an abstract quotient of a valuation ring, so
every statement about the tame symbol at `p` is an explicit congruence.  Every property of `res`
comes from the presentation lemma by one cross-multiplication.

### 2. The tame data of `Q` at a prime

`HTGeometry/RationalTameData.lean`.

```
padicValRat_eq_zero_iff       a p-unit is exactly a rational of p-adic valuation zero
props_of_padicValRat_pos      v > 0  ==>  p | num,  p ∤ den
props_of_padicValRat_neg      v < 0  ==>  p ∤ num,  p | den
ratRes_one_sub                res(1 − q) = 1 − res q     (p ∤ den)
ratPadicValHom, ratResHom
** ratTameData p : TameData Q (ZMod p) **        all four Steinberg clauses
ratTameHom p : K_2^M(Q) →+ Additive (ZMod p)^x
```

The four clauses are elementary congruences once `1 − q = (den − num)/den` is fed to the
presentation lemma: `res(1−a) = 1` when `v(a) > 0`; `res a = 1` when `v(a) = 0` and `v(1−a) > 0`;
and `a(1−a)^{-1} = num/(den − num)` has residue `−1` when `v(a) < 0`, because `den ≡ 0`.

### 3. The smooth units

`HTGeometry/SmoothRationalUnits.lean`.

```
smoothUnits N = {u : Q^x | ord_q u = 0 for every prime q > N}          a subgroup
smoothUnits_le_closure   ** unique factorization **: generated by −1 and the primes ≤ N
mul_self_eq_one_of_mem_smoothUnits_one     the 1-smooth units are ±1
exists_mem_smoothUnits                     every unit is N-smooth for some N
smoothUnits_succ_of_not_prime              nothing changes at a composite bound
```

Defining smoothness by *valuations* rather than by generators is what makes the filtration step
cheap: the decomposition `u = u' p^i` with `u'` one level down is immediate from additivity of the
valuation, while the generation statement is needed only once, to run an induction over generators.

### 4. The filtration and the decomposition

`HTGeometry/MilnorKTateFiltration.lean`, plus `milnorSym2_zpow_left/right` and
`milnorSym2LeftHom` added to `HTGeometry/MilnorKDegTwoSymbol.lean`.

```
smoothK2 N                     generated by the symbols of N-smooth units
smoothK2_mono, smoothK2_succ_of_not_prime
two_zsmul_eq_zero_of_mem_smoothK2_one      ** the bottom is killed by 2 **
exists_mem_smoothK2                        ** the filtration exhausts K_2^M(Q) **
milnorSym2_self : {a,a} = {−1,a}
smoothK2_le_tateDecomp     ** x = y + {u, p}  with y, u one level down **
```

The decomposition collects the four terms of `{a' p^i, b' p^j}` into a single symbol `{u, p}` with
`u = (a')^j (b')^{-i} (−1)^{ij}`, using `{p,p} = {−1,p}`.

### 5. The Euclidean step

`HTGeometry/MilnorKTateEuclid.lean`.

```
euclid_relation   0 < a,b < p,  c = ab mod p
    {a,p} + {b,p} − {c,p}  ∈  smoothK2 (p−1)
tateRepSet, exists_tateRep
    every (p−1)-smooth u has  0 < c < p  with  c ≡ res_p u  and  {u,p} − {c,p} one level down
smoothK2_descent_prime     ** x ∈ smoothK2 p,  tame_p x = 0   ==>   x ∈ smoothK2 (p−1) **
mem_smoothK2_one_of_tame_vanishing
two_zsmul_eq_zero_of_mem_ratTameKernel     ** Tate: the tame kernel of Q is killed by 2 **
** milnorKDegTwo_rat_torsion : every class of K_2^M(Q) is torsion **
```

The Euclidean step is one Steinberg application.  Write `ab = kp + c` with `0 < c < p`, `0 ≤ k < p`,
and put `x = −kp/c`, so `1 − x = (c + kp)/c = ab/c =: W`.  Then

```text
0 = {x, W} = {−1, W} + {k, W} + {p, W} + {c⁻¹, W} ,
```

and `−1, k, c, a, b` are all `(p−1)`-smooth (each of `k, c` is below `p`, and `a, b` are below `p`),
so every term except `{p, W}` lies one level down; hence so does `{W,p} = −{p,W}`, which is exactly
`{a,p} + {b,p} − {c,p}`.

Iterating the relation over the generators `−1` and the primes `< p` gives the representative:
for `−1` the representative is `p − 1`, and `{−1,p} = {p−1,p}` because Steinberg gives
`{p, 1−p} = 0`, i.e. `{−1,p} + {p−1,p} = 0`, while `{−1,p}` is `2`-torsion.

### 6. The card's `(1)` and `(2)` over `Q`

`RHTower/DeningerRationalMilnorAmplitude.lean`.

```
deningerRationalMilnorRealVanishing (k) (t : K^M_{2+k}(Q) ⊗ R) : t = 0        ** (1) for F = Q **
deningerRationalMilnorAmplitude                                              ** (2) for F = Q **
    degree 0 ≅ R ,  degree 1 ≅ Q^x ⊗ R ,  degree ≥ 2 = 0
```

This is `deningerMilnorDegTensorReal_eq_zero` — already in the tree — fed with
`milnorKDegTwo_rat_torsion`.  Nothing is assumed.

### Scope, unchanged

Tate's argument uses the division algorithm, so it settles `F = Q` (and would extend to the
Euclidean imaginary quadratic fields).  The card's `(1)` for an arbitrary algebraic `F/Q` still needs
the torsion of the tame kernel of an arbitrary number field — Garland's finiteness of `K_2(O_K)`, or
Quillen finite generation with Borel's rank computation.  What has changed is that the *shape* of
the remaining input is now visible in Lean: `milnorKDegTwo_torsion_of_tameKernel_torsion` consumes
exactly one hypothesis, and for `Q` that hypothesis is now a theorem.

## Stage-3 gate audit — 2026-08-18: the card has TWO research-scale blockers, not one

A stage-3 attempt was made and the gate does not open.  Recording exactly why, with the literature
check, so the next session does not repeat the search.

### Blocker 1 — `(1)`, and the route that was planned for it is unsound

The Lean chain is unchanged and correct: everything on the near side of `(1)` is unconditional, and
`deningerMilnorRealVanishing_of_tameKernelTorsion` consumes exactly *"the degree-two tame kernel of
every number field is torsion"*.  For `F = ℚ` that hypothesis is now a theorem
(`milnorKDegTwo_rat_torsion`, Tate's computation, formalized here), so `(1)` and `(2)` hold
unconditionally over `ℚ`.  For an arbitrary number field it is Garland's finiteness theorem.

The programme card `garland-formalization-programme` selected Garland's *p-adic curvature* method
for it, on the grounds that it is "combinatorial and linear-algebraic".  **That route does not
close**, and the reason is recorded in full on that card and on `garland-tame-kernel-torsion`:

- Garland's 1971 `K₂`-finiteness theorem is an **archimedean** argument (Riemannian geometry and
  harmonic forms, `H²(SL_n(𝔬), ℝ) = 0` for `n > 6`), not the building argument.
- Garland's 1973 building/spectral-gap theorem has **cocompactness** of the lattice as a hypothesis.
  An `S`-arithmetic lattice is uniform iff the group is anisotropic; `SL_n` is isotropic over every
  number field, so `SL_n(𝒪_S)` is non-uniform, its cell stabilizers in the Bruhat–Tits building are
  infinite arithmetic groups, and the equivariant descent is an isotropy spectral sequence whose
  low rows are exactly the cohomology one is trying to kill.

A literature sweep (August 2026) found **no** elementary or algebraic proof of rank zero for
`K₂(𝒪_F)`: every published route is Borel's stable cohomology of arithmetic groups (equivalently
Garland 1971), Quillen finite generation with Borel's rank computation, Soulé with
Quillen–Lichtenbaum, or the recent Bader–Sauer higher-Kazhdan restriction theorem — all analytic.
Sum-of-squares certificates for cohomological Laplacians are not uniform in `F` and are excluded by
the project's no-computation rule.

So `(1)` is blocked on a classical theorem whose formalization is a multi-year analytic project, and
the corpus's Layer C and Layer D4 — which *are* correct, and are to my knowledge the first
formalization of Garland's 1973 method — do not reach it.

### Blocker 2 — `(4)` needs homotopy theory mathlib does not have

Independently of `(1)`, the card's `(4)` is an equivalence of `E_∞`-algebras obtained by derived base
change along `DAC_CHARACTER_SHAPE_FORMALITY`.  Mathlib has no `E_∞`-algebras, no `∞`-categories and
no derived tensor product of ring spectra, so `(4)` cannot even be *stated*.  Only its closing
assertion — that products of two degree-one classes vanish — is formalized
(`deningerGradedDegreeOne_mul_eq_zero`).

### What the card does own, unconditionally

`(3)` in full (`deningerRealificationTorsionEquiv`), `(2)` in degrees `0` and `1`
(`deningerMilnorDegZeroRealEquiv`, `deningerMilnorDegOneRealEquiv`), the whole reduction chain of
`(1)` down to the tame kernel, Tate's theorem giving `(1)` and `(2)` outright for `F = ℚ`
(`deningerRationalMilnorRealVanishing`, `deningerRationalMilnorAmplitude`), and the square-zero
consequence of `(4)`.  **Do not** promote the card by replacing its statement with the `F = ℚ` case:
that is a strict weakening of the headline.

### The route-independent work that is worth doing next

1. **Matsumoto's theorem** `K₂(F) ≅ K₂^M(F)` — needed on *every* route, purely algebraic, and Layer B
   already carries the Steinberg group, `K₂`, centrality, perfectness and the symbol.
2. **Localization** identifying the Milnor tame kernel of `𝒪_S` with `K₂(𝒪_S)`.
   `HTGeometry/DedekindResidueFieldAtPlace.lean` (landed 2026-08-18) is the first brick: the residue
   field at a finite place is `R ⧸ v.asIdeal`, *with* the compatibility that sends the residue of an
   element of `R` to its class mod `v`, plus surjectivity of `R` onto the residue classes.
3. **Milnor's exact sequence** for `F(t)` and the Bass–Tate–Kato norm.

## CORRECTION — 2026-08-18: `(4)` is NOT a blocker.  The card has exactly ONE remaining input

The "Stage-3 gate audit" entry above named two blockers.  The second — "`(4)` needs homotopy theory
mathlib does not have" — is **wrong**, and was wrong when written: it repeated this card's own older
Lean-status text instead of checking the tree.  The corpus itself supplies the missing layer.

### What the corpus already owns for `(4)`

`deninger-character-shape-formality` is **at stage 3**, and the stage-3 cards
`cdga-module-derived-tensor-layer` and `cdga-bar-construction` carry a 79-module commutative
differential graded algebra stack.  Over a field of characteristic zero — which is where this card
lives, its coefficients being `ℝ` — commutative DGAs model `E_∞`-algebras, which is exactly the
reduction the formality card's own proof invokes.  Verified present and axiom-clean
(`propext, Classical.choice, Quot.sound`):

```text
HTGeometry.freeExteriorCDGAHom, …_unique      (3): the free CDGA on degree-one generators is Λ*
RHTower.deningerTorusFormality_isQuasiIso     (2)/(4) of the formality card, for the card's own
                                              lattice filtration, with no choice left to make
HTGeometry.relTensorCDGA                      the relative tensor product of algebras over a base
HTGeometry.derivedBaseChange_zigZag           (5): both legs of the derived base change are
                                              quasi-isomorphisms; (6) follows on cohomology
```

So the derived-tensor comparison `𝒞^M_{F,ℝ} ≃ 𝒦^M_{F,ℝ}` of this card's `(4)` is available, and its
remaining content — that `𝒦^M_{F,ℝ}` *is* `H(ℝ ⊕ Σ_ar((F^×/μ_∞) ⊗ ℝ))` with square-zero positive
degrees — is `(1)`+`(2)`+`(3)` plus `deningerGradedDegreeOne_mul_eq_zero`, all already here.

### The card, assembled into one conditional theorem

`formal/GaloisForLFunctions/RHTower/DeningerAlgebraicMilnorAmplitude.lean` (wired into the `RHTower`
umbrella; axiom audit `propext, Classical.choice, Quot.sound`).

```text
deningerAlgebraicUnitRealification   ** (3), UNCONDITIONALLY **
deningerAlgebraicMilnorAmplitude     ** (1) and (2) from the single classical hypothesis **
deningerAlgebraicMilnorSquareZero    ** the square-zero conclusion of (4) **
```

`deningerAlgebraicMilnorAmplitude` takes exactly one hypothesis:

```text
for every number subfield K of F, every element of the degree-two tame kernel of K is torsion
```

and produces `(1)` and `(2)` in full.  Nothing else is assumed.

### Consequence

**The card is one classical input from stage 3, and that input is `K₂(𝒪_K) ⊗ ℚ = 0` — Borel's rank
computation, equivalently Garland 1971.**  There is no second blocker.  Work on `E_∞` infrastructure
for this card is finished; all remaining effort belongs to
`garland-tame-kernel-torsion` / `k2-rank-divisibility-firewall`.

## Lean status audit — 2026-08-18 (second pass)

Claim-by-claim, against the tree:

| claim | status |
|---|---|
| `(1)` `K_q^M(F) ⊗ ℝ = 0` for `q ≥ 2` | **OPEN** — reduces to `K₂(𝒪_K) ⊗ ℚ = 0`; the card's own proof cites Borel through Gallauer's Remark 6.8 |
| `(2)` degrees `0` and `1` of the amplitude | **PROVED** — `deningerMilnorDegZeroRealEquiv`, `deningerMilnorDegOneRealEquiv` |
| `(2)` degrees `≥ 2` | follows from `(1)`; formal as `deningerMilnorRealVanishing_of_tameKernelTorsion` |
| `(3)` `F^× ⊗ ℝ ≅ (F^×/μ_∞) ⊗ ℝ` | **PROVED** — `deningerRealificationTorsionEquiv` (documented in the tree as "the realification isomorphism (3)") |
| `(4)` the `E∞` / derived statement | **PROVED** — the corpus's CDGA stack (`deninger-character-shape-formality`, at stage 3), which is the char-0 model of `E∞`-algebras the card's own reduction uses |
| the two-term assembly | **PROVED** given `(1)` — `deningerAlgebraicMilnorAmplitude` |

So every component of the card except `(1)` is formal and unconditional, and `(1)` is a single named
classical input.

### What was built for `(1)` in this pass

The two halves of `K₂(𝒪_K) ⊗ ℚ = 0` are *finite generation* and *rank zero*.

**Finite generation** — reduced to one classical theorem, everything else proved:

```text
divisibility_firewall                  no finite-coefficient information can substitute
steinbergGroup_fg_of_moduleFinite      St(𝒪) is finitely generated
fg_ker_of_central_of_isFinitelyPresented   central extension of an FP group by an FG group
exists_finite_relators                 B. H. Neumann: FP is independent of the presentation
isFinitelyPresented_of_finite          finite groups are finitely presented
isFinitelyPresented_of_macbeath        ** MACBEATH'S THEOREM **
isFinitelyPresented_of_macbeath_convex on an open convex domain
isOpen_posDefCone, convex_posDefCone   the positive definite cone
posDefConeMulAction                    the SL(n, ℤ) action
properlyDiscontinuousSMul_posDefCone   ** the action is properly discontinuous **
exists_arithmeticMinimum               the arithmetic minimum is attained
--------------------------------------------------------------------------------------
Siegel's fundamental set with finitely many overlaps                        [OPEN]
```

**Rank zero** — untouched; needs Borel's rank computation, or Tate/Merkurjev–Suslin
(`K₂(𝒪_S) ⊗ ℤ_p ≅ H²_ét(𝒪_S[1/p], ℤ_p(2))`) together with Iwasawa's weak Leopoldt
(`H²_ét(𝒪_S[1/p], ℚ_p(2)) = 0`).

### Also completed in this pass, independently of `(1)`

**Milnor's exact sequence** `0 → K_n^M(F) → K_n^M(F(t)) → ⊕_π K_{n−1}^M(F[X]/π) → 0` is now formal
and unconditional for every field and every degree — see the ledger on
`garland-tame-kernel-torsion.md`.  This was the card's own listed route-independent remaining work.

## Lean status audit — 2026-08-19 (Bass–Tate pass)

### New unconditional theorem: the degree drop

Claim `(1)` now holds **unconditionally in Lean for every number field, in every degree above its
degree over `ℚ`**:

```text
RHTower.deningerNumberFieldMilnorRealVanishing
  F a number field, m ≥ [F : ℚ] + 1   ⟹   K_m^M(F) ⊗ ℝ = 0
```

This needs no input whatsoever about the tame kernel — no Garland, no Borel, no Quillen.  It is the
Lean formalisation of **Bass and Tate's generators for a simple extension** run over `ℚ`, where
Tate's Euclidean computation already gives `K_j^M(ℚ)` torsion for `j ≥ 2`.

The chain, all newly proved:

```text
exists_monic_irreducible_factorization  a nonzero polynomial is a constant times monic irreducibles
slotClass_prod                          a product in one slot expands into a sum of symbols
nzList_class_mem_goodSpan               every symbol is a combination of symbols whose entries are
                                        constants or monic irreducibles, at no cost in total degree
milnorClassDeg_perm                     permuting entries changes the class by a sign
nzList_class_mem_incSpan                ** BASS–TATE GENERATORS FOR L_d **: the degree filtration is
degreeFiltration_le_incSpan             generated by symbols whose non-constant entries are monic
                                        irreducibles of pairwise distinct degrees
mem_bassTateSpan                        ** BASS–TATE GENERATORS FOR F[X]/π **: applying the residue
                                        at π, all remaining degrees drop below deg π
length_le_of_distinctDegrees            hence at most deg π − 1 entries are non-constant
polyConstHom, resEntry_const            the constant entries are images from the base field
milnorKDeg_torsion_of_bassTate          ** THE DEGREE DROP **
milnorKDeg_torsion_of_finite_separable  via the primitive element theorem
milnorKDeg_numberField_torsion          over ℚ, with Tate's computation as the base case
```

The reduction move behind `nzList_class_mem_incSpan` is the classical identity
`{π, π'} = {f, π'} − {f, π} + {−1, π}` for `f = π − π'`, obtained here from `twoSlot_add_split`
together with `{a,a} = {a,−1}`.

### What the degree drop does *not* reach

The bound is `m ≥ [F : ℚ] + 1`, so degrees `2 ≤ m ≤ [F : ℚ]` remain open for every number field of
degree at least two.  In particular **degree two is never reached**, and by the product structure
degree two is the only degree that matters:

```text
milnorKDeg_mem_torsion_of_two   K_2^M(F) torsion ⟹ K_m^M(F) torsion for every m ≥ 2
```

so `(1)` is *equivalent* to `K_2^M(F)` torsion for every finite subextension, i.e. to the torsion of
the tame kernel of every number field.  No amount of the Bass–Tate generation argument reaches it:
the generation bound loses one degree per unit of extension degree, and a tower only replaces
`d − 1` by `∑ (d_i − 1)`, which is still at least one for any nontrivial extension.

### The remaining input, stated exactly

`K_2(𝒪_K)` is torsion for every number field `K`.  Every published route needs one of:

1. **Borel** (analytic): the stable real cohomology of `SL_n(𝒪_K)` is the continuous cohomology of
   the symmetric space, whose primitive classes sit in degrees `5, 9, …` (real places) and
   `3, 5, 7, …` (complex places) — none in degree two.
2. **Garland 1971** (analytic): harmonic forms on the arithmetic quotient.
3. **Quillen finite generation + Borel.**
4. **Tate / Merkurjev–Suslin + Iwasawa weak Leopoldt** (algebraic, but étale): `K_2(𝒪_S) ⊗ ℤ_p ≅
   H²_ét(𝒪_S[1/p], ℤ_p(2))` and `H²_ét(𝒪_S[1/p], ℚ_p(2)) = 0`.
5. **Moore's theorem + finite generation** (class field theory): Moore's exact sequence
   `K₂(F) → ⊕_{v non-complex} μ(F_v) → μ(F) → 1` identifies the kernel with the maximal divisible
   subgroup; a finitely generated abelian group has no nonzero divisible subgroup; and the maximal
   divisible subgroup always lies in the tame kernel because `⊕_v k(v)^×` is a direct sum of finite
   groups and so has no nonzero divisible subgroup.  Hence
   `K₂(𝒪_K) finitely generated + Moore ⟹ K₂(F) embeds in a torsion group`.

Route 5 is the cheapest algebraically and is the one the corpus is building towards: its finite
generation half is reduced to Siegel's fundamental set (see above) and its rank-zero half is Moore's
theorem.

### The tower form of the bound

The degree drop composes, so a tower costs the sum of its steps:

```text
RHTower.deningerMilnorRealVanishing_tower
  ℚ ⊆ E ⊆ L,  m ≥ 2 + ([E : ℚ] − 1) + ([L : E] − 1)   ⟹   K_m^M(L) ⊗ ℝ = 0
```

For a field of degree `8` with a full tower of quadratic steps this gives `m ≥ 5` instead of
`m ≥ 9`.  It never reaches degree two, since every nontrivial step costs at least one.

### Milnor's norm

The norm map of Bass and Tate is now formal (`milnorNormAt`, `milnorNormAt_spec`), together with
both halves of Milnor's sequence in final form (`mem_range_of_residues_zero`,
`exists_residue_single`) and the residue at infinity (`milnorResidueInfty`).  This is the transfer
machinery that Moore's theorem — route 5 above — is built on.

## Finite generation kills the divisible kernel (2026-08-26)

`formal/GaloisForLFunctions/HTGeometry/FinitelyGeneratedDivisibleSubgroup.lean` formalizes the
firewall-breaking group-theoretic step used by route 5:

```text
eq_zero_of_fg_of_nsmul_surjective
subsingleton_of_fg_of_nsmul_surjective
addSubgroup_eq_bot_of_fg_of_nsmulDivisible
addSubgroup_eq_bot_of_le_fg_of_nsmulDivisible
directSumFinite_isTorsion
addMonoidHom_eq_zero_of_nsmulDivisible_directSumFinite
addSubgroup_le_ker_of_nsmulDivisible_directSumFinite
isTorsion_of_fg_of_ker_nsmulDivisible_directSumFinite
isTorsion_of_ker_le_fg_of_ker_nsmulDivisible_directSumFinite
```

A finitely generated divisible abelian group is first forced to be torsion: otherwise the existing
finite-generation theorem gives a quotient onto `ZMod 2`, while divisibility forces every map to a
finite abelian group to vanish.  A finitely generated torsion abelian group is finite, and
surjectivity of multiplication by its cardinality then kills every element.  No structure theorem
is postulated at the theorem boundary.

The direct-sum lemmas also prove, for an arbitrary reciprocity map, that every divisible subgroup
of its source lies in its kernel.  This formalizes the card's claim that the maximal divisible
subgroup lies in the tame kernel when residues land in a direct sum of finite groups.

Crucially, the final assembly needs finite generation only of a subgroup containing the divisible
kernel, not of the whole source.  This is the exact tame-kernel configuration in route 5.

The leaf passes direct checking and targeted build.  All nine declarations audit to only
`[propext, Classical.choice, Quot.sound]`; it is wired into `HTGeometry` without building the
umbrella.

Thus, once finite generation of the tame kernel and Moore's identification of its maximal
divisible subgroup are supplied, no further abstract group theory is needed to deduce that the
divisible kernel is zero.  The final theorem packages the Moore-style conclusion itself: a
finitely generated source mapping to a direct sum of finite groups is torsion whenever its
reciprocity kernel is divisible.  Finite generation and Moore reciprocity remain the two classical
arithmetic producers; card stays Stage 2.

## Divisible Milnor classes land in the actual tame kernel (2026-08-26)

`formal/GaloisForLFunctions/HTGeometry/MilnorTameDivisibleKernel.lean` specializes the preceding
direct-sum theorem to the corpus's finite-place Milnor residue map.  It first transports finiteness
through the already-proved equivalence `K₁ᴹ(F) ≃ Fˣ`:

```text
finite_milnorKDeg_one
addSubgroup_le_milnorTameKernel_of_nsmulDivisible_of_finiteResidue
addSubgroup_le_milnorTameKernel_of_nsmulDivisible_numberField
milnorKDegTwo_isTorsion_of_tameKernel_fg_of_ker_nsmulDivisible_numberField
```

For every number field, each residue target is therefore finite.  Any divisible subgroup of
`K₂ᴹ(K)` maps trivially under the total residue homomorphism and hence lies in the exact
finite-place tame kernel, using `milnorTameKernel_eq_ker_milnorTotalResidue`.  This closes the
previously informal containment used in route 5.

The capstone composes that containment with the finitely-generated-subgroup assembly: finite
generation of the actual tame kernel plus any Moore reciprocity map whose kernel is divisible
forces `K₂ᴹ(K)` itself to be torsion.  No finite-generation assumption on the full Milnor group is
introduced.

The leaf passes direct checking and targeted build.  Its instance and three theorems audit to only
`[propext, Classical.choice, Quot.sound]`; it is wired into `HTGeometry` without building the
umbrella.  Remaining arithmetic producers are still finite generation of the tame kernel and
Moore's reciprocity/maximal-divisible-kernel theorem.  Card remains Stage 2.

## Lean progress — the covering radius, first brick of the `𝒪_F` reduction theory (2026-08-29)

The card's remaining arithmetic producers are finite generation of the tame kernel and Moore's
reciprocity.  The corpus's finite-generation route (`central-extension-fg-shortcut`) is reduced to
`SL_n(𝒪_F)` being **finitely presented**, and that is Macbeath applied to the `𝒪_F`-Hermitian slice
of the positive-definite cone.  Of the two halves of the Siegel property, the *finiteness* half is
inherited free from `siegel_finiteness` over `ℤ`; the *covering* half has two inputs that `ℤ` gets
for free:

1. size reduction to `|·| ≤ 1/2` — over `𝒪_F` this becomes the **covering radius** of the lattice
   `𝒪_F ⊆ F ⊗ ℝ`;
2. "a primitive vector extends to a basis" — over a Dedekind domain this becomes **Bass's stable
   range theorem**.

Input 1 is now closed.  `formal/GaloisForLFunctions/HTGeometry/LatticeCoveringRadius.lean`,
unconditional, axiom-clean, wired into `HTGeometry`:

```text
exists_intCombination_dist_le   ‖x − ∑ nᵢ bᵢ‖ ≤ (1/2)∑‖bᵢ‖ for nᵢ = round (b.repr x i)
zspan_dense_of_basis            the ℤ-span of a real basis is that dense
exists_coveringRadius           a single constant works for every vector
```

The number-field instantiation is `NumberField.mixedEmbedding.latticeBasis` together with
`NumberField.mixedEmbedding.span_latticeBasis` — the `ℤ`-span of that basis *is* the image of the
ring of integers — once a norm is fixed on the mixed space.  What the descent needs is the
boundedness, not the constant `1/2`, so this is the whole of input 1.

**Input 2 (Bass) and Moore's theorem remain.**  Card stays Stage 2.

## Lean progress — Bass's stable range theorem for Dedekind domains (2026-08-29)

Input 2 of the `𝒪_F` covering half is now closed as well, and it is a genuine mathlib gap: mathlib
has no stable-range theory at all.

`formal/GaloisForLFunctions/HTGeometry/DedekindStableRange.lean`, unconditional, axiom-clean, wired
into `HTGeometry`:

```text
exists_stableRange_two
    for a Dedekind domain `R` and `u a + v b + w c = 1`,
      ∃ x y p q,  p (a + x c) + q (b + y c) = 1
```

This is what replaces "a primitive vector extends to a basis" — true over a principal ideal domain,
false over a general Dedekind domain — and it is the reason `SL_n(𝒪_F)` acts transitively on
unimodular vectors for `n ≥ 3`.

**The proof, recorded because the choice is the whole content.**  If `b = 0` the pair `(a, c)` is
already unimodular and `x = 0`, `y = 1` works.  Otherwise `Ideal.finite_factors` gives finitely many
maximal ideals containing `b`, and one `x` handles all of them by the Chinese remainder theorem
(`Ideal.exists_forall_sub_mem_ideal`, the ideals being pairwise coprime because distinct maximal
ideals are):

* where `c` lies in the maximal ideal, `a` cannot — `a`, `b`, `c` would all lie in it, against
  unimodularity — so nothing is prescribed there;
* where `c` does not, `c` is invertible modulo it (`Ideal.IsMaximal.exists_inv`) and `x` is
  prescribed to make `a + xc ≡ 1`.

Then `y = 0` works: a maximal ideal containing `a + xc` and `b` is nonzero (it contains `b ≠ 0`),
hence a height-one point in the finite set, and both cases give `1` in the ideal.

### State of the `𝒪_F` reduction-theory layer

| input | status |
|---|---|
| Macbeath on the `𝒪_F`-Hermitian slice (open, convex) | inherited from the `ℤ` layer |
| Siegel *finiteness* half | inherited — `siegel_finiteness` |
| covering: bounded size reduction | **closed** — `exists_coveringRadius` |
| covering: primitive vector normalisation | **closed** — `exists_stableRange_two` |
| the covering descent itself over `𝒪_F` | to build |
| `SL_n(𝒪_F)` finitely presented ⟹ `K₂(𝒪_F)` f.g. | owned (`fg_ker_of_central_extension`, `steinbergGroup_fg_of_moduleFinite`) |
| Moore's reciprocity / maximal divisible kernel | **the remaining classical producer** |

### Vaserstein's lemma — stable range two at every length (2026-08-29)

The note above recorded that the length-`m` form is *not* immediate from the three-variable case,
because the obvious grouping needs the shift to lie in the ideal generated by the certificate
coefficients.  The grouping that does work puts the **whole tail** into the auxiliary coordinate,
and with it the induction is five lines:

```text
exists_stableRange_vector
    ∀ n ≥ 2, ∀ a : Fin n → R, ∀ c,  (∑ uᵢaᵢ) + w c = 1  →
      ∃ x p : Fin n → R,  ∑ pᵢ (aᵢ + xᵢ c) = 1
```

With `d = u_last · a_last + w · c`, the shorter vector `(a₁, …, a_{n−1}, d)` is unimodular, and a
shift by `d` is a shift by `w·c` followed by an *elementary* operation adding a multiple of `a_last`
— which does not change unimodularity, so the shifted vector `(aᵢ + xᵢ w c)ᵢ` together with
`a_last` is unimodular with the last shift equal to zero.

Unconditional, axiom-clean, umbrella-wired.

**Next on this input**: `SL_n(𝒪)` acts transitively on unimodular vectors for `n ≥ 2`.  The chain is
now fully determined: `n = 2` is the explicit matrix `!![p, q; −v₁, v₀]` (determinant `p v₀ + q v₁ =
1`, and it sends `v` to `e₀`) over *any* commutative ring; for `n ≥ 3`, `exists_stableRange_vector`
makes the first `n−1` coordinates unimodular by transvections in the last column, a second
unitriangular factor clears the last coordinate, and the induction hypothesis finishes.

### `SL_n` acts transitively on unimodular vectors over a Dedekind domain (2026-08-29)

`formal/GaloisForLFunctions/HTGeometry/UnimodularTransitivity.lean`, unconditional, axiom-clean,
umbrella-wired:

```text
lastColMat f, det_lastColMat, lastColMat_mulVec
    upper unitriangular with a prescribed last column: determinant one, and it adds fᵢ·v_last to
    every other coordinate
lastRowMat g, det_lastRowMat, lastRowMat_mulVec_castSucc, lastRowMat_mulVec_last
    lower unitriangular with a prescribed last row
extendMat γ, det_extendMat, extendMat_mulVec_castSucc, extendMat_mulVec_last
    extension by a `1` in the last diagonal slot, through `finSumFinEquiv` and `fromBlocks`
exists_det_one_mulVec_eq_single
    **for `n ≥ 2` and `v` unimodular over a Dedekind domain, ∃ γ with det γ = 1 and γ·v = e₀**
```

The base case `n = 2` is the explicit `!![p, q; −v₁, v₀]` and works over *any* commutative ring; its
determinant is `p v₀ + q v₁ = 1` and it visibly sends `v` to `e₀`.  The step is exactly Bass:
`exists_stableRange_vector` makes the first `n` coordinates unimodular after adding multiples of the
last (one `lastColMat` factor), the certificate then clears the last coordinate (one `lastRowMat`
factor), and the induction hypothesis acts through `extendMat`.  The target is stated
coordinatewise, `(γ ·ᵥ v) i = if i = 0 then 1 else 0`, so that no `Zero (Fin n)` instance is needed
inside the induction.

### State of the `𝒪_F` reduction-theory layer, updated

| input | status |
|---|---|
| Macbeath on the `𝒪_F`-Hermitian slice | inherited |
| Siegel *finiteness* half | inherited |
| covering: bounded size reduction | **closed** — `exists_coveringRadius` |
| covering: primitive vector normalisation | **closed** — `exists_det_one_mulVec_eq_single` |
| the covering descent itself over `𝒪_F` | to build |
| `SL_n(𝒪_F)` f.p. ⟹ `K₂(𝒪_F)` f.g. | owned |
| Moore's reciprocity | **the remaining classical producer** |

### A unimodular vector extends to a basis (2026-08-29)

`exists_det_one_firstCol_eq` (in `UnimodularTransitivity`), unconditional, axiom-clean:

```text
for a Dedekind domain `R`, `n ≥ 2` and `v` unimodular,
  ∃ β with det β = 1 and first column `v`
```

This is the inverse of the transitivity statement — `γ·v = e₀` gives `β := γ⁻¹` with `β·e₀ = v` and
`det β = 1` — and it is the form the covering descent consumes.  It settles the card's remark that
"a primitive vector extends to a basis" is unavailable over a Dedekind domain: it *is* available for
`n ≥ 2`, once Bass's stable range theorem supplies the transitivity; what fails over a Dedekind
domain is the corresponding statement for projective modules of rank one, which the descent does not
use.

### State of the `𝒪_F` reduction-theory layer, updated

| input | status |
|---|---|
| Macbeath on the `𝒪_F`-Hermitian slice | inherited |
| Siegel *finiteness* half | inherited |
| covering: bounded size reduction | **closed** — `exists_coveringRadius` |
| covering: primitive vector normalisation | **closed** — `exists_det_one_mulVec_eq_single` |
| covering: extension to a basis | **closed** — `exists_det_one_firstCol_eq` |
| the covering descent itself over `𝒪_F` | to build — the Hermite/Siegel induction: a minimal primitive vector, the split above, and size reduction by the covering radius |
| `SL_n(𝒪_F)` f.p. ⟹ `K₂(𝒪_F)` f.g. | owned |
| Moore's reciprocity | the remaining classical producer |

### Concrete number-field covering radius (2026-08-29)

`formal/GaloisForLFunctions/HTGeometry/NumberFieldIntegerCoveringRadius.lean` discharges the
structural basis/span premise left implicit by `LatticeCoveringRadius`:

```text
exists_numberFieldInteger_coveringRadius
    ∃ R ≥ 0, ∀ x : mixedEmbedding.mixedSpace K,
      ∃ a : 𝓞 K, ‖x - mixedEmbedding K (a : K)‖ ≤ R

exists_numberFieldInteger_coordinateCoveringRadius
    the same algebraic integer simultaneously approximates every real and complex place coordinate
```

The witness is an actual algebraic integer, obtained by rewriting the integral span of mathlib's
`mixedEmbedding.latticeBasis` as `mixedEmbedding.integerLattice`.  Thus no arbitrary Hilbert-space
basis, lattice-span equality, density hypothesis, or ambient-norm-to-place-bound hypothesis remains
in the size-reduction input.

Targeted module build passed.  Axiom audit:
`[propext, Classical.choice, Quot.sound]`.  Umbrella-wired.

Card remains Stage 2: covering descent over `𝓞 K`, finite generation of the tame kernel, and
Moore reciprocity remain.

### Canonical integral basis and matrix size reduction (2026-08-29)

Two further unconditional modules remove arbitrary coordinate and matrix hypotheses:

- `NumberFieldIntegerBasis.lean` reindexes `RingOfIntegers.basis K` by
  `Fin (Module.finrank ℚ K)`.  Its index equivalence is proved from
  `Module.finrank_eq_card_chooseBasisIndex` and `RingOfIntegers.rank`; no basis is supplied as data.
- `NumberFieldIntegerMatrixReduction.lean` applies the concrete covering radius entrywise.  It
  produces, with one field-dependent radius, both arbitrary integral matrix approximants and a
  strict-upper approximant whose completed matrix is upper unitriangular over `𝓞 K` with determinant
  exactly `1`.

The latter is the exact integral unipotent witness used by Hermite/Siegel size reduction.  No
integrality, upper-triangularity, unimodularity, determinant, per-place selection, or common-radius
hypothesis remains external.

Both targeted module builds passed.  Axiom audits:
`[propext, Classical.choice, Quot.sound]`.  Both modules are umbrella-wired.

Card remains Stage 2: the induction assembling these witnesses into full covering descent, the
finite-generation bridge for the tame kernel, and Moore reciprocity remain.

### Number-ring Steinberg finite generation (2026-08-29)

`NumberFieldSteinbergFiniteGeneration.lean` now specializes the existing ring-level generation
theorems without external premises:

```text
numberFieldInteger_steinbergGroup_fin3_fg
    Group.FG (SteinbergGroup (𝓞 K) (Fin 3))

numberFieldInteger_elementaryGroup_fin3_fg
    Group.FG (elementaryGroup (𝓞 K) (Fin 3))
```

`Module.Finite ℤ (𝓞 K)` is inferred from the number-field structure.  The rank-three root-index
condition is discharged from `Fintype.card (Fin 3) = 3`, not retained as a hypothesis.

Targeted module build passed.  Axiom audit:
`[propext, Classical.choice, Quot.sound]`.  Umbrella-wired.

Card remains Stage 2.  Finite generation of the Steinberg source is closed; still required are full
`𝓞 K` covering/presentation, identification and centrality of the relevant tame-kernel quotient,
and Moore reciprocity.

### Minimal primitive vector over `𝓞 K` (2026-08-29)

`LatticeSubsetMinimum.lean` strengthens the shortest-vector compactness lemma from a whole discrete
submodule to every nonempty subset of that lattice.  This distinction is necessary: primitive
vectors over a non-PID Dedekind domain are not a submodule.

`NumberFieldPrimitiveLattice.lean` then constructs the coordinatewise mixed-embedding lattice

```text
numberFieldIntegerVectorLattice K n
    ⊆ Fin n → mixedEmbedding.mixedSpace K
```

identifies it homeomorphically with the finite product of mathlib's concrete integer lattices,
derives its discrete topology, proves the primitive subset nonempty, and obtains:

```text
exists_numberFieldInteger_minimalPrimitiveVector
    a primitive a : Fin n → 𝓞 K minimizing the mixed-embedding product norm

exists_numberFieldInteger_minimalPrimitiveVector_detOneFirstCol
    the same a together with β over 𝓞 K, det β = 1, first column β = a
```

No PID assumption, arbitrary lattice, discreteness premise, primitive-vector existence premise, or
basis-extension premise remains.

Both targeted module builds passed.  Axiom audits:
`[propext, Classical.choice, Quot.sound]`.  Both modules are umbrella-wired.

Card remains Stage 2.  Remaining covering brick: transport this minimum from the standard mixed norm
to each positive balanced order form and carry the resulting block induction through the existing
size-reduction witness.  Arithmetic bridge and Moore reciprocity remain afterward.

### Positive order-form primitive minimum (2026-08-29)

Three unconditional modules close the previously retained frame/form hypotheses:

- `NumberFieldMixedVectorCoordinates.lean` reindexes the mixed-embedding lattice basis by
  `Fin (finrank ℚ K)`, flattens `n` copies to `Fin (n * finrank ℚ K)`, and proves that embedded
  algebraic-integer vectors have exactly their canonical integral-basis coefficients.
- `NumberFieldPositiveFormPrimitiveMinimum.lean` factors every positive-definite matrix through an
  invertible Euclidean Jacobi frame and applies lattice-subset minimization.  It returns an actual
  primitive `a : Fin n → 𝓞 K`, a determinant-one matrix with first column `a`, and the direct
  quadratic-form minimum inequality.
- `NumberFieldOrderFormPrimitiveMinimum.lean` specializes this to every point of the positive
  balanced order cone for the canonical basis of `𝓞 K`.

Thus no arbitrary coordinates, continuous linear equivalence, lattice, discreteness, minimizer, or
positive-definiteness premise remains in the order-form minimum.  All three targeted module builds
passed; axiom audits are `[propext, Classical.choice, Quot.sound]`; all are umbrella-wired without
building the umbrella.

Card remains Stage 2.  The exact next open implication is the block induction converting this
minimum plus `exists_numberFieldInteger_unipotentUpperReduction` into order-Siegel covering.  The
later arithmetic obligations remain tame-kernel finite generation and Moore reciprocity.

### Principal and Schur rank descent for order forms (2026-08-30)

Three unconditional modules close the structural rank-lowering step used by the Hermite--Siegel
induction:

- `OrderPrincipalRestriction.lean` characterizes balancedness blockwise and proves that every
  injective selection of complete order blocks preserves symmetry, balancedness and positive
  definiteness.  In particular `orderConeCastSucc` and `orderConeTail` lower rank with no retained
  form, balance or positivity premise.
- `RealSchurPosDef.lean` proves the real block Schur theorem by an explicit upper-unitriangular
  congruence: the Schur complement of an invertible symmetric head in a positive-definite block
  form is positive definite.
- `OrderSchurRestriction.lean` applies that theorem to a positive balanced order form.  It proves
  the head block positive and invertible, identifies the exact head/tail block decomposition, and
  uses the block self-adjointness identities to show that the Schur complement remains balanced.
  The resulting `orderConeSchur` is the canonical rank-`n+1` to rank-`n` descent with every
  invertibility, symmetry, positivity and balancedness condition discharged internally.

All three targeted builds passed.  Axiom audit for every new declaration:
`[propext, Classical.choice, Quot.sound]`.  All three modules are umbrella-wired without an
umbrella build.

Card remains Stage 2.  What remains in the covering half is no longer preservation of the order
cone under block descent; it is the quantitative induction showing that the concrete primitive
minimum and concrete number-field unipotent size reduction put every successive Schur tail in one
fixed order-Siegel region.  The later arithmetic obligations remain finite generation of the tame
kernel and Moore reciprocity.

### Regular-representation coordinate transport (2026-08-30)

`OrderRepVectorCoordinates.lean` closes the coordinate seam between the minimum theorem and the
order action:

```text
orderRep_mulVec_orderVectorCoordsZ
    the integral regular representation acts on flattened basis coordinates exactly as the
    original order matrix acts on the order-valued vector

orderRepR_mulVec_orderVectorCoordsR
    the same identity after passage to real coordinates

numberField_orderVectorCoordsR_eq
    these real basis coordinates are exactly the canonical mixed-embedding coordinates used by
    NumberFieldOrderFormPrimitiveMinimum

numberField_orderRepR_mulVec_mixedCoordinates
    a number-ring matrix acting through orderRepR transports the literal mixed-embedding vector
    coordinates, with no coordinate-identification hypothesis
```

Targeted build passed.  Axiom audit for all declarations:
`[propext, Classical.choice, Quot.sound]`.  Umbrella-wired without an umbrella build.

Card remains Stage 2.  Primitive-vector normalization can now be performed in the same coordinates
as the positive order form.  Remaining covering work is the quantitative minimum-to-Schur-diagonal
inequality and iteration with the concrete number-field upper-unipotent reduction; arithmetic
obligations remain unchanged.

### Primitive minimum normalized to the first order coordinate (2026-08-30)

`NumberFieldOrderFormPrimitiveNormalization.lean` assembles the preceding pieces without retaining
any structural assumption:

- `orderConeCongrDetOne` proves directly that congruence by any determinant-one order matrix stays
  in the positive balanced order cone;
- `NumberFieldOrderPrimitiveNormalization` carries the literal primitive minimizer, its
  determinant-one completion, the congruent order form, the exact mixed-coordinate transport, and
  the exact quadratic-energy identity;
- `exists_numberFieldOrderPrimitiveNormalization` constructs that package for every number field,
  every `n ≥ 2`, and every point of the canonical number-ring order cone.

Thus the shortest primitive vector is now the literal first order coordinate of the congruent
form, and its first-coordinate energy is definitionally connected to the original minimum.  No
arbitrary basis, coordinate equivalence, primitive witness, determinant-one completion,
invertibility, positivity, balance, or energy-transport hypothesis survives.

Targeted build passed.  Axiom audit for all declarations:
`[propext, Classical.choice, Quot.sound]`.  Umbrella-wired without an umbrella build.

Card remains Stage 2.  Remaining covering seam is quantitative: show the normalized minimum bounds
the first diagonal against the next Schur-tail minimum with a field-only constant, then iterate and
apply the concrete upper-unipotent reduction.  Tame-kernel finite generation and Moore reciprocity
remain after covering.

### Unit reduction exposed by primitive normalization (2026-08-30)

The normalized minimum and Schur descent isolate a necessary multiplicative reduction step.  An
additive mixed-space covering radius controls off-diagonal order entries, but it cannot uniformly
compare an arbitrary positive head block with the standard mixed Euclidean norm: its archimedean
weights can have unbounded condition number.  A field-only Siegel constant therefore requires the
Dirichlet-unit logarithmic lattice and a bounded fundamental domain for the norm-zero logarithmic
hyperplane.  Determinant-one diagonal unit congruences can then balance the head weights before the
minimum-to-Schur estimate.

This is now the exact next covering obligation.  No condition-number, bounded-weight, chosen-unit,
log-lattice, or fundamental-domain hypothesis may remain in the final theorem.  Card remains Stage
2 while this number-field infrastructure is constructed; tame-kernel finite generation and Moore
reciprocity remain later obligations.

### Unconditional Dirichlet-unit reduction and full rank (2026-08-30)

The unit-reduction obligation is now discharged without retaining a chosen unit system, rank
formula, condition-number bound, lattice-span premise, or fundamental-domain hypothesis.

The new dependency chain is:

- `DeterminantOneLatticeShortVector.lean`: uniform Minkowski short vectors under every
  determinant-one positive diagonal deformation;
- `NumberFieldMixedRealCoordinates.lean`: exact split real coordinates for real and complex
  places, with complex places counted twice and weighted-zero profiles mapped to determinant one;
- `NumberFieldIntegerMinkowskiReduction.lean`: a uniform nonzero algebraic integer satisfying the
  prescribed exponential bound at every infinite place;
- `NumberFieldPrincipalIdealNormBound.lean` and `NumberFieldBoundedPrincipalIdeals.lean`: the
  weighted place bound gives a bounded principal ideal, hence one of finitely many chosen nonzero
  ideal generators;
- `NumberFieldUnitPlaceLogCovering.lean`: division by that generator produces an actual unit whose
  logarithmic place profile lies within one field-dependent radius of every weighted-zero profile;
- `NumberFieldUnitPlaceLogFullRank.lean`: dilation plus closedness of finite-dimensional subspaces
  proves that the real span of unit logarithms is exactly the weighted-zero hyperplane.

The covering theorem is stronger than a selected-fundamental-units formulation:

```text
exists_numberFieldUnitPlaceLog_coveringRadius
    ∃ R > 0, ∀ y with ∑_w mult(w)y_w = 0,
      ∃ u : (𝓞 K)ˣ, ‖log|u| - y‖ ≤ R

numberFieldUnitPlaceLogRealSpan_eq_hyperplane
    span_ℝ {log|u| : u ∈ (𝓞 K)ˣ}
      = {y : ∑_w mult(w)y_w = 0}
```

All targeted source checks and module builds passed.  Batched axiom audit for the new declarations:
`[propext, Classical.choice, Quot.sound]`.  Modules are umbrella-wired without an umbrella build.

Card remains Stage 2.  Quantitative order-Siegel descent must now consume this closed unit reduction;
tame-kernel finite generation and Moore reciprocity remain afterward.

### Determinant-one unit balancing witnesses (2026-08-30)

`NumberFieldDetOneUnitPlaceLogCovering.lean` upgrades single-profile reduction to every finite
zero-sum tuple.  It constructs units `u_i` with `∏_i u_i = 1` and one uniform bound on
`‖log|u_i| - y_i‖`; the final unit is the inverse product, and the tuple zero-sum identity bounds
its error by the sum of the remaining errors.  `NumberFieldDetOneUnitDiagonal.lean` packages that
tuple as the literal diagonal element of `SL_n(𝓞 K)` and proves its coordinate action.

Both targeted module builds pass.  Every new theorem audits to
`[propext, Classical.choice, Quot.sound]`; both modules are umbrella-wired without an umbrella
build.  Hence determinant one is no longer an external hypothesis in the unit-balancing step.

`NumberFieldDetOneUnitWeightBalancing.lean` now performs the quantitative balancing itself.  For
an arbitrary nonempty matrix of logarithmic place weights it removes the weighted place means and
the coordinate mean, proves that every residual lies in the exact unit-log hyperplane and that the
residual tuple sums to zero, then applies the determinant-one unit covering theorem.  The result is
a field-only radius and product-one units for which every rescaled log weight differs from a sum of
one coordinate-only and one place-only term by at most `2(n+1)R`.  This is the condition-number
discharge required before Hermite--Schur iteration; neither the original weights nor a boundedness
premise occurs in the theorem.

Targeted source check/build pass; all declarations audit to
`[propext, Classical.choice, Quot.sound]`; module is umbrella-wired without an umbrella build.

`NumberFieldDetOneUnitPositiveWeightBalancing.lean` exponentiates this statement.  Every positive
place-weight table is carried by a product-one unit tuple to within the explicit factor
`exp(±2(n+1)R)` of a separable coordinate-scale times place-scale table.  This is the literal
multiplicative condition-number bound consumed by reduction.  Positivity is the only lemma input
and will come from positive-definiteness of the order form; no numerical bound on the input table
is assumed.  Targeted check/build pass and the declaration audits to
`[propext, Classical.choice, Quot.sound]`; module is umbrella-wired without building the umbrella.

### Correct real/Hermitian archimedean cone and unconditional unit action (2026-08-30)

The previous regular-representation `orderCone` cannot be the symmetric space for an arbitrary
number field: its balancedness condition makes multiplication by every number-field scalar
self-adjoint, which is incompatible with a scalar having a nonreal complex-place eigenvalue.  In
particular its nonemptiness premise cannot honestly be discharged when complex places occur.

Three new modules replace that seam instead of retaining the false premise:

- `NumberFieldMixedVectorPlaceCoordinates.lean` constructs the canonical linear equivalence from
  integral-basis vector coordinates to coordinatewise split Minkowski coordinates.
- `NumberFieldArchimedeanCone.lean` defines the actual placewise symmetric space: positive real
  symmetric forms at real places and positive complex Hermitian forms at complex places.  The
  identity point proves nonemptiness for every number field.  Evaluation of
  `SL_n(𝓞 K)` at every place has determinant one and is invertible, so literal placewise
  congruence preserves Hermiticity and positive definiteness and satisfies the full action laws.
- `NumberFieldArchimedeanUnitBalancing.lean` extracts the positive local diagonal table from every
  cone point, proves that product-one unit congruence rescales its `(i,w)` entry by exactly
  `|u_i|_w²`, and applies the unconditional unit covering theorem.  The capstone
  `exists_numberFieldArchimedeanUnitDiagonal_balancingRadius` constructs the determinant-one unit
  tuple internally for every cone point with one field-only radius; no positivity,
  differentiability, bounded-condition-number, chosen-unit, or structural witness is retained as
  a theorem hypothesis.

All three direct source checks and targeted module builds pass.  Every created declaration audits
to `[propext, Classical.choice, Quot.sound]`; all modules are umbrella-wired without an umbrella
build.  Card remains Stage 2.  Remaining reduction obligation is the placewise real/Hermitian
Schur--Iwasawa induction and finite-overlap Siegel region on this corrected cone.  Tame-kernel
finite generation and Moore reciprocity remain after that covering theorem.

### Unconditional real/Hermitian Schur rank descent (2026-08-30)

`ComplexSchurPosDef.lean` upgrades the existing Haynsworth block congruence to the exact strict
positivity theorem needed at complex places: the Schur complement of the Hermitian head of a
positive-definite complex block form is positive definite.  Head invertibility and Hermiticity are
derived from the full positive form.

`NumberFieldArchimedeanSchur.lean` then performs the first-coordinate block reindexing uniformly,
identifies the full form with its head/cross/tail block matrix, proves the head and reindexed full
form positive, and applies the real or complex Schur theorem at the appropriate place.  Its
capstone is the premise-free rank-lowering map

```text
numberFieldArchimedeanSchur :
  numberFieldArchimedeanPositiveForms K (n + 1) →
    numberFieldArchimedeanPositiveForms K n
```

Both direct source checks and targeted module builds pass.  Every new declaration audits to
`[propext, Classical.choice, Quot.sound]` or a subset.  Both modules are umbrella-wired without an
umbrella build.  Card remains Stage 2.  Remaining covering seam is quantitative: compare the
unit-balanced head against the next Schur diagonal, iterate, and prove finite overlaps for the
resulting placewise Siegel region.  Tame-kernel finite generation and Moore reciprocity remain
afterward.

### Unconditional simultaneous Jacobi decomposition and unit transport (2026-08-30)

`ComplexJacobiDecomposition.lean` proves the exact complex Hermitian Jacobi factorization
`A = Uᴴ diag(d) U`, with `U` upper unipotent and every `d_i > 0`; it derives all data directly
from positive definiteness.  `NumberFieldArchimedeanJacobi.lean` applies the real and complex
factorizations simultaneously at every infinite place and forms one uniformly positive real
Jacobi-weight table.  Its balancing theorem chooses both Jacobi data and product-one units
internally.

`JacobiDiagonalRescale.lean` proves the exact real symmetric and complex Hermitian diagonal
congruence formulas, including preservation of positivity, upper triangularity, and unit diagonal.
`NumberFieldArchimedeanJacobiUnitConj.lean` specializes those identities to the actual
`SL_n(𝓞 K)` action and proves that every transported Jacobi weight is exactly its source weight
times `|u_i|_w²`.  Finally, `NumberFieldArchimedeanJacobiReduction.lean` combines this transport
with Dirichlet-unit covering: for every cone point, it constructs source and transformed Jacobi
data, a product-one unit tuple, and uniform field-only multiplicative bounds.  No supplied Jacobi
decomposition, positivity certificate, unit choice, determinant-one proof, or boundedness premise
remains in the capstone.

All direct source checks and targeted module builds pass.  Every declaration created in the three
transport/reduction modules audits to `[propext, Classical.choice, Quot.sound]`; all modules are
umbrella-wired without an umbrella build.  Card remains Stage 2.  Remaining Siegel covering work
is quantitative off-diagonal size reduction, iteration of Jacobi/Schur bounds, and finite
overlaps.  Tame-kernel finite generation and Moore reciprocity remain afterward.

### Unconditional mixed-place off-diagonal size reduction (2026-08-30)

The quantitative off-diagonal seam is now connected to the corrected real/Hermitian cone.
`NumberFieldMixedSizeReduction.lean` performs a superdiagonal sweep in the actual mixed
archimedean algebra
`(real places → ℝ) × (complex places → ℂ)`.  At every step, the number-ring covering radius
chooses the required algebraic integer internally.  The accumulated matrix is upper unipotent,
has determinant exactly one, and reduces every strict-upper mixed entry with one field-only bound.

`NumberFieldArchimedeanJacobiSizeReduction.lean` packages real Jacobi factors together with the
complex-conjugated factors, applies the mixed sweep once, and extracts simultaneous real and
complex entry bounds.  `NumberFieldArchimedeanJacobiActionReduction.lean` then transposes the
integral reducer into an actual element of `SL_n(𝓞 K)`, transports the full Jacobi decomposition
through its cone action, and proves the resulting real/complex upper factors obey the uniform
bound.  Its capstone constructs the original Jacobi data, reducer, determinant certificate,
special-linear element, and transformed Jacobi data internally; none is a theorem premise.

All direct source checks and targeted leaf builds pass.  Every declaration in all three modules
audits to `[propext, Classical.choice, Quot.sound]`; all are umbrella-wired without an umbrella
build.  Card remains Stage 2.  Remaining Siegel work is the diagonal-ratio/greedy reduction and
finite-overlap theorem on the corrected mixed-place cone; tame-kernel finite generation and Moore
reciprocity remain afterward.

### Combined mixed-place Siegel bounds (2026-08-30)

`NumberFieldArchimedeanSiegelReduction.lean` composes determinant-one unit balancing with the
actual unipotent action reduction.  It proves one closed theorem yielding field-only constants
`R > 0` and `C ≥ 0` such that every positive archimedean cone point is carried through internally
chosen elements of `SL_n(𝓞 K)` to simultaneous real/complex Jacobi data with:

- every strict-upper real entry bounded in absolute value by `C`;
- every strict-upper complex entry bounded in norm by `C`;
- every Jacobi weight retaining the explicit `exp(±2nR)` multiplicative balance bounds.

The unipotent transport leaves Jacobi diagonals exactly unchanged, proved separately and consumed
by the capstone.  Source Jacobi data, units, determinant-one certificate, unipotent reducer,
special-linear actions, and target Jacobi data are all constructed inside the proof.  Direct check,
targeted leaf build, and axiom audit pass; both new declarations use only
`[propext, Classical.choice, Quot.sound]`.  Module is umbrella-wired without an umbrella build.

Card remains Stage 2.  The remaining geometric reduction obligations are the adjacent
diagonal-ratio/greedy bound and finite overlap.  Arithmetic obligations remain tame-kernel finite
generation and Moore reciprocity.

### Archimedean bounded-overlap finiteness engine (2026-08-30)

`NumberFieldIntegerFiniteness.lean` proves that algebraic integers with bounded mixed Minkowski
embedding form a finite set, extends this entrywise to matrices, and exposes separate real-place
and complex-place bounds.  Discreteness, properness, and injectivity all come from the actual
number-field integer lattice; no lattice or finiteness premise is retained.

`NumberFieldArchimedeanBoundedOverlap.lean` proves the analytic half for both local types.  A real
or Hermitian congruence carrying a form with coercivity constant `c > 0` to a form whose diagonal
is bounded by `C` has every congruence-matrix entry bounded by `sqrt (C / c)`.  Combining this at
all infinite places with mixed-lattice finiteness proves that all integral congruence matrices
admitting common archimedean coercivity/diagonal bounds form a finite set.

Both direct checks and targeted leaf builds pass.  Every new declaration audits to
`[propext, Classical.choice, Quot.sound]`; both modules are umbrella-wired without an umbrella
build.  Card remains Stage 2: the bounded-overlap implication is now complete, but the adjacent
diagonal-ratio/greedy reduction must still produce uniform coercivity and diagonal constants for
the actual reduced domain.  Tame-kernel finite generation and Moore reciprocity remain afterward.

### Hermitian Siegel infrastructure for tame-kernel finite generation (2026-08-30)

`ComplexSiegelSet.lean` and `ComplexSiegelQuasiDiagonal.lean` supply the complex-place counterpart
of the corpus's real Siegel interface:

- `ComplexJacobiData`, `exists_complexJacobiData` represent every positive-definite Hermitian form
  as `Uᴴ diag(d) U` with a positive real diagonal; diagonal reality is derived from complex-order
  positivity.
- `ComplexJacobiData.det_eq_one`, `inv_upper`, `IsSiegel`, `d_le_pow`, and `d_le_pow_n` derive the
  determinant, inverse-triangularity, and dimension-wide ordered diagonal comparison.
- `ComplexJacobiData.quadForm_eq` and `exists_complexSiegel_quasiDiagonal` give one uniform lower
  bound for every Hermitian Siegel quadratic form by its weighted diagonal form.  Compactness of
  the bounded complex unipotent ball constructs the inverse bound internally.
- `ComplexCongruenceDiagonal.lean` extracts the shared exact identity identifying a diagonal entry
  of `γᴴ A γ` with the quadratic form on a column of `γ`; the number-field overlap module now uses
  this smaller common dependency.
- `ComplexSiegelEntryBound.lean` proves the exact Hermitian Jacobi diagonal formula,
  `ComplexJacobiData.form_diag_le_siegel`, and `complex_siegel_entry_bound`, the complex counterpart
  of the real congruence-entry estimate used by leading-minor comparison.
- `ComplexSiegelWeightedIsometry.lean` strips the Jacobi factors from a Hermitian congruence and
  proves the exact diagonal weighted-isometry law plus its sharp single-entry consequence.
- `ComplexSiegelIsometryVanishing.lean` constructs the weighted conjugate-transpose inverse,
  proves it is the actual inverse, and establishes triangular vanishing across an ordered weight
  gap.  It also supplies the complex matrix-product entry norm bound needed to transport control
  back to the integral conjugator.
- `ComplexJacobiLeadingMinors.lean` proves leading blocks preserve Hermitian Jacobi form, computes
  full and leading determinants as the corresponding positive real diagonal products, and shows
  leading truncations inherit all complex Siegel bounds.

Both direct checks and targeted builds pass; every new declaration audits to
`[propext, Classical.choice, Quot.sound]`.  Modules are umbrella-wired without an umbrella build.
Card remains Stage 2: next geometric obligation is mixed real/complex leading-minor comparison and
greedy covering, followed by finite overlap, tame-kernel finite generation, and Moore reciprocity.
