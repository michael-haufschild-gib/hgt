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
