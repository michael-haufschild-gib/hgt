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
