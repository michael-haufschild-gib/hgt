# Real Kummer--Arakelov boundary

- **ID:** `deninger-real-kummer-arakelov-boundary`
- **Stage:** 3-formalized
- **Type:** SOURCE BOUNDARY THEOREM · LEAN 4 THEOREM
- **Labels:** `DAC_REAL_KUMMER_ARAKELOV_BOUNDARY`,
  `DAC_ARAKELOV_BOUNDARY_SHEAF`
- **Parent:** `deninger-derived-stratum-kummer-arithmetic-coefficient`
- **Statement:** the real logarithmic Kummer functional is a strict
  codimension-one boundary on the cofinite arithmetic base, and
  together with finite valuations its cokernel is the unique
  Arakelov orientation line.
- **Lean modules:**
  `GaloisForLFunctions.RHTower.DeningerRealKummerArakelovBoundary`
  (`DAC_REAL_KUMMER_ARAKELOV_BOUNDARY`),
  `GaloisForLFunctions.RHTower.DeningerSquareZeroKummerBoundary` (`(10)`--`(11)`),
  `GaloisForLFunctions.RHTower.DeningerArakelovBoundarySheaf`
  (`DAC_ARAKELOV_BOUNDARY_SHEAF`, `(1)`--`(2)`)

## Arakelov boundary sheaf

Let
\[
 S=\operatorname{Spec}\mathbb Z,\qquad
 \overline S=S\sqcup\{\infty\}
\]
with the usual Arakelov convention that every nonempty cofinite
arithmetic open \(U_N\subset S\) is enlarged to
\(\overline U_N=U_N\sqcup\{\infty\}\).

Define the real boundary sheaf on \(S\) by
\[
 \mathscr B_\infty^S(U_N)=\mathbb R(-1),\qquad
 \mathscr B_\infty^S(\varnothing)=0,                              \tag{1}
\]
with identity restrictions between nonempty opens.  Equivalently,
`(1)` is the direct image of the skyscraper
\(i_{\infty,*}\mathbb R(-1)\) from \(\overline S\).

`[PROVED HERE] [DAC_ARAKELOV_BOUNDARY_SHEAF]`

The prescription `(1)` is a flasque sheaf of complete real vector
spaces.  Hence
\[
 R\Gamma(S,\mathscr B_\infty^S)
 \simeq\mathbb R(-1)[0].                                         \tag{2}
\]

### Proof

Every restriction between nonempty opens is the identity and every
restriction to the empty open is surjective.  Thus all restrictions
are surjective, so `(1)` is flasque.  Flasque sheaves are acyclic,
which proves `(2)`.

## Real Kummer boundary

For \(a\in\mathbb Q^\times/\{\pm1\}\), define
\[
 \partial_\infty(a)
 =
 -\log|a|_\infty.                                                 \tag{3}
\]
If
\[
 a=\prod_p p^{n_p},
\]
then
\[
 \partial_\infty(a)
 =
 -\sum_p n_p\log p.                                               \tag{4}
\]
After tensoring with \(\mathbb R\), `(3)` is a linear map from the
real Kummer line to \(\mathbb R(-1)\).

`[PROVED HERE] [DAC_REAL_KUMMER_ARAKELOV_BOUNDARY]`

The finite and real Kummer boundaries assemble to
\[
 \partial_{\mathrm{Ar}}:
 (\mathbb Q^\times/\{\pm1\})\otimes\mathbb R
 \longrightarrow
 \left(\bigoplus_p\mathbb R[p]\right)
 \oplus\mathbb R_\infty,
                                                                    \tag{5}
\]
\[
 \partial_{\mathrm{Ar}}(a)
 =
 \left(
   (\operatorname{ord}_p a)_p,\,
   -\sum_p\operatorname{ord}_p(a)\log p
 \right).                                                        \tag{6}
\]
It is injective, its image is the kernel of
\[
 \operatorname{tr}_{\mathrm{Ar}}(d,x)
 =
 \sum_p d_p\log p+x,                                              \tag{7}
\]
and `(7)` is surjective.  Therefore
\[
 \operatorname{coker}\partial_{\mathrm{Ar}}
 \cong\mathbb R(-1).                                              \tag{8}
\]

The map `(3)` is continuous for the mixed Kummer norm because
\[
 |\partial_\infty(a)|
 \leq
 \sum_p\log p\,|\operatorname{ord}_p(a)|.                         \tag{9}
\]
It consequently extends uniquely to the strict \(L^1/L^2\)
completion.

### Proof

Unique factorization identifies
\[
 (\mathbb Q^\times/\{\pm1\})\otimes\mathbb R
 \cong\bigoplus_p\mathbb R[p]
\]
by the finite valuation map.  Formula `(4)` is the product formula.
It gives
\(\operatorname{tr}_{\mathrm{Ar}}\partial_{\mathrm{Ar}}=0\).
Conversely, if `(7)` vanishes on \((d,x)\), then
\[
 x=-\sum_p d_p\log p,
\]
so \((d,x)=\partial_{\mathrm{Ar}}(d)\) under the valuation
identification.  Finally \((0,r)\) maps to \(r\), proving
surjectivity.  Inequality `(9)` is the triangle inequality.

## Square-zero Milnor extension

Let \(K_{\mathbb R}^M(\mathbb Q)\) be the real Milnor algebra.  Rank
gives an augmentation
\[
 s_\infty:K_{\mathbb R}^M(\mathbb Q)\longrightarrow\mathbb R
\]
which is the identity in degree zero and zero in positive degrees.
There is a degree-minus-one \(s_\infty\)-derivation
\[
 \delta_\infty:
 K_{\mathbb R}^M(\mathbb Q)\longrightarrow\mathbb R(-1)[-1]       \tag{10}
\]
equal to `(3)` in Milnor degree one and zero in every other degree.
Equivalently,
\[
 s_\infty\oplus\delta_\infty:
 K_{\mathbb R}^M(\mathbb Q)
 \longrightarrow
 \mathbb R\oplus\mathbb R(-1)[-1]                                \tag{11}
\]
is a map of graded square-zero algebras.

Indeed, the augmentation kills every positive-degree factor.  The
graded Leibniz rule therefore forces the derivation to vanish on
products of two positive-degree classes, exactly as `(10)` does.
It is compatible with Steinberg relations because those lie in
degree two.  Thus the real logarithm is not an ad hoc additive
functional: it is the weight-one square-zero boundary of the
realified Milnor algebra.

By `DAC_UNIT_AMALGAMATION_RESIDUE_UNIVERSAL_DESCENT`, any analytic
Kummer-boundary lift agreeing with `(3)` extends through every
relative Tate--Milnor cell.
`DAC_ARCHIMEDEAN_KUMMER_HOMOLOGY_CURRENT` constructs such a lift as
the unique homology-current functional on every finite character
torus.  `DAC_PRO_STEIN_REAL_BETTI_DERIVED_LIFT` proves its
compatibility with lattice refinements, powers, Galois maps, field
norms, finite correspondences, and the mixed \(L^1/L^2\) completion.
Thus the real Betti boundary is complete on Deninger's prescribed
pro-Stein relevant coefficient \(R\alpha_{\mathrm{PS},*}\mathcal G\).
Comparison with ordinary hypercohomology of the raw nonproper coarse
invariant sheaf is optional and remains separate.

## Strict completed endpoint

Let \(D_{\mathrm{fin}}\) be the strict packet residue space.  Its Haar
splitting is
\[
 D_{\mathrm{fin}}
 =
 D_{\mathrm{val}}\widehat\oplus D_{\mathrm{pkt},0}.               \tag{12}
\]
The theorem above proves the trace-kernel identity on
\[
 D_{\mathrm{val}}\widehat\oplus\mathbb R_\infty.                  \tag{13}
\]
Local log-toric Poincaré residue is surjective onto each finite-stage
mean-zero packet space.  Therefore the full completed endpoint reduces
to one exact analytic assertion:
\[
 D_{\mathrm{pkt},0}
 \subset
 \operatorname{im}\partial_{\mathrm{fin}}
\quad\text{strictly after all-prime completion}.                  \tag{14}
\]
If `(14)` holds, `(8)` upgrades to the full boundary space.

## Boundary of the theorem

- The Kummer generator, real sheaf, continuity, product formula, and
  scalar endpoint are complete.
- The analytic real Betti lift on the pro-Stein relevant coefficient
  is complete; no ordinary coarse-sheaf equivalence is asserted.
- `DAC_STRICT_PRO_LOG_COLLAR_SECTION` proves strict completed
  surjectivity onto packet mean-zero modes in `(14)` using actual
  logarithmic collar forms, not scalar unique factorization.
- The real orientation does not provide Hodge positivity or the
  archimedean fixed-point exponent.

## Formalized statement

All declarations live in the `RHTower` namespace.  Real prime coordinates are `ℕ →₀ ℝ`, which is
`⨁_p ℝ` restricted to prime support.

**`DAC_REAL_KUMMER_ARAKELOV_BOUNDARY`, equations `(3)`--`(9)`, formalized in full.**

- `deningerFiniteTrace : (ℕ →₀ ℝ) →ₗ[ℝ] ℝ` is `d ↦ ∑_p d_p log p`, and
  `deningerArchBoundary` is its negative — equation `(3)`;
- `deningerArakelovBoundary : (ℕ →₀ ℝ) →ₗ[ℝ] (ℕ →₀ ℝ) × ℝ` is `(5)`--`(6)`, and
  `deningerArakelovTrace` is `(7)`;
- `deningerArakelovBoundary_injective` : `∂_Ar` is injective;
- `deningerArakelov_exact` : `range ∂_Ar = ker tr_Ar`;
- `deningerArakelovTrace_surjective` : `tr_Ar` is surjective;
- `deningerArakelovCokerEquiv` : `((ℕ →₀ ℝ) × ℝ) ⧸ range ∂_Ar ≃ₗ[ℝ] ℝ` — equation `(8)`, the
  Arakelov orientation line, obtained from the endpoint cokernel equivalence of
  `DAC_ARITHMETIC_ENDPOINT_RELATIVE_MIDDLE_REDUCTION`;
- `deningerArchBoundary_abs_le` : `|∂_∞ d| ≤ ∑_p log p |d_p|` — equation `(9)`.

**Equation `(4)`, the product formula, formalized in full.**  In
`GaloisForLFunctions/RHTower/DeningerRationalPrimeFactorization.lean`:

- `deningerRatExp_prod_eq` : a positive rational is the product of its prime powers;
- `deningerLog_eq_sum` : `log q = ∑_p ord_p(q) log p`.

And in this module, `deningerRatExpReal` is the real coordinate vector of a rational, with

- `deningerArchBoundary_ratExpReal` : `∂_∞(a) = -log a` for `a > 0`;
- `deningerFiniteTrace_ratExpReal` : `∑_p ord_p(a) log p = log a`;
- `deningerProductFormula` : the finite and archimedean residues of a positive rational cancel.

Sign-insensitivity, i.e. that all of this descends to `ℚ^× / {±1}`, is
`deningerRatExp_neg` / `deningerRatExp_abs`.

**Square-zero Milnor extension `(10)`--`(11)`, formalized.**  In
`GaloisForLFunctions/RHTower/DeningerSquareZeroKummerBoundary.lean`:

- `deningerAugmentation_leibniz` : for an augmented real algebra, a linear functional that kills
  the unit and every product of two elements of the augmentation ideal automatically satisfies
  the Leibniz rule `δ(xy) = s x · δ y + δ x · s y`.  This is exactly the card's argument: the
  augmentation kills every positive-degree factor, so a functional supported in Milnor degree one
  vanishes on `I·I ⊆ ⨁_{n≥2}` and the Leibniz rule is forced.  (The graded sign
  `(-1)^{|x|}` never appears, because whenever `δ x ≠ 0` one has `s x = 0` and conversely, so the
  graded and ungraded rules coincide term by term.)
- `deningerSquareZeroHom` : the pair `(s, δ)` is then an algebra map into the square-zero
  extension `TrivSqZeroExt ℝ ℝ = ℝ ⊕ ℝε` — this is `(11)`;
- `deningerSquareZeroHom_of_algHom`, `deningerSquareZeroHom_of_algHom_one` : the converse, so
  `(11)` and the derivation property are equivalent;
- `deningerKummerSquareZeroHom` : the instantiation.  `DeningerKummerSquareZero = ℝ ⊕ V` is the
  square-zero model of the real Milnor algebra in Kummer degrees, with `V` the real Kummer line;
  `deningerKummerRank` is the rank augmentation and `deningerKummerArchDelta` is `∂_∞`.  The two
  hypotheses hold unconditionally there, and `deningerKummerSquareZeroHom_ratExpReal` evaluates
  the resulting map on a positive rational as `-log q`.

### What is formalized and what is not

`DAC_REAL_KUMMER_ARAKELOV_BOUNDARY` and the square-zero extension `(10)`--`(11)` are formalized
unconditionally and in full.  The instantiation of `(11)` is on the square-zero model `ℝ ⊕ V` of
the Milnor algebra rather than on a formalized graded Milnor `K`-theory: mathlib has no Milnor
`K`-theory, and `DAC_TWO_TERM_CDGA_FORMALITY` is precisely the statement that the relevant
algebra is quasi-isomorphic to that square-zero model.

**The boundary sheaf `(1)`, formalized.**  In
`GaloisForLFunctions/RHTower/DeningerArakelovBoundarySheaf.lean`:

- `deningerArakelovBoundarySheaf` : the prescription `(1)` realized as the skyscraper sheaf at
  the generic point of `Spec ℤ` with value the real orientation line.  The card's own remark that
  `(1)` is a direct image of a skyscraper is what makes this legitimate, and the identification is
  exact rather than approximate because every nonempty open of `Spec ℤ` contains the generic
  point;
- `deningerArakelovBoundarySheaf_obj_of_nonempty` : every nonempty arithmetic open carries
  `ℝ(-1)`, proved from `deningerSpecZGeneric_mem_of_isOpen`;
- `deningerArakelovBoundarySheaf_obj_empty` : the empty open carries the terminal object;
- `deningerArakelovBoundarySheaf_sections` : `Γ(Spec ℤ, ℬ) = ℝ(-1)`;
- `deningerArakelovBoundarySheaf_isFlasque` : `ℬ` is flasque.

So everything in `DAC_ARAKELOV_BOUNDARY_SHEAF` except the single step "flasque, therefore
`RΓ ≃ Γ[0]`" is now unconditional in Lean.

`DAC_ARAKELOV_BOUNDARY_SHEAF` `(2)` is not.  Its arithmetic input is formalized —
`deningerSpecZGeneric_mem_of_isOpen` in
`GaloisForLFunctions.RHTower.DeningerSpecZCofiniteRecollement` proves that every nonempty open of
`Spec ℤ` contains the generic point, which is exactly why the prescription `(1)` is a sheaf and
why all its restrictions between nonempty opens are the identity, hence surjective, hence
flasque.  What is missing is `(2)`.

**Acyclicity `(2)`, formalized.**  The route taken is not the flasque one.  The orientation line
is divisible, hence an injective abelian group; the skyscraper functor is right adjoint to the
stalk functor, which is exact; so the boundary sheaf is an *injective object of the sheaf
category*, and its higher cohomology vanishes for that reason.

- `deningerArakelovBoundarySheaf_injective` : `ℬ` is injective, by
  `Adjunction.map_injective` applied to `stalkSkyscraperSheafAdjunction`;
- `deningerArakelovBoundarySheafSite` : the same sheaf named in mathlib's site form, since
  `TopCat.Sheaf` is a `def` and not an abbreviation, so instance search does not see through it;
- `deningerArakelovBoundarySheaf_higherCohomology` :
  `Subsingleton (Sheaf.H ℬ (n+1))` for every `n`.

Together with `deningerArakelovBoundarySheaf_sections` (`Γ = ℝ(-1)`) and `Sheaf.H.equiv₀` this is
`RΓ(S, ℬ) ≃ ℝ(-1)[0]`, equation `(2)`.

Two notes on how mathlib was used.  Sheaf cohomology is available for sheaves on a topological
space once `Mathlib.Topology.Sheaves.Abelian` and
`Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt` are imported: the former makes the
sheaf category Grothendieck abelian, the latter supplies `HasExt`.  And flasqueness, though
proved here (`deningerArakelovBoundarySheaf_isFlasque`), is *not* what the acyclicity argument
uses: mathlib has no "injective sheaf is flasque", and the injective-object route needs no such
lemma.

### Verification

- Direct commands: `lake env lean` on
  `GaloisForLFunctions/RHTower/DeningerRealKummerArakelovBoundary.lean`,
  `GaloisForLFunctions/RHTower/DeningerSquareZeroKummerBoundary.lean` and
  `GaloisForLFunctions/RHTower/DeningerArakelovBoundarySheaf.lean`
- Result: passed with no errors and no warnings.
- Scratch `#print axioms` on all declarations of the three modules and the two product-formula
  lemmas: only the Lean/mathlib standard `propext`, `Classical.choice`, and `Quot.sound`.
- No `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration.
- All imported by the `GaloisForLFunctions.RHTower` umbrella.

## Gates

- [x] real Kummer boundary, injectivity, exactness, trace surjectivity, cokernel `(3)`--`(9)`
- [x] Lean formalization of `DAC_REAL_KUMMER_ARAKELOV_BOUNDARY`
- [x] Lean formalization of the logarithmic product formula `(4)`
- [x] Lean formalization of the boundary sheaf `(1)`, its values and its flasqueness
  (`deningerArakelovBoundarySheaf`, `deningerArakelovBoundarySheaf_isFlasque`)
- [x] Lean formalization of `DAC_ARAKELOV_BOUNDARY_SHEAF` `(2)`
  (`deningerArakelovBoundarySheaf_injective`,
  `deningerArakelovBoundarySheaf_higherCohomology`)
- [x] Lean formalization of the square-zero Milnor extension `(10)`--`(11)`
  (`deningerAugmentation_leibniz`, `deningerKummerSquareZeroHom`)
- [ ] the strict completed endpoint `(14)`, an open analytic assertion

## References

- Daniel Allcock and Jeffrey D. Vaaler,
  *A Banach space determined by the Weil height*:
  https://arxiv.org/abs/0808.1038
- `DAC_ADELIC_PLACE_AVERAGE_RESIDUE`
- `DAC_REAL_ARAKELOV_DIVISOR_ENDPOINT`
- `DAC_UNIT_AMALGAMATION_RESIDUE_UNIVERSAL_DESCENT`
- `DAC_PRO_LOG_STEIN_KUMMER_RESIDUE_SQUARE`

**Verdict:** `FULLY PROVEN ON PAPER FOR THE REAL KUMMER BOUNDARY,
PRO-STEIN ANALYTIC REAL-BETTI LIFT, AND STRICT COMPLETED ARAKELOV
ENDPOINT; HODGE POSITIVITY IS SEPARATE`.

## Log

- 2026-08-01 — Formalized `DAC_REAL_KUMMER_ARAKELOV_BOUNDARY` and the logarithmic product
  formula unconditionally in Lean 4.  `DAC_ARAKELOV_BOUNDARY_SHEAF` needs flasque acyclicity,
  which mathlib does not have.
- 2026-08-01 — Formalized the square-zero Milnor extension `(10)`--`(11)` on the square-zero
  Kummer model, with the archimedean boundary as its weight-one derivation.
- 2026-08-01 — Located the blocker for `(2)` exactly: not flasque acyclicity (mathlib has both
  hard ingredients plus the `Ext` long exact sequences) but the absence of any
  `HasDerivedCategory`/`HasExt` instance for sheaf categories, without which `Sheaf.H` does not
  even elaborate on a topological space.
- 2026-08-01 — Formalized the boundary sheaf `(1)` as the skyscraper at the generic point of
  `Spec ℤ`, with its values on nonempty opens, its global sections, and its flasqueness.  Only
  the acyclicity step of `(2)` remains, and it is blocked on missing mathlib infrastructure.
- 2026-08-01 — Correction to the previous entry.  Sheaf cohomology is *not* unavailable: the
  earlier probe failed only because `Mathlib.Topology.Sheaves.Abelian` and
  `GrothendieckCategory.HasExt` were not imported.  With them, `Sheaf.H` elaborates and
  `EnoughInjectives` resolves for sheaves on a topological space.  The real remaining gap is the
  single lemma "an injective sheaf is flasque", which needs extension by zero.
- 2026-08-01 — Formalized `(2)`.  The flasque route is a dead end in mathlib (no "injective sheaf
  is flasque"); the injective-object route works instead, because the orientation line is
  divisible and the skyscraper functor is right adjoint to the exact stalk functor.  Both
  `[PROVED HERE]` theorems of this card are now unconditional in Lean 4.
