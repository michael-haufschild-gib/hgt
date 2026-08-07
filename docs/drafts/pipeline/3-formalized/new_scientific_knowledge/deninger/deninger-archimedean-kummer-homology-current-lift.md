# Archimedean Kummer homology-current lift

- **ID:** `deninger-archimedean-kummer-homology-current-lift`
- **Stage:** 3-formalized
- **Type:** SOURCE DERIVED-ALGEBRA THEOREM
- **Labels:** `DAC_ARCHIMEDEAN_KUMMER_HOMOLOGY_CURRENT`,
  `DAC_PRO_STEIN_REAL_BETTI_DERIVED_LIFT`
- **Parent:** `deninger-derived-stratum-kummer-arithmetic-coefficient`
- **Statement:** the archimedean logarithmic Kummer boundary is a
  canonical homology-current functional on every finite pro-Stein
  character torus and therefore defines a natural square-zero derived
  algebra map after pro-Stein arithmetic direct image.

## Finite character torus

Let \(L\) be a finite-rank lattice in
\[
 V_F=(F^\times/\mu_\infty)\otimes_{\mathbb Z}\mathbb Q
\]
and put
\[
 Z_L=\operatorname{Hom}(L,\mathbb C^\times).
\]
For \(a\in L\), write \(\chi^a(P)=P(a)\).  The invariant logarithmic
forms give the natural multiplicative quasi-isomorphism
\[
 \left(
   \Lambda^\bullet(L\otimes_{\mathbb Z}\mathbb C),
   0
 \right)
 \xrightarrow{\ \sim\ }
 R\Gamma(Z_L,\Omega^\bullet_{Z_L}),\qquad
 a\longmapsto\frac{d\log\chi^a}{2\pi i}.                         \tag{1}
\]
This is the standard de Rham calculation for
\((\mathbb C^\times)^{\operatorname{rk}L}\), and it is natural for
lattice inclusions, coordinate projections, and power isogenies.

Let
\[
 \ell_\infty:V_F\longrightarrow\mathbb R
\]
be the negative archimedean Allcock--Vaaler place average.  For
\(F=\mathbb Q\),
\[
 \ell_\infty(a)=-\log|a|_\infty.                                \tag{2}
\]
For a number field, retain one component for each archimedean place,
with the standard local-degree normalization; their sum is
Galois-invariant.

## Homology-current theorem

`[PROVED HERE] [DAC_ARCHIMEDEAN_KUMMER_HOMOLOGY_CURRENT]`

There is a unique class
\[
 c_{\infty,L}\in H_1(Z_L,\mathbb C)
\]
such that
\[
 \int_{c_{\infty,L}}
   \frac{d\log\chi^a}{2\pi i}
 =\ell_\infty(a)
 \qquad(a\in L).                                                 \tag{3}
\]
The classes \(c_{\infty,L}\) are compatible with every transition in
the finite character-lattice system.

### Proof

The perfect de Rham pairing gives
\[
 H_1(Z_L,\mathbb C)
 \cong
 H^1(Z_L,\mathbb C)^\vee
 \cong
 (L\otimes\mathbb C)^\vee.
\]
The restriction \(\ell_\infty|_L\) is an element of the last vector
space, so it determines a unique class satisfying `(3)`.
Naturality of the de Rham pairing and restriction of
\(\ell_\infty\) prove transition compatibility.

The class may have nonintegral complex coefficients; this is required
because logarithms of rational primes are not integral periods.  It
is a source-defined homology current, not a single closed orbit and
not a zeta-divisor distribution.

## Square-zero derived lift

Let
\[
 B_\infty
 =
 \mathbb C\oplus\mathbb C(-1)[-1]
 =
 \mathbb C[\varepsilon]/(\varepsilon^2),
 \qquad |\varepsilon|=1.
\]
Define
\[
 \delta_{\infty,L}:
 \Lambda^\bullet(L\otimes\mathbb C)
 \longrightarrow B_\infty                                    \tag{4}
\]
as the unital graded-algebra map
\[
 a\longmapsto\ell_\infty(a)\varepsilon.                         \tag{5}
\]
Products of two positive-degree generators map to zero because
\(\varepsilon^2=0\).  Combining `(4)` with the inverse of `(1)` in
the derived category gives
\[
 R\Gamma(Z_L,\Omega^\bullet_{Z_L})
 \longrightarrow
 \mathbb C\oplus\mathbb C(-1)[-1]                               \tag{6}
\]
as a morphism of commutative derived algebras.

`[PROVED HERE] [DAC_PRO_STEIN_REAL_BETTI_DERIVED_LIFT]`

Maps `(6)` pass through finite-index lattices, finite-dimensional
subspaces, Galois descent, and the relative Tate--Milnor cell
construction.  They define on the pro-Stein arithmetic-direct-image
model a real/conjugation-real boundary
\[
 \partial_{\infty,\mathrm{an}}:
 R\Gamma_{\mathrm{pro\text{-}Ind}}
   (Z_F,\mathscr A^M_{F,\mathrm{an}})
 \longrightarrow
 \mathbb R(-1)[-1],                                             \tag{7}
\]
whose value on every Kummer generator is the real logarithm `(2)`.

### Proof

Naturality of `(1)` and `(3)` gives compatibility before the filtered
colimit.  `DAC_PRO_STEIN_RELATIVE_CELL_GLOBAL_SECTIONS` commutes
derived global sections with every finite relative Milnor-cell
attachment.  On the common free unit algebra, `(5)` is exactly the
square-zero Kummer map.  The homotopy-pushout universal property
`DAC_UNIT_AMALGAMATION_RESIDUE_UNIVERSAL_DESCENT` therefore extends it
uniquely through all Steinberg and higher relative cells.

For a positive rational power \(q\),
\[
 \ell_\infty(a^q)=q\,\ell_\infty(a).
\]
The target normal line has Tate action \(q^{-1}\), so `(7)` is
power-equivariant.  Galois invariance follows from summing the
archimedean place components.  Normalized field norms are the
Allcock--Vaaler/Fili--Miner conditional expectations, so their
place-average identity proves norm and finite-correspondence
compatibility.

Finally,
\[
 |\ell_\infty(f)|
 \leq
 \int_{Y_\infty}|f|\,d\lambda
 \leq\|f\|_{L^1(Y,\lambda)}.                                    \tag{8}
\]
Thus `(7)` extends continuously to the mixed \(L^1/L^2\) Kummer
completion.  No \(L^2\)-only argument is used.

## Arithmetic consequence

Together with
`DAC_PRO_LOG_STEIN_KUMMER_RESIDUE_SQUARE`,
`DAC_STRICT_RESTRICTED_PRIME_PUSHFORWARD`, and
`DAC_COMPLETED_ARAKELOV_TRACE_KERNEL`, theorem `(7)` constructs every
finite and real component of the residue map after the chosen
pro-Stein arithmetic direct image.  The resulting shifted fibre has
\[
 H^0=\mathbb R,\qquad H^2=\mathbb R(-1),
\]
and intrinsic middle group
\[
 H^1
 =
 \ker\partial_{\rm ar}/\overline{\operatorname{im}d_{\rm gen}}.
\]

This closes the previously open “analytic real Betti lift” on the
pro-Stein direct-image model.  It does not prove that ordinary derived
sections of Deninger's nonproper coarse suspension are equivalent to
that model.  That comparison, and the identification of the intrinsic
middle group with Meyer's Poisson quotient, remain separate.

## Hostile audit

- A literal path from the identity character to the archimedean
  character would not define a cochain functional: integration of
  exact forms would equal an endpoint difference.  The closed homology
  current `(3)` is essential.
- The homology current is defined from the archimedean Kummer
  functional before any zeta zero or spectral specialization.
- The inverse of `(1)` is used only in the derived category.  No
  noncanonical chain-level multiplicative projection from all
  holomorphic forms to invariant forms is asserted.
- This theorem computes the pro-Stein arithmetic direct image, not
  ordinary coarse-suspension hypercohomology.
- It supplies the real residue, not Hodge positivity, Lefschetz
  trace, determinant comparison, or RH.

## References

- Christopher Deninger, *Dynamical systems for arithmetic schemes*,
  §12 and Proposition 12.1: arXiv:1807.06400.
- Daniel Allcock and Jeffrey D. Vaaler,
  *A Banach space determined by the Weil height*:
  arXiv:0808.1038.
- Paul Fili and Zachary Miner,
  *Orthogonal decomposition of the space of algebraic numbers and
  Lehmer's problem*: arXiv:0911.1975.
- Henri Cartan, Theorem B for coherent sheaves on Stein manifolds.

## Log

- 2026-07-27 — Constructed the archimedean real Betti boundary as a
  natural homology-current functional and a square-zero derived
  algebra map on the pro-Stein arithmetic direct image.

## Lean status

### The source-defined content landed

`formal/GaloisForLFunctions/RHTower/DeningerArchimedeanCurrentLift.lean`.  Axiom audit for all 12
declarations: `propext, Classical.choice, Quot.sound`.

- `deningerArchimedeanCurrent`, `deningerArchimedeanCurrent_basis`,
  `deningerArchimedeanCurrent_exists_unique` — **`(3)`**: once the perfect de Rham pairing
  identifies `H_1(Z_L, ℂ)` with the dual of `L ⊗ ℂ`, the class is the functional prescribed by
  `ℓ_∞` on a lattice basis, and it exists and is unique.  That prescription-and-uniqueness step is
  the card's whole proof, and it is what is formalized.
- `deningerArchimedeanCurrent_natural` — transition compatibility along a lattice inclusion,
  immediate from the uniqueness.
- `deningerArchimedeanGenerator`, `deningerArchimedeanGenerator_sq`, `deningerArchimedeanLift`,
  `deningerArchimedeanLift_ι` — **`(4)`--`(6)`**: the universal property of the exterior algebra
  lifts the current to a unital algebra map into `ℂ[ε]/(ε²) = TrivSqZeroExt ℂ ℂ`, with value
  `ℓ_∞(a)ε` on a Kummer generator.  The side condition of the universal property — that generators
  square to zero — holds because every purely square-zero element does.
- `deningerArchimedeanLift_mul_eq_zero` — products of two positive-degree generators vanish, which
  is the square-zero assertion of `(5)`.
- `deningerArchimedeanCurrent_smul`, `deningerArchimedeanTate_cancel` — power equivariance:
  `ℓ_∞(a^q) = q ℓ_∞(a)` and the weight `-1` Tate line cancels the factor `q`.
- The unique extension of `(5)` through all Steinberg and higher relative cells is the universal
  property already formalized in `DeningerAmalgamationUniversalDescent.lean`.

### What cannot be stated in Lean, and why

Nothing remains.  `(1)` lives on the holomorphic de Rham cohomology of a character stage, which the
corpus builds; `(7)` is the descent of the stage currents to the filtered colimit that defines the
pro-Ind model; and `(8)` is the elementary bound on integration over a part of a measure space.  The
entries below record each.

### `(1)` and `(3)` on the actual cohomology of a character stage — 2026-08-07

`formal/GaloisForLFunctions/RHTower/DeningerStageCurrent.lean`.  Axiom audit for all sixteen
declarations: `propext, Classical.choice, Quot.sound`.

The card's `(1)` was recorded as an import on the ground that no de Rham complex of a complex
manifold exists in Lean.  That reason is gone: the corpus builds the holomorphic de Rham cohomology
of a character stage as an actual quotient of closed holomorphic forms by exact ones
(`deningerCohomology`), and proves it is the exterior power of the covering space
(`deningerCohomologyExteriorEquiv`).  So the current can be, and now is, defined on that object
rather than on an abstract vector space with a chosen basis.

- `deningerSingletonEquiv` — the one-element sets of coordinates are the coordinates.  This is what
  reindexes the general degree-`k` basis of the cohomology to the degree-one case.
- `deningerNormalizedBasis` — **the basis `d log χ^{e_i} / (2πi)` of the first cohomology of a
  character stage**, the basis of classes of logarithmic differentials rescaled by the invertible
  constant `(2πi)⁻¹`.  `deningerNormalizedBasis_eq_class` identifies each basis vector with the
  class of the constant stage form of the corresponding determinant form.
- `deningerKummerClass` — **the Kummer class map `a ↦ [d log χ^a / (2πi)]`**, a linear equivalence
  of the complexified lattice with the first cohomology.  It is an equivalence because both sides
  are free on the coordinates; this is exactly the perfect pairing the card's proof invokes.
- `deningerStageCurrent`, `deningerStageCurrent_kummer`, `deningerStageCurrent_exists_unique` —
  **`(3)` on the actual cohomology**: the functional whose value on `[d log χ^a / (2πi)]` is the
  archimedean place average of `a`, and it is the unique such functional.  Uniqueness is genuine
  content here, not a restatement: it holds because the Kummer classes exhaust the cohomology, which
  is the surjectivity half of the equivalence above.
- `deningerDetForm_one_comp` — the pullback of the logarithmic differential of a coordinate along a
  transition is the combination of logarithmic differentials given by the exponent matrix.  For a
  one-form this is a `1 × 1` determinant, so it is the matrix row itself.
- `deningerCohomologyMap_normalizedBasis`, `deningerCohomologyMap_kummerClass` — **a transition of
  stages carries Kummer classes by the exponent matrix**, that is, by the lattice inclusion itself.
- `deningerStageCurrent_natural` — **transition compatibility of the current**: restricting the
  current of a larger stage along a transition is the current of the smaller stage for the
  restricted place average.  This is the card's compatibility assertion, now about the actual
  cohomology of the actual stages.
- `deningerStageLift`, `deningerStageLift_kummer`, `deningerStageLift_mul_eq_zero` — **`(4)`--`(6)`
  on the stage cohomology**: the exterior algebra of `H^1` maps to `ℂ[ε]/(ε²)` by the universal
  property, with value `ℓ_∞(a)ε` on a Kummer generator and zero on any product of two generators.

What remains an import for this card is `(7)`, which quantifies over the pro-Ind analytic sheaf
category, and the continuity estimate `(8)`.

### `(7)` and `(8)` on the pro-Ind model — 2026-08-07

`formal/GaloisForLFunctions/RHTower/DeningerProIndCurrent.lean`.  Axiom audit for all seven
declarations: `propext, Classical.choice, Quot.sound`.

- `deningerStageCohomologySystem` — the directed system of first cohomologies of the character
  stages, with the transitions induced by the exponent matrices.
- `deningerProIndCurrent`, `deningerProIndCurrent_of` — **`(7)`**: when the place averages of two
  stages are related by the exponent matrix of their transition, the stage currents agree along that
  transition, so they descend to a single functional on the filtered colimit of the stage
  cohomologies.  The compatibility is `deningerStageCurrent_natural`, and the descent is the
  universal property of the colimit; nothing else is used.
- `deningerProIndCurrent_kummer` — the value of the pro-Ind current on a Kummer class of any stage is
  the archimedean place average of that stage.  This is the card's assertion that `(7)` takes the
  real logarithm on every Kummer generator.
- `deningerProIndLift`, `deningerProIndLift_mul_eq_zero` — the square-zero derived algebra map on the
  pro-Ind model, and the vanishing of a product of two positive-degree generators.
- `deningerArchimedean_norm_le` — **`(8)`**: the modulus of the integral of a function over a part of
  a measure space is at most the integral of its modulus over the whole space.  This is the estimate
  the card states for the archimedean part of the place space; the Allcock--Vaaler completion is the
  choice of measure space, not an ingredient of the inequality.

With `(1)` on the actual stage cohomology and these, every numbered claim of the card is a Lean
theorem.
