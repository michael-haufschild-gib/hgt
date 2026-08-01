# Archimedean Kummer homology-current lift

- **ID:** `deninger-archimedean-kummer-homology-current-lift`
- **Stage:** 2-fully-proven
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

`(1)`, the de Rham computation identifying invariant logarithmic forms with `RΓ(Z_L, Ω^•)`, and the
pro-Stein direct image `(7)` are not formalizable here: mathlib has no de Rham complex of a complex
manifold, no Stein theory, no coherent-sheaf cohomology and no derived category in which `(6)` and
`(7)` would live.  The estimate `(8)` needs the Allcock--Vaaler space.  What the card contributes
beyond those imports — the existence, uniqueness and naturality of the current, the square-zero
algebra map and its power equivariance — is formalized above; the card therefore stays at stage 2
with its analytic scaffolding recorded as unavailable.
