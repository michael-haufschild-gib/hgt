# Two-term connected CDGA formality

- **ID:** `deninger-two-term-cdga-formality`
- **Stage:** 2-fully-proven
- **Type:** SOURCE ALGEBRA THEOREM
- **Label:** `DAC_TWO_TERM_CDGA_FORMALITY`
- **Parent:** `deninger-baumslag-free-rational-milnor-packet`

## Statement

Let \(k\) be a field and let \(A\) be a nonnegatively graded
graded-commutative DGA with
\[
 A^0=k,\qquad H^0(A)=k,\qquad H^1(A)=V,\qquad H^q(A)=0\ (q\ge2).      \tag{1}
\]
Then \(A\) is formal:
\[
 A\xrightarrow{\sim}k\oplus V[-1],\qquad V^2=0.                    \tag{2}
\]

Consequently every connected rational cochain model whose cohomology is
concentrated in degrees zero and one is quasi-isomorphic, after replacing
it by its connected model, to its square-zero cohomology algebra.

## Proof

Because \(A^0=k\), the differential and positive-degree boundaries out of
degree zero vanish.  Hence
\[
 H^1(A)=Z^1(A)\subset A^1.
\]
Choose a vector-space retraction
\[
 p:A^1\twoheadrightarrow Z^1(A)
\]
of the inclusion.  Define \(f:A\to k\oplus H^1(A)[-1]\) by:

1. \(f|_{A^0}=\operatorname{id}_k\);
2. \(f|_{A^1}=p\), followed by the identification
   \(Z^1(A)=H^1(A)\);
3. \(f|_{A^q}=0\) for \(q\ge2\).

This is a chain map.  The only possibly nonzero products in the target
involve degree zero, so it is also multiplicative: every product of two
positive-degree elements maps to zero on both sides.  It induces the
identity on \(H^0\) and \(H^1\), while both source and target have zero
cohomology above degree one.  Thus \(f\) is a quasi-isomorphism.

## Application

`DAC_BAUMSLAG_FREE_RATIONAL_MILNOR_PACKET` proves
\[
 H^\ast(BR_U;\mathbb Q)=\mathbb Q\oplus U[-1].
\]
Applying `(2)` to a connected CDGA model of \(BR_U\) identifies its
rational cochains with the same square-zero algebra modeled by the relative
Sullivan Milnor resolution.  This closes the isolated packet's CDGA
formality.  It does not prove the cochains of the fiberwise pullback over
\(BA_U\); that remains the twisted Eilenberg--Moore gate.

## Hostile audit

- The assumption \(A^0=k\) matters.  For raw polynomial forms, first pass
  to a connected CDGA model.
- The retraction \(p\) is noncanonical.  Naturality under Galois and power
  maps remains open.
- The theorem proves ordinary CDGA formality over a field, not integral or
  \(E_\infty\)-coherent formality.

**Verdict:** `FULLY PROVEN ON PAPER`.

## Lean status

### The theorem landed

`formal/GaloisForLFunctions/RHTower/Deninger/DeningerTwoTermFormality.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

The cochain algebra is modelled as a nonnegatively graded `k`-algebra `𝒜 : ℕ → Submodule k R` with
`[GradedAlgebra 𝒜]`, connectivity `𝒜 0 = k·1`, a `k`-linear degree-one differential `d`, and the
graded Leibniz rule.  The square-zero target `k ⊕ V[-1]` is mathlib's `TrivSqZeroExt k V`.

- `deningerComp`, `deningerComp_mul_zero`, `deningerComp_mul_one` — the graded components and the
  product formulas in degrees zero and one, from the antidiagonal expansion of a graded product.
- `deningerAugmentation` — **`A⁰ = k` gives a `k`-algebra augmentation**: the degree-zero component
  is a scalar, uniquely, so the projection is an algebra map `A → k`.  With
  `deningerAugmentation_gradeZero_surjective` and `deningerGradeZero_eq_zero` it is a bijection
  from `𝒜 0` onto `k`.
- `deningerDiff_one`, `deningerDiff_gradeZero` — **connectivity kills the differential in degree
  zero**: Leibniz gives `d1 = d1 + d1`, and every degree-zero element is a scalar multiple of `1`.
- `deningerCocycleZero_eq` — hence `H⁰(A) = A⁰ = k`.
- `deningerCocycleOne`, `deningerCoboundaryOne_eq_bot` — **`H¹(A) = Z¹(A)`**: there are no
  coboundaries in degree one.
- `deningerCocycleRetraction_exists` — the noncanonical retraction `p : A ↠ Z¹` exists, because a
  subspace of a vector space is a direct summand.
- `deningerFormalityMap` — **the comparison map** `f(x) = (ε x, φ⁻¹ p(x₁))` is a `k`-algebra map
  into `TrivSqZeroExt k V`, for any model `V ≅ H¹(A)`.  Multiplicativity is the degree-one product
  formula: the augmentation acts as the scalar, and every product of two positive-degree elements
  lands in degree at least two, where both sides vanish.
- `deningerFormalityMap_diff` — **it is a cochain map**: the target differential is zero and
  `f ∘ d = 0`, because the degree-zero part of a differential vanishes and everything else has
  degree at least two.
- `deningerFormalityMap_gradeZero`, `deningerFormalityMap_cocycleOne`,
  `deningerFormalityMap_gradeGe_two` — **it is a quasi-isomorphism**: the identity on `H⁰ = k`, the
  identity on `H¹ = Z¹`, and zero in degrees at least two, where the source cohomology vanishes by
  hypothesis `(1)` and the target has no classes at all.
- `deningerTwoTerm_formality` — **`(2)`**: the packaged existence statement.
- `deningerFormalityTarget_sq_zero` — `V² = 0` in the target.

### Remaining

Nothing.  The theorem is formalized unconditionally.  The card's own caveats stand unchanged: the
retraction is noncanonical, so no naturality is claimed, and this is ordinary CDGA formality over a
field, not integral or `E_∞`-coherent formality.
