# Finite-prime Milnor endpoint page

- **ID:** `deninger-finite-prime-milnor-endpoint-page`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Label:** `DAC_FINITE_PRIME_MILNOR_ENDPOINT_PAGE`
- **Parent:** `deninger-cofinite-divisor-split-strictness`
- **Statement:** after the chartwise Steinberg correction, every
  finite-prime residue page already has the required arithmetic
  endpoint cohomology.

## Setup

Let \(S\) be a finite set of primes and put
\[
 U_S
 =
 \bigl(\mathbb Z[S^{-1}]^\times/\{\pm1\}\bigr)
 \otimes_{\mathbb Z}\mathbb R.                                    \tag{1}
\]
The valuation map is
\[
 \operatorname{ord}_S:
 U_S\longrightarrow\mathbb R^S,\qquad
 a\longmapsto(\operatorname{ord}_p(a))_{p\in S}.                   \tag{2}
\]
Let \(O\) be a one-dimensional real orientation line.  Define
\[
 L_S^0=\mathbb R,\qquad
 L_S^1=U_S,\qquad
 L_S^2=\mathbb R^S\oplus O,                                       \tag{3}
\]
with
\[
 d^0=0,\qquad
 d^1(u)=(\operatorname{ord}_S(u),0).                               \tag{4}
\]

## Theorem

`[PROVED HERE] [DAC_FINITE_PRIME_MILNOR_ENDPOINT_PAGE]`

The map `(2)` is a linear isomorphism and
\[
 H^q(L_S^\bullet)
 =
 \begin{cases}
   \mathbb R,&q=0,\\
   0,&q=1,\\
   O,&q=2,\\
   0,&q\notin\{0,1,2\}.
 \end{cases}                                                       \tag{5}
\]
The degree-two isomorphism is induced by projection
\(\mathbb R^S\oplus O\to O\).  It is natural under inclusions
\(S\subset S'\).

## Proof

Every positive \(S\)-unit has a unique expression
\[
 \prod_{p\in S}p^{n_p},\qquad n_p\in\mathbb Z.                     \tag{6}
\]
Thus
\[
 \mathbb Z[S^{-1}]^\times/\{\pm1\}
 \cong\bigoplus_{p\in S}\mathbb Z[p],
\]
and `(2)` sends the basis vector \([p]\) to the \(p\)-th standard basis
vector.  Tensoring with \(\mathbb R\) proves that `(2)` is an
isomorphism.

Since \(d^0=0\), degree-zero cohomology is \(\mathbb R\).  Injectivity
of `(2)` gives \(\ker d^1=0\), so \(H^1=0\).  Finally,
\[
 \operatorname{im}d^1=\mathbb R^S\oplus0,
\]
hence projection onto the second factor induces
\[
 H^2
 =
 (\mathbb R^S\oplus O)/(\mathbb R^S\oplus0)
 \xrightarrow{\sim}O.
\]
The unique factorization coordinates commute with extension by zero
when \(S\subset S'\), proving naturality.

## Role in source arithmetic localization

`DAC_CHARACTER_SHAPE_FORMALITY` and
`DAC_ALGEBRAIC_CYCLOTOMIC_MILNOR_AMPLITUDE` identify the
Steinberg-corrected chart algebra with a degree-zero unit and a
degree-one unit space.  The present theorem computes what finite
Rost--Schmid residue localization does to that page.

It is the finite omitted-prime endpoint after the source
coarse-analytic divisor comparison.  It is not the cofinite-open
divisor resolution itself: for
\(\operatorname{Spec}\mathbb Z[S^{-1}]\), residue coordinates occur at
primes outside \(S\).  That corrected inside/outside sequence and its
strict mixed completion are
`DAC_COFINITE_DIVISOR_SPLIT_STRICTNESS`.

No bar construction, derived rational-power invariant, or quotient
cohomology is part of this theorem's dependency role.

## Hostile audit

- The theorem computes a finite boundary page, not the comparison from
  Deninger's coarse invariant sheaf.
- It does not justify passage to infinitely many primes or a completed
  restricted product.
- It does not show closed range after nuclear or mixed-topology
  completion.
- The orientation line is adjoined by the real signature boundary; it
  is not produced by finite valuations alone.
- No \(\xi\)-zero, RH premise, CCM model, or numerical computation is
  used.

## Novelty status

The calculation is unique factorization plus elementary homological
algebra and is not new.  Its role is to fix the exact finite target of
the derived quotient contraction.

**Verdict:** `FULLY PROVEN ON PAPER; FORMALIZED AND CHECKED IN LEAN,
INCLUDING THE ARITHMETIC INPUT (2)`.

## References

- `DAC_ALGEBRAIC_CYCLOTOMIC_MILNOR_AMPLITUDE`
- `DAC_REAL_ARAKELOV_DIVISOR_ENDPOINT`
- Christopher Deninger, *Dynamical systems for arithmetic schemes*:
  https://arxiv.org/abs/1807.06400

## Lean status

### The whole page landed, including the arithmetic input

Two modules:

- `formal/GaloisForLFunctions/RHTower/Deninger/DeningerArithmeticFiniteResidueEndpoint.lean` (already in the
  tree) — the homological half: given *any* residue coordinate isomorphism, the three-term complex
  `(3)`--`(4)` has `H⁰ = R`, `H¹ = 0`, `H² = O` by projection.
- `formal/GaloisForLFunctions/RHTower/Deninger/DeningerSUnitEndpointPage.lean` (new) — the arithmetic half,
  i.e. that `(2)` *is* such an isomorphism, plus the naturality claim.

Axiom audit for all 24 new declarations: `propext, Classical.choice, Quot.sound`.

- `deningerSUnits` — `(1)`: the group of positive `S`-units, realized inside `ℚˣ` as the positive
  units whose `p`-adic valuation vanishes at every prime outside `S`.  Working with the positive
  part is exactly the quotient by `{±1}`.
- `deningerSOrd` — `(2)`: the valuation coordinates.
- `deningerSUnitProduct`, `deningerSUnitProduct_val`, `deningerSUnitProduct_mem` — the map
  `n ↦ ∏_{p ∈ S} p^{n_p}` of `(6)`, its valuations (its exponent inside `S`, zero outside), and the
  fact that it lands in the `S`-units.
- `deningerSOrd_product` — **unique factorization, surjectivity half**: the coordinates of a
  prescribed product are its exponents.
- `deningerRat_eq_one_of_valuations` — **the injectivity half, proved from scratch**: a positive
  rational all of whose `p`-adic valuations vanish is `1`.  Numerator and denominator are coprime,
  so a prime dividing either would force a nonzero valuation; hence both are `1`.  mathlib has no
  such statement, and no "the positive rationals are free abelian on the primes".
- `deningerSUnits_eq_of_ord_eq` — `S`-units are determined by their coordinates.
- `deningerSUnitsEquiv` — **`(2)` is an isomorphism onto `⨁_{p ∈ S} ℤ`**, the additive form of
  `ℤ[S^{-1}]^×/{±1} ≅ ⨁_{p∈S} ℤ[p]`.
- `deningerSResidueEquiv` — the linear isomorphism `ℝ ⊗ U_S ≅ ℝ^S` obtained by extension of
  scalars, which is the residue coordinate map required by the endpoint page.
- `deningerSEndpointComplex`, `deningerSEndpoint_H0`, `deningerSEndpoint_H1`,
  `deningerSEndpoint_H2` — **`(5)`** for the actual arithmetic page: `H⁰ ≅ ℝ`, `H¹ = 0`,
  `H² ≅ O` induced by the projection `ℝ^S ⊕ O → O`, for an arbitrary orientation line `O`.
- `deningerSUnits_mono`, `deningerSOrd_extension`, `deningerSUnitProduct_extension` — **naturality
  under `S ⊆ S'`**: `S`-units are `S'`-units, on them the larger coordinate system is the extension
  by zero of the smaller one, and the prescribed products agree accordingly.

### Remaining

Nothing for this page.  The four boundary items of the hostile audit — the comparison from
Deninger's coarse invariant sheaf, passage to infinitely many primes, closed range after nuclear or
mixed-topology completion, and the provenance of the orientation line — are outside this theorem;
the corrected inside/outside sequence is `DAC_COFINITE_DIVISOR_SPLIT_STRICTNESS`.
