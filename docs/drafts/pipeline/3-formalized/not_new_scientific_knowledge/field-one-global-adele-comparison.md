# Global rational adele comparison

- **ID:** `field-one-global-adele-comparison`
- **Stage:** 3-formalized
- **Type:** THEOREM / TYPE CORRECTION
- **Label:** `F1-GLOBAL-ADELE-1`
- **Parent:** `field-one-semilocal-product-l2-density`
- **Target:** identify exactly the adelic carrier underlying the completed
  archimedean--finite Schwartz--Bruhat tensor.

## Theorem

There are a ring equivalence and a homeomorphism, with the same underlying
function,
\[
  \operatorname{AdeleRing}(\mathbb Z,\mathbb Q)
    \cong \mathbb R\times\mathbb A_f.
\]
The equivalence preserves every principal rational adele. Transport of the
standard archimedean--finite additive character gives a nontrivial character
of the rational global adele ring that vanishes on the diagonal copy of
\(\mathbb Q\).

Thus the existing completed product-Haar carrier is global additive adelic.
It is not, by type alone, the finite-\(S\) trace space
\(L^2(\mathbb Z_S^\times\backslash\mathbb A_S)\).

## Proof

The rational field has one infinite place, and it is real. Evaluation at that
unique place followed by the real-completion isometry identifies
`NumberField.InfiniteAdeleRing ℚ` with `ℝ`. Product with mathlib's finite
adele ring gives both comparisons. Uniqueness of ring maps from `ℚ` proves
principal-adele compatibility. Existing rational primary reciprocity then
proves diagonal vanishing; finite-adele character nontriviality proves the
transported global character nontrivial.

## No-go closure

- **Exact killing mechanism:** the full restricted product
  \(\mathbb A_{\mathbb Q}\), the finite product \(\mathbb A_S\), and the
  quotient \(\mathbb Z_S^\times\backslash\mathbb A_S\) are different types.
  Additive-character multipliers are not multiplicative idele-class scaling.
- **Strongest positive survivor:** exact global topological-ring
  identification plus a nontrivial standard global additive character
  trivial on principal rationals.
- **New insight:** existing Hilbert completion supplies a global additive
  Poisson/reciprocity fiber. The child card
  `field-one-finite-stage-class-space` now supplies finite-\(S\) orbit
  quotients and continuous idele-class scaling. Invariant quotient measure,
  its `L²` representation, and restriction maps remain separate RP0 gates.
- **Status:** formalized unconditionally in
  `FieldOneGlobalAdeleComparison.lean`.

## Audit

- [x] Repo and mathlib searched before construction.
- [x] Direct cached
  `lake env lean GaloisForLFunctions/RHTower/FieldOneGlobalAdeleComparison.lean`
  passed.
- [x] `#print axioms` reports only `propext`, `Classical.choice`, and
  `Quot.sound`.
- [x] No computation, quotient-Hilbert identification, trace, Hodge,
  positivity, spectral, or RH premise.
