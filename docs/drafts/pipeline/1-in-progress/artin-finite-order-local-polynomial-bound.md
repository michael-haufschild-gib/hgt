# Uniform inverse bound for finite-order local Artin polynomials

- **ID:** `artin-finite-order-local-polynomial-bound`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Source:** standard finite-image Artin Euler-factor argument; Lean API audit 2026-08-15
- **Statement:** A finite-order complex linear action has reversed characteristic polynomial
  root-free on the open unit disk and an explicit uniform reciprocal estimate near zero.

## Goal

Build the genuine finite-image estimate needed by the Artin Euler product.  This is
`[LITERATURE] [BRIDGE] [NOT NEW]`, but it is not replaceable by a formal power-series inverse or
by `P(0)=1`: those facts contain no radius or norm control.

## Gates

- [x] 0 -> 1 in-progress: dependency-closed paper proof and source-checked primitive APIs
- [x] 1 -> 2 fully-proven: full generic polynomial proof, including factorization transport
- [ ] 2 -> 3 formalized: generic, Frobenius, and canonical finite-place leaves are
  kernel-checked, but the repository-wide formal lint gate remains blocked by unrelated existing
  violations
- [ ] 3 -> 4 publication-ready: standalone proof and Lean certificate

## Exact generic theorem

For a finite-dimensional complex vector space `W`, `A : End_C(W)`, and natural `n > 0` with
`A^n = 1`, write `m = finrank_C(W)` and `P_A(T)=charpoly(A).reverse`.  Prove:

```text
|z| < 1  ->  P_A(z) != 0,

|z| <= 1/2  ->
  |P_A(z)^(-1) - 1| <= 4^m |z|.
```

The Frobenius specialization uses `W = V^(I_v)`, `A = rho^I(Frob_v)`, and
`finrank(W) <= finrank(V)`, so the final constant depends only on the fixed representation and
not on the finite place.

## Paper proof

1. A root `mu` of `charpoly(A)` is an eigenvalue.  An eigenvector and `A^n=1` give `mu^n=1`, hence
   `|mu|=1`.
2. Since the characteristic polynomial splits over `C`, reverse its factorization to obtain

   ```text
   P_A(z) = product_(mu in roots(charpoly A)) (1 - mu*z).
   ```

   Thus every factor is nonzero for `|z|<1`, proving the first assertion.
3. For `r=|z| <= 1/(2(m+1))`, expand the product with
   `f_mu=-mu*z`.  The finite-product estimate gives
   `|P_A(z)-1| <= exp(mr)-1 <= 2mr`; the elementary lower estimate on its factors gives
   `|P_A(z)| >= (1-r)^m >= 2^(-m)`.  Divide to obtain the displayed reciprocal bound.
4. The actual local action has finite order because it is a representation of the finite
   decomposition stabilizer.  The already formalized theorem
   `frobeniusInertiaAction_pow_natCard_eq_one` supplies this exact input.

## Lean route

New generic leaf: `ArtinFiniteOrderLocalPolynomialBound.lean`, then a thin arithmetic
specialization leaf.  Source-checked primitive APIs:

```text
pow_card_eq_one'
Module.End.hasEigenvalue_iff_isRoot_charpoly
Module.End.HasEigenvalue.exists_hasEigenvector
Module.End.HasEigenvector.pow_apply
Complex.norm_eq_one_of_pow_eq_one
Polynomial.Splits.eq_prod_roots_of_monic
IsAlgClosed.splits
Polynomial.reverse_mul_of_domain
Finset.norm_prod_one_add_sub_one_le
Real.abs_exp_sub_one_le
Submodule.finrank_le
```

One small missing Mathlib convenience lemma is `reverse (X - C mu) = 1 - C mu * X`; it must be
proved locally by coefficient extensionality, then used in the finite factorization induction.
No analytic nonvanishing, Euler-product convergence, or Artin holomorphy is assumed.

## Anti-theatre boundary

Do not replace this theorem with an existential continuity bound that assumes the local factors
are nonzero, or with a finite enumeration whose radius is unspecified.  The root-of-unity proof
is needed to certify the full unit-disk root-free statement and an explicit uniform bound.

## Log

- 2026-08-15 -- opened after two independent source audits.  Generic finite-order action and
  root-norm-one lemmas source-check; factorization/reverse and quantitative product estimates
  remain to formalize.
- 2026-08-15 -- formalized `toInvariants_pow_natCard_eq_one` and its actual arithmetic
  specialization `frobeniusInertiaAction_pow_natCard_eq_one` in
  `ArtinLocalEulerFactor.lean`, then formalized
  `finiteOrder_charpoly_root_norm_one` in
  `ArtinFiniteOrderLocalPolynomialBound.lean`.  Both leaves source-check and target-build; the
  axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.  Root factorization and
  the quantitative inverse estimate remain open.
- 2026-08-15 -- completed the qualitative half of the generic theorem: the new module proves the
  reversed split-characteristic-polynomial factorization, then
  `finiteOrder_charpoly_reverse_eval_ne_zero`, and specializes it to the actual
  `frobeniusInertiaEulerPolynomial`.  Both `ArtinLocalEulerFactor` and the new leaf source-check
  and target-build; an eight-theorem axiom audit is standard-foundations-only.  The explicit
  reciprocal bound is still open and is not inferred from nonvanishing.
- 2026-08-15 -- transported the result to canonical number-field finite places in
  `ArtinNumberFieldFinitePlaceNonvanishing.lean`: at every genuine Euler argument
  `N(v)^(-s)` with `Re(s)>0`, the finite-place denominator is nonzero.  The leaf source-checks,
  target-builds, and has only standard foundations in its axiom audit.  This is individual local
  nonvanishing, not an infinite product estimate.
- 2026-08-15 -- formalized the quantitative intermediate estimate
  `finiteOrder_charpoly_reverse_eval_norm_inv_le`: for `|z|<1`, the reciprocal norm is bounded
  by `(1-|z|)^(-finrank W)`.  The proof is a nonnegative multiset product induction over the
  roots, not a continuity assumption.  The leaf source-checks and target-builds; its axiom audit
  reports only `propext`, `Classical.choice`, and `Quot.sound`.  This still does not bound
  `|P_A(z)^(-1)-1|` linearly, so the compact M-test bridge remains open.
- 2026-08-15 -- completed the generic linear difference estimate
  `finiteOrder_charpoly_reverse_eval_inv_sub_one_norm_le` by a direct root-multiset induction:
  on `|z| ≤ 1/2`, `|P_A(z)^(-1)-1| ≤ 4^dim(W)|z|`.  It is transported first to genuine
  Frobenius--inertia factors and then to canonical number-field finite places, where for
  `1 ≤ Re(s)` it gives the uniform majorant
  `4^dim(V) N(v)^(-Re(s))`.  `ArtinFiniteOrderLocalPolynomialBound` and
  `ArtinNumberFieldFinitePlaceNonvanishing` source-check and target-build; the ten-theorem
  axiom audit is standard-foundations-only.  The remaining task is the compact M-test and not a
  local-factor estimate.
