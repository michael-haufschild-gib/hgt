# Finite-image Artin Euler product in the absolute-convergence half-plane

- **ID:** `artin-euler-product-absolute-locally-uniform-convergence`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Source:** classical Artin Euler-product construction; formal dependency audit 2026-08-15
- **Statement:** For a finite Galois extension of number fields and a finite-dimensional complex
  representation of its finite Galois group, the canonical finite-place reciprocal Artin factors
  form a locally uniformly multipliable family on `Re(s) > 1`; its product is holomorphic there.

## Goal

Formalize the actual source-side Euler product before any continuation or Heilbronn-order claim.
This is `[LITERATURE] [BRIDGE] [NOT NEW]`: it establishes only the absolute-convergence chamber,
where Artin local factors are already known to be holomorphic and nonzero.  It does **not** cross
`Re(s)=1`, produce meromorphic continuation, or constrain a continued divisor.

## Gates

- [x] 0 -> 1 in-progress: exact source, non-circular paper proof, and missing Lean core isolated
- [x] 1 -> 2 fully-proven: dependency-closed paper proof of the stated analytic tprod theorem
- [ ] 2 -> 3 formalized: all target leaves are kernel-checked, but the repository-wide formal
  lint gate remains blocked by unrelated existing violations
- [ ] 3 -> 4 publication-ready: standalone theorem/proof/Lean certificate

## Exact statement

Let `v` run over `HeightOneSpectrum (𝓞 K)`, let `q_v = absNorm(v.asIdeal)`, and let

```text
P_v(T) = det(1 - T rho(Frob_v) | V^(I_v)).
E_v(s) = P_v(q_v^(-s))^(-1).
H = {s : C | 1 < Re(s)}.
```

Then `(E_v)_v` is multipliable locally uniformly on `H`; its product is holomorphic and nonzero
on `H`.  A later theorem must separately identify this analytic product with the formal source
`artinFormalEulerSource`; coefficientwise stabilization alone does not supply that identification.

## Paper proof

1. For every finite decomposition group `D`, normal inertia `I`, and Frobenius `phi`, the induced
   action `A = rho^I(phi)` has finite order: `A^(|D|)=1`.
2. Every characteristic-polynomial root `lambda` of `A` is an eigenvalue, hence
   `lambda^(|D|)=1` and `|lambda|=1`.  Therefore
   `P_v(z)=product_lambda (1-lambda*z)` has no zero for `|z|<1`.
3. The degree is at most `d = dim_C(V)`.  For a fixed small radius, e.g.
   `|z| <= 1 / (2*(d+1))`, the product estimate gives a constant `C_d` independent of `v` with

   ```text
   |P_v(z)^(-1) - 1| <= C_d |z|.
   ```

   This can also be derived from the finite set of `(D,I,phi)` possibilities inside fixed finite
   `G`; neither argument uses continuation.
4. For compact `C ⊆ H`, compactness gives `sigma_C>1` with
   `sigma_C <= Re(s)` on `C`.  Thus `|q_v^(-s)| <= q_v^(-sigma_C)`, and
   `numberField_summable_finitePlace_absNorm_rpow sigma_C` supplies a summable majorant.
5. The compact M-test gives local uniform multipliability of `1 + (E_v-1)`.  The standard product
   theorem makes the product holomorphic and nonzero on `H`.

## Remaining Lean core

The finite-image local estimate, compact M-test, factor differentiability, tprod holomorphy, and
tprod nonvanishing are now formalized in the dedicated analytic leaf.  The remaining source-side
problem is not convergence: it is a non-circular equality between this analytic tprod and
`artinFormalEulerSource`/a standard Artin `LSeries`.  Coefficientwise finite-prefix stabilization
does not prove that equality.

**Progress (2026-08-15).** The qualitative finite-image part is now formalized: actual local
polynomials have no zero at every `|z| < 1`.  This is enough to certify individual local factors
in the absolute-convergence regime after the norm argument is transported to finite places.  It
does not give a summable bound for `|E_v(s)-1|`; the explicit inverse estimate remains mandatory
before the compact M-test may be invoked.

That transport is now also formalized: for every finite place and every `Re(s)>0`, the canonical
denominator at `N(v)^(-s)` is nonzero.  This still supplies no majorant for the difference from
one and therefore does not authorize the product theorem.

**Further progress (2026-08-15).** The generic finite-order leaf now also bounds
`|P_A(z)^(-1)|` by `(1-|z|)^(-dim W)` throughout the unit disk.  This is a necessary quantitative
ingredient, but it is not the required summable difference bound: a separate product-deviation
estimate for `|P_A(z)-1|`, and then a linear estimate for `|P_A(z)^(-1)-1|` on a fixed small disk,
remain mandatory.

**Further progress (2026-08-15).** The required local linear bound is now formalized at every
canonical finite place: for `1 ≤ Re(s)`,
`|E_v(s)-1| ≤ 4^dim(V) N(v)^(-Re(s))`.  This is precisely the summable shape needed after taking
a compact minimum `sigma>1`; the local theorem itself still does not instantiate the M-test or
identify an analytic tprod with the formal source.

Mathlib APIs audited for the route include `pow_card_eq_one'`, the characteristic-polynomial
eigenvalue bridge, `Complex.norm_eq_one_of_pow_eq_one`,
`Summable.multipliableUniformlyOn_one_add`, and
`hasProdLocallyUniformlyOn_of_forall_compact`.  The exact analytic product/formal-source equality
is a later leaf; current arithmetic-function Euler-product APIs are coefficientwise.

## Anti-theatre boundary

This card is closed only when it uses the canonical local factors from
`ArtinNumberFieldLocalEulerFactor.lean`, the actual finite-prime norm theorem, and no assumed
`Multipliable`, nonvanishing, or analytic-continuation interface.  A generic product theorem with
those properties as hypotheses does not advance this card.

## Log

- 2026-08-15 -- opened after formal source stabilization and unconditional finite-prime norm
  summability were target-built.  Finite-image local-factor control isolated as exact next gap.
- 2026-08-15 -- completed and target-built the concrete compact M-test in
  `ArtinNumberFieldEulerProductAnalytic.lean`.  It defines canonical reciprocal factors and their
  tprod, then proves `HasProdLocallyUniformlyOn` on `Re(s)>1` from the actual local bound and
  `numberField_summable_finitePlace_absNorm_rpow`.  The axiom audit is standard-foundations-only.
  Factor differentiability and the resulting holomorphy are still separate obligations; no
  formal-source or `LSeries` identification has been claimed.
- 2026-08-15 -- completed those analytic obligations in the same leaf: each actual reciprocal
  factor is differentiable on `Re(s)>0`; locally uniform convergence of finite products gives
  `DifferentiableOn` for the canonical tprod on `Re(s)>1`; and the summable one-plus-product
  theorem proves that tprod nonzero there.  The revised leaf source-checks and target-builds, and
  its five-theorem axiom audit is standard-foundations-only.  The module is wired into
  `RHTower.lean`, but no umbrella build was run.  The remaining source-side gap is equality of
  this analytic product with `artinFormalEulerSource`/an `LSeries`, not half-plane holomorphy of
  the tprod itself.
