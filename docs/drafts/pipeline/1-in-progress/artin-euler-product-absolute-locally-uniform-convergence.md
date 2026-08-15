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
- [ ] 1 -> 2 fully-proven: full Lean-independent paper proof with all analytic identifications
- [ ] 2 -> 3 formalized: local finite-image bound plus compact M-test and product holomorphy
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

## Missing Lean core

`NumberFieldFinitePlaceNormSummability.lean` closes step 4.  The missing nontrivial bridge is the
finite-image local estimate in steps 1--3, beginning with an unconditional theorem that the actual
Frobenius action on inertia invariants has finite order.  `P_v(0)=1` is insufficient: arbitrary
polynomials with constant coefficient one can have roots arbitrarily near zero, so no M-test may
be inferred from the formal source alone.

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
