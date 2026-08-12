# Kummer–Gamma one-sided corona flow and intervention rigidity law — Lean certificate

- **ID:** `cmr-kummer-gamma-one-sided-corona-flow-intervention-rigidity-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `kummer-gamma-one-sided-corona-flow-intervention-rigidity-law.md` (same directory).
- **Status:** `[UNCONDITIONAL]` `[NO SORRY / NO AXIOM / NO PROP INTERFACE]`

## Lean module

`formal/GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/KummerGammaCorona.lean`,
namespace `HTGeometry.ConstraintMotiveRelativity`, imported by `GaloisForLFunctions.HTGeometry`.

## Formal statement chain

### §1–§2 — the fixed corona and the diagonal classification

1. `CoefSpace`, **`coronaIdeal`**, `mem_coronaIdeal` — `(1)`: the raw prime coefficient space and
   the first-trace corona ideal `ℓ¹(P)` as a submodule.
2. `diagMulLin`, `diagMulLin_apply` — `(5)`: the diagonal multiplier.
3. `diagMulLin_mem_of_bounded`, `primeEnum`, `primeEnum_surjective`, `primeEnum_injective`,
   `exists_injective_large` and **`diagMulLin_mem_iff_bounded`** — Theorem 2.1 (1): a diagonal
   multiplier preserves the corona ideal **iff** it is bounded.  The sharpness direction builds the
   `(7a)` witness on an injective prime subsequence extracted with
   `Filter.extraction_forall_of_frequently`.
4. **`diagMul_ker_iff`** — Theorem 2.1 (2): the descended map is injective **iff** `(6)` holds, a
   cofinite lower bound.  The failing direction builds the `x ≡ 1` witness on a subsequence with
   `‖m_{q_n}‖ ≤ 2^{-n}`.
5. **`diagMul_sub_mem_of_eq_one`** — Theorem 2.1 (3): a multiplier equal to one off a finite set
   induces the identity.
6. **`diagMul_not_ker_of_small`** — Theorem 2.1 (4): a multiplier whose `ε`-large sets are all
   finite induces a noninjective map.

### §1 — the physical class

7. `dCoef`, `dCoef_pos`, `inv_four_mul_le_dCoef`, `gammaCoef`, `bockstein`, `bockstein_zero`,
   `norm_bockstein`, `bockstein_neg` — `(2)`, `(4)`.
8. `bockstein_not_mem_of_pos` and **`bockstein_mem_coronaIdeal_iff`** — `(3)`: the corona class of
   the Bockstein vanishes **iff** `t = 0`.  For `t > 0` the coefficient is bounded below by
   `(t log 2/4)·(1/p)`, using `p^t ≥ 1 + t log p` and `d_p ≥ 1/(4p)`, and the prime harmonic series
   diverges (`Nat.Primes.not_summable_one_div`); the negative range follows by `β_{-t} = -β_t`.

### §3 — the raw Kummer–Gamma flow

9. `gammaMul`, `norm_gammaMul`, **`gammaFlow_group`**, `gammaMul_zero` — `(8)`–`(9)`: the raw flow
   is a group on raw coefficient space.
10. **`hasDerivAt_gammaMul`** — `(10)`: its coordinatewise generator is `-2 log p`, twice the signed
    Kummer prime period.
11. `finite_primes_le`, **`gammaMul_bounded_iff`** — Theorem 3.1 (3): the flow descends to the fixed
    corona **iff** `t ≥ 0`.
12. **`gammaFlow_surjective`** and **`gammaFlow_not_injective`** — Theorem 3.1 (3): for `t ≥ 0` the
    descended map is surjective, and for `t > 0` it is not injective.
13. **`gammaFlow_holonomy`** — Theorem 3.1 (4), `(11)`: `G_t F_t - F_t = β_t`, so the finite
    holonomy of the raw flow on the Gamma coefficient family is the physical Bockstein.

### §4 — moving observers

14. `movingIdeal`, **`movingTransport`** — `(13)`–`(14)`: moving-ideal transport is a linear
    isomorphism of quotients.
15. `movingComp` and **`movingComp_trans`** — `(15)`–`(16)`: the transports between moving fibres
    compose.

### §5 — intervention rigidity

16. **`rigidity_scalar`**, **`rigidity_finite_change`**, **`rigidity_cofinite_lower`**,
    **`rigidity_moving`** — Corollary 5.1 (1)–(4): each of the four intervention classes preserves
    the zero/nonzero status of a corona class.
17. **`intervention_rigidity`** — the capstone: for every nonneutral grade the physical Bockstein
    class is nonzero and survives all four intervention classes.

## Verification

```
lake env lean GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/KummerGammaCorona.lean
lake build GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.KummerGammaCorona
```

Green.  `#print axioms` on `diagMulLin_mem_iff_bounded`, `diagMul_ker_iff`,
`diagMul_sub_mem_of_eq_one`, `diagMul_not_ker_of_small`, `bockstein_mem_coronaIdeal_iff`,
`gammaFlow_group`, `hasDerivAt_gammaMul`, `gammaMul_bounded_iff`, `gammaFlow_surjective`,
`gammaFlow_not_injective`, `gammaFlow_holonomy`, `movingComp_trans`, `rigidity_scalar`,
`rigidity_finite_change`, `rigidity_cofinite_lower`, `rigidity_moving` and
`intervention_rigidity` reports only `propext`, `Classical.choice`, `Quot.sound`.

## Scope notes

`(3)` is called "the established first-trace corona estimate" in the card; the module proves it
outright (`bockstein_mem_coronaIdeal_iff`) rather than importing it, so nothing in the certificate
is conditional.  The bound is stated for all real `t`, which is stronger than the card's `|t| < 1`.

`(3a)`, the specialization at a Xi zero by a nonzero source factor `c_ρ`, is the scalar case of
`rigidity_scalar` and needs no separate statement.

Descent of a diagonal multiplier to the quotient is recorded as the preservation statement
`∀ x ∈ I, M_m x ∈ I` and injectivity as `∀ x, M_m x ∈ I → x ∈ I`, which are literally the
conditions for `Submodule.mapQ` to exist and be injective; `movingTransport` shows the quotient
constructions themselves are available and used where the card needs an isomorphism.

§6's chain-level scope and §7's field consequence are programme statements about the Kummer
regulator and the coframe-extension anomaly, proved in the parent cards
(`valuation-coframe-operation-defect-rank-and-determinant-line-law`, already formalized) and not
re-derived here.
