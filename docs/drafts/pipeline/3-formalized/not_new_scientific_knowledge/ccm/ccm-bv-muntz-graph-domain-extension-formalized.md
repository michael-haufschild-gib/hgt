# BV Müntz graph-domain extension — formalized closure

- **ID:** `ccm-bv-muntz-graph-domain-extension-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./ccm-bv-muntz-graph-domain-extension.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`

## Lean module

- `GaloisForLFunctions.RHTower.CCMBVMuntzSummation`

Umbrella: `GaloisForLFunctions.RHTower`.

## Clause-by-clause audit

| card equation | Lean declaration | content |
|---|---|---|
| one-cell discrepancy | `abs_cell_discrepancy_le` | the right-endpoint Riemann value differs from the cell mean by at most the cell length times the variation on that cell (`eVariationOn`, `BoundedVariationOn.dist_le`) |
| partition additivity | `sum_variation_cells_le` | variations over a uniform partition add to at most the total variation (`eVariationOn.sum'`) |
| discrepancy, support-free form | `abs_sum_riemann_sub_integral_le` | `\|u ∑_{n ≤ N} f(nu) - ∫_0^{Nu} f\| ≤ u Var(f)`, with no hypothesis on support or integral, so the card's support and zero-integral hypotheses enter only once, at the end |
| truncation | `integral_trunc_eq_zero` | for a source supported in `(0,L]` with vanishing integral, the truncated integral past `L` still vanishes |
| `(7)` | `abs_sum_le_variation` | `\|∑_{n ≥ 1} f(nu)\| ≤ Var(f)`, uniformly in the sampling scale. This is the only place the bounded-variation hypothesis does work, and it is what makes the endpoint jump harmless |
| `(2)` | `summationVector`, `summationVector_eq_finset`, `summable_summand` | the summation vector as an unconditional `tsum`; at every scale only finitely many terms are nonzero, so no summability hypothesis is needed |
| `(3)`, support | `summationVector_eq_zero_of_lt`, `summationVector_eq_zero_of_nonpos` | `E(f)` vanishes past `L` and on the nonpositive half-line |
| `(3)`, pointwise | `abs_summationVector_le` | `\|E(f)(u)\| ≤ Var(f) √u` |
| measurability | `measurable_summationVector` | from finitely supported summand families, `tsum` is the pointwise limit of measurable partial sums |
| `(3)`, `L²(d*u)` | `integral_sq_summationVector_le`, `integral_Ioi_sq_summationVector_le` | `∫_0^∞ \|E(f)(u)\|² d*u ≤ Var(f)² L`; the multiplicative measure turns the pointwise bound into a constant, so no Minkowski inequality is used |
| unnormalized vector | `arithmeticSum`, `measurable_arithmeticSum`, `arithmeticSum_eq_zero_of_lt`, `abs_arithmeticSum_le` | `∑_{n ≥ 1} f(nu)` bounded by `Var(f)` and vanishing past `L` — exactly the hypotheses the Mellin differentiability criterion consumes |
| `(4)`, `(8)` | `integrableOn_rpow_mul_abs`, `mellinConvergent_source`, `integral_rpow_mul_abs_comp_mul`, `mellin_arithmeticSum_eq_zeta_mul` | the Müntz identity on `1 < Re s` (the card's `Im z > 1/2`); interchange by `hasSum_integral_of_summable_integral_norm`, substitution by `mellin_comp_mul_left`, dilation law for norm integrals from `integral_comp_mul_left_Ioi` |
| holomorphy | `locallyIntegrable_ofReal_of_bound`, `isBigO_atTop_of_support`, `isBigO_zero_of_bound`, `differentiableAt_mellin_of_bound_support` | both Mellin transforms are holomorphic on the whole right half-plane; a bounded compactly supported source is eventually zero, hence `O(t^{-a})` for every `a`, and `O(1)` at the origin |
| `(5)` | `eqOn_mellin_arithmeticSum_zeta` | the continuation, stated for an arbitrary open convex region of the right half-plane avoiding `s = 1` and meeting `Re s > 1` |
| `(6)` | `mellin_arithmeticSum_eq_zero_of_zeta_eq_zero` | the Mellin transform of the summation vector vanishes at every zeta zero of the open critical strip, including any hypothetical off-line zero |

The card removes an apparent pole at `z = i/2` using `Ψ_f(i/2) = 0`; the Lean route does not need
this, because the two quadrants `{Re s > 0, Im s > 0}` and `{Re s > 0, Im s < 0}` are convex, avoid
`s = 1`, and cover every strip zero — zeta has no real zero in `(0,1)`, by the corpus theorem
`RHTower.riemannZeta_ne_zero_of_ofReal_mem_Ioo`.

## Axioms

`#print axioms` on every theorem of the module returns exactly

```text
[propext, Classical.choice, Quot.sound]
```

## Verification performed

- `lake env lean` on a scratch file importing the module: no errors.
- `#print axioms` on every theorem: clean.
- Nothing the card proves is left unformalized; the card's remaining gates are its own open research
  items.
