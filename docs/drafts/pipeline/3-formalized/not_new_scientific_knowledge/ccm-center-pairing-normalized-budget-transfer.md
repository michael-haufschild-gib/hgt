# Vanishing normalized budget forces a negligible CCM center pairing

- **ID:** `ccm-center-pairing-normalized-budget-transfer`
- **Stage:** 3-formalized
- **Type:** THEOREM / ASYMPTOTIC BOOKKEEPING BRIDGE
- **Scientific status:** `[LEAN-PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Formal module:** `RHTower/CCMCenterPairingNormalizedBudgetTransfer.lean`
- **Parent:** `RHTower/CCMCriticalMellinFiniteApertureCenterPairing.lean`
- **Statement:** A center error bounded by a positive defect times a vanishing normalized resource
  budget is little-o of that defect. Applied to the clipped CCM estimate, this gives the correct
  variation thresholds `o(lambda/log lambda)` for an `o(d_lambda)` error and `o(lambda)` for an
  `o(d_lambda log lambda)` error.

## Exact theorem

Let `l` be a filter, let `d : alpha -> R`, `E : alpha -> C`, and `b : alpha -> R`, and let `C>=0`.
Assume eventually

```text
d(x)>0,  b(x)>=0,
||E(x)|| <= C*d(x)*b(x),                                      (1)
```

and assume `b(x)->0` along `l`. Then

```text
E(x)/d(x) -> 0.                                               (2)
```

For the finite-aperture CCM center estimate, put

```text
b_0(lambda)
 =(V_lambda+d_lambda)*(log(lambda)+1)/lambda.                  (3)
```

If `d_lambda>0` eventually and both

```text
V_lambda*(log(lambda)+1)/lambda ->0,
d_lambda*(log(lambda)+1)/lambda ->0,                           (4)
```

then `E_lambda/d_lambda->0`.

For comparison with the leading exterior law, put

```text
b_1(lambda)
 =(V_lambda+d_lambda)*(log(lambda)+1)/(lambda*log(lambda)).    (5)
```

If `lambda->infinity`, `V_lambda/lambda->0`, and `d_lambda/lambda->0`, then `(5)` tends to zero,
because `(log(lambda)+1)/log(lambda)->1`. Hence

```text
E_lambda/(d_lambda*log(lambda))->0.                            (6)
```

whenever `(1)` has the CCM factor `(log(lambda)+1)/lambda`.

## Complete proof

From `(1)` and eventual positivity of `d`,

```text
||E(x)/d(x)||
 =||E(x)||/d(x)
 <=C*b(x).                                                     (7)
```

The left side is nonnegative and the right side tends to zero, since multiplication by the fixed
constant `C` is continuous. The squeeze theorem gives `||E/d||->0`, which is equivalent to `(2)`
in the norm topology.

Expanding `(3)` gives

```text
b_0
 =V_lambda*(log(lambda)+1)/lambda
  +d_lambda*(log(lambda)+1)/lambda,                            (8)
```

so `(4)` and continuity of addition prove `b_0->0`; apply `(2)`.

For `(5)`, write

```text
b_1
 =(V_lambda/lambda+d_lambda/lambda)
   *((log(lambda)+1)/log(lambda)).                             (9)
```

The first factor tends to zero. Since `log(lambda)->infinity`, its reciprocal tends to zero, and
the second factor `1+1/log(lambda)` tends to one. The product therefore tends to zero. Dividing the
CCM estimate by `d_lambda*log(lambda)` gives the form `(1)` with budget `(5)`, so `(2)` proves `(6)`.

## Hostile audit

- The theorem is only a normalization/squeeze lemma; it does not estimate `V_lambda`.
- The two displayed rate conditions are sufficient consequences of the absolute pairing bound,
  not necessary thresholds if the signed pairing has further cancellation.
- The earlier route-card condition `V_lambda=o(lambda*log lambda)` was false for both advertised
  conclusions. Substitution into the bound gives an error as large as
  `d_lambda*(log lambda)^2`, so it cannot preserve a `d_lambda*log lambda` leading term.
- The positive survivor is the exact resource ledger `(8)`--`(9)`: every viable source estimate
  must pay the center channel through one of these normalized budgets.

## Formal theorem surface

The module proves, without project axioms:

```text
tendsto_div_defect_of_norm_le_defect_mul_vanishingBudget
tendsto_ccmCenterError_div_defect_of_normalizedBudget
tendsto_ccmCenterError_div_defect_mul_log_of_normalizedBudget
tendsto_ccmCenterError_div_defect_mul_log_of_sublinearVariation
```

The first theorem is the filter-generic transfer. The next two expose the defect and leading-scale
normalized budgets. The fourth derives the leading-scale conclusion from the concrete sublinear
ratios `V(lambda)/lambda -> 0` and `d(lambda)/lambda -> 0`.

The exact leaf module builds successfully. The axiom audit reports only Lean's standard logical
axioms `propext`, `Classical.choice`, and `Quot.sound` for all four theorems.

## Gates

- [x] exact rate error identified
- [x] false `o(lambda*log lambda)` condition removed from the route card
- [x] complete paper proof of the normalized transfer
- [x] exact Lean theorem and axiom audit

## Log

- 2026-07-18 — Found the logarithmic inversion error, replaced it by the exact normalized budget,
  and closed the paper proof.
- 2026-07-18 — Formalized the generic transfer and all three CCM specializations; the cached leaf
  build and exact axiom audit passed.
