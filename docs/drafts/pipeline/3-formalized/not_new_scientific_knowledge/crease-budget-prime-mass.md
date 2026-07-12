# The line budget carries the Mertens mass

- **ID:** `crease-budget-prime-mass`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scientific status:** `[SEARCH] [FORMALIZATION] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** The Lipschitz variation budget that transfers a square-dilated carrier
  floor from a certified line `re = σ₂` to the critical line must carry the prime
  reciprocal mass up to `√N`; consequently any line-crossing transfer datum forces the
  cutoff's Mertens mass under the explicit cap `2(1 + 1/(2σ₂-1))`.  Stated positively
  throughout: what the budget must contain, what the cutoff must satisfy.

## Exact relations

```text
sum_{p <= sqrt N} 1/p <= lineBudget σ₂ N + (1 + 1/(2σ₂-1))                        (1)
lineBudget σ₂ · -> ∞  with the cutoff                                             (2)
line floor at σ₂  ∧  budget condition to 1/2
    ==>  sum_{p <= sqrt N} 1/p < 2·(1 + 1/(2σ₂-1))                                (3)
sum_{k ∈ [1,M]} k^(-c) <= 1 + 1/(c-1)                 for c > 1, uniform in M     (4)
|dpoly2 sqrtMoebiusCoeff (Icc 1 N) z| <= 1 + 1/(2σ₂-1)   on re z >= σ₂ > 1/2      (5)
```

## Proof

`(1)` the budget's square-only support evaluates exactly at prime squares:
`|μ(p)|·|(p²)^(-1/2) − (p²)^(-σ₂)| = p⁻¹ − p^(-2σ₂)`; summing over the injection
`p ↦ p²` into `[1, N]` and controlling `∑ p^(-2σ₂)` by the partial zeta cap `(4)` leaves
the prime reciprocal sum.  `(2)` is `(1)` plus the divergence of `∑ 1/p` (mathlib's
`not_summable_one_div_on_primes`, converted to partial-sum form).  `(3)`: the line floor
`t₀` is capped by the uniform carrier sup bound `(5)` (finite dilation identity plus the
Möbius sup bound), so the budget condition `lineBudget ≤ t₀ − ε₁ < t₀` traps the prime
mass between `(1)` and twice the cap.  `(4)` splits off `k = 1` and applies the banked
integral-test partial bound; `(5)` reduces to the Möbius carrier at `2z` by the finite
dilation identity.

## Parent classification

`[SEARCH]` The ingredients — Möbius square support, Mertens divergence, triangle-
inequality sup bounds — are classical.  The assembled delimitation is lab-internal: it
quantifies which cutoffs the tree's own `dpoly2_chart_floor` budget technology can carry
to the critical line.  Not new scientific knowledge; the positive-constraint packaging
(forced prime mass, not a negation) is the shipped form.

## Reuse audit

- `SqrtCarrierCertificate.lean`: `dpoly2_sqrtMoebiusCoeff_eq_moebius_sqrt` (both the sup
  bound `(5)` and the term evaluation route), `sum_range_add_rpow_neg_le` (the cap `(4)`);
- `MFreeLadder.lean` / `Mollifier.lean`: `sqrtMoebiusCoeff`, `moebiusCoeff`,
  `abs_moebiusCoeff_le_one`;
- `SquarefreeMoebiusNormalization.lean`: `sqrtPart_apply_sq`;
- mathlib: `not_summable_one_div_on_primes`,
  `not_summable_iff_tendsto_nat_atTop_of_nonneg`, `Nat.primesBelow`,
  `Nat.pow_left_injective`, `Nat.le_sqrt`.

## Lean certificate

File: `formal/GaloisForLFunctions/RHTower/CreaseBudgetPrimeMass.lean`.

- `natCast_sq_rpow`, `sum_Icc_rpow_neg_le`: the real dilation and the partial zeta
  cap `(4)`;
- `norm_dpoly2_moebiusCoeff_le`, `norm_dpoly2_sqrtMoebius_le`: the uniform sup
  bounds `(5)`;
- `lineBudget`, `lineBudget_term_sq_prime`: the budget and its prime-square terms;
- `primeMass_le_lineBudget_add`: the forced Mertens content `(1)`;
- `tendsto_primeMass_atTop`, `tendsto_lineBudget_atTop`: the growth law `(2)`;
- `line_crossing_cutoff_primeMass_lt`: the forced constraint `(3)`.

The module is imported by `GaloisForLFunctions.RHTower` and `GaloisForLFunctions`.

## Gates

- [x] all statements positive (forced quantity + explicit bound), no negation shipped
- [x] unconditional; hypotheses are the transfer datum itself
- [x] carrier sup bound uniform in cutoff and height
- [x] targeted module build passes
- [x] generated indexes, axiom audit, and formal lint gate pass

The umbrella build reaches and accepts `CreaseBudgetPrimeMass`; the independent existing
failure is `SummableEulerCalkinInjectivity.lean`.  All eleven public declarations use
only `propext`, `Classical.choice`, and `Quot.sound`.

## Opens

The cap in `(3)` is `2(1 + 1/(2σ₂-1))`, minimized near `σ₂` large — with Mertens'
second theorem (`∑_{p≤x} 1/p ≈ log log x + M`) the constraint becomes an explicit
double-log bound `√N ≲ exp exp (2 + 2/(2σ₂-1))`: formalizing an effective Mertens lower
bound (`log log x − c ≤ ∑_{p≤x} 1/p`) would turn `(3)` into a closed-form cutoff bound
`N(σ₂)`.  Complementarily, `(1)` says the budget IS a Mertens-mass carrier: read
forward, a budget-shaped functional on square-supported coefficients measures prime
mass — a coefficient-level bridge between the carrier machinery and Mertens sums worth
its own object: which other tree functionals (second moments, detection diagonals)
carry forced prime-mass content under square support?
