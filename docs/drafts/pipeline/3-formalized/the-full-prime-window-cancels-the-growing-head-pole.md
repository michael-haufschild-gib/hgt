# The full prime window cancels the growing-head pole

- **Stage:** 3-formalized
- **Type:** Unconditional theorem
- **Source:** `docs/reports/review-3010/obstacles-summary.md` Q1/A2.
- **Statement:** On the actual detail–far-window witnesses, the joint full prime
  source minus both mixed pole terms is `o(√Y)` as `Y→∞`.

## Paper mechanism

Fix positive integers `a,b`. Write `h_a` for the Haar detail, `q_b` for the
coarse logarithmic cell, and `k_ab(t)=∫h_a(u)q_b(u+t)du`. The full mixed prime
source is exactly
`C_Y=Σ_{m≤Y(b+1)}2Λ(m)m⁻¹ᐟ² k_ab(log m−log Y)`;
all later terms vanish by the support lemma.

With `r=b+1`, its trace is the existing head trace at horizon `rY`, evaluated
at `u+log r`. The proved head-window PNT and dominated convergence give
`C_Y/√Y → 4(√(2b+2)−√(2b)) ∫h_a(u)e^(−u/2)du`.
On the support of `h_a`, both minimum cutoffs in the head-window limit are
inactive. In the corpus convention `A(f)=∫f(u)e^(u/2)du` and
`B(f)=∫f(u)e^(−u/2)du`, the limit equals `2 B(h_a) A(q_b)` because
`A(q_b)=2(√(2b+2)−√(2b))`.

Translation by `log Y` gives the exact mixed pole
`2√Y B(h_a)A(q_b)+2Y⁻¹ᐟ² A(h_a)B(q_b)`. Thus the full tail cancels the
head's leading square-root coupling after the pole is included. For every
fixed finite collection of details and windows, the cancellation is uniform
over its bounded coefficient vectors by finite-dimensionality.

## Lean declarations

Module: `ArithmeticIndexDescent.TheFullPrimeWindowCancelsTheGrowingHeadPole`.

- `fullPrimeWindowCoupling_eq_tsum_euler`: exact literal all-prime source.
- `fullPrimeWindowCoupling_eq_head_add_tail`: exact head–tail decomposition.
- `tendsto_fullPrimeWindowCoupling`: dominated window-PNT limit.
- `fullPrimeWindowMixedPole_div_sqrt`: exact values of both polar moments.
- `tendsto_head_add_tail_sub_mixedPole_div_sqrt` and
  `tendsto_allPrimesMixedSource_sub_pole_div_sqrt`: zero normalized remainders.
- `fullPrimeWindowRemainder_uniform_finite_family`: uniform bounded-coefficient
  cancellation on every fixed finite family.

Direct `lake --old env lean` audit passed. All endpoint transitive axiom
closures contain only `propext`, `Classical.choice`, `Quot.sound`.
The module is imported by its umbrella.

This does not assert a bound uniform in growing detail or window indices.
