# Smooth Vaughan remainder and its absolute budget

- **ID:** vaughan-smooth-remainder-and-absolute-budget
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ../1-in-progress/q-i-selective-square-root-band.md
- **Statement:** The small-small Vaughan piece has an exact floor/pole/remainder expansion; the rectangular sum of individual remainder norms retains the trivial square-root-band exponent.

## Dependency-closed proof

Fix `0<ε<1`, write `Z=ζ(1+ε)` and `c=Re ζ(1-ε)/(1-ε)`. The existing unsigned
divisor expansion and its dilated remainder give, for `m≥1`,

`Σ_(k≤n/m) (mk)^(-ε) floor(n/(mk))`
`= Z m^(-ε) floor(n/m) + 1_(m≤n)c n^(1-ε)/m + m^(-ε)1_(m≤n)R_(ε,m)(n)`.

The identity follows by factoring out `m^(-ε)`, using `floor(n/(mk))=floor(floor(n/m)/k)`,
and inserting the definition of `subHalfDilationRemainder`. It also holds when `m>n`,
because every term then vanishes. Pad the two finite Vaughan cutoffs to their full
rectangle: extra rows or columns have product greater than `n` and vanish. Multiply
the displayed identity by `μ(a)μ(b)` with `m=ab`, sum, and take the negative sign of
the small-small piece. This proves

`p_2(n) = -Z L_(U,V)(n) - c n^(1-ε)P_(U,V)(n) - R_(U,V)(n)`.

Here `L` retains the literal floor prefix, `P=Σ_(a≤U,b≤V,ab≤n)μ(a)μ(b)/(ab)`, and
`R` retains the literal signed double sum of dilated remainders. None is discarded.

The existing atom estimate is `‖1_(m≤n)R_(ε,m)(n)‖_T≤C_ε m^(-1/2)`. Two finite
triangle inequalities and multiplicativity of positive real powers therefore give

`‖R_(U,V)‖_T≤C_ε W_ε(U)W_ε(V)`,
`W_ε(U)=Σ_(a≤U)|μ(a)|a^(-ε-1/2)`.

For `0<ε<1/2`, put `q=1/2-ε>0`. Since `|μ(a)|≤1`, the existing subcritical power-sum
bound gives `W_ε(N)≤N^q/q+1≤(1+1/q)N^q` for `N≥1`.
For a lower bound, the existing squarefree quarter-density theorem gives
`W_0(N)≥N^(1/2)/4` for every `N≥1`. Since `a^(-ε)≥N^(-ε)` for `a≤N`,
it follows that `W_ε(N)≥N^q/4`. This strengthens the initial dyadic-density argument
to every positive cutoff, with an explicit constant.

Taking fourth powers bounds the squared rectangular absolute budget above and below
at exponent `4q=2-4ε`. If it had an eventual bound `C N^(4q-δ)` for any `δ>0`,
division by the positive lower power would imply `N^δ/256≤C`, contradicting
`N^δ→∞`. At the matching square-root horizon `T=N²`, this exponent is `1-2ε`.
The literal atomic constant is strictly positive: the remainder estimate at `n=1`
forces `floorSumRate(1-ε)≥0`, while `c<0` gives `|c|>0`. Thus multiplying by this
constant does not remove the budget obstruction. A saving by `T^δ` at `T=N²`
would be a saving by `N^(2δ)`, already excluded.

## Exact obstruction and positive survivor

- **Refuted estimate:** A fixed power saving in the absolute rectangular coefficient
  budget obtained by summing the known single-atom norms.
- **Positive survivor:** Exact signed floor/pole/remainder decomposition, uniform finite
  norm bound, and matching power bounds for its absolute coefficient budget.
- **New insight:** The individual unsigned remainder is already admitted. The cost lies
  in assembling the Möbius rectangle, where discarding signs restores precisely the
  trivial exponent. The exact identity also prevents a remainder-only estimate from
  being mistaken for control of the complete receiver.
- **Scope:** No lower bound for the signed remainder, no full-energy divergence, and no
  impossibility of selective cancellation. The full Q-I task remains open.

## Lean status

The norm and sharp budget statements are
`pronicNorm_pmVaughanSmoothRemainder_le`, `pmVaughanAtomicAbsoluteMass_lower`,
`pmVaughan_absolute_square_budget_lower`, `exists_pmVaughan_absolute_square_budget_upper`,
`not_pmVaughan_absolute_square_budget_power_saving`,
`exists_pmVaughanSmoothRemainder_square_energy_le`, and
`not_pmVaughanSmoothRemainder_square_horizon_power_saving`.

Lean: `TheAbsoluteVaughanRemainderBudgetHasTheTrivialExponent.lean`.
The identities, two-sided budget powers, and explicit no-power-saving corollary are written.
The first direct leaf check left two proof-script errors, now corrected. The subsequent
source audit passed for all ten public theorems; every transitive-axiom report lists only
`propext`, `Classical.choice`, and `Quot.sound`. Four subsequent corollaries (positive
atomic constant, literal remainder energy bound, full-budget obstruction, and explicit square-horizon obstruction) are
written and now passed the olean-producing leaf check, required by the moving-Gram draft.
All fourteen transitive-axiom reports passed, listing only `propext`, `Classical.choice`,
and `Quot.sound`.
The umbrella import is present. The final direct no-olean leaf check passed.
The unsigned expansion and atom estimates are existing corpus results, not new
analytic inputs or claimed novelties.

## Log

- 2026-10-25 — Recorded paper proof and exact scope before the first leaf check.
