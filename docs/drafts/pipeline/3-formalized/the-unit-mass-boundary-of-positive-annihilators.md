# The unit-mass boundary of positive annihilators

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Lean:** `ArithmeticPositiveDuality/TheUnitMassBoundaryOfPositiveAnnihilators.lean`.
- **Setting:** Positive Dirichlet polynomials on `2^a 3^b`, with constant coefficient one. Write `H(σ)` for nonconstant positive mass and `l=log 2`.

## Unit mass is a sharp simplicity boundary

If `P(β+iγ)=0` and `H(β)=1`, all nonconstant phases equal `−1`. Differentiating the literal finite sum gives

`Re P′(β+iγ)=Σ a_n n^(−β) log n≥log 2>0`.

The zero has analytic order exactly one. Both unit mass and derivative `log 2` are attained by `1+2^(β−s)` at `β+iπ/log 2`. A zero with vanishing derivative therefore requires `H(β)>1`.

## Exact frequency cost of a double zero

If `P(β+iγ)=P′(β+iγ)=0` and every nonconstant logarithmic frequency is at most `B`, then

`B>l`, `H(β)≥(B+l)/(B−l)`.

Equivalently, some supported monomial has logarithmic frequency at least

`l(H(β)+1)/(H(β)−1)`.

For `c=(B+l)/2`, the zeroth and first moment equations give
`Σ(c−log n)a_n n^(−β−iγ)=−c`. Each coefficient multiplier has absolute value at most `(B−l)/2`; the triangle inequality proves the bound. Maximizing over the literal finite support removes the auxiliary frequency-bound hypothesis from the existence conclusion.

## Sharp family and absence of a uniform mass gap

For `m∈ℕ`, put `N=2m+2`, `V(s)=2^(β−s)`, and

`P_m(s)=1+(N/(N−1))V(s)+(1/(N−1))V(s)^N`.

At `ρ=β+iπ/log 2`, its value and first derivative vanish. Its only possible nonconstant monomials have logarithmic frequencies `l` and `Nl`, and

`H_m(β)=(N+1)/(N−1)=(Nl+l)/(Nl−l)`.

Thus the frequency-span bound is attained. For every `ε>0`, some such positive polynomial has a zero with vanishing derivative and `1<H_m(β)<1+ε`. Multiplicity forces a strict mass inequality but no uniform positive gap. The marked root is not asserted to be a zeta zero.

## Certificates

- `log_two_le_deriv_re_at_unit_tail_mass`
- `analyticOrderAt_eq_one_of_unit_tail_mass`
- `one_lt_tail_mass_of_zero_deriv`
- `double_zero_forces_frequency_span_cost`
- `double_zero_forces_large_frequency`
- `exists_sharp_unit_mass_simple_annihilator`
- `exists_double_zero_with_sharp_frequency_cost`
- `exists_double_zero_annihilator_with_mass_near_one`

Direct `lake --old env lean` audit passes without warnings. All eight capstones depend only on `propext`, `Classical.choice`, and `Quot.sound`. The module is umbrella-wired. These are sharp annihilator constraints and explicit positive survivors of the failed uniform-gap conjecture; they do not establish AAL.
