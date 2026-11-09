# Power-thin exceptions in logarithmic prime windows

- **ID:** B130-local-exceptions
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Statement:** A one-sided prime trace bound outside `O(exp(δT))` exceptions,
  `δ<1`, on arbitrarily late windows `|log p−T|≤32log(T+2)` detects exact zero width.

## Target

Fix `σ≥0` and `0≤δ<1`. Conjecturally `Re ρ≤1/2+σ` for every zeta zero
is equivalent to the existence of fixed `K,C` and arbitrarily large `T`
for which at most `C exp(δT)` primes in the window violate

`2 Re lagStructure(log p) ≥ −K p^σ`.

The exceptional primes may change independently between windows. No global
exception-count assumption is imposed. In particular, failure of RH would
force more than `exp(δT)` values below every fixed `−K` in every sufficiently
late logarithmic window, for every `δ<1`.

## Corpus inputs

- `ScaleLocality/PrimePowerWindowTransfer.lean`: prime-gap transfer with a
  derivative bound controlled by the current zero width.
- `SurfaceOfSpecZ/AlmostAllPrimesAndTheStepanovBoundary.lean`:
  `ShortPrimeSparse`, `powGaps_primes_diff_of_shortPrimeSparse`, and
  `shortPrimeSparse_of_card_le_rpow` give the global exception theorem.
- `tendsto_theta_short_window_div_seven_twelfths`: prime logarithmic mass in
  `(x,x+x^β]` is asymptotic to `x^β` for `7/12<β<1`.
- The logarithmic-window depth criterion is still under formalization on
  `1-in-progress/b130-logarithmic-windows-by-positive-source-repair.md`.

## Proposed mechanism

Choose `δ<γ<β<1` with `β>7/12`. Short-interval prime mass gives, uniformly
for every finite set `E` with `#E≤C y^γ`, a prime outside `E` in
`(y,y+y^β]`, once `y` is large: the total mass is asymptotic to `y^β`,
whereas the excluded mass is at most `C y^γ log(2y)=o(y^β)`.
The threshold depends on `C,γ,β`, not on `E`.

In the interior of a selected window, `u=T+O(log T)`. Set
`x=exp u`, `y=x-x^β`. Then `log y=u+o(1)` and
`δT≤γ log y` eventually, uniformly over the interior. Hence the window's
exception count `C exp(δT)` is at most `C y^γ`. The prime just obtained
satisfies `x-x^β<p≤x`, remains in the full window, and avoids its finite
exception set. Thus `0≤u-log p≤2 exp((β-1)u)`.

The derivative estimate at current width `a` transfers the good-prime
bound to a continuous floor of exponent `max(σ,a+β−1)`. Starting at
`a=1/2`, iteration gives `a_n=max(σ,1/2-n(1-β))`, which reaches `σ`
after finitely many steps. Each step reuses the same prime windows; the
continuous criterion uses their interior halves. The reverse implication
has no exceptions, by the global trace bound at width `σ`.

## Missing proof

Uniform local prime avoidance, the window version of the width iteration,
and the exact finite violation-count formulation require proofs and Lean
formalization. Corpus search found global exception and full-window
criteria, not this combination. No external novelty claim.

This would weaken the arithmetic target within each observation window;
it would not supply the missing arithmetic estimate.
