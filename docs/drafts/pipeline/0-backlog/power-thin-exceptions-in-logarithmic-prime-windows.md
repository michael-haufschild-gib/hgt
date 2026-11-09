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

Choose `max(δ,7/12)<β<1`. In the interior of a selected window,
`log x=T+O(log T)`. The total exceptional prime logarithmic mass is at most
`C exp(δT)(T+O(log T))=o(x^β)`, uniformly over that interior.
The short-interval prime theorem therefore supplies a good prime within
`O(x^β)` of every interior point, uniformly across the selected windows.

The gap derivative estimate should lower a current width `a` to
`max(σ,a+β−1)`. Repeated application, starting at `a=1/2`, reaches `σ`.
The same prime windows are reused at each step; the interior radius is
always half the original radius.

## Missing proof

Uniform local prime avoidance, the window version of the width iteration,
and the exact finite violation-count formulation require proofs and Lean
formalization. Corpus search found global exception and full-window
criteria, not this combination. No external novelty claim.

This would weaken the arithmetic target within each observation window;
it would not supply the missing arithmetic estimate.
