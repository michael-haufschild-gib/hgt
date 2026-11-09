# Power-thin exceptions in logarithmic prime windows

- **ID:** B130-local-exceptions
- **Stage:** 1-in-progress
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

The same estimate gives a prime in `[x-x^β,x]` outside every set of size
`C x^γ`: apply it at `y=x-x^β≥x/2`, with constant `C 2^γ`.
In the interior of a selected window, `u=T+O(log T)`, so `δT≤γu`
eventually, uniformly in `u`. With `x=exp u`, the selected window's
exception set has size at most `C x^γ`. The good prime satisfies
`0≤u-log p≤2 exp((β-1)u)`, so it remains in the full window.

The derivative estimate at current width `a` transfers the good-prime
bound to a continuous floor of exponent `b=max(σ,a+β−1)`. Take the exact
width `a=zetaZeroAbscissa−1/2`. The continuous criterion gives `a≤b`.
If `a>σ`, both entries of the maximum defining `b` are strictly below `a`,
a contradiction. No finite iteration or attained extremal zero is needed.
The reverse implication has no exceptions, by the global trace bound at
width `σ`.

## Missing proof

Uniform finite-set prime avoidance, transfer to the interior window, and
the exact-width contradiction have full Lean drafts awaiting verification.
The finite exceptional set is chosen separately in each window and may
contain at most `C exp(δT)` elements; every violating prime must lie in it.
This gives the intended finite violation-count formulation. Corpus search
found global exception and full-window criteria, not this combination. No external novelty claim.

This would weaken the arithmetic target within each observation window;
it would not supply the missing arithmetic estimate.
