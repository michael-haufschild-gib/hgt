# Power-thin exceptions in logarithmic prime windows

- **ID:** B130-local-exceptions
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Independently chosen power-thin exceptional sets preserve exact zero-width detection on arbitrarily late logarithmic prime windows.

## Exact theorem

Fix `σ≥0` and `0≤δ<1`. Every zeta zero satisfies `Re ρ≤1/2+σ` if and
only if there are fixed `K∈ℝ`, `C≥0` such that, for arbitrarily large `T`,
some finite set `E` satisfies

`#E≤C exp(δT)`

and every prime `p∉E` with `|log p−T|≤32log(T+2)` satisfies

`primeWindow p≤archPoleWindow p+K p^σ`.

Equivalently, the prime trace has a lower bound `−K p^σ`, after rescaling
`K` by two. The exceptional set may change independently between windows;
no global exceptional-set bound or density of window centers is required.
The case `σ=0` is RH.

If RH fails, then for every fixed `K`, `C≥0`, and `0≤δ<1`, every sufficiently
late such window contains a prime with trace below `−K` outside every
finite set of size at most `C exp(δT)`. Thus the violating primes cannot
be covered by that many exceptions.

## Proof

Choose `δ<γ<β<1` with `γ≥0` and `β>7/12`. Short-interval prime logarithmic
mass in `(y,y+y^β]` is asymptotic to `y^β`. A finite set of size `C y^γ`
contributes at most `2C y^γ log y=o(y^β)`. Hence a prime survives, with a
starting threshold independent of the finite set.

Apply this at `y=x-x^β≥x/2`, with constant `C 2^γ`, to obtain a surviving
prime below `x` at distance at most `x^β`. In logarithmic coordinates,

`0≤u-log p≤2 exp((β-1)u)`.

For every point of the half-sized interior window, `u=T+O(log T)` and
`δT≤γu` eventually. The same exceptional set therefore satisfies the
avoidance bound there, and the surviving prime remains in the full window.
At current zero width `a`, the trace derivative bound transfers the prime
floor to a continuous floor of exponent `b=max(σ,a+β-1)`.

Take `a=zetaZeroAbscissa-1/2`. The continuous logarithmic-window theorem
forces `a≤b`. If `a>σ`, both entries defining `b` are strictly below `a`,
a contradiction. Neither finite iteration nor an attained deepest zero
is needed. The reverse implication uses the global trace bound at width
`σ`, with no exceptions. Negating the RH equivalence gives the eventual
violation statement.

## Lean

Namespace `GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality`:

- `FinitePrimeAvoidance.lean`: uniform forward, backward, and logarithmic
  prime avoidance for finite exceptional sets.
- `ExceptionalPrimeWindowTransfer.lean`:
  `prime_power_windows_transfer_off_finset`.
- `ExceptionalLogarithmicWindows.lean`:
  `zeta_re_le_iff_prime_logarithmic_power_windows_off_finset`,
  `riemannHypothesis_iff_prime_logarithmic_windows_off_finset`,
  `zeta_re_le_iff_stepanov_logarithmic_power_windows_off_finset`, and
  `eventually_prime_logarithmic_window_negative_off_finset`.

The final production module passed direct `lake --old env lean` checking.
All four final transitive axiom audits contain only `propext`,
`Classical.choice`, and `Quot.sound`. All three modules are wired into the
SurfaceOfSpecZ umbrella.

The corpus already supplied global exceptional-set criteria and complete
window criteria. The new combination allows independently chosen local
exceptions and arbitrarily sparse window centers. No external novelty claim.

## B130 boundary

No arithmetic estimate controlling these violations has been produced.
B130 remains open. The missing input is the displayed one-sided arithmetic
bound on cofinal selected windows outside the permitted exceptional sets.
