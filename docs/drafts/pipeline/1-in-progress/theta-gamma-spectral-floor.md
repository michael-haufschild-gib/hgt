# A Gamma spectral floor for the integrated first atom

- **Stage:** 1-in-progress.
- **Question:** Which Gamma norm survives radial integration at every degree?
- **Inputs:** `BesselHalfOrderSquare`, `BesselRadialSlice`, `BesselWeightedTail`.

Write `Fτ(x)=x|K_(1/2+iτ)(x)|²`. The corpus proves `(exp(2x)Fτ(x))′≥0` and `2π T₁(τ,q)=∫ℝFτ(sqrt(q²+v²))dv`.

The endpoint identity `lim_(x→0+)Fτ(x)=|Γ(1/2+iτ)|²/2=π/(2cosh(πτ))` gives the all-frequency floor `Fτ(x)≥π exp(−2x)/(2cosh(πτ))`. Restricting the radial slice to `|v|≤1`, then applying the existing weighted-tail reserve, gives

`B_q(b)≥2sqrt(q)(q²−2q−1)exp(−2(q+1))/cosh(πb/2)`, `q≥3`.

For `C(q)=2sqrt(q)(q²−2q−1)exp(−2(q+1))>0`, the target polynomial payment is

`C(q)∫P(b)²/cosh(πb/2) db ≤ ∫P(b)²B_q(b) db`

for every real polynomial, without a degree-dependent constant. The endpoint and polynomial payment passed a Lean proof check with only `propext`, `Classical.choice`, and `Quot.sound`. The production leaf `CompletedArithmeticForms/BesselGammaSpectralFloor.lean` uses the inverse-Gaussian Mellin identity, dominated convergence, and square monotonicity; its final individual audit remains pending. This comparison has the actual strip scale. Payment for the complete unequal-pair aggregate remains separate and open.

## Stronger comparison under investigation

The corpus's `WeilWorkDeficitMellin.scaled_mellin` suggests the exact zero-cutoff density
`B₀(2τ)=(τ²+1/16)|Γ(5/4+iτ)|²`.
The next conjecture is `B_q(2τ)≥c(q)(1+τ²)|Γ(5/4+iτ)|²` for some explicit `c(q)>0` and every `τ`. Proposed mechanism: extend the positive radial-square representation to positive cutoffs below one; transport the first weighted tail by its exponential slope bound; compare the higher weighted tails with their complete Mellin masses. The existing sech floor can handle the remaining compact frequency interval. Neither this stronger comparison nor the complete aggregate payment is yet proved.

A sharper intermediate payment keeps the upper tail: `B_q(2τ)≥T_(7/2)(τ,q)/2` for `q≥3`. Indeed the endpoint costs at most `12q T_(3/2)`, while `T_(7/2)≥(q²+q+1/2)T_(3/2)` and `(7/2)(q²+q+1/2)≥12q+6`. This candidate avoids losing the two frequency powers in the natural Gamma scale; Lean verification is pending.

Extending exponential transport to every positive cutoff would give
`T_p(τ,q)≥exp(−2q)T_p(τ,0)` for `p>1`.
The complete Mellin mass is `T_p(τ,0)=|Γ((p+1)/2+iτ)|²/4`.
Together these yield the stronger candidate
`B_q(2τ)≥exp(−2q)|Γ(9/4+iτ)|²/8` for `q≥3`.
The positive-cutoff radial-square extension is drafted in `BesselPositiveCutoff.lean`; the upper-tail payment is drafted in `BesselUpperTailReserve.lean`. Neither draft has passed its audit yet.
