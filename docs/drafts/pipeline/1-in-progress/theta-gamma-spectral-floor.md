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
