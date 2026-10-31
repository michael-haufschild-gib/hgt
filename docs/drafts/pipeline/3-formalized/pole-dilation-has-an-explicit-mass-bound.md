# Pole dilation has an explicit mass bound

For real C² compact `f` supported in `[-1/2,1/2]`, write
`P(f)=2(∫f(u)e^(u/2))(∫f(u)e^(-u/2))` and `E=∫f²`.
For every `r≥1`,

`|r P(f(r·))−P(f)| ≤ 4e²(r−1)E`.

Put `M(q)=∫f(u)e^(qu)` and `A=∫|f|`. For `|q|,|q'|≤1/2`,
the mean value theorem on `[-1/2,1/2]` gives
`|M(q)|≤eA` and `|M(q)−M(q')|≤(e/2)|q−q'|A`.
Thus at `q=1/(2r)`, each moment changes by at most
`e(r−1)A/4`, and their product changes by at most
`e²(r−1)A²/2`. Change of variables gives
`rP(f(r·))=(2/r)M(q)M(−q)`. Since `1/r≤1` and
`|1/r−1|≤r−1`, its total error is at most
`3e²(r−1)A²≤4e²(r−1)E`; the final inequality is
Cauchy–Schwarz on the unit interval.

Lean: `ArithmeticIncidencePositivity/PoleDilationHasAnExplicitMassBound`,
`realPoleForm_dilation_bound`. Direct Lean check and transitive axiom audit passed;
dependencies use only `propext`, `Classical.choice`, and `Quot.sound`.
