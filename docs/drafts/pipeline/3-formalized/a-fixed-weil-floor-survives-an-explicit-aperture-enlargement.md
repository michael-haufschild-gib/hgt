# A fixed Weil floor survives an explicit aperture enlargement

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)

Let `P=√2 log 2`, `T=1+log π+3 log 2+γ_Euler+π/2+P+2e²`,
`D=P(32e^(1/2)T+2)`, and `B=11+4e²`. Define

`s=min(1/10, min(1/(40000B), exp(-1-20000D)/log 2))`,
`a₊=(181/500)(1+s)`.

Then `181/500<a₊<1/2`. Every real C² compact source supported in
`[-a₊,a₊]` satisfies `Q(f)≥(1/8000)∫f²`.
Every complex C² test on the same support satisfies
`Re Wζ(f,f)≥(1/8000)∫|f|²`, by splitting real and imaginary parts.

Proof. Put `r=1+s`, `E=∫f²`, and suppose `Q(f)<E/8000`.
The one-prime energy identity gives `Levy(f)≤TE`. Normalized dilation
to `g(u)=f(ru)` has three errors. Gamma and pole cost at most
`(10 log r+4e²s)E≤E/40000`. The prime modulus costs at most
`D E/(-log(s log 2))≤E/20000`. Thus
`rQ(g)≤Q(f)+3E/40000<E/5000`.
The proved floor at `181/500` gives `rQ(g)≥E/5000`, a contradiction.
Gauss's quarter-digamma identity identifies `T` with `1+2|γ(0)|+P+2e²`.

Lean target: `ArithmeticIncidencePositivity/AnExplicitLargerApertureRetainsAWeilFloor`.
Gamma symbol constant five is [formalized](../3-formalized/gamma-dilation-has-the-explicit-constant-five.md).
The [physical Gamma bound](../3-formalized/physical-dilation-has-a-logarithmic-gamma-form-cost.md)
and [polar bound](../3-formalized/pole-dilation-has-an-explicit-mass-bound.md)
also passed direct Lean and axiom audits. The
[one-prime energy modulus](../3-formalized/one-prime-dilation-has-an-explicit-energy-modulus.md)
passed both audits. The enlarged-radius bounds, real floor and complex floor
passed direct `lake --old env lean` and transitive axiom audits; their only
axioms are `propext`, `Classical.choice`, and `Quot.sound`.
