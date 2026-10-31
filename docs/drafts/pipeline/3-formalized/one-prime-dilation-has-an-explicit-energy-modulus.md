# One-prime dilation has an explicit energy modulus

Let `E(f)=∫f²`, `Q(f)` be the full Weil form, and
`P=√2 log 2`, `T=1+2|γ(0)|+P+2e²`.
Gauss's quarter value gives
`T=1+log π+3 log 2+γ_Euler+π/2+P+2e²`.
For real C² compact sources supported in `[-1/2,1/2]`,

`Q(f)=2γ(0)E(f)+Levy(f)−P A_f(log 2)+Pole(f)`.

All prime atoms from three onward vanish by support. Cauchy–Schwarz gives
`|A_f(t)|≤E(f)` and `|Pole(f)|≤2e²E(f)`. Consequently
`Q(f)≤E(f)` implies `Levy(f)≤T E(f)`.

For `r>1` and `0<(r−1)log 2<1`, normalized dilation satisfies

`|rQ(f(r·))−Q(f)| ≤ [10 log r+4e²(r−1)+D/(-log((r−1)log 2))]E(f)`,

where `D=P(32e^(1/2)T+2)`. The three terms follow from the Gamma modulus,
the two-moment polar estimate, and the existing linear logarithmic
correlation modulus. The correlation scaling law is exact.

Lean: `ArithmeticIncidencePositivity/OnePrimeDilationHasAnExplicitEnergyModulus`.
`primeSum_eq_two_of_unit_support`, `onePrimeLowEnergyConstant_closed`,
`biScaleLevyEnergy_le_of_fullZeroForm_le_mass`, and
`fullZeroForm_dilation_bound` passed the direct Lean check and transitive
axiom audit: only `propext`, `Classical.choice`, `Quot.sound`.
