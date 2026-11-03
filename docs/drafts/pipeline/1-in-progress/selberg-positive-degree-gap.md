# The positive-degree gap in the Selberg class

- **ID:** selberg-positive-degree-gap
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Wall:** Γ15
- **Statement:** Every full Selberg function has presentation degree zero or at least one; degree zero is the Dirichlet unit.

## Mechanism

For `0 < d < 1`, apply Mellin inversion to the ordinary exponential series `Σ a(n) exp(−nz)`. On a far-left line, the reflected Gamma product has total slope `d`, while the Mellin Gamma denominator has slope one. Their ratio therefore decays faster than every exponential in the line index. Contour shifting should give an entire Taylor remainder plus the contribution of the sole possible pole at one.

The exponential series is `2πi`-periodic. Its continuation near `2πi` transports analyticity to zero, removing the polar contribution. Entire periodic continuation then forces exponential coefficient decay, hence absolute Dirichlet convergence on every vertical line. On a left vertical line, the functional equation and the Euler product give a growing Gamma quotient times a uniformly nonzero reflected series, contradicting boundedness.

## Dependencies to discharge

- Ordinary, rather than degree-normalized, Mellin contour expansion with a uniform far-left bound for `d < 1`.
- Periodic removal of the polar term, and exponential coefficient decay from the resulting entire continuation.
- Positive-degree Gamma-quotient growth on a fixed left vertical line, with the Euler lower bound derived from the class axioms.

Existing sources: `SelbergCuspLeftLineDecay`, `SelbergCuspExpansion`, `ComplexRayMellinInversionGeneralLine`, and the degree-zero classification. No analytic input may remain as a premise in the final theorem.
