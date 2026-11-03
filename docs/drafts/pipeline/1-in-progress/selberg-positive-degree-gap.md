# The positive-degree gap in the Selberg class

- **ID:** selberg-positive-degree-gap
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Wall:** Γ15
- **Statement:** Every full Selberg function has presentation degree zero or at least one; degree zero is the Dirichlet unit.

## Mechanism

For `0 < d < 1`, apply Mellin inversion to the ordinary exponential series `Σ a(n) exp(−nz)`. On a far-left line, the reflected Gamma product has total slope `d`, while the Mellin Gamma denominator has slope one. Their ratio therefore decays faster than every exponential in the line index. Contour shifting should give an entire Taylor remainder plus the contribution of the sole possible pole at one.

Let `G` be the entire Taylor remainder plus the polar term. It is analytic on `Im z > 0`. Agreement with the ordinary exponential series in the right half-plane propagates `G(z+2πi)=G(z)` throughout the upper half-plane. Applying Cauchy's theorem to `G(z)e^{nz}` on rectangles with heights `π, 3π` transports coefficient extraction to `Re z=-R`, giving `|a(n)|≤C_R e^{-Rn}`. In particular, the Dirichlet series converges absolutely at zero.

The functional equation between `Re s = 1/4` and `3/4` then makes the latter Dirichlet series tend to zero vertically: each Gamma quotient tends to zero. The existing vertical-decay theorem forces all positive-index coefficients to vanish. This argument would exclude the gap in the extended class as well; no Euler lower bound or separate pole-removal theorem is needed.

## Dependencies to discharge

- Ordinary, rather than degree-normalized, Mellin contour expansion with a uniform far-left bound for `d < 1`.
- Periodicity of the upper-half-plane continuation and exponential coefficient decay by rectangle transport.
- Gamma-quotient decay between the quarter lines and identification of the continued Dirichlet series there.

Existing sources: `SelbergCuspLeftLineDecay`, `SelbergCuspExpansion`, `ComplexRayMellinInversionGeneralLine`, and the degree-zero classification. No analytic input may remain as a premise in the final theorem.
