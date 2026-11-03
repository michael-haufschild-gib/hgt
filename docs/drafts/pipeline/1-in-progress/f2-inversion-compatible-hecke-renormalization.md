# F2 — retain the Hecke boundary without breaking modular inversion

- **Stage:** 1-in-progress
- **Conjecture:** For every upper-resonant core, subtracting its exact Hecke boundary coefficient times `b_s(a)=(1+a)^(−2s)` restores whole-axis Haar energy and preserves modular inversion.
- **Purpose:** Replace the discontinuous cutoff representative of the boundary channel by a representative compatible with the actual Lewis structure.

## Candidate mechanism

The explicit wave satisfies `I_s b_s=b_s`, has lower trace one, and finite upper Haar energy for `Re s>0`. Its difference from `1_(0,1)` is `O(a)` near zero and square-integrable at infinity. Thus the retained-channel classification would imply

`T₂,s core_s − core_s(2)b_s ∈ L²((0,∞),da/a)`.

Since both raw Hecke transport and the wave respect modular inversion, so does this corrected image. The expected lower estimate is `O(a^(1−2 Re s))`; inversion then gives the sharp outgoing `O(a⁻¹)` estimate again.

## Questions

Prove these statements for the actual core, then determine whether repeated corrected Hecke transport preserves the same two-endpoint class. Iteration requires regularity at every branch evaluation point; local differentiability only at `1/2` is insufficient. The correction does not identify PM's signed form with Haar norm or supply positivity.
