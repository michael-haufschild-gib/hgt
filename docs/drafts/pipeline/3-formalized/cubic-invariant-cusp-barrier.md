# The invariant cubic cusp barrier

- **ID:** cubic-invariant-cusp-barrier
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [exterior coercivity](../1-in-progress/cubic-quotient-exterior-coercivity.md)
- **Statement:** For `1<a<b`, the actual cubic quotient has a smooth invariant barrier `φ≥1`, equal to height above `b` in every integral cusp. Its height-profile defect is continuous and compactly supported.

Identify integral matrices having the same transformed height. Two classes
with height greater than one coincide: otherwise the integral height-product
bound contradicts their heights. Finite index transfers principal-row local
finiteness to all integral cusp classes.

Let `F(v)=χ(v)(v−1)`, where `χ=0` below `a` and `χ=1` above `b`.
The sum `φ=1+Σ F(h_x)` is locally finite, smooth, invariant, and at least
one. High-cusp uniqueness gives `φ=v` above `b`. The profile operator
`L F=vF′−v²F″` gives `LF−F=0` below `a` and `LF−F=1` above `b`.
Consequently `D=−1+Σ(LF−F)(h_x)` vanishes in every high cusp. Bianchi
reduction puts its support in a compact quotient core.

Lean: `MetaplecticMobiusDescent/TheCubicCuspBarrier.lean`, namespace
`CubicEisenstein`: `fullCuspHeight_high_unique`,
`kernelQuotientBarrier_contMDiff`, `kernelQuotientBarrier_fordCusp`,
`kernelQuotientBarrierDefect_hasCompactSupport`.
Transitive audits use only `propext`, `Classical.choice`, and `Quot.sound`.
`TheCubicCuspProfileEquation.lean` proves `fullCuspProfileField_laplacian`:
for smooth profiles with `F=LF=0` below height one, the positive Laplacian
of `ΣF(h_x)` is `Σ(LF)(h_x)`. Local finiteness gives a common finite sum
near each point, and the row-profile equation applies term by term.
Identification of `D` with `Δφ−φ` and exterior coercivity remain open.
Adapted from OpenAI's `Eisenstein/CuspHeight.lean`; local finiteness uses
the locally proved integral row bound.
