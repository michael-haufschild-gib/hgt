# The invariant cubic cusp barrier

- **ID:** cubic-invariant-cusp-barrier
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [exterior coercivity](cubic-quotient-exterior-coercivity.md)
- **Statement:** For `1<a<b`, the actual cubic quotient has a smooth invariant barrier `φ≥1`, equal to height above `b` in every integral cusp. Its Laplacian defect is continuous and compactly supported, giving `Δφ=Vφ` with `V≥1−C1_K` for compact `K`.

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
Direct source and transitive audits use only `propext`, `Classical.choice`, and `Quot.sound`.

`TheCubicCuspProfileEquation.lean` proves `fullCuspProfileField_laplacian`:
for smooth profiles with `F=LF=0` below height one, the positive Laplacian
of `ΣF(h_x)` is `Σ(LF)(h_x)`. Local finiteness gives a common finite sum
near each point, and the row-profile equation applies term by term.

`TheCubicBarrierPotential.lean` identifies `D=Δφ−φ` in actual Euclidean
coordinates. Its continuous potential `V=1+D/φ` satisfies `Δφ=Vφ` and
`V≥1−C1_K`, where `K=tsupport D` is compact and `C≥0` bounds `|D|`.
The lower bound uses `φ≥1`. Endpoints: `kernelBarrierPotential_equation`
and `kernelBarrierPotential_lower`.

Scalar square completion gives
`|df|²−dφ·d(|f|²/φ)=|df−f·dφ/φ|²≥0`.
The [integrated inequality and completed-space coercivity](cubic-quotient-exterior-coercivity.md) are formalized.
Adapted from OpenAI's `Eisenstein/CuspHeight.lean`,
`SmoothCuspCutoffs.lean`, and `BarrierPotential.lean`; local finiteness
uses the locally proved integral row bound.
