# Nonnegative twisted arc sums

- **ID:** twisted-arc-nonnegative-rigidity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** quantitative-blind-repair-for-the-quarter-strip
- **Statement:** A finite twisted Whittaker sum nonnegative on the half arc vanishes there.

## Exact result

For `F(u)=Σ_{n<N} a_n twArcMoment n (arcClamp u)`,
`F≥0` on `[0,1/2]` forces `F=0` throughout that interval.
This strengthens the minimum principle excluding strict positivity.

## Paper proof

The clamped kernels satisfy
`k_c(u)≥(1−2c)k_(1/4)(u)` for `0<c≤1/2`, `0≤u≤1/2`.
This follows pointwise for their densities by splitting at `s=c` and
`s=1/4`, then integrating. Put `I=∫₀^(1/2) F(u)k_(1/4)(u)/√y(u) du`.
If `F≥0`, the stream certificate gives
`2G(1/2)−G(c)/c ≥ (I/2)(1/2−c)`.

If `I>0` and `G(1/2)≤0`, the stream minimum principle forces the stream
nonnegative; its lowest sine mode then forces every coefficient to vanish,
contradicting the strict flux gap. If `G(1/2)>0`, apply that principle to
`ψ−2G(1/2)x`: the wall gives `ψ_xy≤0` at the corner, whereas the linear
flux gap gives `ψ_xy>0`. Thus `I=0`. The kernel `k_(1/4)` is positive before
the corner, so continuity and `F≥0` force `F=0` on the open half arc.
Continuity includes both endpoints.

## Lean

- Module: `GaloisForLFunctions/RHTower/ModularArc/TwistedMomentRigidity.lean`.
- `legendreKernel_half_comparison`: the pointwise kernel comparison.
- `twistedArcMomentSum_eq_zero_of_nonneg`: the exact rigidity statement.
- Foreground check: `lake --old env lean GaloisForLFunctions/RHTower/ModularArc/TwistedMomentRigidity.lean` passed.
- Both declarations' transitive axioms: `propext`, `Classical.choice`, `Quot.sound` only.

This does not yet construct a repair with the arithmetic node, pole,
energy, and mass bounds required for the covariance question.
