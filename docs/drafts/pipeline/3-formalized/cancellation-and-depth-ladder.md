# Cancellation and the depth ladder

- **ID:** A103
- **Stage:** 3-formalized
- **Lean:** `SelectiveArithmetic/TheCancellationAndDepthLadder.lean`

## Statement and proof

Cancellation `|Σ₂ⁿ w(k)|≤C n^(1/2+γ)` gives nonnegative system form on packets
with derivative energy at most their mass, at every rung `2γκ<1` and all
sufficiently large conductors. This is the existing cancellation margin,
whose lower bound is `(log q)/2` times mass minus derivative energy.

Full window positivity at rung `κ` gives an off-line companion to every
sufficiently high zero of depth `δ` with `2δκ>1`. The companion lies within
the exponential aperture in ordinate and differs from the zero and its
reflection. This uses `zeta_companion_of_rung`.

A bounded dyadic Möbius moment of length `T^θ`, `θ>1`, leaves only finitely
many zeros of depth at least `1/(2θ)+ε`. The absolute ordinates of that
finite set have an upper bound, giving the stated eventual depth bound.
The same argument applies to the more general prefix-cancelling mollifier.

`quasiRH_crossRoute_seven_way_tfae` supplies the seven equivalent
power-saving formulations. The combined theorem retains the distinct
bounded-shape and full-window test domains; cancellation alone does not
supply the latter.

Direct Lean check passed. Imported by `SelectiveArithmetic.lean`.
