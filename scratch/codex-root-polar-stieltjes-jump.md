# [BRIDGE] Fixed connected CCM clock: polar continuation fact

## Exact statement (paper proof; Lean pending)

Fix `b>0`, `ω>0`. Let

`Pω(u) = ∫_(b,∞) exp(-u h) ccmSuzukiConnectedPolarDensity(ω,h) dh`

on its safe half-plane `Re u>1+ω`. Then `Pω` has a holomorphic continuation to
each open half-plane `Im u>0` and `Im u<0`. Thus a nonreal singularity in the
sixth spectral derivative of the completed connected Abel source cannot be
attributed to the polar channel. No RH hypothesis enters this statement.

Write `J_k(s)=∫_b^∞ exp(-s h) h^(-k) dh` for `k=5,6` and `Re s>0`. The exact
Lean identity `ccmSuzukiConnectedThirdGradeWeight_sixthJet` and the literal
polar density `2 cosh(h/2)` give

`Pω(u)=(96/ω³) Σ_(ε=±1) [J_6(u-ω-ε/2)-J_6(u+ω-ε/2)-2ω J_5(u-ε/2)]`.

The exact pointwise precursor
`h^6·ccmSuzukiConnectedPolarDensity(ω,h) =
(96/ω³)(e^(ωh)-e^(-ωh)-2ωh)·2cosh(h/2)`
passed `lake env lean` in a scratch file on this toolchain. The scratch file
was removed after verification. The integral decomposition and continuation
have not yet been checked in Lean.

For every integer `k≥1`, Gamma integration and absolute Fubini on `Re s>0`
give the *same germ* as the Stieltjes integral

`J_k(s)=1/(k-1)! ∫_0^∞ t^(k-1) exp(-b(s+t))/(s+t) dt`.

The latter integral is holomorphic on `ℂ \ (-∞,0]`. On each compact subset,
`|s+t|` is bounded below for bounded `t`, and is at least `t/2` for all large
`t`; `b>0` supplies an integrable exponential majorant, including for every
complex derivative. Real shifts of `s` leave both open half-planes inside
this domain. This proves the continuation claim.

## Consequence for the hard no-go bridge

`CCMFUSuzukiConnectedCompletedAbel` already gives the source-faithful first
Abel identity on `Re u>1+ω`; `CCMFUSuzukiClockVolterraBridge` says the Cesàro
primitive of that same source is `H` times the literal connected window.
If the window were uniformly bounded, Laplace transformation of its
linear-growth primitive would analytically continue the first Abel source
to `Re u>0`. Adding the continuation of `Pω` would analytically continue the
*actual prime channel* through the upper/lower part of that half-plane.

`CCMFUSuzukiConnectedPrimeSixthJet` already identifies the sixth derivative
of the prime channel on the safe Euler half-plane. Its endpoint-shifted
unweighted von-Mangoldt series has a pole at the rightmost zero on a Hardy
height, while the opposite shift and the unshifted derivative are regular
there (`CCMHardyHorizontalEndpointZero` and the pole argument in
`CCMFUSuzukiConnectedJetPoleNoGo`). The endpoint has nonzero imaginary part
because Xi has no real zeros. Meromorphic identity along the zero-free
rightward horizontal ray then contradicts analytic continuation of the
prime channel. This route needs *no sixth differentiation of the polar
integral*: its separate off-real continuation is stronger.

This is a proved paper-level bridge, not the primary conceptual-jump conjecture
and not a Lean-closed fixed-clock no-go. Lean work still
needed: the Stieltjes representation/holomorphy; the bounded-window
second-Abel analytic continuation for this literal source; and the
prime-channel meromorphic identity/identity-theorem transport. It does not
bound the zero-clock RH-bearing window, and it must not be advertised as an
RH proof or external-priority claim.
