# [BRIDGE] Fixed connected CCM clock: polar continuation fact

## [PIVOT] Differentiate before continuation

The first-transform Stieltjes continuation below is stronger than the fixed-clock
no-go needs. Six spectral derivatives remove the entire `h⁻⁶` factor in the
literal connected polar density. Put

`R_b(z)=exp(-bz)/z`, `S_b(z)=exp(-bz)(b/z+1/z²)`.

On the safe Euler half-plane `Re u>1+ω`, differentiation under the integral and
`ccmSuzukiConnectedThirdGradeWeight_sixthJet` give the exact identity

`(d/du)^6 Pω(u) = (96/ω³) Σ_(ε=±1) [R_b(u-ω-ε/2) - R_b(u+ω-ε/2) - 2ω S_b(u-ε/2)]`.

Every pole of this expression is real. Thus its sixth derivative, unlike its
first transform, has an elementary holomorphic continuation at every nonreal
point. This avoids Stieltjes/Fubini infrastructure in the specific no-go proof.
The identity and its differentiation-under-integral step still need Lean proof;
the weight cancellation alone is already Lean-proved in
`CCMFUSuzukiConnectedSixthJet.lean`.

If a literal fixed-positive-clock connected window were uniformly bounded,
`ccmSuzukiConnectedWindow_eq_cesaroPrimitive` would make its first Cesàro
primitive grow at most linearly. The generic second-Abel analytic mechanism in
`CCMGuinandWeilThirdGradeCesaroCompleteness.lean` then supplies a holomorphic
completed Abel transform on `Re u>0`. On the safe half-plane this is the actual
prime-minus-polar source by `ccmSuzukiConnectedThirdGradeCumulative_abel_eq_source`.
Six derivatives and the rational polar identity would analytically continue
the actual prime sixth jet at a nonreal point `ρ-1/2+ω`, where
`exists_nonanalytic_ccmSuzukiConnectedSixthJetDefect` proves the shifted Xi
divisor obstruction. Transporting the safe-half-plane equality to that point
via a cleared-denominator identity theorem remains a distinct Lean bridge.

**Stronger whole-route consequence if closed:** for every fixed `ω>0` and every
`α<ω`, the literal connected Suzuki window cannot satisfy any cofinal bound
`|Wω(H)| ≤ C exp(α H)`. Indeed such a bound makes its Cesàro primitive
`Q(H)=H Wω(H)` of exponential order `α`, so its second Abel transform is
holomorphic on `Re u>α`, while the rightmost Hardy-height zero produces a
shifted prime pole at `Re u=Re ρ-1/2+ω≥ω`. Thus the positive-clock window has
an unconditional exponential-rate floor, not merely unboundedness. This
rate-strengthening is a paper deduction, not yet Lean-closed.

The RH-bearing zero-clock window is unaffected. The result identifies positive clock
spectral support as a pre-RH obstruction, rather than a candidate positivity
producer. A conjectural extension to compact shift distributions would make
the right edge of clock support the admissibility invariant, but that broader
claim is not proved here.

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
