# Original retarded-field source-encoding obstruction

Status: this carrier matching option is impossible. Positive amplitude recovery and exact field classification are formalized in Lean. RH remains open.

Target: decide whether the literal source carrier can determine the original
retarded potential on the physical causal wedge, for every nonzero source
amplitude. This tests temporal/metric matching before a QNM readout.

[PROVED IN LEAN] The original retarded potential retains exactly the squared
amplitude at every actual Xi copy: equality of its complete physical fields
for amplitudes `a,b` is equivalent to `a^2=b^2`.

Evidence: the original forced equation retains the full scalar half-square
and gradient energy; all radial forcing coefficients scale quadratically.
The carrier instead erases every amplitude at critical copies (DN40).

Attack: use the original wave equation to recover the forcing from the
potential, separate its radial coefficients to recover the scalar square,
and prove that the original Eisenstein scalar is not identically zero.
The proposed statement is stronger than nonvanishing of a selected QNM
value; cancellation in a single source period cannot settle it.

Whole-route consequence: no decoder of the unchanged carrier can
match the original causal potential across amplitudes, even before temporal
integration or meromorphic continuation. A source-retaining representation
remains possible; neither this obstruction nor such a representation proves RH.

## Paper proof

Write `rho=q.1`, `s=physicalRate q br`, and `S=scalar(center q)`.
The horizontal mean of `S` is `A*y^(1-rho)+B*y^rho`, with
`A=Lambda(2*rho-1)` and `B=Lambda(2*rho)`. If `S` vanished identically,
the mean and its derivative at `y=1` would give `A+B=0` and
`(1-rho)*A+rho*B=0`. Since `Im(rho) != 0`, both coefficients would vanish.
For `Re(rho)>=1/2`, `B` is nonzero by the completed-zeta zero-free closed
right half-plane. For `Re(rho)<=1/2`, reflection gives the same conclusion
for `A`. Thus some original angular point has `J=S^2/2 != 0`.

The exact untransformed forcing at this point is an everywhere nonzero
envelope on the physical radial interior times
`A_s*J+B_s*u^2*((s+2)^2*J-K)`, where
`A_s=(5*s^2+15*s+4)/4`, `B_s=s*(s-1)/4`, and `u=radialUnit(t)`.
Here `-2<Re(s)<-1`; hence
`4*Re(A_s)=5*(Re(s)+1)*(Re(s)+2)-6-5*Im(s)^2<0`.
As `t` tends to zero from below, `u` tends to zero. The bracket therefore
tends to the nonzero value `A_s*J`. At some physical interior radius the
unit-amplitude forcing is nonzero. Choose the unchanged late onset `p=2`;
its exponential is nonzero as well.

Equality of two complete causal potentials on the open physical wedge
implies equality of their angular and mixed null derivatives there.
The original wave equation consequently equates their original forcings.
At the point above these are `a^2*F_1` and `b^2*F_1`, with `F_1 != 0`.
Thus `a^2=b^2`. Conversely, equal squared amplitudes give identical original
forcing everywhere; the original retarded source integral gives identical
potentials. No uniqueness hypothesis or prescribed mode coefficient is used.

At an actual critical Xi copy the literal carrier is zero for both amplitudes
one and two, while the corresponding physical fields are unequal. Therefore
an arbitrary carrier decoder cannot reconstruct these fields. The positive
survivor is the all-copy squared-amplitude classification and recovery by a
local wave-operator observation of the original potential.

## Exact scope

The matched object is the original scalar causal potential on `0<p<r`,
with all angular coordinates retained. The decoder may be nonlinear,
discontinuous, copy-dependent, and return an arbitrary field. The no-go
requires matching across nonzero amplitudes; it does not exclude fitting a
single fixed amplitude or using additional original source data. It does
not classify arbitrary metric gauge equivalences.

The positive theorem holds for every actual Xi copy and both source
branches. One original interior point and a nonzero normalization, chosen
independently of amplitude, recover `a^2` by applying the original wave
operator to the actual potential. Thus a zero of one scalar QNM readout
must not be identified with a vanishing full potential.

## Lean certificate

[NativeFieldMatchingNoGo](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMNativeFieldMatchingNoGo.lean) proves
`exists_original_scalar_ne_zero`, `exists_original_forcing_ne_zero`,
`exists_originalPotential_amplitude_observation`,
`originalPotential_amplitude_fibres`, and
`not_exists_originalPotential_source_decoder`.
The statement adds no source-admission, matching, nonvanishing, or RH premise.
No heartbeat or transparency override is used.

Scratch verification and isolated exact-module audit passed (91 seconds, two
jobs). The leaf is wired into `RHTower.lean`; no umbrella build was run.
Repository formal lint passed.
