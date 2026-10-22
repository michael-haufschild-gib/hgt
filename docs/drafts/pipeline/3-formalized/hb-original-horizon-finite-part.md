# Original horizon finite part and continued radial current

## Mathematical statement

Fix the literal source parameters `s,a,J,K`, radial momentum `chi`, and a
nonreal frequency `w` with `Re w>-2`. Write `H` for the original horizon
solution, `U` for the continued native Green response, and

`T(w)=1/(w-2s)+onsetCorrection(2s,w)`.

The original normalized radial equation has forcing
`F(b)=sqrt(1-b)*continuedSourceProfile(b)/2`. Its Green weight is
`rho(b)=1/sqrt(1-b)`. The existing exact source identity therefore gives

`rho(b) H(w,b) F(b) = b^w G(w,b) T(w)/2`,

where `G` is the literal `horizonMellinCore`, including its Gauss factor and
the complete native radial source remainder. For every fixed `0<B<1`, the
actual source supplies a finite `C` such that
`|G(w,t)-G(w,0)|≤Ct` on `0≤t≤B`.

Define

`R(b,w)=integral[0,b] t^w (G(w,t)-G(w,0)) dt`,

`M(b,w)=G(w,0)b^(w+1)/(w+1)+R(b,w)`,

`P(b,w)=M(b,w)T(w)/2`,

`E(b,w)=G(w,0)b^(w+1)T(w)/(2(w+1))`.

The proved source-specific cutoff identity is

`integral[e,b] rho(t)H(w,t)F(t) dt+E(e,w)`
`=P(b,w)-R(e,w)T(w)/2`.

Moreover,

`|R(e,w)|≤C e^(Re w+2)/(Re w+2) → 0` as `e↓0`.

Consequently the actual cutoff pairing, with its source-determined endpoint
term restored, tends to `P(b,w)`. The raw pairing is not asserted to converge
in the fundamental-QNM strip.

## Identification with the actual response

The original response has the form
`U=N*continuedHorizonMoment+H*continuedOuterMoment` with its already-proved
actual first derivative. Its original Green bracket therefore satisfies

`B(H,U)=W(H,N)*continuedHorizonMoment`.

The actual continued Wronskian is `W(H,N)=-connection/2`, whereas the horizon
moment is `M*T/(-connection)`. Away from connection zeros this proves

`B(H,U)(b)=P(b,w)`.

It also proves `B(H,U)(b)-E(b,w)→0` at the horizon. The subtraction is fixed by
the source; no independently chosen zero boundary condition enters.

The connection zeros are isolated in each nonreal frequency half-plane.
Thus the bracket identity holds as a punctured frequency germ at every
point of the strip, including connection zeros. The finite-part value is
meromorphic without dividing by the connection coefficient; the original
onset factor remains present. This identity does not establish disappearance
of a pole of the full response.

Both fundamental QNMs of every Xi divisor lie in this strip. The capstone
uses the actual physical angular momentum `chi=z/2+i/4` and proves, for
both frequencies and every interior upper cutoff, the cutoff limit,
meromorphy, and original-current germ identity without supplied endpoint
admission, nonresonance, left-covector, or RH assumptions.

## Lean modules

- [FirstEndpointMellinLimit](../../../../formal/GaloisForLFunctions/HTGeometry/FirstEndpointMellinLimit.lean): four theorems for the power bound, vanishing remainder, exact cutoff identity, and cutoff limit.
- [BMOriginalHorizonFinitePart](../../../../formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMOriginalHorizonFinitePart.lean): four theorems restoring the original forcing weight and onset, proving its cutoff identity and limit, and establishing meromorphy.
- [BMOriginalHorizonFinitePartCurrent](../../../../formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMOriginalHorizonFinitePartCurrent.lean): three theorems identifying the actual response bracket, its frequency germ, and its subtracted horizon limit.
- [BMFundamentalHorizonFinitePart](../../../../formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMFundamentalHorizonFinitePart.lean): one unconditional all-Xi capstone for both physical fundamental frequencies.

## Remaining HB work

This closes the radial horizon cutoff limit for the original native source.
The complete modular angular/cusp pairing, all cutoff-commutator channels,
the full joint outgoing inverse and its original causal overlap, the physical
advanced/adjoint left residue, and independent Hawking-clock extinction
remain open. A scalar Green-bracket identity does not identify that full
physical pairing or prove pole survival. RH remains unproved.

## Verification

All four scratch leaves passed `lake env lean`. Each canonical module passed
its own foreground `lake build <module>` audit, without Lean warnings. The
isolated audit reused 4085 existing dependency oleans and produced exactly
four new target oleans. All four installed sources and eight installed
olean/ilean artifacts were byte-verified against that audit. The two area
umbrellas are wired without being built.

The 12 new public theorems occupy 295 source lines. Their scratch-only
`#print axioms` audit reports only `propext`, `Classical.choice`, and
`Quot.sound`. No numerical experiment or computational proof certificate was
used.

The corpus index was refreshed. The subsequent global
`lint --check-generated` failed on the concurrently added, unwired unrelated
module `RHTower.SelbergPositiveEisenstein` and generated-file freshness. No
new HB leaf failure was reported. The global gate therefore remains
incomplete pending those independent edits; no repeat Lean build is needed
for this batch.
