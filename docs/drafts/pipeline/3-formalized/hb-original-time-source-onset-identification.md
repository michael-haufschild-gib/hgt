# HB original time source and its retained onset derivative

- **Stage:** 3-formalized; scratch, canonical leaf and new-declaration axiom audits passed.
- **Type:** THEOREM (Lean).
- **RH status:** open.
- **Frontier map:** read-only.

Chain: literal theta cusp → Xi occurrence → retained spin-two source → original
causal response and left-QNM pairing → independent Hawking-clock extinction → RH.

## Exact source identification

The original quadratic scalar-current sector now has an explicit time source,
an actual differentiated gradient-absorbing field, and the exact convergent
Laplace transform used by its frequency-domain construction. The fixed smooth
onset is differentiated throughout. Its second derivatives cancel between
static time and tortoise radius; its first derivative survives with a forced
coefficient.

Write `t<0` for original tortoise radius, `tau` for static time,
`u(t)=-tanh(t)`, and fix the physical source rate s and amplitude a. Define

`A(t)=sourceAmplitude(s,0,a,1,t)`,
`B(t)=-s(s-1) A(t) u(t)^3/4`,
`H(v)=smoothTransition(v) exp(2s v)`.

Here B is the original explicit radial lift, and `v=tau+t` is original ingoing
time. The full literal scalar-square angular field is Q; the original gradient
energy is retained in `timeOriginalForcing`.

Lean proves the exact frequency polynomial identity

`P(s,w,u)=P(s,0,u)+w P1(s,u)`,
`P1(s,u)=-s(s-1)u^2(u-1)((2s+3)u+3)/2`,
`A(t) P1(s,u(t))=2 B'(t)`.

Consequently the actual reduced time coefficient is

`R(tau,t)=reducedCoefficient(s,0,a,1,t) H(tau+t)`
`         + 2 B'(t) H'(tau+t)`.

For the actual field `B(t) H(tau+t) Q(z)`, the original wave operator is
`d_tau^2-d_t^2-(1-u(t)^2) Delta_hyperbolic`. All displayed derivatives are actual
Lean derivatives. The complete scalar-current identity is

`timeOriginalForcing = timeFieldWave(timeLiftField) + R Q`.

The full angular gradient term is absorbed by this field using the proved
literal angular equation. Both original angular source coefficients are retained.
This statement concerns the scalar-current sector; it does not construct the
complete nonlinear Einstein correction.

## Convergent transform and boundary term

For `Re(w)>Re(2s)`, both H and its actual first derivative have absolutely
convergent weighted ray integrals. Integration by parts proves

`Laplace(H')=w Laplace(H)`.

The zero-time boundary value is H(0)=0. At infinity the weighted function equals
the decaying exponential after the transition interval. The compact transition
derivative is retained in H', so this is an integral identity for the actual
smooth profile.

Translation invariance of the full integral, together with causal support,
proves the original delayed ray identity

`Laplace_tau(f(tau+t))=exp(w t) Laplace(f)` for `t<=0`.

Absolute convergence is proved separately. Substitution gives

`Laplace_tau(R)=reducedCoefficient(s,w,a,onsetTransform(2s,w),t)`.

The full original scalar current and the actual time wave of the full angular
lift likewise transform into their original frequency-domain expressions.
The latter follows by integrating the proved time-source identity, retaining
both terms, and comparing with the original frequency-source identity.

## Native spatial admission

For every fixed static time, R is continuous in tortoise radius and vanishes
when `tau+t<0`. Its support in the physical half-line is therefore contained
in a compact interval. This proves radial L² admission in the original measure.

Multiplication by the actual native square remainder
`squareResidual q (coordinates z)` gives `timeCuspMainForcing`. Existing
separated-product L² admission and the proved angular remainder norm construct
`timeCuspMainVector` in the original `SpatialSpace`. It agrees almost everywhere
with the actual source and equals zero for every `tau<=0`. At each original
spatial point its convergent time transform equals exactly the square-remainder
channel of the admitted frequency residual.

## Lean surface

Route namespace: `RHTower.D4BMJointSource`. Canonical module prefix:
`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSource`.

| Suffix | Public theorems | Content |
|---|---:|---|
| FrequencyAffine | 4 | Exact polynomial cancellation and lift derivative |
| OnsetJets | 5 | Actual fixed-onset derivative chain and support |
| TimeLiftJets | 6 | Actual time/radial derivatives and null-coordinate cancellation |
| OnsetLaplace | 4 | Absolute convergence, integration by parts and onset transforms |
| TimeField | 3 | Complete scalar-current time-source identity |
| TimeLaplace | 7 | Actual delayed source and differentiated-wave transforms |
| TimeAdmission | 7 | Native radial/joint L² admission and causal source vector |

Generic namespace `GaloisForLFunctions.HTGeometry`:
`CausalLaplaceDelay` has four public theorems on causal ray integration,
absolute convergence and complex Laplace translation.

Total: eight leaves, forty public theorems, 626 source lines.

## Audit

All eight canonical leaves passed individual `lake build <module>` audits in
an isolated package using existing dependency caches: two jobs per leaf, no
warnings. The eight canonical source files and sixteen installed
`.olean`/`.ilean` artifacts match their audited copies. Each leaf is imported
exactly once by its area umbrella; no umbrella was built.

A scratch `lake env lean` audit checked all forty new public theorem axioms.
Every result contains only `propext`, `Classical.choice`, and `Quot.sound`.
Existing theorem axioms were not re-audited. Scoped whitespace and wiring
checks passed; no numerical computation or dependency rebuild was used.

The source index was refreshed. The last repository-wide
`scripts/formal_tools.py lint --check-generated` run did not pass: concurrent
`BoundedPlaneDisplacementBatch` and `MobiusDivisorApproximateTwoReserve` modules
were not yet wired, and `LEAN_API.md`/`LEAN_OVERVIEW.md` had generated-file drift.
It also reported 141 large-file warnings. None of these findings concerns the
eight HB leaves; their scoped wiring and whitespace checks passed. Concurrent
source files and their unfinished wiring were preserved.

## Remaining hard obligations

The complete cusp residual also contains three cutoff-principal Green-response
terms. Their common causal time family, all cutoff commutators, and the full
joint vector transform remain to be proved. Pointwise transform identities
and L² admission of every time slice do not yet establish Bochner time
integrability or interchange of the time transform with spatial completion.

Applying the previously constructed joint causal response to that complete
time source remains open. So do the constrained Einstein correction sectors,
left-QNM continuation, multiplicity-matched spin-two/AIME projection and
independent Hawking-clock extinction. These source identities imply no
restriction on Xi-zero locations.

No numerical experiment, computational certificate or external novelty claim
is involved. Existing route-independent requirements already cover retention
of onset terms and physical-domain identification; no universal-law entry is
added. The frontier map was not edited.
