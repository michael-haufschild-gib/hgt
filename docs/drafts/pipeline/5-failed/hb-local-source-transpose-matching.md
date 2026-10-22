# Literal source transpose versus physical QNM boundary admission

Target: full temporal/metric/QNM matching in HB. Fixed-clock source reflection has an exact density dual, but that dual has an AdS pole. Test whether a different radial multiplier can preserve the original source-transpose identity and satisfy the physical fundamental-QNM boundary condition.

Retired candidate: a nonzero differentiable radial multiplier of the opposite literal source branch gives both the exact full-source transpose and an AdS-admitted physical QNM test, with the original onset and angular half-square retained. The obstruction and exact positive classification below are closed in Lean.

Classification [BRIDGE, Lean verified]: at every actual Xi copy, all such source-transpose multipliers are constant multiples of `(1+u)^5/u^4`, where `u=-tanh(x)` and `x<0`. The actual source contact is proved nonzero somewhere; it is not replaced by an independent angular input. The forced boundary charge rules out an admitted nonzero member.

Positive survivor, paper and Lean closed: the exact one-dimensional space of literal local transposes, with its source-determined boundary coefficient. Scope excludes projected actions, integral transforms, angular operators, changed time variables and boundary modifications that do not preserve the stipulated identity.

Evidence: `ThetaCuspHawkingBMSourceDensityDual` supplies one exact transpose and its boundary coefficient. `ThetaCuspHawkingBMSourceContactRigidity` supplies an actual contact-jet identity; `ThetaCuspHawkingBMNativeFieldMatchingNoGo.exists_original_scalar_ne_zero` supplies nonzero original scalar at every Xi occurrence.

The broad literature search found [Jin–Ma–Zuazua, January 2026](https://arxiv.org/abs/2601.03616): its transmutation averages auxiliary-time wave propagators to obtain diffusion, assuming a nonnegative self-adjoint factorization. It does not supply an HB fixed-clock source-to-QNM identification. It does motivate distinguishing a local multiplier from a time-integral transformation.

## Paper proof

Write `S=scalar(center q)`, `Q=S²/2`, `λ=ρ(ρ−1)`, and
`C=((7λ−2)Q−2ΔQ)/8`. The scalar nonvanishing theorem and the exact contact identity imply `C` is not identically zero: otherwise its first and second angular derivatives vanish, while the identity gives `(λ−2)(λ−6)(3λ−2)S⁴=0`. The prefactor is nonzero at every actual Xi occurrence.

For an arbitrary differentiable weight `W`, subtract its proposed transpose identity from the literal forcing identity. Multiply by `u−1` to obtain exactly

`−2(1−u²)u³ seed(s,1,2,x,1) seed(−s−3,1,2,x,1) C(z)`

times

`W′(x)−(u−1)(1−4/u)W(x)`.

At a point with `C(z)≠0`, every preceding factor is nonzero on `x<0`; the fixed onset equals one at ingoing time two. Hence the displayed differential equation is forced by the actual source. Its known nonvanishing solution is `D=(1+u)^5/u^4`. The derivative of `W/D` vanishes on the connected physical radial interval, so `W=cD`. Conversely, every such weight preserves the full identity for every source amplitude, dual amplitude and original onset time, by linearity of the transpose.

The original density-dual boundary theorem now gives

`lim_(x→0−) u⁴ W(x) seed(t,a,v,x,Q) = c a² timeOnset(2t,v) Q`,

with `t=−s−3`. For a nonzero weight, `c≠0`. At a point where `S≠0`, with `a=1,v=2`, this limit is nonzero. Any finite unscaled AdS limit would instead make it zero. Thus no nonzero preserving weight has finite AdS limits at every angular point. In particular it cannot equal any fundamental physical QNM radial mode, even for another Xi copy, either radial normalization, either QNM branch, and arbitrary angular coefficient: all such modes have zero AdS limit.

Whole-route consequence: this obstruction is to the whole differentiable **radial multiplication** repair of the exact fixed-clock source transpose, not merely to the originally displayed weight. Its positive survivor is an exact one-dimensional solution space and a nonzero boundary charge at every Xi source. An integral transform, angular operator, changed clock, or an additional boundary contribution is outside this theorem and still requires an actual physical matching proof.

## Lean audit

[ThetaCuspHawkingBMLocalSourceTransposeRigidity.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMLocalSourceTransposeRigidity.lean), namespace `RHTower.D4BMLocalTranspose`:

- `exists_sourceContact_ne_zero`: actual contact nonvanishing.
- `source_weight_derivative`, `source_weight_classification`, `preservesSource_iff`: forced equation and exact converse classification.
- `preserving_weight_boundary_charge`: retained endpoint coefficient.
- `not_exists_admitted_source_weight`: no nonzero preserving weight has all finite angular-point AdS limits.
- `not_exists_physicalQNM_source_weight`: resulting physical fundamental-QNM matching obstruction.

Scratch `lake env lean` passed. Isolated exact-module `lake build` passed in 53.67 seconds, two jobs. No heartbeat or transparency changes, no axiom printing, no umbrella build. Umbrella import added. No general matching impossibility or RH theorem claimed.

Shared formal lint ran and reported a separate unreachable module, `ThetaCuspHawkingBMOnsetTransgressionHorizon`; it reported no error in this leaf. That separate module was not modified or imported by this work.
