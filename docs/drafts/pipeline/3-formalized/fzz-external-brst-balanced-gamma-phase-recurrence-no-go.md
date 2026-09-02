# FZZ external-BRST balanced Gamma phase recurrence no-go

- **ID:** FZZ-BRST-GAMMA-RECURRENCE-NOGO
- **Stage:** 3-formalized
- **Status:** `[LEAN-CLOSED]`
- **Source:** `rh-current-frontier-map.md` · FZZ-P external-BRST open mechanism
- **Proof chain killed:** `balanced external-BRST two-point amplitude → replica-area passivity → Mellin completeness → RH`

## Frontier

- `[CORPUS]` `fzzHJExternalGammaPlusNormalization`, `fzzHJExternalGammaMinusNormalization`, and exact passivity classification are formal.
- `[CORPUS]` `gammaVerticalValue_eq_norm_mul_exp_phase` gives a continuous Gamma phase lift; `tendsto_gammaVerticalPhase_ratio` proves growth `T log T`.
- `[LITERATURE]` Exact cigar reflection coefficients are Gamma ratios and continuum scattering data are phases; no source found stating cofinal return of the HJ balanced amplitude or its FZZ-P passivity no-go.

## Theorem

At physical level `k=4`, let

`A(P)=N₊(4,P)N₋(4,P)`.

For every real `M`, some `P>M` satisfies `A(P)=A(0)=1`. Consequently no predicate of the complete pointwise amplitude `A(P)` is equivalent for every `P` to linear replica-area passivity.

Lean certificate: `fzzHJBalancedExternalGammaAmplitudeRouteKilled` in
`GaloisForLFunctions.RHTower.FZZCigarParityExternalBRSTBalancedGammaPhaseRecurrenceNoGo`.

## Proof

Write `y=√2 P`, `z=1/2+iy`. Gamma recurrence gives

`A(P)=F(y)/conj(F(y))`,

`F(y)=Γ(z+2)Γ(z-2)=Γ(z)^2 z(z+1)/((z-1)(z-2))`.

Since `z-1=-conj(z)` and `z-2=-conj(z+1)`, define

`α(y)=atan(2y)+atan(2y/3)`.

The exact polar identity is

`A(P)=exp(i θ(y))`, `θ(y)=4(γPhase(1/2,y)+α(y))`.

Here `θ(0)=0`, `α` is bounded, and corpus asymptotics give `γPhase(1/2,y)/(y log y)→1`; hence `θ(y)→+∞`. Given `Y`, choose a positive integer `n` with `θ(Y)<2πn`, then choose `T>Y` with `2πn<θ(T)`. Continuity and the intermediate value theorem give `y∈(Y,T)` with `θ(y)=2πn`, so `A(y/√2)=1` cofinally.

At `P=0`, linear replica-area response is passive. At every recurrent `P≠0`, corpus passivity classification says it is nonpassive. Equal complete amplitudes therefore have opposite passivity truth values; no pointwise amplitude predicate can supply the missing Ward arrow.

## Hostile audit

Verdict: `LEAN-CLOSED`. Underlying Gamma phase growth and unitary cigar scattering are known; cofinal exact recurrence plus amplitude-only FZZ-P no-go was not found in corpus or primary literature. Exact scope excludes unwrapped phase history, Wigner--Smith derivative, higher-point integrated kernels, and modulus-to-area Ward coupling.

## Positive survivor

Charge-balanced amplitude value forgets winding number of its lifted phase. Any surviving external-BRST producer must retain unwrapped phase/Wigner--Smith history or couple higher-point integrated source data directly to marked area response.
