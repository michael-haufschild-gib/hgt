# Uniform actual odd-source energy on route SZ

- **ID:** sz-matched-odd-source-bound
- **Stage:** 3-formalized
- **Type:** POSITIVE
- **Date:** 2026-10-02
- **Route:** SZ

## Exact new theorem

`exists_suzukiTaCoalescingOddEnergy_half_uniform_bound` proves

```lean
∃ C : ℝ, 0 < C ∧ ∀ a : SuzukiPositiveAperture,
  suzukiTaCoalescingOddEnergy a (1 / 2) ≤ C
```

This is Suzuki's literal unscaled odd covariance energy, with the actual
prime--polar--Gamma form and the prescribed interval norm shift. The
theorem has no hypothesis binders. It closes the previously open matched
odd-source energy target; RH is not proved.

## Dependency-closed paper proof

Put `D=norm(kappa)+46`, `C0=2D`, `L=4D/pi`, `q=exp(-4)` and
`K=2log(C0)+10`. The proved actual-source recurrence, together with
`norm(p)<=exp(a/2)`, gives

`norm(H^j p)<=q^j*exp(a/2)+eta*C0^j`,
where `eta=L*exp(a/2)/sqrt(exp(K*a))` and `H=B/c` is the actual operator.
For `n=ceil(a)`, `q^n*exp(a/2)<=1` and `eta*C0^n<=L*C0`.
The two finite geometric sums give constants `M,R>0`, independent of
aperture, with `norm(H^n p)<=R` and
`sum_{j<n} norm(H^j p)<=M*exp(a/2)` eventually.

The literal finite vector `u=c^(-1)*sum_{j<n}(-1)^j H^j p` has
`norm(u)<=M*exp(a/2)/c` and exact residual
`p-(cI+B)u=(-1)^n H^n p`. No infinite Neumann limit is used.

Transport the interval sinh source at `1/2` through the existing unitary
to `p=(p_+-p_-)/2`. For the actual odd Riesz response `w`, let `f=Jw`
and `E=norm(w)^2`. The exact source identity gives `E=Re<p,f>`.
The actual energy decomposition is
`E=norm(w)_Gamma^2+Re<(cI+B)f,f>`, with `cI+B>=I`.
Positivity on `f-u`, self-adjointness and Cauchy--Schwarz yield

`E<=2c*norm(u)^2+2norm(p-(cI+B)u)*norm(w)`.

The proved `exp(a)<=2c` therefore gives
`E<=4M^2+2R*sqrt(E)`, hence `E<=8M^2+4R^2` after absorption.
The separate unconditional bound `E<=exp(a)` covers every remaining
bounded aperture range, without a continuity assumption on moving spaces.
The physical test vector `u` need not belong to the Gamma form domain.

## Lean certificate

- `CCMRestrictedWeilFiniteNeumannSource.lean`: final direct leaf audit34076
  passed, no warnings; three public theorems, two literal definitions.
- `SuzukiMatchedOddSourceBound.lean`: final direct leaf audit87048
  passed, no warnings; two public theorems, including the premise-free root.
- Both leaves are wired into `GaloisForLFunctions/RHTower.lean`.
- All five public axiom queries passed in audit29754. Each uses only
  `propext`, `Classical.choice` and `Quot.sound`. The root's printed
  statement confirms no hypothesis binders.
- Formal lint38433 exits1 on twelve unrelated unreachable modules:
  CCMApertureChainProfile, CCMApertureTranslationChains,
  CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation,
  CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower,
  MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines,
  SoninPrimeSquareCorrectionNuclear, ThetaMovingShellFirstOrderPhase,
  ThetaTailConfluentCenterGram, ZetaZeroDensityPowerSaving.
  Neither new leaf is reported. Global lint is not green; unrelated work
  is preserved. Targeted tracked-file whitespace check passes.
- No subagents, numerical experiments, full builds, umbrella builds,
  heartbeat increases, added axioms, commits or pushes.

## Remaining hard frontier

Gamma form-domain admission, logarithmic Fourier energy decay for the
actual finite Neumann vector, and matched physical mass O(a*exp(-a)) are
now Lean-closed; see `sz-matched-odd-physical-decay.md`. The next concrete
source-based target is growing physical coercivity and rescaled response
error in `../1-in-progress/sz-growing-physical-coercivity.md`.

Uniform matched energies alone do not control the complete signed
Wronskian/cusp cancellation, canonical V2 normalization, shift removal,
or Xi identification. These remain open, as does RH.
