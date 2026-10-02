# Actual Gamma admission and matched odd physical decay

- **ID:** sz-matched-odd-physical-decay
- **Stage:** 3-formalized
- **Route:** SZ
- **Type:** POSITIVE
- **Date:** 2026-10-02

## Exact new theorem

`eventually_suzukiTaMatchedOdd_physical_mass_decay` proves, without any
source, regularity, tail, or response hypothesis:

```lean
∃ C : ℝ, 0 < C ∧ ∀ᶠ a : ℝ in atTop, ∀ ha : 0 < a,
  ‖suzukiTaPhysicalEmbedding ⟨a, ha⟩
    (suzukiTaRawCoalescingOdd ⟨a, ha⟩ (1 / 2))‖ ^ 2 ≤
      C * a * Real.exp (-a)
```

This concerns the literal matched source at anchor 1/2, the actual Gamma
form, complete prime/polar remainder, and prescribed interval shift.
It closes the selected physical-decay gap after the uniform odd-energy
bound. It is not an unconditional RH proof.

## Dependency-closed paper proof

For any certified finite-exponential source f with budget V, split its
Fourier energy at R>=1. Plancherel controls the central band; the certified
envelope V/(pi*abs(xi)) controls both tails. The exact primitive
-(log(x)+2)/x gives

    integral_R^infinity (1+log(x))/x^2 dx = (log(R)+2)/R.

Thus the logarithmic Fourier density is integrable and

    Hlog(f) <= (1+log(R))*norm(f)^2
               +2*V^2*(log(R)+2)/(pi^2*R).

The exact Gamma weight is at most C_arch times this logarithmic weight.
Construct the weighted Fourier L2 vector from that integrability. Its
inverse Fourier transform is f itself, so f's actual aperture support
places the constructed vector in the support-defect kernel. This proves
actual Gamma admission and the same quantitative bound for one lift at
every R; it assumes no form-domain membership of f.

Let C0=2*(norm(kappa)+46), c the prescribed shift, p the matched odd source,
H=B/c, and n=ceil(a). Preserve the decay in the proved source recurrence:

    norm(H^n p) <= R0*exp(-7a/2),
    sum_{j<n} norm(H^j p) <= M*exp(a/2).

The literal u=c^(-1)*sum_{j<n}(-1)^j H^j p has residual
r=p-(cI+B)u=(-1)^n H^n p and certified budget
V=C0^n*exp(a/2)/c. Since exp(a)<=2c,
norm(u)<=2M*exp(-a/2). For K=2log(C0)+10 and R=exp(K*a),
V^2/R<=4C0^2*exp(-a). The logarithmic estimate constructs g with
Jg=u and norm(g)_Gamma^2<=D*a*exp(-a), eventually.

For the actual matched odd Riesz response w, put z=w-FromForm(g).
The exact weak source pairing and full form identity give

    norm(z)_Ta^2 = Re<r,Jz> - Re<g,ToForm(z)>_Gamma.

The actual decomposition pays both the Gamma norm and physical norm,
because cI+B>=I. Cauchy--Schwarz gives norm(z)_Ta<=norm(r)+norm(g)_Gamma.
The Gamma embedding is contractive. Consequently

    norm(Jw)^2 <= 2*norm(r)^2 + 8*norm(g)_Gamma^2.

Insert the constructed residual and Gamma bounds to prove the root.

## Lean certificate

Final foreground leaf audits passed without warnings:

- CCMFiniteExponentialLogEnergy, audit4687.
- CCMFiniteExponentialFormLift, audit84631.
- CCMRestrictedWeilFiniteNeumannSource, strengthened audit56559.
- CCMFiniteNeumannFormDecay, audit13151.
- SuzukiMatchedOddSourceBound, strengthened audit54388.

Every final command used `lake --old env lean <leaf> -o <leaf.olean>`.
Three new leaves are wired into RHTower. Existing two leaf imports remain.
No umbrella or full build was run.

- Axiom audit45262 passed for all fourteen public theorems across these five
  leaves. Every query reports only `propext`, `Classical.choice`, `Quot.sound`.
  The printed root statement confirms no unproved hypothesis binders.
- Formal lint17821 exits1 on eleven unrelated unreachable modules:
  CCMApertureChainProfile, CCMApertureTranslationChains,
  CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation,
  CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower,
  MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines,
  ThetaConfluentCoordinateCurrent, ThetaMovingShellFirstOrderPhase,
  ZetaZeroDensityPowerSaving. None of the five audited leaves is flagged.
  Global lint remains non-green; unrelated work is preserved.
- No added axioms, subagents, numerical experiments, heartbeat increases,
  full/umbrella builds, commits or pushes.

## Remaining hard frontier

The complete signed shell/metric Wronskian is still uncontrolled. Physical
decay alone does not pay multiplication by the exponential shift, nor
does it supply canonical normalization, shift removal or Xi identification.

The next source-based paper conjecture is uniform growing physical
coercivity, followed by rescaled response-minus-Neumann error, in
`../1-in-progress/sz-growing-physical-coercivity.md`. The proof mechanism
combines low-band cancellation, the full-line norm bound, and the high-band
Gamma penalty; it does not assume a new spectral hypothesis. RH remains open.
