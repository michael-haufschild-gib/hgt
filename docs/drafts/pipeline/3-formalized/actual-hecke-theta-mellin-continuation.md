# Actual Hecke theta Mellin continuation

- **ID:** actual-hecke-theta-mellin-continuation
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Hecke and class-field programme](../1-in-progress/hecke-l-functions-and-class-field-theory-2026-10-28.md), HL7
- **Statement:** The actual physical Hecke theta and its actual finite-Fourier trace-dual theta have continued Mellin transforms with an arithmetic functional equation and explicit zero-mode residues.

## Exact mathematics

Let `n=[K:ℚ]`, `k` be the actual parity degree, and `κ=n/2+k`. For every
nonzero integral ideal `b` coprime to the finite modulus, every actual ray
character, and every place profile `y`, the proved theta pair has weight `κ`
and nonzero scalar

`A(y)=exp(Σ mult(v)*y_v)/(N(𝔪.fin*b)*sqrt(|disc K|)) * (-i)^k`.

The continued Mellin transform equals the actual integral of physical theta
minus its actual zero mode for `Re z>κ`. It is holomorphic away from `0,κ`,
with residues `-cphysical` and `A(y)*cdual`. Its regular part is entire, and
its reflection is `Λ(κ-z)=A(y)*Λdual(z)`. Nonzero parity kills both zero modes
and makes the continuation entire. The exact affine change
`z=(n*s+k)/2` converts the reflection to `s ↦ 1-s`.

## Dependency-closed proof

Each theta kernel is jointly continuous in profile and Gaussian parameter.
Its norm decreases when the parameter increases. At a fixed positive `t`,
the already proved summable norm series at `t/2` majorizes the series on
`Ici(t/2)`. Uniform convergence gives continuity and local integrability.
The proved exponential tails imply decay faster than every power.

Positive field degree gives `κ>0`. Positivity of the actual ideal covolume
proves `A(y)≠0`. Exact real-power and complex-power normalization converts the
proved arithmetic Poisson formula into the reciprocal-parameter identity.
These actual results discharge every field of Mathlib's `WeakFEPair`; no
analytic interface or field is retained as a premise. Its proved Mellin
continuation theorem gives the stated conclusions.

## Lean declarations

[HeckeThetaHasMellinContinuation.lean](../../../../formal/GaloisForLFunctions/HeckeLFunctions/HeckeThetaHasMellinContinuation.lean)
contains:

- `continuousOn_heckeIdealTheta`, `continuousOn_heckeDualIdealTheta`
- `locallyIntegrableOn_heckeIdealTheta`, `locallyIntegrableOn_heckeDualIdealTheta`
- `heckeThetaMellinWeight`, `heckeThetaMellinScalar`, their positivity/nonvanishing
- `heckeThetaPoissonFactor_reciprocal`
- `heckeIdealTheta_isBigO_rpow`, `heckeDualIdealTheta_isBigO_rpow`
- `heckeThetaMellinPair`, `heckeThetaMellinRegularPart`
- `heckeThetaMellinContinuation`, `heckeDualThetaMellinContinuation`
- `differentiable_heckeThetaMellinRegularPart`
- `differentiableAt_heckeThetaMellinContinuation`
- `hasMellin_heckeIdealTheta`, `hasMellin_heckeDualIdealTheta`
- `heckeThetaMellinContinuation_functional_equation`
- `heckeThetaMellinContinuation_residue_zero`, `heckeThetaMellinContinuation_residue_weight`
- `differentiable_heckeThetaMellinContinuation_of_parity_ne_zero`
- `heckeThetaMellinArgument_one_sub`, `heckeThetaMellinContinuation_reflection`

The complete scratch passes. Seven transitive axiom audits contain only
`propext`, `Classical.choice`, and `Quot.sound`. The final direct
`lake --old env lean` source audit passes without warnings. The module is
wired into the Hecke umbrella; no umbrella was compiled. No proof limits
were raised. Completed scratches are removed. Its olean is built for
the written joint-continuity consumer.

## Scope still open

This is the actual **theta** Mellin continuation. Unit-domain averaging,
exact Gamma/ideal-series unfolding, cancellation of class-character residues,
primitive arithmetic Gauss evaluation, and the final Hecke L-function
continuation/functional equation remain open. HL6's real characters and all
class field theory remain open.
