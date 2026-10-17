# Constructed sharp coprime logarithmic Sobolev traces

- **ID:** coprime-logarithmic-sobolev-traces
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Every finite interior divisor trace has an explicitly constructed
  L2 physical velocity whose locally absolutely continuous logarithmic primitive
  attains weighted derivative energy twice the squared trace norm. Every competing
  L2 velocity has an exact comparison with explicit trace error and nonnegative
  interpolation defect.

## Exact theorem

For amplitudes a, divisor D≥2, and cutoff N, set w(j)=a(j) when 0<j<N and
D divides j, zero otherwise. Define Q(t)=Σ_{j<N}(w(j+1)−w(j))1_(j,j+1](t),
F(t)=∫₀ᵗQ, and f(x)=F(exp x). Then Q belongs to L2, F(j)=w(j) for 0≤j≤N,
f is locally absolutely continuous, and its actual derivative satisfies

    ∫₀^(log(N+1))exp(−x)|f'(x)|²dx = 2Σ_{j<N}w(j)².

For every other physical L2 velocity q, write Fq(t)=∫₀ᵗq,
sj=w(j+2)−w(j+1), ej=Fq(j+2)−Fq(j+1)−sj. The exact identity is

    ∫₀^(log(N+1))exp(−x)|(Fq∘exp)'(x)|²dx
      = 2Σw² + 2Σsj ej + Σ∫_(j+1)^(j+2)(q−sj)².

It supplies the corrected lower bound without assuming away the trace error.
The constructed state attains the matching-trace minimum. It realizes arbitrary
amplitude at D when N=D+1. Actual L2 velocities also satisfy the nonlinear
additive-shear bound with the exact physical resistance b.

## Proof and audit

Dependency-closed paper proof:
`docs/reports/BiScaleUncertainty/CoprimeSobolevTrace.md`.
Detailed fact ledger:
`docs/reports/BiScaleUncertainty/ContinuumCoprimeShear-FACTS.md`, package 2.

Namespace: `GaloisForLFunctions.BiScaleUncertainty.SobolevShear`.

- `SobolevTraceEnergy.lean`: 13 public theorems.
- `CoprimeSobolevInterpolation.lean`: 20 public theorems.
- `SobolevLogarithmicTransport.lean`: 10 public theorems.
- `CoprimeLogSobolevCoercivity.lean`: 12 public theorems.

All four direct final Lean leaf checks exited 0 without diagnostics. All 55 public
theorem axiom reports use only `propext`, `Classical.choice`, `Quot.sound`, including
their private dependencies. Umbrella imports are present and indexes refreshed.
Global lint exited 1 for unrelated concurrent missing imports:
`InfiniteGridPolarRecovery` and `LogarithmicCompressionEnergy`.

## Significance and boundaries

One contribution to the 100-package goal. It constructs the rough states needed
for sharp finite coprime coercivity; the previous C1 layer excluded their derivative
jumps. Finite-element interpolation and the interval Dirichlet principle are
classical; no external novelty claim for those ingredients.

This is a homogeneous Dirichlet primitive construction. Global unweighted L2
mass, identification with Bessel-potential Sobolev spaces, a separate global
uniqueness theorem, infinite graph-domain admission, and unitary affine uncertainty
are outside the certified claim. The overarching goal stays active at 2/100.
