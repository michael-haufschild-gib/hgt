# Suzuki first-moment critical-error classification

- **ID:** CCM-FU-FM-CE
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Statement:** Classify bounded central unit-Riesz source, hence linear Suzuki curvature first moment, as RH plus bounded square-root-normalized Chebyshev error on natural apertures.

## Goal
Kill or validate the proposed CCM-FU first-moment producer. Chain: central bound ↔ first-moment bound → triangular-curvature bound → RH.

## Facts
- `weightedFirstMomentLinearBound_iff_rh_and_psiRemainderSquareRootBounded` gives first moment ↔ `RH ∧ |ψ(M)-M|=O(√M)`.
- `integral_abs_xiPoissonHilbertKernel_eq_one`: odd exponential detector has scale-independent `L¹=1`.
- `xiPoissonHilbertKernelTransform_eq_multiplier`: multiplier is `-iTγ/(T²+γ²)`.
- `xiPoissonHilbertMultiplier_criticalPair`: a critical-line conjugate pair contributes the positive summable weight `2Tγ²/((T²+γ²)(1/4+γ²))`.
- `xiPoissonHilbertPhase_cofinally_unbounded`: complete multiplicity-aware response is cofinally unbounded; RvM gives mass `≫log T`, summability controls the infinite tail, recurrence aligns a finite head.
- Hardy–Littlewood gives `ψ(x)-x=Ω±(√x log log log x)`.

## Status
Classification and complete detector amplification are Lean-complete. Sole no-go gap: arithmetic explicit-formula transport from bounded normalized Chebyshev error through this kernel to its Xi response.
