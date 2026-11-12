# Critical power-comb Abel integrability detects RH

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Target:** A82; positive replacement for ordinary critical divergence.
- **Statement:** `LogarithmicAbelIntegrable (powerCombTail (1/2))` iff RH.
  Under these equivalent conditions the logarithmic Abel mean has a finite,
  explicitly determined limit.

## Candidate limit

Let `C=criticalPowerContactCoefficient` and
`B(s)=-ζ′/ζ(s+1/2)-ζ(s+1/2)`. Symmetry gives `logDeriv ξ(1/2)=0`;
the archimedean row formula gives `B(0)=C`, now verified in Lean.
The harmonic-contact symbol is then `ζ(s+1)(B(s)-B(0))`, with removable
value `B′(0)` at zero.

The exact critical comb decomposition has a convergent elementary
remainder with limit

`E = Σ criticalPowerTailArchimedeanError
     - 2 ∫₀¹ criticalPowerTailReferenceProfile
     + 2 powerTailPole(1/2) Re ζ(1/2)`.

Its candidate Abel limit is `E-2B′(0)`. No identification with a central
second derivative of ξ is asserted; interchanging the power-parameter
limit and the Abel limit has not been justified.

## Required connections

- Critical finite parts and harmonic decomposition: verified in the first
  five critical support modules.
- Central symmetry: `RHTower.logDeriv_xi_one_half` in
  `CompletedPrimeGammaMovingHankel`; archimedean value in
  `PowerTailArchimedeanMellinIntegral`. Their coefficient identity is now
  verified in `CriticalPowerContactCoefficientIsTheRealResidue`.
- RH to subpolynomial critical-contact and comb growth: exact equivalences
  now written in `CriticalPowerCombGrowthDetectsRH`, unverified. Weighted
  Möbius inversion remains valid at threshold zero; harmonic subtraction
  and the convergent elementary remainder preserve that threshold.
- Converse: `CriticalPowerContactAbelIntegrability` now writes literal
  contact holomorphy and its actual Dirichlet symbol. The shared
  `HolomorphicContactSymbolsExcludeInteriorZeros` supplies the pole
  obstruction. `CriticalPowerCombAbelIntegrabilityDetectsRH` writes the
  exact absolute-integrability equivalence. All unverified.
- Abel limit: `CriticalPowerContactAbelMean` now writes the actual mean
  of the harmonic contacts as `ζ(ε+1)(B(ε)-C)` under RH, for `0<ε<1/2`.
  It uses subpolynomial growth, not ordinary convergence. Verification pending.
  Its removable extension is `zetaResidueUnit(s+1) * dslope B 0 s`, with
  value `B′(0)` at zero. The convergent elementary remainder then supplies
  the proposed comb limit. The analytic extension is written in `CriticalPowerContactSymbolIsRegularAtZero`;
  the mean limit and comb limit are written in the two Abel capstones. All unverified.

The equivalence and finite Abel-limit chains are written but unverified.
No new contribution counted.
