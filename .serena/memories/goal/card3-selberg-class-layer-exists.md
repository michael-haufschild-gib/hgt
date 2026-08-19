# Card 3 (cusp-spectrum-radius-law): the Selberg-class layer already exists

The card's "Confirmed absent: any Selberg-class structure, standard twist, or
Kaczorowski--Perelli continuation" is **stale**. As of 2026-08-19 the corpus has:

- `formal/GaloisForLFunctions/RHTower/SelbergClass/` (31 modules). `Basic.lean` carries
  `EntireFiniteOrder`, `SelbergAnalyticContinuation`, `SelbergGammaData`
  (`Q, rank, lambda, mu, rootNumber`, and `degree = 2∑λ`, `conductor = (2π)^d Q² ∏λ^{2λ}`,
  `internalShift`), and **`ExtendedSelbergClass`** with fields `coeff : ArithmeticFunction ℂ`,
  `coeff_ne_zero`, `lSeriesSummable`, `continuation`, `lSeries_eq_value`, `gammaData`,
  `functionalEquation` (codiscrete equality of the completed value with its reflection).
  Note there is NO `a(1) = 1` field — carry `F.coeff 1 ≠ 0` as a hypothesis.
- `formal/GaloisForLFunctions/SelbergClass/` (24 modules) = Kaczorowski--Perelli
  *Multiple standard twists*: `MultipleStandardTwistData`, damping parameter, joint holomorphy of
  the damped twist, termwise Mellin--Barnes, spectral data (1.4)–(1.9) with finite fibres and `Ξ`,
  normal-family bounds on the initial domain, uniqueness from the initial domain.

**The continuation is NOT yet proved** — those modules say so explicitly ("asserts no
meromorphic continuation"; "the sum–integral interchange ... is the next analytic obligation").
Another agent is actively building it. **Do not duplicate that folder.**

## What I own for card 3
`formal/GaloisForLFunctions/RHTower/SelbergCuspSpectrumRadius.lean` — the bridge from the
abstract shift-lattice layer (`HTGeometry/ShiftLattice*`, `PowerSeriesSingularRadius`,
`CuspGapUnconditionalInstances`) to `ExtendedSelbergClass`:
`exists_coeff_bound` (‖a(n)‖ ≤ C n², from `LSeriesSummable a 2` — the only new mathematics),
`theta`, `shiftCoeff`, `shiftSpectrum`, `summable_thetaTerm`, `analyticAt_theta`,
`hasSum_shiftLatticeExpansion`, `hadamardLimsup_shiftCoeff_le` (unconditional half),
`hadamardLimsup_shiftCoeff_eq`, `radius_shiftLattice_eq`, `infDist_zero_shiftSpectrum`,
`cuspConstant_eq`, `hadamardLimsup_shiftCoeff_cusp`.

## Remaining for card 3
Only the K–P continuation dichotomy: `Φ_F(s,·)` has no analytic extension past a boundary point of
`Spec(F)`, i.e. `F_α` entire off the spectrum and `ρ₀(α) ≠ 0` on it. For ζ (degree 1, conductor 1)
and for every `ZMod N` periodic family this is already fully proved in the corpus
(`RHTower/ZetaStandardTwistDichotomy`, `ZetaTwistCuspRadius`, `ZModLFunctionCuspRadius`), and for
non-negative coefficient families below the abscissa (`HTGeometry/NonnegThetaCuspGrowth`,
`CuspGapUnconditionalInstances`). The general-`d` case is the open item, and it lives in the other
agent's `SelbergClass/` folder.
