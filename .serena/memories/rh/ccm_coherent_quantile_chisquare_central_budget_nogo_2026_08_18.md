# CCM coherent quantile chi-square central-budget no-go (2026-08-18)

[LOCAL-RESEARCH][LEAN-PROVED] Proposed Route-O sufficient condition
2 Chi_coh(T,N,f) <= (2 gammaHardyPhaseRate(0)+4)||f||^2
is sign-impossible for every nonzero f, hence eventually false on canonical actual Gamma-Slepian heads.

Gauss quarter-digamma identity yields
gammaHardyPhaseRate(0)=-(3 log 2 + gamma_E + pi/2)/2 - log pi/2,
so 2 gammaHardyPhaseRate(0)+4 = 4-gamma_E-3 log 2-pi/2-log pi < 0.
Strict sign is symbolic from gamma_E>1/2, log 2>0.6931471803, pi>3, log pi>0.
Since `ccmActualHeadCoherentQuantileGammaChiSquare_nonneg`, no nonzero vector can satisfy proposed bound.
Canonical heads are eventually physically nonzero because they converge to nonzero exact restricted-Weil ground.

Formal leaf: `formal/GaloisForLFunctions/RHTower/CCMActualHeadCoherentQuantileGammaNoGo.lean`.
Wired into `formal/GaloisForLFunctions/RHTower.lean`.
Exact leaf source check and `lake build GaloisForLFunctions.RHTower.CCMActualHeadCoherentQuantileGammaNoGo` pass.
Theorem axioms only `propext`, `Classical.choice`, `Quot.sound`.

Key theorems:
- `gammaHardyPhaseRate_zero_closed`
- `two_gammaHardyPhaseRate_zero_add_four_neg`
- `not_coherentChiSquare_le_centralBudget_of_ne_zero`
- `eventually_ccmRestrictedWeilCanonicalGroundHead_physical_ne_zero`
- `eventually_not_ccmRestrictedWeilCanonicalGroundHead_coherentChiSquare_le_centralBudget`

[FALSIFIED] Separate nonnegative coherent-field norm cost cannot close Route O.
Weighted Cauchy-Schwarz preserves prime/terminal autocorrelations inside Chi_coh but destroys phase between Gamma translation increment and coherent field, leaving an already-negative scalar budget before subtracting 2 Chi_coh.

[POSITIVE SURVIVOR / OPEN CORE] Sign joint block directly, cofinally on canonical heads:
H_Gamma(f)+2 C_completed,coh(f) >= -(2 gammaHardyPhaseRate(0)+4)||f||^2.
This is exact source nonnegativity in common-clock normal form and must preserve increment-field phase.