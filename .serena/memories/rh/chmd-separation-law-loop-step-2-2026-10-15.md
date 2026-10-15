# CHMD loop step 2: spectral-realisation gate and the Klein–Gordon separation law (2026-10-15, MUST-1530)

Module `formal/GaloisForLFunctions/RHTower/CHMDKleinGordonSeparationLawAndApproximateRealisation.lean`
(namespace `RHTower.CHMDSeparationLaw`; imports `CHMDGrowthPositivityCollapseAndTwoPointCriterion`; wired; standard axioms).

Question tested: "name the input that passes Wall 1" for the one-sided bound `φ_Λ(u) ≤ φ_Λ(0)` on the CHMD causal wave.
Gate for spectral-realisation candidates: density `(1/2π) log R`, prime dependence not trace-class. All known classes die:
manifold Laplacians (Weyl law), quantum-graph/Berry–Keating prime-length models (CANNOT-546), trace-class prime perturbations
(CANNOT-549), adele/absorption models (trace-form positivity = RH, Wall 12). Mechanism kills in KG coordinates: Λ ≥ 0 with a
positive kernel only at mass 0 (pole exponent ½); imaginary KG time positivity-preserving but blind; twisted-arc annihilation =
mean-periodicity with complex spectrum (null face); KG energy conserved only for the spatial wave; Herglotz/positive-real = receiver.

Survivor (Lean): `sqrt_seven_fourths_lt_re_kgFreq` (`Re √(γ²+2) > √(7/4)` strictly), `kgPoleSet_subset`
(poles in `{√(7/4) < |Im s|, |Re s| < ½}`), `analyticAt_kgPoleSeries_of_abs_im_le` (analytic on `|Im s| ≤ √(7/4)`),
`integral_polePartWave_mul_cexp` (`∫₀^∞ P(u)e^{−su}du = (2/cos²¼) s/(s²+7/4)`, poles ON the separation line),
`not_analyticAt_kgPoleSeries_sub_poleLaplace` (the prime side carries ζ's pole), `riemannHypothesis_of_eq_add_of_le_zero_value`
(approximate unitary realisation with bounded defect suffices). Wall 6 in KG coordinates = the strip below the first possible pole.

Next requirement: unitary realisation of the KG prime wave with bounded defect, density `(1/2π) log R`, non-trace-class prime part.
Other agent's `CHMDStage22PrimeWaveGrowthLawAndTwoPointSumCriterion` imports the growth module (pole/arch/prime wave decomposition).

Lean traps this step: `analyticAt_const.mul h` needs the target lambda ascribed (Pi-sub form otherwise); `sub_sub_cancel` +
`inv_mul_cancel_left₀`; `linear_combination` with `Complex.I_sq` for `(s−Ia)(s+Ia) = s²+a²`; keep `push_cast` away from
`Real.cos (1/4)` (it unfolds to exponentials) — rewrite with `← hc` first; strictness of a blow-up bound needs `1/(12M)`, not `1/(6M)`.
