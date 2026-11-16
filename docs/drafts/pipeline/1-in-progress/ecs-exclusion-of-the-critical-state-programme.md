# Exclusion of the critical state (ECS)

- **ID:** ecs
- **Stage:** 1-in-progress
- **Type:** programme card (goal loop)
- **Source:** docs/reports/review-1511/obstacles-summary.md §2.18 ("the most likely route to a proof, as a research programme")
- **Statement:** make every exact property of the critical half-line state a Lean theorem (stages 1–4: probe kernel, zero side, (★), continuation, sign/decay laws, index law) and attack stage 5 (no state for the zeros of ζ).

## Goal
README: `formal/GaloisForLFunctions/ExclusionOfTheCriticalState/README.md` (Q1–Q9). Lean in
`formal/GaloisForLFunctions/ExclusionOfTheCriticalState/`, umbrella `ExclusionOfTheCriticalState.lean`.

## Gates
- [x] 0 → 1 in-progress: README draft, questions Q1–Q9
- [ ] 1 → 2 fully-proven: per conjecture below
- [ ] 2 → 3 formalized: per module

## Approach
Order: Q1 probe calculus (pole, prime, Gamma parts on `e_p`, Poisson integral of Re ψ) → probe kernel;
state's probe identity in prime coordinates; Q6 finite index law; Q2/Q3 zero side on the domain → (★);
Q5 sign law via Landau; Q4 decay law (divergent half). Stage 5 entry points: wall, collar, charges, difference equation.

## Conjecture ledger
- C1 (PROVED, Lean) probe kernel: `bareMixedEnergy_probe` = (D(p)+D(q))/(p+q), `probeSymbol_eq_logDeriv_xiCent`, zero side `bareMixedEnergy_probe_eq_zeroSide` (WeilsFormOnProbesIsTheCaratheodoryKernelOfXi). Q1 answered.
- C2 (PROVED, Lean) state equation on probes in prime coordinates: `criticalState_probeEquation` (TheStateEquationOnProbes).
- C3 (PROVED, Lean) holomorphic extension: `differentiableOn_laplace_of_sq`, `differentiableOn_stateGamma`, `differentiableOn_stateTail`, `stateEquation_ofReal_eq_zero`.
- C4 (PROVED, Lean) decay law, divergent half for zeros right of the line: `criticalState_not_integrable_of_zero`, `riemannHypothesis_or_criticalState_decay_ruler` (∫F²e^{-bu}<∞ ⇒ Re ρ ≤ (17-b)/2). Mechanism: cleared equation ζ(½+p)A(p)+LF(p)ζ'(½+p)=0 on Re p>max(0,8-b/2), Im p>0; residue of ζ'/ζ forces LF(ρ-½)=0, contradicting closed-RHP zero-freeness. No zero side, no explicit formula on the domain needed.
- C5 (PROVED, Lean) sign law: `criticalState_changes_sign_on_every_ray`, `riemannHypothesis_or_criticalState_changes_sign` (TheStateChangesSignOnEveryRay). Mechanism: one-signed tail ⇒ Landau (corpus IsAbscissa + Cauchy estimates) ⇒ abscissa ≤ -8 because the remainder (with (s-1)ζ(s) and dslope at ½) is holomorphic near the real segment ⇒ LF holomorphic on Re w > -8 ⇒ decay law gives all zeros on Re ≤ ½. Uses: no real zeros of ζ in (½,1) (fails for some prime-two deformations: real factor zeros).
- C4' (PROVED, Lean) general form `zero_re_le_of_laplace_holomorphic`: LF holomorphic on Re w > κ (κ ≤ -7) ⇒ Re ρ ≤ κ + 17/2.
- Note: b ≤ 16 via on-line zeros is weaker than C4 off RH (state exists only off RH) — not pursued.
- C6 (PROVED, Lean) finite index at every ratio: `exists_bound_orthonormal_nonpositive` (TheConfinedFormHasFiniteIndexAtEveryRatio). Mechanism: Q_R = Q_{2R} + (a(R)/2)W₈ bounds W₈ on the nonpositive cone; corpus compactness `exists_domain_limit_of_smooth_energy_limit`; greedy 1/2-separated sequence (`exists_seq_of_forall_finset_exists`). Q6 for ζ answered.
- Assessment: stage 5 ⇔ (★) has no solution ⇔ no eigenvector of the Cauchy matrix 1/(8+z'-z) of the zeros with negative eigenvalue; holds for every configuration without right zeros and fails for prime-two deformations; decay exponent of the state = PNT error exponent (barrier with PNT cancellation is circular).
- C7 (PROVED, Lean) residue law right of the line: `riemannHypothesis_or_criticalState_poles_at_zeros` (TheTransformOfTheStateHasPolesAtTheZeros).
- C8 (PROVED, Lean) Gamma pairing in Lévy form, holomorphic on Re p > -1/2: `levyGamma_eq_stateGamma`, `differentiableOn_levyGamma` (TheGammaPairingInLevyForm). Prime tail holomorphic on Re p > -4; continuation to Re w > -17/2 with a pole at every zero with Re ρ ≥ 1/2: `riemannHypothesis_or_criticalState_poles_across_line` (TheStateContinuesAcrossTheCriticalLine).
- C9 (PROVED, Lean) functional equation in Lévy form: `levySymbol_eq_neg_logDeriv` (2θ'(0)+g(p) = -(ζ'/ζ(1/2+p)+ζ'/ζ(1/2-p)) on |Re p|<1/2), `levyGamma_eq_reflected_euler` (TheGammaPairingIsTheFunctionalEquationOnTheStrip). Mechanism: Lévy–Khintchine of θ' on the line + identity theorem on the cleared product.
- C10 (PROVED, Lean) the state is meromorphic in the plane: `riemannHypothesis_or_criticalState_meromorphic` (holomorphic off ρ-17/2, residue law, pole for Re ρ ≥ 1/2, bounded on Re w ≤ -17/2-δ); left formula `stateMeromorphic_eq_left`: -a LF(w) = J+Ŝ+LF(1/2)/(w+15/2)+LF(-1/2)/(w+17/2) (TheTransformOfTheStateIsMeromorphicInThePlane). Mechanism: three remainders glued; left of the strip the Euler parts of reflected Gamma term and prime tail cancel.
- C11 (PROVED, Lean) zero-sum calculus: `zeroSum F p = Σ_z LF(z)(1/(p-z) - 1/(1-z))` converges absolutely off the zeros (`summable_zeroSum_term`), is holomorphic there, O(|p|²) on |Re p| ≥ 1, o(|p|) along the negative integers (`tendsto_zeroSum_div`); pole removal `zeroSum_eq_dividedSum_add`: Z = Δ + LF·ξ'/ξ with Δ (`dividedSum`) holomorphic on Re p > -2 and O(|p|²) (TheZeroSumOfAProfileConvergesAfterOneSubtraction).
- C12 (PROVED, Lean) growth: Γℝ'/Γℝ linear on Re s ≥ 1/2; Lévy pairing and regular part linear on Re p ≥ 0; state tail, head term, prime heads, left remainder bounded on their half-planes (ThePairingsOfAProfileWithAProbeGrowAtMostLinearly).
- C13 (PROVED, Lean) explicit formula on the domain against probes: `globalRemainder_sub_eq_zeroSum` (B F(p) - B F(1) = Z F(p) off the zeros, every F in the domain), two-point `globalRemainder_sub_eq_tsum`; (★) `criticalState_starEquation` (a(LF(w)-LF(v)) = -Σ_z LF(z)(1/(w+8-z) - 1/(v+8-z)), Re w, Re v > -4), `criticalState_zeroValues_cauchy`, `riemannHypothesis_or_criticalState_starEquation` (TheExplicitFormulaHoldsOnTheEnergyDomainAgainstProbes). Mechanism: defect E = B F(1) - B F + Z F has pole-free forms right of Re p = -1/2 (via (s-1)ζ = 2ξ/(sΓℝ)) and on -2 < Re p < 1/2 (reflected factor); glued entire, O(|p|²), E(1) = 0, o(|p|) on the negative axis ⇒ Liouville on dslope E 1. No ζ'/ζ bound in the strip. Q2 answered (against probes).
- C14 (PROVED, Lean) entire product: `differentiable_clearedRemainder` (ξ(½+p)·B F(p) is entire for every F of the domain), `stateXiProduct_eq_laplace`, `riemannHypothesis_or_criticalState_xi_mul_entire` (TheProductOfTheStateWithXiIsEntire). Entry point (iv).
- C15 (PROVED, Lean) left-end normalisation: `tendsto_zeroSum_left` (Z F(b) → -B F(1) as Re b → -∞), `criticalState_starEquation_normalised`, `criticalState_zeroValues_cauchy_normalised` (TheZeroSideIsNormalisedAtTheLeftEnd).
- C16 (PROVED, Lean) bounds off the zeros: `norm_zeroSum_le_of_dist`, `norm_globalRemainder_le_of_dist`, `norm_stateMeromorphic_le_of_re` (TheContinuationIsPolynomiallyBoundedOffTheZeros).
- C17 (PROVED, Lean) averaged decay law (Q4 convergent half, weak form): `exists_bound_averagedState` (zeros with Re z ≤ κ ⇒ |A(t)| ≤ C e^{-(8-κ')t} for κ' > κ), `criticalState_averaged_decay_beyond_barrier` (every β < 183001/24000), `riemannHypothesis_or_criticalState_averaged_decay` (TheAveragedStateDecaysAtTheRateOfTheZeros). Mechanism: Volterra–Laplace on the causal wedge, quartic symbol, Fourier inversion on Re w = 1, line shift to Re w = κ'-8 with C16.
- C18 (PROVED, Lean) two-line formula: `hasSum_zeroValues_two_lines` (F in the domain, H entire with |H(σ+it)| ≤ D(1+t²)⁻² on a ≤ σ ≤ b, a ≤ -1, 1 ≤ b: Σ_z LF(z)H(z) = (1/2π)(∫H·BF on Re p = b − ∫H·BF on Re p = a)), `criticalState_hasSum_zeroValues_two_lines` (TwoVerticalLinesCutOutTheZeroSeriesOfTheState). Mechanism: termwise integration of the zero sum, corpus `two_line_simple_pole_add_const`.
- C19 (PROVED, Lean) statement (b) in time form: `criticalState_hasSum_heated_zeroSeries` (Σ_z LF(z)e^{εz²−zT} = a(∫_{x>0}k_ε(x−T)F⁺ − ∫_{u<0}k_ε(u−T)e^{−8u}F), every ε > 0, T real), `criticalState_heatedState_add_zeroSeries_le` (T ≤ −4ε: remainder ≤ ‖F⁺e^{−x}‖₂·k_ε(T)) (TheZeroSeriesIsTheStateLeftOfTheWallAndThePrimeSideBeyond). F⁺ = e^{x}·leftContinuationDatum at c = 1. Mechanism: C18 with H = e^{εp²−pT}; Fubini + `integral_cexp_quadratic` turn each line integral into a heat average.
- C20 (PROVED, Lean) (b) as distributions: `criticalState_hasSum_zeroSeries_test` (ψ smooth of compact support, ψ̂(p) = ∫ψ(u)e^{−pu}du: Σ_z LF(z)ψ̂(z) = a(∫_{x>0}ψF⁺ − ∫ψe^{−8u}F)), `_left`, `_right`, and the explicit formula at the state `criticalState_hasSum_bareMixedEnergy` (G real smooth of compact support in u < 0: Σ_z LF(z)LG(−z) = bareMixedEnergy F G) (TheExplicitFormulaHoldsAtTheStateAgainstSmoothTests). Mechanism: C18 with H = ψ̂ (corpus `testTransform` decay of every order), Fourier inversion on each line (`integral_exp_mul_fourier_rescale`), Fubini; weak equation for the last statement. No singular part at the wall.
- Gap (Q4, unaveraged): ∫F²e^{-bu} < ∞ for b < 17 − 2Θ needs square-summability of the zero values LF(z) against the density log|z| of the zeros (the resolvents 1/(p − z) on a vertical line have a Gram matrix that loses one logarithm). No proof; no Lean statement assumes it.
- Next: C21 explicit formula at the state against every test of the domain with Gaussian summation (lim_{ε→0} Σ_z LF(z)LG(−z)e^{εz²} = bareMixedEnergy F G; G = F: the vector of zero values is negative, = −a·W₈); plan: Fubini Σ/∫ against C19, correlation limit via corpus `continuous_connesL2Translate`. Then: index law for ζ (start: `pontryagin_law`); stage 5 entry points (peers own wall mass, prime balance).

## Log
- 2026-11-16 — created; README draft written.
