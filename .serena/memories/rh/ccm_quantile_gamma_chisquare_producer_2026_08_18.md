# CCM quantile Γ chi-square producer (2026-08-18)

New module: `formal/GaloisForLFunctions/RHTower/CCMActualHeadQuantileGammaChiSquareProducer.lean`, wired in `formal/GaloisForLFunctions/RHTower.lean`.

Scientific advance:
- Proved actual-head autocorrelation displacement bound
  `|C_f(h)-C_f(s)| ≤ ‖f‖ sqrt(E_f(h-s))`.
- Proved higher Binet Γ energy is the real integral on CCM form-domain heads, and its symmetric whole-line form is twice the positive-half-line energy.
- Identified explicit continuous reciprocal
  `γ_hi(h)⁻¹ = exp(h/2)(exp(2h)-1)` for h>0.
- Defined literal displaced quantile density `ρ_N` by pushing each exact prime/polar quantile cell by `log n`; cells overlap before squaring.
- Defined source-only cost
  `A_N = ∫ ρ_N(r)^2 exp(|r|/2)(exp(2|r|)-1) dr`.
- Proved weighted Cauchy–Schwarz and completed square:
  `H_Γ(f)+2 S_N(f) ≥ -2 A_N ‖f‖²`.
- Proved unconditional terminal completed-error bound with exact mismatch
  `ε(T)=|E_completed(T)-2(1-exp(-T/2))|`.
- Final theorem:
  `ccmRestrictedWeilSourceQuadratic_ge_signedGammaQuantileProducer`:
  `Q_a(u) ≥ (2γ₀+4-2ε(2a)-2A_N)‖f‖²`,
  `N=floor(exp(2a))+1`.
This preserves prior prime–polar–first-Γ cancellation and uses actual CCM head autocorrelations; no common-clock/Slepian bridge.

Verification:
- direct `lake env lean GaloisForLFunctions/RHTower/CCMActualHeadQuantileGammaChiSquareProducer.lean` passes;
- targeted `lake build GaloisForLFunctions.RHTower.CCMActualHeadQuantileGammaChiSquareProducer` passes;
- key axiom audit uses only `propext, Classical.choice, Quot.sound`;
- no forbidden declarations; umbrella import line 996.
- Route map was not edited.

New exact open core:
prove cofinally
`A_N + ε(2a) ≤ γ₀+2-δ/2`
(or a sharper equivalent) for the literal finite heads. This is now the source-relative arithmetic producer needed for Route O; no operator bridge remains in this step.