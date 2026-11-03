# F2 — sharp order of the Cauchy reflection factor

- **Stage:** 1-in-progress
- **Question:** Does Cauchy averaging preserve a bounded arithmetic reflection on one fixed Haar space throughout the parameter strip?
- **Source:** The literal core transform law in `MayerScattering/ArithmeticMellinReflection`.
- **Target:** Exact Gamma norm, frequency order, sharp boundedness boundary and the surviving physical domain.

## Candidate classification

For `0<Re s<1/2`, let `s♯=1/2−conjugate(s)`, `a_s(t)=symbol(2s,it)/Γℝ(2s)` and `B_s(t)=a_(s♯)(t)/conjugate(a_s(t))`. These factors are defined without the resonance equation.

Put `a=Re s+1/2`, `b=1−Re s`, `τ=Im s−t/2`, and

`C(s)=|Γℝ(2s)Γ(s+1/2)| / |Γℝ(2s♯)Γ(s♯+1/2)| > 0`.

Then cancellation of the common Cauchy Gamma factor gives

`|B_s(t)|=C(s)|Γ(b+iτ)|/|Γ(a+iτ)|`.

For `b≤a`, the vertical Gamma-ratio inequality gives the exact maximum at `τ=0`. The Gamma-ratio asymptotic gives

`|B_s(2(Im s−τ))| τ^(2 Re s−1/2) → C(s)`.

Consequently the factor is bounded exactly when `Re s≥1/4`, and both spectral directions are bounded exactly when `Re s=1/4`. A bounded multiplier family throughout the full strip is therefore impossible in this realization. This statement concerns these Mellin multipliers, not all possible Mayer intertwiners. The normalized-field antiunitary and the exact order remain positive survivors; Krein positivity remains open.

## Gates

- [ ] Verify the exact norm identity and asymptotic in Lean.
- [ ] Verify sharp one-sided and two-sided boundedness classification.
- [ ] Distinguish frequency boundedness from any stronger claim about physical operators.
- [ ] Record the positive survivor and audit the final module.
