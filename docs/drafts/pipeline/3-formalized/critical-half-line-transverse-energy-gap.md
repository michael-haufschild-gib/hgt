# Critical half-line transverse energy gap

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Target:** B104; stability of the actual critical state and control of neutral variations.
- **Statement:** At a finite global threshold, the critical energy controls the eighth-exponential mass on the ordinary-L² orthogonal complement of its unique ground state.
- **Status:** Lean verified; contribution 4.

## Corpus connection

`exists_strong_negative_limit_of_bounded_weilQuad` extracts strong limits of smooth normalized profiles with bounded exponential mass and Weil energy. `criticalHalfLineFullEnergy_zero_eq_laplace_ratio_ae` identifies the entire zero-energy line. The proposed bridge is a compactness argument for almost-zero critical-energy profiles, including the actual measurable energy domain.

## Paper proof

Write `m(G)=∫G²`, `W(G)=∫G²exp(-8u)`, `S(G)=∫G²exp(2|u|)`, and `a=criticalAliasCoefficient W₀>0`. All profiles below vanish on `[0,∞)`.

The weighted prime bound gives `|P(G)|≤2VS(G)`. Weighted Cauchy–Schwarz gives `sinhHalfMoment(G)²≤JS(G)`, where `J=∫exp(-|u|)`. The Gamma lower bound and Plancherel give `arch(G)≥-Dm(G)`, with `D=10+log4`. Therefore `E(G)≥aW(G)-CS(G)-Dm(G)`, where `C=2V+2J≥0`. For every `Y≥0`, the corpus estimate gives `S(G)≤exp(2Y)m(G)+exp(-6Y)W(G)`. Choose `Y` so `Cexp(-6Y)≤a/2`. Then

`E(G) ≥ (a/2)W(G) - Bm(G)` for a fixed `B≥0`. (1)

Suppose no positive ordinary-L² gap exists on the orthogonal complement of the normalized critical state `F`. Choose domain profiles `G_n` with `m(G_n)=1`, `∫FG_n=0`, and `0≤E(G_n)≤1/n`. Equation (1) bounds `W(G_n)` uniformly.

The one-sided recovery theorem supplies smooth compact profiles `H_n`, supported on the negative half-line, with `m(H_n)≤1`, `∫(H_n-G_n)²→0`, uniformly bounded `W(H_n)`, and `E(H_n)→0`. Indeed, its Gamma upper error tends to zero, prime and pole terms converge in `S`, and its exponential mass is bounded above by `exp(8/k)W(G_n)`; choose the recovery index separately for each `n`. Full-form nonnegativity supplies the lower bound on `E(H_n)`.

Their Weil forms are bounded above because `weilQuad(H_n)=E(H_n)-aW(H_n)≤E(H_n)`. Strong compactness gives a subsequence converging to `H` in L² and L¹, with `m(H)=1`, finite `W(H)`, and negative support. Weighted interpolation gives convergence in `S`, hence convergence of the prime and pole terms. Every fixed Gamma truncation converges by the L¹ limit. Fatou for the positive exponential mass then gives

`truncatedWeilForm(H,T)+aW(H)≤0` for every `T≥exp(G₀)`.

Thus `H` is an actual critical ground state. L² convergence preserves `∫FH=0`, while uniqueness gives `H=±F` almost everywhere, a contradiction. Consequently `E(G)≥δm(G)` on `F⊥` for some `δ>0`.

Combining this with (1) yields

`E(G) ≥ [aδ/(2(B+δ))]W(G)` on `F⊥`.

The polar source pairing is continuous in `S`, and `S≤W` on the negative half-line. Hence it is energy-continuous on `F⊥`. This controls neutral variations but does not decide its value on `F`.

More explicitly, put `N_F(G)=G-⟨F,G⟩F`. The actual weak equation gives `E(N_F(G))=E(G)`, and normalization gives `N_F(G)⊥F`. Thus, for constants `γ>0` and `K≥0`, every domain profile satisfies

`γW(N_F(G))≤E(G)` and `|P(G)-⟨F,G⟩P(F)|²≤K E(G)`,

where `P(G)=∫G·polarSourceProfile`. The only uncontrolled polar component is the single scalar `P(F)`.

The wall-trace conjecture remains open; no boundary regularity or polar nonvanishing is assumed here.

## Lean declarations

Module: `ArithmeticHodgeTheoryOfDegenerations/CausalReflection/CriticalHalfLineEnergyGap.lean`.

- `criticalHalfLineFullEnergy_coercive_remainder`: full-domain exponential coercivity up to ordinary square mass.
- `exists_window_energy_recovery`: smooth one-sided recovery of full-domain profiles.
- `exists_groundState_of_smooth_energy_limit`: compactness identifies normalized vanishing-energy limits as actual ground states.
- `criticalHalfLineFullEnergy_transverse_exponential_gap`: positive exponential gap on the ordinary-L² orthogonal complement.
- `criticalHalfLineFullEnergy_controls_neutralPart`: quantitative weighted distance to the ground-state line.
- `criticalHalfLine_polar_residual_energy_bound`: polar pairing error bounded by energy.
- `riemannHypothesis_or_exists_stable_criticalHalfLineGroundState`: unconditional specialization, with every analytic input discharged.

Final audit: `lake --old env lean GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/CriticalHalfLineEnergyGap.lean` passed without warnings. The audited declarations depend exactly on `propext`, `Classical.choice`, and `Quot.sound`.
