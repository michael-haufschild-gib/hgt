# TG — Parseval identity at the extremal line; Gaussian Cramér identity under RH

- **ID:** TG-BOHR-4
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean, unconditional; RH corollary)
- **Statement:** g(u) = e^{-(Θ−½)u/2}G(e^{-u}), c_ρ = ½Γ((ρ−½)/2)·[Re ρ = Θ].
  (a) Abstract Parseval: Σ‖c_q‖ < ∞ ⇒ window means of |Σ c_q e^{iμ_q u}|² → Σ_{μ_q=μ_q'} c_q c̄_q'.
  (b) g + S − K₀ → 0, 0-coefficient of S zero ⇒ T⁻¹∫₀^T g² → ‖K₀‖² + Re Σ_{μ_q=μ_q'} c_q c̄_q'.
  (c) Unconditional: T⁻¹∫₀^T g² → ‖[Θ=½]A(½)‖² + Re Σ_{Re ρ=Re ρ'=Θ, Im ρ=Im ρ'} c_ρ c̄_ρ'.
  (d) RH ⇒ T⁻¹∫₀^T G(e^{-u})² → ‖A(½)‖² + Re Σ_{Im ρ=Im ρ'} ½Γ((ρ−½)/2)·conj ½Γ((ρ'−½)/2) (Gaussian Cramér).

## Proof
(a) |S|² = pair series Σ c_q c̄_q' e^{i(μ_q−μ_q')u} (product of absolutely convergent series, conj of tsum),
then the window coefficient lemma at frequency 0 over ι×ι. (b) g² = |K₀ − S + r|²; cross terms with
r → 0 average to 0; means of S and S̄ → 0. (c) extremal decomposition. (d) Θ = ½, all copies extremal.

## Lean
`RHTower/GaussianWeightedGapExtremalParseval.lean` (306 lines), wired after GaussianWeightedGapExtremalBessel.
`tendsto_gaussianWindowAverage_mul_conj_tsum_cexp`, `tendsto_meanSquare_of_tendsto_add_tsum`,
`tendsto_extremalGap_meanSquare`, `tendsto_centralGap_meanSquare_of_riemannHypothesis`.
Build exit 0, no warnings; axioms [propext, Classical.choice, Quot.sound]. Slow-elaboration trap fixed by
explicit (f := …) (g := …) in `Summable.mul_norm` (implicit higher-order unification timed out).

## Reading
TG "matrix-complete E_base = Tr + residual" realized exactly at the extremal line with zero residual:
prime-side mean square = archimedean bias² + extremal zero Gram trace. Under RH the Gaussian prime gap's
mean square is A(½)² + Σ_γ m_γ²|½Γ(iγ/2)|², i.e. the bias dominates by a factor ~10^{10}.
