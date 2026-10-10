# TG — the sign phase transition of the Gaussian prime gaps

- **ID:** TG-SGN-3
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean, unconditional; RH corollary)
- **Source:** TG-SGN-2 (abstract sign lemma), TG-BOHR-2 (germ expansion), TG-SGN-1, TG-BIAS-1
- **Statement:** G_σ(y) = Σ Λ(n)n^{-σ}e^{-yn²} − ∫₁^∞u^{-σ}e^{-yu²}du, Θ = sup Re ρ.
  (a) σ-germ: e^{-y}/(ρ−½) + E(y,ρ−σ) = e^{-y}(½−σ)/((ρ−½)(ρ−σ)) + ½Γ((ρ−σ)/2)y^{-(ρ−σ)/2} + O(y|ρ−½|^{-2}).
  (b) zeros ≤ θ, 0 < σ < θ, σ ≤ 1 ⇒ e^{-(θ−σ)u/2}G_σ(e^{-u}) + Σ_{Re ρ=θ}½Γ((ρ−σ)/2)e^{i(Im ρ/2)u} → 0.
  (c) a zero on Re ρ = Θ and 0 < σ < Θ ⇒ G_σ(e^{-u}) > εe^{(Θ−σ)u/2} and < −εe^{(Θ−σ)u/2} in every late window of length L.
  (d) RH ⇒ dense sign changes of G_σ for every σ ∈ (0,½) and G_σ eventually negative for every σ ∈ [½,2).

## Proof
(a) germ = e(½−σ)/((ρ−½)a) + [e/a + E(y,a)], a = ρ−σ, with the all-zeros germ expansion; |ρ−s| ≥ |Im ρ| ≥ |ρ−½|/(3/2).
(b) σ-expansion via the zero field at σ; the weight e^{-(θ−σ)u/2} kills the archimedean transform and the
bounded remainder; dominated convergence over zero copies. (c) Abstract sign lemma (TG-SGN-2) with
coefficient ½Γ((ρ₀−σ)/2)·mult(ρ₀) ≠ 0 at Im ρ₀/2 and 0 at frequency 0. (d) Θ = ½ is attained under RH;
σ = ½ is TG-BIAS-1; σ > ½ is TG-SGN-1 with the Γ-current bound.

## Lean
`RHTower/GaussianGapSignPhaseTransition.lean` (513 lines), wired after GaussianCentralGapExtremalSignChanges.
Key: `norm_sigmaZeroGerm_sub_le`, `sigmaGap_eq_archimedean_sub_zeroSeries`,
`tendsto_sigmaWeightedGap_add_extremalSeries`, `exists_dense_sign_changes_sigmaGap_of_extremal_zero`,
`riemannHypothesis_sign_phase_transition`. Build exit 0, no warnings; axioms [propext, Classical.choice, Quot.sound].

## Reading
TG sign-change integer as a function of σ: under RH it jumps at σ = ½ from linear growth (σ < ½, Littlewood/
Kaczorowski-type with explicit amplitude e^{(½−σ)u/2}) to zero (σ ≥ ½: complete archimedean bias at ½,
negative limit A(σ) − ξ'/ξ(σ) above). Unconditionally the jump sits at an attained Θ; residual: unattained Θ.
