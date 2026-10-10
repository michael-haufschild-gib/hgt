# TG — the extremal Bohr spectrum of the Gaussian prime gap (unconditional)

- **ID:** TG-BOHR-2
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean, unconditional, no hypothesis on zeros)
- **Source:** TG-BOHR-1 (window-average calculus), TG-SGN-1 (zero abscissa Θ), TG-EXP-1 (germ bound)
- **Statement:** G(y) = Σ Λ(n)n^{-1/2}e^{-yn²} − ∫₁^∞u^{-1/2}e^{-yu²}du, Θ = sup Re ρ.
  (a) Germ expansion for every zero: Re a > −2, a ≠ 0 ⇒ ‖e^{-y}/a + E(y,a) − ½Γ(a/2)y^{-a/2}‖ ≤ (2y+2y²)/(|a||a+2|).
  (b) G(y) = A_y(½) − Σ_ρ ½Γ((ρ−½)/2)y^{-(ρ−½)/2} − O(y), Σ_ρ |Γ((ρ−½)/2)| < ∞ (unconditional).
  (c) zeros ≤ θ ⇒ ∀τ: T⁻¹∫₀^T e^{-(θ−½)u/2}G(e^{-u})e^{-iτu}du → A(½)[θ=½∧τ=0] − Σ_{Re ρ=θ, Im ρ=2τ}½Γ((ρ−½)/2).
  (d) At θ = Θ this holds with no hypothesis; the coefficient at τ is nonzero iff ξ(θ + 2iτ) = 0.
  (e) ∃τ, θ-weighted coefficient ≠ 0 ⟺ ξ has a zero on Re ρ = θ.

## Proof
(a) Two recursion steps + Gamma form with Re(a+4) > 2. (b) Zero field at σ = ½; amplitude summability
from y = 1 via the exponent-law germ bound. (c) Weighted terms e^{(a−(θ−½))u/2}: on Re ρ = θ they are
characters e^{i(Im ρ/2)u}; strictly left they decay, dominated by ‖½Γ‖; window-average calculus of
TG-BOHR-1. (d),(e) Coefficient = ½Γ((ρ−½)/2)·mult(ρ), Γ ≠ 0 off the real axis.

## Lean
`RHTower/GaussianWeightedGapExtremalBohrSpectrum.lean` (563 lines), wired after GaussianCentralGapBohrSpectrum.
Key: `norm_zeroGerm_sub_gamma_le`, `gaussianCentralGap_eq_archimedean_sub_zeroSeries`,
`tendsto_gaussianWindowAverage_weightedGap`, `tendsto_gaussianWindowAverage_extremalGap`,
`exists_weightedBohrCoefficient_ne_zero_iff`. Build exit 0, no warnings; axioms [propext, Classical.choice, Quot.sound].

## Reading
Positive survivor of the TG faithfulness no-go (readers fail left of Θ): normalized by its exact growth
scale e^{(Θ−½)u/2}, the Gaussian prime source reads the zeros on the extremal line Re ρ = Θ exactly —
frequencies = halved ordinates, amplitudes = multiplicity·½Γ((ρ−½)/2). If RH fails with Θ attained,
the off-line extremal zeros are the visible spectrum; RH is the statement that this spectrum sits at
Θ = ½ together with the archimedean mean A(½).
