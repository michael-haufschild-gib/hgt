# TG — dense sign changes of the central Gaussian gap forced by an extremal zero

- **ID:** TG-SGN-2
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean, unconditional)
- **Source:** TG-BOHR-2 (extremal decomposition, visibility), TG-BIAS-1 (RH ⇒ eventual negativity)
- **Statement:** G(y) = Σ Λ(n)n^{-1/2}e^{-yn²} − ∫₁^∞u^{-1/2}e^{-yu²}du, Θ = sup Re ρ. If ξ(ρ₀) = 0 with
  Re ρ₀ = Θ > ½, then ∃ L, ε > 0, U₀ such that every window [u₀, u₀+L] (u₀ ≥ U₀) contains u, u' with
  G(e^{-u}) > εe^{(Θ−½)u/2} and G(e^{-u'}) < −εe^{(Θ−½)u'/2}.

## Proof
g(u) = e^{-(Θ−½)u/2}G(e^{-u}) = −S(u) + o(1), S = Σ_{Re ρ=Θ}½Γ((ρ−½)/2)e^{i(Im ρ/2)u} (absolutely
convergent). Window averages over [u₀,u₀+L] extract S's coefficients uniformly in u₀
(error Σ|c|·min(1, 2/(L|μ−τ|)) → 0). Coefficient at τ₀ = Im ρ₀/2 is C₀ ≠ 0 (visibility), at 0 it is 0
(no real zeros). If g ≥ −ε on a window: |avg(g e^{-iτ₀u})| ≤ avg(g) + 2ε, i.e. 3|C₀|/4 ≤ |C₀|/4 + 2ε:
contradiction for ε = |C₀|/16. Same for −g.

## Lean
`RHTower/GaussianCentralGapExtremalSignChanges.lean` (427 lines), wired after GaussianWeightedGapExtremalBohrSpectrum
(which now exports `tendsto_weightedGap_add_extremalSeries`). Key: `exists_uniform_shiftedWindowAverage_tsum_cexp`,
`norm_shiftedWindowAverage_le_of_ge`, `weightedBohrCoefficient_zero`, `exists_dense_sign_changes_of_extremal_zero`.
Build exit 0, no warnings; axioms [propext, Classical.choice, Quot.sound].

## Reading
Sharp TG sign dichotomy: RH ⇒ the central gap is eventually negative (finitely many sign changes,
TG-BIAS-1); an off-line zero on the extremal line ⇒ sign changes with bounded gaps L and amplitude
growing like e^{(Θ−½)u/2}, so the TG sign-change count on [0,U] is ≥ U/L − O(1). Open residual: Θ > ½
not attained (zeros accumulating to Θ from the left) — only Ω± (TG cycle 10) is known there.
