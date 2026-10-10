# TG — the Bohr spectrum of the central Gaussian gap is the set of critical zeros

- **ID:** TG-BOHR-1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean, unconditional statements of the form RH → …)
- **Source:** TG-ZF-1 (zero field), TG-BIAS-1 (critical germs), undamped archimedean defect
- **Statement:** G(y) = Σ Λ(n)n^{-1/2}e^{-yn²} − ∫₁^∞u^{-1/2}e^{-yu²}du, u = log(1/y), μ_ρ = Im ρ/2.
  (a) Gamma form: ‖E(y,b) − ½y^{-b/2}Γ(b/2)‖ ≤ 1/Re b (Re b > 0).
  (b) Critical germ: Re a = 0, a ≠ 0 ⇒ ‖e^{-y}/a + E(y,a) − ½Γ(a/2)y^{-a/2}‖ ≤ (2y+y²)/(|a||a+2|).
  (c) RH ⇒ G(e^{-u}) = A_{e^{-u}}(½) − Σ_ρ ½Γ(iμ_ρ)e^{iμ_ρ u} − O(e^{-u}), Σ_ρ|Γ(iμ_ρ)| < ∞.
  (d) RH ⇒ ∀τ: T⁻¹∫₀^T G(e^{-u})e^{-iτu}du → A(½)[τ=0] − ½Γ(iτ)·m(½+2iτ).
  (e) RH ⇒ ∀τ≠0: ξ(½+2iτ) = 0 ⟺ the τ-Bohr coefficient of G is ≠ 0.

## Proof
(a) Γ(b/2) = ∫_{(0,y]} + Γ(b/2,y), E = ½y^{-b/2}Γ(b/2,y), |∫_{(0,y]} e^{-v}v^{b/2−1}| ≤ y^{Re b/2}/(Re b/2).
(b) Two recursion steps, (a) at b = a+4, Γ(a/2+2) = (a/2+1)(a/2)Γ(a/2).
(c) Zero field at σ = ½ + (b) (|a+2| ≥ |a|, Σ|ρ−½|^{-2} < ∞); amplitude summability from y = 1.
(d) Window averages: characters → [μ = 0]; Cesàro for h → 0; dominated convergence over zero copies
for the absolutely convergent series; A_{e^{-u}}(½) → A(½).
(e) Coefficient = ½Γ(iτ)·#copies with Im = 2τ; Γ(iτ) ≠ 0.

## Lean
`RHTower/GaussianCentralGapBohrSpectrum.lean` (658 lines), wired after GaussianCentralGapExplicitCriterion. Build exit 0, no warnings; axioms [propext, Classical.choice, Quot.sound].
Key: `norm_gaussianIncompleteMellin_sub_gamma_le`, `norm_criticalZeroGerm_sub_gamma_le`,
`gaussianCentralGap_eq_archimedean_sub_bohrSeries`, `tendsto_gaussianWindowAverage_gaussianCentralGap`,
`xi_eq_zero_iff_bohrCoefficient_ne_zero`; window-average calculus `tendsto_gaussianWindowAverage_cexp`,
`tendsto_gaussianWindowAverage_of_tendsto_zero`, `tendsto_gaussianWindowAverage_tsum_cexp`.

## Reading
TG's "faithful source-to-zero identification" in spectral form: the Gaussian prime source, read in
the damping variable, is (under RH) an absolutely convergent almost-periodic function whose Bohr
frequencies are exactly the halved ordinates of the critical zeros and whose amplitudes are the
multiplicities weighted by ½Γ(iτ). Mean value = archimedean bias A(½).
