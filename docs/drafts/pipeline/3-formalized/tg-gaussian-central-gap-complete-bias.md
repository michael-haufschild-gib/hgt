# TG — complete archimedean bias and sign law of the central Gaussian gap

- **ID:** TG-BIAS-1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean, unconditional)
- **Source:** TG-ZF-1 (exact zero field), TG-BUD-1 (one-sided Landau law), Hermitian endpoint mass (RH ⟺ Σ|ρ|^{-2} ≤ 2+γ−log 4π)
- **Statement:** G(y) = Σ Λ(n)n^{-1/2}e^{-yn²} − ∫₁^∞u^{-1/2}e^{-yu²}du, A(½) = 2 + ψ(¼)/2 − (log π)/2.
  (a) Re A(½) ≤ ½log(5/(4π)) ≤ −7/24 (true value −0.686 = 2 − ζ'/ζ(½)).
  (b) Under RH: ∀ε>0, eventually |G(y) − A(½)| ≤ 2(2+γ−log 4π) + ε (< 0.19 + ε); hence G ≤ −1/20 eventually.
  (c) RH ⟺ G < 0 eventually ⟺ G eventually bounded above ⟺ G eventually bounded below.
  (d) Dichotomy: G ≤ −1/20 eventually, or ∀K G > K and G < −K frequently as y → 0⁺.

## Proof
(a) ψ(¼) = ψ(5/4) − 4, ψ ≤ log, log(4π/5) ≥ 1 − 5/(4π) ≥ 7/12.
(b) Zero field: G = Re A_y(½) − Re Σ_ρ g_y(ρ), A_y(½) → A(½). For Re ρ = ½, a = ρ−½: two recursion
steps give g = (2y/a)(−e^{-y}/(a+2) + (2y/(a+2))E(y,a+4)), |E(y,a+4)| ≤ 1/(2y²), so
|g| ≤ 2(1+y)/(|a||a+2|) ≤ 2(1+y)/|ρ|² (|Im ρ| > 1). Under RH Σ|ρ|^{-2} ≤ 2+γ−log 4π < 0.0924
(γ < 0.577216, log 12 > 2.4849).
(c),(d) Converse by the one-sided Landau laws at σ = ½ (upper and lower), with |G| ≤ (e²+Γ(½))δ^{-2} on [δ,1].

## Lean
`RHTower/GaussianCentralGapCompleteBias.lean` (407 lines), wired after GaussianPrimeGapInghamOmega.
Key: `re_gaussianArchimedeanCurrent_half_le`, `norm_criticalZeroGerm_le`,
`eventually_abs_gaussianCentralGap_sub_bias_le`, `riemannHypothesis_iff_eventually_gaussianCentralGap_neg`,
`gaussianCentralGap_dichotomy`. Build exit 0, no warnings; axioms [propext, Classical.choice, Quot.sound].

## Reading
Gaussian ζ-analogue of the Hardy–Littlewood–Landau theorem on Chebyshev's conjecture (χ₋₄): the
bias here is archimedean (Γ-factor constant 2 − ζ'/ζ(½) < 0), not a prime-square bias, and is
complete because Gaussian damping weights critical zeros by |Γ(iγ/2)| ~ e^{−π|γ|/4}. TG reading: an
eventual sign is a discrete gate — RH ⟺ the sign of G is eventually −1; any off-line zero forces
infinitely many sign changes with unbounded amplitude. Novelty: BRIDGE (Landau mechanism + corpus
Hermitian mass); the sharp oscillation amplitude under RH is ½Σ|Γ(iγ/2)| ≈ 3·10⁻⁵, the Lean bound 0.19.
