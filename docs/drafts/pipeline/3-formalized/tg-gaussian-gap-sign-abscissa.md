# TG — the sign abscissa of the Gaussian prime gaps is the zero abscissa

- **ID:** TG-SGN-1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean, unconditional)
- **Source:** TG-BIAS-1 (complete archimedean bias), TG-BUD-1 (Landau laws), undamped passage (TG cycle 5), Hadamard pair positivity
- **Statement:** G_σ(y) = Σ Λ(n)n^{-σ}e^{-yn²} − ∫₁^∞u^{-σ}e^{-yu²}du, Θ = sup Re ρ.
  (a) Re A(σ) ≤ ½log((σ+2)/(2π)) for σ > 0 (negative on 0 < σ < 2π−2).
  (b) zeros ≤ θ < σ < 2 ⇒ G_σ(y) → Re(A(σ) − ξ'/ξ(σ)) (Gaussian Mertens limit) and G_σ < ¼log((σ+2)/(2π)) < 0 eventually.
  (c) a zero with Re ρ > σ > 0 ⇒ G_σ > K and G_σ < −K frequently as y → 0⁺, ∀K.
  (d) inf{σ ∈ (0,2) : G_σ < 0 eventually} = Θ; RH ⟺ this sign abscissa = ½.

## Proof
(a) ψ(σ/2) = ψ(σ/2+1) − 2/σ, ψ ≤ log: A(σ) = 1/σ + ψ(σ/2)/2 − ½log π ≤ ½log((σ/2+1)/π).
(b) Formation identity Φₓ'/Φₓ = A − G_σ(πx) and exact passage Φₓ'/Φₓ(σ) → ξ'/ξ(σ). Every zero has
|Re ρ − ½| ≤ θ − ½ < σ − ½ (reflection), so the line-conjugate pair law gives Re ξ'/ξ(σ) ≥ 0.
(c) One-sided Landau laws (upper and lower) + |G_σ| ≤ (e²+Γ(½))δ^{-2} on [δ,1].
(d) IsGLB: eventual negativity at σ bounds all zeros by σ (c); every σ ∈ (Θ,2) qualifies (b).

## Lean
`RHTower/GaussianGapSignAbscissa.lean` (317 lines), wired after GaussianCentralGapCompleteBias. Key:
`re_gaussianArchimedeanCurrent_ofReal_le`, `tendsto_gaussianWeightedGap_of_zero_bound`,
`eventually_gaussianWeightedGap_lt_of_zero_bound`, `frequently_gaussianWeightedGap_gt_of_lt_re`,
`gaussianSignAbscissa_eq_xiZeroAbscissa`, `riemannHypothesis_iff_gaussianSignAbscissa_eq_half`.
Build exit 0, no warnings; axioms [propext, Classical.choice, Quot.sound].

## Reading
The sign of the Gaussian prime gap is a discrete invariant whose region of eventual constancy is
exactly the zero-free half-plane: right of all zeros the gap converges to A(σ) − ξ'/ξ(σ), which is
negative because the Γ-current is negative below 2π−2 and Hadamard positivity only lowers it; left
of a zero it oscillates with unbounded amplitude. At σ = Θ = ½ (RH) the sign is still eventually
negative (TG-BIAS-1), so under RH the sign region is the closed half-line [½, 2).
