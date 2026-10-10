# TG — exponent law of the Gaussian prime gap

- **ID:** TG-EXP-1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** TG-BUD-1 (growth law, Ω±); TG-ZF-1 (exact zero field)
- **Statement:** P_σ(y) = Σ Λ(n)n^{−σ}e^{−yn²}, C_σ(y) = ∫₁^∞ u^{−σ}e^{−yu²}du.
  (a) zeros ≤ θ, 0 < σ ≤ θ ⇒ |P_σ − C_σ|(y) ≤ K y^{−(θ−σ)/2} on (0,1].
  (b) 0 < σ ≤ θ ≤ σ+2: zeros ≤ θ ⟺ ∃K: P_σ − C_σ ≤ K y^{−(θ−σ)/2} on (0,1] (one side suffices).
  (c) For any fixed σ ∈ (0,½]: RH ⟺ P_σ(y) − C_σ(y) ≤ K y^{−(½−σ)/2} on (0,1].
      E.g. RH ⟺ Σ Λ(n)n^{−1/4}e^{−yn²} − ∫₁^∞u^{−1/4}e^{−yu²}du ≤ K y^{−1/8}.
  (d) Central budget (σ = ½, exponent 0): RH ⟺ Σ Λ(n)n^{−1/2}e^{−yn²} ≤ ∫₁^∞u^{−1/2}e^{−yu²}du + K on (0,1].

## Proof
- Right-zero germs: two recursion steps, remainder E(y,a+4) ≤ ½Γ((θ−σ+4)/2) y^{−(θ−σ+4)/2};
  e^{−y}[1/(ρ−½) − 1/(ρ−σ)] = e^{−y}(½−σ)/((ρ−½)(ρ−σ)); |ρ−σ|, |ρ−σ+2| ≥ |Im ρ| > 1.
- gap = MB(y,2,σ) − Σ germ (zero field + passage identity); MB bounded on (0,1].
- (b ⇐): growth law with a = (θ−σ)/2 ∈ [0,1].

## Lean
`RHTower/GaussianPrimeGapExponentLaw.lean` (312 lines), wired after GaussianPrimeBudgetOneSidedLaw.
`lake build --old` exit 0, no warnings; axioms [propext, Classical.choice, Quot.sound].

## Reading
Complete Gaussian exponent dictionary: the one-sided growth exponent of P_σ − C_σ equals
max(0, (Θ − σ)/2), Θ = sup Re ρ (upper bound here, lower bound TG-BUD-1 growth law). RH is the statement
at ONE real point σ ∈ (0,½] with the exact exponent (½−σ)/2. Unconditionally the exponent is ≥ (½−σ)/2
(Hardy) and ≤ (1−σ)/2 (zeros < 1).
