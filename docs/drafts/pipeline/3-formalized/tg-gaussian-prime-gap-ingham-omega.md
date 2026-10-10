# TG — explicit-constant Ω± for the Gaussian prime gap

- **ID:** TG-OMG-1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean, unconditional)
- **Source:** TG-BUD-1 (Landau carrier), TG-EXP-1 (exponent law)
- **Statement:** 0 < σ < ½, a = (½−σ)/2, G = P_σ − C_σ.
  (a) η G ≤ c y^{−a} + K on (0,1] (η = ±1) ⇒ RH and m|Γ((ρ₀−σ)/2)|/2 ≤ c for every critical zero ρ₀ of order m.
  (b) Unconditional: ∃ c₀ > 0 (= |Γ((ρ₀−σ)/2)|/2 at a Hardy zero) with G = Ω±(c y^{−a}) for all c < c₀.

## Proof
Deficit (c+ε)e^{au} − ηG(e^{−u}) is ≥ 0 beyond U = |K|/(εa); its negative part has compact support
(entire Laplace term). Landau: positive carrier abscissa ≤ a; identity theorem: transform =
B'/(w−a) + R(w) on Re w > a (RH from the growth law makes R holomorphic there).
Positivity |L(t+iτ)| ≤ L(t); multiply by (t−a), t↓a: LHS → |η Γ(w₀) m/2| (residue of ξ'/ξ(σ+2w) at
w₀ = (ρ₀−σ)/2 via the HTGeometry residue lemma), RHS → c+ε.

## Lean
`RHTower/GaussianPrimeGapInghamOmega.lean` (334 lines), wired after GaussianPrimeGapExponentLaw. Budget file
refactored: `complexLaplace_gaussianBudgetCarrier_eq` (carrier identity), `exists_isAbscissa_gaussianBudgetCarrier_le`
(Landau). Build exit 0, no warnings; axioms [propext, Classical.choice, Quot.sound].

## Reading
Unconditional Gaussian Ingham theorem: the gap at σ < ½ oscillates with amplitude ≥ c₀ y^{−(½−σ)/2}
in both directions; under RH it is O(y^{−(½−σ)/2}) (TG-EXP-1). So for σ < ½ the order of the gap is
exactly y^{−(½−σ)/2} iff RH. The TG central budget (σ = ½, exponent 0) sits exactly at the boundary
where this oscillation amplitude becomes O(1).
