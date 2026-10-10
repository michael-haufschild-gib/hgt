# TG — one-sided Gaussian prime budget law

- **ID:** TG-BUD-1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** TG Needs "E_base = E_residual + Tr T_D with E_residual ≥ 0"; TG-ABS-1 (two-sided law)
- **Statement:** P_σ(y) = Σ Λ(n)n^{−σ}e^{−yn²}, C_σ(y) = ∫₁^∞ u^{−σ}e^{−yu²}du.
  (a) Unconditional: |P_σ − C_σ|(y) ≤ (e² + Γ(½)) y^{−2} on (0,1] (σ ≥ 0).
  (b) σ > 0, P_σ(y) ≤ C_σ(y) + B on (0,1] ⇒ ξ ≠ 0 on Re z > σ.
  (c) RH ⟺ ∀σ∈(½,1) ∃B ∀y∈(0,1]: P_σ(y) ≤ C_σ(y) + B.
  (d) Integrated: ∫₀¹ (P_σ−C_σ−B)⁺(y) y^{τ−1}dy < ∞ ∀τ>0 ⇒ ξ ≠ 0 on Re z > σ; RH ⟺ this for all σ∈(½,1).
  (e) Both signs: P_σ ≥ C_σ − B ⇒ same conclusion. Abscissa law (θ ≥ 0): zeros ≤ θ ⟺ upper budget ∀σ∈(θ,2).
  (f) Unconditional Ω±: for 0<σ<½, P_σ − C_σ is unbounded above and below on (0,1] (Hardy zeros).
  (g) Growth law: η(P_σ−C_σ) ≤ B y^{−a} on (0,1] (0≤a≤1) ⇒ ξ ≠ 0 on Re z > σ+2a.
      Quantitative Ω±: σ + 2a < ½ ⇒ P_σ − C_σ = Ω±(y^{−a}) (unconditional).

## Proof
- Log variable y = e^{−u}: mellin f z = ∫_ℝ e^{−zu} f(e^{−u}) du (change of variables).
- Deficit h(u) = B − (P_σ − C_σ)(e^{−u}) ≥ 0 on u ≥ 0; carrier ν = (h + e^{−u}) du.
  Laplace(ν)(z) = B/z − mellin(G)(z) + T(z) + 1/(z+1), T = mellin of the y>1 part (entire);
  mellin G = Γ(z)(A − ξ'/ξ)(σ+2z) (TG-ABS-1).
- Abscissa exists (mass finite at 4, infinite at −2). The continuation is analytic at every positive
  real point (ξ real-zero-free) ⇒ corpus Landau (isAbscissa_eq_of_analyticAt_real) ⇒ abscissa ≤ 0 ⇒
  Laplace(ν) holomorphic on Re z > 0 ⇒ ξ'(σ+2w) = ξ(σ+2w)K(w), K holomorphic on Re w > 0 ⇒ no zeros
  (shared lemma xi_ne_zero_of_deriv_eq_mul_holomorphic).
- (c ⇒) RH ⇒ passage converges (TG-ZF-2) ⇒ gap bounded near 0; (a) bounds it on [y₁,1].

## Integrated version (cycle 9)
Split deficit h = h⁺ − h⁻. Carrier of h⁻ (thickened) has abscissa ≤ 0 by hypothesis
(`exists_isAbscissa_expThickenedCarrier_nonpos`), so its Laplace transform is a holomorphic term on
Re z > 0; Landau runs on the h⁺ carrier exactly as before. Generic carrier lemmas
(`expThickenedCarrier`, mass/transform formulas) replace the budget-specific ones.

## Lean
`RHTower/GaussianPrimeBudgetOneSidedLaw.lean` (925 lines), wired after GaussianPassageSinglePointAbscissa
(refactored to expose xi_ne_zero_of_deriv_eq_mul_holomorphic). `lake build --old` exit 0, no warnings;
axioms [propext, Classical.choice, Quot.sound].

## Reading
TG's nonnegative-residual budget, exactly: E_residual(u) = B − (prime − continuum)(e^{−u}) ≥ 0 is the
whole hypothesis; positivity (Λ ≥ 0 is not even needed — the deficit's sign is assumed) plus the
absence of real zeros of ξ do the rest. Only the UPPER prime budget is needed: primes may undershoot
the continuum arbitrarily. RH = "Gaussian prime mass at weight n^{−σ} never overspends its continuum
budget by more than O(1), for every σ > ½". The sieve/upper-bound side of prime counting is the
relevant side; the open content is an O(1) additive (not multiplicative) upper bound.
