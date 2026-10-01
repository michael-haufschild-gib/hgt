# Notch Bochner law: the complete notch information

- **ID:** MC-185
- **Stage:** 3-formalized (STATUS MUST-622)
- **Type:** THEOREM (Lean)
- **Source:** MC loop cycle 185. This is the no-go closure of the notch route: the exact boundary of what notch tests can see.
- **Statement:** For notch-small Weil deviations with convergent gcd-harmonic sums `Γ(g) = Σ_n d(n) gcd(n, P^{g⁺})/n`, every twist polynomial gives `Σ_{a,a'} c_a c_{a'} (P^{|a−a'|})^{−½} Γ(a−a') ≤ 0`.

## Goal
Cycles 179–184 used single and two-point twists. This theorem computes all twists exactly and states the full constraint. It is a Bochner negative-definiteness condition on `ℤ^P` whose value at `0` is `T`. With `T = 0` it forces `Γ ≡ 0` (harmonic pinning, MUST-619). With `T < 0` it is satisfiable by many nonzero deviations, for example balanced semiprime floors with a sufficient total deficit. So the notch route ends exactly at the scalar inequality `T ≥ 0`.

## Paper proof
1. **Exponent identity.** `|v − g| + 2min(v, g⁺) = v + |g|` gives `twistNorm(n,g) · gcd(n,P^{g⁺})² = n · P^{g⁺}P^{g⁻}`.
2. **Main weight.** `W(n) = n^{−½} Σ_{a,a'} c_a c_{a'} (P^{|a−a'|})^{−½} gcd(n, P^{(a−a')⁺})`. Hence the fibre sums are `Σ_{a,a'} c c (P^{|a−a'|})^{−½} Γ_k(a−a')`.
3. **Limit.** A positive limit contradicts MUST-606.

## Lean
- Module `WeilConeNotchBochnerLaw`: `gcdPart`, `twistNorm_mul_gcdPart_sq`, `twistGramWeight`, `inv_sqrt_twistNorm_eq_gcdPart`, `twistMainWeight_eq_gcd`, `gcdHarmonicSum`, `sum_twistFibre_eq`, `notchBochner_le`.
- Audit:
  - compiles cleanly with `lake env lean` (olean with `-o`);
  - standard axioms;
  - wired after `WeilConeHarmonicPinning`;
  - collision scan clean.

## No-go closure (notch route for `T < 0`)
- **Killing mechanism:** every notch, pole or Toeplitz test has a positive diagonal coefficient on `T`, so Weil positivity yields only `T ≤ 0`.
- **Strongest positive survivor:**
  - the notch Bochner law (this card);
  - harmonic pinning: `T = 0 ⇒ lam = Λ` for the nonnegative cone with vanishing local mass (MUST-619/621);
  - the RH criterion `RH ⟺ ∃ lam ≥ 0` in `W` with vanishing local mass and `T ≥ 0`.
- **New insight:** for this cone, the uniqueness half of the RH program is exactly a lower bound for the harmonic constant at `s = 1`, i.e. `H_lam(1) ≤ ξ'/ξ(1) = Σ 1/ρ`.

## Log
- 2026-10-01: created and formalized (cycle 185).
