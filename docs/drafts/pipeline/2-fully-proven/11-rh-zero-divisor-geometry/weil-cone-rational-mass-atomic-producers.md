# Rational-mass atomic producers are fake ζᵏ with RH; half-integer masses force Λ

- **ID:** weil-cone-rational-mass-atomic-producers
- **Stage:** 2-fully-proven (k = 2 theorem; reduction for all k)
- **Type:** THEOREM (paper)
- **Source:** krein-producer-loops L150, L153, L168 (open item "mixed/irrational masses"), L222
- **Statement:**
  - (a) A full-cone producer with locally finite atomic Weil measure and masses in `(1/k)ℤ_{>0}` is exactly `lam = (1/k)Λ_G`, where `G` is a Dirichlet series (`g₁ = 1`) with ζᵏ's functional equation (`Γ_ℝ(s)^k`, conductor 1, only a pole of order `k` at `s = 1`, finite order), all of whose nontrivial zeros lie on `Re s = ½`. Conversely, every such `G` gives a producer.
  - (b) For `k = 2`: `G = ζ²`, so `lam = Λ` and RH holds.

## Goal
Close part of the atomic branch of the uniqueness problem beyond L153 (integer masses), and turn the rest into a precise converse-theorem question.

## Gates
- [x] 0 → 1
- [x] 1 → 2: paper proof, modulo classical inputs:
  - Maass's converse theorem for even forms at level 1 (one functional equation, via Cauchy data on the imaginary axis);
  - `λ₁(SL₂(ℤ)) > ¼` (Roelcke; the numerical value is `91.14`);
  - the Eisenstein constant-term analysis at `s = ½` (`E(z,½) ≡ 0`; `∂_sE` has coefficients `∝ d(n)`).
- [ ] 2 → 3: Lean needs the Maass converse theorem and a spectral-gap input, neither of which is in the corpus.

## Proof sketch
1. **Setup.** The Herglotz function is `Φ = Σ m_j 2(s−½)/((s−½)²+t_j²)`, so `E = exp∫Φ = Π(1+(s−½)²/t_j²)^{m_j} = C·s(s−1)Γ_ℝ(s)F(s)`, with `F = exp(Σ lam(n)n^{−s}/log n)`.
2. **Degree-k functional equation.** `E^k` is single-valued, entire and even. Hence `G = F^k` has ζᵏ's functional equation, and its zeros are the atoms.
3. **Datum.** Only the datum `Γ_ℝ(s)^k` with conductor 1 is allowed. Shifts, odd factors or `q > 1` make the continuous density negative at `t = 0`, because `θ'` has its strict minimum there.
4. **Converse.** For `lam = (1/k)Λ_G` the Weil measure is `(1/k)Σ_{zeros of G} δ`.
5. **k = 2.**
   - Form `u(z) = c(y) + Σ g_n 4√y K₀(2πny)cos 2πnx`. It is even and a Δ-eigenfunction with `λ = ¼`.
   - The functional equation gives `u∘S = u` on `x = 0`, and evenness gives matching `x`-derivatives there. Holmgren then gives `u∘S ≡ u`, so `u` is automorphic.
   - There are no `λ = ¼` cusp forms for `SL₂(ℤ)`, and `E(z,½) ≡ 0`. So `u ∝ ∂_sE(z,½)`, which gives `G = ζ²`, `F = ζ`, `lam = Λ` and RH.

## Literature audit (L223)
Part (b) is a corollary of the Kaczorowski–Perelli classification of degree-2, conductor-1 functions in the extended Selberg class (Adv. Math. 2022; arXiv 2503.02492). The datum `Γ_ℝ²` is their case `χ_F = 0`, whose only member is ζ². So (b) is a BRIDGE. The new content is the correspondence (a) and the datum rigidity at `t = 0`. Degree 3 with conductor 1 has no classification in the literature.

## Open core (k ≥ 3)
- `V_k = ζᵏ·V₀^{ζ,k}`, where `V₀^{ζ,k}` is the set of Dirichlet series `B` with `B(s) = B(1−s)` whose only poles are at nontrivial zeta zeros (of order `≤ k·`multiplicity).
- For `k = 3`: `G/ζ` is a λ = ¼ Maass-type function whose `S`-defect is supported on the zeta spectrum.
- Automorphic fakes are excluded: a level-1 GL(3) cusp form with trivial parameters would have `λ = 1`, below Miller's bound.
- A non-automorphic `G ≠ ζ³` with RH would be a non-Λ producer.

## No-go closure
- **Killing theorem:** (b) for masses in `½ℤ`.
- **Strongest positive survivor:** the exact correspondence (a) between rational-mass atomic producers and fake ζᵏ with RH. It is a new producer source and a new link between Weil-cone uniqueness and twist-free converse theorems.
- **Status:** paper-complete for (a) and (b); (k ≥ 3) open.

## Log
- 2026-09-30 — created at stage 2
