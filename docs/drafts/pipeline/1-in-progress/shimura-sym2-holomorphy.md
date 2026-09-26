# Shimura's theorem: holomorphy of twisted symmetric-square L-functions (formal)

- **ID:** shimura-sym2
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) — classical (Shimura 1975; Gelbart–Jacquet 1978), formal infrastructure
- **Source:** loop card `selberg-quarter-conjecturing-loop.md`, cycle 71
- **Statement:** for a non-dihedral Hecke–Maass cusp form u of level N and a Dirichlet character ψ,
  L(s, sym²u ⊗ ψ) is entire and satisfies its functional equation with Γ-factor
  Γ_ℝ(s+δ)Γ_ℝ(s+δ±2ν).

## Goal
Shimura's theorem is on the critical path of every known route past Selberg's 3/16: Iwaniec's
GL₂-only 10/49 (forced zeros of square twists with a common Γ-factor) and Gelbart–Jacquet (input to
the GL₃ converse theorem, hence Luo–Rudnick–Sarnak and Kim–Sarnak). No GL(3) automorphy is needed.

## Gates
- [x] 0 → 1  plan fixed (cycle 71)
- [ ] 1 → 2  paper proof assembled per module (below)
- [ ] 2 → 3  Lean: `sym2_twist_entire`, functional equation

## Approach (module plan)
- [x] H1 `HalfWeightTheta`: θ(z) = Σ e(n²z) on Γ₀(4); Γ₀(4) = ⟨T, U, −1⟩ (descent); y^{1/2}|θ|²
  invariant; abstract multiplier J(γ,z) = θ(γz)/θ(z) (θ ≠ 0 on ℍ, corpus `Bottcher`), cocycle,
  |J|² = |cz+d|.
- [ ] H2 cusp evaluation: J(γ,z) = κ(γ)(cz+d)^{1/2}, κ constant (holomorphic, modulus 1);
  Poisson at the cusp −d/c: κ(γ) = c√2 / (G(−d;c)·(ic)^{1/2}), G(a;c) = Σ_{r mod c} e(ar²/c);
  corollary |G(a;c)|² = 2c for 4 | c, (a,c) = 1. No Gauss-sum sign evaluation needed.
- [ ] H3 weight-½ Eisenstein series E(z,w;ψ) = Σ_{Γ_∞\Γ₀(4M)} ψ̄(d) \bar j(γ,z) Im(γz)^w, j = J/|J|:
  convergence Re w > 1, transformation E(γz) = ψ(d) j(γ,z) E(z), holomorphy in w.
- [ ] H4 Fourier expansion: coefficients Σ_c c^{−2w−1/2} Σ_{m mod c} r_c(n − m²)·ψ-weights times
  weight-½ Whittaker integrals (Ramanujan sums appear because κ̄ ∝ G(−d;c)/√c).
- [ ] H5 local densities N_c(n) = #{m mod c : m² ≡ n}: Σ_c N_c(n)c^{−s} = ζ(s)L(s,χ_n)/ζ(2s)·(finite
  corrections); continuation and polynomial bounds |L(σ+it,χ)| ≪ |s| q^{1−σ}/σ (partial summation).
- [ ] H6 continuation of E to an open neighbourhood of {1/2 ≤ Re w ≤ 3/4} minus w = 3/4
  (1/ζ(4w−1) holomorphic there by non-vanishing on Re ≥ 1 and openness).
- [ ] H7 twisted Maass forms u⊗χ on Γ₀(Nr²) with nebentypus χ² (weight 0 conjugation by T_{b/r}).
- [ ] H8 Shimura unfolding: ⟨u_χ(4·) θ̄ y^{1/4}, E(·,w)⟩ = C(w) Σ λ(k²)ψ(k)k^{−(2w−1/2)},
  C(w) from ∫ t^{μ−1}e^{−t}K_ν(t)dt = √π Γ(μ+ν)Γ(μ−ν)/(2^μΓ(μ+1/2)).
- [ ] H9 holomorphy of L(s,sym²u⊗ψ) on a neighbourhood of 1/2 ≤ Re s < 1 (s = 2w − 1/2);
  Re s ≥ 1 from Rankin–Selberg L(s,u×(u⊗ψ)) = L(s,sym²u⊗ψ)L(s,ψ) and L(s,ψ) ≠ 0 there.
- [ ] H10 functional equation of L(s,u×(u⊗ψ)) (weight-0 Eisenstein, nebentypus) ÷ that of
  L(s,ψ) ⇒ functional equation of sym² ⊗ ψ; with H9, entire.
- [ ] H11 Iwaniec–Blomer–Brumley framework F(Y); exponent law; 3/16 via sym² (depth aspect q = p^k
  without Deligne); then the 10/49 gain (mechanism not yet reconstructed; source paywalled).

## Log
- 2026-09-26 — created from loop cycle 71; H1 closed (`RHTower/HalfWeightTheta.lean`, wired, axioms
  propext/choice/Quot.sound).
