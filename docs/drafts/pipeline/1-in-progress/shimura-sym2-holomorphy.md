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
- 2026-09-26 — H2 closed (`HalfWeightThetaMultiplier`): κ(γ) constant by maximum modulus; Poisson at
  the cusp −d/c (`theta_cusp`); `J_mul_gauss`: J(γ,z)·G(−d;c)·(ic)^{1/2} = c√2(cz+d)^{1/2};
  `norm_sq_gaussQ`: |G(−d;c)|² = 2c for 4 | c, (c,d) = 1. H3 closed (`HalfWeightEisenstein`):
  `eisHalf` on ⟨T⟩\Γ₀(4M) with nebentypus ψ, absolute convergence Re w > 1, `eisHalf_smul`.
  All wired; axioms propext/choice/Quot.sound.
- 2026-09-26 — H4a closed (`HalfWeightKernel`: kerH = e^{-i arg(x+iy)/2}(y/(x²+y²))^s, |kerH| = wt^σ,
  Fourier decay, Poisson for Re s ≥ 3/4). H4b in progress: `star_jU_mul_im_cpow` (c > 0 summand =
  C(c,d) c^{-2w} kerH(y, x + d/c), C unimodular, C(c,d) = G(−d;c)(ic)^{1/2}/(√2 c)).
  **Design decisions for H6/H8 (recorded so they survive compaction):**
  (a) Growth of E at the other cusps is NOT obtained from Eisenstein series at every cusp. Near a
      rational point a, the expansion at ∞ with |𝓕kerH_{y,w}(n)| ≤ min(y^{1−σ}C_σ, D|w|²y^{−1−σ}/n²)
      and |D_n(w)| ≪ n^{1/2+ε}(1+|w|)^A gives |E(ζ,w)| ≪ (Im ζ)^{−A'}: polynomial growth at every
      cusp, enough because F(z) = u(4z)θ̄(z)y^{1/4} decays exponentially at every cusp.
  (b) Continuation across Re w = 1/2 is required (the critical line s = 2w − 1/2, Re s = 1/2, is not
      covered by the functional equation). Non-constant coefficients: integrate 𝓕kerH by parts
      once (converges for Re w > 0). Constant term: ∫kerH(1,w,x)dx = ∫(1+ix)^{−a}(1−ix)^{−b}dx with
      a = w + 1/4, b = w − 1/4, closed form 2^{2−a−b}πΓ(a+b−1)/(Γ(a)Γ(b)) (Beta integral); its
      pole at w = 1/2 cancels the zero of 1/ζ(4w−1).
  (c) Poles at s = 1 are handled by Rankin–Selberg, not by the θ-residue of E at w = 3/4.
