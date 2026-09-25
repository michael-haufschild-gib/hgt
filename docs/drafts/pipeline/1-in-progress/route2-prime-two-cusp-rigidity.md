# Route 2: the prime-2 boundary relation is cusp rigidity, not a winding mechanism

- **ID:** route2-prime-two-cusp-rigidity
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) + NO-GO for route 2 claim (ii)
- **Source:** docs/reports/route-proposals/route2.md, claim (ii) and steps 3, 6;
  2F/theta/theta-rational-cusp-boundary-law (Q, eq. (7)-(8)).
- **Statement:** the self-similarity Q(r+1)+Q(r)=½Q(4r) acts on every Mellin transform
  as multiplication by an explicit unit of the strip, so it cannot constrain any zero count.
  Its actual content is regularity at the zero-charge cusps (q≡2 mod 4) — exactly the input
  that separates θ from weakly holomorphic weight-½ θ-multiplier forms, whose even,
  integer-spectrum theta sources have off-line strip zeros.

## Setting

For a : ℕ≥1 → ℂ with Σ|a_n|/n² < ∞ put Q_a(r)=Σ a_n e^{−iπn²r}/n² (Q=Q_1).
R₂ is the identity Q_a(r+1)+Q_a(r)=½Q_a(4r) for all real r.
For F holomorphic on ℍ write R₂(F): F(τ)+F(τ+1)=2F(4τ). θ=θ₃ satisfies R₂(θ).

## Results

1. **Coefficient law [P].** Q_a(r+1)+Q_a(r)−½Q_a(4r)=Σ_m (a_{2m}−a_m)/(2m²)·e^{−4iπm²r}.
   By uniqueness of Fourier coefficients on ℝ/2ℤ, R₂ ⟺ a_{2m}=a_m for all m.
   For discrete positive spectra Σ b_λe^{−iπλr} (λ≥λ₀>0), R₂ forces λ∈{4^k·m : m odd},
   b_{4^k m}=4^{−k}b_m: R₂ alone forces integer frequencies.
2. **Hecke family [P].** For prime p: Σ_{j<p}Q_a(r+2j/p)=p^{-1}Q_{a(p·)}(p²r); the relation
   H_p: Σ_{j<p}Q_a(r+2j/p)=p^{−1}Q_a(p²r) ⟺ a_{pm}=a_m. H_2 is R₂. All H_p ⟺ a constant ⟺ Q_a=a₁Q.
3. **Mellin diagonality (kills claim (ii)) [P].** With A(s)=Σa_n n^{−s}: R₂ ⟺
   (1−2^{−s})A(s)=Σ_{n odd}a_n n^{−s}. Translation by 1 acts on Q as ½Q(4·)−Q, a combination of
   dilations, which the Mellin transform diagonalizes: 𝓜[Q(·+1)]=−(1−2^{1−s})𝓜[Q] with
   1−2^{1−s}≠0 on 0<Re s<1. Every loop or function built from Q by R₂ has, in the strip, the ξ
   zero set plus zeros of explicit polynomials in 2^{−s}. "Invariance of the winding under
   r↦4r" holds trivially and "evaluation at the fixed point" returns ξ. At the fixed points
   {0,2/3,4/3} of r↦4r (mod 2) the boundary series are ζ(s) and ζ(s)(ω̄+(1−ω̄)3^{−s}); the second
   factor has all zeros on Re s=½ because |G(1,3)|²=3.
4. **Cusp rigidity (positive survivor) [P].** Let F be holomorphic on ℍ, F(τ+2)=F(τ),
   F(−1/τ)=√(−iτ)F(τ), |F(iy)−c|≤Me^{−πy} (y≥1). If R₂(F) then
   F(1+iε)=ε^{−1/2}[(F(i/4ε)−c)−(F(i/ε)−c)], so |F(1+iε)|≤2Mε^{−1/2}e^{−π/(4ε)}.
   The constant term cancels because R₂'s factor 2 equals 4^{1/2} (weight ½).
   Hence a weakly holomorphic form in M^!_{1/2}(Γ_θ,v_θ) with R₂ has no pole at the cusp 1, so
   F/θ is a bounded modular function on the compact curve and F=cθ.
   The cusp 1 class (odd/odd rationals) is the source's zero-charge boundary set y₀=2ip/q,
   q≡2 mod 4 (rational-cusp card, (1a)).
5. **Counter-models without R₂ [P, Lean open].** h=θ₂⁴θ₄⁴/θ₃⁸=λ(1−λ) is Γ_θ-invariant,
   holomorphic on ℍ, zero at ∞, pole at cusp 1. For real P, F_P=θP(h) is 2-periodic, has the
   θ inversion law, real integer-spectrum q-expansion, and F_P(iy) behaves like P(0)θ at both
   ends of the imaginary axis. Its source k_P(x)=y^{5/4}(2yΘ''+3Θ')(y), Θ(y)=F_P(iy), y=e^{2x},
   is even, a sum of the same Gaussian atoms φ_{πλ} with λ∈ℤ, analytic on |Im x|<π/4, and
   super-exponentially decaying; Ξ_P is entire, even, real on ℝ. Two real parameters
   (P=1+t₁X+t₂X²) place a zero at any z₀ where Ξ_{θh}(z₀), Ξ_{θh²}(z₀) are ℝ-independent, an
   open dense set of the strip (else Ξ_{θh}/Ξ_{θh²} is real on an open set, hence constant,
   contradicting q-expansions 16q+… vs 256q²+…).

## Whole-route consequence

- Claim (ii) as stated is vacuous: R₂ is the 2-Euler factor and acts diagonally.
- Test B for route 2 is met by R₂, but for a different reason than the proposal gives:
  R₂ is the zero-charge cusp regularity (Hamburger's convergence hypothesis in modular form).
  The one-sided gauge k+b·k(·+log 3) also satisfies R₂ (frequencies n², 9n²) with off-line zeros
  (1+b√3·3^{−w}); it breaks FE. The deformation audit must include V=θ·ℝ[h].
- Inside FE + integer spectrum + source-strip analyticity the theta source is a single point
  (rigidity). A route-2 mechanism must be analytic and valid on a class that excludes V; the
  only separating datum is growth at zero-charge cusps. Step 3 has no candidate loop left.

## Log
- 2026-09-26 — created; results 1–5 on paper; Lean formalization of 1, 2, 4 started.
