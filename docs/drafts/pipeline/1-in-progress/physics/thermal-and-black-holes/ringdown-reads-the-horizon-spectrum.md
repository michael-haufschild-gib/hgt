# Ringdown reads the horizon spectrum

- **ID:** ringdown-horizon-spectrum
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** user question: zeta zeros and black-hole ringdown (merger, or a gravitational wave hitting a black hole)
- **Statement:** On exact sech² black holes, ω = ±√(Q−1/4) − i(n+1/2) with Q in the horizon spectrum. A round horizon gives an ℓ²-perturbed arithmetic ladder, which no critical zero sequence contains; the modular horizon carries every zero as a causal pole.

## Goal
Separate what is exact from what is analogy, and locate the arithmetic. Not an RH route: the positive side restates known scattering facts in ringdown form, and the universal-damping form is RH-equivalent.

## Gates
- [x] 0 → 1 in-progress: corpus read (HB route, Putnam chain, QNMPoschlTeller)
- [ ] 1 → 2 fully-proven
- [ ] 2 → 3 formalized

## Claims to prove
1. **Common radial law.** Massless topological black hole (conformal scalar, ψ = rΦ) and Nariai dS₂×S² (massless scalar) both give ψ_tt − ψ_xx + Q sech²x ψ = 0.
2. **ℓ¹ Putnam.** Σ_n |ζ(½+i(a+dn))|/|½+i(a+dn)| = ∞ for every a and d > 0.
3. **ℓ² ladder no-go.** If Σ|η_n|² < ∞, then ζ(½+i(a+dn)+η_n) = 0 fails for infinitely many n.
4. **Round horizon no-go.** For every κ > 0, b and c, the ladder κ√((l+½)²−c)+b is not eventually in the zeros.
5. **Causal symbol.** The n-th overtone carries φ(D+½−iω): pole on ω₋, shadow zero on ω₊. Rate D + (1−β)/2.
6. **Echo train.** φ is the Laplace transform of a causal train with delays 2 log c and weights ϕ(c)/c.

## Paper proofs

**Claim 1.** Hyperbolic case: f = r²−1, r = −coth x on x < 0, so dr/dx = f, f = 1/sinh²x, and (r²−1)/r² = 1/cosh²x. For ψ = rΦ the conformal scalar has V = f(Q/r² + f′/r − 2) with f′/r = 2, so V = Q/cosh²x. Nariai case: ρ = tanh x, f = 1−ρ² = 1/cosh²x, unit S² radius, V = fQ. For Q ≥ ¼ put ξ = √(Q−¼); then Q = ξ²+¼ and the corpus mode `qnmPoschlTeller_wave_equation` is an exact solution with frequency −ξ−i/2.

**Claim 2.** Let D be Putnam's periodisation, P = 2π/d, cₙ = ∫₀ᴾ D e^{−idny} = −ζ(zₙ)/zₙ with zₙ = ½+i(a+dn). Suppose A = Σₙ≥₀|cₙ| < ∞.
1. The conjugate Cauchy pairing C′ᵣ = ∫D(1−re^{−idy})⁻¹ = Σₘ rᵐcₘ has |C′ᵣ| ≤ A.
2. Poisson positivity gives |Cᵣ + C′ᵣ − c₀| ≤ MP with M = sup|D|, so |Cᵣ| ≤ MP + 2A.
3. With Kᵣ = Im(1−re^{idy})⁻¹, ∫DKᵣ = (Cᵣ−C′ᵣ)/(2i), bounded by (MP+3A)/2 uniformly in r.
4. Folding gives ∫DKᵣ = ∫₀^{P/2} Ψ Kᵣ with Ψ(y) = D(y)−D(P−y) → J ≠ 0, Putnam's jump. Since Kᵣ ≥ 0 on (0,P/2] with mass (log(1+r)−log(1−r))/d → ∞ and stays bounded away from 0, the pairing is unbounded. Contradiction.

**Claim 3.** Let C_a be Putnam's kernel, ‖C_a(x)‖ ≤ e^{−|x|/2}, τₙ(x) = C_a(x)e^{−idnx}. For 0 < Re z < 1 with z = zₙ+η, splitting at 0 and using ∫₀^∞{eˣ}e^{−zx} = 1/(z−1) − ζ(z)/z gives ∫τₙ(x)e^{−ηx}dx = −ζ(z)/z.
Let bₙ = ∫xτₙ(x)dx.
- *Square summability.* Put T = Σₙ<N b̄ₙe^{−idnx} and X = Σₙ<N|bₙ|². Then X = ∫xC_a T. With β(x) = 4e^{−|x|/4} ≥ |xC_a(x)| and any λ > 0, |T| ≤ (λ+|T|²/λ)/2. Splitting ℝ into periods, using sup β on the k-th period ≤ βₖ with W = Σβₖ < ∞ and Parseval on a period, ∫β|T|² ≤ WPX. Taking λ = WP gives X ≤ WP∫β.
- *Taylor.* For |η| ≤ ¼, |e^{−ηx}−1+ηx| ≤ |η|²x²e^{|x|/4}, so the remainder is at most K|η|², K = ∫128e^{−|x|/8}dx.
- If ζ(zₙ+ηₙ) = 0 for n ≥ n₀, then for large n |cₙ| ≤ |ηₙ||bₙ| + K|ηₙ|² ≤ (|ηₙ|²+|bₙ|²)/2 + K|ηₙ|², which is summable. This contradicts Claim 2.

**Claim 4.** With A = l+½ and A² ≥ c: √(A²−c)−A = −c/(√(A²−c)+A), so its modulus is at most |c|/A, hence ℓ². Apply Claim 3 with a = b+κ/2, d = κ. Nariai scalar is c = ½; Nariai gravity, Q = (l+2)(l−1), is c = 5/2. More generally any band with ω_l = Ωl+b+O(1/l) is covered.

**Claim 5.** Put s = D+½−iω and z = −2ω−2iD−i/2, so s = ¼+iz/2. Then ω₋(z) ↦ z and ω₊(z) ↦ −z−i, the shadow. Corpus incidence gives a pole at ω₋ and a regular zero at ω₊. Since Im z = ½−β, −Im ω₋ = D+¼+Im z/2 = D+(1−β)/2.

**Claim 6.** For Re s > 1: the Beta integral with x = e^{−v} gives ∫₀^∞e^{−(s−½)v}(1−e^{−v})^{−½}dv = B(s−½,½) = √πΓ(s−½)/Γ(s). Translating by L_c = 2 log c multiplies by c^{−(2s−1)}, so summing with weights ϕ(c)/c gives √πΓ(s−½)/Γ(s)·Σϕ(c)c^{−2s} = Λ(2s−1)/Λ(2s), with Fubini justified by ϕ(c) ≤ c. Taking s = D+½−iω, this is the retarded transform of e^{−Dt}K(t) for Im ω > ½−D, and it equals (s/(s−1))·S_cusp(z).

**Paper only: full-field selection.** For a horizon packet in the Eisenstein channel, the n-th radial residue carries e^{∓iξt}, paired with φ(½∓iξ) in the reflected term. Closing the ξ contour gives poles only where φ(D+½−iω) has them, so ω₋ is excited and ω₊ is not. This needs Eisenstein continuation and growth bounds not formalized here.

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** pending
- **Strongest positive survivor:** pending
- **New insight:** pending
- **Status:** pending

## Log
