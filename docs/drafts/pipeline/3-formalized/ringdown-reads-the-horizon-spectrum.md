# Ringdown reads the horizon spectrum

- **ID:** ringdown-horizon-spectrum
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** user question: zeta zeros and black-hole ringdown (merger, or a gravitational wave hitting a black hole)
- **Statement:** On exact sech² black holes, ringdown frequencies read the horizon spectrum. A round horizon gives an ℓ²-perturbed arithmetic ladder, which no sequence of zeta zeros follows; the modular horizon carries every zero as a pole of a causal symbol, the retarded transform of an echo train with delays 2 log c.

## Goal
Separate what is exact from what is analogy, and locate where arithmetic can enter. Not an RH route: the positive side restates known scattering facts in ringdown form, and the universal-damping form is RH-equivalent. No novelty claim; no literature audit was run.

## Gates
- [x] 0 → 1 in-progress: corpus read (HB route, Putnam chain, QNMPoschlTeller)
- [x] 1 → 2 fully-proven: paper proofs below, except the full-field selection
- [x] 2 → 3 formalized: programme `BlackHoleRingdown/`, modules checked with `lake --old env lean`, axioms `propext`, `Classical.choice`, `Quot.sound`

## Lean certificate
Folder `formal/GaloisForLFunctions/BlackHoleRingdown/`, umbrella `BlackHoleRingdown.lean`, wired into `MainTheorems.lean`.

| Module | Theorems |
|---|---|
| `NoNearArithmeticLadderOfZeros` | `not_summable_norm_riemannZeta_div`, `not_eventually_riemannZeta_eq_zero_of_sq_summable`, `not_eventually_riemannZeta_critical_eq_zero_of_sq_summable`, `not_eventually_riemannZeta_critical_eq_zero_of_eikonal` |
| `RingdownReadsTheHorizonSpectrum` | `topologicalPotential_radius`, `nariaiPotential_tanh`, `horizonMode_wave_equation`, `not_eventually_riemannZeta_eq_zero_roundLadder`, `not_eventually_riemannZeta_eq_zero_nariaiScalar`, `not_eventually_riemannZeta_eq_zero_nariaiGravity` |
| `TheEchoTrainOfTheCusp` | `echoKernel_eq_zero_of_nonpos`, `integral_cexp_mul_echoKernel`, `integral_cexp_mul_echoKernel_eq_completed` |
| `TheCausalSymbolOfTheModularHorizon` | `causalSymbol_qnmMinus_isPole`, `causalSymbol_qnmPlus_isZero`, `ringdownRate_xiSpectralPoint`, `riemannHypothesis_iff_universal_damping`, `exists_excitationFactor`, `retardedTransform_dampedEchoKernel` |

## Paper proofs

**Common radial law.** Hyperbolic case: f = r²−1, r = −coth x on x < 0, so dr/dx = f, f = 1/sinh²x, and (r²−1)/r² = 1/cosh²x. For ψ = rΦ the conformal scalar has V = f(Q/r² + f′/r − 2) with f′/r = 2, so V = Q/cosh²x. Nariai case: ρ = tanh x, f = 1−ρ² = 1/cosh²x, unit S² radius, V = fQ. For Q ≥ ¼ put ξ = √(Q−¼); then Q = ξ²+¼ and `qnmPoschlTeller_wave_equation` gives an exact solution with frequency −ξ−i/2.

**ℓ¹ Putnam.** Let D be Putnam's periodisation, P = 2π/d, cₙ = ∫₀ᴾ D e^{−idny} = −ζ(zₙ)/zₙ with zₙ = ½+i(a+dn). Suppose A = Σₙ≥₀|cₙ| < ∞.
1. The conjugate Cauchy pairing C′ᵣ = ∫D(1−re^{−idy})⁻¹ = Σₘ rᵐcₘ has |C′ᵣ| ≤ A.
2. Poisson positivity gives |Cᵣ + C′ᵣ − c₀| ≤ MP with M = sup|D|, so |Cᵣ| ≤ MP + 2A.
3. With Kᵣ = Im(1−re^{idy})⁻¹, ∫DKᵣ = (Cᵣ−C′ᵣ)/(2i), bounded by (MP+3A)/2 uniformly in r.
4. Folding gives ∫DKᵣ = ∫₀^{P/2} Ψ Kᵣ with Ψ(y) = D(y)−D(P−y) → J ≠ 0, Putnam's jump. Since Kᵣ ≥ 0 on (0,P/2] with mass (log(1+r)−log(1−r))/d → ∞ and stays bounded away from 0, the pairing is unbounded. Contradiction.

**ℓ² ladder.** Let C_a be Putnam's kernel, ‖C_a(x)‖ ≤ e^{−|x|/2}, τₙ(x) = C_a(x)e^{−idnx}. For 0 < Re z < 1 with z = zₙ+η, splitting at 0 and using ∫₀^∞{eˣ}e^{−zx} = 1/(z−1) − ζ(z)/z gives ∫τₙ(x)e^{−ηx}dx = −ζ(z)/z. Let bₙ = ∫xτₙ(x)dx.
- *Square summability.* Put T = Σₙ<N b̄ₙe^{−idnx} and X = Σₙ<N|bₙ|². Then X = ∫xC_a T. With β(x) = 4e^{−|x|/4} ≥ |xC_a(x)| and any λ > 0, |T| ≤ (λ+|T|²/λ)/2. Splitting ℝ into periods, using sup β on the k-th period ≤ βₖ with W = Σβₖ < ∞ and Parseval on a period, ∫β|T|² ≤ WPX. Taking λ = WP gives X ≤ WP∫β.
- *Taylor.* For |η| ≤ ¼, |e^{−ηx}−1+ηx| ≤ |η|²x²e^{|x|/4}, so the remainder is at most K|η|², K = ∫128e^{−|x|/8}dx.
- If ζ(zₙ+ηₙ) = 0 for n ≥ n₀, then for large n |cₙ| ≤ |ηₙ||bₙ| + K|ηₙ|² ≤ (|ηₙ|²+|bₙ|²)/2 + K|ηₙ|², which is summable. This contradicts ℓ¹ Putnam.

**Round horizon.** With A = l+½ and A² ≥ c: √(A²−c)−A = −c/(√(A²−c)+A), so its modulus is at most |c|/A, hence ℓ². Apply the ladder theorem with a = b+κ/2, d = κ. Nariai scalar is c = ½; Nariai gravity, Q = (l+2)(l−1), is c = 5/2.

**Causal symbol.** Put s = D+½−iω and z = −2ω−2iD−i/2, so s = ¼+iz/2. Then ω₋(z) ↦ z and ω₊(z) ↦ −z−i, the shadow. Corpus incidence gives a pole at ω₋ and a regular zero at ω₊. Since Im z = ½−β, −Im ω₋ = D+¼+Im z/2 = D+(1−β)/2.

**Echo train.** For Re s > 1: the Beta integral with x = e^{−v} gives ∫₀^∞e^{−(s−½)v}(1−e^{−v})^{−½}dv = B(s−½,½) = √πΓ(s−½)/Γ(s). Translating by L_c = 2 log c multiplies by c^{−(2s−1)}, so summing with weights ϕ(c)/c gives √πΓ(s−½)/Γ(s)·Σϕ(c)c^{−2s} = Λ(2s−1)/Λ(2s), with Fubini justified by ϕ(c) ≤ c. Taking s = D+½−iω, this is the retarded transform of e^{−Dt}K(t) for Im ω > ½−D, and it equals (s/(s−1))·S_cusp(z).

## Not formalized
- **Radial reduction.** `topologicalPotential` and `nariaiPotential` are defined by their standard formulas. Reducing the wave operator on each metric to these potentials is on paper only.
- **Full-field selection.** For a horizon packet in the Eisenstein channel, the n-th radial residue carries e^{∓iξt}, paired with φ(½∓iξ) in the reflected term. Closing the ξ contour gives poles only where φ(D+½−iω) has them, so ω₋ is excited and ω₊ is not. This is a paper sketch: it needs Eisenstein continuation and growth bounds. Lean proves the divisor of the symbol and its retarded-transform identity, not that the full field carries this symbol.
- **Real black holes.** The law ω_l = Ωl+b+O(1/l) for Schwarzschild and fixed-(m,n) Kerr bands is literature input. Hawking's horizon topology theorem, which excludes hyperbolic horizons for asymptotically flat black holes, is also literature input.

## Limits of the no-go
- The ladder theorem concerns a whole tail of a progression. Sparse subsets of a band are not excluded.
- Perturbations must be ℓ², so a ladder on a fixed vertical line Re s ≠ ½ is not covered.
- Kerr with all m together is not excluded; only one fixed-(m,n) band at a time is.

## No-go closure
- **Exact killing theorem/mechanism:** `not_eventually_riemannZeta_critical_eq_zero_of_eikonal` and its round-horizon corollaries. The mechanism is Putnam's jump: the prime comb does not periodize to something with a one-sided spectrum, even up to ℓ¹ coefficients.
- **Strongest positive survivor:** `causalSymbol_qnmMinus_isPole`, `causalSymbol_qnmPlus_isZero`, `exists_excitationFactor` and `retardedTransform_dampedEchoKernel`.
- **New insight:** arithmetic can enter ringdown only through the horizon spectrum, since the radial operator is the same sech² barrier in both cases. The round spectrum is rigid. The causal symbol also splits the two continued branches: pole on ω₋, zero on ω₊.
- **Status:** dependency-closed in Lean as listed; the items under "Not formalized" remain paper or literature.
