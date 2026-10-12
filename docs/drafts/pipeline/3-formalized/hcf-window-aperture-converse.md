# HCF window ⇐ Weil aperture margin (converse dictionary)

**Route:** HCF. **Stage:** 3-formalized (MUST-1261).

## Statement (target)
Let B > 0 and μ > 0, and suppose the zero-side Weil form has margin μ at aperture B:
Re Σ_q û(z_q)·conj û(z̄_q) ≥ μ‖u‖²₂ for every smooth even u supported in [−B, B].
Then for every K < B²/c₀ (c₀ explicit), for all large n, Re H_{K/n}(P, P) > 0 for every nonzero P of
degree ≤ n. Hence Δ_k(K/n) > 0 for all k ≤ n + 1.

Together with MUST-1251 (an exponential-type witness of type B kills the window at K > (eB+1)²/4),
this makes the HCF window constant equal to the Weil aperture squared, up to constants.

## Proof plan (stages)
1. **Phase-space moments.** For v = P·e^{−πx²}, deg P ≤ d: ‖xv‖ ≤ (√d + √(d+1))/(2√π)·‖v‖, from 4πx = A + A†,
   ‖Av‖² ≤ ‖v‖‖Nv‖ and ‖A†v‖² ≤ ‖v‖‖(N+4π)v‖ (corpus `SchwartzOscillatorL2Bound`,
   `numberCLM_polyGauss_norm_le`). Iterate: ‖x^k v‖ ≤ ∏ c(d+i)‖v‖. Chebyshev then gives tails beyond
   X² ≳ (2d+2k+1)/(2π).
2. **Physical-space form of the HCF test.** G(z) = e^{−az²/2}p(z²) = û with u a degree-2n
   polynomial-Gaussian at scale √a (Hermite Fourier eigenfunctions, `fourierSCLM_hermiteSchwartz`).
3. **Truncation.** u_B = u·χ_B. The error E = G − û_B is bounded at complex z (|Im z| < 1/2) by
   ∫_{|x|>B'}|u|e^{|x|/2}, with 1/|z| decay after one integration by parts. It is e^{−cn}‖u‖ for
   B' > 2√K(1 + ε).
4. **Assembly under the margin hypothesis.** Re Z(G) ≥ μ‖u_B‖² − O(e^{−cn})‖u‖².
5. **Unconditional instance.** Use the CCM polar ground energy (μ₀ ≥ 1/20 at aperture
   ½(log 2 + 1/50), `one_twentieth_le_ccmRestrictedWeilPolarGroundEnergy_primeTwo`) on the hyperplane
   p(−1/4) = 0. Handle the pole direction by the constant test, H(1,1) = M₀(a) ≍ a^{−1/2}log(1/a).

## Status
- Stage 1: DONE [L]. `HTGeometry/PolynomialGaussianPositionMoments`: `norm_toLp_mulX_polyGauss_le` (‖xv‖ ≤ (√d+√(d+1))/(2√π)‖v‖) and `norm_toLp_polyGauss_X_pow_mul_le` (iterated moments); standard axioms.
- Stage 2: DONE [L] (`RHTower/XiGaussianHeatTestPhysicalSide`, `integral_heatPhysical_mul_cexp`, standard axioms). G(z) = e^{−az²/2}p(z²) = ∫ g(x)e^{ixz}dx with g = (2πa)^{−1/2} Σ p_k(−1)^k ∂^{2k}e^{−x²/(2a)}. Proof by integration by parts from Mathlib `fourierIntegral_gaussian` at complex t.
- Stage 3 constants: with x = √(2πa)y, the tail ∫_{|x|>X}|g|² ≤ ((6n+1)·K/(nX²))^n ‖g‖² (k = n moments), so the truncation aperture needs X² > 6K(1+ε). For the 1/|z| decay over zeros, integrate by parts once.
- Unconditional target (5a): from the polar margin (μ₀ ≥ 1/20 at A₁ = ½(log 2 + 1/50)), on p(−1/4) = 0, for K < A₁²/6 (asymptotically) the section has negIndex ≤ 1. The non-explicit unconstrained margin (`exists_suzukiSmallAperture_ccmGroundEnergy_pos`) gains nothing over κ.
- Paper: stages 1–4 sketched (ledger rows 530, 570, 574). Stage 5's pole coupling is an [OPEN CORE].

- Stages 3–5: DONE [L] (2026-10-11). Sharp constant: **K < A²/4** (A = source half-width), not B²/6.
  `RHTower.eventually_le_re_heatHankel_of_polarGroundEnergy`: μ₀(A) > 0, 4K < A² ⇒ for large n, all
  a ≤ K/n, all real P of degree ≤ n with P(−1/4) = 0, Re H_a(P,P) ≥ (μ₀/4)∫g². Pole coupling resolved
  by the correction u = (g − κ)χ, κ = ∫gχe^{x/2}/∫χe^{x/2}, which is small because ∫g e^{x/2} = G(−i/2) = 0.
  The sharp constant comes from moment order k = 2(⌊n/m⌋ + 1) with m large.
- Unconditional (5a): `RHTower.eventually_re_heatHankel_pos_primeTwo` and
  `eventually_hermNegIndex_heatMomentSection_le_one_primeTwo`, window aN ≤ 1/32 (> 16κ), at most one
  negative square.
- Open: (i) the pole direction (needs an explicit unconstrained margin); (ii) the sharp witness
  direction K > A²/4 (MUST-1251 has (eA+1)²/4 from the Taylor truncation; Hermite approximation of a
  Weil-negative source would give A²/4). With (ii) the dictionary would be exact: window constant = A*²/4.
- C591 (MUST-1264): RH ⟺ all windows positive on the pole hyperplane; hence (∀A, μ₀(A) > 0) ⇒ RH through HCF. `RHTower/XiGaussianHeatPoleHyperplaneCriterion`.
