# HCF sharp witness: Weil-negative source of half-width A' ⇒ window K fails for every K > A'²/4

**Route:** HCF. **Stage:** 1-in-progress. **Goal:** make the window/aperture dictionary exact. With MUST-1261,
the pole-hyperplane window threshold K* would equal A*²/4, where A* is the even pole-vanishing Weil threshold.

## Statement
Let u be an even real smooth source with support in [−A', A'], ∫u e^{x/2} = 0 and Weil energy Re Σ_q F_u(z_q)² < 0.
If 4K > A'², then for all large n there is a real P of degree ≤ n, P(−1/4) = 0, with Re H_{K/n}(P,P) < 0.

## Proof
1. **Coherent states.** At unit scale (gauss e^{−πx²}, annihilation B = 2πx + ∂), ψ_y(x) = e^{−π(x−y)²}
   satisfies Bψ_y = 2πy ψ_y. Since B† = A and A h_j = √(4π(j+1)) h_{j+1}, the coefficients satisfy
   c_{j+1}√(4π(j+1)) = 2πy c_j, so |c_j|² = |c_0|²(πy²)^j/j!. Parseval gives |c_0|² = ‖ψ_y‖²e^{−πy²}.
   The Hermite energy of ψ_y is Poisson(πy²)-distributed.
2. **Scale.** At width a (Gaussian e^{−x²/(2a)}, s² = 2πa), the translate G_a(·−y) has Poisson parameter
   λ(y) = y²/(2a). Truncation at degree 2n with a = K/n gives λ ≤ A'²n/(2K) = 2nθ, θ = A'²/(4K) < 1. The tail is
   exponentially small (Chernoff).
3. **Superposition.** u_a = G_a * u has coefficients c_j(u_a) = ∫u(y)c_j(ψ_y)dy. By Cauchy–Schwarz in y,
   Σ_{j>2n}|c_j(u_a)|² ≤ ‖u‖₁ ∫|u| Σ_{j>2n}|c_j(ψ_y)|² ≤ ‖u‖₁² sup_{|y|≤A'} tail. The same holds with weight j, for ∂.
4. **Heat test.** g_n = Π_{2n}u_a = Q e^{−x²/(2a)} with Q even and real of degree ≤ 2n, so g_n = heatPolyR a P_n
   (heatPolyR is a bijection from degree ≤ n onto even degree ≤ 2n).
5. **Zero sums.** ‖z‖‖F_{g_n} − F_{u_a}‖ ≤ ∫|(g_n − u_a)'|e^{|x|/2} ≤ √(2eπ∫((g_n−u_a)')²e^{x²}).
   Split at X with 2√K < X: the inside is bounded by e^{X²}·tail, and the outside by the polynomial–Gaussian
   tail lemma plus the Gaussian tail of u_a. Then Σ F_{g_n}² − Σ F_{u_a}² → 0, and Σ F_{u_a}² → Σ F_u² < 0.
6. **Pole.** P_n(−1/4) ∝ F_{g_n}(i/2) → F_u(i/2) = 0 exponentially. Subtract the constant as in MUST-1264.

## Status
- Paper: complete (steps 1–6); constants explicit.
- Lean Stage 1 DONE: `HTGeometry/HermiteCoherentPoisson` (annihilation eigenvector, geometric pairings,
  ‖h_n‖² = n!/πⁿ‖h_0‖², Poisson law, orthonormal Parseval, tail Parseval, sharp Poisson tail
  (θe^{1−θ})^N/(1−θ)).
- Lean Stage 2 DONE: `HTGeometry/HermiteGaussianSmoothingTail` (Fubini for f ⋆ ψ_0, coefficient superposition,
  tail ‖w − Π_N w‖² ≤ ‖f‖₁²‖ψ_0‖²(θe^{1−θ})^N/(1−θ) when πT² ≤ θN; truncation = polyGauss of an even real
  polynomial of degree < N).
- Lean Stages 3–5 DONE: `RHTower/XiGaussianHeatSourceSmoothing` (F_{u_a} = e^{−az²/2}F_u),
  `RHTower/XiGaussianHeatTestPolynomialBasis` (heatPolyR onto even degree ≤ 2n), `RHTower/XiGaussianHeatSharpWitnessSetup`,
  `…Estimates`, `…Comparison`, `RHTower/XiGaussianHeatSharpWitness` (per-time comparison with pole correction),
  `…Asymptotics`, `RHTower/XiGaussianHeatSharpWitnessTheorem` (final theorem
  `eventually_exists_poleHyperplane_heatHankel_neg_of_source`), `RHTower/XiGaussianHeatWindowThresholdLaw`
  (`heatWindowNonneg_threshold`). MUST-1274. Standard axioms. Card ready for 3-formalized.
- Simplification over the paper plan: the derivative of the difference is not needed.
  Σ|F_g² − F_w²| ≤ N(g − w)(N(g'') + N(w''))Σ|z_q|^{−2}, using |z|²|F_f| ≤ N(f'').
