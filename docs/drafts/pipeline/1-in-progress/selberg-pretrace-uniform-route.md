# Selberg: point-pair invariants, pretrace inequality, uniform congruence gap

- **ID:** SELBERG-PRETRACE-UNIFORM
- **Stage:** 1-in-progress
- **Type:** CANDIDATE (programme)
- **Source:** No-go on `3-formalized/selberg-strip-hardy-gap.md`: strip/cusp energy cannot reach uniform level.
- **Statement:** Build, unconditionally in Lean, Selberg's mean-value theorem for Laplace eigenfunctions on ℍ,
  the pretrace inequality for congruence subgroups, the SL₂(𝔽_p) dimension bound, and lattice counting, then
  prove a level-uniform lower bound λ₁(Γ(p)) ≥ c > 0 (Sarnak–Xue type). Then attack improving c toward 1/4.

## Why this route
Cusp energy is capped (card above). A uniform bound has to use the congruence structure: the eigenspace of an
exceptional λ is an SL₂(𝔽_p)-representation with no invariant vectors, so it has dimension ≥ (p−1)/2 (the
T-eigenvalues ζ, ζ^{a²} are all present). The pretrace inequality plus counting in Γ(p) bounds the multiplicity above.

## Step 1 — mean-value theorem without Legendre functions (paper proof)
- k_θ = [[cos θ, sin θ], [−sin θ, cos θ]] fixes i; d/dθ (k_θ·z) = 1 + (k_θ·z)².
- For C² G and h(φ) = G(k_φ·iy): h''(0) = (1−y²)²∂ₓ²G(iy) + 2y(1−y²)∂_yG(iy).
- For an eigenfunction F (Δ = −y²(∂ₓ²+∂ᵧ²), ΔF = λF), with g(y) = (1/2π)∫_0^{2π} F(k_θ·iy)dθ,
  averaging (periodicity kills ∫h'') gives ((y²−1)g')' = −λ(y²−1)g/y² on y ≠ 1, hence
  (y²−1)g'(y) = −λ∫_1^y (t²−1)g(t)/t² dt for all y > 0.
- Uniqueness: if g(1) = 0 then |g'(y)| ≤ |λ|·max(1, y⁻²)∫|g| between 1 and y; stepwise Gronwall gives g ≡ 0.
- ω_s := rotation average of (Im z)^s, λ = s(1−s). The rotation average of F − F(i)·(Im)^s-average vanishes on
  the axis, hence everywhere (every point is k_θ·iy). So Avg_K F = F(i)·ω_s.
- Point-pair: for k ∘ d(i,·) integrable and K-invariance of dμ, ∫ k(d(i,w))F(w)dμ = F(i)∫ k(d(i,w))ω_s(w)dμ.

## Log
- 2026-09-24 — opened after the strip-energy no-go. Step 1 paper proof complete; Lean in progress.
- 2026-09-24 — Step 1 core closed in Lean: `formal/GaloisForLFunctions/RHTower/HyperbolicRotationMean.lean`.
  `orbit_identity` (pointwise conformal-trace identity), `rotAverage_ode`, `radial_unique` (Gronwall on
  [1,∞)), `rotAverage_inv` (A(1/y) = A(y)), and `rotAverage_eq_smul`: two real-C² eigenfunctions with the
  same λ ∈ ℂ have proportional rotation averages about i. Build green; axioms propext/choice/Quot.sound.
  Wired into `RHTower.lean`. Next: K-invariance of the hyperbolic measure and the point-pair integral
  ∫ k(d(i,w))F(w)dμ = F(i)·ĥ(λ); then general centres via GL⁺ transport; then the pretrace inequality.
- 2026-09-24 — Point-pair principle closed: `formal/GaloisForLFunctions/RHTower/HyperbolicPointPair.lean`.
  `exists_rot_axis` (every point lies on a rotation orbit through the imaginary axis), `kAverage_rot`,
  `two_pi_integral_eq_kAverage` (GL(2,ℝ)-invariance of the hyperbolic measure + Fubini),
  `kAverage_eq_smul`, and `integral_kernel_eigen`: for rotation-invariant φ and eigenfunctions G, E with the
  same λ, ∫φG = (G(i)/E(i))∫φE. Build green, axioms propext/choice/Quot.sound. No heartbeat options used;
  a slow elaboration was fixed by a direct coordinate continuity lemma (`continuous_rot_smul_of`).
  Next: reference eigenfunction E = (Im z)^s; transport to arbitrary centres by GL⁺; pretrace inequality on
  Γ\ℍ (unfolding over a fundamental domain); SL₂(𝔽_p) dimension bound; counting in Γ(p).
- 2026-09-24 — Selberg transform at i closed: `formal/GaloisForLFunctions/RHTower/HyperbolicPowerEigen.lean`.
  `powerEigen_smooth`, `powerEigen_laplacian` (Δ(Im z)^s = s(1−s)(Im z)^s), and
  `integral_kernel_eq_selbergTransform`: ∫φG = G(i)·∫φ·(Im)^s for every eigenfunction G with eigenvalue
  s(1−s) and every rotation-invariant φ. Build green; axioms propext/choice/Quot.sound. Step 1 complete.
