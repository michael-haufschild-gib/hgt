# Reverse Twisted-Arc Duality on the `2 × 2` Pole-Compression Matrix

This directory formalizes **Mechanism 4 (Reverse Twisted-Arc Duality on the `2 × 2`
Pole-Compression Matrix)** from `docs/reports/review-2110/argon.md` (§1.5):

1. [`TwistedArcShiftedGammaPoleProjection.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ReverseTwistedArcPoleCompression/TwistedArcShiftedGammaPoleProjection.lean):
   - **Shifted-Gamma Numerical Range Lower Bound (`shifted_gamma_numerical_range_and_gauss_series`):**
     For every shift `σ ∈ (0, 1)` and frequency `x : ℝ`, the real part of the shifted Gamma jump
     symbol `wallSymbol σ x` is bounded below uniformly by `-gammaShiftKappa σ` and expands into the
     two-sided real Gauss series.
   - **Logarithmic-to-Multiplicative Pole Projection & Prime-Blind Cusp Identity
     (`prime_blind_cusp_pole_identity_log_profile`, `twisted_arc_cusp_defect_bound_and_tendsto`):**
     Under the isometric half-line substitution `y = e^u` mapping `F : ℝ → ℝ` to
     `f(y) = F(log y) y^{-1/2}` on `(0, ∞)`, the two multiplicative pole functionals
     `∫_0^∞ f(y) dy` and `∫_0^∞ (f(y)/y) dy` coincide with `∫_ℝ F(u) e^{u/2} du` and
     `∫_ℝ F(u) e^{-u/2} du`. When `A_f` is blind to all prime powers `n ≥ 2`, the cusp functional
     `C A_f(0) = Ψ_f(0)` equals `2 (∫_ℝ F(u) e^{u/2} du) (∫_ℝ F(u) e^{-u/2} du)`, and its
     twisted-arc defect `(1 - e^{-ε}) Ψ_f(0)` vanishes linearly as `ε → 0⁺`.
   - **Truncated `Ξ`-Divisible Riemann-Kernel Zero Annihilation & Parity Involution
     (`truncated_riemann_kernel_zero_annihilation_and_parity`,
     `parityCoeff_involutive_and_eigenchannels`):**
     Every finite derivative combination `kernelComb a` vanishes at `γ_ρ` and `conj(γ_ρ)` for every
     nontrivial zero `ρ`, its smooth truncation `nearRadicalTest L a` obeys the explicit tail-leakage
     bound, and `parityCoeff` splits the coefficient space into even and odd eigenchannels.

2. [`ParitySplitNullPoleDuality.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ReverseTwistedArcPoleCompression/ParitySplitNullPoleDuality.lean):
   - **Exact Parity Decomposition of the Bilinear Pole Form
     (`pole_of_decayBound_eq_two_mul_cosh_sq_sub_sinh_sq`):**
     `2 (∫ F e^{-u/2}) (∫ F e^{u/2}) = 2 ((∫ F cosh(u/2))^2 - (∫ F sinh(u/2))^2)`.
   - **Three-Way `Ξ`-Divisible Parity Pole Basis & Two-Sided Rigidity
     (`xiDivisible_two_by_two_pole_channel_decomposition`):**
     - `xiShiftedGammaTest 0` is a pure even-pole mode (`∫ F₀ cosh(u/2) = 1/2`,
       `∫ F₀ sinh(u/2) = 0`, pole pairing `+1/2`, forcing `β ≥ 1`),
     - `oddNullTest` is a pure odd-pole mode (`∫ oddNullTest cosh(u/2) = 0`,
       `∫ oddNullTest sinh(u/2) = 1/8`, pole pairing `-1/32`, forcing `β ≤ 1`),
     - `depthNullTest (1/2)` lies in the polar-orthogonal kernel (`∫ depthNullTest(1/2) cosh(u/2) = 0`,
       `∫ depthNullTest(1/2) sinh(u/2) = 0`, forcing `c^2 = 1/4`).

3. [`PoleCompressionTwistedArcBridge.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ReverseTwistedArcPoleCompression/PoleCompressionTwistedArcBridge.lean):
   - **Twisted-Arc Singleton Cone Criterion (`weilPositiveFull_iff_weilPoleCompression_and_eq_vonMangoldt`):**
     `WeilPositiveFull lam ↔ (∀ a, |ccmWeilPoleCross a| ≤ ccmWeilPoleDiagonal a) ∧ (∀ n ≥ 2, lam n = Λ(n))`.
   - **Five-Way Equivalence of `2 × 2` Pole Compression (`poleCompression_five_way_equivalence`)**
     and **Positive-Trace & Opposite-Curvature Wall-Crossing Dichotomy
     (`exists_threshold_poleCompression_trace_pos_and_opposite_curvatures`)**.

4. [`MasterReverseTwistedArcPoleCompressionTheorem.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ReverseTwistedArcPoleCompression/MasterReverseTwistedArcPoleCompressionTheorem.lean):
   - **Shifted-Gamma Pole Series Collapse (`tsum_shiftedGamma_pole_eq_half_mul_zero`)**,
   - **Explicit Twisted-Arc Prime-Blind Weight Sequence & Pole Limit
     (`exists_twistedArc_weights_vonMangoldt_blind_and_pole_limit`)**,
   - **Coupled Prime-Polynomial vs. `2 × 2` Pole Compression
     (`poleCompression_iff_primePolynomial_le_archPart`)**, and
   - **Master Synthesis (`reverse_twisted_arc_pole_compression_master_theorem`)**.
