# Imaginary-energy law for the cosine step

- **ID:** CSS+
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** producer-loop-opus-2026-10-12.md rows 61, 64, 68–79, 85, 94–97 (positive survivor of the heat depth-budget no-go, `HTGeometry/PolynomialHeatDepthBudgetFailure`)
- **Statement:** For a real polynomial p and a > 0, V(cos(aD)p) ≤ Σ_{roots r of p, Im r > a} ((Im r)² − a²), where V(q) = Σ_{roots w of q, Im w > 0} (Im w)².

## Goal
An exact Lyapunov law for the cosine step cos(aD)p = (p(z+ia) + p(z−ia))/2. It strengthens de Bruijn's strip theorem (sup-form) to an energy (ℓ²) form. Together with the corpus depth budget (`nonrealRootCount_shiftAvg_le`) it gives CSS: V(A) + a²·m(A) ≤ V(p). Through cos(√(2τ/n)D)^n → e^{−τD²} it contains the heat law dV/dτ ≤ −2m. No RH content; it is polynomial root dynamics.

## Gates
- [x] 0 → 1  in-progress: well-posed, mechanism (de Bruijn dipole sign X + v² + a² − y²), proven cases
- [x] 1 → 2  fully-proven: general p, top-j (row 141: matrix realization + Ky Fan)
- [x] 2 → 3  formalized: `HTGeometry/CosineStepHeightMajorization` (`sum_roots_shiftAvg_im_sub_pos_le`, `sum_roots_shiftAvg_sq_im_le`), standard axioms
- [ ] 3 → 4  publication-ready

## Proven
- **[L] one deep pair, any degree:** `HTGeometry/PairTimesRealRootedCosineStep`. For p = ((X−x)²+y²)·g·∏(shallow pairs y_j² ≤ a²), g real-rooted, every root w with Im w > 0 satisfies (Re w − x)² + (Im w)² + a² ≤ y² (`sq_add_sq_add_sq_le_of_shiftAvg_pair_mul_shallow_root`).
- **[L] two pairs, quartic:** `HTGeometry/QuarticTwoPairCosineStep`. The resolvent bound u² ≤ ξ² + 2a², i.e. V₁ + V₂ ≤ Y₁ + Y₂ − 2a² (`add_le_of_evenQuarticStep_twoPair`).
- **[L] all real cubics:** `HTGeometry/CubicCosineStepEnergy`.
- **[L] degree-4 extremality:** `HTGeometry/VerticalShiftEnergyQuarticFamily`. Among vertical averages E p(z+iX) with m₂² ≤ m₄, the cosine step is extremal; a single Laguerre step violates the law.
- **[paper] all real quartics** (the cases above plus localisation of a single surviving root to D₁ ∪ D₂).
- **[L] disc localisation, any number of pairs:** `exists_disc_of_shiftAvg_pairs_root` (each surviving root lies in some disc (Re w − x_k)² + (Im w)² + a² ≤ y_k²).
- **[paper] heat analogue with weak majorisation (loop row 119):** for e^{−τD²}p, the sum of the j largest squared heights is ≤ Σ_{i≤j}(y_(i)² − 2τ)_+ for every j. Mechanism: under ż_i = 2Σ(z_i−z_k)^{−1} everything outside the top-j set pulls it down, and pairs inside cancel by symmetry, so D⁺E_j ≤ −2min(j, m); then a barrier argument by induction on j. Lean needs root-ODE infrastructure; alternative route via corpus heat steps + Hurwitz (`PolynomialHeatNonrealCount`) needs a uniform per-step error bound (loop row 127).

## Falsified strengthenings
Layered matching; subadditivity over factors SUB (already false for one inserted real root: a far root at c moves a surviving root by κ/c with Im κ ≠ 0 for asymmetric f, e.g. (z²+1)(z−r₀)); first-order step p + λp′; Laguerre step p − cp″ (c ∈ (2/5, ½)); doubly-stochastic Cauchy weights (complex case); finite free convolution with arbitrary real-rooted q; convexity in Y of the pencil energy.

## Master conjecture
Cosine top-j: the squared heights of the upper roots of cos(aD)p are weakly submajorised by (y_(i)² − a²)_+. It implies the heat top-j law through e^{−τξ²} = lim cos(√(2τ/n)ξ)^n, since weak submajorisation is preserved by x ↦ (x − a²)_+ (loop row 133). j = 1 is the [L] disc theorem.

## Open core
At least two pairs with Im > a in degree ≥ 5. Equivalent horizontal-spread form: X_A − X_p ≤ a²(n(n−1) − 2N_deep) − 2Σ_shallow y², with X = Σ (Re root)². Equality cases: single pair; resonant pairs (vertical separation exactly 2a, frozen roots). Candidate route: RIC pencil monotonicity (dV/dY ≤ 1[Y > a²]); SUB is false.

## Log
- 2026-10-13 — card created from the producer-loop survivor rows; Lean modules listed above.
- 2026-10-13 — heat-CSS+ with top-j majorisation proved on paper (loop row 119).
- 2026-10-13 — SUB falsified (loop row 107); disc localisation for any number of pairs added in Lean (`exists_disc_of_shiftAvg_pairs_root`).

## Proof of the master conjecture (paper, 2026-10-13, loop row 141)
**Theorem (cosine majorisation).** Let p be a real polynomial, a > 0, and let h_1 ≥ h_2 ≥ … be the imaginary parts of the roots of cos(aD)p in the open upper half-plane (with multiplicity). Let ρ_1 ≥ ρ_2 ≥ … be √(y_j² − a²) over the roots x_j + iy_j of p with y_j > a. Then for every σ ≥ 0, Σ_i (h_i − σ)_+ ≤ Σ_j (ρ_j − σ)_+. Equivalently the heights are weakly submajorised by the ρ_j. Squaring (x ↦ x² is convex and increasing) gives the squared-height majorisation and CSS+.

**Realization.** Write E(z) = p(z + ia), so cos(aD)p = (E + E^#)/2 = Re E on ℝ. Factor E as a product of
- pair factors (z − x_j)² + R_j + i c_j (z − x_j) with R_j = y_j² − a² > 0, c_j = 2a (deep pairs), and
- linear factors z − s_k + i t_k with t_k ≥ 0 (real roots: t = a; a shallow pair splits into t = a ∓ y_j).
Let g = (√c) on the positive coordinates (one per pair, one per linear factor) and K_{uv} = i·sgn(v − u)·g_u g_v (Hermitian, zero diagonal). Put
T = [[A, B], [−Bᴴ, D]], A = diag(x_j, s_k) + K, D = diag(x_j), B_{p_j, n_j} = √R_j (zero otherwise).
Then det(z − T) = Re E(z). Proof: Schur complement on D gives det(z − D)·det(diag(e) − K) with e_j = z − x_j + R_j/(z − x_j), e_k = z − s_k; and the sign-Pfaffian identity det(diag(λ) − K) = (∏(λ_u + i g_u²) + ∏(λ_u − i g_u²))/2 (all-ones Pfaffians are 1; or induction on the affine family det(Y + ν g gᵀ)).

**Ky Fan step.** Re T = diag(A, D) and Im T = [[0, −iB], [iBᴴ, 0]], whose quadratic form is 2Σ_j √R_j Im(ū_{p_j} u_{n_j}). Schur-triangulate Uᴴ T U = upper triangular; Im λ_i = ⟨Ue_i, Im T·Ue_i⟩. For S = {i : Im λ_i > σ}, Π = U P_S Uᴴ is an orthogonal projection, so w_j := 2|Π_{n_j p_j}| ≤ min(1, Π_{p_j p_j} + Π_{n_j n_j}) and Σ_j w_j ≤ |S|. Hence Σ_{i∈S}(Im λ_i − σ) ≤ Σ_j w_j √R_j − |S|σ ≤ Σ_j w_j(√R_j − σ) ≤ Σ_j (√R_j − σ)_+.

**Exact defect identity.** V(cos(aD)p) = Σ_j R_j − ½(‖Re T‖_F² − Σ_λ (Re λ)²). The card's horizontal-spread form is Schur's inequality Σ(Re λ)² ≤ ‖Re T‖_F² for this T; e.g. two pairs on one vertical have defect |K_12|²·… = 4a².

**Extensions.** Pair-dependent shifts (c_j arbitrary ≥ 0, R_j > 0) and arbitrary extra lower-half-plane roots are covered by the same T; phases Re(e^{iθ}E) follow by a far linear factor and Hurwitz. Iterating squared-height majorisation (x ↦ (x − a²)_+ is convex increasing) and the limit cos(√(2τ/n)D)^n → e^{−τD²} gives the heat top-j law of row 119 without the root ODE. The height (unsquared) form does not iterate (√(t² − a²) is concave).

## Lean (2026-10-13, loop row 141; all standard axioms, wired into `HTGeometry.lean`)
- `HTGeometry/SignCouplingDeterminant`: `det_diagonal_sub_signCoupling` — det(diag λ − K) = (∏(λ + i g²) + ∏(λ − i g²))/2 for the sign coupling K_{uv} = i·sgn(v − u)·g_u g_v; via the affine family `det_signFamily`.
- `HTGeometry/PairCoupledImaginaryKyFan`: `sum_roots_charpoly_im_sub_pos_le` — if Im⟨x, Tx⟩ = Σ_j 2 r_j Im(x̄_{p_j} x_{q_j}) (p, q injective, disjoint), then Σ_λ (Im λ − σ)_+ ≤ Σ_j (r_j − σ)_+ for σ ≥ 0 (Schur triangulation from `HTGeometry/SchurTriangulation`).
- `HTGeometry/RealPartProductRealization`: `realPartMatrix`, `charpoly_realPartMatrix` (charpoly = (E₊ + E₋)/2 for pair factors (z − x)² + R + i c (z − x), R any real, and linear factors z − s + i t), `im_star_dotProduct_realPartMatrix`, `sum_roots_realPart_im_sub_pos_le` (pair-dependent shifts and arbitrary lower roots: the generalized law).
- `HTGeometry/CosineStepHeightMajorization`: `sum_roots_shiftAvg_im_sub_pos_le` (height majorization for cos(aD)p, p = κ∏((X − x_j)² + y_j²)∏(X − r_k)), `sum_roots_shiftAvg_sq_im_le` (CSS+: Σ_{Im w>0}(Im w)² ≤ Σ_j (y_j² − a²)_+), `sum_sq_le_of_forall_sum_max_sub_le` (weak majorization ⇒ squares, by ∫₀^M (h − σ)_+ dσ = (h⁺)²/2).

## Remaining (not RH-bearing)
Heat top-j in Lean via iterated cosine steps + Hurwitz limit (needs factorization of the intermediate polynomials into `pairRootPoly` form; convex map (·−a²)_+ preserves squared majorization). Phase version Re(e^{iθ}E) via a far linear factor.
- 2026-10-13 — extensions in Lean: `HTGeometry/CosineProductSquaredMajorization` (any real polynomial; products of cosine steps, budget Σa_k²) and `HTGeometry/HeatFlowSquaredMajorization` (`sum_roots_polyHeat_sq_sub_le`: heat flow, budget 2τ, every threshold), with the reusable `HTGeometry/PolynomialRootSumSemicontinuity`. The "Remaining" heat item above is done.
