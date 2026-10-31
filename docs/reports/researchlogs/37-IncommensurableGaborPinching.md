# 37 IncommensurableGaborPinching — mathematical facts log

## DisjointPairSchurSlack (uses Zeta23.Assembly.SeamMult, Zeta23.ZeroSide.RankTraceMult: Lemma R `rank_trace_mult_k`, `kc`, `Pmat`, `xsq`, ZeroBlockData, Seam A)
- Context: Zeta23 Lemma R bounds 2c·tr(P+Q) − ‖P+Q‖_F² ≤ Σ_j k_c(m_j) + c²b (P = WWᴴ on-line Gram, Q Hermitian with posIndex ≤ b), k_c(t) = c² − ((c − t)₊)², discarding the off-diagonal Schur–Jensen pinching slack.
- rot_outer_eq: real 2×2 rotation (α² + β² = 1) of (u, w) preserves uu* + ww* pointwise. exists_unit_rot_scalars: rotation diagonalizing a real symmetric 2×2 block exists ((α²−β²)(A−B) + 4αβρ)² = (A−B)² + 4ρ².
- vecSq, realInnerVec (Re⟨u,w⟩); rotation expansion of norms.
- exists_unit_rot_kc: c ≥ 2, ‖u‖², ‖w‖² ≤ 1 ⇒ rotated pair stays on the quadratic branch of k_c (no kink crossing, sum ≤ 2 ≤ c) and k_c(‖u'‖²) + k_c(‖w'‖²) + 2Re⟨u,w⟩² ≤ k_c(‖u‖²) + k_c(‖w‖²) (A'² + B'² = A² + B² + 2ρ²).
- exists_disjointPairs_rot: simultaneous rotations on pairwise disjoint unit-multiplicity pairs, P unchanged.
- rank_trace_mult_k_disjointPairs: 2c·tr(P+Q) − ‖P+Q‖_F² + 2Σ_{p∈r}Re⟨v_{x_p}, v_{y_p}⟩² ≤ Σ_j k_c(m_j) + c²b (c ≥ 2, pairwise disjoint simple pairs).
- mult_two_disjointPairs / mult_three_disjointPairs: block bounds (c = 2: ≤ s₁; c = 3: ≤ 2|ι|) with slack 2Σ(c₀⁻¹Σ_k Re v_x Re v_y)² on S₁ (simple on-line zeros, real vectors on the line).
- pairGridOverlap (aL²)⁻¹Σ_k φ̂_R(γ_x − τ_k)φ̂_R(γ_y − τ_k); seamA_mult2_disjointPairs / seamA_mult3_disjointPairs: Seam A bounds (counts N0s, Nd of simple/distinct critical zeros) with explicit disjoint-pair Gram slack retained. Inputs PhiHatConj, PhiHatReal, PoissonSq, TailInputs are hypotheses of Zeta23's parameter packages.

## CosineKernelNonLatticeFloor (uses RHTower WindowTransformSamplingParseval; Zeta23.ThmD.ParamsD: vStar, aStar, theta, phiD, sharpW, AdmWindow, TaperProfile, Params.atD)
- Montgomery–Taylor untapered cosine profile v*_λ(v) = cos(√2λv) on [−1/2,1/2]; mtKernelNum = ∫v*_λ(v)cos(2πΔv); mtKernel K_λ(Δ) = mtKernelNum/aStar. Even in Δ.
- λ ∈ [0,1]: v*_λ ∈ [1/2, 1], aStar ∈ [1/2, 1], |mtKernelNum| ≤ aStar, |mtKernelNum| ≤ |K_λ|.
- Closed form (Δ ≥ 2/5): ((πΔ)² − θ²)·num = πΔ cos θ sin(πΔ) − θ sin θ cos(πΔ), θ = λ/√2.
- Enclosures for λ ∈ [999/1000, 1]: cos θ ∈ [3/4, 0.77], θ sin θ ∈ [0.45, 0.47]; cos t ≤ 1 − t²/2 + t⁴/24.
- one_div_250_le_abs_mtKernel: λ ∈ [999/1000, 1], Δ ∈ [0,3] \ (I₁ ∪ I₂), I₁ = (26/25, 43/40), I₂ = (503/250, 256/125) ⇒ |K_λ(Δ)| ≥ 1/250 (11-subinterval case analysis). Unlike sinc (zeros on ℤ∖{0}), zeros of K_λ lie in two narrow non-lattice intervals.
- Sumset disjointness: 2·(26/25) > 256/125 and 26/25 + 503/250 > 3 ⇒ exists_pair_mtKernel_ge_of_triple: any triple γ₁ < γ₂ < γ₃ with α(γ₃ − γ₁) ≤ 3 has a pair with |K_λ(α(v−u))| ≥ 1/250.
- AdmWindow: φ' vanishes for |u| ≥ L/2; |φ'| ≤ c/w (FTC from ‖φ''‖₁ ≤ c/w); grid tail Σ_{far k} v̂_R(γ − τ_k)² ≤ 4L²(c/w)²/T via Parseval of φ' (sum_norm_sq_paperFT_grid_le) when (γ − τ_k)² ≥ T/4.
- VPhiR_phiD_close: |L⁻¹VPhiR(phiD) − mtKernelNum(LΔr/2π)| ≤ 2w/L (taper vs sharp window L¹ comparison).
- eventually_pairGridOverlap_atD_close: for valid P, eventually in T, all bulk pairs (ordinates in [T + √T, 2T − √T]): |pairGridOverlap − K_λ((L/2π)|γ_x − γ_y|)| ≤ 1/500 (grid truncation ≤ 1/1000 + taper/normalization ≤ 1/1000).

## CriticalLineZeroProportion (uses RHTower HorizontallyIsolatedSimpleZeros, ZetaOffLineMomentMontgomeryTaylor; Zeta23 Theorem D: HD, GD, cStar, thmD_mult_lam_abstract, PaperInputs, paperInputs_zeta, zetaZeroConfig)
- Alpöge–Furman Theorem D (Zeta23): simple critical-line proportion ≥ HD(1) = 3/2 − cot(1/√2)/√2 ≈ 0.6725007036, distinct ≥ GD(1) = (HD(1)+1)/2. Their rank–trace inequality bounds P₁ = Σ_{S₁}w_zw_zᵀ only by ‖P₁‖_F² ≤ tr P₁ ≤ s₁, equality iff evaluation vectors pairwise orthogonal.
- Boxcar sinc allows orthogonality on a lattice; MT cosine kernel cannot: no three simple critical ordinates in a short window (α(γ₃ − γ₁) ≤ 3) are mutually orthogonal.
- exists_disjoint_short_triples: m ≥ 3 increasing reals in [a,b], α > 0 ⇒ R ⊆ {0..m−3}, pairwise 3-separated, 9|R| ≥ 3(m−2) − 2α(b−a), each α(g(j+2) − g(j)) ≤ 3 (telescoping two-step spans ≤ 2α(b−a); best residue class mod 3).
- S₁Bulk: simple on-line zeros with ordinate in (T + √T, 2T − √T]; N0s(T,2T) ≤ |S₁Bulk| + boundary strips; boundary = O(√T log T) = o(N(T,2T)) (Riemann–von Mangoldt local count); L·T/2π ≤ N(T,2T) eventually for λ < 1.
- HD Lipschitz: HD(1) − HD(λ) ≤ 56π²(1 − λ) on [1/2,1] (cStar Lipschitz 14, cStar ≥ 1/(2π)).
- eventually_exists_disjointPairs_slack: P valid, λ ∈ [0.999999, 1): eventually, disjoint pairs in S₁ with 2Σ pairGridOverlap² ≥ 10⁻⁸N(T,2T) (HD(λ) ≥ 0.6718 ⇒ |S₁Bulk| ≥ 0.6716N ⇒ ≥ N/625 disjoint short triples; each yields a pair with |K_λ| ≥ 1/250 ⇒ |overlap| ≥ 1/500).
- thmD_mult3_count_of_seam: abstract c = 3 seam consumer ⇒ (3/2 − c⁻¹/2 − ε)N ≤ Cnt3 eventually. thmD_beyond_lam_abstract: simple proportion ≥ HD(λ) + 10⁻⁸, distinct ≥ GD(λ) + ½·10⁻⁸ (slack enters c = 2, c = 3 seams with positive sign).
- Flagship (unconditional, ζ): beyond_HD_one_simple_critical_dyadic/cumulative: (HD(1) + 10⁻⁸ − ε)N ≤ N0simple; beyond_HD_one_critical_dyadic/cumulative (also N0star, N0, Nsimple); beyond_GD_one_distinct_dyadic/cumulative: (GD(1) + ½·10⁻⁸ − ε)N ≤ Ndist.
- HD_one_ge_67250070 (degree-20 Taylor enclosures at 2^{−1/2}); simple_critical_proportion_ge_67250071: proportion ≥ 0.67250071 − ε.
- Transport to project ξ census: beyond_montgomeryTaylor_xiSimpleCritical_epsilon, beyond_montgomeryTaylor_xiDistinct_epsilon; HD_one_add_pos_le_liminf_xiSimpleCriticalRatio: HD(1) + 10⁻⁸ ≤ liminf N₀ˢ(T)/N(T).
