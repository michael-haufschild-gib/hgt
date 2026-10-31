# ArithmeticKunnethTheory working log (mathematical facts)
Namespace GaloisForLFunctions.ArithmeticKunnethTheory. 3 modules.
## ProductReceiversSeeDepthOnlyThroughTotalLength (Mathlib only)
- Product receiver: measure μ on ℝ^k, weight Φ ∈ L¹(μ); productResponse R(z) = ∫Φ(x)e^{⟨z,x⟩}dμ; tested against T^{⊠k}, T(x) = Σ_ρ e^{(ρ−½)x}, z_j = ρ_j − ½. totalLength x = Σ|x_j|.
- |e^{Σz_jx_j}| ≤ e^{Σ|Re z_j||x_j|} ≤ e^{δ·totalLength} when all |Re z_j| ≤ δ.
- PILLAR depth–length conservation (norm_productResponse_le): Φ supported a.e. on totalLength ≤ S, |Re z_j| ≤ δ ⇒ |R(z)| ≤ e^{δS}∫|Φ|dμ; order k absent.
- Diagonal = degree-one receiver: on z = (w,…,w), response = Laplace transform of pushforward of μ under x ↦ Σx_j (integral_cexp_diag_eq_integral_map), a measure on [−S,S] (ae_abs_le_of_map_sum).
- Sharpness (exp_mul_le_re_integral_cexp_diag): finite positive μ carried by {Σx_j ≥ S − ε} has real diagonal response ≥ e^{δ(S−ε)}μ(ℝ^k).
- MESSAGE: a product of any order gains on depth exactly what one receiver of the same total length gains. Tensor power amplifies only when base cost is fixed while local weight is powered (Deligne stalks); on one spectrum the cost is the total length.
## ProductMomentsAreDiagonalBelowTheThreshold (imports SquareRootThreshold.WindowedOffDiagonalBeyondThreshold)
- D(ξ) = Σ_{n∈s}c_ne^{2πiξ log n}, s ⊆ [1,X]. D^k = integer-frequency polynomial on powSupport (products n_1⋯n_k ≤ X^k) with powCoeff c^{*k}(N) = Σ_{Πn_i = N}Πc_{n_i} (expSum_pow_eq_powSum).
- Distinct integers in [1,Y] are 1/Y-separated in log (inv_le_abs_logFreq_sub).
- PILLAR below threshold (integral_pairTransform_mul_normSq_pow_eq_diag): η ∈ C², supp ⊆ [−r,r], 2rX^k ≤ 1 ⇒ windowed 2k-th moment ∫pairTransform·|D|^{2k} = ‖η‖²Σ_N|c^{*k}(N)|² exactly — only coincidences seen are n_1⋯n_k = m_1⋯m_k (unique factorization).
- Beyond threshold (integral_normSq_pow_eq_diag_add_offDiag_nonneg): real nonneg coefficients and window ⇒ moment = diagonal + nonnegative off-diagonal over near-coincident products; size information cannot do better.
- Free region of an order-k product ends at total length X^k = 1/(2r), the square-root threshold, for every k: moment form of the tensor-power trick over the archimedean family.
## KunnethPositivityIsPointCountPositivity (imports ACS.TheLambdaRingOfTheScalingSurface, ACS.FrobeniusSpanHodgeIndexIsRH)
- kunnethCount D m n = Π_iN_{m_in}: ghost sequence of external product of Adams twists ψ^{m_i}C; zeta = λ-ring exponential sigmaSeries σ(g) = exp(Σg(j)X^j/j).
- Newton–Witt positivity (exists_sigmaCoeff_eq_ofReal_nonneg): g(j) ≥ 0 for j ≥ 1 ⇒ all σ-coefficients nonnegative real ((n+1)σ_{n+1} = Σσ_jg(n+1−j), only positive ghost indices). σ_1 = g(1).
- PILLAR kunneth_positivity_tfae: N_n ≥ 0 ∀n ⇔ all Künneth–Adams counts ≥ 0 ⇔ every coefficient of every Künneth–Adams zeta series nonneg real.
- goldenDatum_kunneth_positive_not_pure: fake curve 1 − 5X + 5X² over 𝔽₅ has every Künneth positivity, is not unitary (not pure), fails Hodge index on Frobenius span (CurveDatum.hodgeIndexOnSpan_iff_unitary). Positivity of products of spectrum strictly weaker than purity; Weil's positivity is of correspondences on C×C.
