# RH as endpoint harmonic completeness for the literal theta measure — Lean certificate

- **Paper card:** `theta-endpoint-harmonic-completeness.md`
- **Lean modules:** `GaloisForLFunctions.HTGeometry.FiniteMeasureL1Duality` (`L¹–L^∞` duality for
  finite measures, bounded annihilators, bipolar closure criterion, codimension from functionals),
  `GaloisForLFunctions.HTGeometry.PolynomialImagRaysLiouville` (polynomial Liouville from the
  imaginary axis and four rays), `GaloisForLFunctions.RHTower.ThetaZeroDivisionRealization`
  (complex zero divisions, `O(e^{-2|x|})` relative bounds, successive divisions along a list,
  `listDivisor`), `GaloisForLFunctions.RHTower.ThetaEndpointDivisorClassification` (quadrant
  zeros, multiplicities, the off-line divisor `P`, the measure `μ`, the jets `φ_{γ,j}`, the
  classification `E = P H / F` real even polynomial), `GaloisForLFunctions.RHTower.ThetaEndpointHarmonicCompleteness`
  (the even `L¹(μ)` space, the spans, annihilators, the equivalences (i)⇔(ii)⇔(iii)),
  `GaloisForLFunctions.RHTower.ThetaEndpointDefectIndex` (the defect index (1)),
  `GaloisForLFunctions.RHTower.ThetaEndpointMomentFiltration` (moments as Taylor coefficients,
  the basis sources, the filtrations (2) and the tail filtration),
  `GaloisForLFunctions.RHTower.ThetaEndpointPositiveDeformation` (the divisor polynomial, every
  polynomial occurs, a.e. classification, `lim u/k = lim E/P`, positive local moduli, `u_*`, the
  hidden direction), `GaloisForLFunctions.RHTower.ThetaEndpointLpDefect` (sharp growth of
  `k^{(j)}/k`, the witnesses `f_{4m}`, Hölder pairing, infinite `L^p` codimension),
  `GaloisForLFunctions.RHTower.GaussianControlEndpointIncompleteness` (the Gaussian control fails
  the test); the relative-source rigidity module `GaloisForLFunctions.RHTower.ThetaRelativeSourceRigidity`
  was generalized in place (`exists_quotient_envelope_of_bound`, `rays_of_band_bound`,
  `norm_le_of_band_of_eq_mul`) so that its envelope argument applies to `E = P H / F`.
- **Umbrellas:** `GaloisForLFunctions.HTGeometry`, `GaloisForLFunctions.RHTower`
- **Verification:** targeted `lake build` of every module; `lake env lean` audit clean on all ten
  modules and on the modified rigidity module and its dependent `ThetaTailDivisorCapacity`;
  `#print axioms` = `propext`, `Classical.choice`, `Quot.sound` for all 289 theorems of these
  modules; no `sorry`; lint reports nothing for these modules. The only hypotheses are the card's
  own quantified objects (finiteness or infiniteness of the off-line configuration, the source
  `u` and its bound, the exponent `p`, the deformation parameter, the control parameters `a, ω`).

Dictionary: `k = thetaCuspFullSource`, `F = XiC`, `Fourier(u) = sourceTransform u`,
`μ = thetaSourceMeasure`, `L¹_even(μ) = thetaEvenL1`, `φ_{γ,j} = thetaCosJet γ j`,
`V = thetaJetSpan` (real span of the jets at positive real zeros below the multiplicity),
`span({1} ∪ V) = thetaJetOneSpan`, `{h ∈ L¹_even : ∫ h dμ = 0} = thetaEvenMeanZeroL1`;
first-quadrant zeros `xiQuadrantZeros`, `M = xiQuadrantMult hfin`, `P = xiOffLineDivisor hfin`;
"keeps every real zero of `F` with full multiplicity" is `KeepsRealZeros`;
`W = thetaKeepingSources` (continuous real even `k`-dominated sources keeping the real zeros; every
measurable such source agrees a.e. with one of them), `W_N = thetaKeepingMomentSources N`, the tail
filtration is `thetaKeepingTailSources N`; `L^p(μ) = ThetaLp p`, `L^p_even(μ) = thetaEvenLp p`,
`span({1} ∪ V) ⊆ L^p` is `thetaJetOneSpanLp p hp`; `f_j = k^{(j)}/k = thetaSourceRatio j`;
`k_G = HTGeometry.gaussPairSource a`, `μ_G = gaussPairMeasure a`. Real even polynomials `E` of
degree `≤ 4M` are written `e(z²)` with `e` a real polynomial of degree `≤ 2M`.

| Card item | Lean theorem |
|-|-|
| `φ_{γ,j} = ∂_t^j cos(tx)|_{t=γ}`, even, `|φ_{γ,j}| ≤ |x|^j` | `thetaCosJet_eq_iteratedDeriv`, `thetaCosJet_neg`, `abs_thetaCosJet_le` |
| `φ_{γ,j} ∈ L^p_even(μ)` for every finite `p` | `memLp_thetaCosJet`, `thetaJetL1_mem_thetaEvenL1` |
| zero `μ`-mean: `∫ φ_{γ,j} dμ = F^{(j)}(γ) = 0` | `integral_thetaCosJet_thetaSourceMeasure`, `thetaJetSet_subset_thetaEvenMeanZeroL1` |
| **(i) ⇔ (ii)** | `xiReal_iff_closure_thetaJetOneSpan` |
| **(i) ⇔ (iii)** | `xiReal_iff_closure_thetaJetSpan` |
| dual of `L¹_even(μ)` is `L^∞_even(μ)` via the even projection; Hahn–Banach | `exists_linfty_representation`, `exists_linfty_annihilator`, `mem_topologicalClosure_iff_linfty`, `exists_even_representative`, `annihilates_span_iff` |
| `H^{(j)}(γ) = ∫ f φ_{γ,j} dμ` for `u = kf`; annihilating `V` ⇔ keeping the real divisor | `iteratedDeriv_sourceTransform_ofReal`, `iteratedDeriv_sourceTransform_ofReal_of_moment`, `keepsRealZeros_iff_jets`, `annihilates_thetaJetSpan_iff`, `annihilates_thetaJetOneSpan_iff` |
| under RH the annihilator is constant (relative-source rigidity) | `ae_eq_const_of_keepsRealZeros` |
| complex one-sided division `g_α`, `G_α = F/(1 − z²/α²)`, smooth even join, `|g_α| ≤ C e^{-2|x|} k` | `norm_outwardSine_le_tail_of_le`, `exists_norm_zeroDivision_le_of_le`, `exists_norm_zeroDivision_le_mul_of_le`, `sourceTransform_thetaListDivision_mul`, `tendsto_thetaListDivision_div` |
| repeated division through a multiple off-line zero | `thetaListDivision`, `ThetaDivisionList`, `thetaDivisionList_quadrantListOf`, `exists_source_mul_listDivisor` |
| converse: `u = Re g_α − k` annihilates `V` and `1`, `u ≠ 0` | `exists_offLine_annihilator`, `sourceTransform_ofReal_re`, `sourceTransform_conj_comp` |
| no zeros on the imaginary axis (`F(iy) > 0`) | `XiC_I_mul_ne_zero`, `re_ne_zero_of_XiC_eq_zero` |
| `P`: real, even, `P(0) = 1`, `deg P = 4M`, zeros with multiplicity exactly the off-line zeros, `P(x) > 0` on `ℝ` | `xiOffLineDivisor_properties`, `exists_polynomial_listDivisor`, `xiOffLineDivisor_neg`, `listDivisor_quadrantListOf_ofReal`, `analyticOrderAt_xiOffLineDivisor` |
| `E = P H / F` is a real even polynomial of degree `≤ 4M` (Jensen, indicator, Phragmén–Lindelöf, Liouville) | `exists_realPolynomial_of_keepsRealZeros`, `eq_taylor_of_imag_of_rays`, `exists_quotient_envelope_of_bound`, `rays_of_band_bound` |
| every such `E` occurs; real even sources bounded by `Ck` | `exists_mem_thetaKeepingSources_of_polynomial`, `exists_basis_sources`, `exists_defect_sources` |
| bounded annihilators of `V`: dimension `2M + 1`; with `1`: `2M` | `finrank_thetaKeepingSources`, `exists_mem_thetaKeepingSources_ae_eq`, `ae_eq_sum_defect_annihilators`, `pairing_independent` |
| **(1)** `codim closure(span({1} ∪ V)) = 2M`, `∞` for infinitely many quartets | `finrank_thetaEndpointDefect`, `not_finiteDimensional_thetaEndpointDefect`, `thetaEndpointDefect_eq` |
| even moments are the even Taylor coefficients: vanishing of orders `0,…,2N` ⇔ zero of order `2N+2` at `0` | `iteratedDeriv_two_mul_zero_ofReal`, `moments_eq_zero_iff_order`, `moments_sum_divisorBasis_iff` |
| **(2)** `dim W_N = max(2M − N, 0)` (exact) | `finrank_thetaKeepingMomentSources` |
| infinitely many quartets: every `W_N` infinite-dimensional | `not_finiteDimensional_thetaKeepingMomentSources` |
| positive local moduli: `k + εu > 0`, multiplier `1 + εE(x²)/P(x) > 0`, same real divisor, same first `N+1` even moments | `positive_deformation_of_mem_thetaKeepingMomentSources`, `positive_deformation_of_mul_eq` |
| `lim_{|x|→∞} u/k = lim_{|z|→∞} E/P` | `tendsto_div_thetaCuspFullSource_eq_limit_quotient`, `tendsto_eval_sq_div_listDivisor`, `tendsto_divisorBasisComb_div` |
| tail filtration: dimension `max(2M − N − 1, 0)` (infinite for infinitely many quartets) | `finrank_thetaKeepingTailSources`, `not_finiteDimensional_thetaKeepingTailSources` |
| one off-line quartet: `Fourier(u) = z² F/P` with zero mass, unchanged leading tail, same real divisor, positive perturbations, nonzero second moment | `exists_hidden_direction_of_offLine` |
| `u_*` with `Fourier(u_*) = z^{4M} F/P`: moments of orders `0,…,4M−2` vanish, order `4M` nonzero; `k + t u_*` positive with transform `F (P + t z^{4M})/P`, same real zeros and first `2M` moments, off-line zeros moved to the zeros of `P + t z^{4M}` | `exists_topMoment_deformation`, `ne_zero_of_mul_eq_xiOffLineDivisor`, `xiOffLineDivisor_eq_zero_of_im_ne_zero` |
| `k^{(j)}/k ~ (−2π)^j e^{2jx}`; `|k^{(4m)}|/k ≤ C_m e^{8m|x|}` | `tendsto_thetaSourceRatio_div_exp`, `tendsto_thetaAtomRatio_div_exp`, `exists_abs_thetaSourceRatio_le` |
| `f_{4m} ∈ ⋂_{q<∞} L^q_even(μ)` | `memLp_thetaSourceRatio`, `thetaSourceRatio_four_mul_neg` |
| `Fourier(k^{(4m)}) = z^{4m} F`; `∫ f_{4m} dμ = 0`, `∫ f_{4m} φ_{γ,j} dμ = 0` | `sourceTransform_thetaDerivSourceC_four_mul`, `integral_thetaSourceRatio_eq_zero`, `integral_thetaSourceRatio_mul_thetaCosJet_eq_zero` |
| the `f_{4m}` are linearly independent | `linearIndependent_thetaSourceRatio`, `integral_thetaSourceRatio_mul_cos`, `eq_zero_of_forall_sum_integral_thetaSourceRatio_mul_cos` |
| **Unconditionally, for every finite `p > 1`, closure(span({1} ∪ V)) has infinite codimension in `L^p_even(μ)`** (Hölder duality) | `not_finiteDimensional_thetaLpDefect`, `exists_thetaSourceRatioPairing` |
| the Gaussian control has only real zeros but its real-zero modes fail the weighted `L¹` test | `gaussPair_not_mem_closure_span`, `sourceTransform_gaussPair_annihilator`, `gaussPairTransform_zero_im` |

The `L²` annihilator `f₄` of the card's closing remark is the case `p = 2`, `m = 1` of
`not_finiteDimensional_thetaLpDefect`. Dimensions are stated with natural-number subtraction,
which is the card's `max(·, 0)`.
