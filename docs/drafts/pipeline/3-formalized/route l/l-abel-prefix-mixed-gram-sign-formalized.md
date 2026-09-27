# Route L: Abel-prefix mixed Gamma–Hankel sign atlas — Lean certificate

- **ID:** L-ABEL-PREFIX-MIXED-GRAM-SIGN
- **Stage:** 3-formalized
- **Paper proof:** [l-abel-prefix-mixed-gram-sign.md](l-abel-prefix-mixed-gram-sign.md)
- **Lean modules:** `GaloisForLFunctions.RHTower.MobiusCubicGammaNorm`,
  `GaloisForLFunctions.RHTower.MobiusCubicGammaAtomJets`,
  `GaloisForLFunctions.RHTower.MobiusAbelPrefixGramIntegral`,
  `GaloisForLFunctions.RHTower.MobiusAbelPrefixFourierMultiplier`,
  `GaloisForLFunctions.RHTower.MobiusAbelPrefixGramSign` (pre-existing algebraic bounds)
- **Umbrella:** `GaloisForLFunctions.RHTower`
- **Verification:** `lake env lean` clean on each module (no warnings); targeted `lake --old build` of each
  module; `#print axioms` = `propext`, `Classical.choice`, `Quot.sound` for every theorem below.

All results live in namespace `RHTower.CubicGamma`. The norm `‖F‖_δ² = Γ(5+δ)⁻¹∫_0^∞ t^{4+δ}F²` is
`gammaEnergy δ F` (`gammaInner`, `gammaNorm`), `f_x = atom x`, `∂_x^r f_x = atomJet r x`,
`K_δ = sourceKernel δ`, `G_δ = abelPrefixGramKernel δ`, `g_n = abelDipole n`, `D_δ = abelDipoleGram δ`,
`M(n) = abelMertens n`, `S_N = mobiusCubicSource N`, `P_N = frozenPrefix N`, `b_N = frozenPrefixLog δ N`,
`H_δ = abelLogKernel δ`.

| Card item | Lean theorem |
|-|-|
| (1) `S_N = M(N)f_N + Σ_{n<N} M(n)g_n` | `mobiusCubicSource_eq_abel` (general `sum_Icc_eq_abel`) |
| `g_n = -∫_n^{n+1} ∂_x f_x dx`, `∂_x f_x = (2x - x²t)e^{-xt}` | `abelDipole_eq_neg_integral`, `atomJet_one_eq`, `hasDerivAt_atomJet` |
| Gamma moments / source Gram `⟨f_x,f_y⟩ = K_δ` | `gammaInner_expMono`, `gammaInner_atom` |
| (2) `⟨∂f_x,∂f_y⟩_δ = xy B_δ/(x+y)^{p+2}` | `gammaInner_atomJet_one` |
| (3) `D_δ = ∫∫ G_δ = K(m,n)-K(m+1,n)-K(m,n+1)+K(m+1,n+1)` | `gammaInner_abelDipole`, `integral_integral_abelPrefixGramKernel` (via `hasDerivAt_sourceKernel_fst`, `hasDerivAt_sourceKernelX_snd`) |
| (4) exact prefix energy | `gammaEnergy_mobiusCubicSource` |
| (5) sign bounds, stronger bound `(3+2δ+δ²)xy` | `abelPrefixGramNumerator_ge_three_mul`, `abelPrefixGramNumerator_le_neg_two_thirds`, `abelPrefixGramNumerator_ge_strong` |
| sharp constants (equality at `δ=0,x=2y` / `δ=1,x=3y`) | `isGreatest_abelPrefixGram_comparable_constant`, `isLeast_abelPrefixGram_separated_constant`, `abelPrefixGramNumerator_zero_two_mul`, `abelPrefixGramNumerator_one_three_mul` |
| exact transition `sign G = sign(c_δ - r - 1/r)` | `abelPrefixGramNumerator_eq_transition`, `sign_abelPrefixGramKernel` |
| `c_δ` increasing, derivative `(6+12δ+2δ²)/(6+2δ)²` | `strictMonoOn_abelTransitionConstant`, `hasDerivAt_abelTransitionConstant` |
| positive chamber = reciprocal interval; endpoints `(3+√5)/2`, `(13+√105)/8` | `abelPrefixGramKernel_pos_iff`, `sub_sub_inv_pos_iff`, `abelTransition_upper_zero`, `abelTransition_upper_one` |
| discrete signs `D>0` (comparable), `D<0` (separated) | `abelDipoleGram_pos`, `abelDipoleGram_neg`, `abelDipoleGram_neg'` |
| (6) `S_N(t) = -∫_1^∞ P_N(x)∂_x f_x(t)dx` | `mobiusCubicSource_eq_neg_integral` |
| `b_N` integrable, square-integrable | `integrable_frozenPrefixLog`, `memLp_two_frozenPrefixLog` |
| homogeneity `G(λx,λy) = λ^{-3-δ}G(x,y)` | `abelPrefixGramKernel_smul`, `logAtom_integrand_eq` |
| (7) `‖S_N‖² = ∫∫ b_N(u)b_N(v)H_δ(u-v)` | `gammaEnergy_mobiusCubicSource_eq_logKernel` (atoms: `integral_logAtom_mul_logAtomKernel`) |
| (8) `Ĥ_δ(τ) = (a²+τ²)|Γ(p/2+iτ)|²/Γ(p) > 0` | `fourier_abelLogKernel`, `abelMultiplier_pos` (Beta: `integral_exp_mul_one_add_exp_cpow`) |
| (9) `b̂_N(τ) = (a+iτ)⁻¹Σ μ(n)n^{-a-iτ}` | `fourier_frozenPrefixLog` |
| (10) Mellin–Plancherel identity | `gammaEnergy_mobiusCubicSource_eq_mellin` |
| `‖∂_x f_x‖_δ = O(x^{-3/2-δ/2})` (used in the Fubini remark) | `gammaNorm_atomJet_le` |
