# ShallowCauchyPrimeEnergy: mathematical facts

Namespace `RHTower` (files in ShallowCauchyPrimeEnergy/). 4 modules.

## PoissonKernelDomination (uses HTGeometry HalfPlanePoissonKernel, RHTower FiniteOfflineCauchyEnergy)
- For 0 ≤ a, b ≤ h, h > 0, R₀ ≥ 2h: 4h·transverseCauchyKernel(h+a, h+b, Δ) ≤ 4R₀²/(R₀² + Δ²) (shifted Cauchy kernel ≤ 4 × width-R₀ Lorentzian).
- windowNarrowSum Z γ r t = Σ_{q∈Z} r²/(r² + (t − γ_q)²); nonneg, continuous, monotone in r.
- Product of two narrow Lorentzians = (πr)² P_r(x − t)P_r(t − y) (half-plane Poisson kernel).
- Poisson semigroup P_r ⋆ P_r = P_{2r} at r = R₀/2: ∫ narrow(x)narrow(y) dt = (πR₀/4)·R₀²/(R₀² + (x − y)²).
- Exact L² identity: Σ_{q₁,q₂} R₀²/(R₀² + (γ_{q₁} − γ_{q₂})²) = (4/(πR₀)) ∫ G_{R₀/2}(t)² dt. Lorentzian pair sums are L² norms of a Poisson-smoothed zero density.
- Five-piece union bound of ∫ f over (−∞, T/2], [T/2, T], [T, 2T], [2T, 4T], [4T, ∞).

## MultiscaleLorentzL2 (uses RHTower ZetaTypicalLocalZeroCountMultiScale, ZetaCriticalAsymptotics)
- MultiScaleBad S u t: t ∈ [S, 2S] and some scale v ∈ [u, 1/16] has > 20 v log S ξ-zero copies within ordinate distance v.
- Far zeros (|γ − t| > 1/16): narrowMassTerm ≤ 257 r² × Lorentz mass term; far sum ≤ 65 u log S.
- Deterministic ceiling: windowNarrowSum ≤ 16 log S on [S, 2S] for r ≤ 1 (Lorentz mass ≤ log).
- Near zeros on a good point: dyadic shells 2^j u < |γ − t| ≤ 2^{j+1}u, each term ≤ 4^{−(j+1)}, count ≤ 20·2^{j+1}u log S; geometric sum gives ≤ 40 u log S.
- Good point: windowNarrowSum(R₀/2, t) ≤ 105 u log S.
- Dyadic superlevel sets {G > 105·2^j R₀ log S} ⊂ MultiScaleBad at scale 2^j R₀; G² ≤ majorant built from superlevel indicators.
- Σ_j 4^j e^{−2^j x} ≤ 17 for x ≥ 1.
- exists_integral_Icc_windowNarrowSum_sq_le: ∃ C₁, κ₂ ≥ 120000, eventually in S, for 0 < R₀ ≤ 1/16 with κ₂ ≤ R₀ log S and every finite set of ξ-zero copies: ∫_{[S,2S]} G_{R₀/2}² ≤ C₁(R₀ log S)² S. Input: prime-cascade multiscale local zero-count regularity (volume of bad set at scale v ≤ 12CS e^{−v log S/120000} + CS^{3/4}).
- dyadicZeroWindow T = zero copies with ordinate in [T, 2T]. Tails (−∞, T/2] and [4T, ∞) each ≤ 8π r⁴ N²/T³ (inverse-square decay).
- exists_dyadicZeroWindow_lorentzPairSum_le (unconditional): for 0 < R₀ ≤ 1/32, κ₂ ≤ R₀ log T: Σ_{q₁,q₂ ∈ [T,2T]} R₀²/(R₀² + (γ₁ − γ₂)²) ≤ C_pair (R₀ log T)(T log T). The Lorentzian pair-correlation at width R₀ ≫ 1/log T is the trivial (Poisson) size: mean count R₀ log T per zero.

## ShallowCauchyEnergyBound (uses RHTower XiWardSourceWindowMultiplicity, XiWardTriangularSourceRectangle, XiReflectionSelfIntersectionCharge, ZetaDyadicWindowMomentTwoThirds)
- Centered coordinate xiRightCenteredZero q = ρ − ½; line reflection 1 − ρ̄ keeps the ordinate and negates the depth; right copies and their reflections are disjoint subsets of dyadicZeroWindow T.
- xiShallowRightUpperWindow h T: right upper zero copies in [T, 2T] with 0 < Re ρ − ½ ≤ h; deep window: Re ρ − ½ > h; card(right) = shallow + deep.
- xiShallowCauchyEnergy h T = 4 Σ_{p,q shallow} transverseCauchyKernel(h + β_p, h + β_q, γ_p − γ_q) ≥ 0; it dominates finiteOfflineCauchyEnergy of any injective shallow packet, and of distinct zeros weighted by exact analytic multiplicity (fibres of zero copies have size = order).
- Diagonal lower bound: #shallow copies ≤ h·E_h.
- Line-reflection saving: each shallow pair appears 4 times (p, reflected p) × (q, reflected q) in the global window pair sum, cancelling the factor 4: h·E_h ≤ Σ_{c₁,c₂ ∈ [T,2T]} R₀²/(R₀² + Δγ²) for 2h ≤ R₀.
- exists_uniform_xiShallowCauchyEnergy_le: ∃ C, κ₂ ≥ 120000, eventually in T, ∀ 0 < h ≤ 1/64: h·E_h ≤ C·max(κ₂, 2h log T)·T log T (R₀ = max(κ₂/log T, 2h)).
- exists_xiShallowCauchyEnergy_one_div_log_le: at h = 1/log T: E_h ≤ C T log²T; h·E_h ≤ C T log T; #shallow · log T ≤ E_h (diagonal). Removes the log T loss of the deterministic RvM local ceiling (T log³T); matches the diagonal up to a constant.
- Same bound for any injective packet of right copies, and for distinct right ζ-zeros weighted by multiplicity (ζ and ξ orders agree in the strip).

## ShallowCauchyImplications (uses RHTower XiReciprocalSlicePositiveDensity, SelbergExponentialNearLineDensityLong)
- T log T ≤ 8π N(T, 2T) eventually (Riemann–von Mangoldt).
- (1/log T)·E_{1/log T} ≤ C_N N(T, 2T).
- Saturation: E_{α/log T} ≤ 2C T log²T uniformly for κ₂/2 ≤ α ≤ log T/64 (independent of α).
- Σ m_j² ≤ h·finiteOfflineCauchyEnergy (from diagonal E ≥ 2Σ m²/(h + a) and a ≤ h); close pairs |γ_j − γ_k| ≤ Kh: Σ m_j m_k ≤ ((16 + K²)/8) h E.
- Shallow right ζ zeros in [T, 2T] at depth ≤ 1/log T: Σ m_j² ≤ C T log T; Σ_{|Δγ| ≤ K/log T} m_j m_k ≤ (C/8)(16 + K²) T log T (anti-clustering at critical spacing).
- Unit strip: #ξ-zero copies within ordinate distance 1 of t ≤ 16(c + log(|t| + 4)).
- Deep tail (Selberg long two-length Barban–Vehov density, rate e^{−a/14}): #right copies in [T, 2T] at depth > α/log T ≤ C_deep(T log T e^{−α/28}/α + log²T), 4 ≤ α ≤ log T/64.
- Joint budget: R = R_shallow + R_deep; R_shallow ≤ (α/log T)E; (α/log T)E ≤ C_sh max(κ₂, 2α) N(T, 2T); R_deep exponentially small.
- ∀ε ∃α, B: R_deep(α) ≤ εN(T, 2T), (α/log T)E + R_deep ≤ B N, E ≤ B T log²T. All unconditional; none forces R_shallow = 0: the energy bound is of the size of the diagonal, so it is a density statement (shallow copies ≤ O(N)), never a vanishing statement.
