# CompletedArithmeticForms

Namespace `GaloisForLFunctions.CompletedArithmeticForms`; umbrella `CompletedArithmeticForms.lean`; 106 modules.
All results unconditional; each module ends with `#print axioms` for its main theorems.

## 1. Motivation

RH criteria are positivity statements for complete signed forms: complete Weil matrices, signed theta
Hankel hierarchies, Euler-deletion and Chebyshev energies. Positive pieces of such forms are easy to
find; the difficulty is the transfer: Schur complements, mixed entries, accumulation, truncation, and
simultaneous limits each consume reserve. This programme proves exact completions, exact dual costs, and
quantitative relative estimates that keep every source term (prime, Gamma, polar, mixed, infinite tail)
and record the exact parameter domain on which each reserve survives.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Divisor conductor Gram | `divisorGramEnergy Q a` | Σ_{m∣Q, m≠1} primitive-prefix Gram; kernel Q·min(i,j) − ij |
| Cyclotomic remainder | `cyclotomicRemainder` | Σ over nontrivial roots of |(1+ζ)P_a(ζ)|² |
| Bridge inverse / cost | `bridgeInverse`, `bridgeSchurCost`, `dirichletEnergy` | L/Q (second difference); Dirichlet energy of the coupling |
| Mesh Gram | `meshGram`, `meshDirichletEnergy` | kernel min(k_i,k_j) − k_ik_j/Q on arbitrary integer nodes |
| Prime packet form | `primePacket` | energy-centered pronic prime form on S ⊂ (P,2P] with mass and log-moment zero |
| Accumulated energy | `cumulativeEnergy c T` | Σ_n (Σ_{j≤n}c_j)²/(n(n+1)) |
| Finite source energy | `finiteSourceEnergy c T` | cumulative + terminal mass²/(T+1) = Σ c_jc_k/max(j,k) |
| Free-terminal dual cost | `finiteSourceDualCost b T` | Dirichlet energy of j·b_j on [0,T], no terminal edge |
| Chebyshev completion | `chebyshevCompletedEnergy`, `chebyshevCyclotomicRemainder` | Cesàro-normalized ψ(x)−x energy and its cyclic remainder |
| Gamma moments | `gaussianMoment`, `gaussianFullHead` | γ_k = 16^k(½)_k = 4^k(2k)!/k!; full signed Gaussian head |
| Native balanced moments | `nativeBalancedMoment`, `nativeBalancedFullMoment` | complete theta reflection jets / (f₁²q^{k}), q = πe^{2x} |
| First-atom invariants | `firstAtomNegativeOrder`, `firstAtomFailureRank` | first negative signed moment ν(x); first non-PSD head κ(x) |
| Successor Schur | `finiteHankelSuccessorSchur m N` | m(2N) − coupling·H_N⁻¹·coupling |
| Hermite jet matrix | `hermiteJetMatrix` | unit lower-triangular Gaussian-to-Hermite congruence |
| Quadratic rank scale | `nativeQuadraticRankScale`, `nativeQuadraticRankHorizon` | q-scale 16(M+2)² + 2·cost(M) ≤ C(M+2)²; center log(M+2) + O(1) |
| Native tail head | `nativeTailHead N r` | Hankel head of ∫_{s>r} native signed jets |
| Weighted center moment | `nativeWeightedMoment a U` | ∫_U r sinh(ar)·native jet(r/2) (critical aperture 0<a<½) |
| Complete Weil inverse cost | `tiltedWeilInverseCost c` | 1/E₁(c), reciprocal completed pole energy |
| Conductor Green operator | `tiltedConductorGreen` | diagonal ℓ² operator with weights 1/E_m(c) |
| Residual scale | `weilResidualScale c N` | c¹⁰(log N/N)² + c⁶/√log N |
| Overlap schedule | `logarithmicPacketOverlap α N` | c_N = (log N)^α |
| Conductor subspace | `conductorSubspace M N`, `highConductorSubspace M_low M N` | span of normalized Ramanujan horizon modes v_m (1 ≤ m ≤ M, resp. M_low < m ≤ M) |
| Bessel band source | `besselBandSource`, `besselGaussianFlux` | Re K_{iτ}(x) and its Gaussian Wronskian |

External: `completeWeilMatrix`, `completedConductorEnergy`, `normalizedRamanujanHorizonVector`
(CriticalArithmeticCorrelationTheory / RenormalizedArithmeticPotentialTheory); `tiltedUnitSpline`
(SpacingScaleHarmonicAnalysis); `thetaCuspNativeSignedJet`,
`thetaCuspCenterMixedSignedJet` (RHTower ThetaCusp); `modifiedBesselKOrder` (HTGeometry); `plateauPrefixBlock`
(TransMetzlerWeilPositivity).

## 3. Language

- **Completion**: an exact identity form = comparison + nonnegative remainder, every term literal.
- **Dual cost**: max_a (2⟨a,b⟩ − E(a)); exact when attained, equality set classified.
- **Relative error η**: |vᵀ(A−G)v| ≤ η·vᵀGv; η < ½ leaves A − G/2 ≻ 0; transfers to successors with no
  inverse factor.
- **Horizon**: q-scale or center x beyond which a reserve holds; "joint" = uniform in a second parameter.
- **Native vs first atom**: complete theta source vs its n = 1 term; physical vs balanced = before/after
  mass f₁² and scale q^k normalization.
- **Rank boundary**: ν(x), κ(x): finite at each center, escaping as x → ∞.

## 4. Mechanisms

**A. Arithmetic Gram completion**
1. Divisor sum of primitive Grams = discrete bridge kernel; 4E_Q(a) = Q[(Σa)² + Σa²] + R_Q(a), R ≥ 0 via
   the multiplier 1−ζ; zero interior radical.
2. Exact inverse B_Q⁻¹ = L/Q; E(a) − 2⟨a,b⟩ + D(b)/Q = E(a − Lb/Q); dual cost D(b)/Q attained.
3. Irregular nodes: same identity with slope differences and reciprocal-gap Dirichlet energy; gap ≥ δ
   gives F ≥ (δ/4)|a|²; D_k(b) = min Dirichlet extension through the nodes.
4. Neutral constraints: one or two removed profiles (mass, log-moment) give exact projected dual costs and
   classified radicals; prime packets pay couplings by D_k(P b) ≤ D_k(b); odd/separated support doubles the
   coefficient reserve (|a|² ≤ 2𝒫).

**B. Accumulation and terminal completion**
5. Accumulation a_j = c_j/j turns cumulative energy into E_{T+1}(a)/(T+1); local dual cost of j·b_j.
6. Terminal completion: adding mass²/(T+1) gives the full max-index covariance; free terminal value removes
   the last Dirichlet edge; maximizer c* = j·(second difference), mass T b_T; E(c) − 2⟨c,b⟩ + cost = E(c − c*).
7. Source vs probe support: fixed probe with growing source restores the terminal edge, (T b_T)²; maximizer
   is neutral.
8. Euler deletion: |full − completed(T)| ≤ (M+1)²/(T+1); schedule T = (n+1)(M+1)² gives limits uniform in
   all cutoffs.
9. Chebyshev: all superlinear energy sits in the cyclotomic remainder; far modes cost O(N^{3/2}), leaving
   ≤ 2√N near-constant modes.

**C. Complete Weil matrix**
10. Prefix payment: plateau endpoint energy > 1/20 ⇒ prefix ⪰ I/20 uniformly through touching ⇒ inverse
    cost ≤ 20 and two-sided Schur sandwich; negative subspaces inject into the tail (index ≤ N − M).
11. Spectral floor ⇒ inverse cost; ground eigenvector ⇒ sharpness; quasimode inversion
    |A⁻¹v − λ⁻¹v| ≤ (eλ)⁻¹|Av − λv|.
12. Conductor spectrum: E_m = log m + O(1) shell budget, E_p ≤ log p + O(1); Σ1/p = ∞ fixes heat threshold β = 1.
13. Residual payment: eight-term decomposition, each term polynomial in c with decay (log N/N)² or
    1/√log N; Fourier decay t^{−8} gives E_m(c) ≍ c^{−7}; relative residual → 0 on c_N = (log N)^α, α < 1/40.
14. Conductor level of distribution (`0 < θ < 1/2`, `M = ⌊N^θ⌋₊`): exact Kluyver–Möbius Gram expansion
    isolates prime-power steps `l ∣ m` or `m ∣ l` at scale `1/log N`, giving a two-sided Riesz frame
    `(1 − 2θ)Σ a_m² ≤ ‖Σ a_m v_m‖² ≤ 6 Σ a_m²`; divisor-totient envelope `Σ_{m≤M} c̃_m(n)² ≤ n(1 + log M)⁴`
    and periodic gcd-permutation Cauchy–Schwarz give `Σ_{m≤M} ‖P_N v_m − (log N − E_arith(m))v_m‖² = O(M log N)`
    and collective complete-Weil residual decay up to `c_N² / log N → 0` (covering `c_N = 2(log N)^α`,
    `1/4 < α < 1/2`), forcing diverging conductor-average energy, `o(M)` nonpositive census, and
    `κ(W_{N,c_N}|_{V_M}) = o(M)`.

**D. Signed theta Hankel hierarchy**
14. Gamma moments have product determinants and successor gw^{2N}N!(r)_N; native balanced heads converge to
    them at fixed rank; relative successor fraction N!/(s+½+N)_N ≤ (2/3)^N → 0.
15. Parity split: H_N(s) ≅ H_{⌈N/2⌉}(m) ⊕ H_{⌊N/2⌋}(m_{·+1}) for interleaved zeros.
16. First-atom obstruction: continuation at t = iy is periodic; positive signed moments would force
    monotonicity; g(π/2) > g(π) ⇒ some moment < 0 at every center.
17. Analytic payment chain: Cauchy on the unit disk (factorial), polynomial scale envelope P_k (quadratic order
    cost), Wick kernel e^{8zw}·relative factor, Hermite congruence (det 1), adaptive radii r_n = √((n+1)/8),
    geometric contraction kernel (row mass ≤ 4) ⇒ relative form error 16D(N+1)²/q; infinite native tail adds
    N·A e⁸/q.
18. Successor comparison: H_{N+1}(m) ⪰ H_{N+1}(g) ⇒ S_N(m) ≥ S_N(g); relative η transfers to successors.
19. Rescaling S_N(c t^k m_k) = c t^{2N} S_N(m); Gaussian successor = 8^N N!.
20. Successor mixture: S(m+n) = S(m) + S(n) + minimizer variance (0 iff minimizers agree); monic energy
    identity; global minimizer test converts pointwise native positivity into integrated tail reserves.
21. Seam: tail head at r = 0 is the Gram of derivative packets of the complete theta source ⇒ PD at every rank.
22. Hyperbolic clock: u = arsinh(t/√q) makes the first atom a Gamma mixture C[(B−3)γ_k + (3/8)γ_{k+1}];
    the affine-Gamma cone is exactly a, b ≥ 0.

**E. Bessel source band**
23. Energy flux (x − τ²/x)|K|² + x|K'|² ≥ 0 plus decay ⇒ K_{iτ}(a) > 0 on |τ| ≤ a; all order zeros have
    |Im ν| > a.
24. Wronskians against e^{−x}/x and e^{−τ²/x}K_0 give K' ≥ −(1+1/a)K and K_{iτ}(a) ≥ e^{−τ²/a}K_0(a).
25. Wigner radial transform = a²((a²+9)K + 6aK'); product fibre = divisor trace × radial transform.

## 5. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| Cyclotomic coercive completion, zero radical | `divisorGramEnergy_completion`, `divisorGramEnergy_eq_zero_iff` | proved |
| Exact attained bridge dual cost D(b)/Q | `bridgeSchur_completion`, `bridgeSchurCost_isGreatest` | proved |
| Mesh dual cost = minimal Dirichlet extension | `meshSchurCost_isGreatest`, `meshDirichletEnergy_isLeast_extension` | proved |
| Neutral prime packet dual payment | `primePacket_neutral_mesh_schur_bound`, `meshDoubleNeutralSchurCost_isGreatest` | proved |
| Terminal completion: full covariance, attained free-terminal cost | `finiteSourceEnergy_eq_covariance`, `finiteSourceDualCost_isGreatest` | proved |
| Probe cost = source cost + (T b_T)², neutral maximizer | `finiteProbeDualCost_isGreatest`, `finiteProbe_maximizer_mass_zero` | proved |
| Euler completion uniform along growing cutoffs | `tendsto_fullErrorEnergy_iff_finiteSourceEnergy_on_schedule` | proved |
| Chebyshev energy ≤ 60N + R/3; strips ⇔ remainder exponents | `chebyshevEnergy_cyclotomic_bounds`, `five_sixths_strip_iff_chebyshevCyclotomicRemainder_subpower` | proved |
| Far cyclotomic modes O(N^{3/2}) | `chebyshevCyclotomicFar_sqrt_le` | proved |
| First-mode Mellin multiplier nonzero for Re s > 0, Im s > 2π | `firstCyclotomicMellin_ne_zero` | proved |
| Actual first-mode difference paid by first-band energy for N ≥ 7; real-horizon interpolation costs ≤ 12π | `norm_chebyshevFirstCyclotomicPacket_sq_le`, `norm_chebyshevFirstCyclotomicPacket_sub_floor_le` | proved |
| On Re s > 1/2, the continuous first-mode Mellin transform equals the literal Chebyshev divisor current times its cyclotomic multiplier | `hasMellin_chebyshevFirstCyclotomicContinuous`, `mellin_chebyshevFirstCyclotomicContinuous_eq_logDeriv` | proved |
| Continuous and discrete first-mode packets differ by at most 80π for every real horizon ≥ 2 | `norm_chebyshevFirstCyclotomicContinuous_sub_packet_le` | proved |
| Fixed first band, and every eventually positive bandwidth, has exponent infimum 2Θ among r ≥ 1; its N^(1+ε) bounds are equivalent to RH | `chebyshevFirstCyclotomicBand_exponent_inf`, `chebyshevCyclotomicBand_exponent_inf`, `riemannHypothesis_iff_chebyshevFirstCyclotomicBand` | proved |
| Complete Weil index ≤ N − M on Young range | `eventually_completeWeil_negative_subspace_dim_le_young_tail` | proved |
| Uniform prefix inverse cost 20 | `eventually_plateauPrefixSchur_quadratic_payment` | proved |
| Sharp inverse cost 1/E₁(c) | `eventually_tiltedWeil_inverse_cost_le`, `eventually_tiltedWeil_inverse_cost_gt` | proved |
| Green form diagonal on Ramanujan packets | `tendsto_tiltedWeil_inverse_packet_inner` | proved |
| Finitely many readings control the inverse | `exists_tiltedWeil_inverse_finite_reading_tail` | proved |
| Conductor heat threshold β = 1; E_m/log m → 1 | `summable_completedConductorHeatWeight_iff`, `tendsto_completedConductorEnergy_div_log_one` | proved |
| Green operator: norm 1/E₁, compact, no power summable | `norm_tiltedConductorGreen`, `not_summable_tiltedConductorGreen_coordinate_power` | proved |
| Polynomial eight-term residual | `exists_tiltedWeil_polynomial_residual_bound` | proved |
| E_m(c) ≍ c^{−7} | `tiltedConductorEnergy_two_sided` | proved |
| Fixed conductor packets positive at c_N = (log N)^α, α < 1/40 | `eventually_tiltedWeil_growing_packet_pos` | proved |
| Whole-prefix Ramanujan Riesz frame (`1 − 2θ` lower, `6` upper) & exact Gram | `ramanujanConductor_lower_riesz`, `ramanujanConductor_upper_riesz`, `normalizedRamanujanHorizonVector_gram_exact` | proved |
| Bombieri–Vinogradov level of distribution (`0 < θ < 1/2`) for `fullPrimeMatrix` | `exists_fullPrimeMatrix_levelOfDistribution` | proved |
| Complete-Weil residual level of distribution (`0 < θ < 1/2`, `c_N² / log N → 0`, RH-complete `α < 1/2`) | `tendsto_completeWeil_residual_levelOfDistribution`, `tendsto_tiltedUnitSpline_completeWeil_residual_rhComplete` | proved |
| Diverging conductor average, `o(M)` census, and `κ(W_{N,c_N}|_{V_M}) = o(M)` at RH-complete overlap | `tendsto_completeWeil_conductorAverage_atTop`, `tendsto_nonpositive_conductor_fraction_zero`, `tendsto_completeWeil_conductorSubspace_negIndex_div_zero` | proved |
| No rank-uniform relative native reserve | `not_native_rank_uniform_relative_reserve` | proved |
| First atom: negative moment at every center; κ(x) → ∞ | `exists_firstAtom_signed_moment_neg`, `firstAtomFailureRank_tendsto` | proved |
| √(q/C₂) − 3 < κ(x) ≤ 1 + C_* q | `firstAtomFailureRank_sqrt_scale_lower`, `exists_firstAtom_signed_head_failure_le_scale` | proved |
| Native signed head PD beyond center log(N+2) + O(1) | `nativeSignedHead_posDef_of_quadratic_rank_horizon` | proved |
| Physical successor ∈ (½, 3/2)·f²q^N 8^N N! | `nativePhysicalSuccessor_half_bounds_of_horizon` | proved |
| Successor addition law | `successorSchur_add_eq`, `successorMixtureVariance_eq_zero_iff` | proved |
| Tails strictly Loewner-decreasing; successor strictly decreasing | `nativeTailHead_sub_posDef_of_quadratic_rank_horizon`, `nativeTailSuccessor_strictAnti_of_quadratic_rank_horizon` | proved |
| Rank-7 center successor ≥ band energy + explicit reserve | `centerSeventhSuccessor_explicit_compact_allowance` | proved |
| Seam head PD at every rank | `nativeTailHead_zero_posDef` | proved |
| Clocked first atom positive at all ranks, pullback fails | `firstAtomGaussianClock_positive_pullback_fails` | proved |
| Affine-Gamma cone ⇔ a, b ≥ 0 | `affineGamma_all_head_posSemidef_iff` | proved |
| Bessel band zero-free and Gaussian-dominated | `modifiedBesselKOrder_zero_outside_band`, `modifiedBesselKOrder_gaussian_lower` | proved |
| Fibre sign = divisor-trace sign on the band | `thetaCuspWignerProductFiber_physical_band_sign` | proved |
| All-rank signed center hierarchy / growing overlap c ≫ (log N)^{1/4} | — | open (RH-equivalent) |

## 6. Tools

**Developed**
- Cyclotomic/divisor completion and exact Green inverse (`DirichletSchurCost`, `IrregularGreen`,
  `OptimalInterpolation`, `NeutralPacketDual`).
- Terminal completion calculus (`TerminalCompletion`, `SourceProbeBoundary`).
- Inverse-trace and variance-weighted stability (`InverseTraceStability`, `WeightedInverseStability`).
- Successor calculus: monotonicity, relative error, rescaling, mixture law (`SuccessorComparison`,
  `PhysicalSuccessorMass`, `SuccessorMixture`).
- Hermite congruence plus geometric contraction: dimension-free relative form bound with quadratic degree
  cost (`HermiteJetCongruence`, `GaussianJetConvolution`, `GeometricContraction`, `GaussianContractionBound`).
- Quasimode inversion and finite-reading certificates for complete Weil inverses (`WeilGreenModes`,
  `WeilGreenTail`).
- Bessel flux/Wronskian band estimates (`BesselSpectralBand`, `BesselBarrierPayment`, `BesselGaussianReserve`).

**To build**
- Compact-center payment for the native successor as rank grows (band term of the global-minimizer split).
- Joint estimate of all complete Weil directions against the vanishing ground reserve c^{−7} on
  c_N ≫ (log N)^{1/4}.
- Arithmetic upper bound for the Chebyshev cyclotomic remainder (near-constant modes).
- Inner-cutoff-strength bound for accumulated Euler-deletion covariance.
- Sign control of divisor-character traces in Wigner fibres; polynomial-weighted control outside the band.

## 7. Open questions

1. Exact growth of κ(x) between √q and q.
2. Does native compensation pay the compact center band at all ranks (RH-equivalent all-order hierarchy)?
3. Can fixed-packet positivity at (log N)^α, α < 1/40, extend to full-matrix positivity at α > 1/4
   (RH-equivalent for the tilted spline)?
4. Which arithmetic relation bounds the near-constant cyclotomic Chebyshev modes by N^{3/2+ε} or N^{5/3+ε}?
5. Which nonlinear source coordinate transfers positivity back to physical derivatives (clock pullback)?
6. Is the (log N)^{1/40} packet exponent improvable by sharper residual decay than 1/√log N?

## 8. Traps

| Trap | Fact |
|---|---|
| Use a fixed fraction of each native diagonal as reserve | Successor fraction ≤ (2/3)^N; no rank-uniform relative reserve |
| Keep only the first theta atom | Negative signed moment at every center; finite failing rank |
| Infer mixed-head positivity from moment signs | Clock cone at B < 3: all moments ≥ 0, some head fails |
| Transport positivity through an invertible clock | Clocked first atom PD at all ranks; physical pullback fails |
| Treat truncated and completed energies as equal | Source vs probe support differ by (T b_T)²; energy not monotone in T |
| Bound successors via inverse perturbation | Use successor comparison: same η, no conditioning factor |
| Read compactness as trace class | Conductor Green operator compact but Σ E_m^{−k} = ∞ for all k |
| Spend the ground reserve at growing overlap | E_m(c) ≍ c^{−7}: residuals must decay relative to c^{−7} |
| Apply periodic-continuation argument to the full theta series | Complete series summable only where cos(2 Im z) > 0 |
| Pointwise local positivity ⇒ integrated successor sign | Integrated inverse is nonlocal; use global-minimizer test |
| Exchange fixed and exhausting quantifiers | Every horizon here is rank-, conductor- or overlap-dependent |

## 9. Context

**Uses** (import counts): RHTower 20, HTGeometry 19, CriticalArithmeticCorrelationTheory 14,
TransMetzlerWeilPositivity 3, SignedArithmeticHodgeTheory 2, BezoutValuationIncidence 2,
SpacingScaleHarmonicAnalysis 1, RenormalizedArithmeticPotentialTheory 1, BiScaleUncertainty 1,
ArithmeticIntersectionTheory 1.

**Used by**: SuccessorShellArithmetic (`FixedConductorPacketsArePositiveBelowTheNineteenthRoot` imports
`WeilGrowingPackets`); `MainTheorems`.

| Neighbour | Relation |
|---|---|
| CriticalArithmeticCorrelationTheory | Supplies complete Weil matrix, pole ground state, bounded-overlap positivity, residual pieces; CAF adds sharp inverse cost, Green modes, growing-overlap packets |
| RenormalizedArithmeticPotentialTheory | Conductor energies, Ramanujan packet diagonalization; log-overlap Weil positivity ⇔ RH |
| TransMetzlerWeilPositivity | Plateau prefix and Young range feed the index ceiling and the cost-20 prefix payment |
| RHTower ThetaCusp | Native jets, rank-7 strictness, successor source, seam Gram; CAF supplies all-rank horizons |
| SignedArithmeticHodgeTheory | Uniform residual and Gram budgets for growing Ramanujan families |
| SuccessorShellArithmetic | Continues packet positivity at larger overlap exponents |

## 10. Big picture

The programme shows that every RH-equivalent complete form studied here is positive on every fixed finite
piece, with explicit and usually sharp horizons, and that the remaining difficulty is always a single
exhaustion: rank for the theta hierarchy, overlap for the Weil matrix, cutoff for Euler deletion, frequency
near the constant mode for Chebyshev energy. Exact completions show where the unpaid part lives; it is
never a hidden defect of the method but a precisely located compact region or near-constant band.

The repeated lesson is that reserves degrade at a definite rate (fraction (2/3)^N, floor c^{−7}, failing rank
between √q and q) while the sources supply payments at their own rates (quadratic degree cost, 1/√log N
residuals). RH-strength conclusions require the payment rate to beat the reserve decay along the full
exhaustion. The programme makes both rates explicit and shows that, where they currently fail to meet, no
change of normalization or coordinate (clocks, truncations, single atoms) closes the gap by itself.
