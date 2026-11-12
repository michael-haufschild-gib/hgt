# Spectral theory of the cubic cover (STCC)

- **ID:** stcc
- **Stage:** 1-in-progress
- **Type:** programme card (goal loop)
- **Source:** CRF Q1 (B175): the long columns are first moments of `γ₂²`; user chose "option 1"
  (2026-11-12): global continuation of the cubic Eisenstein series, then the regularized
  Rankin–Selberg integral of `θ²`.
- **Statement:** prove SQ1–SQ5 of `formal/GaloisForLFunctions/SpectralTheoryOfTheCubicCover/README.md`.

## Roadmap
1. Unfolding (SQ1): `∫_{D_Γ} F·E(·∣ψ) = ∫_{D_∞} F·ψ(v)` for `F` of multiplier `κ^{−1}`; complete
   series as `ψ(t) = t^s`. Tools: `hyperbolicFundamentalSet_unique` (strict), Mathlib
   `IsFundamentalDomain.integral_eq_tsum''`, `lintegral_eq_tsum''`, `hyperbolicEisenstein_eq_height_series`,
   `cosetHeight_cosetOf`, `row_eq_iff_left_cusp`.
2. Cusp strip: `D_∞` vs `P × (0, ∞)` (`TheCubicCuspPeriodLattice`, `CubicCuspVolumeCoordinates`);
   `∫ F ψ(v) = ∫_0^∞ ψ(v) a₀(F; v) |P| v^{−3} dv`.
3. Continuation of `E` as a function (SQ2) from MMD's seed + resolvent (`TheCubicInitialResolventMatching`,
   `LocalCubicCorrectedSeeds`, `TheCubicIncomingResidue`); growth.
4. Constant term of `θ²` (SQ3): needs `θ`'s Fourier–Bessel expansion (`WeightedCubicResidualFourierTests`,
   no olean, peer-edited) — wait for it or rebuild the needed part.
5. Renormalization and the double pole (SQ4); Mellin transfer to `D(w)` (SQ5).

## Roadmap (2): the spectral side (user: "continue 1, then 2")
Target: `D_s(w) = Σ_{h≠0} T_s(h)² N(h)^{−w}` has a double pole at `w = 2/3`, leading coefficient
`∝ c³` (`c = 3πr` the constant-term coefficient of θ_s); then `S` has a simple pole at 2/3 (via
`thetaSquareDirichlet_eq`). Route (no pointwise continuation of E needed; only MMD's L² meromorphy):
- 2a [done, module 8] Hecke bound `|T_s(h)| ≤ C(1+|ξ_h|)` for all h ≠ 0 (ramified included).
- 2b [done, module 9] Mellin link `∫_0^∞ v^s R(v) v^{−3} = M(s)·Σ_{h≠0} T_s(h)²(4π|ξ_h|)^{−s}`, Re s > 4;
  `M` holomorphic on Re s > 2/3, `M(4/3) ≠ 0`; constant term of θ_s² = `b(v,0)² + R(v)`.
- 2c Pairing continuation: for G of multiplier κ⁻¹, G ∈ L² (kernel quotient), exponentially small at
  cusp ∞: `Φ_G(s) = ∫_{D_Γ} G·E(s)` (Re s > 2) equals `∫G·seed(s) + ∫G·Corr(s)` for Re s > 4, Im s > 0
  (MMD `kernelEisensteinL2Correction_initial_overlap`, a = 2, b = 3), hence continues to
  `{Re s > 1, Im s > 0} ∪ B(4/3, ε)` with at most a simple pole at 4/3 (`kernelEisensteinCorrectionNumerator_*`).
- 2d The subtraction `H = 4c²·Proj(E_κ̄(·|η v^{4/3}))` (η = smooth cutoff, 0 below 1, 1 above 2) and
  `G = θ_s² − H`: G is Γ_rat-equivariant, `θ_s² − c²v^{4/3}` is exponentially small at ∞ (rational cusps
  by equivariance), θ_s is exponentially small at the two primitive ramified cusp classes
  (`three_cusp_decomposition`, `ramifiedSource_exponential_decay`), H vanishes high in them ⇒ G ∈ L².
- 2e Scattering of H: with compact profiles f_T and both unfoldings,
  `Mellin(a₀(H_T) − c²f_T)(s) = 4c² Φ_rat(s) ∫ f_T v^{−1−s} dv`, `Φ_rat` = v^{2−s} coefficient of the
  constant term of `E_rat(s) = Proj E(s)`; T → ∞ for Re s > 2. Needs the constant term of E(s) at every
  height (check MMD Fourier expansion of `hyperbolicEisenstein`).
- 2f Continuation of Φ_rat from L²: `Φ_rat(s)·∫g v^{−1−s} = ⟨Proj Corr(s), E_κ̄(·|g)⟩` for g supported
  high in the cusp; simple pole at 4/3 with residue from the constant term of θ_s (`Proj Res = θ_s`).
- 2g Assembly: `|P| M_R(s) = Φ_G(s) − |P|c² ∫(1−η)v^{s−5/3} + c²·4Φ_rat(s) f̃(s)`, `f̃(s) = 1/(s−4/3) + entire`
  ⇒ M_R has a double pole at 4/3 with coefficient `∝ c² Res Φ_rat ≠ 0`; divide by M(s).

## Roadmap (3): the twisted layer (user: "continue with the twisted layer")
Goal: the nine twists `P_{a,r}(s) = Σ_{h' primary} (ω^aλ^r/h')₃² T(h')² |ξ_{h'}|^{−s}` (a, r mod 3), whose
untwisted member is `Z₀(3w−1)·S` (CRF's squarefree series); D is one combination of them.
- T1 [done, `TheSquaredThetaSeriesSplitsIntoNineTwists`] `T(h₀ g)T(1) = (h₀/g)₃T(h₀)T(g)` (h₀ coprime to
  g = gen I); split `h = uλ^m gen I`; `D(s) = C̄² Z₀(3s/2−1) Σ_{u,m} (T(uλ^m)/T(1))² (4π|ξ_{uλ^m}|)^{−s} S_{uλ^m}(s/2)`,
  `S_{h₀}(w) = Σ_{A sqfree} (h₀/gen A)₃² σ(A) N(A)^{−w}`; twist depends on (u mod ±1, m mod 3); source mask:
  `T(uλ) = 0`, `T(u) ≠ 0 ⇒ u = ±1`. So `Q = 2(4π|ξ₁|)^{−s} S_1(s/2) + Σ_{m≥2}`.
- T1b [done, `TheTwistedSquarefreeCombinationHasASimplePole`] `Q` (the combination) continues; `(s−4/3)M(s)Q(s) →
  243π³r³/(C̄² L(1,χ₋₃)) ≠ 0`. One linear relation among the nine residues `ρ_{a,r} = Res_{w=2/3} S_{aλ^r}`.
- T2a [done, `TheRotatedCorrelationsSeeOnlyTheThreeDivisibleLayer`] `C_ε(s) = Σ T(εh)T(h)|ξ|^{−s} =
  C̄² Z₀ Σ_{u,m} (T(εuλ^m)T(uλ^m)/T(1)²)(…)^{−s} S_{ε²uλ^m}(s/2)`; for ε ≠ ±1 only m ≥ 2 (unit layer invisible).
- Finding: every coefficient of these relations at m ≥ 2 is a ramified value T(uλ^m); MMD writes these through
  `lowRamifiedTransform` of the nine Patterson residues `U_{j,k} = unramifiedGaussResidue(ω^jλ^k)`, which the
  corpus does not determine. Rotations add relations but cannot isolate `ρ_{1,0}` (S_1) without U_{j,k} or the
  3-part (level 27).
- T2b/T3 [done] `(s−4/3)²M(s)C_ω(s) → 54π³r³` (`rotatedCorrelation_double_pole`): linear subtraction `h` of θ_s
  (`TheThetaFunctionHasALinearCuspSubtraction`), `R = diag(ω,ω²)`, `h(Rw)h(R⁻¹w) = H_R` = two-cusp subtraction
  (cusps ∞, 0), `G_R` bounded (`TheRotatedThetaProductHasATwoCuspSubtraction`), partial subtractions scatter with
  `Φ_k = |P|(π/(s−1))φ + k(π/(s−1))U` (`PartialCuspSubtractionsScatter`), constant term + Mellin link
  (`TheRotatedThetaProductReadsTheRotatedCorrelation`), assembly (`TheRotatedCorrelationHasADoublePole`).
  Corollary (`TheThreeDivisibleLayerHasASimplePole`): `(s−4/3)M(s)Q₃(s) → 243π³r³/(2C̄²L(1,χ₋₃))` — the
  three-divisible layer carries exactly half of Res Q. Relations now: Res Q = 2e₀ρ_{1,0} + R_D(≥2), Res Q₃ = Res Q/2;
  S_1 still not separated (coefficients T(uλ^m), m ≥ 2, unknown).
- Next candidates: (i) Hecke-at-9 correlation `θ_s(Aw)θ_s(A⁻¹w)`, `A = diag(λ,λ⁻¹)`: multiplier κ² on
  Γ_A = Γ(3)∩{b,c ≡ 0 mod 9} (index 81), constant term `Σ T(h)T(9h·unit)`; links layer m to m+4; needs the
  trace to Γ (81 cosets, cusp analysis); (ii) T4 below; (iii) the nine U_{j,k}.
- T4 [λ-twists] level 9: `(λ/d)₃` is a character of Γ(3) trivial on Γ(9) but not a conjugate of κ by any
  element normalizing Γ(3); needs translates `θ_s(w + t)`, `t ∈ (1/3)O`. Rank question: do the available
  combinations determine all nine residues?

## Lean modules
| Module | Content | State |
|---|---|---|
| `TheCubicEisensteinSeriesUnfolds` | `CuspDomain` (strict fundamental sets of Γ∞), `cuspSelect` (one element per coset), `tsum_indicator_smul`, `incompleteEisenstein`, `integral_mul_incompleteEisenstein`, `lintegral_norm_mul_incompleteEisenstein`, `integral_mul_hyperbolicEisenstein` | clean; olean built |
| `TheIncompleteEisensteinSeriesReadsTheConstantTerm` | `translationOf` (Γ∞ ≅ 3O), `cuspStrip_unique`, `CuspDomain.strip`, `cuspStrip_coordinates` (integrability + v^{−3} dv dz), `integral_mul_incompleteEisenstein_eq_constantTerm`, `integral_mul_hyperbolicEisenstein_eq_constantTerm` | clean |
| `TheSquareOfTheCubicThetaUnfolds` | θ = `cubicResidualFunction` (MMD olean built 2026-11-12 10:12 from the 10:02 source); `thetaSq_automorphy`; Parseval on P (`integral_nonzeroSeries_sq`); `integral_thetaSq_periodDomain`; `thetaAmplitude_mul_neg` (Bessel form); `integral_thetaSq_mul_incompleteEisenstein(_of_compact)` (SQ3) | clean |
| `TheSquareOfTheSourceThetaUnfolds` | generic Parseval `integral_cuspCharacterSeries_sq`; generic RS `integral_sq_mul_incompleteEisenstein`; θ_s instance (multiplier via `RationalSource.extendedComplexCharacter_restrict`); `sourceAmplitude_mul_neg` (T_s(h)² v² K²) | clean |
| `TheCubeFrequenciesOfTheThetaSquareFactorOut` | uniqueness of A·B³ (`thetaSquarefreePart_mul_cube`, `thetaCubePart_mul_cube`, `mul_cube_injective`); `sourceCoefficient_sq`; `normWeight_shift`; `thetaSquareDirichlet_eq` (Σ_I N^{−w}T_s² = C̄² Z₀(3w−1) S(w), Re w>1, unramified ideals) | clean |
| `TheCuspHeightsOfAPointAreSparse` | lattice points in a disc; at most `K/Y²` cusp cosets give a point height `≥ Y` (`card_cuspCosets_height_le`) | clean; olean built |
| `TheThetaCoefficientsHaveTheHeckeBound` | one-coefficient Parseval bound; strip lintegral coordinates; `∫_{D_Γ}|θ_s|² < ∞` (L² residue + `levelSet ⊆` kernel set); unfolding bound on `[Y,2Y]`; `sourceCoefficient_hecke_bound` | clean; olean built |
| `TheMellinTransformOfTheThetaSquareReadsItsDirichletSeries` | `|K_{1/3}(x)| ≤ Cx^{−1/3}e^{−x/2}`; `M(s)` holomorphic on Re s > 2/3, `M(4/3) ≠ 0`; `Σ_{h≠0}|ξ_h|^{−t}` (t > 2, ZLattice); `tsum_amplitude_mul_neg`; `integral_thetaSqRemainder` (Re s > 4) | clean; olean built |
| `TheEisensteinPairingContinuesAcrossFourThirds` | `levelPairing` (u ↦ ∫_{D_Γ} G·u, CLM on L² of the kernel quotient via the measure-preserving pullback); `∫_{D_Γ}G·E(s) = ∫G·seed(s) + ⟨G,Corr(s)⟩` (Re s>4, Im s>0); correction pairing analytic off ℝ, `(s−4/3)⟨G,Corr⟩ = ⟨G,N(s)⟩`, N(4/3) = residue; seed term = Mellin of a₀(G) against χv^s | clean; olean built |
| `TheThetaSquareHasARationalCuspSubtraction` | `cosetHeight_translate_le` (bottom-left c of x·g caps height at 1/(\|c\|²v)); `cuspSubtraction` H_S = c²Σ_q conj(E_1(r_q w∣f_S)); multiplier κ⁻¹; `cuspSubtraction_upper` (= c²f_S(v) above height 1/2); `setIntegral_levelSet_translate` | clean; olean built |
| `TheRationalCuspSubtractionScatters` | strip-bounded functions pair with E(s) (absolute unfolding); unfolding of conj E_1(·∣f); constant terms of E(s), E(s)∘S (MMD); truncated identity; `integral_scatterPart`: Mellin(a₀(H) − \|P\|c²f) = c²Φ(s)·∫f v^{−1−s} (Re s>10/3), Φ = \|P\|(π/(s−1))φ + 3(π/(s−1))U | clean; olean built |
| `TheRenormalizedThetaSquareIsBounded` | `G = θ_s² − H` (c = 3πr): rational equivariance of \|G\| (κ̃³ = 1); `lowerLeft_ramified_ne_zero` (r₁₀ + r₁₁ω^j ≢ 0 mod 3); H = 0 through ramified cusps; `renormalizedThetaSq_bounded`, `_memLp`; `O(v^{−7/3})` high; a₀(G) = \|P\|(c²v^{4/3} + R) − a₀(H) | clean; olean built |
| `TheRenormalizedThetaSquareUnfolds` | strip bound ∫\|G\|v^σ < ∞ (2 < σ < 13/3); explicit Mellin integrals; Φ₀ = (π/(s−1))\|P\|(s−4/3)φ·(3·3^{3s−3}−1)/2, Φ₀(4/3) = 12π\|P\|r; `integral_renormalized_mul_eisenstein` (4 < Re s < 13/3) | clean; olean built |
| `TheSquaredThetaSeriesHasADoublePole` | `seedPair` holomorphic (Mellin, 0 < Re s < 13/3); `completedThetaSq` = continuation of M(s)D(s); **`thetaSqDirichlet_double_pole`**: (s−4/3)²M(s)D(s) → 108π³r³ ≠ 0; axioms: propext, choice, Quot.sound | clean; olean built |
| `TheConstantTermContinuesAcrossFourThirds` | `clearedScattering` = (s−4/3)φ(s) via zetaPoleFilled·L(χ₋₃)/Z₀; holomorphic on Re s>1; value r at 4/3; `dedekindZeta_residue_eq`; `clearedConstantTerm` (residue 3πr v^{2/3}); `hasDerivAt_clearedConstantTerm` (log term) | clean |
| `TheSquaredThetaSeriesSplitsIntoNineTwists` | `sourceCoefficient_twisted_mul`; `frequencySplit` (Oˣ×ℕ×GoodIdeal ≃ O∖0); `twistedPrimarySeries_eq` (P = C̄²Z₀(3w−1)S); `thetaSqDirichlet_eq_zeta_mul`; `_neg`, `_lambda_mod`; `sourceCoefficient_unit_mul_lambda`, `sourceCoefficient_unit_eq` | clean; olean built |
| `TheTwistedSquarefreeCombinationHasASimplePole` | `clearedCubeZeta`; `completedCombination`; `twistedSquarefreeCombination_simple_pole` (residue 243π³r³/(C̄²L(1,χ₋₃))) | clean |
| `TheRotatedCorrelationsSeeOnlyTheThreeDivisibleLayer` | `rotatedCorrelation`, `symbol_rotated_pair`, `rotatedCorrelation_eq_zeta_mul`, `rotatedLayerCoeff_zero/_one`, `rotatedCorrelation_eq_three_layer` | clean |
| `TheThetaFunctionHasALinearCuspSubtraction` | `thinProfile`, `linearSubtraction` (multiplier κ, rational-equivariant), `thetaLinear`, `cusp_reduce`, `thetaLinear_bounds` (|θ_s−h|(1+v^{2/3}) ≤ B through every cusp) | clean; olean built |
| `TheRotatedThetaProductHasATwoCuspSubtraction` | `rotation`, `complexCharacter_rotation_pair`, `rotatedThetaProduct` (multiplier κ⁻¹), `cutoff_rotation_mul`, `rotation_cross_zero` (mod 3), `thetaLinear_rotation_mul` (= `rotatedSubtraction`), `rotatedRenormalized_bounded`, `_memLp` | clean; olean built |
| `PartialCuspSubtractionsScatter` | `partialSubtraction Q`, per-cusp unfolding, `integral_partialSubtraction_trunc_mul_eisenstein`, `integral_partialScatterPart` (Φ_k, k = |Q|−1) | clean; olean built |
| `TheRotatedThetaProductReadsTheRotatedCorrelation` | `rotation_smul_upperPoint`, `integral_cuspCharacterSeries_mul` (bilinear Parseval), `cuspConstantTerm_rotatedThetaProduct`, `integral_besselRemainder` (general Mellin link), `besselDirichlet_rotatedCoeff` (= C_ω) | clean; olean built |
| `TheRotatedCorrelationHasADoublePole` | `norm_rotatedRenormalized_high`, `integral_rotatedRenormalized_mul_eisenstein`, `clearedRotScatter` (6π\|P\|r at 4/3), `completedRotated`, **`rotatedCorrelation_double_pole`** (54π³r³) | clean; olean built |
| `TheThreeDivisibleLayerHasASimplePole` | `threeLayerCombination`, `threeLayerCombination_simple_pole` (243π³r³/(2C̄²L(1,χ₋₃))) | clean |

## Notes
**N1 [D] Mechanism of the double pole** (see CRF card N12): `E_{κ²}` constant term `v^s + φ(s)v^{2−s}`,
`φ ~ r/(s − 4/3)`; `E* = lim (E − r θ̄'/(s − 4/3))` has constant term `v^{4/3} − r v^{2/3} log v + φ₀ v^{2/3}`;
`θ² − c²E* ∈ L²`; its small-height constant term `~ B v^{2/3}` (residual) `+ O(v^{1−ε})`; hence
`Σ T²W² = B' v^{2/3} − c² r v^{2/3} log v + O(v^{1−ε})` and a double pole of the Mellin transform at 4/3.

## Conjecture ledger

## Log
- 2026-11-12 — T2b/T3 formalized: rotated correlation double pole 54π³r³ (half of D), three-divisible layer simple pole; product trick (θ_s − h)(R·)θ_s(R⁻¹·) + h(R·)(θ_s − h)(R⁻¹·) avoids rotated cusp analysis.
- 2026-11-12 — twisted layer T1, T1b, T2a formalized; ramified layer reduces to MMD's nine U_{j,k}; T2b (rotated renormalization) planned via the linear subtraction h.
- 2026-11-12 — **SQ4 answered in Lean**: `thetaSqDirichlet_double_pole` (modules 13–15). Route: bounded renormalization G = θ_s² − H + MMD's L² correction (no pointwise continuation of E); double pole only from the explicit scattering of H. Open: SQ5 (element sum ↔ unramified squarefree series S; contour shift for complex T²), SQ7 (column twists θ·θ_n).
- 2026-11-12 — 2c–2e formalized (modules 10–12). Remaining: G = θ_s² − H bounded on H³ (reduction + three cusp classes; mod-3 residue of r_q c_j bottom-left ≠ 0), assembly with clearedScatterTotal = (π/(s−1))\|P\|·clearedScattering·(3·3^{3s−3}−1)/2 (value 12π\|P\|r at 4/3); polynomial cusp decay v^{−7/3} suffices (region 1 < Re s < 13/3).
- 2026-11-12 — (2) started: 2a Hecke bound and 2b Mellin link formalized (modules 7–9); roadmap (2) rewritten around MMD's L² meromorphy (2c–2g).
- 2026-11-12 — (1) arithmetic side done: RS for θ_s², cube factorization. Open in (1): ramified frequencies (no polynomial bound on T_s(λ^k·)), element-vs-ideal bookkeeping (±primary), bridge σ(A) ↔ CRF γ₂(A)² (cubicUnitGaussSum 1 a vs sexticGaussPow 2 a 1).
- 2026-11-12 — created; README first draft; modules 1–4 clean (SQ1, SQ3 done; SQ2/SQ4 constant-term part done). Next: small-height asymptotics of A(v) = c²v^{4/3} + Σ a a (spectral side, renormalization) — needs E continued as a function with growth and the spectral expansion of θ² − c²E*.
