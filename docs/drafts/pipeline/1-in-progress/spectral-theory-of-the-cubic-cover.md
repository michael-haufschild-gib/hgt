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
| `TheConstantTermContinuesAcrossFourThirds` | `clearedScattering` = (s−4/3)φ(s) via zetaPoleFilled·L(χ₋₃)/Z₀; holomorphic on Re s>1; value r at 4/3; `dedekindZeta_residue_eq`; `clearedConstantTerm` (residue 3πr v^{2/3}); `hasDerivAt_clearedConstantTerm` (log term) | clean |

## Notes
**N1 [D] Mechanism of the double pole** (see CRF card N12): `E_{κ²}` constant term `v^s + φ(s)v^{2−s}`,
`φ ~ r/(s − 4/3)`; `E* = lim (E − r θ̄'/(s − 4/3))` has constant term `v^{4/3} − r v^{2/3} log v + φ₀ v^{2/3}`;
`θ² − c²E* ∈ L²`; its small-height constant term `~ B v^{2/3}` (residual) `+ O(v^{1−ε})`; hence
`Σ T²W² = B' v^{2/3} − c² r v^{2/3} log v + O(v^{1−ε})` and a double pole of the Mellin transform at 4/3.

## Conjecture ledger

## Log
- 2026-11-12 — (2) started: 2a Hecke bound and 2b Mellin link formalized (modules 7–9); roadmap (2) rewritten around MMD's L² meromorphy (2c–2g).
- 2026-11-12 — (1) arithmetic side done: RS for θ_s², cube factorization. Open in (1): ramified frequencies (no polynomial bound on T_s(λ^k·)), element-vs-ideal bookkeeping (±primary), bridge σ(A) ↔ CRF γ₂(A)² (cubicUnitGaussSum 1 a vs sexticGaussPow 2 a 1).
- 2026-11-12 — created; README first draft; modules 1–4 clean (SQ1, SQ3 done; SQ2/SQ4 constant-term part done). Next: small-height asymptotics of A(v) = c²v^{4/3} + Σ a a (spectral side, renormalization) — needs E continued as a function with growth and the spectral expansion of θ² − c²E*.
