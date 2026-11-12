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
`∝ Σ_𝔞 c_𝔞³` (constant terms `c_𝔞 v^{2/3}` of θ_s at the cusps 𝔞; on the rational orbit `c_𝔞³ = c³`,
no cancellation since `κ³ = 1`); then `S` has a simple pole at 2/3 (via `thetaSquareDirichlet_eq`).
- 2a. Size of `T_s` at ramified frequencies `uλ^k a b³`: `T(hb³) = |b|T(h)`, prime factors `|·| ≤ 1`
  (`rationalSourceResidualFourierCoefficient_prime_factor`) reduce to `T(uλ^k)`; need a bound in k
  (ramified local factor) or a Hecke bound from a uniform growth bound of θ_s (Ford cover, all cusp tails).
- 2b. Mellin link: `∫_0^∞ v^{s−3}(A(v) − const-mode²) dv = |P| M(s) Σ_h T(h)²(4π|ξ_h|)^{−s}`, `M(s) = ∫ t^{s−1}K_{1/3}(t)²`.
- 2c. Eisenstein series at every cusp / seeds at every cusp tail; constant terms `φ_{∞𝔞}(s) v_𝔞^{2−s}`.
- 2d. Continuation of `E` along `{Re s > 1, Im s > 0} ∪ B(4/3, ε)` (MMD corrected family) with the cusp
  expansion (constant term + rapidly decreasing) at every cusp, uniformly near 4/3.
- 2e. Truncated pairing `I(s,T) = ∫ θ_s² (E(s) − 1_{v>T} v^s)` (converges for Re s > 4/3), equal to
  `|P| ∫_0^T v^{s−3} A(v) dv` for Re s > 2 (unfolding, done for compact profiles).
- 2f. Pole bookkeeping: `∫_T^∞ c_𝔞² v^{4/3} φ_{∞𝔞}(s) v^{2−s} v^{−3}` gives the double pole; residual part
  `⟨θ_s², θ̃⟩` the next coefficient.

## Lean modules
| Module | Content | State |
|---|---|---|
| `TheCubicEisensteinSeriesUnfolds` | `CuspDomain` (strict fundamental sets of Γ∞), `cuspSelect` (one element per coset), `tsum_indicator_smul`, `incompleteEisenstein`, `integral_mul_incompleteEisenstein`, `lintegral_norm_mul_incompleteEisenstein`, `integral_mul_hyperbolicEisenstein` | clean; olean built |
| `TheIncompleteEisensteinSeriesReadsTheConstantTerm` | `translationOf` (Γ∞ ≅ 3O), `cuspStrip_unique`, `CuspDomain.strip`, `cuspStrip_coordinates` (integrability + v^{−3} dv dz), `integral_mul_incompleteEisenstein_eq_constantTerm`, `integral_mul_hyperbolicEisenstein_eq_constantTerm` | clean |
| `TheSquareOfTheCubicThetaUnfolds` | θ = `cubicResidualFunction` (MMD olean built 2026-11-12 10:12 from the 10:02 source); `thetaSq_automorphy`; Parseval on P (`integral_nonzeroSeries_sq`); `integral_thetaSq_periodDomain`; `thetaAmplitude_mul_neg` (Bessel form); `integral_thetaSq_mul_incompleteEisenstein(_of_compact)` (SQ3) | clean |
| `TheSquareOfTheSourceThetaUnfolds` | generic Parseval `integral_cuspCharacterSeries_sq`; generic RS `integral_sq_mul_incompleteEisenstein`; θ_s instance (multiplier via `RationalSource.extendedComplexCharacter_restrict`); `sourceAmplitude_mul_neg` (T_s(h)² v² K²) | clean |
| `TheCubeFrequenciesOfTheThetaSquareFactorOut` | uniqueness of A·B³ (`thetaSquarefreePart_mul_cube`, `thetaCubePart_mul_cube`, `mul_cube_injective`); `sourceCoefficient_sq`; `normWeight_shift`; `thetaSquareDirichlet_eq` (Σ_I N^{−w}T_s² = C̄² Z₀(3w−1) S(w), Re w>1, unramified ideals) | clean |
| `TheConstantTermContinuesAcrossFourThirds` | `clearedScattering` = (s−4/3)φ(s) via zetaPoleFilled·L(χ₋₃)/Z₀; holomorphic on Re s>1; value r at 4/3; `dedekindZeta_residue_eq`; `clearedConstantTerm` (residue 3πr v^{2/3}); `hasDerivAt_clearedConstantTerm` (log term) | clean |

## Notes
**N1 [D] Mechanism of the double pole** (see CRF card N12): `E_{κ²}` constant term `v^s + φ(s)v^{2−s}`,
`φ ~ r/(s − 4/3)`; `E* = lim (E − r θ̄'/(s − 4/3))` has constant term `v^{4/3} − r v^{2/3} log v + φ₀ v^{2/3}`;
`θ² − c²E* ∈ L²`; its small-height constant term `~ B v^{2/3}` (residual) `+ O(v^{1−ε})`; hence
`Σ T²W² = B' v^{2/3} − c² r v^{2/3} log v + O(v^{1−ε})` and a double pole of the Mellin transform at 4/3.

## Conjecture ledger

## Log
- 2026-11-12 — (1) arithmetic side done: RS for θ_s², cube factorization. Open in (1): ramified frequencies (no polynomial bound on T_s(λ^k·)), element-vs-ideal bookkeeping (±primary), bridge σ(A) ↔ CRF γ₂(A)² (cubicUnitGaussSum 1 a vs sexticGaussPow 2 a 1).
- 2026-11-12 — created; README first draft; modules 1–4 clean (SQ1, SQ3 done; SQ2/SQ4 constant-term part done). Next: small-height asymptotics of A(v) = c²v^{4/3} + Σ a a (spectral side, renormalization) — needs E continued as a function with growth and the spectral expansion of θ² − c²E*.
