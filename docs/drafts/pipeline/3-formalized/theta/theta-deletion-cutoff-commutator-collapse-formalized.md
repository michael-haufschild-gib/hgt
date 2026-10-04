# The chronological theta cutoff commutator collapses to a Möbius Gaussian boundary source — Lean certificate

- **Paper card:** `theta-deletion-cutoff-commutator-collapse.md`
- **Lean modules (umbrella `GaloisForLFunctions.RHTower`):**
  - `ThetaCutoffCommutatorShell`: (1), (2) with the moving limit, (3a) Euler summation, (3b), (3c).
  - `ThetaCutoffCommutatorCofinalLimit`: flux-atom form of `C_S`, (4) cofinal limit, `sup_{S,y}|C_S| ≤ 1`, (3d), (3e), (3f).
  - `ThetaCutoffCommutatorMellin`: (3) Mellin law of `C_S`, zero integral, (3g), (5).
  - `ThetaCofinalCurrentSignChanges`: Landau's theorem for countable closed singular sets, both signs of `C_∞` at the negative cusp.
  - `ThetaPrimeScheduleSpectralObservation`: prime supply in multiplicative windows, phase-selected prime sets, (3h), (3k).
  - `ThetaNaturalScheduleEulerOscillation`: complex Abel summation against `θ`, (3i), (3j), and the natural-schedule oscillation of `|E|` and of the raw spectral observation.
- **Verification:**
  - Targeted `lake build --old` of every module; final `lake env lean` audit clean on each source.
  - `#print axioms` = `propext`, `Classical.choice`, `Quot.sound` for every declaration of the six modules (157 + 51).
  - No `sorry`, no new axiom, no heartbeat options.
  - Hypotheses are only the card's quantifiers: finite prime sets, `N ≥ 1`, prime exhaustions, finite complex Borel measures, Mellin parameters in the stated half-planes, `1/2 < σ < 1` (and `0 < σ < 1` for (3i)), `τ ≠ 0` for the oscillation statements.

Dictionary:
- `a_n = thetaCuspSourceTerm · n`; `K_N = integerCutoffThetaSource N`; `C_{S,N} = cutoffCommutatorSource S N`.
- `e^{(y−log N)/2}C_{S,N}(y−log N) = movingCommutatorDensity S N y`; `C_S = commutatorBoundaryProfile S`; `C_∞ = cofinalBoundaryProfile`.
- `q_y = movingSeedProfile y`; `A_S = roughDiscrepancy S`; `R_S = roughCount S`; `H_{S,N} = roughTailDiscrepancy S N`; `η = roughDensity`.
- `G(z) = commutatorGammaFactor z`; `E_S(s) = finitePrimeEulerProduct S s`; `H_N = harmonicCutoff N`; `H^rough_{S,N} = roughHarmonicCutoff S N`.
- `M_{S,N}(z) = commutatorSpectralObservation S N z`; natural schedule `S_N^nat = Nat.primesLE N`.

| Card item | Lean theorem |
|-|-|
| **(1)** exact shell `C_{S,N} = Σ_{d|P} μ(d) Σ_{N<dn≤dN} a_{dn}`; one prime: `−Σ_{N<m≤pN, p|m} a_m` | `cutoffCommutatorSource_eq`, `cutoffCommutatorSource_singleton`, `roughCutoffThetaSource_eq`, `sum_filter_coprime_eq`, `thetaPrimeDeletion_integerCutoffThetaSource` |
| **(2)** moving limit, uniform in `y` | `tendstoUniformly_movingCommutatorDensity`, `movingCommutatorDensity_eq` |
| **(2)** closed form `−2πe^{3y}[Σ μ(d)d²e^{−πd²e^{2y}} − E_S(1)e^{−πe^{2y}}]` | `commutatorBoundaryProfile_eq`, `commutatorBoundaryProfile_eq_flux`, `prod_one_sub_inv_eq_sum_powerset` |
| zero ordinary integral of each `C_S` | `integral_commutatorBoundaryProfile` |
| **(3)** `∫e^{zy}C_S = G(z)[E_S(1) − E_S(1+z)]`, `Re z > −3` | `integral_cexp_mul_commutatorBoundaryProfile`, `integral_cexp_mul_thetaFluxTerm` |
| **(3a)** exact shell quadrature error | `shell_quadrature_error`, `sum_Ioc_floor_eq_integral`, `integral_fract_mul_deriv_cell` |
| **(3b)** `A_S(X) = X E_S(1) − R_S(X)` | `roughDiscrepancy_eq` |
| **(3c)** sieve discrepancy identity for `Δ_{S,N}` | `movingCommutatorDensity_sub_eq` |
| **(3d)** `η_N → 0` along every prime exhaustion | `PrimeExhaustion.tendsto_roughDensity`, `roughCount_le`, `roughCount_anti`, `PrimeExhaustion.tendsto_prod_one_sub_inv` |
| bounds `|A_S(Nt)|/N ≤ tη_N`, `|H_{S,N}(t)|/N ≤ t(η_N + 1/N)` | `abs_roughDiscrepancy_le_mul_roughDensity`, `abs_roughTailDiscrepancy_le_density`, `card_filter_prod_lt_le` |
| seed bounds `sup|q_y(1)| < ∞`, `∫t|q_y'| ≤ ∫u|h'|` | `exists_abs_mul_thetaCuspSeed_le`, `integral_mul_abs_seedProfile_deriv_le`, `seedDerivMoment` |
| **(3e)** `sup_y |Δ_{S_N,N}(y)| ≤ C(η_N + 1/N) → 0`; joint limit `C_∞` locally uniformly | `exists_abs_movingCommutatorDensity_sub_le`, `PrimeExhaustion.tendstoUniformly_movingCommutatorDensity_sub`, `PrimeExhaustion.tendstoUniformlyOn_movingCommutatorDensity` |
| `sup_{S,y}|C_S(y)| < ∞` | `abs_commutatorBoundaryProfile_le` |
| **(3f)** every finite complex Borel measure sees `∫C_∞ dν` | `PrimeExhaustion.tendsto_integral_movingCommutatorDensity_mul` |
| **(3g)** `M_{S,N}(z) = zG(z)N^z[E_S(1+z)H_N(1+z) − H^rough_{S,N}(1+z)]` | `integral_cexp_mul_movingCommutatorDensity`, `integral_cexp_mul_atom_sum` |
| prime supply `Σ_{x<p≤Cx} p^{−σ} → ∞`; phase windows | `tendsto_sum_primeWindow_rpow_neg`, `exists_phase_prime_set`, `normSq_one_sub_le_exp`, `one_add_le_normSq_one_sub` |
| **(3h)** exact form with `H^rough = 1`; schedules `S_N^±` with `M → 0` and `|M| → ∞` | `commutatorSpectralObservation_eq`, `roughHarmonicCutoff_eq_one`, `exists_prime_schedules_spectral_observation` |
| **(3i)** `Σ_{p≤N}p^{−s} = N^{1−s}/((1−s)log N) + o(N^{1−σ}/log N)`, `0 < σ < 1` | `tendsto_sum_primesLE_cpow_sub_main` (real-variable form `tendsto_primeCpowSumIoc_sub_main`; exact Abel remainder `primeCpowSumIoc_eq`, `primeCpowSumIoc_sub_main`) |
| **(3j)** `log|E_{S_N^nat}(s)| = −Re[N^{1−s}/((1−s)log N)] + o(N^{1−σ}/log N)`, `1/2 < σ < 1` | `tendsto_log_norm_naturalEuler_add_main` (summable Euler-log error `abs_sum_primesLE_eulerLogError_le`) |
| **(3j)** phase peaks: subsequences with `|E| → 0` and `→ ∞` faster than every power; `M → 0` on the first, `M = −G(s−1)E(1+o(1))` and `|M| → ∞` on the second | `natural_schedule_spectral_oscillation` (`frequently_half_le_cos_sub_mul_log`, `frequently_cos_sub_mul_log_le_neg_half`, `re_naturalMainTerm`, `tendsto_log_norm_naturalEuler_phase`) |
| **(3k)** `[M/((s−1)G N^{s−1}) + 1]/E = H_N(s)`; subtracting `N^{1−s}/(1−s)` gives `ζ(s)` | `natural_schedule_renormalization`, `natural_schedule_zeta_limit` |
| **(4)** `C_{S_N} → C_∞` along every exhaustion; `C_∞ = O(1)` at `−∞`, Gaussian at `+∞` | `PrimeExhaustion.tendstoUniformlyOn_commutatorBoundaryProfile`, `abs_cofinalBoundaryProfile_le`, `abs_cofinalBoundaryProfile_le_gaussian` |
| **(5)** `∫e^{zy}C_∞ = −G(z)/ζ(1+z)`, `Re z > 0` | `integral_cexp_mul_cofinalBoundaryProfile` |
| `C_∞` has both signs arbitrarily far into the negative cusp | `cofinalBoundaryProfile_takes_both_signs`, `cofinalBoundaryProfile_not_eventually_signed`, `not_eventually_nonneg_of_pole_of_countable` |

Proof-route notes:
- (3i) is proved by complex Abel summation (`sum_mul_eq_sub_sub_integral_mul`) against `θ(t) = t(1 + e(t))`, `e → 0` (corpus `tendsto_thetaError`). The main integral is integrated by parts once more; the doubly logarithmic integral and the `e`-weighted kernel are `o(x^{1−σ}/log x)` by the corpus lemmas `HTGeometry.tendsto_logSqRpowIntegral` and `HTGeometry.tendsto_logKernelRemainder`. The card's route through `π(x)` is replaced by the equivalent route through `θ(x)`.
- In (3j) the integer subsequences are `⌈exp u_k⌉` with `τu_k` on the phase peaks; `log⌈e^u⌉ − u ≤ e^{−u}` replaces "consecutive `log N` gaps tend to zero".
- Landau's theorem is proved for a countable closed singular set, as the zeta zeros require.
