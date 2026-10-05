# Prime-only physical transition of the Möbius–theta causal tail — Lean certificate

- **Paper card:** `causal-mobius-theta-primorial-transition.md`
- **Lean modules (umbrella `GaloisForLFunctions.RHTower`):**
  - corpus, already present: the causal boundary criterion chain (`CausalMobiusThetaTail`, `CausalMobiusThetaPhysicalSource`, `CausalMobiusThetaPhysicalWavelet`, `EulerDeletionPeriodicProjection`, `CausalMobiusThetaSmoothGauge`, `CausalMobiusThetaTransitionClock`), `ThetaCuspReflection` (`k(−x) = k(x)`), `ThetaCuspFinitePrimeSource` (seed and source), the Euler-deletion physical-source modules, `ThetaCutoffCommutatorShell` (`sum_Icc_filter_dvd_eq`), Mathlib `primorial`, `primorial_le_four_pow`, `squarefree_primorial`, Bertrand;
  - new: `CausalMobiusThetaPrimorialInnovation` ((1)–(4), primorial growth, clocks `l₋`, `l₊`, (7), RH equivalence), `CausalMobiusThetaUniformCycle` (uniform averaging, (8)–(13), the smooth/rough prime current), `CausalMobiusThetaLargestPrime` ((14)–(17), reflection duality, superpolynomial suppression, whole-chain check, RH equivalences, unbounded uniform norm of `Q_N`).
- **Verification (2026-10-05):** targeted `lake build --old` of each new module; final `lake env lean` audit of each source with empty output; a `Lean.collectAxioms` sweep over all 299 constants of the three new modules finds only `propext`, `Classical.choice`, `Quot.sound`; no `sorry`, no axiom, no heartbeat options.
- **Hypotheses:** only the card's quantifiers. Stronger forms: (11) is proved for every `g, d ∣ M` with `h = gcd(g, d)` in place of `g`; (16) holds for every real `A` with a constant uniform in all `N ≥ 1`; the `O_δ(1)` in (7) is a single constant for all `N ≥ 1`.

Dictionary: `H = Lp ℝ 2 cellMeasure` (cell `j` is `r = j+1`), `f_d = residueVec d` (physical) / `fracAtom d` (cycle), `C_N = sourceVec μ N` / `moebiusCell N`, `R_l = primorial l`, `F_l = primorialSpace l = periodicSpace (primorial l)`, `Π_l = (primorialSpace l).starProjection`, `I_N^sf = primorialInnovation N`, `P_N^sf = primorialDrift N`, `f_d − Π_{d−1}f_d = primorialIncrement d`, `q_N^flat = flatWaveletVec N`, `l₊ = primorialUpper δ N`, `l₋ = primorialLower δ N`, `B(N) = causalMobiusThetaTail N`, `e_N = thetaCellDefect N`, `V_g = cycleAverage M g`, `U_p − U_{p−1} = cycleLayer M p`, `a_N = thetaIncrement N`, `Q_N = periodizedObserver M N`, `⟨·,·⟩_M = cyclePairing M`, `ψ_p = centeredSawtooth p`, `H_p = roughMoebiusSum p`, `A_N(a,p) = sawtoothObservation N a p`, `G = thetaLatticeSum`, `k = thetaCuspFullSource`, `S_{p,X} = wheelCount p X`, `M_{p,X} = wheelMoebiusSum p X`, `P = lowPrimeThreshold N`.

| Card item | Lean theorem |
|-|-|
| **(1)** `C_N = I_N^sf + P_N^sf` | `sourceVec_eq_primorialInnovation_add_drift`, `primorialInnovation`, `primorialDrift`, `primorialIncrement` |
| `d ∣ R_{d−1}` for composite squarefree `d`; **(2)** only primes innovate | `squarefree_dvd_primorial`, `primorialIncrement_eq_zero_of_not_prime`, `primorialInnovation_eq_sum_primes` |
| increments in `F_p`, orthogonal to `F_{p−1}`, mutually orthogonal | `primorialIncrement_mem`, `primorialIncrement_orthogonal`, `inner_primorialIncrement_eq_zero`, `norm_sq_sum_primorialIncrement` |
| least-squares predictor: `‖f_p − Π_{p−1}f_p‖² ≤ 1/(R_{p−1}+1)` | `norm_sq_primorialIncrement_le` (`predictorVec_mem_periodicSpace`) |
| **(3)** `‖I_N^sf‖² = Σ_p‖…‖² < 2`; geometric bound `R_{p_k−1} ≥ 2^{k−1}` | `norm_sq_primorialInnovation_le`, `sum_prime_inv_primorial_le`, `prime_term_le_telescoping`, `two_mul_primorial_le_of_prime` |
| **(4)** `‖P_N^sf‖ ≤ N + √2`, `|P_N^sf(r)| ≤ 2N`, `P_N^sf ∈ F_N`; innovations in `[−1, 1]` | `norm_primorialDrift_le`, `abs_primorialDrift_apply_le`, `primorialDrift_mem`, `abs_primorialIncrement_apply_le` |
| `R_N` grows faster than every power (Bertrand); `l₋`, `l₊` exist | `two_pow_le_primorial_two_pow`, `eventually_rpow_le_primorial`, `exists_primorial_ge`, `primorialUpper`, `primorialLower`, `primorial_primorialUpper_ge`, `primorial_primorialLower_le`, `le_primorialLower`, `primorialLower_le_upper` |
| **(7)** `B(N) = ⟨(Π_{l₊} − Π_{l₋})P_N^sf, q_N^flat⟩ + O_δ(1) = Σ_{l₋<p≤l₊} ⟨(Π_p − Π_{p−1})P_N^sf, q_N^flat⟩ + O_δ(1)` | `exists_abs_causalMobiusThetaTail_sub_primorialTransition_le`, `primorialTransitionCovariance`, `primorialTransitionLayers`, `inner_primorialProjection_diff_eq`, `abs_inner_primorialDrift_le` |
| RH ⟺ subpower growth of the prime-only covariance | `riemannHypothesis_iff_primorialTransition_subpower` |
| every nonzero atom is `M`-periodic, `U_N C_N = C_N`; `U_l f_d` depends only on `r mod gcd(d, R_l)` | `moebius_ne_zero_dvd_primorial`, `moebiusCell_add_primorial`, `cycleAverage_primorial_moebiusCell`, `cycleAverage_fracAtom` |
| **(8)** `(U_p − U_{p−1})f_d = 0` for `p ∤ d` | `cycleLayer_fracAtom_eq_zero` |
| `a_N(0) = −g(1/N)/√N`, `Σ_{r≥0} a_N(r) = 0`, extension leaves the pairing unchanged | `thetaIncrement_zero`, `hasSum_thetaIncrement`, `thetaIncrement_succ` |
| **(9)** `⟨C_N,q_N⟩_H = ⟨C_N,Q_N⟩_M` | `causalMobiusThetaTail_natCast_eq_cyclePairing`, `tsum_mul_thetaIncrement_eq_cyclePairing` |
| constant layer pairs to zero; telescoping over primes | `cyclePairing_const_periodizedObserver`, `cyclePairing_eq_sum_primeLayers` |
| **(10)** prime–cofactor decomposition, no nonincident layers | `causalMobiusThetaTail_natCast_eq_primeCofactor`, `cycleLayer_moebiusCell_eq` |
| no free Hilbert bound: `‖Q_N‖_M → ∞` | `tendsto_cyclePairing_periodizedObserver_self` |
| **(11)** `V_g f_d(r) = [(r mod g) + (d−g)/2]/d` (`g ∣ d`) | `cycleAverage_fracAtom_of_dvd` |
| **(12)** `(U_p − U_{p−1})f_{pab}(r) = ψ_p(⌊r/a⌋)/b` | `cycleLayer_fracAtom_smooth_rough`, `gcd_primorial_smooth_rough`, `gcd_primorial_pred_smooth_rough` |
| **(13)** `(U_p − U_{p−1})C_N(r) = −Σ_{a ∣ R_{p−1}, pa ≤ N} μ(a)H_p(N/(pa))ψ_p(⌊r/a⌋)`; `|H_p(X)| ≤ 1 + log X` | `cycleLayer_moebiusCell_eq_smooth_rough`, `moebius_smooth_rough`, `abs_roughMoebiusSum_le` |
| (13) in (9)–(10): `B(N) = −Σ_pΣ_a μ(a)H_p(N/(pa))A_N(a,p) + e_N`, `e_N = O(N^{−5/2})` | `causalMobiusThetaTail_natCast_eq_smoothRough`, `cyclePairing_cycleLayer_moebiusCell_eq`, `cyclePairing_centeredSawtooth_eq`, `exists_abs_thetaCellDefect_le` |
| **(14)** `A_N(a,p) = N^{−1/2}[(1/p)Σ_j g(ja/N) − Σ_k g(kpa/N)]` | `sawtoothObservation_eq_lattice`, `centeredSawtooth_succ_sub`, `centeredSawtooth_div_succ_sub` |
| reflection `G(1/x) = xG(x)`; **(15)** `A_N = √N/(pa)[G(N/a) − G(N/(pa))]` | `thetaLatticeSum_inv`, `thetaCuspFullSource_log_eq_lattice`, `sawtoothObservation_eq_dual` |
| `|G(x)| ≤ Ce^{−cx²}` (`x ≥ 1`); **(15a)** `|A_N(a,p)| ≤ CN^{−1/2}e^{−cx²}` | `exists_abs_thetaLatticeSum_le`, `exists_abs_thetaCuspSeed_le_gauss`, `exists_abs_sawtoothObservation_le` |
| `b > 1` forces `x > p`; `x ≥ log N/(4 log 2)` from `R_p ≤ 4^p`; at most `N²` pairs; superpolynomial smallness | `roughMoebiusSum_eq_one_of_le`, `log_div_le_of_primorial`, `abs_sum_primes_divisors_le`, `exists_pow_mul_exp_neg_sq_le` |
| **(16)** largest-prime normal form, every `A` | `exists_abs_causalMobiusThetaTail_sub_largestPrimeCurrent_le`, `largestPrimeCurrent` |
| restriction to `p > P = log N/(4 log log N)` | `exists_abs_lowPrimeCurrent_le`, `four_pow_le_sqrt_of_le_lowPrimeThreshold`, `exists_abs_causalMobiusThetaTail_sub_highPrimeCurrent_le` |
| whole-chain check: current = finite Möbius–theta head over `2 ≤ d ≤ N` up to `O_A(N^{−A})`; `μ(pa) = −μ(a)`, unique largest prime | `exists_abs_largestPrimeCurrent_sub_mobiusThetaHead_le`, `mobiusThetaHead`, `sum_primes_divisors_moebius_eq`, `sqrt_div_mul_thetaLatticeSum_eq` |
| **(17)** sieve dilation defect identity | `sum_moebius_centeredSawtooth_eq_dilationDefect`, `wheelCount`, `wheelMoebiusSum`, `centeredSawtooth_eq` |
| the constant term has zero theta observation; current = wavelet observation of the cross-prime defect | `tsum_thetaIncrement_mul_const`, `largestPrimeCurrent_eq_dilationDefect`, `dilationDefect` |
| RH ⟺ subpower growth of the largest-prime current, of the dilation-defect observation, of the head | `riemannHypothesis_iff_largestPrimeCurrent_subpower`, `riemannHypothesis_iff_dilationDefect_subpower`, `riemannHypothesis_iff_mobiusThetaHead_subpower` |

No signed subpower estimate for the largest-prime current is claimed by the card, and none is formalized.
