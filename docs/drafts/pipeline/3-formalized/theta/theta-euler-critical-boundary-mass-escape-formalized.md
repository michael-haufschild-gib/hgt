# Euler completion creates a critical theta boundary charge absent at every finite prime stage — Lean certificate

- **Paper card:** `theta-euler-critical-boundary-mass-escape.md`
- **Lean modules:**
  - `GaloisForLFunctions.RHTower.ThetaCriticalBoundaryMellinCharge` covers:
    - the Gaussian-rate atom `φ_λ` and its Mellin character (1)–(3), the exact flux law (4) and the charge `−1` in the opposite weight;
    - termwise Laplace integration over arbitrary index sets `A ⊆ ℕ` with `Σ_{n∈A} n^{−(Re w+1/2)} < ∞`;
    - (5), non-convergence in `L¹(e^{x/2}dx)`, (7), the finite-prime Euler product, (8), (9) with divergence, and (9a).
  - `GaloisForLFunctions.RHTower.ThetaCriticalBoundaryFluxPotential` covers:
    - flux potentials `H_A` for every index set, with the termwise flux law `H_A' = −e^{x/2}S_A` and the right-tail formula `H_A(x) = ∫_x^∞ e^{t/2}S_A`;
    - the boundary values of `H_A`: `0/0` for `Σ_A 1/n < ∞`, and `1/2 / 0` for all integers;
    - `0 ≤ H_A ≤ H ≤ 1/2`, and pointwise convergence along exhaustions;
    - (6) and (6a) for every admissible exhaustion, specialised to the finite-prime stages;
    - the unboundedness of the strip tests `ψ_w`.
  - `GaloisForLFunctions.RHTower.ThetaIntegerCutoffMovingPacket` covers:
    - a first-order Riemann-sum estimate for Lipschitz profiles, and uniform convergence of dilated Riemann sums;
    - integer cutoffs `K_N` (critical moment zero, locally uniform convergence to `k`), the moving packet (10), (11), and `∫|B_N − B_∞| ≥ 1/2`;
    - the moving flux potential and its wall profile `0 → 1/2`.
  - `GaloisForLFunctions.RHTower.ThetaContinuousRateOrbitDensity` covers:
    - the rate-Laplace class, the orbit transforms `T_k` (holomorphic, `T_k' = −T_{k+2}`), and the pairing formula (13);
    - propagation by the identity theorem, and the homogeneity ODE `T_{5/2}(s) = c s^{−3/2}`;
    - the half-line pullback and Laplace uniqueness, giving the generalized-annihilator classification;
    - (12) in `L²(ℝ)`, and density of the parity projections in their parity sectors.
- **Umbrella:** `GaloisForLFunctions.RHTower`.
- **Verification:**
  - Targeted `lake build` of every module.
  - `lake env lean` audit clean (no errors, no warnings) on all four modules.
  - `#print axioms` = `propext`, `Classical.choice`, `Quot.sound` for all 202 declarations of the four modules.
  - No `sorry`.
  - The only hypotheses are the card's quantifiers: rates `λ > 0`, Mellin parameters in the stated half-planes, `R`, `N`, the exhaustion conditions `Σ_{n∈A_j} 1/n < ∞` and `1_{A_j}(n) → 1`, bounded differentiable tests with integrable derivative, a nonempty open set `J` of positive rates, and `ε = ±1`.

Dictionary:
- `φ_λ = rateAtom λ`, with `a_n = thetaCuspSourceTerm · n = φ_{πn²}`.
- `M_a(λ) = rateMellin a λ`.
- `k = thetaCuspFullSource`; `S_P = finitePrimeThetaCuspSource N` (prime factors `≤ N`); `S_A = indexThetaSource A`.
- `G(w) = thetaAtomMellinFactor w = (w − 1/2)·thetaAtomGammaFactorC w`.
- `K_N = integerCutoffThetaSource N`.
- `H_A = indexFluxPotential A`, with flux atoms `thetaFluxTerm x n = 2πn² e^{3x}e^{−πn²e^{2x}}`.
- `B_N = movingPacketDensity N`; `B_∞ = movingPacketLimit`; the moving wall is `movingFluxLimit`.
- `F(s) = rateOrbitTransform g (5/2) s`, with `F'(s) = −rateOrbitTransform g (9/2) s`.
- `q(u)e^{−u} = ratePullback g u`.

| Card item | Lean theorem |
|-|-|
| **(1)** `a_n = φ_{πn²}` | `thetaCuspSourceTerm_eq_rateAtom` |
| **(2)** `M_a(λ) = (a − 1/2)Γ(a/2+5/4)λ^{−a/2−1/4}`, absolutely convergent, complex `Re a > −5/2` | `integral_cexp_mul_rateAtom`, `integral_exp_mul_rateAtom` |
| **(3)** `M_{1/2} = 0`, `M_{−1/2} = −1` | `rateMellin_half`, `rateMellin_neg_half` |
| **(4)** `e^{x/2}φ_λ = −2λ (e^{3x}e^{−λe^{2x}})'`, primitive vanishing at both ends | `exp_half_mul_rateAtom`, `hasDerivAt_rateFlux`, `tendsto_rateFlux_atBot`, `tendsto_rateFlux_atTop` |
| opposite weight: charge `−1` per atom, not termwise summable | `integral_exp_neg_half_mul_thetaCuspSourceTerm`, `not_summable_integral_exp_neg_half_mul_thetaCuspSourceTerm` |
| `H_A`: termwise flux law for every `A` | `hasDerivAt_thetaFluxTerm`, `hasDerivAt_indexFluxPotential`, `indexFluxPotential_eq_setIntegral` |
| `H_A → 0` at `+∞` (every `A`) and at `−∞` (`Σ_A 1/n < ∞`, finite primes); all integers: `0` and `1/2` | `tendsto_indexFluxPotential_atTop`, `tendsto_indexFluxPotential_atBot_of_summable`, `tendsto_finitePrimeFluxPotential`, `tendsto_indexFluxPotential_univ_atBot` |
| summand `= n^{−1}·2π(ne^x)³e^{−π(ne^x)²}` | `thetaFluxTerm_eq_inv_mul` |
| **(5)** `∫e^{x/2}S_P = 0`, `∫e^{x/2}k = 1/2`, both absolute; weighted atom mass `C/n` | `integral_exp_half_mul_finitePrimeThetaCuspSource`, `integral_exp_half_mul_thetaCuspFullSource_eq_half` (corpus), `integral_exp_half_mul_abs_thetaCuspSourceTerm`, `integral_exp_half_mul_indexThetaSource` |
| index-set termwise integration | `hasSum_integral_cexp_mul_indexThetaSource`, `integral_cexp_mul_indexThetaSource`, `integral_exp_mul_indexThetaSource` |
| no convergence in `L¹(e^{x/2}dx)` | `not_tendsto_integral_exp_half_mul_abs_sub` |
| **(6)** `∫_{−∞}^{−R} e^{x/2}(k − S_P) → 1/2`; residual total `1/2`, right half-line residual `→ 0` | `tendsto_setIntegral_Iio_exp_half_mul_sub_finitePrimeThetaCuspSource`, `tendsto_setIntegral_Iio_exp_half_mul_sub_indexThetaSource`, `integral_exp_half_mul_sub_indexThetaSource`, `tendsto_setIntegral_Ioi_exp_half_mul_sub_indexThetaSource` |
| **(6a)** `∫ψe^{x/2}S_P → ∫ψe^{x/2}k − ψ(−∞)/2`, any admissible exhaustion `A_j` | `tendsto_integral_mul_exp_half_mul_finitePrimeThetaCuspSource`, `tendsto_integral_mul_exp_half_mul_indexThetaSource` |
| `0 ≤ H_P ≤ H ≤ 1/2`, `H_{A_j} → H` | `indexFluxPotential_nonneg`, `indexFluxPotential_le_univ`, `indexFluxPotential_univ_le_half`, `tendsto_indexFluxPotential_of_exhaustion` |
| **(7)** `∫e^{wx}k = G(w)ζ(w+1/2)` (all `Re w > 1/2`); finite stage `G(w)∏_{p≤N}(1 − p^{−w−1/2})^{−1}` (`Re w > −1/2`) | `integral_cexp_mul_thetaCuspFullSource_eq_zeta`, `integral_cexp_mul_finitePrimeThetaCuspSource` |
| **(8)** `lim_N ∫e^{x/2}S_N = 0`, `lim_{a↓1/2} lim_N ∫e^{ax}S_N = 1/2` | `iterated_limit_integral_exp_mul_finitePrimeThetaCuspSource`, `tendsto_integral_exp_mul_finitePrimeThetaCuspSource`, `tendsto_integral_exp_mul_thetaCuspFullSource_half` |
| **(9)** `d/da|_{1/2}∫e^{ax}S_N = (1/2)∏_{p≤N}(1 − 1/p)^{−1}`, unbounded | `hasDerivAt_integral_exp_mul_finitePrimeThetaCuspSource`, `tendsto_prod_one_sub_inv_primesBelow` |
| strip tests `ψ_w = e^{(w−1/2)x}` blow up at the cusp for `Re w < 1/2` | `tendsto_norm_cexp_sub_half_mul_atBot` |
| **(9a)** `∫e^{wx}K_N + Γ(w/2+5/4)π^{−w/2−1/4}N^{1/2−w} → (w − 1/2)G̃(w)ζ(w+1/2) = ∫e^{wx}k = XiC(iw)`, `0 < Re w < 1/2` | `tendsto_integral_cexp_mul_integerCutoffThetaSource_add`, `integral_cexp_mul_thetaCuspFullSource_eq_mul_zeta`, `XiC_I_mul_eq_thetaAtomMellinFactor_mul_zeta` |
| `K_N` has critical moment zero and `K_N → k` locally uniformly | `integral_exp_half_mul_integerCutoffThetaSource`, `tendstoUniformlyOn_integerCutoffThetaSource` |
| **(10)** `B_N(y) = (e^y/N)Σ h((n/N)e^y) → B_∞ = ∫_0^{e^y}h = −2πe^{3y}e^{−πe^{2y}} < 0`, uniformly on `y ≤ Y`; `h = −2π(t³e^{−πt²})'` | `movingPacketDensity_eq`, `tendstoUniformlyOn_movingPacketDensity`, `movingPacketLimit_eq_integral`, `movingPacketLimit_neg`, `hasDerivAt_thetaCuspSeed_primitive`, `tendstoUniformlyOn_dilatedRiemannSum`, `abs_riemannSum_sub_integral_le` |
| **(11)** `∫B_∞ = −1/2`; `∫B_N = 0`; global `L¹` convergence false | `integral_movingPacketLimit`, `integral_movingPacketDensity`, `half_le_integral_abs_movingPacketDensity_sub`, `not_tendsto_integral_abs_movingPacketDensity_sub` |
| moving flux potential `→ 2π∫_0^{e^y}t²e^{−πt²}`, rising from `0` to `1/2` | `tendstoUniformlyOn_integerCutoffFluxPotential_moving`, `movingFluxLimit_monotone`, `tendsto_movingFluxLimit_atBot`, `tendsto_movingFluxLimit_atTop` |
| **(12)** `closure span{φ_λ : λ ∈ J} = L²(ℝ)` | `topologicalClosure_span_rateAtomLp` (`memLp_rateAtom`, `rateAtomLp`) |
| **(13)** `⟨g, φ_λ⟩ = 2λ[−2λF'(λ) − 3F(λ)]` | `IsRateLaplaceClass.integral_conj_mul_rateAtom`, `IsRateLaplaceClass.hasDerivAt_rateOrbitTransform` |
| identity theorem, then `2sF' + 3F = 0`, then `F = c s^{−3/2}` | `IsRateLaplaceClass.three_mul_eq_of_annihilates`, `IsRateLaplaceClass.rateOrbitTransform_eq_of_annihilates` |
| Laplace uniqueness after exponential damping | `IsRateLaplaceClass.memLp_ratePullback`, `laplaceRay_ratePullback`, `laplaceRay_halfPowerDamped` |
| generalized annihilators are exactly `c e^{x/2}` (non-`L²`) | `IsRateLaplaceClass.annihilates_iff`, `IsRateLaplaceClass.exists_ae_eq_const_mul_exp_half`, `isRateLaplaceClass_exp_half`, `not_memLp_exp_half`, `isRateLaplaceClass_Lp` |
| even/odd projections of the continuous orbit are dense in their parity sectors | `topologicalClosure_span_parityProjection_rateAtomLp`, `mem_paritySector_parityReflectionLp`, `coeFn_parityProjection_rateAtomLp`, `topologicalClosure_span_parityProjection` |

Proof-route notes:
- (12) is derived from the generalized-annihilator classification.
  - An `L²` annihilator equals `c e^{x/2}` a.e., and `e^{x/2} ∉ L²` forces `c = 0`.
  - This replaces the card's Cauchy–Schwarz bound `|F(s)| ≤ C s^{−5/4}`.
  - The theorem proved is the card's statement.
- Laplace uniqueness is applied to `(q(u) − c′u^{1/2})e^{−u} ∈ L²(0,∞)`, the card's "fixed exponential damping".
- The generalized annihilator class is made precise as the rate-Laplace class: `∫|g|²e^{3x}e^{−2δe^{2x}} < ∞` for all `δ > 0`.
- (6) and (6a) are proved for every admissible exhaustion. The finite-prime statements are corollaries.
- (7) holds on the whole half-plane `Re w > 1/2`, which contains the stated range `1/2 < a < 1`.
