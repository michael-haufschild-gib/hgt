# Suzuki v2 unlabeled propositions — CLOSED (2026-08-21)

Paper: arXiv:2606.09096v2 (`screwzelf_9.tex`). Its **eleven labeled results were already
Lean-closed** (`mem:research/suzuki_v2_2606_09096_formal_parity`). This memory records the closure
of the *unlabeled displayed propositions*.

Card (stage 3): `docs/drafts/pipeline/3-formalized/suzuki-v2-unlabeled-propositions-formalization.md`.

## Already corpus-owned (do not rebuild)

- (2.2) origin expansion — `SuzukiOriginLogarithmicRemainder`; (2.4) `suzuki_equation_two_four`;
  (2.5) `suzuki_equation_two_five`; (2.6) `suzukiFinitePartEnergy_eq_logFourier_add_eulerMass`
- (2.9)–(2.11) — `SuzukiScrewDistributionalAtoms`, `SuzukiScrewOperatorEquationTwoFive`
- **`r₀''+r₁''` in closed form** — `suzukiWeilRemainderSecondDerivative`
  (`SuzukiWeilPositionTorqueCurvature`), bridged by `SuzukiOriginRemainderWeilBridge`.
  So the paper's Bernoulli-generating-function step never has to be redone.
- Plancherel autocorrelation transform — `fourier_autocorrelation`
  (`HTGeometry/SchwartzPolynomialDifferentialFrame`)
- archimedean Weil block — `integral_fourier_mul_logPi_sub_re_quarterDigamma_eq_weilDistribution`
- second-order digamma asymptotic — `norm_digamma_sub_log_add_half_inv_le_of_re_pos`
  (`HTGeometry/DigammaHalfPlaneAsymptotic`)
- Gauss digamma series — `digamma_eq_neg_euler_add_tsum_gauss`, `integral_gaussDigammaLaplaceTerm`
- `ein`/`frullaniHead`/`frullaniTail`/`frullani_eq_eulerMascheroni`; complex Frullani
  `integral_frullani`; product-majorant Fubini `integral_swap_of_dominated_prod`
- §8.1 `Q_{G̃}=Q_G` on `L²₀` — `suzukiScrewIntervalForm_eq_raw_of_zeroMean`
- §4 scaling — `suzukiWeilIntervalFormRayleigh_eq_scaledUnitPullback`; §5 Dirichlet-form layer —
  `SuzukiLimitingLogClosedMarkov`, `…IrreducibilityCore`, `…GroundSimplicity`

## Landed (10 modules, all axiom-clean, warning-free, wired)

1. `HTGeometry/TriangularIntervalFubini` — `∫_p^q F(x)(∫_x^q G) = ∫_p^q (∫_p^t F) G(t)`.
2. `RHTower/SuzukiInverseNeumannLaplacian` — §8.2 + (8.4).
3. `RHTower/SuzukiDeBrangesDeficiencyKernel` — §7 kernel algebra.
4. `RHTower/SuzukiApertureFourierDecay` — §3: `ê_n`, (3.3), (3.4).
5. `HTGeometry/ParityRayleighDecomposition` — (4.10) `λ = min(λ⁺,λ⁻)`.
6. `RHTower/SuzukiCutoffLogWindow` — the `I_ε ≪ ε log(1/ε) → 0` step.
7. `RHTower/EulerMascheroniGaussKernel` — `∫₀^∞(e^{-t}/t − e^{-t}/(1−e^{-t}))dt = −γ`.
8. `RHTower/DigammaIntegralRepresentation` — `ψ(s)=∫₀^∞(e^{-u}/u − e^{-su}/(1−e^{-u}))du`;
   `suzukiArchKernel`, `integral_suzukiArchKernel = −Re ψ(1/4+iz/2)`.
9. `RHTower/CosineIntegralAsymptotic` — improper `∫cos t/t`, its Abel limit,
   `∫₀^∞(e^{-t}−cos t)/t dt = 0`, and `∫_ε^∞ e^{-u}/u − ∫_{aε}^∞ cos u/u → log a`.
10. `RHTower/SuzukiRemainderFourierTransform` — **(2.7)–(2.8)**:
    `r'' = r₀'' + r₁''` with `r₁''(t)=e^{-|t|/2}/(1−e^{-2|t|})−1/(2|t|)`
    (`exp_div_two_sinh_eq` makes this algebraic);
    `suzukiR1Fourier_regularized`: `\hat{r₁''}(z) = −Reψ(1/4+iz/2) + log z − log 2` as an iterated
    limit (`R→∞` then `ε→0`) — the only sense it exists, `r₁''` decaying like `−1/(2|t|)`;
    `suzukiArchimedeanSymbol`/`suzukiR1Fourier_symbol`: `log z − log(2π) − \hat{r₁''} =
    Reψ(1/4+iz/2) − log π`, the passage (2.7)→(2.8);
    `abs_re_digamma_half_sub_log_le`: `Re ψ(s/2) = log|s| − log2 + O(|s|^{-2})` with constant
    `(20+Re s)/|s|²`;
    `tendsto_setIntegral_Ioi_nhdsWithin_zero` (reusable).

## Two source-independent findings

- §7's last display carries `π²`; computed from the paper's own definitions of `K` and `f̂` the
  constant is `π`. Structure and the `θ=π` collapse agree.
- The §7 boundary form needs **no** nonvanishing hypothesis: at `z = ∓i` the numerator vanishes.

## Traps hit

- Narrow imports hide `integral_pow`, `integral_id`, `intervalIntegrable_id`,
  `ContinuousLinearMap.hasDerivAt`, `HasDerivAt.cexp`,
  `intervalIntegral.integral_mul_deriv_eq_deriv_mul`, `integral_Ioi_of_hasDerivAt_of_tendsto`,
  `integrableOn_Ioi_deriv_of_nonneg` — the error is "unknown identifier", not a rename.
- `HasDerivAt (fun t : ℝ => (t:ℂ)) 1 x` is `Complex.ofRealCLM.hasDerivAt.congr_deriv (by simp)`.
- `HasDerivAt.neg/.sub/.mul` return Pi forms — use `congr_deriv (by ring)`, and `dsimp only`
  before `intervalIntegral.integral_congr` goals.
- `exp_neg_integrableOn_Ioi` yields `rexp (-ε * x)`, not `rexp (-(ε*x))`; bridge with `simpa [neg_mul]`.
- `integral_re`/`integral_ofReal` are `RCLike`-stated; for `ℂ` use `Complex.reCLM.integral_comp_comm`
  + `Complex.reCLM_apply`, and `integral_complex_ofReal`.
- The repo root holds a stray `GaloisForLFunctions/` tree; always use absolute paths.
