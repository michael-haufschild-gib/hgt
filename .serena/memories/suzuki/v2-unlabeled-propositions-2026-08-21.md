# Suzuki v2 unlabeled propositions (2026-08-21)

Paper: arXiv:2606.09096v2 (`screwzelf_9.tex`). Its **eleven labeled results are already Lean-closed**
(see `mem:research/suzuki_v2_2606_09096_formal_parity`). This memory covers the *unlabeled displayed
propositions*.

Card: `docs/drafts/pipeline/1-in-progress/suzuki-v2-unlabeled-propositions-formalization.md`.

## Already corpus-owned (do not rebuild)

- (2.2) origin expansion — `SuzukiOriginLogarithmicRemainder`, `suzukiApertureScrewExpansion`
- (2.4) — `suzuki_equation_two_four`; (2.5) — `suzuki_equation_two_five`
- (2.6) — `suzukiFinitePartEnergy_eq_logFourier_add_eulerMass` (`SuzukiFinitePartLogFourier`)
- (2.9)–(2.11) — `SuzukiScrewDistributionalAtoms`, `SuzukiScrewOperatorEquationTwoFive`
- §8.1 `Q_{G̃}=Q_G` on `L²₀` — `suzukiScrewIntervalForm_eq_raw_of_zeroMean`
- archimedean Fourier block — `integral_fourier_mul_logPi_sub_re_quarterDigamma_eq_weilDistribution`
- Gauss digamma series — `digamma_eq_neg_euler_add_tsum_gauss`, `integral_gaussDigammaLaplaceTerm`
  (`HTGeometry/DigammaGaussSeries`)
- `ein`/`frullaniHead`/`frullaniTail`/`frullani_eq_eulerMascheroni`
  (`RHTower/EulerMascheroniExponentialIntegral`)
- complex Frullani `integral_frullani` (`HTGeometry/FrullaniIntegral`)
- product-majorant Fubini `integral_swap_of_dominated_prod` (`HTGeometry/BlockWindowFubini`)

## Landed here (9 new modules, all axiom-clean, warning-free, wired)

1. `HTGeometry/TriangularIntervalFubini` — reusable
   `∫_p^q F(x)(∫_x^q G) = ∫_p^q (∫_p^t F) G(t)`, integrability only.
2. `RHTower/SuzukiInverseNeumannLaplacian` — **§8.2 + (8.4)**. `N(x,y)=(x²+y²)/(4a)−|x−y|/2+a/6`
   and `a − max x y` differ by the separable `φ(x)+φ(y)`, hence agree on mean-zero data.
   `suzuki_equation_802`, positivity, `∫N(x,y)dy=0`, range in `L²₀`, `(K_au)'=−v`, `(K_au)''=−u`,
   Neumann boundary limits, `D:H_0^1→L²₀` bijective, `suzuki_equation_804`.
3. `RHTower/SuzukiDeBrangesDeficiencyKernel` — **§7**. `E(∓i)`,`E♯(∓i)` from `ξ(3/2),ξ'(3/2)`;
   `K(∓i,∓i)=ξ(3/2)ξ'(3/2)/π`; the boundary form with `C_θ` (**valid for every z** — the numerator
   vanishes at the singular point); `θ=π` collapse; the `f̂_w=K(w̄,·)/E` relation.
   Correction: the source's last display has `π²`; direct computation gives `π`.
4. `RHTower/SuzukiApertureFourierDecay` — **§3**: `ê_n`, (3.3), (3.4).
5. `HTGeometry/ParityRayleighDecomposition` — **(4.10)** `λ = min(λ⁺,λ⁻)` as `IsGLB`, for any
   inner-product-symmetric linear involution.
6. `RHTower/SuzukiCutoffLogWindow` — the `I_ε ≪ ε log(1/ε) → 0` step:
   `∫_R^∞ log(3+z)/z² ≤ (log(3+R)+1)/R`, `∫_{-R}^R log(3+|z|) ≤ 2R log(3+R)`, and the assembled
   `∫_ℝ log(3+|z|)|ŵ|² ≤ 8ε log(3+1/ε) + 2M²(ε log(3+1/ε)+ε) → 0`.
7. `RHTower/EulerMascheroniGaussKernel` — `∫_ε^∞ e^{-t}/(1−e^{-t}) = −log(1−e^{-ε})`,
   `∫_ε^∞ e^{-t}/t = −log ε + Ein(ε) − γ`, and **`∫_0^∞(e^{-t}/t − e^{-t}/(1−e^{-t}))dt = −γ`**.
8. `RHTower/DigammaIntegralRepresentation` — **`ψ(s)=∫_0^∞(e^{-u}/u − e^{-su}/(1−e^{-u}))du`**
   (Re s>0), by geometric summation of the corpus's Laplace terms plus dominated convergence;
   plus `integral_archimedean_gaussKernel`:
   `∫_0^∞(e^{-u/4}cos(zu/2)/(1−e^{-u}) − e^{-u}/u)du = −Re ψ(1/4+iz/2)`.
9. `RHTower/CosineIntegralAsymptotic` — the conditionally convergent half.
   IBP against `t⁻¹` makes `∫_1^y cos t/t` converge; the damped version has the Abel limit
   `∫_1^∞ e^{-εt}cos t/t → cosTailValue` (the error carries `ε∫_1^∞ e^{-εt}/t ≤ ε(log(1/ε)+1)`);
   the real part of `integral_frullani` at rates `1, ε−i` is `log√(ε²+1)`, giving
   `gaussCosineIdentity` (the improper `∫_0^∞(e^{-t}−cos t)/t dt = 0`) and finally
   **`∫_ε^∞ e^{-u}/u du − ∫_{aε}^∞ cos u/u du → log a`**.

## Still open

The *assembly* of (2.7)–(2.8): both analytic halves are closed; what remains is identifying the
source's `r_1''` from the Bernoulli generating function plus the regularized Fourier bookkeeping.
`r_1''` is not `L¹`, so `\hat{r_1''}` is itself a regularized object — the corpus's own route to
(2.6) uses Abel limits for that reason.

## Traps hit

- Narrow imports silently hide `integral_pow`, `integral_id`, `intervalIntegrable_id`,
  `ContinuousLinearMap.hasDerivAt`, `HasDerivAt.cexp`,
  `intervalIntegral.integral_mul_deriv_eq_deriv_mul`, `integral_Ioi_of_hasDerivAt_of_tendsto`,
  `integrableOn_Ioi_deriv_of_nonneg`. The error is "unknown identifier", not a rename.
- `HasDerivAt (fun t : ℝ => (t:ℂ)) 1 x` is `Complex.ofRealCLM.hasDerivAt.congr_deriv (by simp)`;
  going through `hasFDerivAt` hits an `instInnerProductSpaceRealComplex` module-instance mismatch.
- `HasDerivAt.neg`/`.sub`/`.mul` frequently return Pi forms — use `congr_deriv (by ring)` rather
  than `simpa`, and `dsimp only` before `intervalIntegral.integral_congr` goals.
- `exp_neg_integrableOn_Ioi` yields `rexp (-ε * x)`, not `rexp (-(ε * x))`; bridge with
  `simpa [neg_mul]`.
- `integral_re`/`integral_ofReal` are stated for `RCLike.re`/`RCLike.ofReal`; for `ℂ` use
  `Complex.reCLM.integral_comp_comm` + `Complex.reCLM_apply`, and `integral_complex_ofReal`.
- The repo root contains a stray `GaloisForLFunctions/` tree; always use absolute paths.
