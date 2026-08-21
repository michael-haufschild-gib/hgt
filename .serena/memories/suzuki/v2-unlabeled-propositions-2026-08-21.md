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
- archimedean Fourier block `Re ψ(1/4+iz/2) − log π` —
  `integral_fourier_mul_logPi_sub_re_quarterDigamma_eq_weilDistribution` (`CCMArchimedeanPhaseWeilBridge`)
- §4/§5 consequences (Thms 1.3, 1.4) — `SuzukiGroundEnergyContinuity`,
  `SuzukiSmallApertureTheoremOneFour`, `SuzukiLimitingLogClosedMarkov/IrreducibilityCore/GroundSimplicity`

## Landed here (4 new modules, all axiom-clean, all wired)

1. `HTGeometry/TriangularIntervalFubini.lean` — **reusable**:
   `intervalIntegral_triangle_swap : ∫_p^q F(x)(∫_x^q G) = ∫_p^q (∫_p^t F) G(t)`,
   only interval integrability. Built on `integral_swap_of_dominated_prod` (`BlockWindowFubini`).
2. `RHTower/SuzukiInverseNeumannLaplacian.lean` — **§8.2 + §8.5**.
   Kernels `a − max x y` and `N(x,y)=(x²+y²)/(4a) − |x−y|/2 + a/6`; they differ by the *separable*
   `φ(x)+φ(y)`, `φ(t)=t²/(4a)+t/2−5a/12`, hence agree on mean-zero data.
   `suzuki_equation_802` (‖v‖² = ⟨N u,u⟩), positivity, `∫N(x,y)dy=0`, range in `L²₀`,
   `(K_a u)' = −v`, `(K_a u)'' = −u`, Neumann boundary limits, `D:H_0^1→L²₀` bijective,
   `suzuki_equation_804`.
3. `RHTower/SuzukiDeBrangesDeficiencyKernel.lean` — **§7 kernel algebra**.
   `E(∓i)`, `E♯(∓i)` in terms of `ξ(3/2), ξ'(3/2)`; `K(∓i,∓i)=ξ(3/2)ξ'(3/2)/π`;
   the boundary form with `C_θ = ξ(3/2)cos(θ/2)+iξ'(3/2)sin(θ/2)` (**valid for every z**, no
   nonvanishing hypothesis: the numerator vanishes at the singular point); `θ=π` collapse to
   `(2i/π)ξ'(3/2)ΞC(z)`; and the `f̂_w = K(w̄,·)/E` relation.
   Correction: the source's last display has `π²`; direct computation from the definitions gives `π`.
4. `RHTower/SuzukiApertureFourierDecay.lean` — **§3 displayed estimates**:
   `∫_{-a}^a e^{iξx} = 2sin(ξa)/ξ`, `ê_n(z) = 2sin(az+nπ)/(z+nπ/a)`, (3.3) `|ŵ|≤∫|w|`,
   (3.4) `|ŵ(z)| ≤ (|w(a)|+|w(−a)|+‖w'‖_{L¹})/|z|`.

## Still open

- (2.7)–(2.8): needs `\hat{r_1''}(z) = −Re ψ(1/4+iz/2) + log|z| − log 2`, i.e. the digamma integral
  representation `ψ(s)=∫_0^∞(e^{-u}/u − e^{-su}/(1−e^{-u}))du`. Corpus owns `gauss_digamma`
  (`HTGeometry/DigammaAsymptotic`) and `HTGeometry/FrullaniIntegral` — bounded project, not a gap.
- (4.10) `λ_a = min(λ_a^+, λ_a^-)` parity decomposition of the ground energy.
- The cut-off convergence `I_ε ≪ ε log(1/ε) → 0` (Theorem 1.1's density step; the theorem itself is
  already owned).

## Traps hit

- Narrow imports silently hide `integral_pow`, `integral_id`, `ContinuousLinearMap.hasDerivAt`,
  `HasDerivAt.cexp`, `intervalIntegral.integral_mul_deriv_eq_deriv_mul` — the error is
  "unknown identifier", not a name change. Add `Mathlib.Analysis.SpecialFunctions.Integrals.Basic`,
  `Mathlib.Analysis.Calculus.Deriv.Linear`, `Mathlib.Analysis.SpecialFunctions.ExpDeriv`,
  `Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts`.
- `HasDerivAt (fun t : ℝ => (t:ℂ)) 1 x` is `Complex.ofRealCLM.hasDerivAt.congr_deriv (by simp)`;
  going through `hasFDerivAt` hits an `instInnerProductSpaceRealComplex` vs
  `NormedSpace.complexToReal` module-instance mismatch.
- The repo root contains a stray `GaloisForLFunctions/` directory (other agents' junk). Always use
  absolute paths for `cat >>` — a failed `cd` silently writes there.
