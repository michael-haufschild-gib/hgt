# Constrained Weil form: Bombieri–Yoshida receiver, the prime-2 entry, and a large-values engine

**Stage:** 1 (in progress), opened 2026-09-04.  Working log: `weil-polar-ground-energy-working-log.md`.
Three deliverables requested together:

* **(BY)** Lean: `ccmRestrictedWeilPolarGroundEnergy a > 0` (or `≥ 0`) for all apertures `a` ⇒ `RiemannHypothesis`
  (Bombieri–Yoshida / pole-vanishing Weil criterion).  Corpus has the unconstrained version
  (`exists_ccmRestrictedWeilGroundEnergy_neg_of_not_riemannHypothesis`) via Suzuki's smooth-test
  criterion; the two-bump witness is not pole-vanishing.
* **(P2)** Paper + Lean: analytic (non-numerical) positivity of the pole-vanishing form across the prime-2 entry
  `a = (log 2)/2`, replacing Connes–Consani's computer-checked step; explicit aperture range.
* **(GM)** Lean: a Guth–Maynard-type large-values theorem for Dirichlet polynomials.

## (BY) route — discrete multiplier + weighted Widder–Landau

Corpus facts used (all Lean, unconditional):
`suzukiScrewSmoothForm_eq_tsum`: for a smooth zero-mean test `φ` on `[-a,a]`,
`Q(φ) = Σ'_q B̄_q(φ) B_q(φ) / γ_q²`, `B_q(φ) = ∫ (e^{-iγ_q u} − 1) φ(u) du` (ray energy, `XiZeroCopy` = zeros with
multiplicity, `γ_q = xiSpectralPoint q`, `|Im γ_q| < 1/2`).  `IsPolarConstrained a u` ⇔
`⟨e^{±x/2}·1_{[-a,a]}, u⟩ = 0`.  CCM restricted quadratic = Suzuki form on zero-mean smooth tests
(`suzukiWeilIntervalForm_eq_ccmRestrictedWeilForm`, `ccmRestrictedWeilForm_primitive_eq_screw`).
Two-bump limit `Q(b_t − b_0) → 2Ψ(t)` (`suzukiScrewSmoothForm_twoBump`, `abs_suzukiLocalizedKernelAverage_sub_le`).
`Ψ(t) = Σ_q (1 − e^{iγ_q t})/γ_q²` (`ofReal_suzukiPsi_eq_xiScrewDivisor`), Widder–Landau engine
(`SuzukiScrewPointwiseNonnegativityCriterion`: `riemannHypothesis_of_suzukiPsiPointwiseNonnegative`).

1. **Discrete multiplier.** For `h > 0` let `M(γ) = (e^{iγh} − 1)(e^{iγh} − e^{h/2})(e^{iγh} − e^{-h/2}) = Σ_k μ_k e^{iγτ_k}`
   (`τ_k ∈ {0,h,2h,3h}`).  For any smooth `φ` put `(M∗φ)(x) = Σ_k μ_k φ(x − τ_k)`.  Then
   `∫ e^{sx}(M∗φ) = M(-is)·∫e^{sx}φ`, so `M∗φ` has zero mean and vanishing `e^{±x/2}` moments for **every** `φ`:
   `M∗φ` is pole-vanishing and zero-mean, support grows by `3h`.
2. **Twisted ray energy.** `B_q(M∗φ) = M(γ_q) B_q(φ)`, hence `Q(M∗φ) = Σ_q W_q |B_q(φ)|²/γ_q²`-type with
   `W_q = M(γ_q)·conj(M(conj γ_q))`; `W_q = |M(γ_q)|² ≥ 0` on the line, `W_q ≠ 0` at every off-line zero
   (`M` vanishes only on `Im γ ∈ {0, ±1/2}`).
3. **Twisted two-bump limit.** With `φ = b_t − b_0` (bumps of width `ε → 0`):
   `Q(M∗(b_t − b_0)) → 2 Φ(t)`, `Φ(t) := Re Ψ_M(t) − Ψ_M(0)`, `Ψ_M(t) = Σ_{k,l} μ_k μ̄_l Ψ(t + τ_k − τ_l)`.
   Zero series: `Φ(t) = Σ_q Re[W_q (1 − e^{iγ_q t})/γ_q²]`.  Constrained positivity at all apertures ⇒ `Φ ≥ 0` on `ℝ`.
4. **Weighted Widder–Landau.** `Φ ≥ 0`, continuous, `|Φ| ≤ C e^{y* t}`; Laplace transform
   `F(s) = Σ_q W_q(−i)/(γ_q s (s − iγ_q))` (single-pole rational atoms, poles at `s = iγ_q`, real parts `−Im γ_q`).
   Landau: the abscissa `σ_c` is a real singularity ⇒ a pole on the real axis ⇒ a zero with `Re γ_q = 0`
   (real zero of `ξ` in the strip) — excluded; hence `σ_c = −∞`?? no: hence every pole has `Re ≤ σ_c` and the
   abscissa is not a singularity unless real pole ⇒ contradiction unless there is no pole with `Re > σ_c`…
   Precisely: if an off-line zero exists, the conjugate pair gives poles with real parts `±y`, `y > 0`, `W ≠ 0`,
   so `σ_c ≥ y > 0` and Landau forces a real pole at `σ_c`, impossible.  So the engine's inputs are:
   (a) Landau's theorem for nonnegative functions (corpus: the halving argument of the pointwise module, to be
   generalized to weighted single-pole atoms), (b) no real zeros of `ξ` in the strip (corpus check needed),
   (c) `W_q ≠ 0` off the line.
5. **Assembly.** `∀a, μ₀^{pol}(a) ≥ 0` ⇒ `Q(M∗(b_t−b_0)) ≥ 0` for all small `ε` (the test is polar-constrained and
   its CCM embedding has nonnegative Rayleigh quotient) ⇒ `Φ ≥ 0` ⇒ RH.  Note only `≥ 0` is needed.

Open Lean work: translate-combination tests as `SuzukiSmoothZeroMeanTest`; `IsPolarConstrained` of their CCM
embedding; ray-coefficient translation rule; multi-bump localized limit; weighted Landau engine.

## (P2) route — see working log; needs Connes–Consani Thm 1 / (115) exactly.
## (GM) route — programme card `guth-maynard-large-values-lean-programme.md` (to be written after the exact statement is fetched).
