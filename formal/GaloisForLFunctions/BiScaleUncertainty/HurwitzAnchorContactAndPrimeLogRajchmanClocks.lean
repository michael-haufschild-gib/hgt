import GaloisForLFunctions.BiScaleUncertainty.TypeIPrimeAmplifierWattMomentAndHeathBrownSparseMeanValue
import GaloisForLFunctions.Hurwitz.AnchorLevelGraph
import GaloisForLFunctions.Hurwitz.AnchorGraphContact
import GaloisForLFunctions.Hurwitz.AllNHZeta
import GaloisForLFunctions.HTGeometry.CaiChenFangGuoRajchman
import GaloisForLFunctions.HTGeometry.MellinPlancherelBound
import GaloisForLFunctions.HTGeometry.RiemannGaussian.MontgomeryVaughan.EigenIdentity
import GaloisForLFunctions.U0.U0Capstone

/-!
# Hurwitz Anchor Zero-Order Contact, Prime-Log Rajchman Clocks, and Montgomery–Vaughan Eigen-Identity

This module connects `BiScaleUncertainty` across the Lean corpus to `Hurwitz`, `HTGeometry`, and
`U0`:

1. **Hurwitz Canonical Anchor Level Graph, Exact Zeta Zero Contact Order, and All-$N$ Quadratic
   Independence (`hurwitz_anchor_level_graph_contact_and_allN_independence`):**
   - Connects `HurwitzZetaContinuation.fderiv_continuedHzeta_joint_comp_inr`,
     `HurwitzZetaContinuation.exists_analytic_anchor_level_graph`, and
     `HurwitzZetaContinuation.analyticOrderAt_anchor_zero_graph_contact`
     (`Hurwitz/AnchorLevelGraph.lean:18, 57`, `Hurwitz/AnchorGraphContact.lean:42`):
     at every anchor $(s, 1)$ with $\operatorname{Re} s > 0$ and $s \neq 1$, the shift partial
     derivative of `continuedHzeta` is $-s \zeta(s+1) \neq 0$, yielding a holomorphic local level
     graph $a = A(s)$ through $(s, 1)$; along any local zero graph $\zeta(s, A(s)) = 0$ through
     $(\rho, 1)$, the displacement $1 - A(s)$ has the exact analytic zero order of $\zeta(s)$ at $\rho$:
     $$\operatorname{analyticOrderAt}(1 - A, \rho) = \operatorname{analyticOrderAt}(\zeta, \rho).$$
   - Connects `HurwitzAllNHZeta.hurwitz_allN_hzeta_upper_half_plane` (`Hurwitz/AllNHZeta.lean:43`):
     for $\operatorname{Re} s > 1$, $s \notin \mathbb{Z}$, and any $N \in \mathbb{N}$, no non-trivial
     polynomial-coefficient quadratic relation among $\zeta(s, a), \dots, \zeta(s+N, a)$ can hold
     on the upper half-plane $\operatorname{Im} a > 0$.

2. **Infinite-Torus Ray-Rajchman Suppression of Prime-Logarithm Characters Across Corpus Clocks
   (`primeLog_infiniteTorus_rayRajchman_clock_suppression`):**
   Connects `primeLogMobiusLaplaceGapClockSample_isInfiniteTorusRayRajchman`,
   `primeLogMobiusExponentialGapClockSample_isInfiniteTorusRayRajchman`,
   `countableGammaHeightClockSample_fourier_integral`,
   `primeLogGammaHeightClockSample_isInfiniteTorusRayRajchman`,
   `primeLogSemilocalGammaClockSample_isInfiniteTorusRayRajchman`, and
   `primeLogLogisticKernelClockSample_isInfiniteTorusRayRajchman`
   (`HTGeometry/CaiChenFangGuoRajchman.lean:1679, 1693, 1930, 1961, 2045, 2091`):
   every nonzero finite-support prime-logarithm character $m : \mathrm{Primes} \to_0 \mathbb{Z}$
   is ray-Rajchman suppressed on the infinite torus $\prod_p \mathbb{T}$ under Möbius Laplace-gap,
   Möbius exponential-gap, normalized Gamma-height (with exact Fourier integral
   $\cosh(\Delta(m, \omega)/2)^{-r}$), Sonin semilocal Archimedean Gamma, and logistic
   cutoff-derivative clock sampling.

3. **Preissmann–Lévêque / Montgomery–Vaughan Eigen-Identity, Mellin–Plancherel Vertical-Line $L^2$
   Bound, and Subthreshold $u_0$–Böttcher Independence
   (`montgomeryVaughan_eigenIdentity_mellinPlancherel_and_u0_capstone`):**
   - Connects `RiemannGaussian.MontgomeryVaughan.eigen_identity'`
     (`HTGeometry/RiemannGaussian/MontgomeryVaughan/EigenIdentity.lean:47`): exact Hilbert-matrix
     eigen-identity $\mu^2 \|u_m\|^2 = \sum_{n \neq m} c_m^2 c_n^2 \|u_n\|^2 / (\lambda_m - \lambda_n)^2
     + 2 \sum_{n \neq m} c_m^3 c_n \operatorname{Re}(u_m \bar{u}_n) / (\lambda_m - \lambda_n)^2$.
   - Connects `GaloisForLFunctions.HTGeometry.MellinPlancherel.integral_norm_sq_mellin_eq` and
     `integral_norm_sq_mellin_le` (`HTGeometry/MellinPlancherelBound.lean:57, 78`): exact
     Mellin–Plancherel identity on $\operatorname{Re} s = \sigma$ and vertical-line $L^2$ bound
     $\int_{\mathbb{R}} |\mathcal{M}f(\sigma + it)|^2\,dt \le 2\pi B^2 b^{2\sigma}(\log b - \log a)$.
   - Connects `U0Capstone.u0_topic_capstone` (`U0/U0Capstone.lean:103`): unconditional algebraic
     independence $u_0 \perp \psi$ over $\mathbb{C}(z)$ across the entire viable region (including
     strictly below the $2 + \sqrt{2}$ threshold at $b = 3$).
-/

open Complex MeasureTheory Set Filter Topology Finset Metric
open scoped Real BigOperators ComplexConjugate ContDiff
open HurwitzZetaContinuation HurwitzAllNHZeta HurwitzZetaShift
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.MellinPlancherel
open RiemannGaussian.MontgomeryVaughan
open Bottcher U0ParameterSpace U0PhiMStep U0PhiMStepFar U0MStepBranch U0Capstone

noncomputable section

namespace GaloisForLFunctions.BiScaleUncertainty

set_option autoImplicit false

/-! ## §1. Hurwitz Canonical Anchor Level Graph, Exact Zeta Zero Contact Order, and All-$N$ Independence -/

/-- **Hurwitz Canonical Anchor Level Graph, Exact Zeta Zero Contact Order, and All-$N$ Quadratic
Independence (`hurwitz_anchor_level_graph_contact_and_allN_independence`):**
1. At every anchor $(s, 1)$ with $\operatorname{Re} s > 0$ and $s \neq 1$, the shift partial
   derivative of `continuedHzeta` is $-s \zeta(s+1) \neq 0$, yielding a unique holomorphic local
   level graph $a = A(z)$ with $A(s) = 1$ such that $\zeta(z, a) = \zeta(s) \iff a = A(z)$ near $(s, 1)$.
2. Along any local Hurwitz zero graph $\zeta(z, A(z)) = 0$ with $A(\rho) = 1$ ($\operatorname{Re} \rho > 0$,
   $\rho \neq 1$), the displacement $1 - A(z)$ has the exact analytic zero order of $\zeta(z)$ at $\rho$:
   $\operatorname{analyticOrderAt}(1 - A, \rho) = \operatorname{analyticOrderAt}(\zeta, \rho)$.
3. For $\operatorname{Re} w > 1$, $w \notin \mathbb{Z}$, and any $N \in \mathbb{N}$, any symmetric
   degree-$\le 2$ polynomial-coefficient relation among $\zeta(w, a), \dots, \zeta(w+N, a)$ on
   $\operatorname{Im} a > 0$ has $q_{ij} = 0$, $l_j = 0$, and $cc = 0$. -/
theorem hurwitz_anchor_level_graph_contact_and_allN_independence
    {s rho w : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    (hrho : 0 < rho.re) (hrho1 : rho ≠ 1)
    {A : ℂ → ℂ} (hA : A rho = 1) (hAa : AnalyticAt ℂ A rho)
    (hgraph : ∀ᶠ z in 𝓝 rho, continuedHzeta z (A z) = 0)
    {N : ℕ} (hw1 : 1 < w.re) (hwZ : ∀ k : ℤ, (k : ℂ) ≠ w)
    (q : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ) (l : Fin (N + 1) → Polynomial ℂ)
    (cc : Polynomial ℂ) (hSymm : ∀ i j, q i j = q j i)
    (hrel : ∀ a : ℂ, 0 < a.im →
      (∑ i : Fin (N + 1), ∑ j : Fin (N + 1), (q i j).eval a
          * (hzeta (w + (i : ℂ)) a * hzeta (w + (j : ℂ)) a))
        + (∑ k : Fin (N + 1), (l k).eval a * hzeta (w + (k : ℂ)) a) + cc.eval a = 0) :
    (((fderiv ℂ (fun p : ℂ × ℂ => continuedHzeta p.1 p.2) (s, 1)).comp
        (ContinuousLinearMap.inr ℂ ℂ ℂ) =
      ContinuousLinearMap.toSpanSingleton ℂ (-s * riemannZeta (s + 1))) ∧
      (∃ B : ℂ → ℂ, B s = 1 ∧ AnalyticAt ℂ B s ∧
        ∀ᶠ p : ℂ × ℂ in 𝓝 (s, 1),
          continuedHzeta p.1 p.2 = riemannZeta s ↔ p.2 = B p.1)) ∧
    (analyticOrderAt (fun z => 1 - A z) rho = analyticOrderAt riemannZeta rho) ∧
    ((∀ i j, q i j = 0) ∧ (∀ j, l j = 0) ∧ cc = 0) :=
  ⟨⟨fderiv_continuedHzeta_joint_comp_inr hs hs1,
    exists_analytic_anchor_level_graph hs hs1⟩,
   analyticOrderAt_anchor_zero_graph_contact hrho hrho1 hA hAa hgraph,
   hurwitz_allN_hzeta_upper_half_plane hw1 hwZ q l cc hSymm hrel⟩

/-! ## §2. Infinite-Torus Ray-Rajchman Suppression of Prime-Logarithm Characters Across Clocks -/

/-- **Infinite-Torus Ray-Rajchman Suppression of Prime-Logarithm Characters Across Corpus Clocks
(`primeLog_infiniteTorus_rayRajchman_clock_suppression`):**
For every nonzero finite-support prime-logarithm character $m : \mathrm{Primes} \to_0 \mathbb{Z}$
and every positive Gamma-height shape $r > 0$:
1. The countable Gamma-height clock Fourier integral of any character $m_0$ on spectrum $\omega$
   equals $\cosh(\Delta(m_0, \omega)/2)^{-r}$.
2. The prime-logarithm character ray $m$ is ray-Rajchman on the infinite torus $\prod_p \mathbb{T}$
   under Möbius Laplace-gap, Möbius exponential-gap, normalized Gamma-height, Sonin semilocal
   Archimedean Gamma, and logistic cutoff-derivative clock sampling. -/
theorem primeLog_infiniteTorus_rayRajchman_clock_suppression
    (r : PositiveGammaHeightShape) (m : {q : Nat.Primes →₀ ℤ // q ≠ 0}) :
    ((∫ x, infiniteTorusFourier m.1 x
        ∂(countableClockSampledPhaseProbabilityMeasure
          (gammaHeightClockProbabilityMeasure r)
          (fun p : Nat.Primes => Real.log (p : ℝ)) : Measure (Nat.Primes → UnitAddCircle))) =
      ((Real.cosh (infiniteTorusCharacterDetuning m.1
          (fun p : Nat.Primes => Real.log (p : ℝ)) / 2) ^ (-r.1) : ℝ) : ℂ)) ∧
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        RHTower.mobiusCriticalLaplaceGapProbabilityMeasure
        (fun p : Nat.Primes => Real.log (p : ℝ)) : Measure (Nat.Primes → UnitAddCircle)) m.1 ∧
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        RHTower.mobiusCriticalExponentialGapProbabilityMeasure
        (fun p : Nat.Primes => Real.log (p : ℝ)) : Measure (Nat.Primes → UnitAddCircle)) m.1 ∧
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        (gammaHeightClockProbabilityMeasure r)
        (fun p : Nat.Primes => Real.log (p : ℝ)) : Measure (Nat.Primes → UnitAddCircle)) m.1 ∧
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        semilocalArchimedeanGammaClockProbabilityMeasure
        (fun p : Nat.Primes => Real.log (p : ℝ)) : Measure (Nat.Primes → UnitAddCircle)) m.1 ∧
    IsInfiniteTorusRayRajchman
      (countableClockSampledPhaseProbabilityMeasure
        logisticKernelClockProbabilityMeasure
        (fun p : Nat.Primes => Real.log (p : ℝ)) : Measure (Nat.Primes → UnitAddCircle)) m.1 :=
  ⟨countableGammaHeightClockSample_fourier_integral r (fun p : Nat.Primes => Real.log (p : ℝ)) m.1,
   primeLogMobiusLaplaceGapClockSample_isInfiniteTorusRayRajchman m,
   primeLogMobiusExponentialGapClockSample_isInfiniteTorusRayRajchman m,
   primeLogGammaHeightClockSample_isInfiniteTorusRayRajchman r m,
   primeLogSemilocalGammaClockSample_isInfiniteTorusRayRajchman m,
   primeLogLogisticKernelClockSample_isInfiniteTorusRayRajchman m⟩

/-! ## §3. Montgomery–Vaughan Eigen-Identity, Mellin–Plancherel Bound, and Subthreshold $u_0$ Capstone -/

/-- **Preissmann–Lévêque / Montgomery–Vaughan Eigen-Identity, Mellin–Plancherel Vertical-Line $L^2$
Bound, and Subthreshold $u_0$–Böttcher Independence
(`montgomeryVaughan_eigenIdentity_mellinPlancherel_and_u0_capstone`):**
1. Any eigenvector $u$ of the weighted Hilbert matrix $\sum_{n \neq m} c_m c_n u_n / (\lambda_m - \lambda_n) = i \mu u_m$
   satisfies the Preissmann–Lévêque / Montgomery–Vaughan identity `eigen_identity'`.
2. Any smooth function $f : \mathbb{R} \to \mathbb{C}$ supported in $[a, b]$ ($0 < a \le b$) with
   $\|f\| \le B$ satisfies the Mellin–Plancherel identity `integral_norm_sq_mellin_eq` and the
   vertical-line $L^2$ bound $\int_{\mathbb{R}} \|\mathcal{M}f(\sigma + it)\|^2\,dt \le 2\pi B^2 b^{2\sigma}(\log b - \log a)$
   for $\sigma \ge 0$.
3. Unconditionally, `u0_topic_capstone` holds: the obstructed parameter set is closed, the $m$-step
   Böttcher branch exists and is algebraically independent of $u_0$ over $\mathbb{C}(z)$ across the
   entire viable region, and subthreshold independence holds at $b = 3$ ($\|3\| < 2 + \sqrt{2}$). -/
theorem montgomeryVaughan_eigenIdentity_mellinPlancherel_and_u0_capstone
    {ι : Type*} [Fintype ι] [DecidableEq ι] {freq : ι → ℝ}
    (hinj : Function.Injective freq) (c : ι → ℝ) (hc : ∀ r, 0 < c r)
    (u : ι → ℂ) (μ : ℝ)
    (heig : ∀ m, ∑ n ∈ Finset.univ.erase m,
        ((c m * c n / (freq m - freq n) : ℝ) : ℂ) * u n = (μ : ℂ) * Complex.I * u m)
    (m : ι)
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hsupp : Function.support f ⊆ Icc a b) {σ : ℝ} (hσ : 0 ≤ σ) {B : ℝ}
    (hB : ∀ x, ‖f x‖ ≤ B) :
    (μ ^ (2 : ℕ) * ‖u m‖ ^ (2 : ℕ) =
      (∑ n ∈ Finset.univ.erase m, (c m * c n) ^ (2 : ℕ) * ‖u n‖ ^ (2 : ℕ) / (freq m - freq n) ^ (2 : ℕ))
      + 2 * ∑ n ∈ Finset.univ.erase m,
          c m ^ (3 : ℕ) * c n * (u m * conj (u n)).re / (freq m - freq n) ^ (2 : ℕ)) ∧
    ((∫ t : ℝ, ‖mellin f ((σ : ℂ) + t * I)‖ ^ 2 = 2 * Real.pi * ∫ v : ℝ, ‖logPull f σ v‖ ^ 2) ∧
      (∫ t : ℝ, ‖mellin f ((σ : ℂ) + t * I)‖ ^ 2 ≤
        2 * Real.pi * (B ^ 2 * b ^ (2 * σ) * (Real.log b - Real.log a)))) ∧
    (IsClosed Obstructed ∧
      (∃ b₀ : ℂ, b₀ ∈ frontier Obstructed ∧
        b₀ ∈ segment ℝ (⟨-33/25, 44/25⟩ : ℂ) (⟨-66/25, 88/25⟩ : ℂ)) ∧
      (∀ b₀ : ℂ, (∀ z : ℂ, ‖z‖ ≤ 1 → z ∉ filledJulia b₀) →
        ∃ (r₀ : ℝ) (N : ℕ), 1 < r₀ ∧
          AnalyticOnNhd ℂ (psiN b₀ N) (ball (0 : ℂ) r₀) ∧ (∀ z : ℂ, psiN b₀ N z ≠ 0)) ∧
      (∀ b₀ : ℂ, (∀ z : ℂ, ‖z‖ ≤ 1 → z ∉ filledJulia b₀) → MStepIndependence b₀) ∧
      MStepIndependence (3 : ℂ)) :=
  ⟨eigen_identity' hinj c hc u μ heig m,
   ⟨integral_norm_sq_mellin_eq hf ha hsupp σ,
    integral_norm_sq_mellin_le hf ha hab hsupp hσ hB⟩,
   u0_topic_capstone⟩

end GaloisForLFunctions.BiScaleUncertainty

end
