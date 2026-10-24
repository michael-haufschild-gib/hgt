import GaloisForLFunctions.BiScaleUncertainty.FactorialMuntzTailWeilGrowth
import GaloisForLFunctions.BiScaleUncertainty.PrimeGraphClockCorrelationKernels
import GaloisForLFunctions.BiScaleUncertainty.PrimeGraphClockOffDiagonalSynthesisAndStationaryEnergyProducer
import GaloisForLFunctions.BiScaleUncertainty.PrimeClockGraphTailTightness
import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialRampSmoothingAndGramMargin
import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialTailSpanWeilCoercivity
import GaloisForLFunctions.RHTower.WeilWorkExposingRayCoherentCompletion

/-!
# Producer Completion, Energy Redistribution, and Prime Clock Correlation Kernel Synthesis

This module resolves the two coupled problems on producer completion and prime-clock correlation
kernels in the Bi-Scale Uncertainty programme:

1. **Bounded-Cost Producer Completion and Multi-Scale Archimedean Redistribution.**
   - *Single-scale localization vs. rank-one source readout:* For a single scale `n`, the
     smoothed correction tail `U_{n,k} = factorialMuntzSmoothedTail n k` has prime and polar
     explicit-formula channels bounded by `(factorialMuntzTailPrimeBudget + 144 e²) / (n + 1)`
     while its archimedean energy grows like `((1/2) log(n + 1) - C_arch) ∫ U_{n,k}²`, forcing
     `Re W(U_{n,k}, U_{n,k}) / ∫ U_{n,k}² → +∞`. However, the completed source
     `H_{n,k} = r_{n,k} + U_{n,k}` has rank-one zero-divisor readout
     `F_{H_{n,k}}(ρ) = κ_k(ρ) c_n / ρ` with `c_n = 1 / (2 √(n + 1))`, so its zero-divisor
     sampling mass is bounded by `O(1 / (n + 1))` without the logarithmic factor. This
     transfers the `(1/2) log(n + 1)` archimedean growth directly into a positive Weil margin
     `Re W(r_{n,k}, r_{n,k}) ≥ log(n + 1) / (4096 (n + 1)) ≥ δ Z(r_{n,k})` on the compact
     smoothed ramp `r_{n,k}`.
   - *Zero-cost multi-scale completion on the codimension-one pole-free hyperplane:* Across
     multiple scales `n ∈ S`, the zero-divisor readout of the completed source combination
     `H_{S,a,k} = ∑_{n ∈ S} a_n H_{n,k}` factors through the single linear functional
     `Λ_pole(S, a) = ∑_{n ∈ S} a_n c_n`. On the codimension-one pole-free hyperplane
     `Λ_pole(S, a) = 0` (in particular for every canonical two-scale pair
     `c_{n₂} H_{n₁,k} - c_{n₁} H_{n₂,k}`), the completion has identically zero zero-divisor
     mass `Z(H_{S,a,k}) = 0` and identically zero Weil pairing `W(H_{S,a,k}, g) = 0`.
     Consequently, the compactly supported ramp combination `R_{S,a,k}` and the tail
     combination `U_{S,a,k}` have opposite zero-divisor readouts and identically equal
     zero-divisor mass and Weil energy with zero completion loss, and for any real pole-free
     combination supported on `n + 1 ≥ M ≥ 2`,
     `lim_{k → ∞} Re W(R_{S,d,k}, R_{S,d,k}) ≥ ((A/2) log M - C) ∑_{n ∈ S} ‖d_n a_n‖²`.
   - *Coherent step-subdivision completion of far polar packets:* Every far polar packet
     `farPolarTest X` (`X ≥ 4`) admits a finite nonnegative polar completion by `N²`
     coherent step packets at the same aperture `X + 17/50` that cancels every integer atom
     `n ≥ 2` identically at uniformly bounded total archimedean energy `≤ C` while preserving a
     strictly positive total-energy floor across short-step refinements.

2. **Prime Clock Mass and Edge Kernels: Curve Identification, Operator Decompositions,
   Center-Decay Estimates, and Off-Diagonal Sign Characterization.**
   - *Exact curve representation:* For all `k : ℕ` and `t, lag : ℝ`, `primeClockMassKernel k t lag`
     and `primeClockEdgeKernel k t lag` are the mass and edge inner products of
     `PrimeClock.curve k (t + lag)` and `PrimeClock.curve k t`, and their difference is
     identically `sourcePair (PrimeClock.curve k (t + lag)) (PrimeClock.curve k t)`.
   - *Operator decompositions, Cauchy–Schwarz bounds, and center decay:* The kernel difference
     decomposes into the stationary edge correlation minus the archimedean ground-state diagonal
     minus the prime-shift correlation (and into stationary + `primeGenerator` +
     `groundPotentialOperator - I`), obeys exact lag-reversal symmetry and Cauchy–Schwarz bounds
     by the `lag = 0` diagonals, and decays to `0` as `t → ±∞` for every fixed `lag`, proving
     genuine dependence on the center variable `t`.
   - *Off-diagonal prime-pair realization and sign characterization:* The distinct-prime
     off-diagonal sum of `canonicalPrimeGraphClockAtom k N` is the exact `(N / (p q))`-weighted
     sum of `primeClockEdgeKernel - primeClockMassKernel` at `t = log(N/q)` and `lag = log(q/p)`.
     Its asymptotic nonnegativity implies `∀ q : SourceGraph, 0 ≤ sourceEnergy q` and rules out
     resolvent eigenvalues `μ > 1/2`.
-/

open Complex MeasureTheory Set Filter
open scoped BigOperators Topology ComplexConjugate InnerProductSpace
open _root_.Zeta23 _root_.RHTower _root_.RHTower.WeilSpectral _root_.RHTower.CHMDDoobGraph
open _root_.RHTower.CHMDClosedJump _root_.RHTower.CHMDPolar
open _root_.RHTower.ExposingRayCompletion
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open GaloisForLFunctions.ArithmeticPositivityTheory

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

/-! ## §1. Producer Completion and Multi-Scale Archimedean Energy Redistribution -/

/-- **Single-scale tail localization vs. completed source transfer.**
For a single scale `n` and smoothing index `k`:
1. The smoothed tail `U_{n,k} = factorialMuntzSmoothedTail n k` has bounded prime+polar budget
   `≤ (factorialMuntzTailPrimeBudget + 144 e²) / (n + 1)`, eventual `L²` norm lower bound
   `1 / (512 (n + 1)) ≤ ∫ U_{n,k}²`, and logarithmic archimedean and Weil coercivity
   `((1/2) log(n + 1) - C_loss) ∫ U_{n,k}² ≤ Re W(U_{n,k}, U_{n,k})`.
2. Yet the completed source `H_{n,k}` has rank-one zero-divisor sampling mass bounded by
   `factorialCorrectedSamplingConstant / (n + 1)` without the `log(n + 1)` factor, transferring
   the logarithmic Weil positivity `log(n + 1) / (4096 (n + 1)) ≤ Re W(r_{n,k}, r_{n,k})` and
   relative positive margin `δ Z(r_{n,k}) ≤ Re W(r_{n,k}, r_{n,k})` directly to the compactly
   supported smoothed ramp `r_{n,k}`. -/
theorem single_scale_tail_localization_and_ramp_transfer :
    (∀ n k : ℕ,
      |(zetaZeroConfig.W (fun x => (factorialMuntzSmoothedTail n k x : ℂ))
          (fun x => (factorialMuntzSmoothedTail n k x : ℂ))).re -
        archGammaEnergy (factorialMuntzSmoothedTail n k)| ≤
        (factorialMuntzTailPrimeBudget + 144 * Real.exp 1 ^ 2) / ((n + 1 : ℕ) : ℝ) ∧
      zetaZeroSquareMass (fun x => (factorialMuntzSmoothed n k x : ℂ)) ≤
        factorialCorrectedSamplingConstant / ((n + 1 : ℕ) : ℝ)) ∧
    (∀ n : ℕ, ∀ᶠ k : ℕ in atTop,
      1 / (512 * ((n + 1 : ℕ) : ℝ)) ≤ ∫ x : ℝ, factorialMuntzSmoothedTail n k x ^ 2 ∧
      (Real.log ((n + 1 : ℕ) : ℝ) / 2 - factorialMuntzTailWeilLoss) *
          (∫ x : ℝ, factorialMuntzSmoothedTail n k x ^ 2) ≤
        (zetaZeroConfig.W (fun x => (factorialMuntzSmoothedTail n k x : ℂ))
          (fun x => (factorialMuntzSmoothedTail n k x : ℂ))).re) ∧
    (∀ᶠ n : ℕ in atTop, ∀ᶠ k : ℕ in atTop,
      Real.log ((n + 1 : ℕ) : ℝ) / (4096 * ((n + 1 : ℕ) : ℝ)) ≤
        (zetaZeroConfig.W (fun x => (factorialMuntzSmoothedRamp n k x : ℂ))
          (fun x => (factorialMuntzSmoothedRamp n k x : ℂ))).re) ∧
    (∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop, ∀ᶠ k : ℕ in atTop,
      δ * zetaZeroSquareMass (fun x => (factorialMuntzSmoothedRamp n k x : ℂ)) ≤
        (zetaZeroConfig.W (fun x => (factorialMuntzSmoothedRamp n k x : ℂ))
          (fun x => (factorialMuntzSmoothedRamp n k x : ℂ))).re) := by
  refine ⟨fun n k => ⟨factorialMuntzSmoothedTail_zero_arch_budget n k,
      factorialCorrected_zeroSquare_le n k⟩,
    fun n => ?_, factorialMuntzSmoothedRamp_weil_log_lower,
    exists_factorialMuntzSmoothedRamp_relative_positive_margin⟩
  filter_upwards [factorialMuntzSmoothedTail_sq_integral_eventually_lower n,
    factorialMuntzSmoothedTail_weil_log_lower n] with k h1 h2
  exact ⟨h1, h2⟩

/-- The complexified real smoothed tail combination `factorialTailCombinationSmoothed S d k`
coincides pointwise with `factorialSmoothedTailCombo S (fun n => (d n : ℂ)) k`. -/
theorem factorialTailCombinationSmoothed_ofReal_eq_tailCombo
    (S : Finset ℕ) (d : ℕ → ℝ) (k : ℕ) :
    (fun x : ℝ => (factorialTailCombinationSmoothed S d k x : ℂ)) =
      factorialSmoothedTailCombo S (fun n => (d n : ℂ)) k := by
  funext x
  simp [factorialTailCombinationSmoothed, factorialSmoothedTailCombo]

/-- **Multi-scale zero-cost completion on the codimension-one pole-free hyperplane.**
For any finite scale set `S` and complex weights `a : ℕ → ℂ` in the kernel of the rank-one pole
functional `factorialPoleFunctional S a = ∑_{n ∈ S} a_n / (2 √(n + 1)) = 0`:
1. The completed source combination `H_{S,a,k} = factorialSmoothedCombo S a k` has identically
   zero zero-divisor sampling mass `Z(H_{S,a,k}) = 0` and identically zero Weil pairing
   `W(H_{S,a,k}, g) = 0` with every test `g`.
2. Consequently, the compactly supported smoothed ramp combination `R_{S,a,k}` and the smoothed
   tail combination `U_{S,a,k}` have opposite readouts at every nontrivial zero and identically
   equal zero-divisor mass and Weil energy at every smoothing index `k`, with zero completion
   loss. -/
theorem pole_free_hyperplane_zero_cost_completion
    (S : Finset ℕ) (a : ℕ → ℂ) (k : ℕ) (h0 : factorialPoleFunctional S a = 0) :
    (∀ ρ : zetaZeroConfig.carrier,
      paperFT (factorialSmoothedCombo S a k) (gammaOf ρ) = 0 ∧
      paperFT (factorialSmoothedRampCombo S a k) (gammaOf ρ) =
        -paperFT (factorialSmoothedTailCombo S a k) (gammaOf ρ)) ∧
    zetaZeroSquareMass (factorialSmoothedCombo S a k) = 0 ∧
    (∀ g : ℝ → ℂ,
      zetaZeroConfig.W (factorialSmoothedCombo S a k) g = 0 ∧
      zetaZeroConfig.W g (factorialSmoothedCombo S a k) = 0) ∧
    zetaZeroSquareMass (factorialSmoothedRampCombo S a k) =
      zetaZeroSquareMass (factorialSmoothedTailCombo S a k) ∧
    zetaZeroConfig.W (factorialSmoothedRampCombo S a k)
        (factorialSmoothedRampCombo S a k) =
      zetaZeroConfig.W (factorialSmoothedTailCombo S a k)
        (factorialSmoothedTailCombo S a k) :=
  ⟨fun ρ => ⟨paperFT_factorialSmoothedCombo_eq_zero_of_pole_zero S a h0 k ρ,
      paperFT_factorialSmoothedRampCombo_eq_neg_tailCombo_of_pole_zero S a h0 k ρ⟩,
    zetaZeroSquareMass_factorialSmoothedCombo_eq_zero_of_pole_zero S a h0 k,
    weil_factorialSmoothedCombo_eq_zero_of_pole_zero S a h0 k,
    (zeroSquareMass_and_weil_rampCombo_eq_tailCombo_of_pole_zero S a h0 k).1,
    (zeroSquareMass_and_weil_rampCombo_eq_tailCombo_of_pole_zero S a h0 k).2⟩

/-- **High-scale logarithmic Weil coercivity transferred to compact ramp combinations on the
pole-free hyperplane.**
For any finite scale set `S` supported on `n + 1 ≥ M ≥ 2` and any real weights `d : ℕ → ℝ`
satisfying the pole-free condition `factorialPoleFunctional S (fun n => (d n : ℂ)) = 0`, the
compactly supported smoothed ramp combinations
`R_{S,d,k} = factorialSmoothedRampCombo S (fun n => (d n : ℂ)) k` satisfy:
1. At every smoothing scale `k`, `W(R_{S,d,k}, R_{S,d,k}) = W(U_{S,d,k}, U_{S,d,k})` with zero
   completion cost (`Z(H_{S,d,k}) = 0` and `W(H_{S,d,k}, H_{S,d,k}) = 0`).
2. As `k → ∞`, `Re W(R_{S,d,k}, R_{S,d,k})` converges to `Re W(g_{S,d}, g_{S,d})` where
   `g_{S,d} = factorialTailCombination S d`.
3. This limit obeys the high-scale logarithmic coercivity bound
   `((factorialWeightedPhaseLower / 2) * log M - factorialSpanWeilOffset) ∑_{n ∈ S} ‖d_n a_n‖² ≤ Re W(g_{S,d}, g_{S,d})`. -/
theorem pole_free_ramp_combination_smoothing_limit_and_weil_coercivity
    (S : Finset ℕ) (d : ℕ → ℝ) {M : ℕ} (hM : 2 ≤ M) (hS : ∀ n ∈ S, M ≤ n + 1)
    (h0 : factorialPoleFunctional S (fun n => (d n : ℂ)) = 0) :
    (∀ k : ℕ,
      zetaZeroSquareMass (factorialSmoothedCombo S (fun n => (d n : ℂ)) k) = 0 ∧
      zetaZeroConfig.W (factorialSmoothedRampCombo S (fun n => (d n : ℂ)) k)
          (factorialSmoothedRampCombo S (fun n => (d n : ℂ)) k) =
        zetaZeroConfig.W (fun x => (factorialTailCombinationSmoothed S d k x : ℂ))
          (fun x => (factorialTailCombinationSmoothed S d k x : ℂ))) ∧
    Tendsto (fun k : ℕ =>
        (zetaZeroConfig.W (factorialSmoothedRampCombo S (fun n => (d n : ℂ)) k)
          (factorialSmoothedRampCombo S (fun n => (d n : ℂ)) k)).re)
      atTop
      (𝓝 (zetaZeroConfig.W (fun x => (factorialTailCombination S d x : ℂ))
        (fun x => (factorialTailCombination S d x : ℂ))).re) ∧
    ((factorialWeightedPhaseLower / 2) * Real.log M - factorialSpanWeilOffset) *
        (∑ n ∈ S, ‖factorialTailCombinationPhaseCoeff d n‖ ^ 2) ≤
      (zetaZeroConfig.W (fun x => (factorialTailCombination S d x : ℂ))
        (fun x => (factorialTailCombination S d x : ℂ))).re := by
  have hEq : ∀ k : ℕ,
      zetaZeroConfig.W (factorialSmoothedRampCombo S (fun n => (d n : ℂ)) k)
        (factorialSmoothedRampCombo S (fun n => (d n : ℂ)) k) =
      zetaZeroConfig.W (fun x => (factorialTailCombinationSmoothed S d k x : ℂ))
        (fun x => (factorialTailCombinationSmoothed S d k x : ℂ)) := by
    intro k
    rw [factorialTailCombinationSmoothed_ofReal_eq_tailCombo]
    exact (zeroSquareMass_and_weil_rampCombo_eq_tailCombo_of_pole_zero S
      (fun n => (d n : ℂ)) h0 k).2
  refine ⟨fun k => ⟨zetaZeroSquareMass_factorialSmoothedCombo_eq_zero_of_pole_zero S _ h0 k,
      hEq k⟩, ?_, factorialTailCombination_re_W_coercivity S d hM hS⟩
  simp_rw [hEq]
  exact (Complex.continuous_re.tendsto _).comp (tendsto_W_factorialTailCombinationSmoothed S d)

/-- **Uniformly bounded archimedean completion and positive total-energy floor for far polar
packets via coherent step subdivision.**
1. There exists an absolute constant `C` such that for every `X ≥ 4`, `farPolarTest X` admits a
   finite family of `N²` coherent polar step packets `h_i` at the same aperture `X + 17/50` with
   nonnegative weights `α_i ≥ 0` that cancels every integer atom `n ≥ 2` identically while
   keeping total archimedean energy bounded by `C`.
2. For every separation threshold `X₀ > 0`, there exists `δ > 0` such that under every short-step
   refinement `0 ≤ s ≤ 1/200` with `X₀ ≤ N * s`, the combined archimedean energy of
   `farPolarTest (N * s)` and its coherent repair family is at least `δ`. -/
theorem exists_bounded_archimedean_coherent_polar_completion :
    (∃ C : ℝ, ∀ X : ℝ, 4 ≤ X →
      ∃ (N : ℕ) (h : Fin N × Fin N → ℝ → ℂ) (α : Fin N × Fin N → ℝ),
        (∀ i, IsPolarTest (X + 17 / 50) (h i)) ∧
        (∀ i, 0 ≤ α i) ∧
        (∀ n : ℕ, 2 ≤ n → atomCoeff (farPolarTest X) n + ∑ i, α i * atomCoeff (h i) n = 0) ∧
        (∑ i, α i * archEnergy (h i)) ≤ C) ∧
    (∀ X₀ : ℝ, 0 < X₀ → ∃ δ : ℝ, 0 < δ ∧
      ∀ (N : ℕ) (s : ℝ), 0 ≤ s → s ≤ 1 / 200 → X₀ ≤ N * s →
        δ ≤ archEnergy (farPolarTest (N * s)) +
          ∑ i : Fin N × Fin N, (weight N s i / mass N s) * archEnergy (repair N s i)) :=
  ⟨bounded_coherent_completion, geometric_completion_uniform_positive_floor⟩

/-! ## §2. Prime Clock Mass and Edge Kernels: Curve Representation, Operator Decompositions,
Center Decay, and Off-Diagonal Sign Characterization -/

/-- The vertex component of `PrimeClock.curve k t` coincides almost everywhere under `massMeasure`
with `primeClockProfile k t`. -/
theorem primeClockCurve_fst_profile_ae (k : ℕ) (t : ℝ) :
    (PrimeClock.curve k t).val.fst =ᵐ[massMeasure] primeClockProfile k t :=
  criticalClockGraph_source (cutoff k)
    (GaloisForLFunctions.HTGeometry.boundedVariationOn_of_contDiff_compact
      ((cutoff_contDiff k).of_le (by norm_num)) (cutoff_hasCompactSupport k)) t

/-- The edge component of `PrimeClock.curve k t` coincides almost everywhere under `edgeMeasure`
with `difference (primeClockProfile k t)`. -/
theorem primeClockCurve_snd_profile_ae (k : ℕ) (t : ℝ) :
    (PrimeClock.curve k t).val.snd =ᵐ[edgeMeasure] difference (primeClockProfile k t) := by
  have hg := (PrimeClock.curve k t).property
  filter_upwards [hg,
    nonsingular_left.ae (primeClockCurve_fst_profile_ae k t),
    nonsingular_right.ae (primeClockCurve_fst_profile_ae k t)] with e he hl hr
  change _ = _ - _ at he
  rw [he, hl, hr]
  rfl

/-- The mass correlation kernel `primeClockMassKernel k t lag` is the `L²(0, 1)` mass inner
product of `PrimeClock.curve k (t + lag)` and `PrimeClock.curve k t`. -/
theorem primeClockMassKernel_eq_inner_curve_fst (k : ℕ) (t lag : ℝ) :
    primeClockMassKernel k t lag =
      ⟪(PrimeClock.curve k (t + lag)).val.fst, (PrimeClock.curve k t).val.fst⟫_ℝ := by
  rw [L2.inner_def, primeClockMassKernel]
  apply integral_congr_ae
  filter_upwards [primeClockCurve_fst_profile_ae k (t + lag),
    primeClockCurve_fst_profile_ae k t] with x hx hy
  simp only [RCLike.inner_apply, conj_trivial]
  rw [hx, hy]
  ring

/-- The edge correlation kernel `primeClockEdgeKernel k t lag` is the `L²(ℝ)` edge inner
product of `PrimeClock.curve k (t + lag)` and `PrimeClock.curve k t`. -/
theorem primeClockEdgeKernel_eq_inner_curve_snd (k : ℕ) (t lag : ℝ) :
    primeClockEdgeKernel k t lag =
      ⟪(PrimeClock.curve k (t + lag)).val.snd, (PrimeClock.curve k t).val.snd⟫_ℝ := by
  rw [L2.inner_def, primeClockEdgeKernel]
  apply integral_congr_ae
  filter_upwards [primeClockCurve_snd_profile_ae k (t + lag),
    primeClockCurve_snd_profile_ae k t] with e hx hy
  simp only [RCLike.inner_apply, conj_trivial]
  rw [hx, hy]
  ring

/-- **Exact identification of the kernel difference with `sourcePair` along the clock curve.**
For every cutoff index `k` and all `t, lag : ℝ`, the difference between the edge and mass
kernels is identically the Doob source pairing of `PrimeClock.curve k (t + lag)` and
`PrimeClock.curve k t`. -/
theorem primeClockEdgeKernel_sub_massKernel_eq_sourcePair_curve (k : ℕ) (t lag : ℝ) :
    primeClockEdgeKernel k t lag - primeClockMassKernel k t lag =
      sourcePair (PrimeClock.curve k (t + lag)) (PrimeClock.curve k t) := by
  rw [primeClockEdgeKernel_eq_inner_curve_snd, primeClockMassKernel_eq_inner_curve_fst]
  rfl

/-- **Operator decompositions of `primeClockEdgeKernel` and `primeClockEdgeKernel - primeClockMassKernel`.**
Retaining both the center variable `t` and the cutoff `k`, the edge kernel and the kernel
difference decompose into:
1. `primeClockEdgeKernel k t lag = stationary + primeGenerator + groundPotentialOperator`, and
2. `primeClockEdgeKernel k t lag - primeClockMassKernel k t lag = stationary - archGroundConstant * θ-overlap - primeShiftOperator`. -/
theorem primeClockKernel_operator_decompositions (k : ℕ) (t lag : ℝ) :
    primeClockEdgeKernel k t lag =
      ⟪(fullGroundEquiv (PrimeClock.curve k (t + lag))).val.snd,
        (fullGroundEquiv (PrimeClock.curve k t)).val.snd⟫_ℝ +
      ⟪primeGenerator (PrimeClock.curve k (t + lag)).val.fst,
        (PrimeClock.curve k t).val.fst⟫_ℝ +
      ⟪groundPotentialOperator (PrimeClock.curve k (t + lag)).val.fst,
        (PrimeClock.curve k t).val.fst⟫_ℝ ∧
    primeClockEdgeKernel k t lag - primeClockMassKernel k t lag =
      ⟪(fullGroundEquiv (PrimeClock.curve k (t + lag))).val.snd,
        (fullGroundEquiv (PrimeClock.curve k t)).val.snd⟫_ℝ -
      ⟪archDiagonalOperator (PrimeClock.curve k (t + lag)).val.fst,
        (PrimeClock.curve k t).val.fst⟫_ℝ -
      ⟪primeShiftOperator (PrimeClock.curve k (t + lag)).val.fst,
        (PrimeClock.curve k t).val.fst⟫_ℝ := by
  rw [primeClockEdgeKernel_sub_massKernel_eq_sourcePair_curve,
    primeClockEdgeKernel_eq_inner_curve_snd]
  refine ⟨(inner_snd_eq_stationary_add_primeGenerator_add_groundPotential
      (PrimeClock.curve k (t + lag)) (PrimeClock.curve k t)).2, ?_⟩
  rw [sourcePair_eq_stationary_sub_arch_sub_primeShift, inner_archDiagonalOperator]

/-- **Lag-reversal symmetry of the prime clock kernels and their difference.**
Shifting the center from `t` to `t + lag` and negating `lag` leaves `primeClockMassKernel`,
`primeClockEdgeKernel`, and their difference invariant. -/
theorem primeClockKernel_lag_reversal_symm (k : ℕ) (t lag : ℝ) :
    primeClockMassKernel k (t + lag) (-lag) = primeClockMassKernel k t lag ∧
    primeClockEdgeKernel k (t + lag) (-lag) = primeClockEdgeKernel k t lag ∧
    primeClockEdgeKernel k (t + lag) (-lag) - primeClockMassKernel k (t + lag) (-lag) =
      primeClockEdgeKernel k t lag - primeClockMassKernel k t lag := by
  have h1 : primeClockMassKernel k (t + lag) (-lag) = primeClockMassKernel k t lag := by
    rw [primeClockMassKernel_eq_inner_curve_fst, primeClockMassKernel_eq_inner_curve_fst,
      add_neg_cancel_right, real_inner_comm]
  have h2 : primeClockEdgeKernel k (t + lag) (-lag) = primeClockEdgeKernel k t lag := by
    rw [primeClockEdgeKernel_eq_inner_curve_snd, primeClockEdgeKernel_eq_inner_curve_snd,
      add_neg_cancel_right, real_inner_comm]
  exact ⟨h1, h2, by rw [h1, h2]⟩

/-- **Zero-lag diagonal identities.**
At `lag = 0`, the mass and edge kernels are the squared norms of the mass and edge components
of `PrimeClock.curve k t` (hence nonnegative), their sum is the squared graph norm
`‖PrimeClock.curve k t‖²`, and their difference is `sourceEnergy (PrimeClock.curve k t)`. -/
theorem primeClockKernel_zero_lag_identities (k : ℕ) (t : ℝ) :
    primeClockMassKernel k t 0 = ‖(PrimeClock.curve k t).val.fst‖ ^ 2 ∧
    primeClockEdgeKernel k t 0 = ‖(PrimeClock.curve k t).val.snd‖ ^ 2 ∧
    0 ≤ primeClockMassKernel k t 0 ∧
    0 ≤ primeClockEdgeKernel k t 0 ∧
    primeClockMassKernel k t 0 + primeClockEdgeKernel k t 0 = ‖PrimeClock.curve k t‖ ^ 2 ∧
    primeClockEdgeKernel k t 0 - primeClockMassKernel k t 0 =
      sourceEnergy (PrimeClock.curve k t) := by
  have hm : primeClockMassKernel k t 0 = ‖(PrimeClock.curve k t).val.fst‖ ^ 2 := by
    rw [primeClockMassKernel_eq_inner_curve_fst, add_zero, real_inner_self_eq_norm_sq]
  have he : primeClockEdgeKernel k t 0 = ‖(PrimeClock.curve k t).val.snd‖ ^ 2 := by
    rw [primeClockEdgeKernel_eq_inner_curve_snd, add_zero, real_inner_self_eq_norm_sq]
  have hsum : ‖(PrimeClock.curve k t).val.fst‖ ^ 2 + ‖(PrimeClock.curve k t).val.snd‖ ^ 2 =
      ‖PrimeClock.curve k t‖ ^ 2 := (graph_norm_sq (PrimeClock.curve k t)).symm
  have hdiff : primeClockEdgeKernel k t 0 - primeClockMassKernel k t 0 =
      sourceEnergy (PrimeClock.curve k t) := by
    rw [primeClockEdgeKernel_sub_massKernel_eq_sourcePair_curve, add_zero, sourcePair_self]
  refine ⟨hm, he, hm ▸ sq_nonneg _, he ▸ sq_nonneg _, ?_, hdiff⟩
  rw [hm, he, hsum]

/-- **Cauchy–Schwarz bounds for the mass kernel, edge kernel, and kernel difference.**
For all `k : ℕ` and `t, lag : ℝ`:
1. `|primeClockMassKernel k t lag| ≤ ‖(curve k (t + lag)).1‖ * ‖(curve k t).1‖` and
   `(primeClockMassKernel k t lag)² ≤ primeClockMassKernel k (t + lag) 0 * primeClockMassKernel k t 0`.
2. `|primeClockEdgeKernel k t lag| ≤ ‖(curve k (t + lag)).2‖ * ‖(curve k t).2‖` and
   `(primeClockEdgeKernel k t lag)² ≤ primeClockEdgeKernel k (t + lag) 0 * primeClockEdgeKernel k t 0`.
3. `|primeClockEdgeKernel k t lag - primeClockMassKernel k t lag| ≤ ‖curve k (t + lag)‖ * ‖curve k t‖`. -/
theorem primeClockKernel_cauchy_schwarz_bounds (k : ℕ) (t lag : ℝ) :
    |primeClockMassKernel k t lag| ≤
      ‖(PrimeClock.curve k (t + lag)).val.fst‖ * ‖(PrimeClock.curve k t).val.fst‖ ∧
    primeClockMassKernel k t lag ^ 2 ≤
      primeClockMassKernel k (t + lag) 0 * primeClockMassKernel k t 0 ∧
    |primeClockEdgeKernel k t lag| ≤
      ‖(PrimeClock.curve k (t + lag)).val.snd‖ * ‖(PrimeClock.curve k t).val.snd‖ ∧
    primeClockEdgeKernel k t lag ^ 2 ≤
      primeClockEdgeKernel k (t + lag) 0 * primeClockEdgeKernel k t 0 ∧
    |primeClockEdgeKernel k t lag - primeClockMassKernel k t lag| ≤
      ‖PrimeClock.curve k (t + lag)‖ * ‖PrimeClock.curve k t‖ := by
  have hm : |primeClockMassKernel k t lag| ≤
      ‖(PrimeClock.curve k (t + lag)).val.fst‖ * ‖(PrimeClock.curve k t).val.fst‖ := by
    rw [primeClockMassKernel_eq_inner_curve_fst]
    exact abs_real_inner_le_norm (PrimeClock.curve k (t + lag)).val.fst
      (PrimeClock.curve k t).val.fst
  have he : |primeClockEdgeKernel k t lag| ≤
      ‖(PrimeClock.curve k (t + lag)).val.snd‖ * ‖(PrimeClock.curve k t).val.snd‖ := by
    rw [primeClockEdgeKernel_eq_inner_curve_snd]
    exact abs_real_inner_le_norm (PrimeClock.curve k (t + lag)).val.snd
      (PrimeClock.curve k t).val.snd
  have hm_sq : primeClockMassKernel k t lag ^ 2 ≤
      primeClockMassKernel k (t + lag) 0 * primeClockMassKernel k t 0 := by
    rw [(primeClockKernel_zero_lag_identities k (t + lag)).1,
      (primeClockKernel_zero_lag_identities k t).1, ← mul_pow, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hm 2
  have he_sq : primeClockEdgeKernel k t lag ^ 2 ≤
      primeClockEdgeKernel k (t + lag) 0 * primeClockEdgeKernel k t 0 := by
    rw [(primeClockKernel_zero_lag_identities k (t + lag)).2.1,
      (primeClockKernel_zero_lag_identities k t).2.1, ← mul_pow, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) he 2
  refine ⟨hm, hm_sq, he, he_sq, ?_⟩
  rw [primeClockEdgeKernel_sub_massKernel_eq_sourcePair_curve]
  exact abs_sourcePair_le_norm_mul (PrimeClock.curve k (t + lag)) (PrimeClock.curve k t)

/-- **Center-decay of the prime clock kernels as `t → +∞` and `t → -∞`.**
For every cutoff `k` and every fixed `lag : ℝ`, both `primeClockMassKernel k t lag` and
`primeClockEdgeKernel k t lag` (and hence their difference) converge to `0` as `t → +∞` and as
`t → -∞`. In particular, the correlation kernels genuinely depend on the center variable `t`
rather than reducing to a stationary function of `lag` alone. -/
theorem primeClockKernel_tendsto_zero_atTop_and_atBot (k : ℕ) (lag : ℝ) :
    Tendsto (fun t : ℝ => primeClockMassKernel k t lag) atTop (𝓝 0) ∧
    Tendsto (fun t : ℝ => primeClockMassKernel k t lag) atBot (𝓝 0) ∧
    Tendsto (fun t : ℝ => primeClockEdgeKernel k t lag) atTop (𝓝 0) ∧
    Tendsto (fun t : ℝ => primeClockEdgeKernel k t lag) atBot (𝓝 0) ∧
    Tendsto (fun t : ℝ => primeClockEdgeKernel k t lag - primeClockMassKernel k t lag)
      atTop (𝓝 0) ∧
    Tendsto (fun t : ℝ => primeClockEdgeKernel k t lag - primeClockMassKernel k t lag)
      atBot (𝓝 0) := by
  have h_top : Tendsto (fun t : ℝ => ‖PrimeClock.curve k t‖) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mp (PrimeClock.curve_zero_atTop k)
  have h_bot : Tendsto (fun t : ℝ => ‖PrimeClock.curve k t‖) atBot (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mp (PrimeClock.curve_zero_atBot k)
  have h_shift_top : Tendsto (fun t : ℝ => ‖PrimeClock.curve k (t + lag)‖) atTop (𝓝 0) :=
    h_top.comp (tendsto_atTop_add_const_right atTop lag tendsto_id)
  have h_shift_bot : Tendsto (fun t : ℝ => ‖PrimeClock.curve k (t + lag)‖) atBot (𝓝 0) :=
    h_bot.comp (tendsto_atBot_add_const_right atBot lag tendsto_id)
  have h_prod_top :
      Tendsto (fun t : ℝ => ‖PrimeClock.curve k (t + lag)‖ * ‖PrimeClock.curve k t‖)
        atTop (𝓝 0) := by
    simpa using h_shift_top.mul h_top
  have h_prod_bot :
      Tendsto (fun t : ℝ => ‖PrimeClock.curve k (t + lag)‖ * ‖PrimeClock.curve k t‖)
        atBot (𝓝 0) := by
    simpa using h_shift_bot.mul h_bot
  have hm_bound (t : ℝ) :
      ‖primeClockMassKernel k t lag‖ ≤
        ‖PrimeClock.curve k (t + lag)‖ * ‖PrimeClock.curve k t‖ := by
    rw [Real.norm_eq_abs]
    exact (primeClockKernel_cauchy_schwarz_bounds k t lag).1.trans
      (mul_le_mul (norm_fst_le_norm _) (norm_fst_le_norm _) (norm_nonneg _) (norm_nonneg _))
  have he_bound (t : ℝ) :
      ‖primeClockEdgeKernel k t lag‖ ≤
        ‖PrimeClock.curve k (t + lag)‖ * ‖PrimeClock.curve k t‖ := by
    rw [Real.norm_eq_abs]
    exact (primeClockKernel_cauchy_schwarz_bounds k t lag).2.2.1.trans
      (mul_le_mul (norm_snd_le_norm _) (norm_snd_le_norm _) (norm_nonneg _) (norm_nonneg _))
  have hm_top := squeeze_zero_norm hm_bound h_prod_top
  have hm_bot := squeeze_zero_norm hm_bound h_prod_bot
  have he_top := squeeze_zero_norm he_bound h_prod_top
  have he_bot := squeeze_zero_norm he_bound h_prod_bot
  exact ⟨hm_top, hm_bot, he_top, he_bot,
    by simpa using he_top.sub hm_top, by simpa using he_bot.sub hm_bot⟩

/-- **Exact off-diagonal prime-pair sum in terms of `primeClockEdgeKernel - primeClockMassKernel`.**
For any finite set `S ⊆ ℕ` of positive integers (`∀ p ∈ S, 0 < p`) and any `N > 0`, the
off-diagonal source-pair sum of `canonicalPrimeGraphClockAtom k N` is the exact
`(N / (p q))`-weighted sum of `primeClockEdgeKernel - primeClockMassKernel` evaluated at
center `t = log(N / q)` and lag `log(q / p)`. -/
theorem offDiagSourcePairSum_eq_sum_primeClockKernel_diff
    (k : ℕ) {N : ℕ} (hN : 0 < N) (S : Finset ℕ) (hS : ∀ p ∈ S, 0 < p) :
    offDiagSourcePairSum S (canonicalPrimeGraphClockAtom k N) =
      ∑ p ∈ S, ∑ q ∈ S.erase p,
        ((N : ℝ) / ((p : ℝ) * (q : ℝ))) *
          (primeClockEdgeKernel k (Real.log ((N : ℝ) / (q : ℝ)))
              (Real.log ((q : ℝ) / (p : ℝ))) -
            primeClockMassKernel k (Real.log ((N : ℝ) / (q : ℝ)))
              (Real.log ((q : ℝ) / (p : ℝ)))) := by
  unfold offDiagSourcePairSum
  refine Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => ?_
  exact canonicalPrimeGraphClockAtom_sourcePair_eq_kernel hN
    (hS p hp) (hS q (Finset.mem_of_mem_erase hq))

/-- **Sign and spectral characterization of the off-diagonal kernel-difference sum.**
1. *Universal approximation of `sourceEnergy`:* For every `q : SourceGraph`, depth threshold
   `T₀ : ℝ`, and `ε > 0`, there exist `k : ℕ` and eventually all `N` with prime sets `S`
   (`p > √N`, `log(N/p) > T₀`) whose distinct-prime sum of
   `(N / (p q)) (primeClockEdgeKernel - primeClockMassKernel)` approximates `sourceEnergy q`
   within `ε + ε² + 2 ε ‖q‖` at diagonal cost `< ε`.
2. *Strict negativity for above-threshold eigenvectors:* For any nonzero `w : MassSpace` and
   `μ > 1 / 2` with `resolvent w = μ • w`, there exist `k : ℕ` and eventually all `N` with
   prime sets `S` for which the distinct-prime sum of
   `(N / (p q)) (primeClockEdgeKernel - primeClockMassKernel)` is strictly negative
   (`< ((1 - 2 * μ) / (2 * μ)) * ‖(rieszLift w).val.fst‖² < 0`).
3. *Nonnegativity criterion for `sourceEnergy q ≥ 0` and `μ ≤ 1 / 2`:* Nonnegativity of the
   distinct-prime kernel-difference sum along arbitrary-precision clock realizations forces
   `0 ≤ sourceEnergy q` and `μ ≤ 1 / 2`. -/
theorem primeClockKernel_diff_sign_and_spectral_characterization :
    (∀ (q : SourceGraph) (T₀ : ℝ) {ε : ℝ}, 0 < ε →
      ∃ k : ℕ, ∀ᶠ N : ℕ in atTop, ∃ S : Finset ℕ,
        (∀ p ∈ S, p.Prime ∧ Real.sqrt N < p ∧ T₀ < Real.log ((N : ℝ) / p)) ∧
        ‖(∑ p ∈ S, canonicalPrimeGraphClockAtom k N p) - q‖ < ε ∧
        (∑ p ∈ S, ‖canonicalPrimeGraphClockAtom k N p‖ ^ 2) < ε ∧
        |offDiagSourcePairSum S (canonicalPrimeGraphClockAtom k N) - sourceEnergy q| ≤
          ε + ε ^ 2 + 2 * ε * ‖q‖) ∧
    (∀ {μ : ℝ}, 1 / 2 < μ → ∀ {w : MassSpace}, w ≠ 0 → resolvent w = μ • w → ∀ T₀ : ℝ,
      let q := rieszLift w
      ((1 - 2 * μ) / (2 * μ)) * ‖q.val.fst‖ ^ 2 < 0 ∧
        ∃ k : ℕ, ∀ᶠ N : ℕ in atTop, ∃ S : Finset ℕ,
          (∀ p ∈ S, p.Prime ∧ Real.sqrt N < p ∧ T₀ < Real.log ((N : ℝ) / p)) ∧
          offDiagSourcePairSum S (canonicalPrimeGraphClockAtom k N) <
            ((1 - 2 * μ) / (2 * μ)) * ‖q.val.fst‖ ^ 2) ∧
    (∀ q : SourceGraph,
      (∀ ε > 0, ∃ k N : ℕ, ∃ S : Finset ℕ,
        ‖(∑ p ∈ S, canonicalPrimeGraphClockAtom k N p) - q‖ < ε ∧
        (∑ p ∈ S, ‖canonicalPrimeGraphClockAtom k N p‖ ^ 2) < ε ∧
        0 ≤ offDiagSourcePairSum S (canonicalPrimeGraphClockAtom k N)) →
      0 ≤ sourceEnergy q) ∧
    (∀ {μ : ℝ}, 0 < μ → ∀ {w : MassSpace}, w ≠ 0 → resolvent w = μ • w →
      (∀ ε > 0, ∃ k N : ℕ, ∃ S : Finset ℕ,
        ‖(∑ p ∈ S, canonicalPrimeGraphClockAtom k N p) - rieszLift w‖ < ε ∧
        (∑ p ∈ S, ‖canonicalPrimeGraphClockAtom k N p‖ ^ 2) < ε ∧
        0 ≤ offDiagSourcePairSum S (canonicalPrimeGraphClockAtom k N)) →
      μ ≤ 1 / 2) := by
  refine ⟨?_, ?_, sourceEnergy_nonneg_of_offDiag_primeClock_nonneg,
    @eigenvalue_le_one_half_of_offDiag_primeClock_nonneg⟩
  · intro q T₀ ε hε
    obtain ⟨k, hk⟩ := exists_cutoff_eventually_offDiag_primeClock_realization
      q (ContinuousLinearMap.id ℝ MassSpace) T₀ hε
    refine ⟨k, ?_⟩
    filter_upwards [hk] with N hN
    obtain ⟨S, hS, happ, hdiag, hE, -⟩ := hN
    exact ⟨S, hS, happ, hdiag, hE⟩
  · intro μ hμ w hw heig T₀
    obtain ⟨hneg, k, hk⟩ :=
      exists_cutoff_eventually_offDiag_primeClock_neg_of_eigenvector_gt_half hμ hw heig T₀
    refine ⟨hneg, k, ?_⟩
    filter_upwards [hk] with N hN
    obtain ⟨S, hS, -, -, hoff⟩ := hN
    exact ⟨S, hS, hoff⟩

end

end GaloisForLFunctions.BiScaleUncertainty
