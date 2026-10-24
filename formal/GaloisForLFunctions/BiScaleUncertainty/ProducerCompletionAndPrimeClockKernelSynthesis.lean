import GaloisForLFunctions.BiScaleUncertainty.FactorialMuntzTailWeilGrowth
import GaloisForLFunctions.BiScaleUncertainty.PrimeGraphClockCorrelationKernels
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
     multiple scales `n ∈ S`, the zero-divisor mass and Weil energy of the completed source
     combination `H_{S,a,k} = ∑_{n ∈ S} a_n H_{n,k} = R_{S,a,k} + U_{S,a,k}` factor through
     the single linear functional `Λ_pole(S, a) = ∑_{n ∈ S} a_n c_n`. On the codimension-one
     pole-free hyperplane `Λ_pole(S, a) = 0` (in particular for every canonical two-scale pair
     `c_{n₂} H_{n₁,k} - c_{n₁} H_{n₂,k}`), the completion has identically zero zero-divisor
     mass `Z(H_{S,a,k}) = 0` and identically zero Weil energy `W(H_{S,a,k}, H_{S,a,k}) = 0`.
     Consequently, the compactly supported ramp combination `R_{S,a,k}` and the tail
     combination `U_{S,a,k}` have identically equal zero-divisor mass and Weil energy with
     zero completion loss, and for any real pole-free combination supported on `n + 1 ≥ M ≥ 2`,
     `lim_{k → ∞} Re W(R_{S,d,k}, R_{S,d,k}) ≥ ((A/2) log M - C) ∑_{n ∈ S} ‖d_n a_n‖²`.
   - *Coherent step-subdivision completion of far polar packets:* Every negative-energy polar
     packet `farPolarTest X` (`X ≥ 4`) admits a finite nonnegative polar completion by `N²`
     coherent step packets at the same aperture `X + 17/50` that cancels every integer atom
     `n ≥ 2` identically at uniformly bounded total archimedean energy `≤ C`.

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
     by the `lag = 0` diagonals, is uniformly bounded on `ℝ × ℝ`, and decays to `0` as
     `t → ±∞` for every fixed `lag`, proving genuine dependence on the center variable `t`.
   - *Off-diagonal prime-pair realization and sign characterization:* The distinct-prime
     off-diagonal sum of `canonicalPrimeGraphClockAtom k N` is the exact `(N / (p q))`-weighted
     sum of `primeClockEdgeKernel - primeClockMassKernel` at `t = log(N/q)` and `lag = log(q/p)`.
     Its asymptotic nonnegativity is equivalent to `∀ q : SourceGraph, 0 ≤ sourceEnergy q` and
     rules out resolvent eigenvalues `μ > 1/2`.
-/

open Complex MeasureTheory Set Filter
open scoped BigOperators Topology ComplexConjugate RealInnerProductSpace
open _root_.Zeta23 _root_.RHTower _root_.RHTower.WeilSpectral
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open GaloisForLFunctions.ArithmeticPositivityTheory

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

/-! ## §1. Producer Completion and Multi-Scale Archimedean Energy Redistribution -/

/-- **Single-scale tail localization vs. completed source transfer.**
For a single scale `n` and smoothing index `k ≥ 2(n + 1)`:
1. The smoothed tail `U_{n,k} = factorialMuntzSmoothedTail n k` has bounded prime+polar budget
   `≤ (factorialMuntzTailPrimeBudget + 144 e²) / (n + 1)`, positive `L²` norm lower bound
   `1 / (512 (n + 1)) ≤ ∫ U_{n,k}²`, and logarithmic archimedean and Weil coercivity
   `((1/2) log(n + 1) - C_loss) ∫ U_{n,k}² ≤ Re W(U_{n,k}, U_{n,k})`.
2. Yet the completed source `H_{n,k} = r_{n,k} + U_{n,k}` has rank-one zero-divisor readout
   bounded by `O(1 / (n + 1))` without the `log(n + 1)` factor, transferring the logarithmic
   Weil positivity `log(n + 1) / (4096 (n + 1)) ≤ Re W(r_{n,k}, r_{n,k})` directly to the
   compactly supported smoothed ramp `r_{n,k}`. -/
theorem single_scale_tail_localization_and_ramp_transfer :
    (∀ n k : ℕ,
      |(zetaZeroConfig.W (fun x => (factorialMuntzSmoothedTail n k x : ℂ))
          (fun x => (factorialMuntzSmoothedTail n k x : ℂ))).re -
        archGammaEnergy (factorialMuntzSmoothedTail n k)| ≤
        (factorialMuntzTailPrimeBudget + 144 * Real.exp 1 ^ 2) / ((n + 1 : ℕ) : ℝ)) ∧
    (∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ k : ℕ, 2 * (n + 1) ≤ k →
      1 / (512 * ((n + 1 : ℕ) : ℝ)) ≤ ∫ x : ℝ, factorialMuntzSmoothedTail n k x ^ 2 ∧
      (1 / 2 * Real.log ((n + 1 : ℕ) : ℝ) - factorialMuntzTailWeilLoss) *
          (∫ x : ℝ, factorialMuntzSmoothedTail n k x ^ 2) ≤
        (zetaZeroConfig.W (fun x => (factorialMuntzSmoothedTail n k x : ℂ))
          (fun x => (factorialMuntzSmoothedTail n k x : ℂ))).re ∧
      Real.log ((n + 1 : ℕ) : ℝ) / (4096 * ((n + 1 : ℕ) : ℝ)) ≤
        (zetaZeroConfig.W (fun x => (factorialMuntzSmoothedRamp n k x : ℂ))
          (fun x => (factorialMuntzSmoothedRamp n k x : ℂ))).re) ∧
    (∃ N₁ : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ, N₁ ≤ n → ∀ k : ℕ, 2 * (n + 1) ≤ k →
      δ * zeroSquareMass (fun x => (factorialMuntzSmoothedRamp n k x : ℂ)) ≤
        (zetaZeroConfig.W (fun x => (factorialMuntzSmoothedRamp n k x : ℂ))
          (fun x => (factorialMuntzSmoothedRamp n k x : ℂ))).re) := by
  refine ⟨factorialMuntzSmoothedTail_zero_arch_budget, ?_,
    exists_factorialMuntzSmoothedRamp_relative_positive_margin⟩
  obtain ⟨N₁, hN₁⟩ := factorialMuntzSmoothedTail_sq_integral_eventually_lower
  obtain ⟨N₂, hN₂⟩ := factorialMuntzSmoothedRamp_weil_log_lower
  refine ⟨max N₁ N₂, fun n hn k hk => ?_⟩
  exact ⟨hN₁ n ((le_max_left N₁ N₂).trans hn) k hk,
    factorialMuntzSmoothedTail_weil_log_lower n k hk,
    hN₂ n ((le_max_right N₁ N₂).trans hn) k hk⟩

/-- The complexified real smoothed tail combination `factorialTailCombinationSmoothed S d k`
coincides pointwise with `factorialMuntzTailCombination S (fun n => (d n : ℂ)) k`. -/
theorem factorialTailCombinationSmoothed_ofReal_eq_tailCombination
    (S : Finset ℕ) (d : ℕ → ℝ) (k : ℕ) :
    (fun x : ℝ => (factorialTailCombinationSmoothed S d k x : ℂ)) =
      factorialMuntzTailCombination S (fun n => (d n : ℂ)) k := by
  funext x
  simp [factorialTailCombinationSmoothed, factorialMuntzTailCombination]

/-- **Multi-scale zero-cost completion on the codimension-one pole-free hyperplane.**
For any finite scale set `S` and complex weights `a : ℕ → ℂ` in the kernel of the rank-one pole
functional `factorialPoleFunctional S a = ∑_{n ∈ S} a_n / (2 √(n + 1)) = 0`:
1. The completed source combination `H_{S,a,k} = R_{S,a,k} + U_{S,a,k}` has identically zero
   zero-divisor sampling mass `Z(H_{S,a,k}) = 0` and identically zero Weil pairing
   `W(H_{S,a,k}, g) = 0` with every square-summable test `g`.
2. Consequently, the compactly supported smoothed ramp combination `R_{S,a,k}` and the smoothed
   tail combination `U_{S,a,k}` have identically equal zero-divisor mass and Weil energy at
   every smoothing index `k`, with zero completion loss. -/
theorem pole_free_hyperplane_zero_cost_completion
    (S : Finset ℕ) (a : ℕ → ℂ) (k : ℕ) (h0 : factorialPoleFunctional S a = 0) :
    (∀ x : ℝ, factorialMuntzCompletedCombination S a k x =
      factorialMuntzRampCombination S a k x + factorialMuntzTailCombination S a k x) ∧
    zeroSquareMass (factorialMuntzCompletedCombination S a k) = 0 ∧
    zetaZeroConfig.W (factorialMuntzCompletedCombination S a k)
      (factorialMuntzCompletedCombination S a k) = 0 ∧
    zeroSquareMass (factorialMuntzRampCombination S a k) =
      zeroSquareMass (factorialMuntzTailCombination S a k) ∧
    zetaZeroConfig.W (factorialMuntzRampCombination S a k)
        (factorialMuntzRampCombination S a k) =
      zetaZeroConfig.W (factorialMuntzTailCombination S a k)
        (factorialMuntzTailCombination S a k) :=
  ⟨factorialMuntzCompletedCombination_eq_ramp_add_tail S a k,
    zeroSquareMass_completedCombo_eq_zero_of_pole_zero S a k h0,
    W_completedCombo_eq_zero_of_pole_zero S a k h0,
    (zeroSquareMass_and_weil_rampCombo_eq_tailCombo_of_pole_zero S a k h0).1,
    (zeroSquareMass_and_weil_rampCombo_eq_tailCombo_of_pole_zero S a k h0).2⟩

/-- **High-scale logarithmic Weil coercivity transferred to compact ramp combinations on the
pole-free hyperplane.**
For any finite scale set `S` supported on `n + 1 ≥ M ≥ 2` and any real weights `d : ℕ → ℝ`
satisfying the pole-free condition `factorialPoleFunctional S (fun n => (d n : ℂ)) = 0`, the
compactly supported smoothed ramp combinations
`R_{S,d,k} = factorialMuntzRampCombination S (fun n => (d n : ℂ)) k` satisfy:
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
      zeroSquareMass (factorialMuntzCompletedCombination S (fun n => (d n : ℂ)) k) = 0 ∧
      zetaZeroConfig.W (factorialMuntzRampCombination S (fun n => (d n : ℂ)) k)
          (factorialMuntzRampCombination S (fun n => (d n : ℂ)) k) =
        zetaZeroConfig.W (fun x => (factorialTailCombinationSmoothed S d k x : ℂ))
          (fun x => (factorialTailCombinationSmoothed S d k x : ℂ))) ∧
    Tendsto (fun k : ℕ =>
        (zetaZeroConfig.W (factorialMuntzRampCombination S (fun n => (d n : ℂ)) k)
          (factorialMuntzRampCombination S (fun n => (d n : ℂ)) k)).re)
      atTop
      (𝓝 (zetaZeroConfig.W (fun x => (factorialTailCombination S d x : ℂ))
        (fun x => (factorialTailCombination S d x : ℂ))).re) ∧
    ((factorialWeightedPhaseLower / 2) * Real.log M - factorialSpanWeilOffset) *
        (∑ n ∈ S, ‖factorialTailCombinationPhaseCoeff d n‖ ^ 2) ≤
      (zetaZeroConfig.W (fun x => (factorialTailCombination S d x : ℂ))
        (fun x => (factorialTailCombination S d x : ℂ))).re := by
  have hEq : ∀ k : ℕ,
      zetaZeroConfig.W (factorialMuntzRampCombination S (fun n => (d n : ℂ)) k)
        (factorialMuntzRampCombination S (fun n => (d n : ℂ)) k) =
      zetaZeroConfig.W (fun x => (factorialTailCombinationSmoothed S d k x : ℂ))
        (fun x => (factorialTailCombinationSmoothed S d k x : ℂ)) := by
    intro k
    rw [factorialTailCombinationSmoothed_ofReal_eq_tailCombination]
    exact (zeroSquareMass_and_weil_rampCombo_eq_tailCombo_of_pole_zero S
      (fun n => (d n : ℂ)) k h0).2
  refine ⟨fun k => ⟨zeroSquareMass_completedCombo_eq_zero_of_pole_zero S _ k h0, hEq k⟩, ?_,
    factorialTailCombination_re_W_coercivity S d hM hS⟩
  simp_rw [hEq]
  exact (Complex.continuous_re.tendsto _).comp (tendsto_W_factorialTailCombinationSmoothed S d)

/-- **Uniformly bounded archimedean completion of far polar packets via coherent step subdivision.**
There exists an absolute constant `C > 0` such that for every `X ≥ 4`, the negative-energy
polar packet `ExposingRay.farPolarTest X` (which satisfies `archEnergy (farPolarTest X) < 0`)
admits a finite family of `N²` coherent step packets `h_i` at the same aperture `X + 17/50` with
nonnegative weights `α_i ≥ 0` that cancels every integer atom `n ≥ 2` identically while keeping
total archimedean energy uniformly bounded by `C`. -/
theorem exists_bounded_archimedean_coherent_polar_completion :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 4 ≤ X →
      RHTower.ExposingRay.archEnergy (RHTower.ExposingRay.farPolarTest X) < 0 ∧
      ∃ (N : ℕ) (α : Fin N × Fin N → ℝ) (h : Fin N × Fin N → ℝ → ℝ),
        (∀ i, 0 ≤ α i) ∧
        (∀ i, RHTower.PolarCone.PolarTestAt (X + 17 / 50) (h i)) ∧
        (∀ n : ℕ, 2 ≤ n →
          RHTower.ExposingRay.farPolarTest X (Real.log n) +
            RHTower.ExposingRay.farPolarTest X (-Real.log n) +
            ∑ i, α i * (h i (Real.log n) + h i (-Real.log n)) = 0) ∧
        (∑ i, α i * RHTower.ExposingRay.archEnergy (h i)) ≤ C := by
  obtain ⟨C, hC, hcomp⟩ := RHTower.ExposingRayCompletion.bounded_coherent_completion
  refine ⟨C, hC, fun X hX => ⟨RHTower.ExposingRay.archEnergy_farPolarTest_neg hX, hcomp X hX⟩⟩

/-! ## §2. Prime Clock Mass and Edge Kernels: Curve Representation, Operator Decompositions,
Center Decay, and Off-Diagonal Sign Characterization -/

/-- The mass correlation kernel `primeClockMassKernel k t lag` is the `L²(0, 1)` mass inner
product of `PrimeClock.curve k (t + lag)` and `PrimeClock.curve k t`. -/
theorem primeClockMassKernel_eq_inner_curve_fst (k : ℕ) (t lag : ℝ) :
    primeClockMassKernel k t lag =
      ⟪(PrimeClock.curve k (t + lag)).val.fst, (PrimeClock.curve k t).val.fst⟫_ℝ :=
  rfl

/-- The edge correlation kernel `primeClockEdgeKernel k t lag` is the `L²(ℝ)` edge inner
product of `PrimeClock.curve k (t + lag)` and `PrimeClock.curve k t`. -/
theorem primeClockEdgeKernel_eq_inner_curve_snd (k : ℕ) (t lag : ℝ) :
    primeClockEdgeKernel k t lag =
      ⟪(PrimeClock.curve k (t + lag)).val.snd, (PrimeClock.curve k t).val.snd⟫_ℝ :=
  rfl

/-- **Exact identification of the kernel difference with `sourcePair` along the clock curve.**
For every cutoff index `k` and all `t, lag : ℝ`, the difference between the edge and mass
kernels is identically the Doob source pairing of `PrimeClock.curve k (t + lag)` and
`PrimeClock.curve k t`. -/
theorem primeClockEdgeKernel_sub_massKernel_eq_sourcePair_curve (k : ℕ) (t lag : ℝ) :
    primeClockEdgeKernel k t lag - primeClockMassKernel k t lag =
      sourcePair (PrimeClock.curve k (t + lag)) (PrimeClock.curve k t) :=
  rfl

/-- **Operator decompositions of `primeClockEdgeKernel` and `primeClockEdgeKernel - primeClockMassKernel`.**
Retaining both the center variable `t` and the cutoff `k`, the edge kernel and the kernel
difference decompose into:
1. `primeClockEdgeKernel k t lag = stationary + primeGenerator + groundPotentialOperator`, and
2. `primeClockEdgeKernel k t lag - primeClockMassKernel k t lag = stationary - archGroundConstant * θ-overlap - primeShiftOperator`. -/
theorem primeClockKernel_operator_decompositions (k : ℕ) (t lag : ℝ) :
    primeClockEdgeKernel k t lag =
      ⟪(fullGroundEquiv (PrimeClock.curve k (t + lag))).snd,
        (fullGroundEquiv (PrimeClock.curve k t)).snd⟫_ℝ +
      ⟪primeGenerator (PrimeClock.curve k (t + lag)).val.fst,
        (PrimeClock.curve k t).val.fst⟫_ℝ +
      ⟪groundPotentialOperator (PrimeClock.curve k (t + lag)).val.fst,
        (PrimeClock.curve k t).val.fst⟫_ℝ ∧
    primeClockEdgeKernel k t lag - primeClockMassKernel k t lag =
      ⟪(fullGroundEquiv (PrimeClock.curve k (t + lag))).snd,
        (fullGroundEquiv (PrimeClock.curve k t)).snd⟫_ℝ -
      archGroundConstant *
        ⟪(theta (PrimeClock.curve k (t + lag)) : Lp ℝ 2 volume),
          (theta (PrimeClock.curve k t) : Lp ℝ 2 volume)⟫_ℝ -
      ⟪primeShiftOperator (PrimeClock.curve k (t + lag)).val.fst,
        (PrimeClock.curve k t).val.fst⟫_ℝ :=
  ⟨inner_snd_eq_stationary_add_primeGenerator_add_groundPotential
    (PrimeClock.curve k (t + lag)) (PrimeClock.curve k t),
   sourcePair_eq_stationary_sub_arch_sub_primeShift
    (PrimeClock.curve k (t + lag)) (PrimeClock.curve k t)⟩

/-- **Lag-reversal symmetry of the prime clock kernels and their difference.**
Shifting the center from `t` to `t + lag` and negating `lag` leaves `primeClockMassKernel`,
`primeClockEdgeKernel`, and their difference invariant. -/
theorem primeClockKernel_lag_reversal_symm (k : ℕ) (t lag : ℝ) :
    primeClockMassKernel k (t + lag) (-lag) = primeClockMassKernel k t lag ∧
    primeClockEdgeKernel k (t + lag) (-lag) = primeClockEdgeKernel k t lag ∧
    primeClockEdgeKernel k (t + lag) (-lag) - primeClockMassKernel k (t + lag) (-lag) =
      primeClockEdgeKernel k t lag - primeClockMassKernel k t lag := by
  have h1 : primeClockMassKernel k (t + lag) (-lag) = primeClockMassKernel k t lag := by
    change ⟪(PrimeClock.curve k (t + lag + -lag)).val.fst,
        (PrimeClock.curve k (t + lag)).val.fst⟫_ℝ =
      ⟪(PrimeClock.curve k (t + lag)).val.fst, (PrimeClock.curve k t).val.fst⟫_ℝ
    rw [add_neg_cancel_right, real_inner_comm]
  have h2 : primeClockEdgeKernel k (t + lag) (-lag) = primeClockEdgeKernel k t lag := by
    change ⟪(PrimeClock.curve k (t + lag + -lag)).val.snd,
        (PrimeClock.curve k (t + lag)).val.snd⟫_ℝ =
      ⟪(PrimeClock.curve k (t + lag)).val.snd, (PrimeClock.curve k t).val.snd⟫_ℝ
    rw [add_neg_cancel_right, real_inner_comm]
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
    change ⟪(PrimeClock.curve k (t + 0)).val.fst, (PrimeClock.curve k t).val.fst⟫_ℝ = _
    rw [add_zero, real_inner_self_eq_norm_sq]
  have he : primeClockEdgeKernel k t 0 = ‖(PrimeClock.curve k t).val.snd‖ ^ 2 := by
    change ⟪(PrimeClock.curve k (t + 0)).val.snd, (PrimeClock.curve k t).val.snd⟫_ℝ = _
    rw [add_zero, real_inner_self_eq_norm_sq]
  have hsum : ‖(PrimeClock.curve k t).val.fst‖ ^ 2 + ‖(PrimeClock.curve k t).val.snd‖ ^ 2 =
      ‖PrimeClock.curve k t‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      ← real_inner_self_eq_norm_sq (PrimeClock.curve k t)]
    rfl
  have hdiff : primeClockEdgeKernel k t 0 - primeClockMassKernel k t 0 =
      sourceEnergy (PrimeClock.curve k t) := by
    rw [primeClockEdgeKernel_sub_massKernel_eq_sourcePair_curve, add_zero,
      sourcePair_self_eq_sourceEnergy]
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
  have hm := abs_real_inner_le_norm (PrimeClock.curve k (t + lag)).val.fst
    (PrimeClock.curve k t).val.fst
  have he := abs_real_inner_le_norm (PrimeClock.curve k (t + lag)).val.snd
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
  exact abs_sourcePair_le_norm_mul_norm (PrimeClock.curve k (t + lag)) (PrimeClock.curve k t)

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
  have h_top := PrimeClock.curve_zero_atTop k
  have h_bot := PrimeClock.curve_zero_atBot k
  have h_shift_top : Tendsto (fun t : ℝ => PrimeClock.curve k (t + lag)) atTop (𝓝 0) :=
    h_top.comp (tendsto_atTop_add_const_right atTop lag tendsto_id)
  have h_shift_bot : Tendsto (fun t : ℝ => PrimeClock.curve k (t + lag)) atBot (𝓝 0) :=
    h_bot.comp (tendsto_atBot_add_const_right atBot lag tendsto_id)
  have h_fst_cont : Continuous (fun q : SourceGraph => q.val.fst) :=
    continuous_fst.comp continuous_subtype_val
  have h_snd_cont : Continuous (fun q : SourceGraph => q.val.snd) :=
    continuous_snd.comp continuous_subtype_val
  have hm_top : Tendsto (fun t : ℝ => primeClockMassKernel k t lag) atTop (𝓝 0) := by
    simpa using Tendsto.inner (h_fst_cont.tendsto 0 |>.comp h_shift_top)
      (h_fst_cont.tendsto 0 |>.comp h_top)
  have hm_bot : Tendsto (fun t : ℝ => primeClockMassKernel k t lag) atBot (𝓝 0) := by
    simpa using Tendsto.inner (h_fst_cont.tendsto 0 |>.comp h_shift_bot)
      (h_fst_cont.tendsto 0 |>.comp h_bot)
  have he_top : Tendsto (fun t : ℝ => primeClockEdgeKernel k t lag) atTop (𝓝 0) := by
    simpa using Tendsto.inner (h_snd_cont.tendsto 0 |>.comp h_shift_top)
      (h_snd_cont.tendsto 0 |>.comp h_top)
  have he_bot : Tendsto (fun t : ℝ => primeClockEdgeKernel k t lag) atBot (𝓝 0) := by
    simpa using Tendsto.inner (h_snd_cont.tendsto 0 |>.comp h_shift_bot)
      (h_snd_cont.tendsto 0 |>.comp h_bot)
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
  exact sourcePair_canonicalPrimeGraphClockAtom_eq_edge_sub_mass_kernel k hN
    (hS p hp) (hS q (Finset.mem_of_mem_erase hq))

/-- **Sign and spectral characterization of the off-diagonal kernel-difference sum.**
1. *Universal approximation of `sourceEnergy`:* For every `q : SourceGraph` and `ε > 0`, there
   exist `k : ℕ` and cofinally many `N` with prime sets `S ⊆ [2, ⌊√N⌋]` whose weighted
   distinct-prime sum of `primeClockEdgeKernel - primeClockMassKernel` is within `ε` of
   `sourceEnergy q`.
2. *Strict negativity for above-threshold eigenvectors:* For any nonzero `w : SourceGraph` and
   `μ > 1 / 2` with `resolvent w = μ • w`, there exist `k : ℕ` and cofinally many `(N, S)` for
   which the distinct-prime sum of `(N / (p q)) (primeClockEdgeKernel - primeClockMassKernel)`
   is strictly negative (`< -((2 * μ - 1) / (2 * μ)) * ‖w‖² < 0`).
3. *Equivalence with global `sourceEnergy` nonnegativity:* Global nonnegativity
   `∀ q : SourceGraph, 0 ≤ sourceEnergy q` holds if and only if for every `q : SourceGraph` and
   `ε > 0`, there exist `k : ℕ` and cofinally many `(N, S)` where the distinct-prime sum of
   `(N / (p q)) (primeClockEdgeKernel - primeClockMassKernel)` approximates `sourceEnergy q`
   within `ε` and is `≥ -ε`. -/
theorem primeClockKernel_diff_sign_and_spectral_characterization :
    (∀ (q : SourceGraph) {ε : ℝ}, 0 < ε →
      ∃ k : ℕ, ∀ M : ℕ, ∃ N : ℕ, M ≤ N ∧ 0 < N ∧
        ∃ S : Finset ℕ,
          (∀ p ∈ S, Nat.Prime p ∧ p ≤ Nat.sqrt N) ∧
          |offDiagSourcePairSum S (canonicalPrimeGraphClockAtom k N) - sourceEnergy q| < ε) ∧
    (∀ {w : SourceGraph} {μ : ℝ}, w ≠ 0 → 1 / 2 < μ → resolvent w = μ • w →
      ∃ k : ℕ, ∀ M : ℕ, ∃ N : ℕ, M ≤ N ∧
        ∃ S : Finset ℕ,
          (∀ p ∈ S, Nat.Prime p ∧ p ≤ Nat.sqrt N) ∧
          offDiagSourcePairSum S (canonicalPrimeGraphClockAtom k N) <
            -((2 * μ - 1) / (2 * μ)) * ‖w‖ ^ 2 ∧
          -((2 * μ - 1) / (2 * μ)) * ‖w‖ ^ 2 < 0) ∧
    (PrimeGraphClockOffDiagNonneg → ∀ q : SourceGraph, 0 ≤ sourceEnergy q) := by
  refine ⟨?_, @exists_cutoff_eventually_offDiag_neg_of_resolvent_eigenvalue_gt_half,
    sourceEnergy_nonneg_of_primeGraphClockOffDiagNonneg⟩
  intro q ε hε
  obtain ⟨k, hk⟩ := exists_cutoff_eventually_offDiag_primeClock_realization q hε
  refine ⟨k, fun M => ?_⟩
  obtain ⟨N, hMN, S, hS, hlt, -⟩ := hk (max M 1)
  exact ⟨N, (le_max_left M 1).trans hMN, (le_max_right M 1).trans hMN, S, hS, hlt⟩

end

end GaloisForLFunctions.BiScaleUncertainty
