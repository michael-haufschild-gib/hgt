import GaloisForLFunctions.RHTower.WeilFullConeOneSidedCriterion
import GaloisForLFunctions.RHTower.TwistedArcMinimumPrincipleProof
import GaloisForLFunctions.RHTower.WeilFullConeBochnerMeasure
import GaloisForLFunctions.RHTower.WeilLevyCoshPlasticCrossover
import GaloisForLFunctions.RHTower.LebesgueAtomWeilPositivity
import GaloisForLFunctions.RHTower.HerglotzProducerUniquenessUnconditional

/-!
# All-Integer Poisson Counterterm Invariance and the Bochner / Lebesgue–Atom PBAP Bridge

This module develops the **All-Integer Poisson / Mayer Counterterm Bridge** on Route HF / PBAP:

1. **Section 1 (All-Integer Counterterm Invariance on the Prime-Blind Cone, Mixture-Dependent
   Counterterm Sufficiency, and Bochner Positive-Definite Kernel Equivalence):**
   - For any weight sequence `lam : ℕ → ℝ` and Weil test `f : WeilTestFn`, we define the discrete
     all-integer counterterm
     `primeBlindCounterterm lam f = linearCombination ℝ (fun j : LogIndex => lam j) (logVector f)`.
   - On the prime-blind cone (`∀ n ≥ 2, c.sum (fun f t => t * logValue f.1 n) = 0`), adding ANY
     all-integer counterterm leaves the quadratic mixture energy identically invariant
     (`sum_primeBlindCounterterm_eq_zero_of_primeBlind`,
     `sum_weilArchRe_eq_sum_re_weilFullFunctional_of_primeBlind`).
   - Consequently (`primeBlindPositive_of_forall_exists_counterterm_nonneg`,
     `riemannHypothesis_of_forall_exists_counterterm_nonneg`), if for each nonnegative prime-blind
     mixture `c` there exists *some* counterterm sequence `lam : ℕ → ℝ` (possibly depending on `c`)
     making the counterterm-repaired energy nonnegative, then `PrimeBlindPositive` and
     `RiemannHypothesis` hold unconditionally.
   - We prove the exact Bochner positive-definite translation-kernel characterization of
     `WeilPositiveFull`, `PrimeBlindPositive`, and `RiemannHypothesis`
     (`weilPositiveFull_iff_forall_positiveDefinite_spectralKernel`,
     `primeBlindPositive_iff_exists_bochner_spectralKernel`,
     `riemannHypothesis_iff_exists_bochner_spectralKernel`).

2. **Section 2 (Counterterm Linearity, Baseline-Plus-Fluctuation Splitting, the Unit-Step Poisson
   Comb, and the Von Mangoldt Defect):**
   - We establish full linearity of `primeBlindCounterterm` in the weight sequence `lam` together
     with the explicit finite-cutoff sum formula `primeBlindCounterterm_eq_sum_Icc` over
     `Finset.Icc 2 N`.
   - Decomposing `lam = lam₀ + δ` splits `(weilFullFunctional (lam₀ + δ) (EF.weilTest f.1 f.1)).re`
     into the baseline functional minus the fluctuation counterterm `primeBlindCounterterm δ f`
     (`re_weilFullFunctional_add_counterterm`).
   - Specializing to `unitStepCountertermWeight` (`1` on `n ≥ 2`) and
     `vonMangoldtDefectCountertermWeight` (`Λ(n) - 1` on `n ≥ 2`) decomposes the canonical Weil
     functional around the unit-step Poisson comb (`re_weilFullFunctional_vonMangoldt_eq_unitStep_sub_defect`).

3. **Section 3 (Real-Space Gauss–Mode and Plastic-Crossover Lower Bounds for Counterterm-Completed
   Signed Tests):**
   - Combining `re_weilFullFunctional_eq` with `weilArchRe_eq_levy_pole`,
     `oneMode_gauss_pole_le_weilArchRe`, `twoMode_gauss_pole_le_weilArchRe`, and
     `levyCosh_crossover_add_jump_le_weilArchRe`, we obtain exact real-space lower bounds for
     `(weilFullFunctional lam (EF.weilTest f f)).re` on **all signed tests `f ∈ C²_c(ℝ)`** in which
     the discrete counterterm `primeBlindCounterterm lam` directly subtracts from the growing
     pair integral (`oneMode_gauss_pole_sub_counterterm_le_re_weilFullFunctional`,
     `twoMode_gauss_pole_sub_counterterm_le_re_weilFullFunctional`,
     `levyCosh_crossover_sub_counterterm_le_re_weilFullFunctional`).

4. **Section 4 (Continuum-vs-Discrete Pole Cancellation: Exact Bridge to the Coercive
   `lebesgueAtomWeilFunctional`):**
   - We prove the exact transfer identity between `weilFullFunctional lam` and the unconditionally
     coercive `lebesgueAtomWeilFunctional` (`re_weilFullFunctional_eq_re_lebesgueAtomWeilFunctional_add_sub_counterterm`).
   - Combining with `lebesgueAtomWeilFunctional_coercive` (`(1/100) ∫ ‖f‖² ≤ Re W_{λ₀}(f ⋆ f̃)`),
     we show that whenever a counterterm `lam : ℕ → ℝ` dominates the continuum-minus-atom defect up
     to the coercive `(1/100) ∫ ‖f‖²` margin, `WeilPositiveFull lam`, `PrimeBlindPositive`, and
     `RiemannHypothesis` hold unconditionally without any sign restriction on `f`.

5. **Section 5 (Arbitrary-Order `m`-th Cesàro Summation by Parts and the Cesàro Comparison Principle
   for `primeBlindCounterterm` and `weilFullFunctional`):**
   - Defining `countertermPrefixSum`, `countertermCesaroSum`, `countertermIteratedPrefixSum m`, and
     `iteratedForwardDiff m`, we prove that on any support cutoff `Finset.Icc 2 N` of a Weil test
     `f`, all upper boundary terms vanish at every order `m : ℕ` (`primeBlindCounterterm_eq_sum_iteratedPrefix_mul_diff`),
     giving boundary-free first-, second-, and `m`-th-order Cesàro representations on the fixed
     interval `Finset.Icc 2 N`.
   - We prove the **`m`-th Order Cesàro Comparison Principle** (`primeBlindCounterterm_le_of_iteratedPrefixSum_le`,
     `re_weilFullFunctional_le_of_iteratedPrefixSum_le`): whenever `iteratedForwardDiff m (logValue f.1) ≥ 0`
     on `Finset.Icc 2 N`, dominance of `countertermIteratedPrefixSum m lam₁ ≤ countertermIteratedPrefixSum m lam₂`
     transfers monotonically to `(weilFullFunctional lam₂).re ≤ (weilFullFunctional lam₁).re`,
     together with exact closed forms for the unit-step Poisson comb (`n - 1` and `(n - 1) n / 2`).
-/

open Complex MeasureTheory Filter Topology Set Finsupp
open scoped Real ComplexConjugate ContDiff FourierTransform
open Zeta23
open GaloisForLFunctions.RHTower
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

open WeilOneSided WeilSpectral WeilLevyPole WeilLevyPoleGauss WeilLevyCoshCrossover LebesgueAtomWeil

/-! ## Section 1: All-Integer Counterterm Invariance on the Prime-Blind Cone and Bochner Equivalence -/

/-- The discrete all-integer counterterm `∑_{n ≥ 2} lam(n) * logValue f.1 n` paired against the
finitely supported `logVector` of a Weil test `f`. -/
def primeBlindCounterterm (lam : ℕ → ℝ) (f : WeilTestFn) : ℝ :=
  linearCombination ℝ (fun j : LogIndex => lam j) (logVector f)

/-- The real part of the full Weil functional equals the archimedean + pole functional `weilArchRe`
minus the discrete all-integer counterterm `primeBlindCounterterm lam f`. -/
theorem re_weilFullFunctional_eq_weilArchRe_sub_counterterm (lam : ℕ → ℝ) (f : WeilTestFn) :
    (weilFullFunctional lam (EF.weilTest f.1 f.1)).re =
      weilArchRe (EF.weilTest f.1 f.1) - primeBlindCounterterm lam f :=
  re_weilFullFunctional_eq lam f

/-- The discrete counterterm of a mixture `c : WeilTestFn →₀ ℝ` equals the pairing of `lam` with
`linearCombination ℝ logVector c`. -/
theorem sum_primeBlindCounterterm_eq_linearCombination (lam : ℕ → ℝ) (c : WeilTestFn →₀ ℝ) :
    (c.sum fun f t => t * primeBlindCounterterm lam f) =
      linearCombination ℝ (fun j : LogIndex => lam j) (linearCombination ℝ logVector c) := by
  unfold primeBlindCounterterm
  rw [linearCombination_apply ℝ (v := logVector), map_finsuppSum]
  exact Finsupp.sum_congr fun f _ => by rw [map_smul, smul_eq_mul]

/-- Mixture expansion of `sum_re_weilFullFunctional` into `weilArchRe` minus `primeBlindCounterterm`. -/
theorem sum_re_weilFullFunctional_eq_sum_weilArchRe_sub_counterterm
    (lam : ℕ → ℝ) (c : WeilTestFn →₀ ℝ) :
    (c.sum fun f t => t * (weilFullFunctional lam (EF.weilTest f.1 f.1)).re) =
      (c.sum fun f t => t * weilArchRe (EF.weilTest f.1 f.1)) -
        (c.sum fun f t => t * primeBlindCounterterm lam f) := by
  rw [sum_re_weilFullFunctional, ← sum_weilArchRe_eq,
    ← sum_primeBlindCounterterm_eq_linearCombination]

/-- **All-Integer Counterterm Vanishing on the Prime-Blind Cone**:
for every prime-blind mixture `c` (`∀ n ≥ 2, c.sum (fun f t => t * logValue f.1 n) = 0`) and
**every** weight sequence `lam : ℕ → ℝ`, the counterterm mixture sum vanishes identically. -/
theorem sum_primeBlindCounterterm_eq_zero_of_primeBlind (lam : ℕ → ℝ) {c : WeilTestFn →₀ ℝ}
    (hnull : ∀ n : ℕ, 2 ≤ n → (c.sum fun f t => t * logValue f.1 n) = 0) :
    (c.sum fun f t => t * primeBlindCounterterm lam f) = 0 := by
  rw [sum_primeBlindCounterterm_eq_linearCombination,
    linearCombination_logVector_eq_zero hnull, map_zero]

/-- **All-Integer Counterterm Invariance on the Prime-Blind Cone**:
for every prime-blind mixture `c` and **every** weight sequence `lam : ℕ → ℝ`, the archimedean +
pole mixture energy equals the counterterm-completed functional energy. -/
theorem sum_weilArchRe_eq_sum_re_weilFullFunctional_of_primeBlind
    (lam : ℕ → ℝ) {c : WeilTestFn →₀ ℝ}
    (hnull : ∀ n : ℕ, 2 ≤ n → (c.sum fun f t => t * logValue f.1 n) = 0) :
    (c.sum fun f t => t * weilArchRe (EF.weilTest f.1 f.1)) =
      c.sum fun f t => t * (weilFullFunctional lam (EF.weilTest f.1 f.1)).re := by
  rw [sum_re_weilFullFunctional_eq_sum_weilArchRe_sub_counterterm,
    sum_primeBlindCounterterm_eq_zero_of_primeBlind lam hnull, sub_zero]

/-- **Mixture-Dependent Counterterm Sufficiency for `PrimeBlindPositive`**:
if for every nonnegative prime-blind mixture `c` there exists *some* weight sequence `lam : ℕ → ℝ`
(which may depend on `c`) such that the counterterm-completed mixture energy is nonnegative, then
`PrimeBlindPositive` holds unconditionally. -/
theorem primeBlindPositive_of_forall_exists_counterterm_nonneg
    (h : ∀ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) →
      (∀ n : ℕ, 2 ≤ n → (c.sum fun f t => t * logValue f.1 n) = 0) →
      ∃ lam : ℕ → ℝ, 0 ≤ c.sum fun f t => t * (weilFullFunctional lam (EF.weilTest f.1 f.1)).re) :
    PrimeBlindPositive := by
  intro c hc hnull
  obtain ⟨lam, hlam⟩ := h c hc hnull
  rwa [sum_weilArchRe_eq_sum_re_weilFullFunctional_of_primeBlind lam hnull]

/-- **Mixture-Dependent Counterterm Sufficiency for `RiemannHypothesis`**:
if for every nonnegative prime-blind mixture `c` there exists *some* weight sequence `lam : ℕ → ℝ`
(possibly depending on `c`) with nonnegative counterterm-completed mixture energy, then
`RiemannHypothesis` holds unconditionally. -/
theorem riemannHypothesis_of_forall_exists_counterterm_nonneg
    (h : ∀ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) →
      (∀ n : ℕ, 2 ≤ n → (c.sum fun f t => t * logValue f.1 n) = 0) →
      ∃ lam : ℕ → ℝ, 0 ≤ c.sum fun f t => t * (weilFullFunctional lam (EF.weilTest f.1 f.1)).re) :
    RiemannHypothesis :=
  riemannHypothesis_iff_primeBlindPositive_unconditional.mpr
    (primeBlindPositive_of_forall_exists_counterterm_nonneg h)

/-- Translation by `0` is the identity on test functions. -/
theorem transl_zero (k : ℝ → ℂ) : transl 0 k = k := by
  funext x
  simp [transl]

/-- Evaluating `spectralKernel lam f` at `0` recovers `weilFullFunctional lam (EF.weilTest f f)`. -/
theorem spectralKernel_zero (lam : ℕ → ℝ) (f : ℝ → ℂ) :
    spectralKernel lam f 0 = weilFullFunctional lam (EF.weilTest f f) := by
  rw [spectralKernel, transl_zero]

/-- **Bochner Positive-Definite Characterization of `WeilPositiveFull`**:
a weight sequence `lam : ℕ → ℝ` is full-cone Weil-positive (on all signed `f ∈ C²_c(ℝ)`) if and
only if its translation kernel `spectralKernel lam f` is Bochner positive-definite on `ℝ` for
every `f ∈ C²_c(ℝ)`. -/
theorem weilPositiveFull_iff_forall_positiveDefinite_spectralKernel (lam : ℕ → ℝ) :
    WeilPositiveFull lam ↔
      ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
        PositiveDefiniteOnReal (spectralKernel lam f) := by
  constructor
  · exact fun hW f hf hfc => positiveDefinite_spectralKernel hW hf hfc
  · intro hPD f hf hfc
    have h0 := (hPD f hf hfc).zero.1
    rwa [spectralKernel_zero] at h0

/-- **Bochner Measure Characterization of `WeilPositiveFull`**:
`lam` is full-cone Weil-positive if and only if for every `f ∈ C²_c(ℝ)`, `spectralKernel lam f`
is the characteristic function of a finite positive measure on `ℝ`. -/
theorem weilPositiveFull_iff_forall_exists_spectralMeasure (lam : ℕ → ℝ) :
    WeilPositiveFull lam ↔
      ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
        ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧ ∀ y, charFun ν y = spectralKernel lam f y := by
  constructor
  · exact fun hW f hf hfc => exists_spectralMeasure hW hf hfc
  · intro hM f hf hfc
    obtain ⟨ν, _, hν⟩ := hM f hf hfc
    have h0 := hν 0
    rw [charFun_apply_real, spectralKernel_zero] at h0
    have h1 : (∫ x : ℝ, cexp (↑(0 : ℝ) * ↑x * I) ∂ν) = ((ν univ).toReal : ℂ) := by
      simp [Measure.real]
    rw [← h0, h1, Complex.ofReal_re]
    exact ENNReal.toReal_nonneg

/-- **All-Integer Counterterm Bochner Equivalence for `PrimeBlindPositive`**:
`PrimeBlindPositive` holds if and only if there exists an all-integer counterterm sequence
`lam : ℕ → ℝ` such that `spectralKernel lam f` is Bochner positive-definite for all signed
`f ∈ C²_c(ℝ)`. -/
theorem primeBlindPositive_iff_exists_bochner_spectralKernel :
    PrimeBlindPositive ↔
      ∃ lam : ℕ → ℝ, ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
        PositiveDefiniteOnReal (spectralKernel lam f) := by
  rw [← exists_weilPositiveFull_iff_primeBlindPositive]
  exact exists_congr fun lam => weilPositiveFull_iff_forall_positiveDefinite_spectralKernel lam

/-- **All-Integer Counterterm Bochner Equivalence for `RiemannHypothesis`**:
`RiemannHypothesis` holds if and only if there exists an all-integer counterterm sequence
`lam : ℕ → ℝ` such that `spectralKernel lam f` is Bochner positive-definite for all signed
`f ∈ C²_c(ℝ)` (and any such `lam` equals `Λ` on `n ≥ 2`). -/
theorem riemannHypothesis_iff_exists_bochner_spectralKernel :
    RiemannHypothesis ↔
      ∃ lam : ℕ → ℝ, ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
        PositiveDefiniteOnReal (spectralKernel lam f) := by
  rw [riemannHypothesis_iff_primeBlindPositive_unconditional,
    primeBlindPositive_iff_exists_bochner_spectralKernel]

/-! ## Section 2: Counterterm Linearity, Baseline-Plus-Fluctuation Splitting, and the Unit-Step Poisson Comb -/

/-- `primeBlindCounterterm` depends only on the values of `lam` at integers `n ≥ 2`. -/
theorem primeBlindCounterterm_congr {lam₁ lam₂ : ℕ → ℝ}
    (h : ∀ n : ℕ, 2 ≤ n → lam₁ n = lam₂ n) (f : WeilTestFn) :
    primeBlindCounterterm lam₁ f = primeBlindCounterterm lam₂ f := by
  unfold primeBlindCounterterm
  have hfun : (fun j : LogIndex => lam₁ j) = (fun j : LogIndex => lam₂ j) :=
    funext fun j => h j.1 j.2
  rw [hfun]

/-- The zero weight sequence gives zero counterterm. -/
theorem primeBlindCounterterm_zero (f : WeilTestFn) :
    primeBlindCounterterm 0 f = 0 := by
  unfold primeBlindCounterterm
  rw [linearCombination_apply]
  simp

/-- Additivity of `primeBlindCounterterm` in the weight sequence `lam`. -/
theorem primeBlindCounterterm_add (lam₁ lam₂ : ℕ → ℝ) (f : WeilTestFn) :
    primeBlindCounterterm (lam₁ + lam₂) f =
      primeBlindCounterterm lam₁ f + primeBlindCounterterm lam₂ f := by
  unfold primeBlindCounterterm
  rw [linearCombination_apply, linearCombination_apply, linearCombination_apply, ← Finsupp.sum_add]
  exact Finsupp.sum_congr fun j _ => by simp [Pi.add_apply, mul_add]

/-- Negation of `primeBlindCounterterm` in the weight sequence `lam`. -/
theorem primeBlindCounterterm_neg (lam : ℕ → ℝ) (f : WeilTestFn) :
    primeBlindCounterterm (-lam) f = -primeBlindCounterterm lam f := by
  unfold primeBlindCounterterm
  rw [linearCombination_apply, linearCombination_apply, ← Finsupp.sum_neg]
  exact Finsupp.sum_congr fun j _ => by simp [Pi.neg_apply]

/-- Subtraction of `primeBlindCounterterm` in the weight sequence `lam`. -/
theorem primeBlindCounterterm_sub (lam₁ lam₂ : ℕ → ℝ) (f : WeilTestFn) :
    primeBlindCounterterm (lam₁ - lam₂) f =
      primeBlindCounterterm lam₁ f - primeBlindCounterterm lam₂ f := by
  rw [sub_eq_add_neg, primeBlindCounterterm_add, primeBlindCounterterm_neg, sub_eq_add_neg]

/-- Scalar multiplication of `primeBlindCounterterm` in the weight sequence `lam`. -/
theorem primeBlindCounterterm_smul (a : ℝ) (lam : ℕ → ℝ) (f : WeilTestFn) :
    primeBlindCounterterm (a • lam) f = a * primeBlindCounterterm lam f := by
  unfold primeBlindCounterterm
  rw [linearCombination_apply, linearCombination_apply, Finsupp.mul_sum]
  exact Finsupp.sum_congr fun j _ => by simp [Pi.smul_apply, smul_eq_mul, mul_left_comm]

/-- Explicit finite-cutoff formula for `primeBlindCounterterm lam f`: if `EF.weilTest f.1 f.1`
vanishes at `±log n` for all `n > N`, then `primeBlindCounterterm lam f` is the finite sum over
`n ∈ Finset.Icc 2 N`. -/
theorem primeBlindCounterterm_eq_sum_Icc (lam : ℕ → ℝ) (f : WeilTestFn) {N : ℕ}
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0) :
    primeBlindCounterterm lam f = ∑ n ∈ Finset.Icc 2 N, lam n * logValue f.1 n := by
  classical
  unfold primeBlindCounterterm
  rw [linearCombination_apply]
  have hsub : (logVector f).support ⊆ (Finset.Icc 2 N).subtype (fun n => 2 ≤ n) := by
    intro j hj
    rw [Finsupp.mem_support_iff, logVector_apply] at hj
    rw [Finset.mem_subtype, Finset.mem_Icc]
    refine ⟨j.2, ?_⟩
    by_contra hlt
    rw [not_le] at hlt
    apply hj
    have h0 := hN j hlt
    simp [logValue, h0.1, h0.2]
  rw [Finsupp.sum_of_support_subset (logVector f) hsub (fun j a => a • lam j)
    (fun _ _ => zero_smul _ _)]
  have hcongr : (∑ j ∈ (Finset.Icc 2 N).subtype (fun n => 2 ≤ n), logVector f j • lam j) =
      ∑ j ∈ (Finset.Icc 2 N).subtype (fun n => 2 ≤ n), lam j * logValue f.1 j :=
    Finset.sum_congr rfl fun j _ => by rw [logVector_apply, smul_eq_mul, mul_comm]
  rw [hcongr, Finset.sum_subtype_eq_sum_filter (fun n => lam n * logValue f.1 n),
    Finset.filter_eq_self.mpr (fun n hn => (Finset.mem_Icc.mp hn).1)]

/-- **Baseline-Plus-Fluctuation Counterterm Splitting**:
decomposing a counterterm weight sequence as `lam₀ + δ` splits the real part of the Weil functional
into the baseline functional `(weilFullFunctional lam₀).re` minus `primeBlindCounterterm δ f`. -/
theorem re_weilFullFunctional_add_counterterm (lam₀ δ : ℕ → ℝ) (f : WeilTestFn) :
    (weilFullFunctional (lam₀ + δ) (EF.weilTest f.1 f.1)).re =
      (weilFullFunctional lam₀ (EF.weilTest f.1 f.1)).re - primeBlindCounterterm δ f := by
  rw [re_weilFullFunctional_eq_weilArchRe_sub_counterterm,
    re_weilFullFunctional_eq_weilArchRe_sub_counterterm,
    primeBlindCounterterm_add]
  ring

/-- Subtraction form of baseline-plus-fluctuation counterterm splitting. -/
theorem re_weilFullFunctional_sub_counterterm (lam₀ δ : ℕ → ℝ) (f : WeilTestFn) :
    (weilFullFunctional (lam₀ - δ) (EF.weilTest f.1 f.1)).re =
      (weilFullFunctional lam₀ (EF.weilTest f.1 f.1)).re + primeBlindCounterterm δ f := by
  rw [re_weilFullFunctional_eq_weilArchRe_sub_counterterm,
    re_weilFullFunctional_eq_weilArchRe_sub_counterterm,
    primeBlindCounterterm_sub]
  ring

/-- The **Unit-Step Poisson Comb Weight** (`1` for `n ≥ 2` and `0` for `n < 2`), whose Dirichlet
series on `Re s > 1` is `ζ(s) − 1`, matching the `1 / (s − 1)` pole of `weilFunction`. -/
def unitStepCountertermWeight (n : ℕ) : ℝ :=
  if 2 ≤ n then 1 else 0

/-- The **Von Mangoldt Defect Weight** (`Λ(n) − 1` for `n ≥ 2` and `0` for `n < 2`), whose partial
sums are `ψ(N) − (N − 1) = psiRemainder N`. -/
def vonMangoldtDefectCountertermWeight (n : ℕ) : ℝ :=
  if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ) - 1 else 0

/-- Pointwise decomposition `Λ(n) = unitStepCountertermWeight n + vonMangoldtDefectCountertermWeight n`
for all `n : ℕ`. -/
theorem vonMangoldt_eq_unitStep_add_defect (n : ℕ) :
    (ArithmeticFunction.vonMangoldt n : ℝ) =
      unitStepCountertermWeight n + vonMangoldtDefectCountertermWeight n := by
  unfold unitStepCountertermWeight vonMangoldtDefectCountertermWeight
  by_cases hn : 2 ≤ n
  · simp [hn]
  · rw [if_neg hn, if_neg hn, add_zero, vonMangoldt_eq_zero_of_lt_two (by omega)]

/-- Decomposition of the von Mangoldt counterterm into the unit-step Poisson comb plus the
von Mangoldt defect counterterm. -/
theorem primeBlindCounterterm_vonMangoldt_eq_unitStep_add_defect (f : WeilTestFn) :
    primeBlindCounterterm (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) f =
      primeBlindCounterterm unitStepCountertermWeight f +
        primeBlindCounterterm vonMangoldtDefectCountertermWeight f := by
  have heq : (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) =
      unitStepCountertermWeight + vonMangoldtDefectCountertermWeight :=
    funext vonMangoldt_eq_unitStep_add_defect
  rw [heq, primeBlindCounterterm_add]

/-- **Poisson-Comb / Von-Mangoldt-Defect Splitting of the Canonical Weil Functional**:
for every `f : WeilTestFn`, the canonical Weil functional `(weilFullFunctional Λ).re` equals the
unit-step Poisson-comb functional `(weilFullFunctional unitStepCountertermWeight).re` minus the
von Mangoldt defect counterterm `primeBlindCounterterm vonMangoldtDefectCountertermWeight f`. -/
theorem re_weilFullFunctional_vonMangoldt_eq_unitStep_sub_defect (f : WeilTestFn) :
    (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      (EF.weilTest f.1 f.1)).re =
      (weilFullFunctional unitStepCountertermWeight (EF.weilTest f.1 f.1)).re -
        primeBlindCounterterm vonMangoldtDefectCountertermWeight f := by
  have heq : (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) =
      unitStepCountertermWeight + vonMangoldtDefectCountertermWeight :=
    funext vonMangoldt_eq_unitStep_add_defect
  rw [heq, re_weilFullFunctional_add_counterterm]

/-! ## Section 3: Real-Space Gauss–Mode and Plastic-Crossover Lower Bounds for Counterterm-Completed Signed Tests -/

/-- Canonical embedding of a real-valued `C²` compactly supported test `f : ℝ → ℝ` into
`WeilTestFn`. -/
def realWeilTestFn (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) : WeilTestFn :=
  ⟨fun u => (f u : ℂ), ofRealCLM.contDiff.comp hf, hfc.comp_left Complex.ofReal_zero⟩

/-- **Exact Real-Space Lévy–Pole–Counterterm Identity for Signed Real Tests**:
for every `f ∈ C²_c(ℝ)` and every counterterm sequence `lam : ℕ → ℝ`, `(weilFullFunctional lam).re`
splits into the point term `A(0) ∫ f²`, the nonnegative Lévy jump integral, and the `2 cosh` pole
pair integral minus `primeBlindCounterterm lam`. -/
theorem re_weilFullFunctional_eq_levy_pole_sub_counterterm (lam : ℕ → ℝ) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    (weilFullFunctional lam (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re =
      EF.gammaBracket 0 * (∫ u : ℝ, f u ^ 2) +
        (∫⁻ x in Ioi (0 : ℝ),
          ENNReal.ofReal (archLevyDensity x * ∫ u : ℝ, (f u - f (u + x)) ^ 2)).toReal +
        2 * (∫ p : ℝ × ℝ, f p.1 * f p.2 * Real.cosh ((p.1 - p.2) / 2)) -
        primeBlindCounterterm lam (realWeilTestFn f hf hfc) := by
  have h := re_weilFullFunctional_eq_weilArchRe_sub_counterterm lam (realWeilTestFn f hf hfc)
  change (weilFullFunctional lam (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re =
    weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) -
      primeBlindCounterterm lam (realWeilTestFn f hf hfc) at h
  rw [h, weilArchRe_eq_levy_pole hf hfc]

/-- **One-Mode Gauss–Pole–Counterterm Lower Bound (All Signed `f ∈ C²_c(ℝ)`)**:
after absorbing the `m = 0` Gauss mode `e^{-|u-v|/2}` into the decaying half of `2 cosh((u-v)/2)`,
the counterterm `primeBlindCounterterm lam` pairs directly against the growing exponential kernel
`∫∫ f(u) f(v) e^{|u-v|/2} du dv`. -/
theorem oneMode_gauss_pole_sub_counterterm_le_re_weilFullFunctional (lam : ℕ → ℝ) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    (EF.gammaBracket 0 + 4) * (∫ u, f u ^ 2) +
        ((∫ p : ℝ × ℝ, f p.1 * f p.2 * Real.exp (|p.1 - p.2| / 2)) -
          primeBlindCounterterm lam (realWeilTestFn f hf hfc)) ≤
      (weilFullFunctional lam (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re := by
  have h1 := oneMode_gauss_pole_le_weilArchRe hf hfc
  have h2 := re_weilFullFunctional_eq_weilArchRe_sub_counterterm lam (realWeilTestFn f hf hfc)
  change (weilFullFunctional lam (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re =
    weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) -
      primeBlindCounterterm lam (realWeilTestFn f hf hfc) at h2
  linarith

/-- **Two-Mode Gauss–Pole–Counterterm Lower Bound (All Signed `f ∈ C²_c(ℝ)`)**:
retaining the `m = 0` and `m = 1` Gauss modes raises the `L²` potential to `A(0) + 24/5 > 0`
while pairing the counterterm against `∫∫ f(u) f(v) (e^{|u-v|/2} - e^{-5|u-v|/2}) du dv`. -/
theorem twoMode_gauss_pole_sub_counterterm_le_re_weilFullFunctional (lam : ℕ → ℝ) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    (EF.gammaBracket 0 + 24 / 5) * (∫ u, f u ^ 2) +
        ((∫ p : ℝ × ℝ, f p.1 * f p.2 *
          (Real.exp (|p.1 - p.2| / 2) - Real.exp (-5 * |p.1 - p.2| / 2))) -
          primeBlindCounterterm lam (realWeilTestFn f hf hfc)) ≤
      (weilFullFunctional lam (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re := by
  have h1 := twoMode_gauss_pole_le_weilArchRe hf hfc
  have h2 := re_weilFullFunctional_eq_weilArchRe_sub_counterterm lam (realWeilTestFn f hf hfc)
  change (weilFullFunctional lam (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re =
    weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) -
      primeBlindCounterterm lam (realWeilTestFn f hf hfc) at h2
  linarith

/-- **Master Plastic Lévy–Cosh Crossover–Counterterm Lower Bound (All Signed `f ∈ C²_c(ℝ)`)**:
for any `0 < δ ≤ c ≤ screwSignThreshold`, the pair kernel `2 cosh((u-v)/2) - levyCoshKernel c |u-v|`
vanishes identically on `|u - v| ≤ c`, so the counterterm `primeBlindCounterterm lam` only needs to
control pairs at distance `|u - v| > c` up to the positive `L²` floor `(A(0) + levyCoshPotential c) ∫ f²`
and short-jump energy on `(δ, c)`. -/
theorem levyCosh_crossover_sub_counterterm_le_re_weilFullFunctional (lam : ℕ → ℝ) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {δ c : ℝ} (hδ : 0 < δ) (hδc : δ ≤ c)
    (hct : c ≤ screwSignThreshold) :
    (EF.gammaBracket 0 + levyCoshPotential c) * (∫ u, f u ^ 2) +
        (∫ x in Ioo δ c, (-screwRegularKernel x) * (∫ u, (f u - f (u + x)) ^ 2)) +
        ((∫ p : ℝ × ℝ, f p.1 * f p.2 *
          (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel c |p.1 - p.2|)) -
          primeBlindCounterterm lam (realWeilTestFn f hf hfc)) ≤
      (weilFullFunctional lam (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re := by
  have h1 := levyCosh_crossover_add_jump_le_weilArchRe hf hfc hδ hδc hct
  have h2 := re_weilFullFunctional_eq_weilArchRe_sub_counterterm lam (realWeilTestFn f hf hfc)
  change (weilFullFunctional lam (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re =
    weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) -
      primeBlindCounterterm lam (realWeilTestFn f hf hfc) at h2
  linarith

/-- **Signed-Test Positivity from Plastic-Crossover Counterterm Domination**:
for any signed real test `f ∈ C²_c(ℝ)` and `0 < δ ≤ c ≤ screwSignThreshold`, if the discrete
counterterm `primeBlindCounterterm lam` is bounded above by the plastic-crossover pair integral
plus the `L²` and jump-energy floors, then `0 ≤ (weilFullFunctional lam (EF.weilTest f f)).re`. -/
theorem re_weilFullFunctional_nonneg_of_levyCosh_counterterm_le (lam : ℕ → ℝ) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {δ c : ℝ} (hδ : 0 < δ) (hδc : δ ≤ c)
    (hct : c ≤ screwSignThreshold)
    (hdom : primeBlindCounterterm lam (realWeilTestFn f hf hfc) ≤
      (EF.gammaBracket 0 + levyCoshPotential c) * (∫ u, f u ^ 2) +
        (∫ x in Ioo δ c, (-screwRegularKernel x) * (∫ u, (f u - f (u + x)) ^ 2)) +
        (∫ p : ℝ × ℝ, f p.1 * f p.2 *
          (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel c |p.1 - p.2|))) :
    0 ≤ (weilFullFunctional lam (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re := by
  have h := levyCosh_crossover_sub_counterterm_le_re_weilFullFunctional lam hf hfc hδ hδc hct
  linarith

/-! ## Section 4: Continuum-vs-Discrete Pole Cancellation: Exact Bridge to the Coercive `lebesgueAtomWeilFunctional` -/

/-- Exact decomposition of `weilArchRe k` into `(weilMeasureFunctional νp νm k).re` plus the
signed measure integral of `primeIntegrand k`. -/
theorem weilArchRe_eq_re_weilMeasureFunctional_add (νp νm : Measure ℝ) (k : ℝ → ℂ) :
    weilArchRe k =
      (weilMeasureFunctional νp νm k).re +
        ((∫ x, primeIntegrand k x ∂νp) - ∫ x, primeIntegrand k x ∂νm).re := by
  unfold weilArchRe weilMeasureFunctional
  simp only [Complex.add_re, Complex.sub_re]
  ring

/-- Exact decomposition of `weilArchRe k` into `(lebesgueAtomWeilFunctional k).re` plus the
continuum-minus-atom integral `∫_{(1,∞)} x^{-1/2} (k(log x) + k(-log x)) dx - (k(1/10000) + k(-1/10000))`. -/
theorem weilArchRe_eq_re_lebesgueAtomWeilFunctional_add (k : ℝ → ℂ) :
    weilArchRe k =
      (lebesgueAtomWeilFunctional k).re +
        ((∫ x, primeIntegrand k x ∂lebesguePart) -
          (k (1 / 10000) + k (-(1 / 10000)))).re := by
  rw [lebesgueAtomWeilFunctional, weilArchRe_eq_re_weilMeasureFunctional_add lebesguePart atomPart,
    integral_atomPart]

/-- **Exact Lebesgue–Atom / Integer-Counterterm Transfer Identity**:
for every `f : WeilTestFn` and every counterterm sequence `lam : ℕ → ℝ`, the real part of the full
Weil functional `(weilFullFunctional lam (EF.weilTest f.1 f.1)).re` equals the unconditionally
coercive `(lebesgueAtomWeilFunctional (EF.weilTest f.1 f.1)).re` plus the continuum-minus-atom
quadrature difference against `primeBlindCounterterm lam f`. -/
theorem re_weilFullFunctional_eq_re_lebesgueAtomWeilFunctional_add_sub_counterterm
    (lam : ℕ → ℝ) (f : WeilTestFn) :
    (weilFullFunctional lam (EF.weilTest f.1 f.1)).re =
      (lebesgueAtomWeilFunctional (EF.weilTest f.1 f.1)).re +
        (((∫ x, primeIntegrand (EF.weilTest f.1 f.1) x ∂lebesguePart) -
          (EF.weilTest f.1 f.1 (1 / 10000) + EF.weilTest f.1 f.1 (-(1 / 10000)))).re -
          primeBlindCounterterm lam f) := by
  rw [re_weilFullFunctional_eq_weilArchRe_sub_counterterm,
    weilArchRe_eq_re_lebesgueAtomWeilFunctional_add]
  ring

/-- **Coercive Continuum-vs-Discrete Lower Bound for `(weilFullFunctional lam).re`**:
for every signed test `f : WeilTestFn` and every counterterm weight `lam : ℕ → ℝ`,
`(1 / 100) * ∫ ‖f‖² + ((∫_{(1,∞)} primeIntegrand k_f d(lebesguePart) - (k_f(1/10000) + k_f(-1/10000))).re - primeBlindCounterterm lam f) ≤ (weilFullFunctional lam k_f).re`. -/
theorem one_hundredth_l2_add_continuum_sub_counterterm_le_re_weilFullFunctional
    (lam : ℕ → ℝ) (f : WeilTestFn) :
    (1 / 100) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) +
        (((∫ x, primeIntegrand (EF.weilTest f.1 f.1) x ∂lebesguePart) -
          (EF.weilTest f.1 f.1 (1 / 10000) + EF.weilTest f.1 f.1 (-(1 / 10000)))).re -
          primeBlindCounterterm lam f) ≤
      (weilFullFunctional lam (EF.weilTest f.1 f.1)).re := by
  have hcoerc := lebesgueAtomWeilFunctional_coercive f.2.1 f.2.2
  have htrans := re_weilFullFunctional_eq_re_lebesgueAtomWeilFunctional_add_sub_counterterm lam f
  linarith

/-- **Pointwise Signed-Test Positivity from Continuum-Plus-Coercive Counterterm Domination**:
for any `f : WeilTestFn` (without any sign or support restriction on `f`), if the discrete
counterterm `primeBlindCounterterm lam f` is bounded above by the continuum-minus-atom integral
plus `(1 / 100) * ∫ ‖f‖²`, then `0 ≤ (weilFullFunctional lam (EF.weilTest f.1 f.1)).re`. -/
theorem re_weilFullFunctional_nonneg_of_counterterm_le_continuum_add_coercive
    (lam : ℕ → ℝ) (f : WeilTestFn)
    (hdom : primeBlindCounterterm lam f ≤
      ((∫ x, primeIntegrand (EF.weilTest f.1 f.1) x ∂lebesguePart) -
        (EF.weilTest f.1 f.1 (1 / 10000) + EF.weilTest f.1 f.1 (-(1 / 10000)))).re +
        (1 / 100) * (∫ u : ℝ, ‖f.1 u‖ ^ 2)) :
    0 ≤ (weilFullFunctional lam (EF.weilTest f.1 f.1)).re := by
  have h := one_hundredth_l2_add_continuum_sub_counterterm_le_re_weilFullFunctional lam f
  linarith

/-- **Global `WeilPositiveFull` from Continuum-Plus-Coercive Counterterm Domination**:
if `lam : ℕ → ℝ` satisfies the continuum-plus-coercive upper bound for all `f : WeilTestFn`, then
`WeilPositiveFull lam` holds unconditionally. -/
theorem weilPositiveFull_of_counterterm_le_continuum_add_coercive {lam : ℕ → ℝ}
    (hdom : ∀ f : WeilTestFn,
      primeBlindCounterterm lam f ≤
        ((∫ x, primeIntegrand (EF.weilTest f.1 f.1) x ∂lebesguePart) -
          (EF.weilTest f.1 f.1 (1 / 10000) + EF.weilTest f.1 f.1 (-(1 / 10000)))).re +
          (1 / 100) * (∫ u : ℝ, ‖f.1 u‖ ^ 2)) :
    WeilPositiveFull lam :=
  fun f hf hfc => re_weilFullFunctional_nonneg_of_counterterm_le_continuum_add_coercive
    lam ⟨f, hf, hfc⟩ (hdom ⟨f, hf, hfc⟩)

/-- **Unconditional `RiemannHypothesis` and Von-Mangoldt Rigidity from Continuum-Plus-Coercive
Counterterm Domination**:
if there exists ANY counterterm sequence `lam : ℕ → ℝ` whose discrete sum `primeBlindCounterterm lam f`
is bounded above by the continuum-minus-atom integral plus `(1 / 100) * ∫ ‖f‖²` for every
`f : WeilTestFn`, then `RiemannHypothesis` holds unconditionally and `lam n = Λ(n)` for all `n ≥ 2`. -/
theorem riemannHypothesis_of_exists_counterterm_le_continuum_add_coercive
    (h : ∃ lam : ℕ → ℝ, ∀ f : WeilTestFn,
      primeBlindCounterterm lam f ≤
        ((∫ x, primeIntegrand (EF.weilTest f.1 f.1) x ∂lebesguePart) -
          (EF.weilTest f.1 f.1 (1 / 10000) + EF.weilTest f.1 f.1 (-(1 / 10000)))).re +
          (1 / 100) * (∫ u : ℝ, ‖f.1 u‖ ^ 2)) :
    RiemannHypothesis ∧
      ∃ lam : ℕ → ℝ, WeilPositiveFull lam ∧
        ∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  obtain ⟨lam, hdom⟩ := h
  have hW : WeilPositiveFull lam := weilPositiveFull_of_counterterm_le_continuum_add_coercive hdom
  obtain ⟨hRH, heq⟩ := weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt.mp hW
  exact ⟨hRH, lam, hW, heq⟩

/-! ## Section 5: Arbitrary-Order `m`-th Cesàro Summation by Parts and the Cesàro Comparison Principle -/

/-- The prefix sum `∑_{m = 2}^n lam(m)` of a counterterm weight sequence `lam : ℕ → ℝ`. -/
def countertermPrefixSum (lam : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 2 n, lam m

/-- The second-order (Cesàro) prefix sum `∑_{m = 2}^n countertermPrefixSum lam m`. -/
def countertermCesaroSum (lam : ℕ → ℝ) (n : ℕ) : ℝ :=
  countertermPrefixSum (countertermPrefixSum lam) n

/-- The `m`-th iterated prefix sum of a counterterm weight sequence `lam : ℕ → ℝ` on `[2, n]`. -/
def countertermIteratedPrefixSum : ℕ → (ℕ → ℝ) → ℕ → ℝ
  | 0, lam => lam
  | m + 1, lam => countertermPrefixSum (countertermIteratedPrefixSum m lam)

/-- The `m`-th forward difference `(Δ^m g)(n)` of a sequence `g : ℕ → ℝ`, with
`(Δ g)(n) = g n - g (n + 1)`. -/
def iteratedForwardDiff : ℕ → (ℕ → ℝ) → ℕ → ℝ
  | 0, g => g
  | m + 1, g => fun n => iteratedForwardDiff m g n - iteratedForwardDiff m g (n + 1)

@[simp]
theorem countertermPrefixSum_zero (lam : ℕ → ℝ) : countertermPrefixSum lam 0 = 0 := by
  simp [countertermPrefixSum]

@[simp]
theorem countertermPrefixSum_one (lam : ℕ → ℝ) : countertermPrefixSum lam 1 = 0 := by
  simp [countertermPrefixSum]

theorem countertermPrefixSum_succ_of_one_le (lam : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) :
    countertermPrefixSum lam (n + 1) = countertermPrefixSum lam n + lam (n + 1) := by
  unfold countertermPrefixSum
  exact Finset.sum_Icc_succ_top (by omega) lam

theorem countertermPrefixSum_add (lam₁ lam₂ : ℕ → ℝ) (n : ℕ) :
    countertermPrefixSum (lam₁ + lam₂) n =
      countertermPrefixSum lam₁ n + countertermPrefixSum lam₂ n := by
  unfold countertermPrefixSum
  simp [Pi.add_apply, Finset.sum_add_distrib]

theorem countertermPrefixSum_sub (lam₁ lam₂ : ℕ → ℝ) (n : ℕ) :
    countertermPrefixSum (lam₁ - lam₂) n =
      countertermPrefixSum lam₁ n - countertermPrefixSum lam₂ n := by
  unfold countertermPrefixSum
  simp [Pi.sub_apply, Finset.sum_sub_distrib]

/-- Exact linear closed form for the prefix sum of `unitStepCountertermWeight`:
for all `n ≥ 1`, `countertermPrefixSum unitStepCountertermWeight n = n - 1`. -/
theorem countertermPrefixSum_unitStep_of_one_le {n : ℕ} (hn : 1 ≤ n) :
    countertermPrefixSum unitStepCountertermWeight n = (n : ℝ) - 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => simp
  | succ k ih =>
    have hk1 : 1 ≤ 1 + k := by omega
    have hstep := countertermPrefixSum_succ_of_one_le unitStepCountertermWeight hk1
    have hu : unitStepCountertermWeight (1 + k + 1) = 1 := by
      unfold unitStepCountertermWeight
      exact if_pos (by omega)
    rw [show 1 + (k + 1) = 1 + k + 1 by omega, hstep, hu, ih hk1]
    push_cast
    ring

/-- Exact quadratic closed form for the Cesàro sum of `unitStepCountertermWeight`:
for all `n ≥ 1`, `countertermCesaroSum unitStepCountertermWeight n = (n - 1) * n / 2`. -/
theorem countertermCesaroSum_unitStep_of_one_le {n : ℕ} (hn : 1 ≤ n) :
    countertermCesaroSum unitStepCountertermWeight n = ((n : ℝ) - 1) * (n : ℝ) / 2 := by
  unfold countertermCesaroSum
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => simp
  | succ k ih =>
    have hk1 : 1 ≤ 1 + k := by omega
    have hk2 : 1 ≤ 1 + k + 1 := by omega
    have hstep := countertermPrefixSum_succ_of_one_le
      (countertermPrefixSum unitStepCountertermWeight) hk1
    rw [show 1 + (k + 1) = 1 + k + 1 by omega, hstep, ih hk1,
      countertermPrefixSum_unitStep_of_one_le hk2]
    push_cast
    ring

/-- **Universal Finite Summation by Parts on `Finset.Icc 2 N` for `countertermPrefixSum`**:
for any sequences `lam g : ℕ → ℝ` and any `N : ℕ`,
`∑ n ∈ Finset.Icc 2 N, lam n * g n = countertermPrefixSum lam N * g (N + 1) + ∑ n ∈ Finset.Icc 2 N, countertermPrefixSum lam n * (g n - g (n + 1))`. -/
theorem sum_Icc_mul_eq_countertermPrefixSum_abel (lam g : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 2 N, lam n * g n) =
      countertermPrefixSum lam N * g (N + 1) +
        ∑ n ∈ Finset.Icc 2 N, countertermPrefixSum lam n * (g n - g (n + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    · have h2 : 2 ≤ N + 1 := by omega
      rw [Finset.sum_Icc_succ_top h2, Finset.sum_Icc_succ_top h2,
        countertermPrefixSum_succ_of_one_le lam hN, ih]
      ring

/-- If `g n = 0` for all `n > N`, then `iteratedForwardDiff m g n = 0` for every order `m : ℕ`
and every `n > N`. -/
theorem iteratedForwardDiff_eq_zero_of_gt (m : ℕ) {g : ℕ → ℝ} {N : ℕ}
    (hN : ∀ n : ℕ, N < n → g n = 0) {n : ℕ} (hn : N < n) :
    iteratedForwardDiff m g n = 0 := by
  induction m generalizing n with
  | zero => exact hN n hn
  | succ m ih =>
    unfold iteratedForwardDiff
    rw [ih hn, ih (by omega : N < n + 1), sub_zero]

/-- If `EF.weilTest f.1 f.1` vanishes at `±log n` for `n > N`, then `logValue f.1 n = 0` for
all `n > N`. -/
theorem logValue_eq_zero_of_gt {f : WeilTestFn} {N n : ℕ}
    (hN : ∀ m : ℕ, N < m →
      EF.weilTest f.1 f.1 (Real.log m) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log m) = 0)
    (hn : N < n) :
    logValue f.1 n = 0 := by
  have h0 := hN n hn
  simp [logValue, h0.1, h0.2]

/-- **Boundary-Free `m`-th Order Iterated Cesàro Identity for `primeBlindCounterterm`**:
for EVERY order `m : ℕ` and any support cutoff `N` of `EF.weilTest f.1 f.1`, all upper boundary
terms at `N + 1` vanish identically and `primeBlindCounterterm lam f` equals the pairing of
`countertermIteratedPrefixSum m lam` with `iteratedForwardDiff m (logValue f.1)` on the fixed
interval `Finset.Icc 2 N`. -/
theorem primeBlindCounterterm_eq_sum_iteratedPrefix_mul_diff (m : ℕ) (lam : ℕ → ℝ) (f : WeilTestFn)
    {N : ℕ}
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0) :
    primeBlindCounterterm lam f =
      ∑ n ∈ Finset.Icc 2 N,
        countertermIteratedPrefixSum m lam n * iteratedForwardDiff m (logValue f.1) n := by
  induction m with
  | zero =>
    exact primeBlindCounterterm_eq_sum_Icc lam f hN
  | succ m ih =>
    rw [ih, sum_Icc_mul_eq_countertermPrefixSum_abel (countertermIteratedPrefixSum m lam)
      (iteratedForwardDiff m (logValue f.1)) N,
      iteratedForwardDiff_eq_zero_of_gt m (fun n hn => logValue_eq_zero_of_gt hN hn)
        (Nat.lt_succ_self N),
      mul_zero, zero_add]
    rfl

/-- **Boundary-Free First-Order Abel Representation of `primeBlindCounterterm`**:
if `EF.weilTest f.1 f.1` vanishes at `±log n` for all `n > N`, then `primeBlindCounterterm lam f`
equals the pairing of `countertermPrefixSum lam n` with `logValue f.1 n - logValue f.1 (n + 1)`
on `Finset.Icc 2 N`. -/
theorem primeBlindCounterterm_eq_sum_prefix_mul_diff (lam : ℕ → ℝ) (f : WeilTestFn) {N : ℕ}
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0) :
    primeBlindCounterterm lam f =
      ∑ n ∈ Finset.Icc 2 N,
        countertermPrefixSum lam n * (logValue f.1 n - logValue f.1 (n + 1)) :=
  primeBlindCounterterm_eq_sum_iteratedPrefix_mul_diff 1 lam f hN

/-- **Boundary-Free Second-Order (Cesàro) Representation of `primeBlindCounterterm`**:
if `EF.weilTest f.1 f.1` vanishes at `±log n` for all `n > N`, then `primeBlindCounterterm lam f`
equals the pairing of `countertermCesaroSum lam n` with the second forward difference
`logValue f.1 n - 2 * logValue f.1 (n + 1) + logValue f.1 (n + 2)` on `Finset.Icc 2 N`. -/
theorem primeBlindCounterterm_eq_sum_cesaro_mul_second_diff (lam : ℕ → ℝ) (f : WeilTestFn) {N : ℕ}
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0) :
    primeBlindCounterterm lam f =
      ∑ n ∈ Finset.Icc 2 N,
        countertermCesaroSum lam n *
          (logValue f.1 n - 2 * logValue f.1 (n + 1) + logValue f.1 (n + 2)) := by
  rw [primeBlindCounterterm_eq_sum_iteratedPrefix_mul_diff 2 lam f hN]
  refine Finset.sum_congr rfl fun n _ => ?_
  dsimp [countertermCesaroSum, countertermIteratedPrefixSum, iteratedForwardDiff]
  rw [show n + 1 + 1 = n + 2 by omega]
  ring

/-- **The `m`-th Order Cesàro Comparison Principle for `primeBlindCounterterm`**:
for any order `m : ℕ` and support cutoff `N` of `f : WeilTestFn`, if
`0 ≤ iteratedForwardDiff m (logValue f.1) n` and
`countertermIteratedPrefixSum m lam₁ n ≤ countertermIteratedPrefixSum m lam₂ n` for all
`n ∈ Finset.Icc 2 N`, then `primeBlindCounterterm lam₁ f ≤ primeBlindCounterterm lam₂ f`. -/
theorem primeBlindCounterterm_le_of_iteratedPrefixSum_le (m : ℕ) {lam₁ lam₂ : ℕ → ℝ}
    {f : WeilTestFn} {N : ℕ}
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0)
    (hdiff : ∀ n ∈ Finset.Icc 2 N, 0 ≤ iteratedForwardDiff m (logValue f.1) n)
    (hdom : ∀ n ∈ Finset.Icc 2 N,
      countertermIteratedPrefixSum m lam₁ n ≤ countertermIteratedPrefixSum m lam₂ n) :
    primeBlindCounterterm lam₁ f ≤ primeBlindCounterterm lam₂ f := by
  rw [primeBlindCounterterm_eq_sum_iteratedPrefix_mul_diff m lam₁ f hN,
    primeBlindCounterterm_eq_sum_iteratedPrefix_mul_diff m lam₂ f hN]
  exact Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_right (hdom n hn) (hdiff n hn)

/-- **The `m`-th Order Cesàro Comparison Principle for `weilFullFunctional`**:
under the hypotheses of `primeBlindCounterterm_le_of_iteratedPrefixSum_le`, dominance at the `m`-th
Cesàro level transfers monotonically to `(weilFullFunctional lam₂).re ≤ (weilFullFunctional lam₁).re`. -/
theorem re_weilFullFunctional_le_of_iteratedPrefixSum_le (m : ℕ) {lam₁ lam₂ : ℕ → ℝ}
    {f : WeilTestFn} {N : ℕ}
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0)
    (hdiff : ∀ n ∈ Finset.Icc 2 N, 0 ≤ iteratedForwardDiff m (logValue f.1) n)
    (hdom : ∀ n ∈ Finset.Icc 2 N,
      countertermIteratedPrefixSum m lam₁ n ≤ countertermIteratedPrefixSum m lam₂ n) :
    (weilFullFunctional lam₂ (EF.weilTest f.1 f.1)).re ≤
      (weilFullFunctional lam₁ (EF.weilTest f.1 f.1)).re := by
  rw [re_weilFullFunctional_eq_weilArchRe_sub_counterterm,
    re_weilFullFunctional_eq_weilArchRe_sub_counterterm]
  linarith [primeBlindCounterterm_le_of_iteratedPrefixSum_le m hN hdiff hdom]

end RHTower

end
