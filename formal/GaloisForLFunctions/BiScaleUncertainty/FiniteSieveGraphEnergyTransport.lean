import GaloisForLFunctions.BiScaleUncertainty.FiniteSieveRealization
import GaloisForLFunctions.BiScaleUncertainty.ExactDoublingEnergy
import GaloisForLFunctions.BiScaleUncertainty.WeightedDoublingIncidence
import GaloisForLFunctions.BiScaleUncertainty.DyadicMantissaVariance

/-!
# Exact transport of finite graph energies to divisor sieves

The explicit Möbius coefficients realize every window signal. Centered
variance, adjacent differences, integer doubling, and both physical-position
incidence energies are preserved, so the arithmetic model has the same
coercivity constants and the same witnesses.
-/

noncomputable section
open Finset
open scoped BigOperators
namespace GaloisForLFunctions.BiScaleUncertainty.FiniteHorizon
set_option autoImplicit false

/-- The actual arithmetic signal furnished by finite Möbius inversion. -/
def realizedSieveSignal (N : ℕ) (f : ℕ → ℝ) : ℕ → ℝ :=
  BezoutValuationIncidence.sieveSeq N (finiteIntegerSignalCoefficient N f)

theorem realizedSieveSignal_eq (N : ℕ) (f : ℕ → ℝ) {n : ℕ} (hn : n ∈ Icc 1 N) :
    realizedSieveSignal N f n = f n :=
  sieveSeq_finiteIntegerSignalCoefficient N f (mem_Icc.mp hn).1 (mem_Icc.mp hn).2

/-- Every center has exactly the same squared error in the arithmetic realization. -/
theorem realizedSieveSignal_centered (N : ℕ) (f : ℕ → ℝ) (c : ℝ) :
    (∑ n ∈ Icc 1 N, (realizedSieveSignal N f n - c) ^ 2) =
      ∑ n ∈ Icc 1 N, (f n - c) ^ 2 := by
  apply sum_congr rfl
  intro n hn
  rw [realizedSieveSignal_eq N f hn]

theorem realizedSieveSignal_mean (N : ℕ) (f : ℕ → ℝ) :
    integerWindowMean N (realizedSieveSignal N f) = integerWindowMean N f := by
  unfold integerWindowMean
  congr 1
  exact sum_congr rfl (fun n hn => realizedSieveSignal_eq N f hn)

/-- Minimization over centers is preserved, including the empty window. -/
theorem realizedSieveSignal_variance (N : ℕ) (f : ℕ → ℝ) :
    integerWindowVariance N (realizedSieveSignal N f) = integerWindowVariance N f := by
  unfold integerWindowVariance
  rw [realizedSieveSignal_mean, realizedSieveSignal_centered]

/-- Both endpoints of every adjacent edge lie in the realized window. -/
theorem realizedSieveSignal_additive_energy (N : ℕ) (f : ℕ → ℝ) :
    additiveStepEnergy N (realizedSieveSignal N f) = additiveStepEnergy N f := by
  unfold additiveStepEnergy
  apply sum_congr rfl
  intro n hn
  have hn' := mem_Ico.mp hn
  rw [realizedSieveSignal_eq N f (mem_Icc.mpr ⟨by omega, by omega⟩),
    realizedSieveSignal_eq N f (mem_Icc.mpr ⟨hn'.1, by omega⟩)]

/-- Both endpoints of every integer doubling edge are realized exactly. -/
theorem realizedSieveSignal_doubling_energy (N : ℕ) (f : ℕ → ℝ) :
    multiplicativeScaleEnergy 2 N (realizedSieveSignal N f) = multiplicativeScaleEnergy 2 N f := by
  simp only [multiplicativeScaleEnergy, Icc_self, sum_singleton]
  apply sum_congr rfl
  intro n hn
  have hn' := mem_Icc.mp hn
  rw [realizedSieveSignal_eq N f (mem_Icc.mpr ⟨by omega, by omega⟩),
    realizedSieveSignal_eq N f (mem_Icc.mpr ⟨hn'.1, by omega⟩)]

theorem realizedSieveSignal_joint_energy (N : ℕ) (f : ℕ → ℝ) :
    biScaleJointEnergy 2 N (realizedSieveSignal N f) = biScaleJointEnergy 2 N f := by
  simp only [biScaleJointEnergy, realizedSieveSignal_additive_energy,
    realizedSieveSignal_doubling_energy]

/-- Exact physical incidences need no compatibility between positions and sieve divisibility. -/
theorem realizedSieveSignal_exact_energy (N : ℕ) (x f : ℕ → ℝ) :
    exactDoublingEnergy N x (realizedSieveSignal N f) = exactDoublingEnergy N x f := by
  classical
  unfold exactDoublingEnergy
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  rw [realizedSieveSignal_eq N f hj, realizedSieveSignal_eq N f hi]

/-- The actual all-pairs weighted energy is preserved for arbitrary physical positions. -/
theorem realizedSieveSignal_soft_energy (N : ℕ) (x f : ℕ → ℝ) :
    softDoublingEnergy N x (realizedSieveSignal N f) = softDoublingEnergy N x f := by
  unfold softDoublingEnergy
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  rw [realizedSieveSignal_eq N f hj, realizedSieveSignal_eq N f hi]

/-- In logarithmic coordinates the physical mismatch is exactly the difference of exponentials. -/
theorem softDoublingEnergy_exp_log (N : ℕ) (x f : ℕ → ℝ) {δ : ℝ}
    (hδ : δ < 1 / 6) (hx : ∀ i ∈ Icc 1 N, |x i - (i : ℝ)| ≤ δ) :
    softDoublingEnergy N (fun n => Real.exp (Real.log (x n))) f =
      softDoublingEnergy N x f := by
  have hpos (i : ℕ) (hi : i ∈ Icc 1 N) : 0 < x i := by
    have hlo := (abs_le.mp (hx i hi)).1
    have hiR : (1 : ℝ) ≤ i := by exact_mod_cast (mem_Icc.mp hi).1
    linarith only [hlo, hiR, hδ]
  unfold softDoublingEnergy
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  simp only [softDoublingWeight, Real.exp_log (hpos i hi), Real.exp_log (hpos j hj)]

/-- The same finite coefficients simultaneously preserve all graph data. -/
theorem exists_sieveSeq_graph_realization (N : ℕ) (f : ℕ → ℝ) :
    ∃ a : ℕ → ℝ, (∀ d, N < d → a d = 0) ∧
      (∀ n ∈ Icc 1 N, BezoutValuationIncidence.sieveSeq N a n = f n) ∧
      integerWindowVariance N (BezoutValuationIncidence.sieveSeq N a) = integerWindowVariance N f ∧
      additiveStepEnergy N (BezoutValuationIncidence.sieveSeq N a) = additiveStepEnergy N f ∧
      multiplicativeScaleEnergy 2 N (BezoutValuationIncidence.sieveSeq N a) =
        multiplicativeScaleEnergy 2 N f ∧
      ∀ x : ℕ → ℝ,
        exactDoublingEnergy N x (BezoutValuationIncidence.sieveSeq N a) = exactDoublingEnergy N x f ∧
        softDoublingEnergy N x (BezoutValuationIncidence.sieveSeq N a) = softDoublingEnergy N x f := by
  refine ⟨finiteIntegerSignalCoefficient N f,
    fun _ hd => finiteIntegerSignalCoefficient_eq_zero N f hd,
    fun _ hn => realizedSieveSignal_eq N f hn, realizedSieveSignal_variance N f,
    realizedSieveSignal_additive_energy N f, realizedSieveSignal_doubling_energy N f, ?_⟩
  exact fun x => ⟨realizedSieveSignal_exact_energy N x f, realizedSieveSignal_soft_energy N x f⟩

/-- Finite divisor sieves have exactly the same valid joint coercivity constants. -/
theorem sieveSeq_joint_coercivity_iff (N : ℕ) (C : ℝ) :
    (∀ a : ℕ → ℝ, integerWindowVariance N (BezoutValuationIncidence.sieveSeq N a) ≤
      C * biScaleJointEnergy 2 N (BezoutValuationIncidence.sieveSeq N a)) ↔
    ∀ f : ℕ → ℝ, integerWindowVariance N f ≤ C * biScaleJointEnergy 2 N f := by
  constructor
  · intro h f
    have hf := h (finiteIntegerSignalCoefficient N f)
    change integerWindowVariance N (realizedSieveSignal N f) ≤
      C * biScaleJointEnergy 2 N (realizedSieveSignal N f) at hf
    simpa only [realizedSieveSignal_variance, realizedSieveSignal_joint_energy] using hf
  · exact fun h a => h (BezoutValuationIncidence.sieveSeq N a)

/-- The quadratic obstruction remains exact when all test signals are actual divisor sieves. -/
theorem sieveSeq_exact_quadratic_coercivity_lower {δ C : ℝ} (hδ : 0 < δ)
    (hδ1 : δ < 1 / 4) {N : ℕ} (hN : 2 ≤ N)
    (hC : ∀ a : ℕ → ℝ, integerWindowVariance N (BezoutValuationIncidence.sieveSeq N a) ≤ C *
      (additiveStepEnergy N (BezoutValuationIncidence.sieveSeq N a) +
        exactDoublingEnergy N (quadraticPerturbedNode δ N) (BezoutValuationIncidence.sieveSeq N a))) :
    (N : ℝ) * ((N : ℝ) + 1) / 12 ≤ C := by
  apply exactDoubling_quadratic_coercivity_lower hδ hδ1 hN
  intro f
  have hf := hC (finiteIntegerSignalCoefficient N f)
  change integerWindowVariance N (realizedSieveSignal N f) ≤ C *
    (additiveStepEnergy N (realizedSieveSignal N f) +
      exactDoublingEnergy N (quadraticPerturbedNode δ N) (realizedSieveSignal N f)) at hf
  simpa only [realizedSieveSignal_variance, realizedSieveSignal_additive_energy,
    realizedSieveSignal_exact_energy] using hf

/-- The weighted positive survivor holds in the same actual arithmetic model. -/
theorem sieveSeq_soft_coercivity (N : ℕ) (hN : 1 ≤ N) (x a : ℕ → ℝ) {δ : ℝ}
    (hδ : δ < 1 / 6) (hx : ∀ i ∈ Icc 1 N, |x i - (i : ℝ)| ≤ δ) :
    integerWindowVariance N (BezoutValuationIncidence.sieveSeq N a) ≤
      (24 * (N : ℝ) / (1 - 6 * δ)) *
        (additiveStepEnergy N (BezoutValuationIncidence.sieveSeq N a) +
          softDoublingEnergy N x (BezoutValuationIncidence.sieveSeq N a)) :=
  softDoubling_window_coercivity N hN x (BezoutValuationIncidence.sieveSeq N a) hδ hx

/-- The same physical weights give exactly the same valid constants on arithmetic signals. -/
theorem sieveSeq_soft_coercivity_iff (N : ℕ) (x : ℕ → ℝ) (C : ℝ) :
    (∀ a : ℕ → ℝ, integerWindowVariance N (BezoutValuationIncidence.sieveSeq N a) ≤ C *
      (additiveStepEnergy N (BezoutValuationIncidence.sieveSeq N a) +
        softDoublingEnergy N x (BezoutValuationIncidence.sieveSeq N a))) ↔
    ∀ f : ℕ → ℝ, integerWindowVariance N f ≤
      C * (additiveStepEnergy N f + softDoublingEnergy N x f) := by
  constructor
  · intro h f
    have hf := h (finiteIntegerSignalCoefficient N f)
    change integerWindowVariance N (realizedSieveSignal N f) ≤ C *
      (additiveStepEnergy N (realizedSieveSignal N f) +
        softDoublingEnergy N x (realizedSieveSignal N f)) at hf
    simpa only [realizedSieveSignal_variance, realizedSieveSignal_additive_energy,
      realizedSieveSignal_soft_energy] using hf
  · exact fun h a => h (BezoutValuationIncidence.sieveSeq N a)

/-- The original tent forces linear deterioration for every allowed perturbation. -/
theorem softDoubling_dyadic_coercivity_lower (h : ℕ) (x : ℕ → ℝ) {δ C : ℝ}
    (hδ : δ < 1 / 6)
    (hx : ∀ i ∈ Icc 1 (2 ^ (h + 4) - 1), |x i - (i : ℝ)| ≤ δ)
    (hC : ∀ f : ℕ → ℝ, integerWindowVariance (2 ^ (h + 4) - 1) f ≤ C *
      (additiveStepEnergy (2 ^ (h + 4) - 1) f +
        softDoublingEnergy (2 ^ (h + 4) - 1) x f)) :
    ((2 ^ (h + 4) - 1 : ℕ) : ℝ) / 4096 ≤ C := by
  let N := 2 ^ (h + 4) - 1
  have hN : 2 ≤ N := by
    have hp : (2 : ℕ) ^ (h + 4) = 16 * 2 ^ h := by rw [pow_add]; norm_num; ring
    have hh : 0 < (2 : ℕ) ^ h := by positivity
    dsimp only [N]
    omega
  have hv : (N : ℝ) / 2048 ≤ integerWindowVariance N dyadicMantissaTent := by
    simpa only [integerWindowVariance] using
      dyadicMantissaTent_variance_lower h (integerWindowMean N dyadicMantissaTent)
  have hc := hC dyadicMantissaTent
  rw [softDoublingEnergy_dyadicMantissaTent _ x hδ hx, add_zero] at hc
  have hnR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hC0 : 0 ≤ C := by
    by_contra hneg
    have hb := mul_nonpos_of_nonpos_of_nonneg (le_of_lt (lt_of_not_ge hneg))
      (additiveStepEnergy_nonneg N dyadicMantissaTent)
    linarith only [hv, hc, hb, hnR]
  have hb := mul_le_mul_of_nonneg_left (additiveStepEnergy_dyadicMantissaTent_lt_two hN).le hC0
  change (N : ℝ) / 4096 ≤ C
  linarith only [hv, hc, hb]

/-- Restricting to actual finite divisor sieves does not improve the weighted lower constant. -/
theorem sieveSeq_soft_dyadic_coercivity_lower (h : ℕ) (x : ℕ → ℝ) {δ C : ℝ}
    (hδ : δ < 1 / 6)
    (hx : ∀ i ∈ Icc 1 (2 ^ (h + 4) - 1), |x i - (i : ℝ)| ≤ δ)
    (hC : ∀ a : ℕ → ℝ,
      integerWindowVariance (2 ^ (h + 4) - 1)
          (BezoutValuationIncidence.sieveSeq (2 ^ (h + 4) - 1) a) ≤ C *
        (additiveStepEnergy (2 ^ (h + 4) - 1)
            (BezoutValuationIncidence.sieveSeq (2 ^ (h + 4) - 1) a) +
          softDoublingEnergy (2 ^ (h + 4) - 1) x
            (BezoutValuationIncidence.sieveSeq (2 ^ (h + 4) - 1) a))) :
    ((2 ^ (h + 4) - 1 : ℕ) : ℝ) / 4096 ≤ C :=
  softDoubling_dyadic_coercivity_lower h x hδ hx
    ((sieveSeq_soft_coercivity_iff _ x C).mp hC)

end GaloisForLFunctions.BiScaleUncertainty.FiniteHorizon
