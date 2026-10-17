import GaloisForLFunctions.BiScaleUncertainty.HyperbolicMultiplierGramTransfer
import GaloisForLFunctions.BiScaleUncertainty.SchurCappedCollarHierarchy

/-!
# Physical energy from the full measured signed Gram matrix

Every signed node correlation and every cross-coset entry is retained. An origin
anchor cancels the singular weight before integration: the exact Gram deficit is
between zero and twice the allocated collar mass times source energy. Main source
theorems apply to arbitrary compact continuous sources, without grid blindness.
-/

set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators CompactlySupported ENNReal
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm
namespace GaloisForLFunctions.BiScaleUncertainty
noncomputable section
variable {ι : Type*}

namespace AnchoredGram

def nodes (M : Finset ι) : Finset (Unit ⊕ ι) := ({()} : Finset Unit).disjSum M
def weights (W : ℝ) (a : ι → ℝ) : Unit ⊕ ι → ℝ := Sum.elim (fun _ => W) a
def shifts (t : ι → ℝ) : Unit ⊕ ι → ℝ := Sum.elim (fun _ => 0) t
def gram (f : C_c(ℝ, ℝ)) (M : Finset ι) (a t : ι → ℝ) (W : ℝ) : ℝ :=
  translationGramEnergy f (nodes M) (weights W a) (shifts t)
def kernel (f : C_c(ℝ, ℝ)) (M : Finset ι) (a t : ι → ℝ) (W : ℝ) : ℝ :=
  autocorr f 0 * (W + ∑ i ∈ M, a i) - Real.sqrt (autocorr f 0 * gram f M a t W)

theorem pairing_le (f : C_c(ℝ, ℝ)) (M : Finset ι) (a t : ι → ℝ) (W y : ℝ) :
    W * autocorr f y + (∑ i ∈ M, a i * autocorr f (t i - y)) ≤
      Real.sqrt (autocorr f 0 * gram f M a t W) := by
  have h := translationPacket_correlation_le f (nodes M) (weights W a) (shifts t) y
  simpa [nodes, weights, shifts, Finset.sum_disjSum, autocorr_neg, gram] using h

theorem gram_le_mass_sq (f : C_c(ℝ, ℝ)) (M : Finset ι) (a t : ι → ℝ)
    (ha : ∀ i ∈ M, 0 ≤ a i) :
    translationGramEnergy f M a t ≤ autocorr f 0 * (∑ i ∈ M, a i) ^ 2 := by
  calc
    _ ≤ ∑ i ∈ M, ∑ j ∈ M, a i * a j * autocorr f 0 := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (ha i hi) (ha j hj))
      exact (abs_le.mp (abs_autocorr_le_zero f.hasCompactSupport f.continuous _)).2
    _ = _ := by
      rw [pow_two]
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- The singular origin anchor cancels, leaving a finite collar-mass bound. -/
theorem kernel_bounds (f : C_c(ℝ, ℝ)) (M : Finset ι) (a t : ι → ℝ) {W : ℝ}
    (hW : 0 ≤ W) (ha : ∀ i ∈ M, 0 ≤ a i) :
    0 ≤ kernel f M a t W ∧ kernel f M a t W ≤ 2 * autocorr f 0 * ∑ i ∈ M, a i := by
  have hR := autocorr_zero_nonneg f
  have hm : 0 ≤ ∑ i ∈ M, a i := Finset.sum_nonneg ha
  have haw : ∀ i ∈ nodes M, 0 ≤ weights W a i := by
    intro i hi
    cases i with
    | inl u => exact hW
    | inr i => exact ha i (by simpa [nodes] using hi)
  have hu := gram_le_mass_sq f (nodes M) (weights W a) (shifts t) haw
  have hsum : (∑ i ∈ nodes M, weights W a i) = W + ∑ i ∈ M, a i := by
    simp [nodes, weights, Finset.sum_disjSum]
  rw [hsum] at hu
  change gram f M a t W ≤ _ at hu
  have hupper : Real.sqrt (autocorr f 0 * gram f M a t W) ≤
      autocorr f 0 * (W + ∑ i ∈ M, a i) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨mul_nonneg hR (add_nonneg hW hm), ?_⟩
    nlinarith only [mul_le_mul_of_nonneg_left hu hR]
  have hl := pairing_le f M a t W 0
  have hc : -(autocorr f 0 * ∑ i ∈ M, a i) ≤ ∑ i ∈ M, a i * autocorr f (t i - 0) := by
    rw [← neg_mul, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have h := mul_le_mul_of_nonneg_left
      (abs_le.mp (abs_autocorr_le_zero f.hasCompactSupport f.continuous (t i - 0))).1 (ha i hi)
    nlinarith only [h]
  unfold kernel
  constructor <;> nlinarith only [hupper, hl, hc]

theorem kernel_source_pointwise (f : C_c(ℝ, ℝ)) (M : Finset ι) (a t : ι → ℝ) (W y : ℝ) :
    kernel f M a t W ≤ W * (autocorr f 0 - autocorr f y) +
      ∑ i ∈ M, a i * (autocorr f 0 - autocorr f (t i - y)) := by
  have h := pairing_le f M a t W y
  unfold kernel
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  nlinarith only [h]

/-- The actual signed node deficits give a sharper capacity bound than `2 R` per weight. -/
theorem kernel_le_node_deficit (f : C_c(ℝ, ℝ)) (M : Finset ι) (a t : ι → ℝ) (W : ℝ) :
    kernel f M a t W ≤ ∑ i ∈ M, a i * (autocorr f 0 - autocorr f (t i)) := by
  simpa only [sub_self, mul_zero, zero_add, sub_zero] using kernel_source_pointwise f M a t W 0

end AnchoredGram

namespace PhysicalCollarPartition
variable {n : ℕ}

def signedGramNodes (n : ℕ) : Finset (Bool × ℕ) := Finset.univ ×ˢ Finset.range (n + 1)
def signedGramShift (p : Bool × ℕ) : ℝ := if p.1 then -logarithmicCollarNode p.2 else logarithmicCollarNode p.2
def signedGramKernel (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) (y : ℝ) : ℝ :=
  AnchoredGram.kernel f (signedGramNodes n) (fun p => ρ.weight p.1 p.2 y)
    signedGramShift (archLevySinhWeight y)
def signedGramCoefficient (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) : ℝ :=
  ∫ y in Ioo 0 logarithmicCollarRadius, ρ.signedGramKernel f y

theorem signedGram_mass (ρ : PhysicalCollarPartition n) (y : ℝ) :
    (∑ p ∈ signedGramNodes n, ρ.weight p.1 p.2 y) = ρ.mass y := by
  simp [signedGramNodes, Finset.sum_product, mass, Finset.sum_add_distrib, add_comm]

theorem signedGram_cost (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) (y : ℝ) :
    (∑ p ∈ signedGramNodes n, ρ.weight p.1 p.2 y *
      (autocorr f 0 - autocorr f (signedGramShift p - y))) =
      ∑ j ∈ Finset.range (n + 1),
        (ρ.weight false j y * (autocorr f 0 - autocorr f (logarithmicCollarNode j - y)) +
         ρ.weight true j y * (autocorr f 0 - autocorr f (logarithmicCollarNode j + y))) := by
  have he (j : ℕ) : autocorr f (-logarithmicCollarNode j - y) =
      autocorr f (logarithmicCollarNode j + y) := by
    rw [show -logarithmicCollarNode j - y = -(logarithmicCollarNode j + y) by ring, autocorr_neg]
  simp [signedGramNodes, signedGramShift, Finset.sum_product,
    Finset.sum_add_distrib, he, add_comm]

theorem signedGramKernel_le_node_deficits (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) (y : ℝ) :
    ρ.signedGramKernel f y ≤ ∑ k ∈ Finset.range (n + 1),
      (ρ.weight false k y + ρ.weight true k y) * (autocorr f 0 - autocorr f (logarithmicCollarNode k)) := by
  have h := AnchoredGram.kernel_le_node_deficit f (signedGramNodes n)
    (fun p => ρ.weight p.1 p.2 y) signedGramShift (archLevySinhWeight y)
  change ρ.signedGramKernel f y ≤ _ at h
  simpa [signedGramNodes, signedGramShift, Finset.sum_product, autocorr_neg,
    Finset.sum_add_distrib, add_mul, add_comm] using h

theorem signedGramKernel_bounds (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ))
    {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ ρ.signedGramKernel f y ∧ ρ.signedGramKernel f y ≤ 2 * autocorr f 0 * ρ.mass y := by
  have h := AnchoredGram.kernel_bounds f (signedGramNodes n)
    (fun p => ρ.weight p.1 p.2 y) signedGramShift (archLevySinhWeight_nonneg hy)
    (fun p _ => ρ.weight_nonneg p.1 p.2 y)
  rwa [ρ.signedGram_mass y] at h

theorem measurable_signedGramKernel (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) :
    Measurable (ρ.signedGramKernel f) := by
  have hw (i : Unit ⊕ (Bool × ℕ)) : Measurable (fun y =>
      AnchoredGram.weights (archLevySinhWeight y) (fun p => ρ.weight p.1 p.2 y) i) := by
    cases i with
    | inl u => exact measurable_archLevySinhWeight
    | inr p => exact ρ.measurable_weight p.1 p.2
  have hg : Measurable (fun y => AnchoredGram.gram f (signedGramNodes n)
      (fun p => ρ.weight p.1 p.2 y) signedGramShift (archLevySinhWeight y)) := by
    unfold AnchoredGram.gram translationGramEnergy
    exact (AnchoredGram.nodes (signedGramNodes n)).measurable_sum fun i _ =>
      (AnchoredGram.nodes (signedGramNodes n)).measurable_sum fun j _ =>
        ((hw i).mul (hw j)).mul_const _
  have he : ρ.signedGramKernel f = fun y => autocorr f 0 * (archLevySinhWeight y + ρ.mass y) -
      Real.sqrt (autocorr f 0 * AnchoredGram.gram f (signedGramNodes n)
        (fun p => ρ.weight p.1 p.2 y) signedGramShift (archLevySinhWeight y)) := by
    funext y
    simp only [signedGramKernel, AnchoredGram.kernel, ρ.signedGram_mass]
  rw [he]
  exact ((measurable_archLevySinhWeight.add ρ.measurable_mass).const_mul _).sub
    (Real.continuous_sqrt.measurable.comp (hg.const_mul _))

theorem integrableOn_signedGramKernel (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) :
    IntegrableOn (ρ.signedGramKernel f) (Ioo 0 logarithmicCollarRadius) := by
  apply volume.integrableOn_of_bounded
    (M := 2 * autocorr f 0 * (((n + 1 : ℕ) : ℝ) * (2 * logarithmicCollarWeightBound n)))
    (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top) (ρ.measurable_signedGramKernel f).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
  have h := ρ.signedGramKernel_bounds f hy.1.le
  have hm := mul_le_mul_of_nonneg_left (ρ.mass_le_bound y) (by positivity [autocorr_zero_nonneg f] : 0 ≤ 2 * autocorr f 0)
  simpa only [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2.trans hm

theorem signedGramKernel_source_pointwise (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) (y : ℝ) :
    ρ.signedGramKernel f y ≤ archLevySinhWeight y * (autocorr f 0 - autocorr f y) +
      ∑ j ∈ Finset.range (n + 1),
        (ρ.weight false j y * (autocorr f 0 - autocorr f (logarithmicCollarNode j - y)) +
         ρ.weight true j y * (autocorr f 0 - autocorr f (logarithmicCollarNode j + y))) := by
  have h := AnchoredGram.kernel_source_pointwise f (signedGramNodes n)
    (fun p => ρ.weight p.1 p.2 y) signedGramShift (archLevySinhWeight y) y
  rwa [ρ.signedGram_cost f y] at h

/-- Unconditional actual-source receiver retaining the complete measured signed Gram data. -/
theorem signedGramCoefficient_source_energy (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) :
    ENNReal.ofReal (ρ.signedGramCoefficient f) ≤
      ∫⁻ x in Ioo 0 (logarithmicCollarEndpoint n), continuousArchIncrementDensity (compactAutocorrKernel f) x := by
  have hn : 0 ≤ᵐ[volume.restrict (Ioo 0 logarithmicCollarRadius)] ρ.signedGramKernel f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    exact (ρ.signedGramKernel_bounds f hy.1.le).1
  unfold signedGramCoefficient
  rw [ofReal_integral_eq_lintegral_ofReal (ρ.integrableOn_signedGramKernel f) hn]
  calc
    _ ≤ ∫⁻ y in Ioo 0 logarithmicCollarRadius, ρ.sourceFibre f y := by
      apply setLIntegral_mono' measurableSet_Ioo
      intro y hy
      rw [ρ.sourceFibre_eq_ofReal f hy.1.le]
      exact ENNReal.ofReal_le_ofReal (ρ.signedGramKernel_source_pointwise f y)
    _ = _ := ρ.lintegral_sourceFibre f

/-- Smoothness is a domain condition; no grid zero or signed-correlation hypothesis is supplied. -/
theorem signedGramCoefficient_le_energy (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 2 (f : ℝ → ℝ)) : ρ.signedGramCoefficient f ≤ biScaleLevyEnergy f := by
  have hb := (ρ.signedGramCoefficient_source_energy f).trans
    (lintegral_mono_set (show Ioo 0 (logarithmicCollarEndpoint n) ⊆ Ioi 0 from fun _ hx => hx.1))
  have hi := integrableOn_biScaleLevyIntegrand hf f.hasCompactSupport
  have hn : 0 ≤ᵐ[volume.restrict (Ioi 0)]
      (fun x => (autocorr f 0 - autocorr f x) * archLevySinhWeight x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (autocorr_sub_nonneg f.hasCompactSupport f.continuous x) (archLevySinhWeight_pos hx).le
  have he : ENNReal.ofReal (biScaleLevyEnergy f) =
      ∫⁻ x in Ioi 0, continuousArchIncrementDensity (compactAutocorrKernel f) x :=
    ofReal_integral_eq_lintegral_ofReal hi hn
  rw [← he] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (biScaleLevyEnergy_nonneg f.hasCompactSupport f.continuous)).1 hb

theorem signedGramCoefficient_le_normalized_energy (ρ : PhysicalCollarPartition n)
    (f : C_c(ℝ, ℝ)) (hf : ContDiff ℝ 2 (f : ℝ → ℝ)) :
    ρ.signedGramCoefficient f / autocorr f 0 ≤ biScaleLevyEnergy f / autocorr f 0 :=
  div_le_div_of_nonneg_right (ρ.signedGramCoefficient_le_energy f hf) (autocorr_zero_nonneg f)

/-- On the grid-blind domain, retain both the uniform Schur hierarchy and the
additional certificate from all measured signed cross-coset entries. -/
theorem measuredGram_and_schur_source_certificate (ρ : PhysicalCollarPartition n)
    (f : SmoothLogarithmicGridSource n) :
    max (monotoneSchurCappedCoefficient n) (ρ.signedGramCoefficient f.1.1 / autocorr f.1.1 0) ≤
      biScaleLevyEnergy f.1.1 / autocorr f.1.1 0 :=
  max_le (monotoneSchurCappedCoefficient_le_normalized_energy n f)
    (ρ.signedGramCoefficient_le_normalized_energy f.1.1 f.2.1)

end PhysicalCollarPartition
end
end GaloisForLFunctions.BiScaleUncertainty
