/-
# Trace-class completion of the Suzuki causal-depth Gamma Schur kernel

The corpus Gamma Schur residual has an exact Mercer expansion after deleting Jacobi degrees zero
and two.  The actual cubic-aperture Suzuki weights are square-summable over every prime and
valuation depth.  This file assembles those two facts into one global operator.

The resulting feature matrix is Hilbert--Schmidt.  Its positive energy `A†A` is trace class, and
its source block is exactly the existing prime-depth Gamma Schur kernel.  Its trace is bounded by
the aperture-independent wall-mass ceiling.  This closes the complete Gamma-Schur operator
placement and bounded-holonomy premise of `SUZUKI-FE-REFLECTED-WALL-WARD-ASSEMBLY`; it does not
assert the remaining Robin trace comparison or marked-halfgap lower bound.
-/
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCausalDepthGammaSchurCoherence
import GaloisForLFunctions.RHTower.Suzuki.SuzukiApertureDressedWallLightCompletion
import GaloisForLFunctions.HTGeometry.HilbertSchmidtAlgebra
import GaloisForLFunctions.HTGeometry.HilbertSchmidtTrace

noncomputable section

open scoped BigOperators

namespace RHTower

/-- Enumeration of the surviving projected Gamma Jacobi degrees: one, then every degree at
least three. -/
def suzukiCausalDepthGammaSurvivingDegree : ℕ → ℕ
  | 0 => 1
  | k + 1 => k + 3

/-- One surviving Gamma Mercer feature. -/
def suzukiCausalDepthGammaFeature (k : ℕ) (t : ℝ) : ℝ :=
  gammaConductorJacobiFeature (suzukiCausalDepthGammaSurvivingDegree k) t

theorem summable_sq_suzukiCausalDepthGammaFeature
    {t : ℝ} (ht : 0 < t) :
    Summable (fun k : ℕ => suzukiCausalDepthGammaFeature k t ^ (2 : ℕ)) := by
  have htail : Summable (fun k : ℕ =>
      gammaConductorJacobiFeature (k + 3) t ^ (2 : ℕ)) := by
    simpa using
      (summable_gammaConductorJacobiTail_sum_sq
        (n := 1) (fun _ : Fin 1 => t) (fun _ : Fin 1 => 1) (fun _ => ht))
  apply (summable_nat_add_iff 1).mp
  simpa [suzukiCausalDepthGammaFeature,
    suzukiCausalDepthGammaSurvivingDegree] using htail

/-- The squared feature-row energy is exactly the projected Gamma residual diagonal. -/
theorem tsum_sq_suzukiCausalDepthGammaFeature
    {t : ℝ} (ht : 0 < t) :
    (∑' k : ℕ, suzukiCausalDepthGammaFeature k t ^ (2 : ℕ)) =
      gammaConductorModeSchurResidual t t := by
  have hs := summable_sq_suzukiCausalDepthGammaFeature ht
  have hsplit := hs.sum_add_tsum_nat_add 1
  rw [gammaConductorModeSchurResidual_eq_jacobi_one_add_tsum ht ht]
  rw [← hsplit]
  simp [suzukiCausalDepthGammaFeature,
    suzukiCausalDepthGammaSurvivingDegree, pow_two]

theorem summable_mul_suzukiCausalDepthGammaFeature
    {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    Summable (fun k : ℕ =>
      suzukiCausalDepthGammaFeature k t *
        suzukiCausalDepthGammaFeature k u) := by
  apply Summable.of_norm_bounded
      (g := fun k : ℕ =>
        (suzukiCausalDepthGammaFeature k t ^ (2 : ℕ) +
          suzukiCausalDepthGammaFeature k u ^ (2 : ℕ)) / 2)
  · exact ((summable_sq_suzukiCausalDepthGammaFeature ht).add
      (summable_sq_suzukiCausalDepthGammaFeature hu)).div_const 2
  · intro k
    rw [Real.norm_eq_abs, abs_mul]
    nlinarith [sq_nonneg
        (|suzukiCausalDepthGammaFeature k t| -
          |suzukiCausalDepthGammaFeature k u|),
      sq_abs (suzukiCausalDepthGammaFeature k t),
      sq_abs (suzukiCausalDepthGammaFeature k u)]

/-- Polarized Mercer identity for all positive Gamma frequencies. -/
theorem tsum_mul_suzukiCausalDepthGammaFeature
    {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    (∑' k : ℕ,
      suzukiCausalDepthGammaFeature k t *
        suzukiCausalDepthGammaFeature k u) =
      gammaConductorModeSchurResidual t u := by
  have hs := summable_mul_suzukiCausalDepthGammaFeature ht hu
  have hsplit := hs.sum_add_tsum_nat_add 1
  rw [gammaConductorModeSchurResidual_eq_jacobi_one_add_tsum ht hu]
  rw [← hsplit]
  simp [suzukiCausalDepthGammaFeature,
    suzukiCausalDepthGammaSurvivingDegree]

/-- A Schur complement cannot exceed the unit covariance diagonal. -/
theorem gammaConductorModeSchurResidual_self_le_one (t : ℝ) :
    gammaConductorModeSchurResidual t t ≤ 1 := by
  unfold gammaConductorModeSchurResidual gammaConductorModeCovariance
  have hschur : 0 ≤
      semilocalArchimedeanSecondMomentCovarianceKernel t *
        semilocalArchimedeanSecondMomentCovarianceKernel t / (3 / 2 : ℝ) := by
    exact div_nonneg (mul_self_nonneg _) (by norm_num)
  have hphi : 0 ≤ semilocalArchimedeanCharacteristic t ^ (2 : ℕ) := sq_nonneg _
  have hzero : semilocalArchimedeanCharacteristic (t - t) = 1 := by
    simp [semilocalArchimedeanCharacteristic]
  rw [hzero]
  nlinarith

/-- Actual aperture-weighted Gamma feature at one prime-depth source coordinate. -/
def suzukiCausalDepthGammaWeightedFeature
    (h a : ℝ) (pe : Nat.Primes × ℕ) (k : ℕ) : ℝ :=
  suzukiCausalDepthGammaWeight h a pe *
    suzukiCausalDepthGammaFeature k (suzukiCausalDepthGammaFrequency pe)

theorem summable_sq_suzukiCausalDepthGammaWeight_allPrime
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) :
    Summable (fun pe : Nat.Primes × ℕ =>
      suzukiCausalDepthGammaWeight h a pe ^ (2 : ℕ)) := by
  simpa only [normSq_suzukiCriticalApertureBoundaryAtom_eq_causalDepthGammaWeight_sq]
    using summable_normSq_suzukiCriticalApertureBoundaryAtom_allPrime hh ha 0

theorem summable_sq_suzukiCausalDepthGammaWeightedFeature_row
    (h a : ℝ) (pe : Nat.Primes × ℕ) :
    Summable (fun k : ℕ =>
      suzukiCausalDepthGammaWeightedFeature h a pe k ^ (2 : ℕ)) := by
  have hs := summable_sq_suzukiCausalDepthGammaFeature
    (suzukiCausalDepthGammaFrequency_pos pe)
  refine (hs.mul_left (suzukiCausalDepthGammaWeight h a pe ^ (2 : ℕ))).congr ?_
  intro k
  simp only [suzukiCausalDepthGammaWeightedFeature]
  ring

theorem tsum_sq_suzukiCausalDepthGammaWeightedFeature_row
    (h a : ℝ) (pe : Nat.Primes × ℕ) :
    (∑' k : ℕ,
      suzukiCausalDepthGammaWeightedFeature h a pe k ^ (2 : ℕ)) =
      suzukiCausalDepthGammaWeight h a pe ^ (2 : ℕ) *
        gammaConductorModeSchurResidual
          (suzukiCausalDepthGammaFrequency pe)
          (suzukiCausalDepthGammaFrequency pe) := by
  rw [show (∑' k : ℕ,
      suzukiCausalDepthGammaWeightedFeature h a pe k ^ (2 : ℕ)) =
      suzukiCausalDepthGammaWeight h a pe ^ (2 : ℕ) *
        ∑' k : ℕ,
          suzukiCausalDepthGammaFeature k
            (suzukiCausalDepthGammaFrequency pe) ^ (2 : ℕ) by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro k
    simp only [suzukiCausalDepthGammaWeightedFeature]
    ring]
  rw [tsum_sq_suzukiCausalDepthGammaFeature
    (suzukiCausalDepthGammaFrequency_pos pe)]

/-- Polarized weighted feature sum recovers the literal source Gamma Schur kernel. -/
theorem tsum_mul_suzukiCausalDepthGammaWeightedFeature
    (h a : ℝ) (x y : Nat.Primes × ℕ) :
    (∑' k : ℕ,
      suzukiCausalDepthGammaWeightedFeature h a x k *
        suzukiCausalDepthGammaWeightedFeature h a y k) =
      suzukiCausalDepthGammaSchurKernel h a x y := by
  calc
    (∑' k : ℕ,
        suzukiCausalDepthGammaWeightedFeature h a x k *
          suzukiCausalDepthGammaWeightedFeature h a y k) =
        (suzukiCausalDepthGammaWeight h a x *
          suzukiCausalDepthGammaWeight h a y) *
          ∑' k : ℕ,
            suzukiCausalDepthGammaFeature k
                (suzukiCausalDepthGammaFrequency x) *
              suzukiCausalDepthGammaFeature k
                (suzukiCausalDepthGammaFrequency y) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro k
      simp only [suzukiCausalDepthGammaWeightedFeature]
      ring
    _ = suzukiCausalDepthGammaSchurKernel h a x y := by
      rw [tsum_mul_suzukiCausalDepthGammaFeature
        (suzukiCausalDepthGammaFrequency_pos x)
        (suzukiCausalDepthGammaFrequency_pos y)]
      unfold suzukiCausalDepthGammaSchurKernel
      ring

/-- Joint square-summability over every prime-depth source and every surviving Gamma feature. -/
theorem summable_sq_suzukiCausalDepthGammaWeightedFeature_allPrime
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) :
    Summable (fun z : (Nat.Primes × ℕ) × ℕ =>
      suzukiCausalDepthGammaWeightedFeature h a z.1 z.2 ^ (2 : ℕ)) := by
  rw [summable_prod_of_nonneg (fun _ => sq_nonneg _)]
  constructor
  · exact fun pe =>
      summable_sq_suzukiCausalDepthGammaWeightedFeature_row h a pe
  · have hweights := summable_sq_suzukiCausalDepthGammaWeight_allPrime hh ha
    have houter : Summable (fun pe : Nat.Primes × ℕ =>
        suzukiCausalDepthGammaWeight h a pe ^ (2 : ℕ) *
          gammaConductorModeSchurResidual
            (suzukiCausalDepthGammaFrequency pe)
            (suzukiCausalDepthGammaFrequency pe)) := by
      refine Summable.of_nonneg_of_le (fun pe => ?_) (fun pe => ?_) hweights
      · exact mul_nonneg (sq_nonneg _)
          (gammaConductorModeSchurResidual_pos
            (suzukiCausalDepthGammaFrequency_pos pe)
            (suzukiCausalDepthGammaFrequency_pos pe)).le
      · have hr := gammaConductorModeSchurResidual_self_le_one
          (suzukiCausalDepthGammaFrequency pe)
        have hw := sq_nonneg (suzukiCausalDepthGammaWeight h a pe)
        nlinarith
    refine houter.congr (fun pe => ?_)
    exact (tsum_sq_suzukiCausalDepthGammaWeightedFeature_row h a pe).symm

/-- Shared carrier containing source coordinates and Mercer-feature coordinates. -/
abbrev SuzukiCausalDepthGammaTraceIndex := (Nat.Primes × ℕ) ⊕ ℕ

/-- Rectangular weighted feature matrix, embedded as the feature-to-source block of one square
kernel. -/
def suzukiCausalDepthGammaFeatureKernel (h a : ℝ) :
    SuzukiCausalDepthGammaTraceIndex × SuzukiCausalDepthGammaTraceIndex → ℂ := fun z =>
  match z with
  | (Sum.inr k, Sum.inl pe) =>
      (suzukiCausalDepthGammaWeightedFeature h a pe k : ℂ)
  | _ => 0

private def suzukiCausalDepthGammaCrossEmbedding :
    (Nat.Primes × ℕ) × ℕ →
      SuzukiCausalDepthGammaTraceIndex × SuzukiCausalDepthGammaTraceIndex := fun z =>
  (Sum.inr z.2, Sum.inl z.1)

private theorem suzukiCausalDepthGammaCrossEmbedding_injective :
    Function.Injective suzukiCausalDepthGammaCrossEmbedding := by
  rintro ⟨pe, k⟩ ⟨qe, l⟩ h
  change (Sum.inr k, Sum.inl pe) = (Sum.inr l, Sum.inl qe) at h
  have hk : k = l := Sum.inr_injective (congrArg Prod.fst h)
  have hpe : pe = qe := Sum.inl_injective (congrArg Prod.snd h)
  exact Prod.ext hpe hk

private def suzukiCausalDepthGammaCrossSupport :
    Set (SuzukiCausalDepthGammaTraceIndex × SuzukiCausalDepthGammaTraceIndex) :=
  Set.range suzukiCausalDepthGammaCrossEmbedding

private def suzukiCausalDepthGammaCrossEquiv :
    ((Nat.Primes × ℕ) × ℕ) ≃ suzukiCausalDepthGammaCrossSupport :=
  Equiv.ofInjective suzukiCausalDepthGammaCrossEmbedding
    suzukiCausalDepthGammaCrossEmbedding_injective

/-- **Global Gamma-Schur placement.**  The complete prime-depth feature matrix is
Hilbert--Schmidt. -/
theorem suzukiCausalDepthGammaFeatureKernel_isHS
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) :
    HilbertSchmidt.IsHS (suzukiCausalDepthGammaFeatureKernel h a) := by
  let energy :
      SuzukiCausalDepthGammaTraceIndex × SuzukiCausalDepthGammaTraceIndex → ℝ :=
    fun z => ‖suzukiCausalDepthGammaFeatureKernel h a z‖ ^ (2 : ℕ)
  have hcomp : Summable (fun z : (Nat.Primes × ℕ) × ℕ =>
      energy (suzukiCausalDepthGammaCrossEquiv z)) := by
    refine (summable_sq_suzukiCausalDepthGammaWeightedFeature_allPrime hh ha).congr
      (fun z => ?_)
    change suzukiCausalDepthGammaWeightedFeature h a z.1 z.2 ^ (2 : ℕ) =
      ‖(suzukiCausalDepthGammaWeightedFeature h a z.1 z.2 : ℂ)‖ ^ (2 : ℕ)
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hsub : Summable
      (energy ∘ Subtype.val : suzukiCausalDepthGammaCrossSupport → ℝ) :=
    (suzukiCausalDepthGammaCrossEquiv.summable_iff).mp hcomp
  have hindicator :
      Summable (suzukiCausalDepthGammaCrossSupport.indicator energy) :=
    summable_subtype_iff_indicator.mp hsub
  exact hindicator.congr fun z => by
    show suzukiCausalDepthGammaCrossSupport.indicator energy z =
      ‖suzukiCausalDepthGammaFeatureKernel h a z‖ ^ (2 : ℕ)
    by_cases hz : z ∈ suzukiCausalDepthGammaCrossSupport
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz]
      rcases z with ⟨i, j⟩
      cases i <;> cases j <;>
        simp [suzukiCausalDepthGammaCrossSupport,
          suzukiCausalDepthGammaCrossEmbedding,
          suzukiCausalDepthGammaFeatureKernel] at hz ⊢

/-- Hilbert--Schmidt energy equals the complete weighted Mercer energy. -/
theorem hsNormSq_suzukiCausalDepthGammaFeatureKernel_eq
    (h a : ℝ) :
    HilbertSchmidt.hsNormSq (suzukiCausalDepthGammaFeatureKernel h a) =
      ∑' z : (Nat.Primes × ℕ) × ℕ,
        suzukiCausalDepthGammaWeightedFeature h a z.1 z.2 ^ (2 : ℕ) := by
  let energy :
      SuzukiCausalDepthGammaTraceIndex × SuzukiCausalDepthGammaTraceIndex → ℝ :=
    fun z => ‖suzukiCausalDepthGammaFeatureKernel h a z‖ ^ (2 : ℕ)
  rw [HilbertSchmidt.hsNormSq]
  change (∑' z, energy z) = _
  calc
    (∑' z, energy z) =
        ∑' z, suzukiCausalDepthGammaCrossSupport.indicator energy z := by
      apply tsum_congr
      intro z
      by_cases hz : z ∈ suzukiCausalDepthGammaCrossSupport
      · rw [Set.indicator_of_mem hz]
      · rw [Set.indicator_of_notMem hz]
        rcases z with ⟨i, j⟩
        cases i <;> cases j <;>
          simp [energy, suzukiCausalDepthGammaCrossSupport,
            suzukiCausalDepthGammaCrossEmbedding,
            suzukiCausalDepthGammaFeatureKernel] at hz ⊢
    _ = ∑' z : suzukiCausalDepthGammaCrossSupport, energy z :=
      (tsum_subtype suzukiCausalDepthGammaCrossSupport energy).symm
    _ = ∑' z : (Nat.Primes × ℕ) × ℕ,
        energy (suzukiCausalDepthGammaCrossEquiv z) :=
      (suzukiCausalDepthGammaCrossEquiv.tsum_eq
        (fun z : suzukiCausalDepthGammaCrossSupport => energy z)).symm
    _ = ∑' z : (Nat.Primes × ℕ) × ℕ,
        suzukiCausalDepthGammaWeightedFeature h a z.1 z.2 ^ (2 : ℕ) := by
      apply tsum_congr
      intro z
      change ‖(suzukiCausalDepthGammaWeightedFeature h a z.1 z.2 : ℂ)‖ ^ (2 : ℕ) = _
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem hsNormSq_suzukiCausalDepthGammaFeatureKernel_eq_weightedResidual
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) :
    HilbertSchmidt.hsNormSq (suzukiCausalDepthGammaFeatureKernel h a) =
      ∑' pe : Nat.Primes × ℕ,
        suzukiCausalDepthGammaWeight h a pe ^ (2 : ℕ) *
          gammaConductorModeSchurResidual
            (suzukiCausalDepthGammaFrequency pe)
            (suzukiCausalDepthGammaFrequency pe) := by
  rw [hsNormSq_suzukiCausalDepthGammaFeatureKernel_eq]
  rw [(summable_sq_suzukiCausalDepthGammaWeightedFeature_allPrime hh ha).tsum_prod]
  apply tsum_congr
  intro pe
  exact tsum_sq_suzukiCausalDepthGammaWeightedFeature_row h a pe

theorem hsNormSq_suzukiCausalDepthGammaFeatureKernel_le_weightMass
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) :
    HilbertSchmidt.hsNormSq (suzukiCausalDepthGammaFeatureKernel h a) ≤
      ∑' pe : Nat.Primes × ℕ,
        suzukiCausalDepthGammaWeight h a pe ^ (2 : ℕ) := by
  rw [hsNormSq_suzukiCausalDepthGammaFeatureKernel_eq_weightedResidual hh ha]
  have hweights := summable_sq_suzukiCausalDepthGammaWeight_allPrime hh ha
  have hres : Summable (fun pe : Nat.Primes × ℕ =>
      suzukiCausalDepthGammaWeight h a pe ^ (2 : ℕ) *
        gammaConductorModeSchurResidual
          (suzukiCausalDepthGammaFrequency pe)
          (suzukiCausalDepthGammaFrequency pe)) := by
    refine Summable.of_nonneg_of_le (fun pe => ?_) (fun pe => ?_) hweights
    · exact mul_nonneg (sq_nonneg _)
        (gammaConductorModeSchurResidual_pos
          (suzukiCausalDepthGammaFrequency_pos pe)
          (suzukiCausalDepthGammaFrequency_pos pe)).le
    · have hr := gammaConductorModeSchurResidual_self_le_one
        (suzukiCausalDepthGammaFrequency pe)
      have hw := sq_nonneg (suzukiCausalDepthGammaWeight h a pe)
      nlinarith
  exact hres.tsum_le_tsum (fun pe => by
    have hr := gammaConductorModeSchurResidual_self_le_one
      (suzukiCausalDepthGammaFrequency pe)
    have hw := sq_nonneg (suzukiCausalDepthGammaWeight h a pe)
    nlinarith) hweights

/-- Uniform trace budget inherited from the complete dressed Suzuki wall mass. -/
theorem hsNormSq_suzukiCausalDepthGammaFeatureKernel_le_uniformCeiling
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) :
    HilbertSchmidt.hsNormSq (suzukiCausalDepthGammaFeatureKernel h a) ≤
      2 * ((h * Real.sqrt h)⁻¹) ^ (2 : ℕ) *
        (∑' p : Nat.Primes,
          Real.log (p : ℝ) * ((p : ℝ) ^ (2 : ℕ))⁻¹) := by
  calc
    HilbertSchmidt.hsNormSq (suzukiCausalDepthGammaFeatureKernel h a) ≤
        ∑' pe : Nat.Primes × ℕ,
          suzukiCausalDepthGammaWeight h a pe ^ (2 : ℕ) :=
      hsNormSq_suzukiCausalDepthGammaFeatureKernel_le_weightMass hh ha
    _ = ∑' pe : Nat.Primes × ℕ,
        Complex.normSq
          (suzukiCriticalApertureBoundaryAtom h a 0 pe.1 pe.2) := by
      apply tsum_congr
      intro pe
      exact (normSq_suzukiCriticalApertureBoundaryAtom_eq_causalDepthGammaWeight_sq
        h a 0 pe).symm
    _ ≤ 2 * ((h * Real.sqrt h)⁻¹) ^ (2 : ℕ) *
        (∑' p : Nat.Primes,
          Real.log (p : ℝ) * ((p : ℝ) ^ (2 : ℕ))⁻¹) :=
      tsum_normSq_suzukiCriticalApertureBoundaryAtom_allPrime_le hh ha 0

/-- Positive Gram kernel of the complete feature matrix. -/
def suzukiCausalDepthGammaEnergyKernel (h a : ℝ) :
    SuzukiCausalDepthGammaTraceIndex × SuzukiCausalDepthGammaTraceIndex → ℂ :=
  HilbertSchmidt.hsComp
    (HilbertSchmidt.hsAdjoint (suzukiCausalDepthGammaFeatureKernel h a))
    (suzukiCausalDepthGammaFeatureKernel h a)

/-- The source-source block of the global Gram is exactly the corpus Gamma Schur kernel. -/
theorem suzukiCausalDepthGammaEnergyKernel_sourceBlock
    (h a : ℝ) (x y : Nat.Primes × ℕ) :
    suzukiCausalDepthGammaEnergyKernel h a (Sum.inl x, Sum.inl y) =
      (suzukiCausalDepthGammaSchurKernel h a x y : ℂ) := by
  let f : SuzukiCausalDepthGammaTraceIndex → ℂ := fun z =>
    HilbertSchmidt.hsAdjoint (suzukiCausalDepthGammaFeatureKernel h a)
        (Sum.inl x, z) *
      suzukiCausalDepthGammaFeatureKernel h a (z, Sum.inl y)
  have hreal : Summable (fun k : ℕ =>
      suzukiCausalDepthGammaWeightedFeature h a x k *
        suzukiCausalDepthGammaWeightedFeature h a y k) := by
    have hbase := summable_mul_suzukiCausalDepthGammaFeature
      (suzukiCausalDepthGammaFrequency_pos x)
      (suzukiCausalDepthGammaFrequency_pos y)
    refine (hbase.mul_left
      (suzukiCausalDepthGammaWeight h a x *
        suzukiCausalDepthGammaWeight h a y)).congr ?_
    intro k
    simp only [suzukiCausalDepthGammaWeightedFeature]
    ring
  have hright : Summable (f ∘ Sum.inr) := by
    apply Summable.of_norm_bounded (hreal.norm)
    intro k
    simp [f, HilbertSchmidt.hsAdjoint,
      suzukiCausalDepthGammaFeatureKernel, Complex.norm_real]
  have hleft : HasSum (f ∘ Sum.inl) 0 := by
    have hz : (f ∘ Sum.inl) =
        (fun _ : Nat.Primes × ℕ => (0 : ℂ)) := by
      funext pe
      simp [f, HilbertSchmidt.hsAdjoint,
        suzukiCausalDepthGammaFeatureKernel]
    rw [hz]
    exact hasSum_zero
  have hsum : HasSum f (0 + ∑' k : ℕ, (f ∘ Sum.inr) k) :=
    hleft.sum hright.hasSum
  unfold suzukiCausalDepthGammaEnergyKernel HilbertSchmidt.hsComp
  change (∑' z : SuzukiCausalDepthGammaTraceIndex, f z) = _
  rw [hsum.tsum_eq, zero_add]
  rw [show (∑' k : ℕ, (f ∘ Sum.inr) k) =
      ((∑' k : ℕ,
        suzukiCausalDepthGammaWeightedFeature h a x k *
          suzukiCausalDepthGammaWeightedFeature h a y k : ℝ) : ℂ) by
    rw [Complex.ofReal_tsum]
    apply tsum_congr
    intro k
    simp [f, HilbertSchmidt.hsAdjoint,
      suzukiCausalDepthGammaFeatureKernel]]
  rw [tsum_mul_suzukiCausalDepthGammaWeightedFeature]

/-- Hilbert space carrying the source and surviving Gamma-feature coordinates. -/
abbrev SuzukiCausalDepthGammaTraceL2 :=
  lp (fun _ : SuzukiCausalDepthGammaTraceIndex => ℂ) 2

/-- Global feature operator. -/
def suzukiCausalDepthGammaFeatureOperator
    (h a : ℝ) (hh : 0 < h) (ha : 0 < a) :
    SuzukiCausalDepthGammaTraceL2 →L[ℂ] SuzukiCausalDepthGammaTraceL2 :=
  HilbertSchmidt.toOperator (suzukiCausalDepthGammaFeatureKernel_isHS hh ha)

theorem suzukiCausalDepthGammaFeatureOperator_isHilbertSchmidt
    (h a : ℝ) (hh : 0 < h) (ha : 0 < a) :
    ContinuousLinearMap.IsHilbertSchmidt
      (suzukiCausalDepthGammaFeatureOperator h a hh ha) :=
  HilbertSchmidt.isHilbertSchmidt_toOperator
    (suzukiCausalDepthGammaFeatureKernel_isHS hh ha)

/-- Positive complete Gamma Schur energy operator. -/
def suzukiCausalDepthGammaEnergyOperator
    (h a : ℝ) (hh : 0 < h) (ha : 0 < a) :
    SuzukiCausalDepthGammaTraceL2 →L[ℂ] SuzukiCausalDepthGammaTraceL2 :=
  ContinuousLinearMap.adjoint
      (suzukiCausalDepthGammaFeatureOperator h a hh ha) ∘L
    suzukiCausalDepthGammaFeatureOperator h a hh ha

/-- **Trace-class Gamma-Schur completion.**  The full prime-depth Gamma Schur Gram is the source
block of one unconditional positive trace-class operator. -/
theorem suzukiCausalDepthGammaEnergyOperator_isTraceClass
    (h a : ℝ) (hh : 0 < h) (ha : 0 < a) :
    ContinuousLinearMap.IsTraceClass
      (suzukiCausalDepthGammaEnergyOperator h a hh ha) :=
  (suzukiCausalDepthGammaFeatureOperator_isHilbertSchmidt h a hh ha).adjoint_comp_self_isTraceClass

theorem suzukiCausalDepthGammaEnergyOperator_re_inner_nonneg
    (h a : ℝ) (hh : 0 < h) (ha : 0 < a)
    (v : SuzukiCausalDepthGammaTraceL2) :
    0 ≤ Complex.re
      (inner ℂ v (suzukiCausalDepthGammaEnergyOperator h a hh ha v)) := by
  change 0 ≤ Complex.re
    (inner ℂ v
      (ContinuousLinearMap.adjoint
        (suzukiCausalDepthGammaFeatureOperator h a hh ha)
        (suzukiCausalDepthGammaFeatureOperator h a hh ha v)))
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact inner_self_nonneg (𝕜 := ℂ) (E := SuzukiCausalDepthGammaTraceL2)

/-- Exact operator-matrix realization of the existing source Gamma Schur kernel. -/
theorem suzukiCausalDepthGammaEnergyOperator_sourceBlock
    (h a : ℝ) (hh : 0 < h) (ha : 0 < a)
    (x y : Nat.Primes × ℕ) :
    HilbertSchmidt.matrixOf
        (suzukiCausalDepthGammaEnergyOperator h a hh ha)
        (Sum.inl x, Sum.inl y) =
      (suzukiCausalDepthGammaSchurKernel h a x y : ℂ) := by
  rw [suzukiCausalDepthGammaEnergyOperator,
    suzukiCausalDepthGammaFeatureOperator,
    HilbertSchmidt.adjoint_toOperator]
  rw [← HilbertSchmidt.toOperator_hsComp,
    HilbertSchmidt.matrixOf_toOperator]
  exact suzukiCausalDepthGammaEnergyKernel_sourceBlock h a x y

/-- The trace of the complete positive Gamma Schur energy has the aperture-independent source
ceiling. -/
theorem suzukiCausalDepthGammaEnergyOperator_re_opTrace_le_uniformCeiling
    (h a : ℝ) (hh : 0 < h) (ha : 0 < a) :
    Complex.re (ContinuousLinearMap.opTrace
      (suzukiCausalDepthGammaEnergyOperator h a hh ha)) ≤
      2 * ((h * Real.sqrt h)⁻¹) ^ (2 : ℕ) *
        (∑' p : Nat.Primes,
          Real.log (p : ℝ) * ((p : ℝ) ^ (2 : ℕ))⁻¹) := by
  calc
    Complex.re (ContinuousLinearMap.opTrace
        (suzukiCausalDepthGammaEnergyOperator h a hh ha)) =
        ContinuousLinearMap.hsNormSq
          (suzukiCausalDepthGammaFeatureOperator h a hh ha) := by
      exact ContinuousLinearMap.re_opTrace_adjoint_comp_self
        (suzukiCausalDepthGammaFeatureOperator_isHilbertSchmidt h a hh ha)
    _ = HilbertSchmidt.hsNormSq
        (suzukiCausalDepthGammaFeatureKernel h a) :=
      HilbertSchmidt.hsNormSq_toOperator
        (suzukiCausalDepthGammaFeatureKernel_isHS hh ha)
    _ ≤ 2 * ((h * Real.sqrt h)⁻¹) ^ (2 : ℕ) *
        (∑' p : Nat.Primes,
          Real.log (p : ℝ) * ((p : ℝ) ^ (2 : ℕ))⁻¹) :=
      hsNormSq_suzukiCausalDepthGammaFeatureKernel_le_uniformCeiling hh ha

/-! ### Premise-free canonical source scale -/

/-- Fixed unit source/aperture realization of the complete Gamma Schur energy. -/
def suzukiCanonicalCausalDepthGammaEnergyOperator :
    SuzukiCausalDepthGammaTraceL2 →L[ℂ] SuzukiCausalDepthGammaTraceL2 :=
  suzukiCausalDepthGammaEnergyOperator 1 1 zero_lt_one zero_lt_one

/-- Premise-free trace-class completion at the fixed canonical source scale. -/
theorem suzukiCanonicalCausalDepthGammaEnergyOperator_isTraceClass :
    ContinuousLinearMap.IsTraceClass
      suzukiCanonicalCausalDepthGammaEnergyOperator :=
  suzukiCausalDepthGammaEnergyOperator_isTraceClass
    1 1 zero_lt_one zero_lt_one

/-- Premise-free positivity of the canonical complete Gamma Schur energy. -/
theorem suzukiCanonicalCausalDepthGammaEnergyOperator_re_inner_nonneg
    (v : SuzukiCausalDepthGammaTraceL2) :
    0 ≤ Complex.re
      (inner ℂ v (suzukiCanonicalCausalDepthGammaEnergyOperator v)) :=
  suzukiCausalDepthGammaEnergyOperator_re_inner_nonneg
    1 1 zero_lt_one zero_lt_one v

/-- Exact canonical operator block; no trace, positivity, or RH premise is supplied. -/
theorem suzukiCanonicalCausalDepthGammaEnergyOperator_sourceBlock
    (x y : Nat.Primes × ℕ) :
    HilbertSchmidt.matrixOf suzukiCanonicalCausalDepthGammaEnergyOperator
        (Sum.inl x, Sum.inl y) =
      (suzukiCausalDepthGammaSchurKernel 1 1 x y : ℂ) :=
  suzukiCausalDepthGammaEnergyOperator_sourceBlock
    1 1 zero_lt_one zero_lt_one x y

/-- Premise-free trace ceiling for the canonical complete Gamma Schur energy. -/
theorem suzukiCanonicalCausalDepthGammaEnergyOperator_re_opTrace_le :
    Complex.re (ContinuousLinearMap.opTrace
      suzukiCanonicalCausalDepthGammaEnergyOperator) ≤
      2 * (∑' p : Nat.Primes,
        Real.log (p : ℝ) * ((p : ℝ) ^ (2 : ℕ))⁻¹) := by
  simpa [suzukiCanonicalCausalDepthGammaEnergyOperator] using
    (suzukiCausalDepthGammaEnergyOperator_re_opTrace_le_uniformCeiling
      1 1 zero_lt_one zero_lt_one)

end RHTower
