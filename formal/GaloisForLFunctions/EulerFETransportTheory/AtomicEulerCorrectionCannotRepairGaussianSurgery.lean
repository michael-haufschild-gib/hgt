import GaloisForLFunctions.EulerFETransportTheory.TheGaussianDefectDeterminesCausalMeasures
import GaloisForLFunctions.HTGeometry.PositiveMeasureExtremeRays
import Mathlib.MeasureTheory.Group.IntegralConvolution

/-!
# Infinite Euler corrections cannot repair Gaussian surgery

The Gaussian-weighted causal measures form a convolution algebra, even when
their undamped masses are infinite. Fubini identifies convolution with the
literal composition of outward translation operators. Atomic and continuous
parts remain separately visible to the local Gaussian differential defect.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace GaloisForLFunctions.EulerFETransportTheory

noncomputable section

/-- Gaussian damping dominates every exponential on the causal half-line. -/
theorem gaussianSourceWeight_le_exponential (B : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    gaussianSourceWeight t ≤ Real.exp (1 + (B + 1 / 2) ^ 2 / 8) * Real.exp (-B * t) := by
  have he : 2 * t ^ 2 ≤ Real.exp (2 * t) := by
    have hh := Real.pow_div_factorial_le_exp (2 * t) (by positivity) 2
    norm_num at hh
    nlinarith only [hh]
  rw [gaussianSourceWeight, ← Real.exp_add]
  apply Real.exp_le_exp.2
  unfold gaussianCausalRate
  nlinarith only [he, sq_nonneg (4 * t - (B + 1 / 2))]

/-- Every causal source with any convergent Laplace transform is admitted.
This includes logarithmic Euler measures in a Dirichlet half-plane. -/
theorem integrable_gaussianSourceWeight_of_laplace {μ : Measure ℝ}
    (hμ : μ (Ici (0 : ℝ))ᶜ = 0) {B : ℝ}
    (hB : Integrable (fun t => Real.exp (-B * t)) μ) :
    Integrable gaussianSourceWeight μ := by
  refine (hB.const_mul (Real.exp (1 + (B + 1 / 2) ^ 2 / 8))).mono' (by fun_prop) ?_
  filter_upwards [ae_iff.2 hμ] with t ht
  rw [Real.norm_of_nonneg (gaussianSourceWeight_pos _).le]
  exact gaussianSourceWeight_le_exponential B ht

theorem sFinite_of_integrable_gaussianSourceWeight {μ : Measure ℝ}
    (hw : Integrable gaussianSourceWeight μ) : SFinite μ := by
  let w : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (gaussianSourceWeight t)
  letI : IsFiniteMeasure (μ.withDensity w) := gaussianWeightedSource_finite hw
  have he : (μ.withDensity w).withDensity (fun t => (w t)⁻¹) = μ :=
    withDensity_inv_same (by fun_prop)
      (Eventually.of_forall fun t => ENNReal.ofReal_ne_zero_iff.2 (gaussianSourceWeight_pos t))
      (Eventually.of_forall fun _ => ENNReal.ofReal_ne_top)
  rw [← he]
  infer_instance

private theorem causal_prod {μ ν : Measure ℝ} [SFinite ν]
    (hμ : μ (Ici (0 : ℝ))ᶜ = 0) (hν : ν (Ici (0 : ℝ))ᶜ = 0) :
    ∀ᵐ z ∂μ.prod ν, 0 ≤ z.1 ∧ 0 ≤ z.2 := by
  apply (Measure.ae_prod_iff_ae_ae
    ((isClosed_le continuous_const continuous_fst).measurableSet.inter
      (isClosed_le continuous_const continuous_snd).measurableSet)).2
  filter_upwards [ae_iff.2 hμ] with t ht
  filter_upwards [ae_iff.2 hν] with u hu
  exact ⟨ht, hu⟩

/-- Gaussian-weighted admission is closed under full causal convolution. -/
theorem integrable_gaussianSourceWeight_conv {μ ν : Measure ℝ}
    (hμ : μ (Ici (0 : ℝ))ᶜ = 0) (hν : ν (Ici (0 : ℝ))ᶜ = 0)
    (hwμ : Integrable gaussianSourceWeight μ) (hwν : Integrable gaussianSourceWeight ν) :
    Integrable gaussianSourceWeight (μ ∗ ν) := by
  letI := sFinite_of_integrable_gaussianSourceWeight hwμ
  letI := sFinite_of_integrable_gaussianSourceWeight hwν
  rw [Measure.conv, integrable_map_measure (by fun_prop) (by fun_prop)]
  refine (hwμ.mul_prod hwν).mono' (by fun_prop) ?_
  filter_upwards [causal_prod hμ hν] with z hz
  rw [Function.comp_apply, Real.norm_of_nonneg (gaussianSourceWeight_pos _).le]
  exact gaussianSourceWeight_add_le_mul hz.1 hz.2

theorem causal_conv {μ ν : Measure ℝ} [SFinite ν]
    (hμ : μ (Ici (0 : ℝ))ᶜ = 0) (hν : ν (Ici (0 : ℝ))ᶜ = 0) :
    (μ ∗ ν) (Ici (0 : ℝ))ᶜ = 0 := by
  rw [Measure.conv, Measure.map_apply (by fun_prop) measurableSet_Ici.compl]
  apply ae_iff.1
  filter_upwards [causal_prod hμ hν] with z hz
  exact add_nonneg hz.1 hz.2

/-- Literal composition holds for the whole Gaussian response, with Fubini
admission supplied by the convolution weight. -/
theorem causalGaussianMeasureResponse_conv {μ ν : Measure ℝ}
    (hμ : μ (Ici (0 : ℝ))ᶜ = 0) (hν : ν (Ici (0 : ℝ))ᶜ = 0)
    (hwμ : Integrable gaussianSourceWeight μ) (hwν : Integrable gaussianSourceWeight ν)
    {x : ℝ} (hx : 1 < Real.pi * Real.exp (2 * x)) :
    causalGaussianMeasureResponse (μ ∗ ν) x =
      ∫ t, causalGaussianMeasureResponse ν (x + t) ∂μ := by
  letI := sFinite_of_integrable_gaussianSourceWeight hwμ
  letI := sFinite_of_integrable_gaussianSourceWeight hwν
  have hi := integrable_causalGaussianMeasureResponse (causal_conv hμ hν)
    (integrable_gaussianSourceWeight_conv hμ hν hwμ hwν) hx
  rw [causalGaussianMeasureResponse, integral_conv hi]
  apply integral_congr_ae
  filter_upwards with t
  simp only [causalGaussianMeasureResponse, add_assoc]

private theorem dirac_zero_causal :
    Measure.dirac (0 : ℝ) (Ici (0 : ℝ))ᶜ = 0 := by simp

private theorem causal_add {μ ν : Measure ℝ}
    (hμ : μ (Ici (0 : ℝ))ᶜ = 0) (hν : ν (Ici (0 : ℝ))ᶜ = 0) :
    (μ + ν) (Ici (0 : ℝ))ᶜ = 0 := by rw [Measure.add_apply, hμ, hν, add_zero]

/-- A normalized positive atomic Euler operator cannot repair a continuous
causal surgery, even with infinitely many atoms and infinite undamped mass.
Equality of local Gaussian defects forces the Euler operator to be the identity
and the signed continuous correction to vanish. -/
theorem atomic_convolution_repair_is_trivial {A K H : Measure ℝ} {S : Set ℝ}
    (hS : S.Countable) (hA : A Sᶜ = 0) (hA0 : A {0} = 1)
    (hK : K ≪ volume) (hH : H ≪ volume)
    (hAc : A (Ici (0 : ℝ))ᶜ = 0) (hKc : K (Ici (0 : ℝ))ᶜ = 0)
    (hHc : H (Ici (0 : ℝ))ᶜ = 0)
    (hwA : Integrable gaussianSourceWeight A) (hwK : Integrable gaussianSourceWeight K)
    (hwH : Integrable gaussianSourceWeight H)
    {a b : ℝ} (ha : 1 < Real.pi * Real.exp (2 * a)) (hab : a < b)
    (heq : ∀ x ∈ Ioo a b,
      causalGaussianMeasureDefect (A + A ∗ K) x =
        causalGaussianMeasureDefect (Measure.dirac 0 + A ∗ H) x) :
    A = Measure.dirac 0 ∧ K = H := by
  letI := sFinite_of_integrable_gaussianSourceWeight hwA
  letI := sFinite_of_integrable_gaussianSourceWeight hwK
  letI := sFinite_of_integrable_gaussianSourceWeight hwH
  have hwAK := integrable_gaussianSourceWeight_conv hAc hKc hwA hwK
  have hwAH := integrable_gaussianSourceWeight_conv hAc hHc hwA hwH
  have hwδ : Integrable gaussianSourceWeight (Measure.dirac (0 : ℝ)) :=
    integrable_dirac (by simp)
  have hA' : A (S ∪ {0})ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.2 subset_union_left) hA
  have hδ : Measure.dirac (0 : ℝ) (S ∪ {0})ᶜ = 0 := by simp
  have hp := atomic_and_continuous_parts_eq_of_gaussianDefect_local
    (hS.union (countable_singleton 0)) hA' hδ
    (Measure.conv_absolutelyContinuous hK) (Measure.conv_absolutelyContinuous hH)
    (causal_add hAc (causal_conv hAc hKc))
    (causal_add dirac_zero_causal (causal_conv hAc hHc))
    (integrable_add_measure.2 ⟨hwA, hwAK⟩)
    (integrable_add_measure.2 ⟨hwδ, hwAH⟩) ha hab heq
  have hpos : A (Ioi 0) = 0 := by
    exact Measure.restrict_eq_zero.1
      (hp.1.trans (Measure.restrict_eq_zero.2 (by simp)))
  have hzero : A {0}ᶜ = 0 := by
    have hnp : ∀ᵐ t ∂A, ¬0 < t := by
      rw [ae_iff]
      have hs : {t : ℝ | ¬¬0 < t} = Ioi 0 := by
        ext t
        simp only [mem_setOf_eq, not_not, mem_Ioi]
      rw [hs]
      exact hpos
    apply ae_iff.1
    filter_upwards [ae_iff.2 hAc, hnp] with t ht hnt
    change t = 0
    exact le_antisymm (le_of_not_gt hnt) ht
  have hAid : A = Measure.dirac 0 := by
    rw [HTGeometry.eq_smul_dirac_of_compl_singleton_null A hzero, hA0, one_smul]
  exact ⟨hAid, by simpa only [hAid, Measure.dirac_zero_conv] using hp.2⟩

#print axioms integrable_gaussianSourceWeight_conv
#print axioms integrable_gaussianSourceWeight_of_laplace
#print axioms causalGaussianMeasureResponse_conv
#print axioms atomic_convolution_repair_is_trivial

end

end GaloisForLFunctions.EulerFETransportTheory
