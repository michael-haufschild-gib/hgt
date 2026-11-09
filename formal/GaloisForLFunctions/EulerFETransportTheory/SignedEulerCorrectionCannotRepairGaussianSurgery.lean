import GaloisForLFunctions.EulerFETransportTheory.AtomicEulerCorrectionCannotRepairGaussianSurgery

/-!
# Signed Euler corrections cannot repair continuous Gaussian surgery

Positive and negative atomic sources may both have infinite undamped mass.
Gaussian weighting makes their common terms finite and cancellable. Local
Gaussian source reconstruction then separates the atomic operator from the
continuous surgery, including signed normalized Euler and Möbius operators.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace GaloisForLFunctions.EulerFETransportTheory

noncomputable section

/-- Positive Gaussian damping permits cancellation of a common measure whose
undamped total mass may be infinite. -/
theorem cancel_gaussianWeighted_common_measure {C K H : Measure ℝ}
    (hwC : Integrable gaussianSourceWeight C) (he : C + K = C + H) : K = H := by
  let w : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (gaussianSourceWeight t)
  letI : IsFiniteMeasure (C.withDensity w) := gaussianWeightedSource_finite hwC
  have he' : C.withDensity w + K.withDensity w = C.withDensity w + H.withDensity w := by
    simpa only [withDensity_add_measure] using congrArg (fun μ : Measure ℝ => μ.withDensity w) he
  have hd := (Measure.add_right_inj (C.withDensity w) (K.withDensity w) (H.withDensity w)).1 he'
  have hr (μ : Measure ℝ) : (μ.withDensity w).withDensity (fun t => (w t)⁻¹) = μ :=
    withDensity_inv_same (by fun_prop)
      (Eventually.of_forall fun t => ENNReal.ofReal_ne_zero_iff.2 (gaussianSourceWeight_pos t))
      (Eventually.of_forall fun _ => ENNReal.ofReal_ne_top)
  rw [← hr K, ← hr H, hd]

private theorem causal_measure_decomposition {μ : Measure ℝ}
    (hμ : μ (Ici (0 : ℝ))ᶜ = 0) :
    μ = μ.restrict (Ioi 0) + μ {0} • Measure.dirac 0 := by
  have hc : μ.restrict (Ici 0) = μ := Measure.restrict_eq_self_of_ae_mem (ae_iff.2 hμ)
  have hs : (Ioi (0 : ℝ))ᶜ ∩ Ici 0 = {0} := by
    ext t
    simp only [mem_inter_iff, mem_compl_iff, mem_Ioi, mem_Ici, mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact le_antisymm (le_of_not_gt h1) h2
    · rintro rfl
      simp
  have he : μ.restrict (Ioi 0)ᶜ = μ.restrict {0} := by
    calc μ.restrict (Ioi 0)ᶜ = (μ.restrict (Ici 0)).restrict (Ioi 0)ᶜ := by rw [hc]
      _ = μ.restrict {0} := by
        rw [Measure.restrict_restrict measurableSet_Ioi.compl, hs]
  calc μ = μ.restrict (Ioi 0) + μ.restrict (Ioi 0)ᶜ :=
      (Measure.restrict_add_restrict_compl measurableSet_Ioi).symm
    _ = μ.restrict (Ioi 0) + μ {0} • Measure.dirac 0 := by
      rw [he, Measure.restrict_singleton]

private theorem signed_atomic_identity {A B : Measure ℝ}
    (hAc : A (Ici (0 : ℝ))ᶜ = 0) (hBc : B (Ici (0 : ℝ))ᶜ = 0)
    (h0 : A {0} = B {0} + 1)
    (hpos : A.restrict (Ioi 0) = B.restrict (Ioi 0)) : A = B + Measure.dirac 0 := by
  calc A = A.restrict (Ioi 0) + A {0} • Measure.dirac 0 := causal_measure_decomposition hAc
    _ = B.restrict (Ioi 0) + (B {0} + 1) • Measure.dirac 0 := by rw [h0, hpos]
    _ = (B.restrict (Ioi 0) + B {0} • Measure.dirac 0) + Measure.dirac 0 := by
      rw [add_smul, one_smul, add_assoc]
    _ = B + Measure.dirac 0 := by rw [← causal_measure_decomposition hBc]

private theorem add_causal {μ ν : Measure ℝ}
    (hμ : μ (Ici (0 : ℝ))ᶜ = 0) (hν : ν (Ici (0 : ℝ))ᶜ = 0) :
    (μ + ν) (Ici (0 : ℝ))ᶜ = 0 := by rw [Measure.add_apply, hμ, hν, add_zero]

/-- No normalized real signed atomic operator can repair a nonzero continuous
Gaussian surgery. The positive and negative sources may each have infinitely
many atoms and infinite total mass; only Gaussian-weighted variation is finite. -/
theorem signed_atomic_convolution_repair_is_trivial {A B K H : Measure ℝ} {S : Set ℝ}
    (hS : S.Countable) (hA : A Sᶜ = 0) (hB : B Sᶜ = 0) (h0 : A {0} = B {0} + 1)
    (hK : K ≪ volume) (hH : H ≪ volume)
    (hAc : A (Ici (0 : ℝ))ᶜ = 0) (hBc : B (Ici (0 : ℝ))ᶜ = 0)
    (hKc : K (Ici (0 : ℝ))ᶜ = 0) (hHc : H (Ici (0 : ℝ))ᶜ = 0)
    (hwA : Integrable gaussianSourceWeight A) (hwB : Integrable gaussianSourceWeight B)
    (hwK : Integrable gaussianSourceWeight K) (hwH : Integrable gaussianSourceWeight H)
    {a b : ℝ} (ha : 1 < Real.pi * Real.exp (2 * a)) (hab : a < b)
    (heq : ∀ x ∈ Ioo a b,
      causalGaussianMeasureDefect (A + A ∗ K + B ∗ H) x =
        causalGaussianMeasureDefect (B + A ∗ H + B ∗ K) x) :
    A = B + Measure.dirac 0 ∧ K = H := by
  letI := sFinite_of_integrable_gaussianSourceWeight hwA
  letI := sFinite_of_integrable_gaussianSourceWeight hwB
  letI := sFinite_of_integrable_gaussianSourceWeight hwK
  letI := sFinite_of_integrable_gaussianSourceWeight hwH
  have hwAK := integrable_gaussianSourceWeight_conv hAc hKc hwA hwK
  have hwAH := integrable_gaussianSourceWeight_conv hAc hHc hwA hwH
  have hwBK := integrable_gaussianSourceWeight_conv hBc hKc hwB hwK
  have hwBH := integrable_gaussianSourceWeight_conv hBc hHc hwB hwH
  have hp := atomic_and_continuous_parts_eq_of_gaussianDefect_local hS hA hB
    ((Measure.conv_absolutelyContinuous hK).add_left (Measure.conv_absolutelyContinuous hH))
    ((Measure.conv_absolutelyContinuous hH).add_left (Measure.conv_absolutelyContinuous hK))
    (add_causal hAc (add_causal (causal_conv hAc hKc) (causal_conv hBc hHc)))
    (add_causal hBc (add_causal (causal_conv hAc hHc) (causal_conv hBc hKc)))
    (integrable_add_measure.2 ⟨hwA, integrable_add_measure.2 ⟨hwAK, hwBH⟩⟩)
    (integrable_add_measure.2 ⟨hwB, integrable_add_measure.2 ⟨hwAH, hwBK⟩⟩)
    ha hab (fun x hx => by simpa only [add_assoc] using heq x hx)
  have hAid := signed_atomic_identity hAc hBc h0 hp.1
  have hc : (B ∗ K + B ∗ H) + K = (B ∗ K + B ∗ H) + H := by
    calc (B ∗ K + B ∗ H) + K = (B ∗ K + K) + B ∗ H := by ac_rfl
      _ = (B ∗ H + H) + B ∗ K := by
        simpa only [hAid, Measure.add_conv, Measure.dirac_zero_conv] using hp.2
      _ = (B ∗ K + B ∗ H) + H := by ac_rfl
  exact ⟨hAid, cancel_gaussianWeighted_common_measure
    (integrable_add_measure.2 ⟨hwBK, hwBH⟩) hc⟩

#print axioms cancel_gaussianWeighted_common_measure
#print axioms signed_atomic_convolution_repair_is_trivial

end

end GaloisForLFunctions.EulerFETransportTheory
