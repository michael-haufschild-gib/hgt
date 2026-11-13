import GaloisForLFunctions.HTGeometry.CompactKernelL2Convolution

/-!+# Translation kernels against square-integrable profiles

A product-measure square majorant justifies Fubini without pointwise bounds
on either profile. A square-integrable kernel then bounds its pairing with
a nonnegative integrable test by the test's ordinary mass.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
namespace GaloisForLFunctions.HTGeometry

/-- A nonnegative integrable kernel admits Fubini against two measurable L² profiles. -/
theorem integrable_weighted_translation_pairing {K F G : ℝ → ℝ}
    (hK : Integrable K) (hKm : Measurable K) (hK0 : ∀ h, 0 ≤ K h)
    (hFm : Measurable F) (hGm : Measurable G)
    (hF2 : Integrable (fun u => F u ^ 2)) (hG2 : Integrable (fun u => G u ^ 2)) :
    Integrable (fun p : ℝ × ℝ => K p.1 * F (p.2 - p.1) * G p.2)
      ((volume : Measure ℝ).prod volume) := by
  have h1 : Integrable (fun p : ℝ × ℝ => K p.1 * F (p.2 - p.1) ^ 2)
      ((volume : Measure ℝ).prod volume) :=
    (measurePreserving_prod_sub volume volume).integrable_comp_of_integrable
      (hK.mul_prod hF2)
  have h2 := hK.mul_prod hG2
  refine (h1.add h2).mono'
    (((hKm.comp measurable_fst).mul (hFm.comp (measurable_snd.sub measurable_fst))).mul
      (hGm.comp measurable_snd)).aestronglyMeasurable ?_
  exact Eventually.of_forall fun p => by
    have hp : |F (p.2 - p.1) * G p.2| ≤ F (p.2 - p.1) ^ 2 + G p.2 ^ 2 := by
      rw [abs_mul]
      nlinarith only [sq_nonneg (|F (p.2 - p.1)| - |G p.2|),
        sq_abs (F (p.2 - p.1)), sq_abs (G p.2),
        mul_nonneg (abs_nonneg (F (p.2 - p.1))) (abs_nonneg (G p.2))]
    change ‖K p.1 * F (p.2 - p.1) * G p.2‖ ≤
      K p.1 * F (p.2 - p.1) ^ 2 + K p.1 * G p.2 ^ 2
    rw [Real.norm_eq_abs, mul_assoc, abs_mul, abs_of_nonneg (hK0 p.1)]
    exact (mul_le_mul_of_nonneg_left hp (hK0 p.1)).trans_eq (by ring)

/-- Averaging translated pairings is the literal convolution pairing. -/
theorem integral_weighted_translation_pairing {K F G : ℝ → ℝ}
    (hK : Integrable K) (hKm : Measurable K) (hK0 : ∀ h, 0 ≤ K h)
    (hFm : Measurable F) (hGm : Measurable G)
    (hF2 : Integrable (fun u => F u ^ 2)) (hG2 : Integrable (fun u => G u ^ 2)) :
    (∫ h, K h * ∫ u, F (u - h) * G u) = ∫ u, lineConvolution K F u * G u := by
  calc
    _ = ∫ h, ∫ u, K h * F (u - h) * G u := by
      apply integral_congr_ae
      exact Eventually.of_forall fun h => by
        dsimp only
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall fun u => (mul_assoc _ _ _).symm
    _ = ∫ u, ∫ h, K h * F (u - h) * G u :=
      integral_integral_swap (integrable_weighted_translation_pairing hK hKm hK0 hFm hGm hF2 hG2)
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun u => by
        dsimp only
        rw [integral_mul_const]
        rfl

/-- L² kernel control turns a translated mixed pairing into an ordinary-mass bound. -/
theorem integral_weighted_translation_pairing_le {K F G : ℝ → ℝ}
    (hK : Integrable K) (hKm : Measurable K) (hK0 : ∀ h, 0 ≤ K h)
    (hK2 : Integrable (fun h => K h ^ 2)) (hFm : Measurable F) (hGm : Measurable G)
    (hF2 : Integrable (fun u => F u ^ 2)) (hG2 : Integrable (fun u => G u ^ 2))
    (hG1 : Integrable G) (hG0 : ∀ u, 0 ≤ G u) :
    (∫ h, K h * ∫ u, F (u - h) * G u) ≤
      Real.sqrt ((∫ h, K h ^ 2) * ∫ u, F u ^ 2) * ∫ u, G u := by
  let D := Real.sqrt ((∫ h, K h ^ 2) * ∫ u, F u ^ 2)
  have hb (u : ℝ) : |lineConvolution K F u| ≤ D :=
    abs_lineConvolution_le hKm.aestronglyMeasurable hK2 hFm.aestronglyMeasurable hF2 u
  have hm : StronglyMeasurable (lineConvolution K F) :=
    ((hKm.comp measurable_snd).mul
      (hFm.comp (measurable_fst.sub measurable_snd))).stronglyMeasurable.integral_prod_right'
  have hi : Integrable (fun u => lineConvolution K F u * G u) := by
    refine (hG1.norm.const_mul D).mono' (hm.mul hGm.stronglyMeasurable).aestronglyMeasurable ?_
    exact Eventually.of_forall fun u => by
      dsimp only
      rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hb u) (abs_nonneg _)
  rw [integral_weighted_translation_pairing hK hKm hK0 hFm hGm hF2 hG2,
    ← integral_const_mul]
  exact integral_mono hi (hG1.const_mul D) fun u =>
    mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hb u)) (hG0 u)

/-- Reflection gives the same mass bound for forward translated pairings. -/
theorem integral_weighted_forward_pairing_le {K F G : ℝ → ℝ}
    (hK : Integrable K) (hKm : Measurable K) (hK0 : ∀ h, 0 ≤ K h)
    (hK2 : Integrable (fun h => K h ^ 2)) (hFm : Measurable F) (hGm : Measurable G)
    (hF2 : Integrable (fun u => F u ^ 2)) (hG2 : Integrable (fun u => G u ^ 2))
    (hG1 : Integrable G) (hG0 : ∀ u, 0 ≤ G u) :
    (∫ h, K h * ∫ u, F (u + h) * G u) ≤
      Real.sqrt ((∫ h, K h ^ 2) * ∫ u, F u ^ 2) * ∫ u, G u := by
  have hneg (f : ℝ → ℝ) : (∫ u, f (-u)) = ∫ u, f u := by
    simpa only [zero_sub] using integral_sub_left_eq_self f volume 0
  have hcross (h : ℝ) : (∫ u, F (-(u - h)) * G (-u)) = ∫ u, F (u + h) * G u := by
    calc
      _ = ∫ u, F (-(-u - h)) * G (-(-u)) :=
        (hneg (fun u => F (-(u - h)) * G (-u))).symm
      _ = _ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun u => by
          dsimp only
          rw [neg_neg, show -(-u - h) = u + h by ring]
  have hh := integral_weighted_translation_pairing_le
    (F := fun u => F (-u)) (G := fun u => G (-u))
    hK hKm hK0 hK2 (hFm.comp measurable_neg) (hGm.comp measurable_neg)
    hF2.comp_neg hG2.comp_neg hG1.comp_neg (fun u => hG0 (-u))
  simp_rw [hcross] at hh
  rw [hneg (fun u => F u ^ 2), hneg G] at hh
  exact hh

#print axioms integral_weighted_translation_pairing
#print axioms integral_weighted_translation_pairing_le
#print axioms integral_weighted_forward_pairing_le
end GaloisForLFunctions.HTGeometry
