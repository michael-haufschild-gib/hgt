import GaloisForLFunctions.RHTower.SoninDilationSourceSupportRecovery
import GaloisForLFunctions.RHTower.SoninCoherentWardCubic

/-!
# Source rigidity of the single-scale balanced Ward cubic

The exact support-recovery theorem makes the adjoint retained transition injective
on the lost Sonin layer in the crossing chamber. Hence `Z†W=0` forces `Z=0` for
the actual single-scale source. The balanced Ward cubic is strictly negative
exactly when the successive-layer transition is nonzero.

This closes the single-scale decoupling locus without an abstract density premise.
Coherent mixtures, cofinal prime--Gamma completion and the Hardy-index budget are
not asserted here.
-/

noncomputable section
namespace RHTower
open ContinuousLinearMap

/-- Retained-channel injectivity on the even Sonin carrier. -/
theorem eq_zero_of_evenCentralSoninProjection_dilationSum_eq_zero
    {a b c r : ℝ} (hb : 0 < b) (hc : 0 < c) (hr : 1 < r) (hca : c ≤ r * a)
    {v : evenSubspace} (hva : evenCentralSoninProjection a v = v)
    (hvb : evenCentralSoninProjection b v = 0)
    (hvD : evenCentralSoninProjection c (evenDilationSum r hr v) = 0) : v = 0 := by
  have hva' : centralSoninProjection a (v : SoninL2) = v :=
    congrArg Subtype.val hva
  have hvb' : centralSoninProjection b (v : SoninL2) = 0 := congrArg Subtype.val hvb
  have hvD' : centralSoninProjection c (dilationSum r hr (v : SoninL2)) = 0 :=
    congrArg Subtype.val hvD
  apply Subtype.ext
  exact eq_zero_of_centralSoninProjection_dilationSum_eq_zero hb hc hr hca
    (Submodule.starProjection_eq_self_iff.mp hva') hvb' hvD'

private theorem lost_layer_support {a b : ℝ} (hab : a ≤ b) :
    evenCentralSoninProjection a * evenSoninApertureLayer a b = evenSoninApertureLayer a b ∧
    evenCentralSoninProjection b * evenSoninApertureLayer a b = 0 := by
  have haa := (evenCentralSoninProjection_mul_of_le (a := a) (b := a) le_rfl).1
  have hbb := (evenCentralSoninProjection_mul_of_le (a := b) (b := b) le_rfl).1
  constructor
  · rw [evenSoninApertureLayer, mul_sub, haa,
      (evenCentralSoninProjection_mul_of_le hab).2]
  · rw [evenSoninApertureLayer, mul_sub,
      (evenCentralSoninProjection_mul_of_le hab).1, hbb, sub_self]

/-- The adjoint retained transition detects every operator valued in the lost layer. -/
theorem evenSoninRetainedAdjoint_mul_eq_zero_iff
    {a b c r : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (hr : 1 < r) (hca : c ≤ r * a)
    (T : evenSubspace →L[ℂ] evenSubspace)
    (hT : evenSoninApertureLayer a b * T = T) :
    adjoint (evenSoninApertureLayer a b * evenDilationSum r hr *
      evenCentralSoninProjection c) * T = 0 ↔ T = 0 := by
  constructor
  · intro hzero
    rw [adjoint_mul_clm, adjoint_mul_clm, adjoint_evenCentralSoninProjection,
      adjoint_evenDilationSum, adjoint_evenSoninApertureLayer, mul_assoc, mul_assoc, hT] at hzero
    rcases lost_layer_support hab with ⟨hQa, hQb⟩
    have hQaT : evenCentralSoninProjection a * T = T := by
      calc _ = evenCentralSoninProjection a * (evenSoninApertureLayer a b * T) := by rw [hT]
           _ = T := by rw [← mul_assoc, hQa, hT]
    have hQbT : evenCentralSoninProjection b * T = 0 := by
      calc _ = evenCentralSoninProjection b * (evenSoninApertureLayer a b * T) := by rw [hT]
           _ = 0 := by rw [← mul_assoc, hQb, zero_mul]
    apply ContinuousLinearMap.ext
    intro v
    change T v = 0
    apply eq_zero_of_evenCentralSoninProjection_dilationSum_eq_zero
      (ha.trans_le hab) (ha.trans_le (hab.trans hbc)) hr hca
    · exact congrArg (fun A : evenSubspace →L[ℂ] evenSubspace => A v) hQaT
    · exact congrArg (fun A : evenSubspace →L[ℂ] evenSubspace => A v) hQbT
    · exact congrArg (fun A : evenSubspace →L[ℂ] evenSubspace => A v) hzero
  · rintro rfl
    exact mul_zero _

/-- At one scale, retained/lost Gram decoupling forces the successive-layer transition to vanish. -/
theorem evenSoninSuccessiveLayer_decoupling_iff
    {a b c r : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (hr : 1 < r) (hca : c ≤ r * a) :
    adjoint (evenSoninApertureSuccessiveLayerTransition a b c r hr) *
      (evenSoninApertureLayer a b * evenDilationSum r hr * evenCentralSoninProjection c) = 0 ↔
    evenSoninApertureSuccessiveLayerTransition a b c r hr = 0 := by
  have hT : evenSoninApertureLayer a b *
      evenSoninApertureSuccessiveLayerTransition a b c r hr =
      evenSoninApertureSuccessiveLayerTransition a b c r hr := by
    unfold evenSoninApertureSuccessiveLayerTransition
    rw [← mul_assoc, ← mul_assoc, evenSoninApertureLayer_mul_self hab]
  have hiff := evenSoninRetainedAdjoint_mul_eq_zero_iff ha hab hbc hr hca _ hT
  constructor
  · intro h
    apply hiff.mp
    have hadj := congrArg adjoint h
    simpa only [adjoint_mul_clm, adjoint_adjoint, ContinuousLinearMap.adjoint.map_zero] using hadj
  · rintro h
    rw [h, ContinuousLinearMap.adjoint.map_zero, zero_mul]

/-- The actual singleton Ward cubic vanishes exactly when its source transition vanishes. -/
theorem re_opTrace_singletonSoninBalancedWard_cube_eq_zero_iff
    {a b c r : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (hr : 1 < r) (hca : c ≤ r * a) :
    (opTrace (soninCoherentBalancedWardCompletion {()} a b c
      (fun _ : Unit => r) (fun _ => hr) (fun _ => 1) ^ 3)).re = 0 ↔
      evenSoninApertureSuccessiveLayerTransition a b c r hr = 0 := by
  rw [re_opTrace_soninCoherentBalancedWardCompletion_cube_eq_zero_iff
    {()} ha hab hbc (fun _ : Unit => r) (fun _ => hr) (fun _ => 1) (fun _ _ => hca)]
  have hret : soninCoherentApertureRetainedTransition {()} a b c
      (fun _ : Unit => r) (fun _ => hr) (fun _ => 1) =
      evenSoninApertureLayer a b * evenDilationSum r hr * evenCentralSoninProjection c := by
    simp only [soninCoherentApertureRetainedTransition, soninCoherentApertureLostTransition,
      Finset.sum_singleton, one_smul, evenSoninApertureLostTransition, mul_assoc,
      (evenCentralSoninProjection_mul_of_le hbc).2]
  rw [hret]
  simp only [soninCoherentApertureSuccessiveLayerTransition, Finset.sum_singleton, one_smul]
  exact evenSoninSuccessiveLayer_decoupling_iff ha hab hbc hr hca

/-- Every nonzero single-scale lost transition has strictly negative balanced cubic trace. -/
theorem re_opTrace_singletonSoninBalancedWard_cube_lt_zero_iff
    {a b c r : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (hr : 1 < r) (hca : c ≤ r * a) :
    (opTrace (soninCoherentBalancedWardCompletion {()} a b c
      (fun _ : Unit => r) (fun _ => hr) (fun _ => 1) ^ 3)).re < 0 ↔
      evenSoninApertureSuccessiveLayerTransition a b c r hr ≠ 0 := by
  have hle : (opTrace (soninCoherentBalancedWardCompletion {()} a b c
      (fun _ : Unit => r) (fun _ => hr) (fun _ => 1) ^ 3)).re ≤ 0 := by
    rw [re_opTrace_soninCoherentBalancedWardCompletion_cube
      {()} ha hab hbc (fun _ : Unit => r) (fun _ => hr) (fun _ => 1) (fun _ _ => hca)]
    exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (hsNormSq_nonneg _)
  rw [lt_iff_le_and_ne]
  simp only [hle, true_and, ne_eq,
    re_opTrace_singletonSoninBalancedWard_cube_eq_zero_iff ha hab hbc hr hca]

end RHTower
