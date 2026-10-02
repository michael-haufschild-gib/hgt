import GaloisForLFunctions.RHTower.SoninFiniteDilationSourceSupport
import GaloisForLFunctions.RHTower.SoninCoherentWardCubic

/-!
# Exact source rigidity of the full coherent Sonin Ward cubic

For every finite complex packet in the crossing chamber, retained/lost Gram
decoupling is equivalent to a zero successive-layer transition. The proof applies
the exact finite-source support law to the adjoint source, retaining every scale
and complex phase. Repeated scales and the identically zero source are handled
inside the proof.

Consequently the actual balanced Ward completion has zero cubic trace precisely
when the transition vanishes, and strictly negative cubic trace otherwise. This
is finite-source rigidity, not a cofinal prime--Gamma or Hardy-index identification.
-/

noncomputable section
namespace RHTower
open ContinuousLinearMap
variable {ι : Type*}

/-- Restriction of the literal coherent dilation source to the even carrier. -/
def soninFiniteEvenDilationSource (s : Finset ι) (r : ι → ℝ)
    (hr : ∀ i, 1 < r i) (u : ι → ℂ) : evenSubspace →L[ℂ] evenSubspace :=
  ∑ i ∈ s, u i • evenDilationSum (r i) (hr i)

/-- The even source is the restriction of the actual ambient source. -/
theorem coe_soninFiniteEvenDilationSource_apply (s : Finset ι) (r : ι → ℝ)
    (hr : ∀ i, 1 < r i) (u : ι → ℂ) (v : evenSubspace) :
    ((soninFiniteEvenDilationSource s r hr u v : evenSubspace) : SoninL2) =
      soninFiniteDilationSource s r hr u (v : SoninL2) := by
  simp only [soninFiniteEvenDilationSource, soninFiniteDilationSource,
    _root_.sum_apply, _root_.smul_apply, Submodule.coe_sum, Submodule.coe_smul,
    coe_evenDilationSum_apply]

/-- Adjoint formation conjugates the coherent coefficients without discarding any scale. -/
theorem adjoint_soninFiniteEvenDilationSource (s : Finset ι) (r : ι → ℝ)
    (hr : ∀ i, 1 < r i) (u : ι → ℂ) :
    adjoint (soninFiniteEvenDilationSource s r hr u) =
      soninFiniteEvenDilationSource s r hr (fun i => star (u i)) := by
  unfold soninFiniteEvenDilationSource
  rw [adjoint_sum_even]
  apply Finset.sum_congr rfl
  intro i hi
  change star (u i • evenDilationSum (r i) (hr i)) = _
  rw [star_smul]
  change star (u i) • adjoint (evenDilationSum (r i) (hr i)) = _
  rw [adjoint_evenDilationSum]

/-- Exact factorization of the existing coherent lost transition through its source. -/
theorem soninCoherentApertureLostTransition_eq_source (s : Finset ι) (a b : ℝ)
    (r : ι → ℝ) (hr : ∀ i, 1 < r i) (u : ι → ℂ) :
    soninCoherentApertureLostTransition s a b r hr u =
      evenSoninApertureLayer a b * soninFiniteEvenDilationSource s r hr u *
        evenCentralSoninProjection b := by
  simp only [soninCoherentApertureLostTransition, evenSoninApertureLostTransition,
    soninFiniteEvenDilationSource, Finset.mul_sum, Finset.sum_mul,
    mul_smul_even, smul_mul_even]

/-- Exact factorization of the existing successive-layer transition through its source. -/
theorem soninCoherentApertureSuccessiveLayerTransition_eq_source
    (s : Finset ι) (a b c : ℝ) (r : ι → ℝ) (hr : ∀ i, 1 < r i) (u : ι → ℂ) :
    soninCoherentApertureSuccessiveLayerTransition s a b c r hr u =
      evenSoninApertureLayer a b * soninFiniteEvenDilationSource s r hr u *
        evenSoninApertureLayer b c := by
  simp only [soninCoherentApertureSuccessiveLayerTransition, evenSoninApertureSuccessiveLayerTransition,
    soninFiniteEvenDilationSource, Finset.mul_sum, Finset.sum_mul,
    mul_smul_even, smul_mul_even]

/-- The retained source channel has no intermediate aperture factor after nesting. -/
theorem soninCoherentApertureRetainedTransition_eq_source
    (s : Finset ι) (a : ℝ) {b c : ℝ} (hbc : b ≤ c)
    (r : ι → ℝ) (hr : ∀ i, 1 < r i) (u : ι → ℂ) :
    soninCoherentApertureRetainedTransition s a b c r hr u =
      evenSoninApertureLayer a b * soninFiniteEvenDilationSource s r hr u *
        evenCentralSoninProjection c := by
  rw [soninCoherentApertureRetainedTransition, soninCoherentApertureLostTransition_eq_source,
    mul_assoc, (evenCentralSoninProjection_mul_of_le hbc).2]

private theorem even_source_eq_zero_of_ambient_eq_zero
    (s : Finset ι) (r : ι → ℝ) (hr : ∀ i, 1 < r i) (u : ι → ℂ)
    (h : soninFiniteDilationSource s r hr u = 0) :
    soninFiniteEvenDilationSource s r hr u = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  apply Subtype.ext
  rw [coe_soninFiniteEvenDilationSource_apply, h]
  rfl

private theorem coherent_transition_support (s : Finset ι) {a b c : ℝ} (hab : a ≤ b)
    (r : ι → ℝ) (hr : ∀ i, 1 < r i) (u : ι → ℂ) :
    let Z := soninCoherentApertureSuccessiveLayerTransition s a b c r hr u
    evenSoninApertureLayer a b * Z = Z ∧
      evenCentralSoninProjection a * Z = Z ∧ evenCentralSoninProjection b * Z = 0 := by
  dsimp only
  rw [soninCoherentApertureSuccessiveLayerTransition_eq_source]
  have hQa : evenCentralSoninProjection a * evenSoninApertureLayer a b =
      evenSoninApertureLayer a b := by
    rw [evenSoninApertureLayer, mul_sub,
      (evenCentralSoninProjection_mul_of_le (a := a) (b := a) le_rfl).1,
      (evenCentralSoninProjection_mul_of_le hab).2]
  have hQb : evenCentralSoninProjection b * evenSoninApertureLayer a b = 0 := by
    rw [evenSoninApertureLayer, mul_sub,
      (evenCentralSoninProjection_mul_of_le hab).1,
      (evenCentralSoninProjection_mul_of_le (a := b) (b := b) le_rfl).1, sub_self]
  simp only [← mul_assoc, evenSoninApertureLayer_mul_self hab, hQa, hQb, zero_mul, and_self]

/-- No coherent finite packet can have nontrivial retained/lost Gram decoupling.
Equal scales, vanishing combined coefficients, and arbitrary complex phases are included. -/
theorem soninCoherentApertureTransitions_decoupling_iff
    (s : Finset ι) {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (r : ι → ℝ) (hr : ∀ i, 1 < r i) (u : ι → ℂ) (hcross : ∀ i ∈ s, c ≤ r i * a) :
    adjoint (soninCoherentApertureSuccessiveLayerTransition s a b c r hr u) *
      soninCoherentApertureRetainedTransition s a b c r hr u = 0 ↔
    soninCoherentApertureSuccessiveLayerTransition s a b c r hr u = 0 := by
  constructor
  · intro hzero
    by_cases hH : soninFiniteDilationSource s r hr (fun i => star (u i)) = 0
    · have heven := even_source_eq_zero_of_ambient_eq_zero s r hr (fun i => star (u i)) hH
      rw [← adjoint_soninFiniteEvenDilationSource] at heven
      have heven' : soninFiniteEvenDilationSource s r hr u = 0 := by
        simpa only [adjoint_adjoint, ContinuousLinearMap.adjoint.map_zero] using congrArg adjoint heven
      rw [soninCoherentApertureSuccessiveLayerTransition_eq_source, heven', mul_zero, zero_mul]
    · let Z := soninCoherentApertureSuccessiveLayerTransition s a b c r hr u
      rcases coherent_transition_support s hab r hr u with ⟨hEZ, hQaZ, hQbZ⟩
      change evenSoninApertureLayer a b * Z = Z at hEZ
      change evenCentralSoninProjection a * Z = Z at hQaZ
      change evenCentralSoninProjection b * Z = 0 at hQbZ
      have hadj := congrArg adjoint hzero
      simp only [adjoint_mul_clm, adjoint_adjoint, ContinuousLinearMap.adjoint.map_zero] at hadj
      rw [soninCoherentApertureRetainedTransition_eq_source s a hbc,
        adjoint_mul_clm, adjoint_mul_clm, adjoint_evenCentralSoninProjection,
        adjoint_evenSoninApertureLayer, adjoint_soninFiniteEvenDilationSource] at hadj
      change (evenCentralSoninProjection c *
        (soninFiniteEvenDilationSource s r hr (fun i => star (u i)) * evenSoninApertureLayer a b)) * Z = 0 at hadj
      rw [mul_assoc, mul_assoc, hEZ] at hadj
      apply ContinuousLinearMap.ext
      intro v
      apply Subtype.ext
      have hQa : centralSoninProjection a (Z v : SoninL2) = (Z v : SoninL2) :=
        congrArg (fun T : evenSubspace →L[ℂ] evenSubspace => (T v : SoninL2)) hQaZ
      have hQb : centralSoninProjection b (Z v : SoninL2) = 0 :=
        congrArg (fun T : evenSubspace →L[ℂ] evenSubspace => (T v : SoninL2)) hQbZ
      have hret : centralSoninProjection c
          (soninFiniteDilationSource s r hr (fun i => star (u i)) (Z v : SoninL2)) = 0 := by
        have h := congrArg (fun T : evenSubspace →L[ℂ] evenSubspace => (T v : SoninL2)) hadj
        simpa only [mul_apply_eq_comp, coe_evenCentralSoninProjection_apply,
          coe_soninFiniteEvenDilationSource_apply, _root_.zero_apply, Submodule.coe_zero] using h
      exact eq_zero_of_soninFiniteDilationSource_retained_eq_zero s r hr (fun i => star (u i))
        (ha.trans_le hab) (ha.trans_le (hab.trans hbc)) hcross hH
        (Submodule.starProjection_eq_self_iff.mp hQa) hQb hret
  · intro h
    rw [h, ContinuousLinearMap.adjoint.map_zero, zero_mul]

/-- The full coherent balanced Ward cubic detects precisely its nonzero lost transition. -/
theorem re_opTrace_soninCoherentBalancedWardCompletion_cube_eq_zero_iff_transition
    (s : Finset ι) {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (r : ι → ℝ) (hr : ∀ i, 1 < r i) (u : ι → ℂ) (hcross : ∀ i ∈ s, c ≤ r i * a) :
    (opTrace (soninCoherentBalancedWardCompletion s a b c r hr u ^ 3)).re = 0 ↔
      soninCoherentApertureSuccessiveLayerTransition s a b c r hr u = 0 := by
  rw [re_opTrace_soninCoherentBalancedWardCompletion_cube_eq_zero_iff s ha hab hbc r hr u hcross,
    soninCoherentApertureTransitions_decoupling_iff s ha hab hbc r hr u hcross]

/-- Every nonzero coherent lost transition has strictly negative balanced cubic trace. -/
theorem re_opTrace_soninCoherentBalancedWardCompletion_cube_lt_zero_iff
    (s : Finset ι) {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (r : ι → ℝ) (hr : ∀ i, 1 < r i) (u : ι → ℂ) (hcross : ∀ i ∈ s, c ≤ r i * a) :
    (opTrace (soninCoherentBalancedWardCompletion s a b c r hr u ^ 3)).re < 0 ↔
      soninCoherentApertureSuccessiveLayerTransition s a b c r hr u ≠ 0 := by
  have hle : (opTrace (soninCoherentBalancedWardCompletion s a b c r hr u ^ 3)).re ≤ 0 := by
    rw [re_opTrace_soninCoherentBalancedWardCompletion_cube s ha hab hbc r hr u hcross]
    exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (hsNormSq_nonneg _)
  rw [lt_iff_le_and_ne]
  simp only [hle, true_and, ne_eq,
    re_opTrace_soninCoherentBalancedWardCompletion_cube_eq_zero_iff_transition s ha hab hbc r hr u hcross]

end RHTower
