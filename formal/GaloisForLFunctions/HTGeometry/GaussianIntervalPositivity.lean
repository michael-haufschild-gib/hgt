import Mathlib

/-!
# Standard Gaussian measures charge every nondegenerate box

The one-dimensional standard Gaussian density is bounded below by a positive constant on any
compact interval, so every nondegenerate interval has positive measure.  Taking products, every
nondegenerate coordinate box has positive product-Gaussian measure, and consequently the
complement of any centred sup-norm ball has positive measure.

These are the positivity facts needed to make a Gaussian small-ball shortcut bound nonvacuous;
mathlib records the density and its positivity but not the resulting set positivity.
-/

open MeasureTheory ProbabilityTheory Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Nondegenerate intervals are charged.**  The one-dimensional standard Gaussian gives positive
measure to every interval of positive length. -/
theorem gaussianReal_Icc_pos {a b : ℝ} (hab : a < b) :
    0 < gaussianReal 0 1 (Set.Icc a b) := by
  classical
  have hcont : ContinuousOn (gaussianPDFReal 0 1) (Set.Icc a b) := by
    rw [gaussianPDFReal_def]
    fun_prop
  obtain ⟨x₀, hx₀mem, hx₀min⟩ :=
    isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.mpr hab.le) hcont
  set c : ℝ := gaussianPDFReal 0 1 x₀ with hc
  have hcpos : 0 < c := gaussianPDFReal_pos 0 1 x₀ (by norm_num)
  rw [gaussianReal_apply 0 (by norm_num) (Set.Icc a b)]
  have hlow : ∀ x ∈ Set.Icc a b, ENNReal.ofReal c ≤ gaussianPDF 0 1 x := by
    intro x hx
    rw [gaussianPDF]
    exact ENNReal.ofReal_le_ofReal (hx₀min hx)
  have hmono : ∫⁻ _x in Set.Icc a b, ENNReal.ofReal c ≤
      ∫⁻ x in Set.Icc a b, gaussianPDF 0 1 x := by
    refine setLIntegral_mono_ae (by fun_prop) ?_
    filter_upwards with x hx using hlow x hx
  refine lt_of_lt_of_le ?_ hmono
  rw [setLIntegral_const]
  refine ENNReal.mul_pos ?_ ?_
  · exact (ENNReal.ofReal_pos.mpr hcpos).ne'
  · rw [Real.volume_Icc]
    exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne'

/-- **Nondegenerate boxes are charged.**  The standard product Gaussian on finitely many
coordinates gives positive measure to every coordinate box of positive side length. -/
theorem measure_pi_gaussian_box_pos {v : ℕ} (lo hi : Fin v → ℝ) (h : ∀ i, lo i < hi i) :
    0 < (Measure.pi fun _ : Fin v => gaussianReal 0 1)
      (Set.univ.pi fun i => Set.Icc (lo i) (hi i)) := by
  classical
  rw [Measure.pi_pi, pos_iff_ne_zero]
  intro hzero
  rw [Finset.prod_eq_zero_iff] at hzero
  obtain ⟨i, -, hi⟩ := hzero
  exact absurd hi (gaussianReal_Icc_pos (h i)).ne'

/-- **The Gaussian escapes every centred ball.**  In at least one coordinate the standard product
Gaussian gives positive measure to the sup-norm shell `1 ≤ ‖x‖ ≤ 2`. -/
theorem measure_pi_gaussian_shell_pos {v : ℕ} (hv : 0 < v) :
    0 < (Measure.pi fun _ : Fin v => gaussianReal 0 1)
      {x : Fin v → ℝ | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2} := by
  classical
  obtain ⟨i₀⟩ : Nonempty (Fin v) := ⟨⟨0, hv⟩⟩
  have hlt : ∀ i : Fin v,
      (if i = i₀ then (1 : ℝ) else -1) < (if i = i₀ then (2 : ℝ) else 1) := by
    intro i
    by_cases h : i = i₀
    · simp [h]
    · simp [h]
  have hsub : (Set.univ.pi fun i : Fin v =>
        Set.Icc (if i = i₀ then (1 : ℝ) else -1) (if i = i₀ then (2 : ℝ) else 1)) ⊆
      {x : Fin v → ℝ | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2} := by
    intro x hx
    have hx' : ∀ i : Fin v, x i ∈
        Set.Icc (if i = i₀ then (1 : ℝ) else -1) (if i = i₀ then (2 : ℝ) else 1) :=
      fun i => hx i (Set.mem_univ i)
    have hone : (1 : ℝ) ≤ x i₀ := by
      have := (hx' i₀).1
      simpa using this
    have htwo : x i₀ ≤ 2 := by
      have := (hx' i₀).2
      simpa using this
    refine ⟨?_, ?_⟩
    · have hle : ‖x i₀‖ ≤ ‖x‖ := norm_le_pi_norm x i₀
      have habs : (1 : ℝ) ≤ ‖x i₀‖ := by
        rw [Real.norm_eq_abs]
        exact le_trans hone (le_abs_self _)
      linarith
    · refine (pi_norm_le_iff_of_nonneg (by norm_num)).mpr fun i => ?_
      rw [Real.norm_eq_abs, abs_le]
      by_cases h : i = i₀
      · have h1 : (1 : ℝ) ≤ x i := by rw [h]; exact hone
        have h2 : x i ≤ 2 := by rw [h]; exact htwo
        constructor <;> linarith
      · have h1 : (-1 : ℝ) ≤ x i := by have := (hx' i).1; simpa [h] using this
        have h2 : x i ≤ 1 := by have := (hx' i).2; simpa [h] using this
        constructor <;> linarith
  exact lt_of_lt_of_le
    (measure_pi_gaussian_box_pos (fun i => if i = i₀ then (1 : ℝ) else -1)
      (fun i => if i = i₀ then (2 : ℝ) else 1) hlt)
    (measure_mono hsub)

end

end GaloisForLFunctions.HTGeometry
