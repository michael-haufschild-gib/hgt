import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicRamareLadderLevelTrivial

/-!
# The `L²`--`L^∞` split of a frequency window

Menon's argument bounds the frequency integral by splitting the window at a threshold: where the
polynomial is below the threshold the integral is at most `V²` times the length of the window, and
the rest is the exceptional set, on which the Ramare ladder is run.  This file supplies that split,
for an arbitrary continuous function, and names the exceptional set.

Nothing is assumed; the exceptional set is measurable because the function is continuous.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- The frequencies of the window at which a function exceeds a threshold. -/
def windowSuperLevel (F : ℝ → ℂ) (W V : ℝ) : Set ℝ :=
  Set.Icc (-W) W ∩ {w | V < ‖F w‖}

theorem measurableSet_windowSuperLevel {F : ℝ → ℂ} (hF : Continuous F) (W V : ℝ) :
    MeasurableSet (windowSuperLevel F W V) :=
  measurableSet_Icc.inter (measurableSet_lt measurable_const hF.norm.measurable)

theorem windowSuperLevel_subset (F : ℝ → ℂ) (W V : ℝ) :
    windowSuperLevel F W V ⊆ Set.Icc (-W) W := fun _ hw => hw.1

/-- A mean square over a set on which the function is bounded. -/
theorem setIntegral_normSq_le_of_bound {F : ℝ → ℂ} (hF : Continuous F) {W V : ℝ}
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W)
    (hbd : ∀ w ∈ E, ‖F w‖ ≤ V) :
    (∫ w in E, ‖F w‖ ^ 2) ≤ V ^ 2 * volume.real E := by
  classical
  have hfin : volume E ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono hEs)
    simp [Real.volume_Icc]
  have hcont : Continuous fun w : ℝ => ‖F w‖ ^ 2 := (hF.norm).pow 2
  have hint1 : IntegrableOn (fun w : ℝ => ‖F w‖ ^ 2) E volume :=
    (hcont.integrableOn_Icc (a := -W) (b := W)).mono_set hEs
  have hint2 : IntegrableOn (fun _ : ℝ => V ^ 2) E volume :=
    integrableOn_const (by exact hfin) (by simp)
  have hmono := setIntegral_mono_on hint1 hint2 hEm fun w hw =>
    pow_le_pow_left₀ (norm_nonneg _) (hbd w hw) 2
  refine hmono.trans (le_of_eq ?_)
  rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_comm]

/-- **The `L²`--`L^∞` split of the window.** -/
theorem integral_Icc_normSq_le_threshold_add_superLevel
    {F : ℝ → ℂ} (hF : Continuous F) {W V : ℝ} (hW : 0 ≤ W) :
    (∫ w in Set.Icc (-W) W, ‖F w‖ ^ 2)
      ≤ V ^ 2 * (2 * W) + ∫ w in windowSuperLevel F W V, ‖F w‖ ^ 2 := by
  classical
  set E₂ : Set ℝ := windowSuperLevel F W V with hE₂def
  set E₁ : Set ℝ := Set.Icc (-W) W ∩ {w | ‖F w‖ ≤ V} with hE₁def
  have hcont : Continuous fun w : ℝ => ‖F w‖ ^ 2 := (hF.norm).pow 2
  have hE₁m : MeasurableSet E₁ :=
    measurableSet_Icc.inter (measurableSet_le hF.norm.measurable measurable_const)
  have hE₂m : MeasurableSet E₂ := measurableSet_windowSuperLevel hF W V
  have hE₁s : E₁ ⊆ Set.Icc (-W) W := fun _ hw => hw.1
  have hE₂s : E₂ ⊆ Set.Icc (-W) W := windowSuperLevel_subset F W V
  have hdisj : Disjoint E₁ E₂ := by
    rw [Set.disjoint_left]
    rintro w ⟨-, hw1⟩ ⟨-, hw2⟩
    simp only [Set.mem_setOf_eq] at hw1 hw2
    exact absurd hw2 (not_lt.2 hw1)
  have hunion : E₁ ∪ E₂ = Set.Icc (-W) W := by
    ext w
    constructor
    · rintro (hw | hw) <;> exact hw.1
    · intro hw
      rcases le_or_gt ‖F w‖ V with h | h
      · exact Or.inl ⟨hw, h⟩
      · exact Or.inr ⟨hw, h⟩
  have hint : IntegrableOn (fun w : ℝ => ‖F w‖ ^ 2) (Set.Icc (-W) W) volume :=
    hcont.integrableOn_Icc
  have hsplit : (∫ w in Set.Icc (-W) W, ‖F w‖ ^ 2)
      = (∫ w in E₁, ‖F w‖ ^ 2) + ∫ w in E₂, ‖F w‖ ^ 2 := by
    rw [← hunion, MeasureTheory.setIntegral_union hdisj hE₂m
      (hint.mono_set (hunion ▸ Set.subset_union_left))
      (hint.mono_set (hunion ▸ Set.subset_union_right))]
  rw [hsplit]
  refine add_le_add ?_ le_rfl
  refine (setIntegral_normSq_le_of_bound hF hE₁m hE₁s fun w hw => hw.2).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hle : volume.real (Set.Icc (-W) W) = 2 * W := by
    rw [measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
    ring
  calc
    volume.real E₁ ≤ volume.real (Set.Icc (-W) W) := by
      refine measureReal_mono hE₁s ?_
      simp [Real.volume_Icc]
    _ = 2 * W := hle

end

end RHTower.Sieve
