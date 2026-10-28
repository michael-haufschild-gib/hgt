import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.PeriodicPairSumsOfADecreasingKernelAreLinear
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFinitePartOfTheMarkovFormAtTheSpacing
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheStabilityLawReachesTheSpacingUpToALogarithm
import GaloisForLFunctions.RHTower.WeilArchimedeanExactForm

/-!
# The archimedean cross terms vanish on periodic profiles

For an atomic test `f_x = Σ_{n ≤ N} x_n g(· − log n)` with a bump `g ≥ 0` on `[0, w]` below the
spacing, the archimedean (Lévy) energy is the self-energy of the atoms minus their interaction:

* **The exact expansion** (`levyEnergy_atomicTest_eq_cross`):
  `L(f_x) = |x|² L(g) − 2 Σ_{m<n} x_m x_n Ω(log n − log m)`, with the **cross kernel**
  `Ω(t) = ∫_0^∞ ω(s) G(s − t) ds` and `G` the autocorrelation of `g`.
* **The cross kernel** is nonnegative, decreasing in `t`, and at most `2w‖g‖²(1/t + 1)` for
  `t ≥ 4w` (`atomCrossKernel_nonneg`, `atomCrossKernel_anti`, `atomCrossKernel_le`).
* **Periodic profiles** (`abs_levyEnergy_atomicTest_sub_le_of_periodic`): for `x_n = ψ(n)/√n` with
  `ψ` `q`-periodic of mean zero and `|ψ| ≤ B`, `|L(f_x) − |x|² L(g)| ≤ 168 q B² (wN) ‖g‖²`. Since
  `|x|² ≍ log N`, the cross terms are `O(wN/log N)` per unit mass: they vanish at every fixed
  overlap ratio `wN`. On the pole `ψ = 1` they are a nonzero constant per unit mass.
-/

noncomputable section

open MeasureTheory Finset RHTower

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open GaloisForLFunctions.SpacingScaleHarmonicAnalysis GaloisForLFunctions.ArithmeticElectrostatics

variable {g : ℝ → ℝ} {w : ℝ}

/-! ### 1. The cross kernel -/

/-- The cross kernel of two atoms at log-distance `t`: `Ω(t) = ∫_0^∞ ω(s) G(s − t) ds`. -/
def atomCrossKernel (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in Set.Ioi 0, archLevyDensity s * bumpCorr g (s - t)

theorem archLevyDensity_anti {y₁ y₂ : ℝ} (h0 : 0 < y₁) (h12 : y₁ ≤ y₂) :
    archLevyDensity y₂ ≤ archLevyDensity y₁ := by
  unfold archLevyDensity
  have e1 : Real.exp (-y₂ / 2) ≤ Real.exp (-y₁ / 2) := Real.exp_le_exp.mpr (by linarith)
  have e2 : Real.exp (-2 * y₂) ≤ Real.exp (-2 * y₁) := Real.exp_le_exp.mpr (by linarith)
  have d1 : 0 < 1 - Real.exp (-2 * y₁) := by
    have : Real.exp (-2 * y₁) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  rw [div_le_div_iff₀ (by linarith) d1]
  have := Real.exp_pos (-y₂ / 2)
  nlinarith [Real.exp_pos (-y₁ / 2)]

theorem continuous_bumpCorr (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    Continuous (bumpCorr g) :=
  RHTower.ArchimedeanExactForm.continuous_autocorr hg hgc

theorem bumpCorr_nonneg (hg0 : ∀ u, 0 ≤ g u) (t : ℝ) : 0 ≤ bumpCorr g t :=
  integral_nonneg fun v => mul_nonneg (hg0 v) (hg0 _)

theorem integrableOn_crossIntegrand (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw0 : 0 < w) {t : ℝ} (ht : w < t) :
    IntegrableOn (fun s => archLevyDensity s * bumpCorr g (s - t)) (Set.Ioi 0) := by
  have hK : IntegrableOn (fun s => archLevyDensity s * bumpCorr g (s - t))
      (Set.Icc (t - w) (t + w)) :=
    ContinuousOn.integrableOn_Icc ((continuousOn_archLevyDensity_Ioi.mono fun s hs =>
      lt_of_lt_of_le (by linarith) hs.1).mul
        ((continuous_bumpCorr hg hgc).comp (continuous_sub_right t)).continuousOn)
  refine hK.of_forall_diff_eq_zero measurableSet_Ioi fun s hs => ?_
  have hs' : w < |s - t| := by
    rcases hs with ⟨-, hs2⟩
    simp only [Set.mem_Icc, not_and_or, not_le] at hs2
    rcases hs2 with h | h
    · rw [abs_sub_comm, abs_of_pos (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  rw [bumpCorr_eq_zero hgsupp hs', mul_zero]

theorem atomCrossKernel_nonneg (hg0 : ∀ u, 0 ≤ g u) (t : ℝ) : 0 ≤ atomCrossKernel g t :=
  setIntegral_nonneg measurableSet_Ioi fun s hs =>
    mul_nonneg (archLevyDensity_pos hs).le (bumpCorr_nonneg hg0 _)

/-- The cross kernel lives on the window `[t − w, t + w]`. -/
theorem atomCrossKernel_eq_window (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw0 : 0 < w)
    {t : ℝ} (ht : w < t) :
    atomCrossKernel g t = ∫ s in Set.Icc (t - w) (t + w), archLevyDensity s * bumpCorr g (s - t) := by
  rw [atomCrossKernel]
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (fun s (hs : s ∈ Set.Icc (t - w) (t + w)) => (lt_of_lt_of_le (by linarith) hs.1 : 0 < s))
    fun s hs => ?_
  have hs' : w < |s - t| := by
    rcases hs with ⟨-, hs2⟩
    simp only [Set.mem_Icc, not_and_or, not_le] at hs2
    rcases hs2 with h | h
    · rw [abs_sub_comm, abs_of_pos (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  rw [bumpCorr_eq_zero hgsupp hs', mul_zero]

/-- `Ω(t) ≤ 2w‖g‖²(1/t + 1)` for `t ≥ 4w`. -/
theorem atomCrossKernel_le (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw0 : 0 < w) {t : ℝ} (ht : 4 * w ≤ t) :
    atomCrossKernel g t ≤ 2 * w * (∫ u, g u ^ 2) * (1 / t + 1) := by
  have ht' : w < t := by linarith
  have ht0 : 0 < t := by linarith
  rw [atomCrossKernel_eq_window hgsupp hw0 ht']
  have hG : 0 ≤ ∫ u, g u ^ 2 := integral_nonneg fun u => sq_nonneg (g u)
  have hbound : ∀ s ∈ Set.Icc (t - w) (t + w),
      archLevyDensity s * bumpCorr g (s - t) ≤ (1 / t + 1) * ∫ u, g u ^ 2 := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le (by linarith) hs.1
    have h1 := archLevyDensity_le hs0
    have h2 : 1 / (2 * s) ≤ 1 / t := by
      rw [div_le_div_iff₀ (by positivity) ht0]; linarith [hs.1]
    have h3 := (abs_le.mp (abs_bumpCorr_le hg.continuous hgc (s - t))).2
    have h4 : 0 ≤ archLevyDensity s := (archLevyDensity_pos hs0).le
    calc archLevyDensity s * bumpCorr g (s - t) ≤ archLevyDensity s * ∫ u, g u ^ 2 :=
          mul_le_mul_of_nonneg_left h3 h4
      _ ≤ (1 / t + 1) * ∫ u, g u ^ 2 := mul_le_mul_of_nonneg_right (by linarith) hG
  calc ∫ s in Set.Icc (t - w) (t + w), archLevyDensity s * bumpCorr g (s - t)
      ≤ ∫ _s in Set.Icc (t - w) (t + w), (1 / t + 1) * ∫ u, g u ^ 2 :=
        setIntegral_mono_on ((integrableOn_crossIntegrand hg hgc hgsupp hw0 ht').mono_set
          fun s hs => lt_of_lt_of_le (by linarith) hs.1)
          continuousOn_const.integrableOn_Icc measurableSet_Icc hbound
    _ = 2 * w * (∫ u, g u ^ 2) * (1 / t + 1) := by
        rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
        ring

/-- The cross kernel in the coordinates of the bump: `Ω(t) = ∫_{−w}^{w} ω(τ + t) G(τ) dτ`. -/
theorem atomCrossKernel_eq_shift (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw0 : 0 < w)
    {t : ℝ} (ht : w < t) :
    atomCrossKernel g t = ∫ τ in Set.Icc (-w) w, archLevyDensity (τ + t) * bumpCorr g τ := by
  have hzero : ∀ s, s ∉ Set.Ioi 0 → archLevyDensity s * bumpCorr g (s - t) = 0 := fun s hs => by
    have : w < |s - t| := by
      rw [abs_sub_comm, abs_of_pos (by simp only [Set.mem_Ioi, not_lt] at hs; linarith)]
      simp only [Set.mem_Ioi, not_lt] at hs; linarith
    rw [bumpCorr_eq_zero hgsupp this, mul_zero]
  rw [atomCrossKernel, setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
    ← integral_add_right_eq_self (fun s => archLevyDensity s * bumpCorr g (s - t)) t]
  simp only [add_sub_cancel_right]
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun τ hτ => ?_).symm
  have : w < |τ| := by
    simp only [Set.mem_Icc, not_and_or, not_le] at hτ
    rcases hτ with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; exact h
  rw [bumpCorr_eq_zero hgsupp this, mul_zero]

/-- The cross kernel decreases in the log-distance. -/
theorem atomCrossKernel_anti (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hg0 : ∀ u, 0 ≤ g u) (hw0 : 0 < w) {t₁ t₂ : ℝ}
    (h1 : w < t₁) (h12 : t₁ ≤ t₂) : atomCrossKernel g t₂ ≤ atomCrossKernel g t₁ := by
  rw [atomCrossKernel_eq_shift hgsupp hw0 (by linarith), atomCrossKernel_eq_shift hgsupp hw0 h1]
  have hint : ∀ t, w < t → IntegrableOn (fun τ => archLevyDensity (τ + t) * bumpCorr g τ)
      (Set.Icc (-w) w) := fun t ht =>
    ContinuousOn.integrableOn_Icc ((continuousOn_archLevyDensity_Ioi.comp
      (continuous_add_const t).continuousOn fun τ hτ => by
        simp only [Set.mem_Ioi]; linarith [hτ.1]).mul (continuous_bumpCorr hg hgc).continuousOn)
  refine setIntegral_mono_on (hint t₂ (by linarith)) (hint t₁ h1) measurableSet_Icc fun τ hτ => ?_
  exact mul_le_mul_of_nonneg_right (archLevyDensity_anti (by linarith [hτ.1]) (by linarith))
    (bumpCorr_nonneg hg0 τ)

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
