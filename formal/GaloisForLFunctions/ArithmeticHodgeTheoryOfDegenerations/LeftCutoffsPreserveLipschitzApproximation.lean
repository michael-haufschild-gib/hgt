import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.SampledJumpsAdmitLipschitzApproximation
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.ContinuousWindowsAdmitCompactLipschitzApproximation

/-!
# Compact Lipschitz approximation with a prescribed left cutoff

A fixed affine cutoff vanishes below its left endpoint and equals one two units
later. Multiplying a compact Lipschitz approximant by this cutoff preserves its
uniform error and gives the exact support needed by atomic adjoint synthesis.
-/

set_option autoImplicit false
noncomputable section
open Set
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

/-- An ascending cutoff with transition interval `[a,a+2]`. -/
def leftProfileCutoff (a u : ℝ) : ℝ := 1 - descendingRamp (a + 1) 1 u

lemma leftProfileCutoff_bounds (a u : ℝ) :
    0 ≤ leftProfileCutoff a u ∧ leftProfileCutoff a u ≤ 1 := by
  obtain ⟨h0, h1⟩ := descendingRamp_bounds (a + 1) 1 u
  dsimp only [leftProfileCutoff]
  constructor <;> linarith only [h0, h1]

lemma leftProfileCutoff_eq_zero {a u : ℝ} (hu : u ≤ a) : leftProfileCutoff a u = 0 := by
  unfold leftProfileCutoff
  rw [descendingRamp_eq_one (by norm_num : (0 : ℝ) < 1) (by linarith only [hu]), sub_self]

lemma leftProfileCutoff_eq_one {a u : ℝ} (hu : a + 2 ≤ u) : leftProfileCutoff a u = 1 := by
  unfold leftProfileCutoff
  rw [descendingRamp_eq_zero (by norm_num : (0 : ℝ) < 1) (by linarith only [hu]), sub_zero]

lemma abs_leftProfileCutoff_sub_le (a u v : ℝ) :
    |leftProfileCutoff a u - leftProfileCutoff a v| ≤ (1 / 2 : ℝ) * |u - v| := by
  have hh := (lipschitzWith_descendingRamp (by norm_num : (0 : ℝ) < 1) (a + 1)).dist_le_mul u v
  norm_num only [Real.dist_eq, mul_one, Real.coe_toNNReal _ (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hh
  unfold leftProfileCutoff
  have he (x y : ℝ) : (1 - x) - (1 - y) = -(x - y) := by ring
  rw [he, abs_neg]
  exact hh

/-- A continuous target on a compact interval admits compact Lipschitz approximants after a
fixed left cutoff, with exact vanishing below that endpoint. -/
theorem exists_compact_leftCutoff_lipschitz_approximation {g : ℝ → ℝ} {a b ε : ℝ}
    (hg : ContinuousOn g (Icc a b)) (hε : 0 < ε) :
    ∃ f : ℝ → ℝ, ∃ K : NNReal, HasCompactSupport f ∧ LipschitzWith K f ∧
      (∀ u, u ≤ a → f u = 0) ∧
      ∀ u ∈ Icc a b, |f u - leftProfileCutoff a u * g u| < ε := by
  obtain ⟨P, L, hPd, hPc, hPL, happrox⟩ := exists_compact_lipschitz_uniform_approximation hg hε
  obtain ⟨M₀, hM₀⟩ := hPd.continuous.bounded_above_of_compact_support hPc
  let M := max M₀ 0
  have hM : 0 ≤ M := le_max_right _ _
  have hPb : ∀ u, |P u| ≤ M := fun u => by
    simpa only [Real.norm_eq_abs] using (hM₀ u).trans (le_max_left _ _)
  let f := fun u => leftProfileCutoff a u * P u
  have hfc : HasCompactSupport f := hPc.mono fun u hu => by
    rw [Function.mem_support] at hu ⊢
    intro hz
    exact hu (by dsimp only [f]; rw [hz, mul_zero])
  have hLip : LipschitzWith (Real.toNNReal ((L : ℝ) + M / 2)) f := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
    have hcut : |leftProfileCutoff a u| ≤ 1 := by
      rw [abs_of_nonneg (leftProfileCutoff_bounds a u).1]
      exact (leftProfileCutoff_bounds a u).2
    have hPL' : |P u - P v| ≤ (L : ℝ) * |u - v| := by
      simpa only [Real.dist_eq] using hPL.dist_le_mul u v
    have hp := mul_le_mul hcut hPL' (abs_nonneg _) zero_le_one
    have hq := mul_le_mul (abs_leftProfileCutoff_sub_le a u v) (hPb v)
      (abs_nonneg _) (by positivity)
    simp only [one_mul, ← abs_mul] at hp hq
    have he : f u - f v = leftProfileCutoff a u * (P u - P v) +
        (leftProfileCutoff a u - leftProfileCutoff a v) * P v := by dsimp only [f]; ring
    rw [he]
    exact ((abs_add_le _ _).trans (add_le_add hp hq)).trans_eq (by ring)
  refine ⟨f, _, hfc, hLip, ?_, ?_⟩
  · intro u hu
    dsimp only [f]
    rw [leftProfileCutoff_eq_zero hu, zero_mul]
  · intro u hu
    have hcut : |leftProfileCutoff a u| ≤ 1 := by
      rw [abs_of_nonneg (leftProfileCutoff_bounds a u).1]
      exact (leftProfileCutoff_bounds a u).2
    have he : f u - leftProfileCutoff a u * g u = leftProfileCutoff a u * (P u - g u) := by
      dsimp only [f]
      ring
    rw [he, abs_mul]
    exact ((mul_le_mul_of_nonneg_right hcut (abs_nonneg _)).trans_eq (one_mul _)).trans_lt (happrox u hu)

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
