import GaloisForLFunctions.goldbach.LiLiu.MellinWeight
import GaloisForLFunctions.HTGeometry.MellinTwistedTestBound
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusPrefixEnergy

/-! # Uniform squared norm of the Mellin test on the left edge -/

namespace GaloisForLFunctions.Goldbach.LiLiu
open MeasureTheory Set _root_.Complex
noncomputable section

theorem boundaryTest_continuous (φ : TestWeight) {N : ℕ} (hN : 0 < N) :
    Continuous (boundaryTest φ N) := by
  have h0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hs : Continuous (fun t : ℝ => (leftEdge N : ℂ) + t * I) := by fun_prop
  exact ((hs.const_cpow (Or.inl h0)).mul
    ((mellin_companion_differentiable φ).continuous.comp hs)).mul (continuous_const.add hs)

/-- Uniform domination by a fixed integrable function on the Mellin line. -/
theorem boundaryTest_square_majorant (φ : TestWeight) :
    ∃ g : ℝ → ℝ, Integrable g ∧ ∀ N : ℕ, 1 ≤ Real.log N → ∀ t,
      ‖boundaryTest φ N t‖ ^ 2 ≤ g t := by
  obtain ⟨D, hD, hb⟩ := boundaryTest_decay φ 1
  refine ⟨fun t => D ^ 2 * (1 + |t|) ^ (-2 : ℝ),
    (HTGeometry.TestFunctionPerron.integrable_one_add_abs_rpow (by norm_num)).const_mul _, ?_⟩
  intro N hN t
  have hp : 0 < 1 + |t| := by positivity
  have ht := hb N hN t
  rw [pow_one, mul_comm] at ht
  have hs := pow_le_pow_left₀ (norm_nonneg _) ((le_div_iff₀ hp).mpr ht) 2
  simpa only [div_pow, Real.rpow_neg hp.le, Real.rpow_two, div_eq_mul_inv] using hs

/-- The Mellin density on the left line lies in L² for every admissible modulus. -/
theorem boundaryTest_memLp (φ : TestWeight) {N : ℕ} (hN : 1 ≤ Real.log N) :
    MemLp (boundaryTest φ N) 2 volume := by
  have hpos : 0 < N := by by_contra! h; simp [Nat.eq_zero_of_le_zero h] at hN
  have hc := boundaryTest_continuous φ hpos
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  obtain ⟨g, hg, hb⟩ := boundaryTest_square_majorant φ
  apply hg.mono' (hc.norm.pow 2).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun t => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] using hb N hN t

/-- Its squared norm is bounded by a constant depending only on the original test weight. -/
theorem boundaryTest_norm_sq_bounded (φ : TestWeight) :
    ∃ C : ℝ, ∀ (N : ℕ) (hN : 1 ≤ Real.log N),
      ‖(boundaryTest_memLp φ hN).toLp (boundaryTest φ N)‖ ^ 2 ≤ C := by
  obtain ⟨g, hg, hb⟩ := boundaryTest_square_majorant φ
  refine ⟨∫ t, g t, fun N hN => ?_⟩
  have hm := boundaryTest_memLp φ hN
  rw [← _root_.RHTower.pm_integral_norm_sq_toLp hm]
  exact integral_mono ((memLp_two_iff_integrable_sq_norm hm.1).mp hm) hg (hb N hN)

#print axioms boundaryTest_norm_sq_bounded
end
end GaloisForLFunctions.Goldbach.LiLiu
