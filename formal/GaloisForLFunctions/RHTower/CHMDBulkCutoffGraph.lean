import GaloisForLFunctions.RHTower.CHMDThetaRelativeGraph
import GaloisForLFunctions.RHTower.CHMDSignedGraphPolarization
import GaloisForLFunctions.RHTower.WeilPrimeBlindZeroSideIdentity

/-!
# The explicit-formula cutoffs converge in the literal CHMD graph

The same bulk cutoffs used to pass the full zero sum to noncompact sources
also converge in the complete arithmetic graph. Bounded inverse-Doob profiles
consume only the full displacement moment, with every prime atom retained.
-/

open MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower.CHMDDoobGraph
open CHMDClosedJump WeilSpectral

theorem exists_bulkCutoff_lipschitz : ∃ C : NNReal, ∀ L : ℝ, LipschitzWith C (bulkCutoff L) := by
  obtain ⟨Λ, hΛ0, hΛ⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  refine ⟨⟨2 * Λ, by positivity⟩, fun L =>
    lipschitzWith_of_nnnorm_deriv_le (fun x => (hasDerivAt_bulkCutoff L x).differentiableAt)
      fun x => ?_⟩
  change ‖deriv (bulkCutoff L) x‖ ≤ 2 * Λ
  rw [(hasDerivAt_bulkCutoff L x).deriv, Real.norm_eq_abs]
  exact abs_bulkCutoffDeriv_le hΛ L x

theorem bulkCutoff_nat_tendsto (x : ℝ) :
    Tendsto (fun n : ℕ => bulkCutoff n x) atTop (𝓝 1) := by
  have he : ∀ᶠ n : ℕ in atTop, (1 : ℝ) = bulkCutoff n x := by
    have hn := (tendsto_natCast_atTop_atTop :
      Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually_ge_atTop (|x| + 1)
    filter_upwards [hn] with n hn
    exact (bulkCutoff_eq_one (by linarith : |x| ≤ (n : ℝ) - 1)).symm
  exact tendsto_const_nhds.congr' he

theorem phiDoobInv_truncTest (f : ℝ → ℝ) (L x : ℝ) :
    phiDoobInv (truncTest f L) x = phiDoobInv f x * bulkCutoff L x := by
  dsimp only [phiDoobInv, truncTest]
  ring

theorem bulk_relative_difference_bound {f : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ x, |phiDoobInv f x| ≤ M) {B : NNReal} (hB : ∀ L, LipschitzWith B (bulkCutoff L))
    (L : ℝ) (e : ℝ × ℝ) :
    |difference (phiDoobInv (truncTest f L)) e| ≤
      |difference (phiDoobInv f) e| + M * B * |e.1| := by
  have hid : difference (phiDoobInv (truncTest f L)) e =
      difference (phiDoobInv f) e * bulkCutoff L (left e) +
        phiDoobInv f (right e) * (bulkCutoff L (left e) - bulkCutoff L (right e)) := by
    simp only [difference, phiDoobInv_truncTest]
    ring
  rw [hid]
  calc
    _ ≤ |difference (phiDoobInv f) e| * |bulkCutoff L (left e)| +
        |phiDoobInv f (right e)| * |bulkCutoff L (left e) - bulkCutoff L (right e)| := by
      simpa only [abs_mul] using abs_add_le
        (difference (phiDoobInv f) e * bulkCutoff L (left e))
        (phiDoobInv f (right e) * (bulkCutoff L (left e) - bulkCutoff L (right e)))
    _ ≤ |difference (phiDoobInv f) e| + M * ((B : ℝ) * |left e - right e|) := by
      apply add_le_add
      · rw [abs_of_nonneg (bulkCutoff_nonneg L _)]
        exact mul_le_of_le_one_right (abs_nonneg _) (bulkCutoff_le_one L _)
      · exact mul_le_mul (hb _) (by
          simpa only [Real.norm_eq_abs] using (hB L).norm_sub_le (left e) (right e))
          (abs_nonneg _) hM
    _ = _ := by simp [left, right]; ring

def bulkTestLift (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (n : ℕ) : SourceGraph :=
  testLift (truncTest f n) (contDiff_truncTest hf n) (hasCompactSupport_truncTest f n)

/-- Actual compact tests converge strongly to the theta-relative source vector. -/
theorem bulkTestLift_tendsto {f : ℝ → ℝ} (hfd : ContDiff ℝ 2 f) {A : NNReal}
    (hf : LipschitzWith A f) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ x, |f x| ≤ M * riemannKernelReal x) :
    Tendsto (bulkTestLift f hfd) atTop (𝓝 (relativeLift f hf hM hb)) := by
  obtain ⟨B, hB⟩ := exists_bulkCutoff_lipschitz
  have hs := relative_memLp_mass hf.continuous hM hb
  have hd := relative_memLp_difference hf hM hb
  have hvM := abs_phiDoobInv_le hb
  unfold bulkTestLift testLift compactLift relativeLift
  apply ofFunction_tendsto
  · apply toLp_tendsto_of_sq_dom _ hs (hs.integrable_sq.const_mul 4)
    · intro n
      filter_upwards [] with x
      have ha : |phiDoobInv (truncTest f n) x| ≤ |phiDoobInv f x| := by
        rw [phiDoobInv_truncTest, abs_mul, abs_of_nonneg (bulkCutoff_nonneg n x)]
        exact mul_le_of_le_one_right (abs_nonneg _) (bulkCutoff_le_one n x)
      have hsq := sq_le_sq.mpr ha
      change (phiDoobInv (truncTest f n) x - phiDoobInv f x) ^ 2 ≤ 4 * phiDoobInv f x ^ 2
      nlinarith [sq_nonneg (phiDoobInv (truncTest f n) x + phiDoobInv f x)]
    · exact Eventually.of_forall fun x => by
        simpa only [phiDoobInv_truncTest, mul_one] using
          (bulkCutoff_nat_tendsto x).const_mul (phiDoobInv f x)
  · let b : ℝ × ℝ → ℝ := fun e => 2 * |difference (phiDoobInv f) e| + M * B * |e.1|
    have hi : MemLp b 2 edgeMeasure := (hd.norm.const_mul 2).add
      (memLp_displacement.norm.const_mul (M * B))
    apply toLp_tendsto_of_sq_dom _ hd hi.integrable_sq
    · intro n
      filter_upwards [] with e
      have ha : |difference (phiDoobInv (truncTest f n)) e - difference (phiDoobInv f) e| ≤ b e :=
        (abs_sub _ _).trans (by
          dsimp [b]
          linarith [bulk_relative_difference_bound hM hvM hB n e])
      change (difference (phiDoobInv (truncTest f n)) e - difference (phiDoobInv f) e) ^ 2 ≤ b e ^ 2
      exact sq_le_sq.mpr (ha.trans (le_abs_self _))
    · exact Eventually.of_forall fun e => by
        simpa only [difference, phiDoobInv_truncTest, mul_one] using
          ((bulkCutoff_nat_tendsto (left e)).const_mul (phiDoobInv f (left e))).sub
            ((bulkCutoff_nat_tendsto (right e)).const_mul (phiDoobInv f (right e)))

end RHTower.CHMDDoobGraph
