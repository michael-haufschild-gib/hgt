import GaloisForLFunctions.RHTower.CHMDFullJumpMoment
import GaloisForLFunctions.RHTower.CHMDJumpGraphContractions
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Compact cutoffs for the full signed Doob graph

The actual constant ground state is a graph limit of compact C2 tests.
Every bounded function in the maximal domain admits compactly supported graph
approximants. Both statements retain the entire arithmetic edge measure.
-/

open MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower.CHMDDoobGraph
open CHMDClosedJump

def baseCutoff : ContDiffBump (0 : ℝ) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def cutoffScale (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹
def cutoff (n : ℕ) (x : ℝ) : ℝ := baseCutoff (cutoffScale n * x)

theorem cutoffScale_pos (n : ℕ) : 0 < cutoffScale n := by unfold cutoffScale; positivity
theorem cutoffScale_le_one (n : ℕ) : cutoffScale n ≤ 1 := by
  unfold cutoffScale
  exact inv_le_one_of_one_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) n])

theorem cutoff_contDiff (n : ℕ) : ContDiff ℝ 2 (cutoff n) :=
  (baseCutoff.contDiff : ContDiff ℝ 2 baseCutoff).comp (contDiff_const.mul contDiff_id)

theorem cutoff_hasCompactSupport (n : ℕ) : HasCompactSupport (cutoff n) :=
  baseCutoff.hasCompactSupport.comp_homeomorph (Homeomorph.mulLeft₀ (cutoffScale n) (cutoffScale_pos n).ne')

theorem cutoff_nonneg (n : ℕ) (x : ℝ) : 0 ≤ cutoff n x := baseCutoff.nonneg
theorem cutoff_le_one (n : ℕ) (x : ℝ) : cutoff n x ≤ 1 := baseCutoff.le_one

theorem cutoff_tendsto (x : ℝ) : Tendsto (fun n => cutoff n x) atTop (𝓝 1) := by
  have hs : Tendsto cutoffScale atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hb : baseCutoff 0 = 1 := baseCutoff.one_of_mem_closedBall (by norm_num [baseCutoff])
  simpa only [Function.comp_def, cutoff, zero_mul, hb] using
    baseCutoff.continuous.continuousAt.tendsto.comp (hs.mul_const x)

theorem exists_baseCutoff_lipschitz : ∃ C, LipschitzWith C (baseCutoff : ℝ → ℝ) :=
  ContDiff.lipschitzWith_of_hasCompactSupport baseCutoff.hasCompactSupport
    (baseCutoff.contDiff : ContDiff ℝ 2 baseCutoff) (by norm_num)

def cutoffLipschitz : NNReal := exists_baseCutoff_lipschitz.choose

theorem cutoff_difference_le (n : ℕ) (x y : ℝ) :
    |cutoff n x - cutoff n y| ≤ cutoffLipschitz * |x - y| := by
  have hb := exists_baseCutoff_lipschitz.choose_spec.norm_sub_le (cutoffScale n * x) (cutoffScale n * y)
  change _ ≤ (cutoffLipschitz : ℝ) * ‖cutoffScale n * x - cutoffScale n * y‖ at hb
  rw [← mul_sub, norm_mul, Real.norm_of_nonneg (cutoffScale_pos n).le, Real.norm_eq_abs] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left
    (mul_le_of_le_one_left (abs_nonneg _) (cutoffScale_le_one n)) (by positivity))

def cutoffLift (n : ℕ) : SourceGraph := compactLift (cutoff n) (cutoff_contDiff n) (cutoff_hasCompactSupport n)

/-- Compact C2 cutoffs recover the genuine zero-jump ground state in graph norm. -/
theorem cutoffLift_tendsto_constant : Tendsto cutoffLift atTop (𝓝 (constantLift 1)) := by
  have hs := toLp_tendsto_of_sq_dom
    (fun n => compact_memLp_mass (cutoff_contDiff n).continuous (cutoff_hasCompactSupport n))
    (memLp_const (1 : ℝ) : MemLp (fun _ : ℝ => (1 : ℝ)) 2 massMeasure)
    (integrable_const (1 : ℝ)) (fun n => ?_)
    (Eventually.of_forall cutoff_tendsto)
  · have he := toLp_tendsto_of_sq_dom
      (g := fun _ : ℝ × ℝ => (0 : ℝ))
      (fun n => compact_memLp_difference (cutoff_contDiff n) (cutoff_hasCompactSupport n))
      (MemLp.zero : MemLp (fun _ : ℝ × ℝ => (0 : ℝ)) 2 edgeMeasure)
      (memLp_displacement.integrable_sq.const_mul ((cutoffLipschitz : ℝ) ^ 2)) (fun n => ?_) ?_
    · have he' : Tendsto (fun n => (cutoffLift n).val.snd) atTop (𝓝 (constantLift 1).val.snd) := by
        rw [constantLift_edge]
        exact he
      rw [tendsto_subtype_rng]
      exact (WithLp.prod_continuous_toLp 2 _ _).continuousAt.tendsto.comp (hs.prodMk_nhds he')
    · filter_upwards with e
      have hb := cutoff_difference_le n (left e) (right e)
      have ht : |left e - right e| = |e.1| := by simp [left, right]
      rw [ht] at hb
      change (difference (cutoff n) e - 0) ^ 2 ≤ _
      dsimp only [difference]
      simpa only [sub_zero, mul_pow, sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hb
    · exact Eventually.of_forall fun e => by
        simpa only [difference, sub_self] using (cutoff_tendsto (left e)).sub (cutoff_tendsto (right e))
  filter_upwards with x
  have h0 := cutoff_nonneg n x
  have h1 := cutoff_le_one n x
  nlinarith [mul_nonneg h0 (show 0 ≤ 1 - cutoff n x by linarith)]

theorem isClosed_compactCore : IsClosed (compactCore : Set SourceGraph) :=
  Submodule.isClosed_topologicalClosure _

theorem constant_one_mem_core : constantLift 1 ∈ compactCore :=
  isClosed_compactCore.mem_of_tendsto cutoffLift_tendsto_constant
    (Eventually.of_forall fun n => compactLift_mem_core (cutoff n) (cutoff_contDiff n) (cutoff_hasCompactSupport n))

theorem constantLift_smul (c : ℝ) : constantLift c = c • constantLift 1 := by
  apply source_projection_injective
  apply Lp.ext
  have hc := (memLp_const c : MemLp (fun _ : ℝ => c) 2 massMeasure).coeFn_toLp
  have h1 := (memLp_const (1 : ℝ) : MemLp (fun _ : ℝ => (1 : ℝ)) 2 massMeasure).coeFn_toLp
  filter_upwards [hc, h1, Lp.coeFn_smul c (constantLift 1).val.fst] with x hx h1x hs
  change (memLp_const c).toLp _ x = (c • (constantLift 1).val.fst) x
  rw [hs, hx]
  change c = c * (memLp_const (1 : ℝ) : MemLp (fun _ : ℝ => (1 : ℝ)) 2 massMeasure).toLp _ x
  rw [h1x, mul_one]

theorem constant_mem_core (c : ℝ) : constantLift c ∈ compactCore := by
  rw [constantLift_smul]
  exact compactCore.smul_mem c constant_one_mem_core

def cutoffFunction (v : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ := v x * cutoff n x

theorem cutoffFunction_hasCompactSupport (v : ℝ → ℝ) (n : ℕ) :
    HasCompactSupport (cutoffFunction v n) := (cutoff_hasCompactSupport n).mul_left

theorem cutoffFunction_memLp {v : ℝ → ℝ} (hv : MemLp v 2 massMeasure) (n : ℕ) :
    MemLp (cutoffFunction v n) 2 massMeasure := by
  apply hv.mono (hv.aestronglyMeasurable.mul (cutoff_contDiff n).continuous.aestronglyMeasurable)
  exact Eventually.of_forall fun x => by
    rw [Pi.mul_apply, norm_mul, Real.norm_of_nonneg (cutoff_nonneg n x)]
    exact mul_le_of_le_one_right (norm_nonneg _) (cutoff_le_one n x)

theorem cutoffFunction_difference_bound {v : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hvM : ∀ x, |v x| ≤ M) (n : ℕ) (e : ℝ × ℝ) :
    |difference (cutoffFunction v n) e| ≤
      |difference v e| + (M * cutoffLipschitz) * |e.1| := by
  have hid : difference (cutoffFunction v n) e = difference v e * cutoff n (left e) +
      v (right e) * (cutoff n (left e) - cutoff n (right e)) := by
    unfold difference cutoffFunction
    ring
  rw [hid]
  calc
    _ ≤ |difference v e| * |cutoff n (left e)| + |v (right e)| * |cutoff n (left e) - cutoff n (right e)| := by
      simpa only [abs_mul] using abs_add_le (difference v e * cutoff n (left e))
        (v (right e) * (cutoff n (left e) - cutoff n (right e)))
    _ ≤ |difference v e| + M * ((cutoffLipschitz : ℝ) * |left e - right e|) := by
      apply add_le_add
      · rw [abs_of_nonneg (cutoff_nonneg n _)]
        exact mul_le_of_le_one_right (abs_nonneg _) (cutoff_le_one n _)
      · exact mul_le_mul (hvM _) (cutoff_difference_le n _ _) (abs_nonneg _) hM
    _ = _ := by simp [left, right]; ring

theorem cutoffFunction_memLp_difference {v : ℝ → ℝ} (hv : Measurable v)
    (hd : MemLp (difference v) 2 edgeMeasure) {M : ℝ} (hM : 0 ≤ M)
    (hvM : ∀ x, |v x| ≤ M) (n : ℕ) : MemLp (difference (cutoffFunction v n)) 2 edgeMeasure := by
  have hm : Measurable (cutoffFunction v n) := hv.mul (cutoff_contDiff n).continuous.measurable
  have hi := hd.norm.add (memLp_displacement.norm.const_mul (M * cutoffLipschitz))
  apply hi.mono ((hm.comp measurable_snd).sub (hm.comp (measurable_snd.add measurable_fst))).aestronglyMeasurable
  filter_upwards with e
  change |difference (cutoffFunction v n) e| ≤ ‖|difference v e| + M * cutoffLipschitz * |e.1|‖
  rw [Real.norm_of_nonneg (by positivity)]
  exact cutoffFunction_difference_bound hM hvM n e

def boundedCutoffLift (v : ℝ → ℝ) (hv : Measurable v) (hs : MemLp v 2 massMeasure)
    (hd : MemLp (difference v) 2 edgeMeasure) (M : ℝ) (hM : 0 ≤ M)
    (hvM : ∀ x, |v x| ≤ M) (n : ℕ) : SourceGraph :=
  ofFunction massMeasure edgeMeasure left right nonsingular_left nonsingular_right
    (cutoffFunction v n) (cutoffFunction_memLp hs n) (cutoffFunction_memLp_difference hv hd hM hvM n)

theorem boundedCutoffLift_tendsto (v : ℝ → ℝ) (hv : Measurable v) (hs : MemLp v 2 massMeasure)
    (hd : MemLp (difference v) 2 edgeMeasure) (M : ℝ) (hM : 0 ≤ M) (hvM : ∀ x, |v x| ≤ M) :
    Tendsto (boundedCutoffLift v hv hs hd M hM hvM) atTop
      (𝓝 (ofFunction massMeasure edgeMeasure left right nonsingular_left nonsingular_right v hs hd)) := by
  apply ofFunction_tendsto
  · apply toLp_tendsto_of_sq_dom _ hs (hs.integrable_sq.const_mul 4)
    · intro n
      filter_upwards with x
      have hc0 := cutoff_nonneg n x
      have hc1 := cutoff_le_one n x
      have ha : |cutoffFunction v n x| ≤ |v x| := by
        rw [cutoffFunction, abs_mul, abs_of_nonneg hc0]
        exact mul_le_of_le_one_right (abs_nonneg _) hc1
      have hsq := sq_le_sq.mpr ha
      nlinarith [sq_nonneg (cutoffFunction v n x + v x)]
    · exact Eventually.of_forall fun x => by simpa [cutoffFunction] using (cutoff_tendsto x).const_mul (v x)
  · let b := fun e : ℝ × ℝ => 2 * |difference v e| + (M * cutoffLipschitz) * |e.1|
    have hb : MemLp b 2 edgeMeasure := (hd.norm.const_mul 2).add
      (memLp_displacement.norm.const_mul (M * cutoffLipschitz))
    apply toLp_tendsto_of_sq_dom _ hd hb.integrable_sq
    · intro n
      filter_upwards with e
      have ha : |difference (cutoffFunction v n) e - difference v e| ≤ b e :=
        (abs_sub _ _).trans (by dsimp [b]; linarith [cutoffFunction_difference_bound hM hvM n e])
      change (difference (cutoffFunction v n) e - difference v e) ^ 2 ≤ b e ^ 2
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by dsimp [b]; positivity)).mpr ha
    · exact Eventually.of_forall fun e => by
        simpa [difference, cutoffFunction] using
          ((cutoff_tendsto (left e)).const_mul (v (left e))).sub
            ((cutoff_tendsto (right e)).const_mul (v (right e)))

end RHTower.CHMDDoobGraph
