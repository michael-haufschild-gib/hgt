import GaloisForLFunctions.ArithmeticElectrostatics.TheGlobalHeatDepthDissipates
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# A continuous elapsed-depth action

Subtracting the real-axis baseline makes the elapsed-depth weight vanish
at real zeros. Multiplicity conservation then gives continuity through
collisions. Uniform continuity of the moving weight, together with the
finite nonreal count on positive-time intervals, controls its time dependence.
-/

open Complex Filter Topology Set Metric
open GaloisForLFunctions.HTGeometry RHTower.DeBruijn

namespace GaloisForLFunctions.ArithmeticElectrostatics

noncomputable section

/-- Elapsed-depth weight with the real-axis baseline removed. -/
def elapsedDepthActionWeight (q c : ℝ) (z : ℂ) : ℝ :=
  (z.im ^ 2 + c) ^ q - c ^ q

/-- The full corrected action, counting both halves and analytic multiplicity. -/
def heatElapsedDepthAction (q t : ℝ) : ℝ :=
  heatWeightedZeroSum (elapsedDepthActionWeight q (2 * t)) t

private theorem elapsedDepthActionWeight_real (q c : ℝ) {z : ℂ} (hz : z.im = 0) :
    elapsedDepthActionWeight q c z = 0 := by
  simp only [elapsedDepthActionWeight, hz, zero_pow two_ne_zero, zero_add, sub_self]

private theorem continuous_elapsedDepthActionWeight (q : ℝ) {c : ℝ} (hc : 0 < c) :
    Continuous (elapsedDepthActionWeight q c) := by
  apply Continuous.sub _ continuous_const
  exact ((Complex.continuous_im.pow 2).add continuous_const).rpow_const
    (fun z => Or.inl (add_pos_of_nonneg_of_pos (sq_nonneg z.im) hc).ne')

private theorem heatWeightedZeroSum_eq_nonreal_sum {t : ℝ} (ht : 0 < t)
    (Ψ : ℂ → ℝ) (hreal : ∀ z : ℂ, z.im = 0 → Ψ z = 0) :
    heatWeightedZeroSum Ψ t =
      ∑ z ∈ (riemannHeat_nonreal_zeros_finite ht).toFinset,
        (zeroMult (riemannHeat t) z : ℝ) * Ψ z := by
  classical
  apply tsum_eq_sum
  intro z hz
  by_cases hf : riemannHeat t z = 0
  · have hi : z.im = 0 := by
      by_contra hi
      exact hz ((Set.Finite.mem_toFinset _).mpr ⟨hf, hi⟩)
    rw [hreal z hi, mul_zero]
  · rw [zeroMult_riemannHeat_eq_zero ht.le hf, Nat.cast_zero, zero_mul]

/-- Any continuous weight vanishing on the real axis has a continuous global
heat-zero sum at positive times. -/
theorem continuousOn_heatWeightedZeroSum_of_real_vanishing
    {Ψ : ℂ → ℝ} (hΨ : Continuous Ψ) (hreal : ∀ z : ℂ, z.im = 0 → Ψ z = 0) :
    ContinuousOn (heatWeightedZeroSum Ψ) (Ioi 0) := by
  intro t ht
  change 0 < t at ht
  obtain ⟨R, hR⟩ := exists_heat_nonreal_norm_bound (half_pos ht)
  let Φ : ℂ → ℝ := fun z => max 0 (min 1 (R + 1 - ‖z‖)) * Ψ z
  have hΦ : Continuous Φ := by fun_prop
  have hsupp : ∀ s : ℝ, 0 ≤ s → ∀ z : ℂ, riemannHeat s z = 0 →
      R + 1 ≤ ‖z‖ → Φ z = 0 := by
    intro s _ z _ hz
    have h : min 1 (R + 1 - ‖z‖) ≤ 0 :=
      (min_le_right _ _).trans (by linarith only [hz])
    simp only [Φ, max_eq_left h, zero_mul]
  have hc := continuous_heatWeightedZeroSum_clamped_of_support hΦ (R + 1) hsupp
  have heq : ∀ s : ℝ, t / 2 ≤ s →
      heatWeightedZeroSum Ψ s = heatWeightedZeroSum Φ (max s 0) := by
    intro s hs
    have hs0 : 0 < s := (half_pos ht).trans_le hs
    rw [max_eq_left hs0.le]
    unfold heatWeightedZeroSum
    apply tsum_congr
    intro z
    by_cases hz : riemannHeat s z = 0
    · by_cases hi : z.im = 0
      · simp only [Φ, hreal z hi, mul_zero]
      · have hn := hR s hs z hz hi
        have h1 : 1 ≤ R + 1 - ‖z‖ := by linarith only [hn]
        simp only [Φ, min_eq_left h1, max_eq_right zero_le_one, one_mul]
    · rw [zeroMult_riemannHeat_eq_zero hs0.le hz, Nat.cast_zero, zero_mul, zero_mul]
  have hevent : heatWeightedZeroSum Ψ =ᶠ[𝓝 t]
      (fun s => heatWeightedZeroSum Φ (max s 0)) := by
    filter_upwards [Ioi_mem_nhds (show t / 2 < t by linarith only [ht])] with s hs
    exact heq s hs.le
  exact (hc.continuousAt.congr hevent.symm).continuousWithinAt

private theorem heatWeightedZeroSum_sub_le_count {t η : ℝ} (ht : 0 < t)
    (Ψ Φ : ℂ → ℝ)
    (hΨ : ∀ z : ℂ, z.im = 0 → Ψ z = 0)
    (hΦ : ∀ z : ℂ, z.im = 0 → Φ z = 0)
    (hclose : ∀ z, riemannHeat t z = 0 → z.im ≠ 0 → |Ψ z - Φ z| ≤ η) :
    |heatWeightedZeroSum Ψ t - heatWeightedZeroSum Φ t| ≤
      (nonrealZeroCount t : ℝ) * η := by
  classical
  rw [heatWeightedZeroSum_eq_nonreal_sum ht Ψ hΨ,
    heatWeightedZeroSum_eq_nonreal_sum ht Φ hΦ, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ z ∈ (riemannHeat_nonreal_zeros_finite ht).toFinset,
        |(zeroMult (riemannHeat t) z : ℝ) * Ψ z -
          (zeroMult (riemannHeat t) z : ℝ) * Φ z| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ z ∈ (riemannHeat_nonreal_zeros_finite ht).toFinset,
        (zeroMult (riemannHeat t) z : ℝ) * η := by
      apply Finset.sum_le_sum
      intro z hz
      have hz' := (Set.Finite.mem_toFinset _).mp hz
      rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      exact mul_le_mul_of_nonneg_left (hclose z hz'.1 hz'.2) (Nat.cast_nonneg _)
    _ = _ := by rw [← Finset.sum_mul, ← Nat.cast_sum, ← nonrealZeroCount_eq ht]

/-- The corrected elapsed-depth action is continuous through every positive-time
collision, for every real exponent. -/
theorem continuousOn_heatElapsedDepthAction (q : ℝ) :
    ContinuousOn (heatElapsedDepthAction q) (Ioi 0) := by
  intro t ht
  change 0 < t at ht
  have ht2 := half_pos ht
  obtain ⟨R, hR⟩ := exists_heat_nonreal_norm_bound ht2
  let K := closedBall (0 : ℂ) R
  letI : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : ℂ) R)
  let F : ℝ → K → ℝ := fun s z => elapsedDepthActionWeight q (2 * max s (t / 2)) z
  have hF : Continuous (Function.uncurry F) := by
    have hc : Continuous (fun p : ℝ × K => 2 * max p.1 (t / 2)) := by fun_prop
    have hcpos (p : ℝ × K) : 0 < 2 * max p.1 (t / 2) :=
      mul_pos (by norm_num) (ht2.trans_le (le_max_right _ _))
    have hy : Continuous (fun p : ℝ × K => (p.2 : ℂ).im ^ 2) := by fun_prop
    exact ((hy.add hc).rpow_const (fun p => Or.inl
      (add_pos_of_nonneg_of_pos (sq_nonneg _) (hcpos p)).ne')).sub
      (hc.rpow_const (fun p => Or.inl (hcpos p).ne'))
  have hu := Continuous.tendstoUniformly F hF t
  have hfixed : ContinuousAt (heatWeightedZeroSum (elapsedDepthActionWeight q (2 * t))) t :=
    (continuousOn_heatWeightedZeroSum_of_real_vanishing
      (continuous_elapsedDepthActionWeight q (by positivity))
      (fun z hz => elapsedDepthActionWeight_real q (2 * t) hz) t ht).continuousAt
        (Ioi_mem_nhds ht)
  apply ContinuousAt.continuousWithinAt
  rw [Metric.continuousAt_iff]
  intro ε hε
  let M : ℝ := nonrealZeroCount (t / 2)
  have hM : 0 ≤ M := Nat.cast_nonneg _
  let η := ε / (2 * (M + 1))
  have hη : 0 < η := div_pos hε (by positivity)
  have huη := (Metric.tendstoUniformly_iff.mp hu) η hη
  obtain ⟨δ₁, hδ₁, hnear₁⟩ := Metric.eventually_nhds_iff.mp huη
  obtain ⟨δ₂, hδ₂, hnear₂⟩ := Metric.continuousAt_iff.mp hfixed (ε / 2) (half_pos hε)
  refine ⟨min (t / 2) (min δ₁ δ₂), lt_min ht2 (lt_min hδ₁ hδ₂), fun s hs => ?_⟩
  have hsabs : |s - t| < t / 2 := by
    rw [← Real.dist_eq]
    exact hs.trans_le (min_le_left _ _)
  have hst : t / 2 ≤ s := by linarith only [(abs_lt.mp hsabs).1]
  have hs0 : 0 < s := ht2.trans_le hst
  have hs₁ : dist s t < δ₁ := hs.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hs₂ : dist s t < δ₂ := hs.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hclose (z : ℂ) (hz : riemannHeat s z = 0) (hi : z.im ≠ 0) :
      |elapsedDepthActionWeight q (2 * s) z - elapsedDepthActionWeight q (2 * t) z| ≤ η := by
    have hzK : z ∈ K := by
      simpa only [K, mem_closedBall, dist_zero_right] using (hR s hst z hz hi).le
    have h := hnear₁ hs₁ ⟨z, hzK⟩
    simpa only [F, max_eq_left hst, max_eq_left (by linarith only [ht] : t / 2 ≤ t),
      Real.dist_eq, abs_sub_comm] using h.le
  have hdiff := heatWeightedZeroSum_sub_le_count hs0
    (elapsedDepthActionWeight q (2 * s)) (elapsedDepthActionWeight q (2 * t))
    (fun z hz => elapsedDepthActionWeight_real q (2 * s) hz)
    (fun z hz => elapsedDepthActionWeight_real q (2 * t) hz) hclose
  have hcount : (nonrealZeroCount s : ℝ) ≤ M := by
    dsimp only [M]
    exact_mod_cast nonrealZeroCount_antitoneOn ht2 hs0 hst
  have hsmall : M * η < ε / 2 := by
    dsimp only [η]
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith only [hε]
  have hdiff' : dist (heatElapsedDepthAction q s)
      (heatWeightedZeroSum (elapsedDepthActionWeight q (2 * t)) s) < ε / 2 := by
    rw [Real.dist_eq]
    exact (hdiff.trans (mul_le_mul_of_nonneg_right hcount hη.le)).trans_lt hsmall
  have hfixed' : dist (heatWeightedZeroSum (elapsedDepthActionWeight q (2 * t)) s)
      (heatElapsedDepthAction q t) < ε / 2 := hnear₂ hs₂
  exact (dist_triangle _ _ _).trans_lt (by
    change dist (heatElapsedDepthAction q s)
      (heatWeightedZeroSum (elapsedDepthActionWeight q (2 * t)) s) +
      dist (heatWeightedZeroSum (elapsedDepthActionWeight q (2 * t)) s)
        (heatElapsedDepthAction q t) < ε
    linarith only [hdiff', hfixed'])

#print axioms continuousOn_heatWeightedZeroSum_of_real_vanishing
#print axioms continuousOn_heatElapsedDepthAction

end

end GaloisForLFunctions.ArithmeticElectrostatics
