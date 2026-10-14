import GaloisForLFunctions.HTGeometry.PaperRotationPhaseSlope
import GaloisForLFunctions.HTGeometry.UnitIntervalRiemannLimit

/-! # Finite phase packets and their sampled energy

The frequency set is fixed while coefficients may converge. Uniform bounds
on the coefficients control both the quadrature and coefficient errors.
-/

namespace GaloisForLFunctions.HTGeometry
open Filter Topology MeasureTheory
noncomputable section

def finitePhasePacket {ι : Type*} (s : Finset ι) (a : ι → ℂ) (ω : ι → ℝ) (x : ℝ) : ℂ :=
  ∑ i ∈ s, a i * paperRotationPhase (ω i * x)

def finitePhaseEnergy {ι : Type*} (s : Finset ι) (a : ι → ℂ) (ω : ι → ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, ‖finitePhasePacket s a ω x‖ ^ 2

def finitePhaseSampleEnergy {ι : Type*} (s : Finset ι) (a : ι → ℂ) (ω : ι → ℝ)
    (n : ℕ) : ℝ :=
  (1 / ((n : ℝ) + 1)) * ∑ j ∈ Finset.range (n + 1),
    ‖finitePhasePacket s a ω ((j : ℝ) / ((n : ℝ) + 1))‖ ^ 2

theorem finitePhasePacket_norm_le {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (ω : ι → ℝ) (x : ℝ) : ‖finitePhasePacket s a ω x‖ ≤ ∑ i ∈ s, ‖a i‖ := by
  simpa [finitePhasePacket, norm_mul] using
    norm_sum_le s (fun i => a i * paperRotationPhase (ω i * x))

theorem finitePhasePacket_sub_norm_le {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (ω : ι → ℝ) (x y : ℝ) :
    ‖finitePhasePacket s a ω x - finitePhasePacket s a ω y‖ ≤
      (∑ i ∈ s, ‖a i‖ * |ω i|) * |x - y| := by
  rw [finitePhasePacket, finitePhasePacket, ← Finset.sum_sub_distrib, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [← mul_sub, norm_mul]
  have h := paperRotationPhase_sub_norm_le (ω i * x) (ω i * y)
  rw [← mul_sub, abs_mul] at h
  exact (mul_le_mul_of_nonneg_left h (norm_nonneg _)).trans_eq (by ring)

theorem finitePhasePacket_lipschitz {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (ω : ι → ℝ) :
    LipschitzWith (Real.toNNReal (∑ i ∈ s, ‖a i‖ * |ω i|)) (finitePhasePacket s a ω) := by
  apply LipschitzWith.of_dist_le'
  intro x y
  simpa only [dist_eq_norm, Real.norm_eq_abs] using finitePhasePacket_sub_norm_le s a ω x y

theorem abs_norm_sq_sub_norm_sq_le (u v : ℂ) :
    |‖u‖ ^ 2 - ‖v‖ ^ 2| ≤ (‖u‖ + ‖v‖) * ‖u - v‖ := by
  rw [show ‖u‖ ^ 2 - ‖v‖ ^ 2 = (‖u‖ + ‖v‖) * (‖u‖ - ‖v‖) by ring,
    abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  exact mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le u v)
    (add_nonneg (norm_nonneg _) (norm_nonneg _))

theorem finitePhasePacket_energy_lipschitz {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (ω : ι → ℝ) :
    LipschitzWith (Real.toNNReal
      (2 * (∑ i ∈ s, ‖a i‖) * (∑ i ∈ s, ‖a i‖ * |ω i|)))
      (fun x => ‖finitePhasePacket s a ω x‖ ^ 2) := by
  apply LipschitzWith.of_dist_le'
  intro x y
  rw [Real.dist_eq, Real.dist_eq]
  refine (abs_norm_sq_sub_norm_sq_le _ _).trans ?_
  calc
    _ ≤ (2 * ∑ i ∈ s, ‖a i‖) *
        ((∑ i ∈ s, ‖a i‖ * |ω i|) * |x - y|) := by
      apply mul_le_mul
      · linarith [finitePhasePacket_norm_le s a ω x, finitePhasePacket_norm_le s a ω y]
      · exact finitePhasePacket_sub_norm_le s a ω x y
      · exact norm_nonneg _
      · positivity
    _ = _ := by ring

theorem finitePhasePacket_sub_coeff_norm_le {ι : Type*} (s : Finset ι) (a b : ι → ℂ)
    (ω : ι → ℝ) (x : ℝ) :
    ‖finitePhasePacket s a ω x - finitePhasePacket s b ω x‖ ≤ ∑ i ∈ s, ‖a i - b i‖ := by
  rw [finitePhasePacket, finitePhasePacket, ← Finset.sum_sub_distrib]
  simpa only [← sub_mul, norm_mul, paperRotationPhase_norm, mul_one] using
    norm_sum_le s (fun i => a i * paperRotationPhase (ω i * x) -
      b i * paperRotationPhase (ω i * x))

theorem finitePhaseSampleEnergy_tendsto {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (ω : ι → ℝ) :
    Tendsto (finitePhaseSampleEnergy s a ω) atTop (𝓝 (finitePhaseEnergy s a ω)) :=
  tendsto_real_unitRiemannSum (finitePhasePacket_energy_lipschitz s a ω)

theorem abs_unit_sample_difference_le (f g : ℝ → ℝ) (n : ℕ) {D : ℝ}
    (h : ∀ x, |f x - g x| ≤ D) :
    |(1 / ((n : ℝ) + 1)) * ∑ j ∈ Finset.range (n + 1), f (j / ((n : ℝ) + 1)) -
      (1 / ((n : ℝ) + 1)) * ∑ j ∈ Finset.range (n + 1), g (j / ((n : ℝ) + 1))| ≤ D := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_pos (one_div_pos.mpr hn)]
  calc
    _ ≤ (1 / ((n : ℝ) + 1)) * ∑ j ∈ Finset.range (n + 1), D := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc
        _ ≤ ∑ j ∈ Finset.range (n + 1),
            |f (j / ((n : ℝ) + 1)) - g (j / ((n : ℝ) + 1))| := by
          simpa only [Real.norm_eq_abs] using norm_sum_le (Finset.range (n + 1))
            (fun j => f (j / ((n : ℝ) + 1)) - g (j / ((n : ℝ) + 1)))
        _ ≤ _ := Finset.sum_le_sum fun j _ => h _
    _ = D := by simp; field_simp

theorem finitePhaseSampleEnergy_coeff_tendsto {ι : Type*} (s : Finset ι)
    (a : ℕ → ι → ℂ) (b : ι → ℂ) (ω : ι → ℝ) {B : ℝ}
    (hB : 0 ≤ B) (ha : ∀ n, ∑ i ∈ s, ‖a n i‖ ≤ B)
    (hb : ∑ i ∈ s, ‖b i‖ ≤ B)
    (hlim : ∀ i ∈ s, Tendsto (fun n => a n i) atTop (𝓝 (b i))) :
    Tendsto (fun n => finitePhaseSampleEnergy s (a n) ω n) atTop
      (𝓝 (finitePhaseEnergy s b ω)) := by
  have herr : Tendsto (fun n => ∑ i ∈ s, ‖a n i - b i‖) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum s (fun i hi => ((hlim i hi).sub_const (b i)).norm)
  have hbound (n : ℕ) :
      |finitePhaseSampleEnergy s (a n) ω n - finitePhaseSampleEnergy s b ω n| ≤
        (2 * B) * ∑ i ∈ s, ‖a n i - b i‖ := by
    apply abs_unit_sample_difference_le
      (fun x => ‖finitePhasePacket s (a n) ω x‖ ^ 2)
      (fun x => ‖finitePhasePacket s b ω x‖ ^ 2) n
    intro x
    refine (abs_norm_sq_sub_norm_sq_le _ _).trans ?_
    apply mul_le_mul
    · linarith [(finitePhasePacket_norm_le s (a n) ω x).trans (ha n),
        (finitePhasePacket_norm_le s b ω x).trans hb]
    · exact finitePhasePacket_sub_coeff_norm_le s (a n) b ω x
    · exact norm_nonneg _
    · positivity
  have hd : Tendsto (fun n => finitePhaseSampleEnergy s (a n) ω n -
      finitePhaseSampleEnergy s b ω n) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) hbound
      (by simpa using herr.const_mul (2 * B))
  have h := hd.add (finitePhaseSampleEnergy_tendsto s b ω)
  simpa only [sub_add_cancel, zero_add] using h

end
end GaloisForLFunctions.HTGeometry
