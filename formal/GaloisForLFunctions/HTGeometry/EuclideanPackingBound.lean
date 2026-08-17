import GaloisForLFunctions.HTGeometry.VerticalCurvature

/-!
# The packing bound in a Euclidean ball

An `ε`-separated set inside a ball of radius `B` in `k` dimensions has at most `(1 + 2B/ε)^k`
points: the balls of radius `ε/2` around its points are disjoint and sit inside the ball of radius
`B + ε/2`, and Euclidean ball volume scales as the `k`-th power of the radius, so the common
normalizing constant cancels.

This is the entropy factor of a finite-action address bound: the address set lies in a
`k`-dimensional ball of radius `B`, so its `ε`-net has at most that many points.
-/

open MeasureTheory Metric

namespace GaloisForLFunctions.HTGeometry

section Packing

variable {k : ℕ} [NeZero k]

/-- The Euclidean ball volume constant in dimension `k`. -/
noncomputable def euclideanBallConst (k : ℕ) : ENNReal :=
  ENNReal.ofReal (Real.sqrt Real.pi ^ k / Real.Gamma ((k : ℝ) / 2 + 1))

theorem volume_ball_eq (x : EuclideanSpace ℝ (Fin k)) (r : ℝ) :
    volume (Metric.ball x r) = ENNReal.ofReal r ^ k * euclideanBallConst k := by
  have h := EuclideanSpace.volume_ball (Fin k) x r
  simpa [euclideanBallConst] using h

omit [NeZero k] in
theorem euclideanBallConst_ne_zero : euclideanBallConst k ≠ 0 := by
  have hpi : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hgamma : (0 : ℝ) < Real.Gamma ((k : ℝ) / 2 + 1) := by
    refine Real.Gamma_pos_of_pos ?_
    positivity
  rw [euclideanBallConst, ne_eq, ENNReal.ofReal_eq_zero, not_le]
  positivity

omit [NeZero k] in
theorem euclideanBallConst_ne_top : euclideanBallConst k ≠ ⊤ := by
  rw [euclideanBallConst]
  exact ENNReal.ofReal_ne_top

/-- **The packing bound.**  An `ε`-separated subset of a ball of radius `B` has at most
`(1 + 2B/ε)^k` points. -/
private theorem card_le_of_separated {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε)
    (s : Finset (EuclideanSpace ℝ (Fin k)))
    (hsub : ∀ x ∈ s, ‖x‖ ≤ B)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ε ≤ dist x y) :
    (s.card : ℝ) ≤ (1 + 2 * B / ε) ^ k := by
  have hhalf : (0 : ℝ) < ε / 2 := by positivity
  -- the small balls are pairwise disjoint
  have hdisj : (↑s : Set (EuclideanSpace ℝ (Fin k))).PairwiseDisjoint
      fun x => Metric.ball x (ε / 2) := by
    intro x hx y hy hxy
    refine Metric.ball_disjoint_ball ?_
    have := hsep x hx y hy hxy
    linarith
  -- they sit inside the enlarged ball
  have hcover : (⋃ x ∈ s, Metric.ball x (ε / 2))
      ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin k)) (B + ε / 2) := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨x, hx, hzx⟩ := hz
    have hxB : ‖x‖ ≤ B := hsub x hx
    have hdz : dist z x < ε / 2 := Metric.mem_ball.mp hzx
    rw [Metric.mem_ball, dist_zero_right]
    have htri : ‖z‖ ≤ ‖x‖ + dist z x := by
      rw [dist_eq_norm]
      calc ‖z‖ = ‖x + (z - x)‖ := by congr 1; abel
        _ ≤ ‖x‖ + ‖z - x‖ := norm_add_le _ _
    linarith
  have hmeas : ∀ b ∈ s, MeasurableSet (Metric.ball b (ε / 2)) :=
    fun b _ => measurableSet_ball
  have hsum : volume (⋃ x ∈ s, Metric.ball x (ε / 2))
      = ∑ x ∈ s, volume (Metric.ball x (ε / 2)) :=
    measure_biUnion_finset hdisj hmeas
  have hle : ∑ x ∈ s, volume (Metric.ball x (ε / 2))
      ≤ volume (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) (B + ε / 2)) := by
    rw [← hsum]
    exact measure_mono hcover
  have hconst : ∀ x : EuclideanSpace ℝ (Fin k),
      volume (Metric.ball x (ε / 2)) = ENNReal.ofReal (ε / 2) ^ k * euclideanBallConst k :=
    fun x => volume_ball_eq x (ε / 2)
  rw [Finset.sum_congr rfl fun x _ => hconst x, Finset.sum_const, nsmul_eq_mul,
    volume_ball_eq] at hle
  -- pass to real numbers
  have hCfin : euclideanBallConst k ≠ ⊤ := euclideanBallConst_ne_top
  have hLfin : (s.card : ENNReal) * (ENNReal.ofReal (ε / 2) ^ k * euclideanBallConst k) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      hCfin)
  have hRfin : ENNReal.ofReal (B + ε / 2) ^ k * euclideanBallConst k ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hCfin
  have hreal := (ENNReal.toReal_le_toReal hLfin hRfin).mpr hle
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_pow, ENNReal.toReal_natCast, ENNReal.toReal_ofReal (le_of_lt hhalf),
    ENNReal.toReal_ofReal (by positivity)] at hreal
  have hcpos : 0 < (euclideanBallConst k).toReal :=
    ENNReal.toReal_pos euclideanBallConst_ne_zero hCfin
  have hdiv : (s.card : ℝ) * (ε / 2) ^ k ≤ (B + ε / 2) ^ k := by
    nlinarith [hreal, hcpos]
  have hpow : (1 + 2 * B / ε) ^ k * (ε / 2) ^ k = (B + ε / 2) ^ k := by
    rw [← mul_pow]
    congr 1
    field_simp
    ring
  rw [← hpow] at hdiv
  exact le_of_mul_le_mul_right hdiv (pow_pos hhalf k)

/-! ## A deficient address space is null -/

section Null

open Module

variable {d : ℕ}

/-- **A subspace of deficient dimension is Lebesgue-null.**  This is the codimension hypothesis
`k_p < d` of the addressability law, in measure-theoretic form. -/
theorem volume_submodule_eq_zero (S : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hlt : finrank ℝ ↥S < d) : volume (S : Set (EuclideanSpace ℝ (Fin d))) = 0 := by
  refine Measure.addHaar_submodule volume S ?_
  intro htop
  rw [htop] at hlt
  have htopdim : finrank ℝ ↥(⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
      = finrank ℝ (EuclideanSpace ℝ (Fin d)) := finrank_top ℝ _
  rw [htopdim] at hlt
  simp at hlt

/-- Every subset of a deficient subspace is null; in particular the action-bounded address set. -/
theorem volume_subset_submodule_eq_zero {S : Submodule ℝ (EuclideanSpace ℝ (Fin d))}
    (hlt : finrank ℝ ↥S < d) {A : Set (EuclideanSpace ℝ (Fin d))}
    (hA : A ⊆ (S : Set (EuclideanSpace ℝ (Fin d)))) : volume A = 0 :=
  measure_mono_null hA (volume_submodule_eq_zero S hlt)

end Null


end Packing

end GaloisForLFunctions.HTGeometry
