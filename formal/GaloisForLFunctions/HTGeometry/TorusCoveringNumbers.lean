import GaloisForLFunctions.HTGeometry.BoxDimension
import GaloisForLFunctions.HTGeometry.CompletedTimeSmallBall

/-!
# Covering numbers of a phase torus

The rational grid of `n`-th roots covers the phase torus at resolution `1/(2n)` with `n^k` points,
and Haar measure forces at least `(4ε)^{-k}` points in any `ε`-cover, because every closed ball of
radius `ε` has measure at most `(4ε)^k`.

The two bounds trap the covering number of the `k`-dimensional phase torus between constant
multiples of `ε^{-k}`, which is what identifies its box dimension with `k`.
-/

open Filter MeasureTheory Metric Set Topology
open scoped ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {k : Type*} [Fintype k] [DecidableEq k]

theorem norm_circle_le_abs (w : ℝ) : ‖((w : ℝ) : UnitAddCircle)‖ ≤ |w| := by
  rw [UnitAddCircle.norm_eq]
  simpa using round_le w 0

theorem coe_int_circle_eq_zero (z : ℤ) : (((z : ℤ) : ℝ) : UnitAddCircle) = 0 :=
  (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨z, by simp⟩

/-- The grid of `n`-th roots on the phase torus. -/
def torusGrid (k : Type*) [Fintype k] (n : ℕ) : Set (UnitAddTorus k) :=
  Set.range fun j : k → Fin n => fun i => ((((j i : ℕ) : ℝ) / (n : ℝ) : ℝ) : UnitAddCircle)

omit [DecidableEq k] in
theorem finite_torusGrid (n : ℕ) : (torusGrid k n).Finite := Set.finite_range _

theorem encard_torusGrid_le (n : ℕ) :
    (torusGrid k n).encard ≤ ((n ^ Fintype.card k : ℕ) : ℕ∞) := by
  classical
  have himg : torusGrid k n
      = (fun j : k → Fin n => fun i => ((((j i : ℕ) : ℝ) / (n : ℝ) : ℝ) : UnitAddCircle)) ''
          Set.univ := by
    rw [Set.image_univ]
    rfl
  rw [himg]
  refine le_trans (Set.encard_image_le _ _) ?_
  rw [Set.encard_univ]
  simp [Fintype.card_pi]

/-- Every circle point lies within `1/(2n)` of the grid of `n`-th roots. -/
theorem exists_circleGrid_close (n : ℕ) (hn : 0 < n) (x : UnitAddCircle) :
    ∃ j : Fin n, dist x ((((j : ℕ) : ℝ) / (n : ℝ) : ℝ) : UnitAddCircle) ≤ 1 / (2 * n) := by
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective x
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set m : ℤ := round ((n : ℝ) * u) with hm
  have hnonneg : 0 ≤ m % (n : ℤ) := Int.emod_nonneg m (by exact_mod_cast hn.ne')
  have hlt : ((m % n).toNat) < n := by
    have h2 : m % (n : ℤ) < (n : ℤ) := Int.emod_lt_of_pos m (by exact_mod_cast hn)
    omega
  refine ⟨⟨(m % n).toNat, hlt⟩, ?_⟩
  have htoNat : (((m % n).toNat : ℕ) : ℝ) = ((m % (n : ℤ) : ℤ) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hnonneg
  have hmod : ((m % (n : ℤ) : ℤ) : ℝ) = (m : ℝ) - (n : ℝ) * ((m / (n : ℤ) : ℤ) : ℝ) := by
    have hid : m % (n : ℤ) = m - (n : ℤ) * (m / (n : ℤ)) := Int.emod_def m (n : ℤ)
    rw [hid]
    push_cast
    ring
  have hgrid : ((((((m % n).toNat : ℕ) : ℝ) / (n : ℝ)) : ℝ) : UnitAddCircle)
      = (((m : ℝ) / (n : ℝ) : ℝ) : UnitAddCircle) := by
    have hdiff : (((m % n).toNat : ℕ) : ℝ) / (n : ℝ) - (m : ℝ) / (n : ℝ)
        = ((-(m / (n : ℤ)) : ℤ) : ℝ) := by
      rw [htoNat, hmod]
      push_cast
      field_simp
      ring
    have hzero : ((((((m % n).toNat : ℕ) : ℝ) / (n : ℝ)) - ((m : ℝ) / (n : ℝ)) : ℝ) :
        UnitAddCircle) = 0 := by
      rw [hdiff]
      exact coe_int_circle_eq_zero _
    have hsub : ((((((m % n).toNat : ℕ) : ℝ) / (n : ℝ)) : ℝ) : UnitAddCircle)
        - (((m : ℝ) / (n : ℝ) : ℝ) : UnitAddCircle) = 0 := by
      rw [← hzero]
      exact map_sub (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) _ _
    exact sub_eq_zero.mp hsub
  rw [hgrid, dist_eq_norm]
  have hcoe : ((u : ℝ) : UnitAddCircle) - (((m : ℝ) / (n : ℝ) : ℝ) : UnitAddCircle)
      = ((u - (m : ℝ) / (n : ℝ) : ℝ) : UnitAddCircle) :=
    (map_sub (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) _ _).symm
  rw [hcoe]
  refine le_trans (norm_circle_le_abs _) ?_
  have heq : u - (m : ℝ) / (n : ℝ) = ((n : ℝ) * u - (m : ℝ)) / (n : ℝ) := by
    field_simp
  rw [heq, abs_div, abs_of_pos hnR]
  have hround : |(n : ℝ) * u - (m : ℝ)| ≤ 1 / 2 := by
    rw [hm]
    exact abs_sub_round ((n : ℝ) * u)
  calc |(n : ℝ) * u - (m : ℝ)| / (n : ℝ) ≤ (1 / 2) / (n : ℝ) := by gcongr
    _ = 1 / (2 * n) := by
        field_simp

omit [DecidableEq k] in
/-- **The grid covers the torus.**  At resolution `1/(2n)` the `n`-th root grid is a cover. -/
theorem isCover_torusGrid (n : ℕ) (hn : 0 < n) :
    Metric.IsCover (Real.toNNReal (1 / (2 * n))) (Set.univ : Set (UnitAddTorus k))
      (torusGrid k n) := by
  intro x _
  choose j hj using fun i => exists_circleGrid_close n hn (x i)
  refine ⟨fun i => ((((j i : ℕ) : ℝ) / (n : ℝ) : ℝ) : UnitAddCircle), ⟨j, rfl⟩, ?_⟩
  have hpos : (0 : ℝ) ≤ 1 / (2 * n) := by positivity
  have hd : dist x (fun i => ((((j i : ℕ) : ℝ) / (n : ℝ) : ℝ) : UnitAddCircle))
      ≤ 1 / (2 * n) := by
    refine (dist_pi_le_iff hpos).mpr fun i => ?_
    exact hj i
  show edist x (fun i => ((((j i : ℕ) : ℝ) / (n : ℝ) : ℝ) : UnitAddCircle))
      ≤ ((Real.toNNReal (1 / (2 * n)) : ℝ≥0) : ℝ≥0∞)
  rw [edist_dist]
  exact ENNReal.ofReal_le_ofReal hd

/-- **Upper covering bound.**  The torus needs at most `n^k` balls of radius `1/(2n)`. -/
theorem externalCoveringNumber_torus_le (n : ℕ) (hn : 0 < n) :
    Metric.externalCoveringNumber (Real.toNNReal (1 / (2 * n)))
        (Set.univ : Set (UnitAddTorus k))
      ≤ ((n ^ Fintype.card k : ℕ) : ℕ∞) :=
  le_trans (Metric.IsCover.externalCoveringNumber_le_encard (isCover_torusGrid n hn))
    (encard_torusGrid_le n)

omit [DecidableEq k] in
/-- **Lower covering bound.**  Haar measure forces `(4ε)^{-k}` balls in every `ε`-cover. -/
theorem one_le_encard_mul_of_isCover_torus {ε : ℝ≥0} (hε : 0 < (ε : ℝ))
    (hε4 : (ε : ℝ) ≤ 1 / 4) {C : Set (UnitAddTorus k)} (hC : Metric.IsCover ε Set.univ C) :
    (1 : ℝ≥0∞) ≤ (C.encard : ℝ≥0∞) * ENNReal.ofReal (2 * (2 * (ε : ℝ))) ^ Fintype.card k := by
  classical
  set μ : Measure (UnitAddTorus k) :=
    ((finiteTorusHaarProbabilityMeasure k : ProbabilityMeasure (UnitAddTorus k)) :
      Measure (UnitAddTorus k)) with hμ
  have hballs : ∀ x : UnitAddTorus k,
      μ (Metric.closedBall x ε) ≤ ENNReal.ofReal (2 * (2 * (ε : ℝ))) ^ Fintype.card k := by
    intro x
    have hsub : Metric.closedBall x (ε : ℝ) ⊆ Metric.ball x (2 * (ε : ℝ)) := by
      intro y hy
      rw [Metric.mem_closedBall] at hy
      rw [Metric.mem_ball]
      linarith
    have hball := finiteTorusHaarProbabilityMeasure_ball (k := k) x
      (show (0:ℝ) < 2 * (ε : ℝ) by linarith) (show 2 * (ε : ℝ) ≤ 1 / 2 by linarith)
    calc μ (Metric.closedBall x ε) ≤ μ (Metric.ball x (2 * (ε : ℝ))) := measure_mono hsub
      _ = ENNReal.ofReal (2 * (2 * (ε : ℝ))) ^ Fintype.card k := hball
  by_cases hfin : C.Finite
  · have hmass := le_encard_of_isCover_of_measure_le μ hC hballs hfin
    have hone : μ (Set.univ : Set (UnitAddTorus k)) = 1 := by
      rw [hμ]
      exact measure_univ
    rw [hone] at hmass
    exact hmass
  · have htop : C.encard = ⊤ := Set.Infinite.encard_eq hfin
    have hmne : (ENNReal.ofReal (2 * (2 * (ε : ℝ))) ^ Fintype.card k) ≠ 0 := by
      refine pow_ne_zero _ ?_
      exact (ENNReal.ofReal_pos.mpr (by linarith)).ne'
    rw [htop]
    simp only [ENat.toENNReal_top]
    rw [ENNReal.top_mul hmne]
    exact le_top

end

end GaloisForLFunctions.HTGeometry
