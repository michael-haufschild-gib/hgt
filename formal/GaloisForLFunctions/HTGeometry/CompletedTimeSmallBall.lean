import GaloisForLFunctions.HTGeometry.CompletedObserverTimeTorus

/-!
# The small-ball law of completed time

Haar measure of a ball of radius `ε ≤ 1/2` in the phase torus is exactly `(2ε)^{card}`: the ball is
the product of circle balls, and a circle ball of small radius is the image of an interval of twice
its radius in the fundamental domain.

Applied to the presenting torus of a completed observer time, this is the exact form of the
return-volume law: the asymptotic fraction of clock labels landing within `ε` of a prescribed phase
is `(2ε)^{d_O}`, so the exponent reads off the temporal dimension.
-/

open Filter MeasureTheory Metric Set Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {k : Type*} [Fintype k]

theorem volume_eq_haarAddCircle : (volume : Measure UnitAddCircle) = AddCircle.haarAddCircle := by
  rw [AddCircle.volume_eq_smul_haarAddCircle]
  simp

/-- In the fundamental domain, the small ball around zero of the unit circle is the interval of
twice its radius. -/
theorem preimage_mk_ball_zero_inter {ε : ℝ} (hε' : ε ≤ 1 / 2) :
    (((↑) : ℝ → UnitAddCircle) ⁻¹' (ball 0 ε)) ∩ Ioc (-(1 / 2) : ℝ) (-(1 / 2) + 1)
      = Ioo (-ε) ε := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage, mem_ball, dist_zero_right, Set.mem_Ioc,
    Set.mem_Ioo]
  constructor
  · rintro ⟨hnorm, hx1, hx2⟩
    rw [UnitAddCircle.norm_eq] at hnorm
    by_cases hhalf : x = 1 / 2
    · subst hhalf
      rw [show round (1 / 2 : ℝ) = 1 by
        norm_num [round_eq]] at hnorm
      norm_num at hnorm
      constructor <;> linarith
    · have hround : round x = 0 := by
        rw [round_eq_zero_iff]
        constructor
        · linarith
        · rcases lt_or_eq_of_le (by linarith : x ≤ 1 / 2) with h | h
          · exact h
          · exact absurd h hhalf
      rw [hround] at hnorm
      simp only [Int.cast_zero, sub_zero] at hnorm
      constructor
      · linarith [neg_abs_le x, abs_lt.mp hnorm |>.1]
      · exact (abs_lt.mp hnorm).2
  · rintro ⟨hx1, hx2⟩
    have hround : round x = 0 := by
      rw [round_eq_zero_iff]
      constructor <;> linarith
    refine ⟨?_, by linarith, by linarith⟩
    rw [UnitAddCircle.norm_eq, hround]
    simp only [Int.cast_zero, sub_zero]
    exact abs_lt.mpr ⟨hx1, hx2⟩

/-- **Circle small-ball law.**  A ball of radius at most one half has Haar measure twice its
radius. -/
theorem haarAddCircle_ball_zero {ε : ℝ} (hε' : ε ≤ 1 / 2) :
    (AddCircle.haarAddCircle : Measure UnitAddCircle) (ball 0 ε) = ENNReal.ofReal (2 * ε) := by
  have hmp := AddCircle.measurePreserving_mk (T := 1) (t := -(1 / 2))
  have hpre := hmp.measure_preimage
    (measurableSet_ball (x := (0 : UnitAddCircle)) (ε := ε)).nullMeasurableSet
  rw [← volume_eq_haarAddCircle, ← hpre,
    Measure.restrict_apply
      (measurableSet_preimage (AddCircle.measurable_mk' (a := (1 : ℝ))) measurableSet_ball),
    preimage_mk_ball_zero_inter hε', Real.volume_Ioo]
  congr 1
  ring

theorem haarAddCircle_ball (x : UnitAddCircle) {ε : ℝ} (hε' : ε ≤ 1 / 2) :
    (AddCircle.haarAddCircle : Measure UnitAddCircle) (ball x ε) = ENNReal.ofReal (2 * ε) := by
  have h := MeasureTheory.measure_preimage_add
    (AddCircle.haarAddCircle : Measure UnitAddCircle) x (ball x ε)
  rw [preimage_add_ball] at h
  simp only [sub_self] at h
  rw [← h]
  exact haarAddCircle_ball_zero hε'

/-- **Small-ball law of completed time.**  Haar measure of a ball of radius `ε ≤ 1/2` in a phase
torus is `(2ε)` to the power of its dimension. -/
theorem finiteTorusHaarProbabilityMeasure_ball (x : UnitAddTorus k) {ε : ℝ} (hε : 0 < ε)
    (hε' : ε ≤ 1 / 2) :
    (finiteTorusHaarProbabilityMeasure k : Measure (UnitAddTorus k)) (ball x ε)
      = ENNReal.ofReal (2 * ε) ^ Fintype.card k := by
  show (Measure.pi fun _ => AddCircle.haarAddCircle) (ball x ε) = _
  rw [ball_pi x hε, Measure.pi_pi]
  rw [Finset.prod_congr rfl fun i (_ : i ∈ Finset.univ) => haarAddCircle_ball (x i) hε']
  rw [Finset.prod_const, Finset.card_univ]

end

end GaloisForLFunctions.HTGeometry
