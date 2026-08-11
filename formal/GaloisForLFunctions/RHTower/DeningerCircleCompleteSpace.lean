import GaloisForLFunctions.RHTower.DeningerCircleComplete

/-!
# The circle of smooth periodic functions is complete

The `C^r` seminorms increase with `r`, so the neighbourhood filter of the origin has a basis indexed
by a single order and a radius.  Sequential completeness then upgrades to completeness, because the
uniformity is countably generated.

* `deningerPeriodicSupLe_mono` : the seminorms increase with the order.
* `DeningerCircle.hasBasis_nhds_zero` : the single-index basis.
-/

namespace RHTower

open Filter Topology GaloisForLFunctions

/-- **The `C^r` seminorms increase with `r`.** -/
theorem deningerPeriodicSupLe_mono {L : ℝ} (hL : 0 < L) {r r' : ℕ} (h : r ≤ r')
    (F : DeningerSmoothPeriodic L) :
    deningerPeriodicSupLe r F ≤ deningerPeriodicSupLe r' F := by
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (fun i hi => Finset.mem_range.2
      (lt_of_lt_of_le (Finset.mem_range.1 hi) (Nat.succ_le_succ h)))
    fun i _ _ => deningerPeriodicSup_nonneg hL i F

namespace DeningerCircle

variable {P : {x : ℝ // 0 < x}}

/-- The seminorm family is monotone. -/
theorem seminorms_mono {r r' : ℕ} (h : r ≤ r') (F : DeningerCircle P) :
    seminorms P r F ≤ seminorms P r' F :=
  deningerPeriodicSupLe_mono P.2 h (toPeriodic F)

/-- **A single-index basis of the neighbourhood filter of the origin.** -/
theorem hasBasis_nhds_zero :
    (𝓝 (0 : DeningerCircle P)).HasBasis (fun rε : ℕ × ℝ => 0 < rε.2)
      fun rε => {x : DeningerCircle P | seminorms P rε.1 x < rε.2} := by
  refine ((withSeminorms P).hasBasis_zero_ball).to_hasBasis ?_ ?_
  · rintro ⟨s, ε⟩ hε
    refine ⟨(s.sup id, ε), hε, fun x hx => ?_⟩
    simp only [Set.mem_setOf_eq] at hx
    refine (Seminorm.mem_ball_zero _).2 ?_
    refine lt_of_le_of_lt ?_ hx
    refine Finset.sup_le fun i hi => ?_
    exact fun y => seminorms_mono (Finset.le_sup (f := (id : ℕ → ℕ)) hi) y
  · rintro ⟨r, ε⟩ hε
    refine ⟨({r}, ε), hε, fun x hx => ?_⟩
    have := (Seminorm.mem_ball_zero _).1 hx
    simpa using this

end DeningerCircle

end RHTower
