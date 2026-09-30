import GaloisForLFunctions.RHTower.XiHorizontalSliceConeCriterion
import GaloisForLFunctions.RHTower.XiLaguerreShadowDensity

/-!
# All-order slice positivity on more than half of the heights

RH is equivalent to the nonnegativity of every Taylor coefficient at `x = 0` of the slice product
`ξ(½ + x + it) ξ(½ − x + it)` at every height `t`.  The per-zero cone condition
`|Re ρ − ½| ≤ |Im ρ − t|` suffices (`xiSliceCoeff_nonneg_of_cone`); it fails at `t` exactly when
`t` lies in the shadow of the off-line zeros, since for `ζ = −i(ρ − ½)` the failure
`(Im ρ − t)² < (Re ρ − ½)²` reads `(Re ζ − t)² < (Im ζ)²` (`xiSliceCoeff_nonneg_of_not_mem_xiShadow`).
With the unconditional shadow bound, for all large `V`

  `vol{t ∈ [0, V] : every slice coefficient at t is ≥ 0} ≥ (29/50) V − 21/100`

(`eventually_volume_sliceCoeff_nonneg_ge`).
-/

open Complex Filter Topology Set MeasureTheory
open scoped ComplexOrder

namespace RHTower.DeBruijn

noncomputable section

/-- Off the shadow, every slice coefficient is nonnegative. -/
theorem xiSliceCoeff_nonneg_of_not_mem_xiShadow {t : ℝ} (ht : t ∉ xiShadow) (n : ℕ) :
    0 ≤ xiSliceCoeff t n := by
  refine xiSliceCoeff_nonneg_of_cone (fun q => ?_) n
  by_contra hlt
  rw [not_le] at hlt
  apply ht
  have hq : xi (q.1 : ℂ) = 0 := xi_eq_zero_of_mem_divisor_support q.1
  refine ⟨-I * ((q.1 : ℂ) - 1 / 2), ?_, ?_⟩
  · rw [riemannHeat_zero]
    convert hq using 1
    congr 1
    ring_nf
    rw [I_sq]
    ring
  · have hre : (-I * ((q.1 : ℂ) - 1 / 2)).re = (q.1 : ℂ).im := by simp
    have him : (-I * ((q.1 : ℂ) - 1 / 2)).im = 1 / 2 - (q.1 : ℂ).re := by simp
    rw [hre, him]
    have := sq_lt_sq.mpr hlt
    nlinarith [this]

/-- **All-order slice positivity on more than half of the heights.** -/
theorem eventually_volume_sliceCoeff_nonneg_ge :
    ∀ᶠ V in atTop, ENNReal.ofReal (29 / 50 * V - 21 / 100) ≤
      volume {t ∈ Icc (0 : ℝ) V | ∀ n : ℕ, 0 ≤ xiSliceCoeff t n} := by
  filter_upwards [eventually_volume_xiShadow_inter_Icc_le, eventually_ge_atTop 0] with V hV hV0
  have hsub : Icc 0 V \ (xiShadow ∩ Icc 0 V) ⊆ {t ∈ Icc (0 : ℝ) V | ∀ n : ℕ, 0 ≤ xiSliceCoeff t n} :=
    fun t ht => ⟨ht.1, xiSliceCoeff_nonneg_of_not_mem_xiShadow fun h => ht.2 ⟨h, ht.1⟩⟩
  calc ENNReal.ofReal (29 / 50 * V - 21 / 100)
      = ENNReal.ofReal V - ENNReal.ofReal (21 / 50 * V + 21 / 100) := by
        rw [← ENNReal.ofReal_sub _ (by positivity)]
        congr 1
        ring
    _ ≤ volume (Icc (0 : ℝ) V) - volume (xiShadow ∩ Icc 0 V) := by
        rw [Real.volume_Icc, sub_zero]
        exact tsub_le_tsub_left hV _
    _ ≤ volume (Icc (0 : ℝ) V \ (xiShadow ∩ Icc 0 V)) := le_measure_sdiff
    _ ≤ _ := measure_mono hsub

end

end RHTower.DeBruijn
