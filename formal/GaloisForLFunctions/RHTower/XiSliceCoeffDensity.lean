import GaloisForLFunctions.RHTower.XiHorizontalSliceConeCriterion
import GaloisForLFunctions.RHTower.XiLaguerreShadowDensity

/-!
# All-order slice positivity on more than half of the heights

RH is equivalent to the nonnegativity of every Taylor coefficient at `x = 0` of the slice product
`ξ(½ + x + it) ξ(½ − x + it)` at every height `t`.  The per-zero cone condition
`|Re ρ − ½| ≤ |Im ρ − t|` suffices (`xiSliceCoeff_nonneg_of_cone`); it fails at `t` exactly when
`t` lies in the shadow of the off-line zeros, since for `ζ = −i(ρ − ½)` the failure
`(Im ρ − t)² < (Re ρ − ½)²` reads `(Re ζ − t)² < (Im ζ)²` (`xiSliceCoeff_nonneg_of_not_mem_xiShadow`).
An off-line moment bound `Σ m(ρ)(Re ρ − ½) ≤ μ V` gives, for all large `V`,

  `vol{t ∈ [0, V] : every slice coefficient at t is ≥ 0} ≥ (1 − 2μ) V − μ`

(`eventually_volume_sliceCoeff_nonneg_ge_of_moment`); `μ = 21/100` gives `(29/50) V − 21/100`
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

/-- **All-order slice positivity from an off-line moment bound.**  If
`Σ m(ρ)(Re ρ − ½) ≤ μ V` for all large `V`, `μ ≥ 0`, then for all large `V` every slice coefficient
is nonnegative on height measure at least `(1 − 2μ) V − μ` in `[0, V]`. -/
theorem eventually_volume_sliceCoeff_nonneg_ge_of_moment {μ : ℝ} (hμ : 0 ≤ μ)
    (hmom : ∀ᶠ V in atTop, offLineMoment V ≤ μ * V) :
    ∀ᶠ V in atTop, ENNReal.ofReal ((1 - 2 * μ) * V - μ) ≤
      volume {t ∈ Icc (0 : ℝ) V | ∀ n : ℕ, 0 ≤ xiSliceCoeff t n} := by
  filter_upwards [eventually_volume_xiShadow_inter_Icc_le_of_moment hmom, eventually_ge_atTop 0]
    with V hV hV0
  have h := ofReal_sub_le_volume_of_not_mem_xiShadow
    (fun t ht => xiSliceCoeff_nonneg_of_not_mem_xiShadow ht) (by positivity) hV
  rwa [show V - (2 * μ * V + μ) = (1 - 2 * μ) * V - μ by ring] at h

/-- **All-order slice positivity on more than half of the heights.** -/
theorem eventually_volume_sliceCoeff_nonneg_ge :
    ∀ᶠ V in atTop, ENNReal.ofReal (29 / 50 * V - 21 / 100) ≤
      volume {t ∈ Icc (0 : ℝ) V | ∀ n : ℕ, 0 ≤ xiSliceCoeff t n} :=
  (eventually_volume_sliceCoeff_nonneg_ge_of_moment (by norm_num)
    ZetaGateProductAFE.eventually_offLineMoment_le).mono fun V h =>
      le_trans (le_of_eq (by congr 1; ring)) h

end

end RHTower.DeBruijn
