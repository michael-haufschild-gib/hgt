import GaloisForLFunctions.RHTower.XiHorizontalSliceLogConcaveCone
import GaloisForLFunctions.RHTower.XiLaguerreShadowScaledDensity
import GaloisForLFunctions.RHTower.ZetaOffLineMomentNinthConsequences

/-!
# Log-concave slice coefficients on almost half of the heights

The slice coefficients `a_k(t) = c_{2k}(t)` of `ξ(½ + x + it)ξ(½ − x + it)` form a Turán sequence
(nonnegative and log-concave) at every height `t` where every zero copy satisfies
`3 (Re ρ − ½)² ≤ (Im ρ − t)²` (`xiSliceCoeff_turanSeq_of_cone`).  This fails only on the shadow
`xiShadowScaled √3` of the off-line zeros dilated by `√3`, whose measure in `[0, V]` is at most
`2√3 Σ m(ρ)(Re ρ − ½)` over the off-line zeros up to height `V + √3/2`.  With the unconditional
off-line moment `7/50` (Selberg's twisted mollifier of length `U^{1/9}`), for all large `V`

  `vol{t ∈ [0, V] : (c_{2k}(t))_k is a Turán sequence} ≥ (1 − 7√3/25) V − 21/50`

(`eventually_volume_sliceCoeff_turanSeq_ge_ninth`), a proportion `1 − 7√3/25 ≈ 0.515` of heights.
-/

open Filter Set MeasureTheory
open GaloisForLFunctions.HTGeometry

namespace RHTower.DeBruijn

noncomputable section

/-- A property holding at every real point outside a set `S` holds on measure at least `V − c` of
`[0, V]` once `S` occupies at most `c ≥ 0` of `[0, V]`. -/
theorem ofReal_sub_le_volume_of_not_mem {S : Set ℝ} {P : ℝ → Prop}
    (hP : ∀ x : ℝ, x ∉ S → P x) {V c : ℝ} (hc : 0 ≤ c)
    (hV : volume (S ∩ Icc 0 V) ≤ ENNReal.ofReal c) :
    ENNReal.ofReal (V - c) ≤ volume {x ∈ Icc (0 : ℝ) V | P x} := by
  have hsub : Icc 0 V \ (S ∩ Icc 0 V) ⊆ {x ∈ Icc (0 : ℝ) V | P x} :=
    fun x hx => ⟨hx.1, hP x fun h => hx.2 ⟨h, hx.1⟩⟩
  calc ENNReal.ofReal (V - c) = ENNReal.ofReal V - ENNReal.ofReal c := ENNReal.ofReal_sub _ hc
    _ ≤ volume (Icc (0 : ℝ) V) - volume (S ∩ Icc 0 V) := by
        rw [Real.volume_Icc, sub_zero]
        exact tsub_le_tsub_left hV _
    _ ≤ volume (Icc (0 : ℝ) V \ (S ∩ Icc 0 V)) := le_measure_sdiff
    _ ≤ _ := measure_mono hsub

/-- Off the `√3`-dilated shadow the slice coefficients form a Turán sequence. -/
theorem xiSliceCoeff_turanSeq_of_not_mem_xiShadowScaled {t : ℝ}
    (ht : t ∉ xiShadowScaled (Real.sqrt 3)) :
    TuranSeq (fun k => (xiSliceCoeff t (2 * k)).re) := by
  refine xiSliceCoeff_turanSeq_of_cone fun q => ?_
  have h := cone_of_not_mem_xiShadowScaled ht q
  rwa [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)] at h

/-- **Log-concave slices from an off-line moment bound.**  If `Σ m(ρ)(Re ρ − ½) ≤ μ V` for all large
`V`, `μ ≥ 0`, then for all large `V` the slice coefficients form a Turán sequence on height measure
at least `(1 − 2√3 μ) V − 3μ` in `[0, V]`. -/
theorem eventually_volume_sliceCoeff_turanSeq_ge_of_moment {μ : ℝ} (hμ : 0 ≤ μ)
    (hmom : ∀ᶠ V in atTop, offLineMoment V ≤ μ * V) :
    ∀ᶠ V in atTop, ENNReal.ofReal ((1 - 2 * Real.sqrt 3 * μ) * V - 3 * μ) ≤
      volume {t ∈ Icc (0 : ℝ) V | TuranSeq (fun k => (xiSliceCoeff t (2 * k)).re)} := by
  filter_upwards [eventually_volume_xiShadowScaled_inter_Icc_le_of_moment
    (Real.sqrt_nonneg 3) hmom, eventually_ge_atTop 0] with V hV hV0
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)] at hV
  have h := ofReal_sub_le_volume_of_not_mem
    (fun t ht => xiSliceCoeff_turanSeq_of_not_mem_xiShadowScaled ht)
    (by have := Real.sqrt_nonneg 3; positivity) hV
  rwa [show V - (2 * Real.sqrt 3 * μ * V + 3 * μ) = (1 - 2 * Real.sqrt 3 * μ) * V - 3 * μ by ring]
    at h

/-- **Unconditional log-concave slices on almost half of the heights.**  For all large `V`, at
heights `t ∈ [0, V]` of total measure at least `(1 − 7√3/25) V − 21/50` the coefficients `c_{2k}(t)`
of `ξ(½ + x + it)ξ(½ − x + it)` in `y = x²` are nonnegative and log-concave. -/
theorem eventually_volume_sliceCoeff_turanSeq_ge_ninth :
    ∀ᶠ V in atTop, ENNReal.ofReal ((1 - 7 * Real.sqrt 3 / 25) * V - 21 / 50) ≤
      volume {t ∈ Icc (0 : ℝ) V | TuranSeq (fun k => (xiSliceCoeff t (2 * k)).re)} :=
  (eventually_volume_sliceCoeff_turanSeq_ge_of_moment (by norm_num)
    ZetaGateProductAFE.eventually_offLineMoment_le_selberg_ninth).mono fun _ h =>
      le_trans (le_of_eq (by ring_nf)) h

end

end RHTower.DeBruijn
