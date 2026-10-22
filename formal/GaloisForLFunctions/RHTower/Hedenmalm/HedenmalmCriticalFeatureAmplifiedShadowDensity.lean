import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCriticalFeatureGaussianAmplifiedReceiver
import GaloisForLFunctions.RHTower.XiLaguerreShadowScaledDensity
import GaloisForLFunctions.RHTower.ZetaOffLineMomentSelbergWeights
import GaloisForLFunctions.RHTower.ZetaOffLineMomentSelbergUpper

/-!
# The amplified HCF ceiling holds off the Laguerre shadow, on at least `33/50` of all heights

The local light-cone law (`criticalFeatureGaussianAmplifiedTrace_bounded_iff`) says the amplified
critical-feature diagonal `σ ↦ Σ_γ F_t(γ)² exp(-σ(γ - t)²)` is bounded exactly when no zero lies in
the open cone `|Re γ - t| < |Im γ|` over the height `t`.  The union of these cones over all
off-line zeros is the Laguerre shadow `xiShadow` of `Ξ`.  So the exact amplified HCF layer and the
Laguerre–Pólya shadow receiver coincide height by height.

* `criticalFeatureGaussianAmplifiedTrace_bounded_of_not_mem_xiShadow`: off the shadow the amplified
  diagonal is bounded by the Hermitian feature energy for every amplification.
* `eventually_volume_unbounded_amplifiedTrace_le`: the heights in `[0, V]` where the amplified
  ceiling fails have measure at most `(17/50)(V + 1/2)` for all large `V`.  The bound comes from
  `vol(xiShadow ∩ [0, V]) ≤ 2 Σ m(ρ)(Re ρ - 1/2)` and the Selberg-weight off-line moment bound
  `Σ m(ρ)(Re ρ - 1/2) ≤ (17/100) V`.

RH is the statement that the exceptional set is empty.  These results give its unconditional density
form: the amplified HCF ceiling holds on at least `33/50` of all heights, and on at least `433/500`
with the sharper Selberg-weight moment `Σ m(ρ)(Re ρ - 1/2) ≤ (67/1000) V`
(`eventually_volume_unbounded_amplifiedTrace_le_sharp`).
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

/-- **Off the Laguerre shadow the amplified HCF diagonal is bounded.** -/
theorem criticalFeatureGaussianAmplifiedTrace_bounded_of_not_mem_xiShadow {t : ℝ}
    (ht : t ∉ DeBruijn.xiShadow) :
    ∃ C : ℝ, ∀ σ : ℝ, 0 ≤ σ → ‖criticalFeatureGaussianAmplifiedTrace t σ‖ ≤ C := by
  refine (criticalFeatureGaussianAmplifiedTrace_bounded_iff t).2 fun q => ?_
  have hscaled : t ∉ DeBruijn.xiShadowScaled 1 := by
    rintro ⟨ζ, hζ, hlt⟩
    exact ht ⟨ζ, hζ, by simpa using hlt⟩
  have hcone := DeBruijn.cone_of_not_mem_xiShadowScaled hscaled q
  rw [one_pow, one_mul] at hcone
  have hre : (xiSpectralPoint q).re = (q.1 : ℂ).im := by
    rw [xiSpectralPoint]; simp [Complex.mul_re]
  rw [xiSpectralPoint_im_eq, hre]
  rw [show (1 / 2 - (q.1 : ℂ).re) = -((q.1 : ℂ).re - 1 / 2) by ring, abs_neg]
  exact sq_le_sq.1 hcone

/-- The heights at which the amplified HCF ceiling fails lie in the Laguerre shadow. -/
theorem setOf_unbounded_amplifiedTrace_subset_xiShadow :
    {t : ℝ | ¬ ∃ C : ℝ, ∀ σ : ℝ, 0 ≤ σ → ‖criticalFeatureGaussianAmplifiedTrace t σ‖ ≤ C} ⊆
      DeBruijn.xiShadow := fun t ht => by
  by_contra hshadow
  exact ht (criticalFeatureGaussianAmplifiedTrace_bounded_of_not_mem_xiShadow hshadow)

/-- **Density of the amplified HCF ceiling.**  For all large `V` the heights in `[0, V]` at which
the amplified critical-feature diagonal is unbounded have measure at most `(17/50)(V + 1/2)`. -/
theorem eventually_volume_unbounded_amplifiedTrace_le :
    ∀ᶠ V : ℝ in atTop,
      volume ({t : ℝ | ¬ ∃ C : ℝ, ∀ σ : ℝ, 0 ≤ σ →
          ‖criticalFeatureGaussianAmplifiedTrace t σ‖ ≤ C} ∩ Icc 0 V) ≤
        ENNReal.ofReal (17 / 50 * (V + 1 / 2)) := by
  have hmom := ZetaGateProductAFE.eventually_offLineMoment_le_selberg
  have hshift : ∀ᶠ V : ℝ in atTop, offLineMoment (V + 1 / 2) ≤ 17 / 100 * (V + 1 / 2) :=
    (tendsto_atTop_add_const_right atTop (1 / 2) tendsto_id).eventually hmom
  filter_upwards [hshift] with V hV
  calc volume ({t : ℝ | ¬ ∃ C : ℝ, ∀ σ : ℝ, 0 ≤ σ →
          ‖criticalFeatureGaussianAmplifiedTrace t σ‖ ≤ C} ∩ Icc 0 V)
      ≤ volume (DeBruijn.xiShadow ∩ Icc 0 V) :=
        measure_mono (inter_subset_inter_left _ setOf_unbounded_amplifiedTrace_subset_xiShadow)
    _ ≤ ENNReal.ofReal (2 * offLineMoment (V + 1 / 2)) :=
        DeBruijn.volume_xiShadow_inter_Icc_le_offLineMoment V
    _ ≤ ENNReal.ofReal (17 / 50 * (V + 1 / 2)) :=
        ENNReal.ofReal_le_ofReal (by linarith)

/-- **Sharper density.**  With the off-line moment bound `(67/1000) V` the heights in `[0, V]` at
which the amplified HCF diagonal is unbounded have measure at most `(67/500)(V + 1/2)`. -/
theorem eventually_volume_unbounded_amplifiedTrace_le_sharp :
    ∀ᶠ V : ℝ in atTop,
      volume ({t : ℝ | ¬ ∃ C : ℝ, ∀ σ : ℝ, 0 ≤ σ →
          ‖criticalFeatureGaussianAmplifiedTrace t σ‖ ≤ C} ∩ Icc 0 V) ≤
        ENNReal.ofReal (67 / 500 * (V + 1 / 2)) := by
  have hmom := ZetaGateProductAFE.eventually_offLineMoment_le_selberg_upper
  have hshift : ∀ᶠ V : ℝ in atTop, offLineMoment (V + 1 / 2) ≤ 67 / 1000 * (V + 1 / 2) :=
    (tendsto_atTop_add_const_right atTop (1 / 2) tendsto_id).eventually hmom
  filter_upwards [hshift] with V hV
  calc volume ({t : ℝ | ¬ ∃ C : ℝ, ∀ σ : ℝ, 0 ≤ σ →
          ‖criticalFeatureGaussianAmplifiedTrace t σ‖ ≤ C} ∩ Icc 0 V)
      ≤ volume (DeBruijn.xiShadow ∩ Icc 0 V) :=
        measure_mono (inter_subset_inter_left _ setOf_unbounded_amplifiedTrace_subset_xiShadow)
    _ ≤ ENNReal.ofReal (2 * offLineMoment (V + 1 / 2)) :=
        DeBruijn.volume_xiShadow_inter_Icc_le_offLineMoment V
    _ ≤ ENNReal.ofReal (67 / 500 * (V + 1 / 2)) :=
        ENNReal.ofReal_le_ofReal (by linarith)

end

end RHTower
