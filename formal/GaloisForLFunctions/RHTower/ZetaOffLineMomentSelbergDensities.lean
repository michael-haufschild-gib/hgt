import GaloisForLFunctions.RHTower.ZetaOffLineMomentSelbergWeights
import GaloisForLFunctions.RHTower.SpeiserCleanHeights
import GaloisForLFunctions.RHTower.XiHadamardSignDensity
import GaloisForLFunctions.RHTower.XiCriticalScaleDiscSeamExplicitDensity

/-!
# Density consequences of the off-line moment bound `17/100`

With `Σ_{0 < Im ρ ≤ V} m(ρ)(Re ρ − ½) ≤ (17/100) V` for all large `V`
(`ZetaGateProductAFE.eventually_offLineMoment_le_selberg`), for all large `V`, `K`:

* Laguerre positivity and vertical monotonicity of `Ξ` on measure `≥ (33/50) V − 17/100` of `[0, V]`
  (`eventually_volume_laguerre_monotone_ge_selberg`);
* every horizontal slice coefficient `≥ 0` on height measure `≥ (33/50) V − 17/100`
  (`eventually_volume_sliceCoeff_nonneg_ge_selberg`);
* `Re(ξ'/ξ) ≥ 0` on area `≥ (33/100) V − 17/200` of `{½ < Re s < 1, 0 ≤ Im s ≤ V}`
  (`eventually_volume_hadamardSign_ge_selberg`);
* zero-free right discs with contracting adjoint Hankel seam: at least `(49/100) K − 17/100` of
  `D_1, …, D_K`, at every radius (`exists_card_goodCriticalScaleDiscs_ge_selberg`);
* Speiser-clean heights of measure `≥ (33/50) V − 17/100` in `[0, V]`
  (`eventually_volume_speiserUnshadowed_ge_selberg`), and one in every `[a, b]` with
  `(17/50)(b + 1) < b − a` (`exists_speiserUnshadowed_mem_Icc_selberg`).
-/

open Complex Filter Topology Set MeasureTheory Metric
open scoped ComplexOrder

namespace RHTower

noncomputable section

/-- **`Ξ` is Laguerre-positive and vertically monotone on `66%` of the real line.** -/
theorem eventually_volume_laguerre_monotone_ge_selberg :
    ∀ᶠ V in atTop, ENNReal.ofReal (33 / 50 * V - 17 / 100) ≤
      volume {x ∈ Icc (0 : ℝ) V |
        MonotoneOn (fun y : ℝ => ‖DeBruijn.riemannHeat 0 ((x : ℂ) + I * y)‖) (Ici 0) ∧
        0 ≤ (deriv (DeBruijn.riemannHeat 0) x ^ 2 - DeBruijn.riemannHeat 0 x * deriv (deriv (DeBruijn.riemannHeat 0)) x).re} :=
  (DeBruijn.eventually_volume_laguerre_monotone_ge_of_moment (by norm_num)
    ZetaGateProductAFE.eventually_offLineMoment_le_selberg).mono fun _ h =>
      le_trans (le_of_eq (by norm_num)) h

/-- **All-order slice positivity on `66%` of the heights.** -/
theorem eventually_volume_sliceCoeff_nonneg_ge_selberg :
    ∀ᶠ V in atTop, ENNReal.ofReal (33 / 50 * V - 17 / 100) ≤
      volume {t ∈ Icc (0 : ℝ) V | ∀ n : ℕ, 0 ≤ xiSliceCoeff t n} :=
  (DeBruijn.eventually_volume_sliceCoeff_nonneg_ge_of_moment (by norm_num)
    ZetaGateProductAFE.eventually_offLineMoment_le_selberg).mono fun _ h =>
      le_trans (le_of_eq (by norm_num)) h

/-- **`Re(ξ'/ξ) ≥ 0` on `66%` of the right half of the critical strip.** -/
theorem eventually_volume_hadamardSign_ge_selberg :
    ∀ᶠ V in atTop, ENNReal.ofReal (33 / 100 * V - 17 / 200) ≤
      volume {s : ℂ | 1 / 2 < s.re ∧ s.re < 1 ∧ 0 ≤ s.im ∧ s.im ≤ V ∧
        xi s ≠ 0 ∧ 0 ≤ (logDeriv xi s).re} :=
  (DeBruijn.eventually_volume_hadamardSign_ge_of_moment (by norm_num)
    ZetaGateProductAFE.eventually_offLineMoment_le_selberg).mono fun _ h =>
      le_trans (le_of_eq (by norm_num)) h

/-- **Contracting seams on `49%` of the right discs, at every scale.** -/
theorem exists_card_goodCriticalScaleDiscs_ge_selberg :
    ∃ T₀ : ℝ, ∀ r : ℝ, ∀ hr : 0 < r, ∀ K : ℕ, T₀ ≤ 3 * r * K + r →
      49 / 100 * (K : ℝ) - 17 / 100 ≤
        ((Finset.Icc 1 K \ badCriticalScaleDiscs r K).card : ℝ) ∧
      ∀ k ∈ Finset.Icc 1 K \ badCriticalScaleDiscs r K,
        ∃ hne : ∀ ζ ∈ sphere (criticalScaleCenter r k) r, xi ζ ≠ 0,
          ‖(xiDiscDatum (criticalScaleCenter r k) r hr hne).circlePhase.datum.adjointHankelSeam‖
            < 1 := by
  obtain ⟨T₀, hT₀⟩ := exists_card_goodCriticalScaleDiscs_ge_of_moment
    ZetaGateProductAFE.eventually_offLineMoment_le_selberg
  refine ⟨T₀, fun r hr K hK => ⟨le_trans (le_of_eq (by ring)) (hT₀ r hr K hK).1, (hT₀ r hr K hK).2⟩⟩

/-- **Speiser-clean heights on `66%` of `[0, V]`.** -/
theorem eventually_volume_speiserUnshadowed_ge_selberg :
    ∀ᶠ V in atTop, ENNReal.ofReal (33 / 50 * V - 17 / 100) ≤
      volume {T : ℝ | T ∈ Icc 0 V ∧ SpeiserUnshadowed T} :=
  (eventually_volume_speiserUnshadowed_ge_of_moment (by norm_num)
    ZetaGateProductAFE.eventually_offLineMoment_le_selberg).mono fun _ h =>
      le_trans (le_of_eq (by norm_num)) h

/-- **Speiser-clean heights in every interval of relative length `17/50`.** -/
theorem exists_speiserUnshadowed_mem_Icc_selberg :
    ∃ V₀ : ℝ, ∀ a b : ℝ, 0 ≤ a → V₀ ≤ b → 17 / 50 * (b + 1) < b - a →
      ∃ T ∈ Icc a b, SpeiserUnshadowed T := by
  obtain ⟨V₀, -, h⟩ := exists_speiserUnshadowed_mem_Icc_of_moment (by norm_num)
    ZetaGateProductAFE.eventually_offLineMoment_le_selberg
  exact ⟨V₀, fun a b ha hb hlen => h a b ha hb (by linarith)⟩

end

end RHTower
