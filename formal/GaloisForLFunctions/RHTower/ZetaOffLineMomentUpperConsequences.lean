import GaloisForLFunctions.RHTower.ZetaOffLineMomentSelbergUpper
import GaloisForLFunctions.RHTower.ZetaOffLineMomentNinthConsequences

/-!
# Consequences of the off-line moment `67/1000`

The off-line moment `Σ_{0 < Im ρ ≤ V} m_ρ (Re ρ − ½) ≤ (67/1000) V`
(`eventually_offLineMoment_le_selberg_upper`, Selberg's twisted mollifier of length `U^{21/50}` on
the upper range) gives Laguerre positivity, all-order slice positivity and Speiser-clean heights on
measure `≥ (433/500) V − 67/1000`; `Re(ξ'/ξ) ≥ 0` on area `≥ (433/1000) V − 67/2000`; contracting
seams on `≥ (799/1000) K − 67/1000` right discs at every radius; a clean height in every `[a, b]`
with `(67/500)(b + 1) < b − a`.
-/

open Complex Filter Topology Set MeasureTheory Metric
open scoped ComplexOrder

namespace RHTower

noncomputable section

/-! ## The off-line moment `67/1000` -/

theorem eventually_volume_laguerre_monotone_ge_upper :
    ∀ᶠ V in atTop, ENNReal.ofReal (433 / 500 * V - 67 / 1000) ≤
      volume {x ∈ Icc (0 : ℝ) V |
        MonotoneOn (fun y : ℝ => ‖DeBruijn.riemannHeat 0 ((x : ℂ) + I * y)‖) (Ici 0) ∧
        0 ≤ (deriv (DeBruijn.riemannHeat 0) x ^ 2
          - DeBruijn.riemannHeat 0 x * deriv (deriv (DeBruijn.riemannHeat 0)) x).re} :=
  (DeBruijn.eventually_volume_laguerre_monotone_ge_of_moment (by norm_num)
    ZetaGateProductAFE.eventually_offLineMoment_le_selberg_upper).mono fun _ h =>
      le_trans (le_of_eq (by norm_num)) h

theorem eventually_volume_sliceCoeff_nonneg_ge_upper :
    ∀ᶠ V in atTop, ENNReal.ofReal (433 / 500 * V - 67 / 1000) ≤
      volume {t ∈ Icc (0 : ℝ) V | ∀ n : ℕ, 0 ≤ xiSliceCoeff t n} :=
  (DeBruijn.eventually_volume_sliceCoeff_nonneg_ge_of_moment (by norm_num)
    ZetaGateProductAFE.eventually_offLineMoment_le_selberg_upper).mono fun _ h =>
      le_trans (le_of_eq (by norm_num)) h

theorem eventually_volume_hadamardSign_ge_upper :
    ∀ᶠ V in atTop, ENNReal.ofReal (433 / 1000 * V - 67 / 2000) ≤
      volume {s : ℂ | 1 / 2 < s.re ∧ s.re < 1 ∧ 0 ≤ s.im ∧ s.im ≤ V ∧
        xi s ≠ 0 ∧ 0 ≤ (logDeriv xi s).re} :=
  (DeBruijn.eventually_volume_hadamardSign_ge_of_moment (by norm_num)
    ZetaGateProductAFE.eventually_offLineMoment_le_selberg_upper).mono fun _ h =>
      le_trans (le_of_eq (by norm_num)) h

theorem exists_card_goodCriticalScaleDiscs_ge_upper :
    ∃ T₀ : ℝ, ∀ r : ℝ, ∀ hr : 0 < r, ∀ K : ℕ, T₀ ≤ 3 * r * K + r →
      799 / 1000 * (K : ℝ) - 67 / 1000 ≤
        ((Finset.Icc 1 K \ badCriticalScaleDiscs r K).card : ℝ) ∧
      ∀ k ∈ Finset.Icc 1 K \ badCriticalScaleDiscs r K,
        ∃ hne : ∀ ζ ∈ sphere (criticalScaleCenter r k) r, xi ζ ≠ 0,
          ‖(xiDiscDatum (criticalScaleCenter r k) r hr hne).circlePhase.datum.adjointHankelSeam‖
            < 1 := by
  obtain ⟨T₀, hT₀⟩ := exists_card_goodCriticalScaleDiscs_ge_of_moment
    ZetaGateProductAFE.eventually_offLineMoment_le_selberg_upper
  refine ⟨T₀, fun r hr K hK =>
    ⟨le_trans (le_of_eq (by ring)) (hT₀ r hr K hK).1, (hT₀ r hr K hK).2⟩⟩

theorem eventually_volume_speiserUnshadowed_ge_upper :
    ∀ᶠ V in atTop, ENNReal.ofReal (433 / 500 * V - 67 / 1000) ≤
      volume {T : ℝ | T ∈ Icc 0 V ∧ SpeiserUnshadowed T} :=
  (eventually_volume_speiserUnshadowed_ge_of_moment (by norm_num)
    ZetaGateProductAFE.eventually_offLineMoment_le_selberg_upper).mono fun _ h =>
      le_trans (le_of_eq (by norm_num)) h

theorem exists_speiserUnshadowed_mem_Icc_upper :
    ∃ V₀ : ℝ, ∀ a b : ℝ, 0 ≤ a → V₀ ≤ b → 67 / 500 * (b + 1) < b - a →
      ∃ T ∈ Icc a b, SpeiserUnshadowed T := by
  obtain ⟨V₀, -, h⟩ := exists_speiserUnshadowed_mem_Icc_of_moment (by norm_num)
    ZetaGateProductAFE.eventually_offLineMoment_le_selberg_upper
  exact ⟨V₀, fun a b ha hb hlen => h a b ha hb (by linarith)⟩

end

end RHTower
