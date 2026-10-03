import GaloisForLFunctions.RHTower.ZetaOffLineMomentSelbergSeventh
import GaloisForLFunctions.RHTower.ZetaOffLineMomentNinthConsequences

/-!
# Consequences of Selberg's twisted mollifier of length `U^{1/7}`

The gate constant `c_R = e^{2R}/(1 − e^{−2R/7})` (`ZetaOffLineMomentSelbergSeventh`) gives

* the off-line moment `Σ_{0 < Im ρ ≤ V} m_ρ (Re ρ − ½) ≤ (3/25) V`, hence
  - Laguerre positivity, all-order slice positivity and Speiser-clean heights on measure
    `≥ (19/25) V − 3/25`; `Re(ξ'/ξ) ≥ 0` on area `≥ (19/50) V − 3/50`; contracting seams on
    `≥ (16/25) K − 3/25` right discs at every radius; a clean height in every `[a, b]` with
    `(6/25)(b + 1) < b − a`;
* the tail law `4π Σ m_ρ (Re ρ − ½ − R/log V)⁺ ≤ (g₇(R) + η) V`, `g₇(R) = −log(1 − e^{−2R/7})`
  (`eventually_offLineTail_le_selberg_seventh`), hence at most `(g₇(R) + η) V log V/(4πR)` zeros
  with `Re ρ ≥ ½ + 2R/log V`, contracting seams on all but a fraction `≈ (3/2π)g₇(R)` of the right
  discs of radius `2R/log V`, and a `κ`-shadow of measure `≤ (g₇(κ/2) + η)(V + 1)/π`.
-/

open Complex Filter Topology Set MeasureTheory Metric
open scoped ComplexOrder

namespace RHTower

noncomputable section

/-! ## The off-line moment `3/25` -/

theorem eventually_volume_laguerre_monotone_ge_seventh :
    ∀ᶠ V in atTop, ENNReal.ofReal (19 / 25 * V - 3 / 25) ≤
      volume {x ∈ Icc (0 : ℝ) V |
        MonotoneOn (fun y : ℝ => ‖DeBruijn.riemannHeat 0 ((x : ℂ) + I * y)‖) (Ici 0) ∧
        0 ≤ (deriv (DeBruijn.riemannHeat 0) x ^ 2
          - DeBruijn.riemannHeat 0 x * deriv (deriv (DeBruijn.riemannHeat 0)) x).re} :=
  (DeBruijn.eventually_volume_laguerre_monotone_ge_of_moment (by norm_num)
    ZetaGateProductAFE.eventually_offLineMoment_le_selberg_seventh).mono fun _ h =>
      le_trans (le_of_eq (by norm_num)) h

theorem eventually_volume_sliceCoeff_nonneg_ge_seventh :
    ∀ᶠ V in atTop, ENNReal.ofReal (19 / 25 * V - 3 / 25) ≤
      volume {t ∈ Icc (0 : ℝ) V | ∀ n : ℕ, 0 ≤ xiSliceCoeff t n} :=
  (DeBruijn.eventually_volume_sliceCoeff_nonneg_ge_of_moment (by norm_num)
    ZetaGateProductAFE.eventually_offLineMoment_le_selberg_seventh).mono fun _ h =>
      le_trans (le_of_eq (by norm_num)) h

theorem eventually_volume_hadamardSign_ge_seventh :
    ∀ᶠ V in atTop, ENNReal.ofReal (19 / 50 * V - 3 / 50) ≤
      volume {s : ℂ | 1 / 2 < s.re ∧ s.re < 1 ∧ 0 ≤ s.im ∧ s.im ≤ V ∧
        xi s ≠ 0 ∧ 0 ≤ (logDeriv xi s).re} :=
  (DeBruijn.eventually_volume_hadamardSign_ge_of_moment (by norm_num)
    ZetaGateProductAFE.eventually_offLineMoment_le_selberg_seventh).mono fun _ h =>
      le_trans (le_of_eq (by norm_num)) h

theorem exists_card_goodCriticalScaleDiscs_ge_seventh :
    ∃ T₀ : ℝ, ∀ r : ℝ, ∀ hr : 0 < r, ∀ K : ℕ, T₀ ≤ 3 * r * K + r →
      16 / 25 * (K : ℝ) - 3 / 25 ≤
        ((Finset.Icc 1 K \ badCriticalScaleDiscs r K).card : ℝ) ∧
      ∀ k ∈ Finset.Icc 1 K \ badCriticalScaleDiscs r K,
        ∃ hne : ∀ ζ ∈ sphere (criticalScaleCenter r k) r, xi ζ ≠ 0,
          ‖(xiDiscDatum (criticalScaleCenter r k) r hr hne).circlePhase.datum.adjointHankelSeam‖
            < 1 := by
  obtain ⟨T₀, hT₀⟩ := exists_card_goodCriticalScaleDiscs_ge_of_moment
    ZetaGateProductAFE.eventually_offLineMoment_le_selberg_seventh
  refine ⟨T₀, fun r hr K hK =>
    ⟨le_trans (le_of_eq (by ring)) (hT₀ r hr K hK).1, (hT₀ r hr K hK).2⟩⟩

theorem eventually_volume_speiserUnshadowed_ge_seventh :
    ∀ᶠ V in atTop, ENNReal.ofReal (19 / 25 * V - 3 / 25) ≤
      volume {T : ℝ | T ∈ Icc 0 V ∧ SpeiserUnshadowed T} :=
  (eventually_volume_speiserUnshadowed_ge_of_moment (by norm_num)
    ZetaGateProductAFE.eventually_offLineMoment_le_selberg_seventh).mono fun _ h =>
      le_trans (le_of_eq (by norm_num)) h

theorem exists_speiserUnshadowed_mem_Icc_seventh :
    ∃ V₀ : ℝ, ∀ a b : ℝ, 0 ≤ a → V₀ ≤ b → 6 / 25 * (b + 1) < b - a →
      ∃ T ∈ Icc a b, SpeiserUnshadowed T := by
  obtain ⟨V₀, -, h⟩ := exists_speiserUnshadowed_mem_Icc_of_moment (by norm_num)
    ZetaGateProductAFE.eventually_offLineMoment_le_selberg_seventh
  exact ⟨V₀, fun a b ha hb hlen => h a b ha hb (by linarith)⟩

/-! ## The tail law with rate `2R/7` -/

/-- `g₇(R) = −log(1 − e^{−2R/7})`. -/
def selbergTailRateSeventh (R : ℝ) : ℝ := -Real.log (1 - Real.exp (-(2 * R / 7)))

theorem selbergTailRateSeventh_add_nonneg {R η : ℝ} (hR : 0 < R) (hη : 0 < η) :
    0 ≤ selbergTailRateSeventh R + η := by
  unfold selbergTailRateSeventh
  have h := ZetaGateProductAFE.exp_neg_lt_one (show 0 < 2 * R / 7 by positivity)
  have hpos : 0 < 1 - Real.exp (-(2 * R / 7)) := by linarith
  have : Real.log (1 - Real.exp (-(2 * R / 7))) ≤ 0 :=
    Real.log_nonpos hpos.le (by linarith [Real.exp_pos (-(2 * R / 7))])
  linarith

theorem log_selbergBlockConstSeventh_sub {R : ℝ} (hR : 0 < R) :
    Real.log (max (ZetaGateProductAFE.selbergBlockConstSeventh R) 1) - 2 * R
      = selbergTailRateSeventh R := by
  have h2 := ZetaGateProductAFE.exp_neg_lt_one (show 0 < 2 * R / 7 by positivity)
  have hc1 : 1 ≤ ZetaGateProductAFE.selbergBlockConstSeventh R := by
    unfold ZetaGateProductAFE.selbergBlockConstSeventh
    have h1 : 0 < Real.exp (-(2 * R / 7)) := Real.exp_pos _
    rw [le_div_iff₀ (by linarith)]
    have h3 : 1 ≤ Real.exp (2 * R) := Real.one_le_exp (by positivity)
    linarith
  rw [max_eq_left hc1]
  unfold ZetaGateProductAFE.selbergBlockConstSeventh selbergTailRateSeventh
  rw [Real.log_div (Real.exp_pos _).ne' (by linarith), Real.log_exp]
  ring

/-- **The tail law with Selberg's twisted mollifier of length `U^{1/7}`.** -/
theorem eventually_offLineTail_le_selberg_seventh {R η : ℝ} (hR : 0 < R) (hη : 0 < η) :
    ∀ᶠ V in atTop,
      4 * Real.pi * offLineTail (R / Real.log V) V ≤ (selbergTailRateSeventh R + η) * V := by
  have h := eventually_offLineTail_le_of_zetaGate hR (le_max_right _ 1) hη
    (ZetaGateProductAFE.zetaMollifiedMeanSquareGate_selberg_seventh hR)
  rwa [log_selbergBlockConstSeventh_sub hR] at h

theorem eventually_offLineCountBeyond_le_selberg_seventh {R η : ℝ} (hR : 0 < R) (hη : 0 < η) :
    ∀ᶠ V in atTop,
      offLineCountBeyond (2 * (R / Real.log V)) V
        ≤ (selbergTailRateSeventh R + η) / (4 * Real.pi * R) * (V * Real.log V) :=
  eventually_offLineCountBeyond_le_of_tail hR (eventually_offLineTail_le_selberg_seventh hR hη)

theorem eventually_goodCriticalScaleDiscs_selberg_seventh {R η : ℝ} (hR : 0 < R) (hη : 0 < η) :
    ∀ᶠ V in atTop, ∀ K : ℕ,
      3 * (2 * R / Real.log V) * K + 2 * R / Real.log V ≤ V →
      V ≤ 3 * (2 * R / Real.log V) * K + 4 * (2 * R / Real.log V) →
      (K : ℝ) - (3 * K + 4) * (selbergTailRateSeventh R + η) / (2 * Real.pi)
          ≤ ((Finset.Icc 1 K \ badCriticalScaleDiscs (2 * R / Real.log V) K).card : ℝ) ∧
      ∀ hr : 0 < 2 * R / Real.log V,
        ∀ k ∈ Finset.Icc 1 K \ badCriticalScaleDiscs (2 * R / Real.log V) K,
          ∃ hne : ∀ ζ ∈ sphere (criticalScaleCenter (2 * R / Real.log V) k)
              (2 * R / Real.log V), xi ζ ≠ 0,
            ‖(xiDiscDatum (criticalScaleCenter (2 * R / Real.log V) k) (2 * R / Real.log V) hr
              hne).circlePhase.datum.adjointHankelSeam‖ < 1 :=
  eventually_goodCriticalScaleDiscs_of_tail hR (selbergTailRateSeventh_add_nonneg hR hη)
    (eventually_offLineTail_le_selberg_seventh hR hη)

theorem eventually_volume_kappaShadow_le_selberg_seventh {κ η : ℝ} (hκ : 0 < κ) (hη : 0 < η) :
    ∀ᶠ V in atTop,
      volume {t : ℝ | t ∈ Icc 20 V ∧ ∃ ρ : ℂ, xi ρ = 0 ∧
          κ / Real.log V ≤ |ρ.re - 1 / 2| ∧ |t - ρ.im| ≤ |ρ.re - 1 / 2|} ≤
        ENNReal.ofReal ((selbergTailRateSeventh (κ / 2) + η) * (V + 1) / Real.pi) :=
  eventually_volume_kappaShadow_le_of_tail hκ
    (eventually_offLineTail_le_selberg_seventh (by positivity : 0 < κ / 2) hη)

end

end RHTower
