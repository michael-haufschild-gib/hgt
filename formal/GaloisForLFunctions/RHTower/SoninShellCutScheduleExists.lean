import GaloisForLFunctions.RHTower.SoninShellCutTotalSlack
import GaloisForLFunctions.RHTower.SoninShellCutSharpSchedule

/-!
# A schedule exists, with as many annuli as one likes

Choosing the prescribed product first and the cut second discharges every hypothesis of the energy
bound: the product settles the packets' tail conditions and the two slack terms that do not see the
cut, the cut settles the remaining slack term and every largeness condition, and the cut may be
taken finer than any prescribed threshold.

So for every shortfall there is a schedule realising it, at arbitrarily many annuli — and the energy
bound then reads with that number in place of the family's size.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open Filter ContinuousLinearMap

/-- **A schedule exists at every size.**  For any shortfall there is a *single* product such that
every fine enough cut gives coupling energy at least the number of annuli, less the ideal errors'
fixed discount, times the squared shortfall.  The product is chosen before the cut, since nothing in
its four obligations mentions the cut. -/
theorem exists_schedule_card_sub_le_hsNormSq_soninApertureCoupling (N₀ : ℕ) (hN₀ : 1 ≤ N₀) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (a b c q : ℝ), b < c → 0 < a → a ≤ b → 0 < b → a < q → 2 * q ≤ b →
      ∀ η : ℝ, 0 < η → η ≤ 1 →
        ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ N : ℕ in Filter.atTop,
          ∃ hr : 1 < soninShellCutScale b c N κ, 0 < N ∧
          ((N : ℝ) - ∑ k : Fin 3, hsNormSq (soninCouplingIdealErrors a b
              (soninShellCutScale b c N κ)⁻¹
              (inv_pos.mpr (zero_lt_one.trans hr)) k) / (η / 6) ^ 2) * (1 - η) ^ 2 ≤
            hsNormSq (evenSoninApertureSuccessiveLayerTransition a b c
              (soninShellCutScale b c N κ) hr) := by
  obtain ⟨K, hK0, hK⟩ := exists_card_sub_le_hsNormSq_soninApertureCoupling_shellCut_sharp N₀ hN₀
  refine ⟨K, hK0, ?_⟩
  intro a b c q hbc ha hab hb haq hqb η hη hη1
  have hI : (0 : ℝ) < ∫ y : ℝ, soninUnitBumpSq y := integral_soninUnitBumpSq_pos
  have hJ₀ : (0 : ℝ) < ∫ y : ℝ, soninUnitBumpData y := integral_soninUnitBumpData_pos
  have hq : (0 : ℝ) < q := ha.trans haq
  have hgap : (0 : ℝ) < q - a := by linarith
  set A : ℝ := a / ((q - a) * ∫ y : ℝ, soninUnitBumpSq y) with hAdef
  set C : ℝ := 4 * K / (((2 * N₀ : ℝ) - 1) * ∫ y : ℝ, soninUnitBumpSq y) with hCdef
  set D : ℝ := 2 * (2 * (1 + 2 * soninRefTailSup 0 / (∫ y : ℝ, soninUnitBumpData y))) with hDdef
  have hAnn : (0 : ℝ) ≤ A := by
    rw [hAdef]
    positivity
  have hDnn : (0 : ℝ) ≤ D := by
    have := soninRefTailSup_nonneg (0 : ℝ)
    have hfrac : (0 : ℝ) ≤ 2 * soninRefTailSup 0 / (∫ y : ℝ, soninUnitBumpData y) := by positivity
    rw [hDdef]
    linarith
  -- first choice: the prescribed product, made once and for all
  obtain ⟨κ, hκ, hmean, hSq, hslackκ⟩ :=
    exists_kappa_full a q b A C D hAnn haq hb hq hN₀ (show (0 : ℝ) < η / 6 by linarith)
  refine ⟨κ, hκ, ?_⟩
  -- second choice: the cut, eventually
  filter_upwards [eventually_soninShellCut_second_choice a b c q κ D hbc ha hq hκ
    (show (0 : ℝ) < η / 6 by linarith)] with N hNcond
  obtain ⟨⟨hN, hscale, hcarrier, hap⟩, houter⟩ := hNcond
  refine ⟨hscale, hN, ?_⟩
  -- the packets' tail conditions, read through the fixed product
  obtain ⟨htail1, htail2⟩ :=
    soninShellCut_tail_conditions_of_product b c hbc hN hκ q hq hmean hSq
  -- the slack condition
  have houterle := outerSlack_le_global b c hbc hN (soninShellCutScale b c N κ * q) D hDnn
    hcarrier.le
  have hslack : 3 * (η / 6) +
      (Real.sqrt (soninShellCutHighBoundAt b c N K N₀ (soninShellCutScale b c N κ * b)) +
        Real.sqrt (soninShellCutSharpBandBoundAt b c N
          (soninShellCutScale b c N κ * q) (soninShellCutScale b c N κ * a)) +
        Real.sqrt (soninShellCutSharpBandBoundAt b c N
          (soninShellCutScale b c N κ * q) b)) / soninShellCutNormFloor b c N ≤ η := by
    rw [totalSlack_scale_eq b c hbc hN a q κ ha haq hκ hb hK0 hN₀]
    linarith [hslackκ, houter, houterle]
  exact hK a b c q hscale hbc hN ha hab hb haq hqb hcarrier hap htail1 htail2 (η / 6) η
    (by linarith) hη1 hslack

end RHTower
