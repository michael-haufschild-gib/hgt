import GaloisForLFunctions.ArithmeticIndexDescent.TouchingSupportsHaveBoundedGammaInteraction
import GaloisForLFunctions.ArithmeticIndexDescent.TheSeparatedMixedSourceIsBounded
import GaloisForLFunctions.ArithmeticIndexDescent.EveryShortCellPaysAnyFixedMassCharge

/-!
# Full source payment for touching ordered cells

The sharp Gamma boundary bound combines with the actual finite prime horizon
and both global poles. The resulting mixed payment has no support-gap parameter.
An arbitrarily short adjacent cell pays this charge while retaining the exact
old Weil diagonal.
-/

noncomputable section

open MeasureTheory Set Filter Complex
open scoped ComplexConjugate
open RHTower RHTower.WeilSpectral Zeta23

namespace GaloisForLFunctions.ArithmeticIndexDescent

open ArithmeticCastelnuovoSeveri

private theorem re_polePart_weilTest (f g : realTests) :
    (_root_.RHTower.WeilSpectral.polePart (EF.weilTest (cx f.1) (cx g.1))).re =
      poleB f.1 * poleA g.1 + poleA f.1 * poleB g.1 := by
  have hB (h : ℝ → ℝ) : paperFT (cx h) (I / 2) = (poleB h : ℂ) := by
    change paperFT (fun u => (h u : ℂ)) (I / 2) = (poleB h : ℂ)
    simpa only [poleB, neg_div] using paperFT_ofReal_I_half h
  have hA (h : ℝ → ℝ) : paperFT (cx h) (-(I / 2)) = (poleA h : ℂ) :=
    paperFT_ofReal_neg_I_half h
  have hc1 : conj (I / 2) = -(I / 2) := by
    rw [map_div₀, Complex.conj_I, map_ofNat]
    ring
  have hc2 : conj (-(I / 2)) = I / 2 := by rw [map_neg, hc1, neg_neg]
  rw [_root_.RHTower.WeilSpectral.polePart, show -I / 2 = -(I / 2) by ring,
    EF.paperFT_weilTest (cx_contDiff f.2.1).continuous (cx_contDiff g.2.1).continuous
      (cx_hasCompactSupport f.2.2) (cx_hasCompactSupport g.2.2),
    EF.paperFT_weilTest (cx_contDiff f.2.1).continuous (cx_contDiff g.2.1).continuous
      (cx_hasCompactSupport f.2.2) (cx_hasCompactSupport g.2.2),
    hc1, hc2, hB, hA, hB, hA]
  simp only [Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_add, Complex.ofReal_re]

private theorem re_archPart_weilTest (f g : realTests) :
    (archPart (EF.weilTest (cx f.1) (cx g.1))).re =
      (1 / (2 * Real.pi)) * ∫ r : ℝ,
        (paperFT (cx f.1) r * conj (paperFT (cx g.1) r)).re * EF.gammaBracket r := by
  have hi := LebesgueAtomWeil.integrable_paperFT_weilTest_mul_gammaBracket
    (cx_contDiff f.2.1) (cx_hasCompactSupport f.2.2)
    (cx_contDiff g.2.1) (cx_hasCompactSupport g.2.2)
  have hconst : (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) := by
    push_cast
    ring
  have hre : (∫ r : ℝ, paperFT (EF.weilTest (cx f.1) (cx g.1)) r *
      (EF.gammaBracket r : ℂ)).re =
      ∫ r : ℝ, (paperFT (EF.weilTest (cx f.1) (cx g.1)) r *
        (EF.gammaBracket r : ℂ)).re := (integral_re hi).symm
  rw [archPart, hconst, Complex.re_ofReal_mul, hre]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with r
  rw [EF.paperFT_weilTest (cx_contDiff f.2.1).continuous (cx_contDiff g.2.1).continuous
    (cx_hasCompactSupport f.2.2) (cx_hasCompactSupport g.2.2),
    Complex.conj_ofReal, Complex.re_mul_ofReal]

/-- The exact literal source decomposition, with neither pole removed. -/
theorem realWeilForm_eq_source_parts (f g : realTests) :
    realWeilForm f g = poleB f.1 * poleA g.1 + poleA f.1 * poleB g.1 -
      (primePart (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest (cx f.1) (cx g.1))).re +
      (1 / (2 * Real.pi)) * ∫ r : ℝ,
        (paperFT (cx f.1) r * conj (paperFT (cx g.1) r)).re * EF.gammaBracket r := by
  change (weilFullFunctional _ (EF.weilTest (cx f.1) (cx g.1))).re = _
  rw [weilFullFunctional_eq_parts, Complex.add_re, Complex.sub_re,
    re_polePart_weilTest, re_archPart_weilTest]

/-- One window constant controls all profiles ordered across any touching boundary. -/
theorem exists_orderedWeil_window_mass_bound {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (b : ℝ) (f g : realTests),
      (∀ u, R < |u| → f.1 u = 0) → (∀ u, R < |u| → g.1 u = 0) →
      (∀ u, b ≤ u → f.1 u = 0) → (∀ u, u ≤ b → g.1 u = 0) →
      |realWeilForm f g| ≤ C * (sectionMass f.1 + sectionMass g.1) := by
  obtain ⟨P, hP, hprime⟩ := exists_primePart_window_mass_bound R
  let B := 2 * R * Real.exp R
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨B + P + Real.pi, add_nonneg (add_nonneg hB hP) Real.pi_pos.le, ?_⟩
  intro b f g hsf hsg hleft hright
  have hp := abs_mixedPole_le_window f.2.1.continuous g.2.1.continuous hR hsf hsg
  have hq := hprime f.1 g.1 f.2.1.continuous f.2.2 g.2.1.continuous g.2.2 hsf hsg
  have ha := abs_archCross_le_of_ordered f.2.1 f.2.2 g.2.1 g.2.2 hleft hright
  rw [realWeilForm_eq_source_parts]
  have ht1 := abs_add_le
    (poleB f.1 * poleA g.1 + poleA f.1 * poleB g.1 -
      (primePart (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest (cx f.1) (cx g.1))).re)
    ((1 / (2 * Real.pi)) * ∫ r : ℝ,
      (paperFT (cx f.1) r * conj (paperFT (cx g.1) r)).re * EF.gammaBracket r)
  have ht2 := abs_add_le (poleB f.1 * poleA g.1 + poleA f.1 * poleB g.1)
    (-(primePart (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      (EF.weilTest (cx f.1) (cx g.1))).re)
  rw [← sub_eq_add_neg, abs_neg] at ht2
  dsimp only [B]
  linarith only [hp, hq, ha, ht1, ht2]

/-- Any prescribed old-mass allowance pays the full mixed source, including a touching endpoint. -/
theorem exists_orderedWeil_mass_payment {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (b : ℝ) (f g : realTests),
      (∀ u, R < |u| → f.1 u = 0) → (∀ u, R < |u| → g.1 u = 0) →
      (∀ u, b ≤ u → f.1 u = 0) → (∀ u, u ≤ b → g.1 u = 0) →
      2 * |realWeilForm f g| ≤ ε * sectionMass f.1 + D * sectionMass g.1 := by
  obtain ⟨C, hC, hbound⟩ := exists_orderedWeil_window_mass_bound hR
  have hC1 : 0 < C + 1 := by linarith only [hC]
  let t := ε / (2 * (C + 1))
  have ht : 0 < t := div_pos hε (mul_pos (by norm_num) hC1)
  refine ⟨4 * (C + 1) ^ 2 / ε, by positivity, ?_⟩
  intro b f g hsf hsg hleft hright
  have hs : ∀ u, R < |u| → (t • f).1 u = 0 := by
    intro u hu
    change t * f.1 u = 0
    rw [hsf u hu, mul_zero]
  have hl : ∀ u, b ≤ u → (t • f).1 u = 0 := by
    intro u hu
    change t * f.1 u = 0
    rw [hleft u hu, mul_zero]
  have hm : sectionMass (t • f).1 = t ^ 2 * sectionMass f.1 := by
    change (∫ u, (t * f.1 u) ^ 2) = _
    simp only [mul_pow, integral_const_mul, sectionMass]
  have hh := hbound b (t • f) g hs hsg hl hright
  rw [map_smul realWeilForm t f, LinearMap.smul_apply, smul_eq_mul,
    abs_mul, abs_of_pos ht, hm] at hh
  have hmass : 0 ≤ t ^ 2 * sectionMass f.1 + sectionMass g.1 :=
    add_nonneg (mul_nonneg (sq_nonneg _) (sectionMass_nonneg _)) (sectionMass_nonneg _)
  have hh' : t * |realWeilForm f g| ≤
      (C + 1) * (t ^ 2 * sectionMass f.1 + sectionMass g.1) :=
    hh.trans (mul_le_mul_of_nonneg_right (by linarith only) hmass)
  have hpaid : t * (2 * |realWeilForm f g|) ≤
      t * (ε * sectionMass f.1 + (4 * (C + 1) ^ 2 / ε) * sectionMass g.1) := by
    calc
      t * (2 * |realWeilForm f g|) ≤
          2 * (C + 1) * (t ^ 2 * sectionMass f.1 + sectionMass g.1) := by
        linarith only [hh']
      _ = t * (ε * sectionMass f.1 + (4 * (C + 1) ^ 2 / ε) * sectionMass g.1) := by
        dsimp [t]
        field_simp [ne_of_gt hε, ne_of_gt hC1]
        ring
  nlinarith only [hpaid, ht]

/-- A short cell immediately to the right pays its complete interaction with the old region. -/
theorem exists_touchingCell_diagonal_extension {R ε : ℝ}
    (hR : 0 < R) (hε : 0 < ε) (b L : ℝ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∀ p g : realTests,
        (∀ u, R < |u| → p.1 u = 0) →
        (∀ u, b ≤ u → p.1 u = 0) →
        (∀ u, u ∉ Ioo b (b + δ) → g.1 u = 0) →
        realWeilForm p p - ε * sectionMass p.1 + L * sectionMass g.1 ≤
          realWeilForm (p + g) (p + g) := by
  let R' := R + |b| + 2
  have hR' : 0 < R' := by dsimp [R']; positivity
  obtain ⟨D, _, hpayment⟩ := exists_orderedWeil_mass_payment hR' hε
  obtain ⟨η, hη, hcell⟩ := exists_shortCell_weil_coercivity (D + L)
  refine ⟨min 1 η, lt_min zero_lt_one hη, ?_⟩
  intro δ hδ hδlt p g hps hleft hgs
  have hδ1 : δ ≤ 1 := (hδlt.trans_le (min_le_left _ _)).le
  have hδη : δ < η := hδlt.trans_le (min_le_right _ _)
  have hps' : ∀ u, R' < |u| → p.1 u = 0 := by
    intro u hu
    apply hps
    have hRR : R ≤ R' := by dsimp [R']; linarith only [abs_nonneg b]
    exact hRR.trans_lt hu
  have hgs' : ∀ u, R' < |u| → g.1 u = 0 := by
    intro u hu
    apply hgs u
    intro hm
    have habs : |u - b| ≤ δ := by
      rw [abs_of_pos (sub_pos.mpr hm.1)]
      linarith only [hm.2]
    have htri := abs_add_le (u - b) b
    rw [sub_add_cancel] at htri
    dsimp [R'] at hu
    linarith only [hu, habs, htri, hδ1, hR]
  have hright : ∀ u, u ≤ b → g.1 u = 0 := by
    intro u hu
    exact hgs u (fun hm => (not_lt_of_ge hu hm.1).elim)
  have hcenter : ∀ u, δ / 2 < |u - (b + δ / 2)| → g.1 u = 0 := by
    intro u hu
    apply hgs u
    intro hm
    have hc : |u - (b + δ / 2)| ≤ δ / 2 := abs_le.mpr
      ⟨by linarith only [hm.1], by linarith only [hm.2]⟩
    exact not_lt_of_ge hc hu
  have hmix := hpayment b p g hps' hgs' hleft hright
  have hnew := hcell δ hδ hδη (b + δ / 2) g hcenter
  have hsum : realWeilForm (p + g) (p + g) =
      realWeilForm p p + 2 * realWeilForm p g + realWeilForm g g := by
    simp only [map_add, LinearMap.add_apply]
    rw [realWeilForm_symm g p]
    ring
  rw [hsum]
  linarith only [hmix, hnew, neg_abs_le (realWeilForm p g)]

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_orderedWeil_window_mass_bound
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_orderedWeil_mass_payment
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_touchingCell_diagonal_extension
