import GaloisForLFunctions.ArithmeticIndexDescent.SeparatedSupportsRemoveTheGammaSingularity
import GaloisForLFunctions.ArithmeticIndexDescent.BoundedWindowsHaveFinitePrimeInteraction
import GaloisForLFunctions.ArithmeticIndexDescent.ArithmeticSectionsHaveOnlyPresentationRadicals
import GaloisForLFunctions.RHTower.WeilPolarConeKernelTransformForm

/-!
# Uniform mixed-source payment across a gap

On a bounded window, separated real profiles have a bounded mixed Weil pairing
in their actual square masses. The bound includes the finite prime horizon,
the Gamma tail and both pole moments. Rescaling one profile makes its assigned
cost arbitrarily small, with an explicit reciprocal cost on the other profile.
-/

open MeasureTheory Set Filter Complex
open scoped ComplexConjugate
open Zeta23 RHTower RHTower.WeilSpectral

noncomputable section

namespace GaloisForLFunctions.ArithmeticIndexDescent

open ArithmeticCastelnuovoSeveri

private theorem windowMoment_sq_le {f k : ℝ → ℝ} {R K : ℝ}
    (hf : Continuous f) (hk : Continuous k) (hR : 0 < R)
    (hs : ∀ u, R < |u| → f u = 0)
    (hb : ∀ u ∈ Icc (-R) R, k u ^ 2 ≤ K) :
    (∫ u, f u * k u) ^ 2 ≤ (2 * R * K) * sectionMass f := by
  have hfi : IntegrableOn (fun u => f u ^ 2) (Icc (-R) R) := (hf.pow 2).integrableOn_Icc
  have hki : IntegrableOn (fun u => k u ^ 2) (Icc (-R) R) := (hk.pow 2).integrableOn_Icc
  have hcs := HTGeometry.sq_integral_mul_le (μ := volume.restrict (Icc (-R) R))
    hf.aestronglyMeasurable hk.aestronglyMeasurable hfi hki
  have hz (u : ℝ) (hu : u ∉ Icc (-R) R) : f u = 0 :=
    hs u (lt_of_not_ge fun hh => hu (abs_le.mp hh))
  have hp : (∫ u in Icc (-R) R, f u * k u) = ∫ u, f u * k u :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => by rw [hz u hu, zero_mul]
  have hm : (∫ u in Icc (-R) R, f u ^ 2) = sectionMass f :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => by
      rw [hz u hu, zero_pow (by decide : (2 : ℕ) ≠ 0)]
  have hkbound : (∫ u in Icc (-R) R, k u ^ 2) ≤ 2 * R * K := by
    calc
      _ ≤ ∫ _u in Icc (-R) R, K :=
        setIntegral_mono_on hki continuous_const.integrableOn_Icc measurableSet_Icc hb
      _ = _ := by
        rw [setIntegral_const]
        change (volume (Icc (-R) R)).toReal * K = _
        rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith only [hR])]
        ring
  rw [hp, hm] at hcs
  calc
    _ ≤ sectionMass f * (∫ u in Icc (-R) R, k u ^ 2) := hcs
    _ ≤ sectionMass f * (2 * R * K) :=
      mul_le_mul_of_nonneg_left hkbound (sectionMass_nonneg f)
    _ = _ := mul_comm _ _

/-- Both pole moments are controlled uniformly on a bounded source window. -/
theorem poleMoments_sq_le_window {f : ℝ → ℝ} {R : ℝ}
    (hf : Continuous f) (hR : 0 < R) (hs : ∀ u, R < |u| → f u = 0) :
    poleA f ^ 2 ≤ (2 * R * Real.exp R) * sectionMass f ∧
      poleB f ^ 2 ≤ (2 * R * Real.exp R) * sectionMass f := by
  constructor
  · apply windowMoment_sq_le hf (Real.continuous_exp.comp (continuous_id.div_const 2)) hR hs
    intro u hu
    change Real.exp (u / 2) ^ 2 ≤ Real.exp R
    rw [pow_two, ← Real.exp_add, show u / 2 + u / 2 = u by ring]
    exact Real.exp_le_exp.mpr hu.2
  · apply windowMoment_sq_le hf (Real.continuous_exp.comp (continuous_id.neg.div_const 2)) hR hs
    intro u hu
    change Real.exp (-u / 2) ^ 2 ≤ Real.exp R
    rw [pow_two, ← Real.exp_add, show -u / 2 + -u / 2 = -u by ring]
    exact Real.exp_le_exp.mpr (by linarith only [hu.1])

theorem abs_mixedPole_le_window {f g : ℝ → ℝ} {R : ℝ}
    (hf : Continuous f) (hg : Continuous g) (hR : 0 < R)
    (hsf : ∀ u, R < |u| → f u = 0) (hsg : ∀ u, R < |u| → g u = 0) :
    |poleB f * poleA g + poleA f * poleB g| ≤
      (2 * R * Real.exp R) * (sectionMass f + sectionMass g) := by
  obtain ⟨hAf, hBf⟩ := poleMoments_sq_le_window hf hR hsf
  obtain ⟨hAg, hBg⟩ := poleMoments_sq_le_window hg hR hsg
  have h1 : |poleB f * poleA g| ≤
      (2 * R * Real.exp R) * (sectionMass f + sectionMass g) / 2 := by
    rw [abs_mul]
    nlinarith only [hBf, hAg, sq_nonneg (|poleB f| - |poleA g|), sq_abs (poleB f), sq_abs (poleA g)]
  have h2 : |poleA f * poleB g| ≤
      (2 * R * Real.exp R) * (sectionMass f + sectionMass g) / 2 := by
    rw [abs_mul]
    nlinarith only [hAf, hBg, sq_nonneg (|poleA f| - |poleB g|), sq_abs (poleA f), sq_abs (poleB g)]
  have ht := abs_add_le (poleB f * poleA g) (poleA f * poleB g)
  linarith only [h1, h2, ht]

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

/-- Full mixed-source control, with all three arithmetic places paid explicitly. -/
theorem exists_separatedWeil_window_mass_bound {R d : ℝ} (hR : 0 < R) (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f g : realTests,
      (∀ u, R < |u| → f.1 u = 0) → (∀ u, R < |u| → g.1 u = 0) →
      (∀ u v, f.1 u ≠ 0 → g.1 v ≠ 0 → d < |u - v|) →
      |realWeilForm f g| ≤ C * (sectionMass f.1 + sectionMass g.1) := by
  obtain ⟨P, hP, hprime⟩ := exists_primePart_window_mass_bound R
  let A := ∫ x in Ioi d, archLevyDensity x
  let B := 2 * R * Real.exp R
  have hA : 0 ≤ A := setIntegral_nonneg measurableSet_Ioi fun x hx =>
    (archLevyDensity_pos (hd.trans hx)).le
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨B + P + A, add_nonneg (add_nonneg hB hP) hA, ?_⟩
  intro f g hsf hsg hgap
  have hp := abs_mixedPole_le_window f.2.1.continuous g.2.1.continuous hR hsf hsg
  have hq := hprime f.1 g.1 f.2.1.continuous f.2.2 g.2.1.continuous g.2.2 hsf hsg
  have ha := abs_archCross_le_of_gap hd f.2.1 f.2.2 g.2.1 g.2.2 hgap
  have hparts : realWeilForm f g =
      poleB f.1 * poleA g.1 + poleA f.1 * poleB g.1 -
        (primePart (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
          (EF.weilTest (cx f.1) (cx g.1))).re +
        (1 / (2 * Real.pi)) * ∫ r : ℝ,
          (paperFT (cx f.1) r * conj (paperFT (cx g.1) r)).re * EF.gammaBracket r := by
    change (weilFullFunctional _ (EF.weilTest (cx f.1) (cx g.1))).re = _
    rw [weilFullFunctional_eq_parts, Complex.add_re, Complex.sub_re,
      re_polePart_weilTest, re_archPart_weilTest]
  rw [hparts]
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
  dsimp [A, B]
  linarith only [hp, hq, ha, ht1, ht2]

private theorem sectionMass_smul (t : ℝ) (f : realTests) :
    sectionMass (t • f).1 = t ^ 2 * sectionMass f.1 := by
  change (∫ u, (t * f.1 u) ^ 2) = _
  simp only [mul_pow, integral_const_mul, sectionMass]

/-- An arbitrary fraction of the old mass can pay the mixed term; the new mass
receives the explicit reciprocal charge. The bound is produced by the source. -/
theorem exists_separatedWeil_mass_payment {R d ε : ℝ}
    (hR : 0 < R) (hd : 0 < d) (hε : 0 < ε) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ f g : realTests,
      (∀ u, R < |u| → f.1 u = 0) → (∀ u, R < |u| → g.1 u = 0) →
      (∀ u v, f.1 u ≠ 0 → g.1 v ≠ 0 → d < |u - v|) →
      2 * |realWeilForm f g| ≤ ε * sectionMass f.1 + D * sectionMass g.1 := by
  obtain ⟨C, hC, hbound⟩ := exists_separatedWeil_window_mass_bound hR hd
  have hC1 : 0 < C + 1 := by linarith only [hC]
  let t := ε / (2 * (C + 1))
  have ht : 0 < t := div_pos hε (mul_pos (by norm_num) hC1)
  refine ⟨4 * (C + 1) ^ 2 / ε, by positivity, ?_⟩
  intro f g hsf hsg hgap
  have hs : ∀ u, R < |u| → (t • f).1 u = 0 := by
    intro u hu
    change t * f.1 u = 0
    rw [hsf u hu, mul_zero]
  have hgap' : ∀ u v, (t • f).1 u ≠ 0 → g.1 v ≠ 0 → d < |u - v| := by
    intro u v hu hv
    apply hgap u v _ hv
    intro hf0
    apply hu
    change t * f.1 u = 0
    rw [hf0, mul_zero]
  have hh := hbound (t • f) g hs hsg hgap'
  rw [map_smul realWeilForm t f, LinearMap.smul_apply, smul_eq_mul,
    abs_mul, abs_of_pos ht, sectionMass_smul] at hh
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

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_separatedWeil_window_mass_bound
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_separatedWeil_mass_payment
