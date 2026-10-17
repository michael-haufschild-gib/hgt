import GaloisForLFunctions.BiScaleUncertainty.FiniteTrainGridClassification

/-!
# Energy stability from a local normalized correlation

The singular part cancels when normalized correlations agree near zero. The remaining
energy difference is bounded by twice the integrable weight tail, independently of
source support, packet count, and coefficient size.
-/

open MeasureTheory Set Filter Topology
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

theorem normalizedArchEnergy_eq_integral (f : ℝ → ℝ) :
    normalizedArchEnergy f = ∫ x in Ioi 0,
      (autocorr f 0 - autocorr f x) * archLevySinhWeight x / autocorr f 0 := by
  simp only [div_eq_mul_inv, integral_mul_const]
  rfl

/-- Local normalized correlations determine energy up to a universal integrable-tail error. -/
theorem normalizedArchEnergy_abs_sub_le_of_local {f g : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hRf : 0 < autocorr f 0)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (hRg : 0 < autocorr g 0)
    {a : ℝ} (ha : 0 < a)
    (hlocal : ∀ x, 0 ≤ x → x ≤ a → autocorr g x / autocorr g 0 = autocorr f x / autocorr f 0) :
    |normalizedArchEnergy g - normalizedArchEnergy f| ≤
      2 * ∫ x in Ioi a, archLevySinhWeight x := by
  let F := fun (u : ℝ → ℝ) x =>
    (autocorr u 0 - autocorr u x) * archLevySinhWeight x / autocorr u 0
  have hi (u : ℝ → ℝ) (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) :
      IntegrableOn (F u) (Ioi 0) := (integrableOn_biScaleLevyIntegrand hu huc).div_const _
  have hsplit (u : ℝ → ℝ) (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) :
      normalizedArchEnergy u = (∫ x in Ioc 0 a, F u x) + ∫ x in Ioi a, F u x := by
    rw [normalizedArchEnergy_eq_integral]
    change (∫ x in Ioi 0, F u x) = _
    rw [← Ioc_union_Ioi_eq_Ioi ha.le]
    exact setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      ((hi u hu huc).mono_set fun x hx => hx.1)
      ((hi u hu huc).mono_set fun x hx => ha.trans hx)
  have htail (u : ℝ → ℝ) (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u)
      (hRu : 0 < autocorr u 0) :
      0 ≤ (∫ x in Ioi a, F u x) ∧
        (∫ x in Ioi a, F u x) ≤ 2 * ∫ x in Ioi a, archLevySinhWeight x := by
    constructor
    · apply setIntegral_nonneg measurableSet_Ioi
      intro x hx
      exact div_nonneg (mul_nonneg (autocorr_sub_nonneg huc hu.continuous x)
        (archLevySinhWeight_pos (ha.trans hx)).le) hRu.le
    · calc
        _ ≤ ∫ x in Ioi a, 2 * archLevySinhWeight x := by
          apply setIntegral_mono_on ((hi u hu huc).mono_set fun x hx => ha.trans hx)
            ((integrableOn_archLevySinhWeight_Ioi ha).const_mul 2) measurableSet_Ioi
          intro x hx
          dsimp [F]
          apply (div_le_iff₀ hRu).mpr
          have hinc : autocorr u 0 - autocorr u x ≤ 2 * autocorr u 0 := by
            linarith [autocorr_add_nonneg huc hu.continuous x]
          have hb := mul_le_mul_of_nonneg_right hinc (archLevySinhWeight_pos (ha.trans hx)).le
          nlinarith
        _ = _ := integral_const_mul _ _
  have hnear : (∫ x in Ioc 0 a, F g x) = ∫ x in Ioc 0 a, F f x := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    dsimp [F]
    calc
      _ = (1 - autocorr g x / autocorr g 0) * archLevySinhWeight x := by
        field_simp [hRg.ne']
      _ = (1 - autocorr f x / autocorr f 0) * archLevySinhWeight x := by
        rw [hlocal x hx.1.le hx.2]
      _ = _ := by field_simp [hRf.ne']
  have htf := htail f hf hfc hRf
  have htg := htail g hg hgc hRg
  rw [hsplit f hf hfc, hsplit g hg hgc, hnear]
  apply abs_le.mpr
  constructor <;> linarith

/-- Arbitrarily many separated packets change normalized energy by only a fixed tail constant. -/
theorem normalizedArchEnergy_copyTrain_uniform_error {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hR : 0 < autocorr f 0)
    {m : ℕ} (c : Fin (m + 1) → ℝ) (hc : ∃ i, c i ≠ 0) {D S : ℝ}
    (hD : 0 ≤ D) (hsupp : ∀ x, D < |x| → autocorr f x = 0) (hS : D + 1 < S) :
    |normalizedArchEnergy (copyTrain f c S) - normalizedArchEnergy f| ≤
      2 * ∫ x in Ioi (1 : ℝ), archLevySinhWeight x := by
  have hQ := copyTrainMass_pos_of_exists hc
  have hm : autocorr (copyTrain f c S) 0 = copyTrainMass c * autocorr f 0 :=
    autocorr_copyTrain_local hf.continuous hfc c hD hsupp hS (by norm_num : |(0 : ℝ)| ≤ 1)
  have hRG : 0 < autocorr (copyTrain f c S) 0 := by rw [hm]; exact mul_pos hQ hR
  apply normalizedArchEnergy_abs_sub_le_of_local hf hfc hR
    (contDiff_copyTrain hf c S) (hasCompactSupport_copyTrain hfc c S) hRG (by norm_num)
  intro x hx0 hx1
  rw [autocorr_copyTrain_local hf.continuous hfc c hD hsupp hS
    (by rwa [abs_of_nonneg hx0] : |x| ≤ 1), hm]
  field_simp [hQ.ne', hR.ne']

/-- One fixed smooth bump realizes every small correlation radius at coefficient-one logarithmic cost. -/
theorem exists_smooth_small_support_logarithmic_cost :
    ∃ C : ℝ, ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      ∃ f : ℝ → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) f ∧ HasCompactSupport f ∧
        0 < autocorr f 0 ∧ (∀ x, ρ < |x| → autocorr f x = 0) ∧
        normalizedArchEnergy f ≤ C - Real.log ρ := by
  obtain ⟨f, hf, hfc, hR⟩ := exists_smooth_compact_source_positive_mass
  have hr : (2 : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) :=
    WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)
  obtain ⟨D, hD, hsupp⟩ := exists_pos_autocorr_support_radius hfc
  obtain ⟨A, hA⟩ := exists_sourceRescale_logarithmic_energy_bound_of_support
    (hf.of_le hr) hfc hR hD hsupp
  refine ⟨A + Real.log (D + 1), ?_⟩
  intro ρ hρ hρ1
  let L := (D + 1) / ρ
  have hL : 0 < L := by dsimp [L]; positivity
  have hDL : D ≤ L := by
    dsimp [L]
    apply (le_div_iff₀ hρ).mpr
    have hb := mul_le_mul_of_nonneg_left hρ1 hD.le
    nlinarith
  refine ⟨sourceRescale f L, contDiff_sourceRescale hf L,
    hasCompactSupport_sourceRescale hfc hL, ?_, ?_, ?_⟩
  · rw [autocorr_sourceRescale f hL, mul_zero]
    positivity
  · intro x hx
    rw [autocorr_sourceRescale f hL, hsupp, mul_zero]
    rw [abs_mul, abs_of_pos hL]
    have hm := mul_lt_mul_of_pos_left hx hL
    have heq : L * ρ = D + 1 := by dsimp [L]; field_simp
    rw [heq] at hm
    linarith
  · have hb := hA L hL hDL
    have hl : Real.log L = Real.log (D + 1) - Real.log ρ := Real.log_div (by positivity) hρ.ne'
    rw [hl] at hb
    linarith

end

end GaloisForLFunctions.BiScaleUncertainty
