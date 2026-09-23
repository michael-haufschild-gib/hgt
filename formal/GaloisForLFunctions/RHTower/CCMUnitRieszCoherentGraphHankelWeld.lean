import GaloisForLFunctions.RHTower.CCMUnitRieszCoherentPolarSamplingNoGo
import GaloisForLFunctions.RHTower.CCMBoundaryRelativeTrace

/-!
# Coherent source graph energy as an exact Hankel boundary slope

Bare polar `L²` energy cannot control fixed evaluation even inside the canonical unit-Riesz
coherent source span.  The surviving first-order graph energy has, however, a literal CCM-HG
carrier.  For the compact third-difference packet `g`, encode its weak generator as the complex
leak profile

`ell(u) = 2 g'(u) + i g(u)`.

Then `|ell|² = 4|g'|² + |g|²`, the leak profile is admissible, and its initial Hankel boundary
relative-trace slope is exactly four times source-Gram energy.  Consequently the HG four-unit
infinitesimal condition on this packet family is equivalent to the source-Gram unit-ball condition,
and fixed coherent evaluation is recovered exactly from the same boundary slope.

This is a source-faithful FU/UR-to-HG weld.  It does not assert the still-missing arithmetic
four-unit bound for the literal completed prime-minus-polar source.
-/

open Complex Filter Topology Set MeasureTheory

noncomputable section

namespace GaloisForLFunctions.RHTower

def unitExponentialThirdDifferenceWeakGenerator (a h u : ℝ) : ℝ :=
  if u ≤ a then 0
  else if u ≤ a + h then unitExponentialThirdDifferenceFirstGenerator a u
  else if u ≤ a + 2 * h then unitExponentialThirdDifferenceMiddleGenerator a h u
  else if u ≤ a + 3 * h then unitExponentialThirdDifferenceLastGenerator a h u
  else 0

def unitExponentialThirdDifferenceGraphLeakProfile (a h u : ℝ) : ℂ :=
  (2 * unitExponentialThirdDifferenceWeakGenerator a h u : ℝ) +
    Complex.I * (unitExponentialThirdDifferenceResponse a h u : ℝ)

theorem measurable_unitExponentialThirdDifferenceWeakGenerator (a h : ℝ) :
    Measurable (unitExponentialThirdDifferenceWeakGenerator a h) := by
  have hfirst : Measurable (unitExponentialThirdDifferenceFirstGenerator a) := by
    unfold unitExponentialThirdDifferenceFirstGenerator
    fun_prop
  have hmiddle : Measurable (unitExponentialThirdDifferenceMiddleGenerator a h) := by
    unfold unitExponentialThirdDifferenceMiddleGenerator
    fun_prop
  have hlast : Measurable (unitExponentialThirdDifferenceLastGenerator a h) := by
    unfold unitExponentialThirdDifferenceLastGenerator
    fun_prop
  unfold unitExponentialThirdDifferenceWeakGenerator
  exact Measurable.ite measurableSet_Iic measurable_const
    (Measurable.ite measurableSet_Iic hfirst
      (Measurable.ite measurableSet_Iic hmiddle
        (Measurable.ite measurableSet_Iic hlast measurable_const)))

theorem continuous_unitExponentialThirdDifferenceResponse (a h : ℝ) :
    Continuous (unitExponentialThirdDifferenceResponse a h) := by
  unfold unitExponentialThirdDifferenceResponse unitExponentialIncrementKernel
  fun_prop

theorem measurable_unitExponentialThirdDifferenceGraphLeakProfile (a h : ℝ) :
    Measurable (unitExponentialThirdDifferenceGraphLeakProfile a h) := by
  unfold unitExponentialThirdDifferenceGraphLeakProfile
  have hw : Measurable (fun u => ((2 *
      unitExponentialThirdDifferenceWeakGenerator a h u : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp
      ((measurable_unitExponentialThirdDifferenceWeakGenerator a h).const_mul 2)
  have hg : Measurable (fun u => ((unitExponentialThirdDifferenceResponse a h u : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp
      (continuous_unitExponentialThirdDifferenceResponse a h).measurable
  exact hw.add (measurable_const.mul hg)

theorem leakDensity_unitExponentialThirdDifferenceGraphLeakProfile (a h u : ℝ) :
    leakDensity (unitExponentialThirdDifferenceGraphLeakProfile a h) u =
      4 * unitExponentialThirdDifferenceWeakGenerator a h u ^ (2 : ℕ) +
        unitExponentialThirdDifferenceResponse a h u ^ (2 : ℕ) := by
  unfold leakDensity unitExponentialThirdDifferenceGraphLeakProfile
  rw [Complex.sq_norm]
  simp [Complex.normSq_apply]
  ring

theorem unitExponentialThirdDifferenceWeakGenerator_eq_first
    {a h u : ℝ} (hu0 : a < u) (hu1 : u ≤ a + h) :
    unitExponentialThirdDifferenceWeakGenerator a h u =
      unitExponentialThirdDifferenceFirstGenerator a u := by
  simp [unitExponentialThirdDifferenceWeakGenerator, not_le_of_gt hu0, hu1]

theorem unitExponentialThirdDifferenceWeakGenerator_eq_middle
    {a h u : ℝ} (hu1 : a + h < u) (hu2 : u ≤ a + 2 * h) :
    unitExponentialThirdDifferenceWeakGenerator a h u =
      unitExponentialThirdDifferenceMiddleGenerator a h u := by
  have hu0 : ¬ u ≤ a := by linarith
  simp [unitExponentialThirdDifferenceWeakGenerator, hu0, not_le_of_gt hu1, hu2]

theorem unitExponentialThirdDifferenceWeakGenerator_eq_last
    {a h u : ℝ} (hu2 : a + 2 * h < u) (hu3 : u ≤ a + 3 * h) :
    unitExponentialThirdDifferenceWeakGenerator a h u =
      unitExponentialThirdDifferenceLastGenerator a h u := by
  have hu0 : ¬ u ≤ a := by linarith
  have hu1 : ¬ u ≤ a + h := by linarith
  simp [unitExponentialThirdDifferenceWeakGenerator, hu0, hu1, not_le_of_gt hu2, hu3]

theorem unitExponentialThirdDifferenceWeakGenerator_eq_zero_of_le
    {a h u : ℝ} (hu : u ≤ a) :
    unitExponentialThirdDifferenceWeakGenerator a h u = 0 := by
  simp [unitExponentialThirdDifferenceWeakGenerator, hu]

theorem unitExponentialThirdDifferenceWeakGenerator_eq_zero_of_gt
    {a h u : ℝ} (hh : 0 ≤ h) (hu : a + 3 * h < u) :
    unitExponentialThirdDifferenceWeakGenerator a h u = 0 := by
  have hu0 : ¬ u ≤ a := by linarith
  have hu1 : ¬ u ≤ a + h := by linarith
  have hu2 : ¬ u ≤ a + 2 * h := by linarith
  simp [unitExponentialThirdDifferenceWeakGenerator, hu0, hu1, hu2, not_le_of_gt hu]

theorem leakProfile_unitExponentialThirdDifferenceGraphLeakProfile
    {a h : ℝ} (hh : 0 ≤ h) :
    LeakProfile (unitExponentialThirdDifferenceGraphLeakProfile a h) := by
  constructor
  · exact (measurable_unitExponentialThirdDifferenceGraphLeakProfile a h).aestronglyMeasurable
  · let F : ℝ → ℝ := fun u =>
      (1 + u) * leakDensity (unitExponentialThirdDifferenceGraphLeakProfile a h) u
    have hleft : IntegrableOn F (Ioc 0 a) := by
      refine (integrableOn_zero : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Ioc 0 a)).congr_fun
        ?_ measurableSet_Ioc
      intro u hu
      dsimp only [F]
      rw [leakDensity_unitExponentialThirdDifferenceGraphLeakProfile,
        unitExponentialThirdDifferenceWeakGenerator_eq_zero_of_le hu.2,
        unitExponentialThirdDifferenceResponse_eq_zero_of_le hh hu.2]
      ring
    have hfirst : IntegrableOn F (Ioc a (a + h)) := by
      have hgen : Continuous (unitExponentialThirdDifferenceFirstGenerator a) := by
        unfold unitExponentialThirdDifferenceFirstGenerator
        fun_prop
      have hc : Continuous (fun u : ℝ =>
          (1 + u) * (4 * unitExponentialThirdDifferenceFirstGenerator a u ^ (2 : ℕ) +
            unitExponentialThirdDifferenceResponse a h u ^ (2 : ℕ))) := by
        exact (continuous_const.add continuous_id).mul
          ((continuous_const.mul (hgen.pow 2)).add
            ((continuous_unitExponentialThirdDifferenceResponse a h).pow 2))
      refine (hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self).congr_fun ?_
        measurableSet_Ioc
      intro u hu
      dsimp only [F]
      rw [leakDensity_unitExponentialThirdDifferenceGraphLeakProfile,
        unitExponentialThirdDifferenceWeakGenerator_eq_first hu.1 hu.2]
    have hmiddle : IntegrableOn F (Ioc (a + h) (a + 2 * h)) := by
      have hgen : Continuous (unitExponentialThirdDifferenceMiddleGenerator a h) := by
        unfold unitExponentialThirdDifferenceMiddleGenerator
        fun_prop
      have hc : Continuous (fun u : ℝ =>
          (1 + u) * (4 * unitExponentialThirdDifferenceMiddleGenerator a h u ^ (2 : ℕ) +
            unitExponentialThirdDifferenceResponse a h u ^ (2 : ℕ))) := by
        exact (continuous_const.add continuous_id).mul
          ((continuous_const.mul (hgen.pow 2)).add
            ((continuous_unitExponentialThirdDifferenceResponse a h).pow 2))
      refine (hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self).congr_fun ?_
        measurableSet_Ioc
      intro u hu
      dsimp only [F]
      rw [leakDensity_unitExponentialThirdDifferenceGraphLeakProfile,
        unitExponentialThirdDifferenceWeakGenerator_eq_middle hu.1 hu.2]
    have hlast : IntegrableOn F (Ioc (a + 2 * h) (a + 3 * h)) := by
      have hgen : Continuous (unitExponentialThirdDifferenceLastGenerator a h) := by
        unfold unitExponentialThirdDifferenceLastGenerator
        fun_prop
      have hc : Continuous (fun u : ℝ =>
          (1 + u) * (4 * unitExponentialThirdDifferenceLastGenerator a h u ^ (2 : ℕ) +
            unitExponentialThirdDifferenceResponse a h u ^ (2 : ℕ))) := by
        exact (continuous_const.add continuous_id).mul
          ((continuous_const.mul (hgen.pow 2)).add
            ((continuous_unitExponentialThirdDifferenceResponse a h).pow 2))
      refine (hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self).congr_fun ?_
        measurableSet_Ioc
      intro u hu
      dsimp only [F]
      rw [leakDensity_unitExponentialThirdDifferenceGraphLeakProfile,
        unitExponentialThirdDifferenceWeakGenerator_eq_last hu.1 hu.2]
    have hright : IntegrableOn F (Ioi (a + 3 * h)) := by
      refine (integrableOn_zero : IntegrableOn (fun _ : ℝ => (0 : ℝ))
        (Ioi (a + 3 * h))).congr_fun ?_ measurableSet_Ioi
      intro u hu
      dsimp only [F]
      rw [leakDensity_unitExponentialThirdDifferenceGraphLeakProfile,
        unitExponentialThirdDifferenceWeakGenerator_eq_zero_of_gt hh hu,
        unitExponentialThirdDifferenceResponse_eq_zero_of_ge hh hu.le]
      ring
    have hall := hleft.union (hfirst.union (hmiddle.union (hlast.union hright)))
    exact hall.mono_set (by
      intro u hu
      simp only [mem_Ioi, mem_union, mem_Ioc]
      by_cases h0 : u ≤ a
      · exact Or.inl ⟨hu, h0⟩
      · right
        by_cases h1 : u ≤ a + h
        · exact Or.inl ⟨lt_of_not_ge h0, h1⟩
        · right
          by_cases h2 : u ≤ a + 2 * h
          · exact Or.inl ⟨lt_of_not_ge h1, h2⟩
          · right
            by_cases h3 : u ≤ a + 3 * h
            · exact Or.inl ⟨lt_of_not_ge h2, h3⟩
            · exact Or.inr (lt_of_not_ge h3))

theorem integral_leakDensity_unitExponentialThirdDifferenceGraphLeakProfile
    {a h : ℝ} (ha : 0 ≤ a) (hh : 0 ≤ h) :
    (∫ u in Ioi (0 : ℝ),
        leakDensity (unitExponentialThirdDifferenceGraphLeakProfile a h) u) =
      unitExponentialThirdDifferenceGeneratorEnergy a h := by
  let D : ℝ → ℝ := fun u =>
    leakDensity (unitExponentialThirdDifferenceGraphLeakProfile a h) u
  have hp := leakProfile_unitExponentialThirdDifferenceGraphLeakProfile (a := a) (h := h) hh
  have hint : IntegrableOn D (Ioi (0 : ℝ)) := hp.integrable
  have ha1 : 0 ≤ a + h := by linarith
  have ha2 : 0 ≤ a + 2 * h := by linarith
  have ha3 : 0 ≤ a + 3 * h := by linarith
  have h0 : IntegrableOn D (Ioc 0 a) := hint.mono_set (by
    intro u hu
    exact hu.1)
  have h1 : IntegrableOn D (Ioc a (a + h)) := hint.mono_set (by
    intro u hu
    exact lt_of_le_of_lt ha hu.1)
  have h2 : IntegrableOn D (Ioc (a + h) (a + 2 * h)) := hint.mono_set (by
    intro u hu
    exact lt_of_le_of_lt ha1 hu.1)
  have h3 : IntegrableOn D (Ioc (a + 2 * h) (a + 3 * h)) := hint.mono_set (by
    intro u hu
    exact lt_of_le_of_lt ha2 hu.1)
  have ht0 : IntegrableOn D (Ioi a) := hint.mono_set (Ioi_subset_Ioi ha)
  have ht1 : IntegrableOn D (Ioi (a + h)) := hint.mono_set (Ioi_subset_Ioi ha1)
  have ht2 : IntegrableOn D (Ioi (a + 2 * h)) := hint.mono_set (Ioi_subset_Ioi ha2)
  have ht3 : IntegrableOn D (Ioi (a + 3 * h)) := hint.mono_set (Ioi_subset_Ioi ha3)
  have hz0 : (∫ u in Ioc 0 a, D u) = 0 := by
    rw [show (∫ u in Ioc 0 a, D u) = ∫ _u in Ioc 0 a, (0 : ℝ) by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro u hu
      dsimp only [D]
      rw [leakDensity_unitExponentialThirdDifferenceGraphLeakProfile,
        unitExponentialThirdDifferenceWeakGenerator_eq_zero_of_le hu.2,
        unitExponentialThirdDifferenceResponse_eq_zero_of_le hh hu.2]
      ring]
    simp
  have hz3 : (∫ u in Ioi (a + 3 * h), D u) = 0 := by
    rw [show (∫ u in Ioi (a + 3 * h), D u) =
        ∫ _u in Ioi (a + 3 * h), (0 : ℝ) by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      dsimp only [D]
      rw [leakDensity_unitExponentialThirdDifferenceGraphLeakProfile,
        unitExponentialThirdDifferenceWeakGenerator_eq_zero_of_gt hh hu,
        unitExponentialThirdDifferenceResponse_eq_zero_of_ge hh hu.le]
      ring]
    simp
  have hc1 : (∫ u in Ioc a (a + h), D u) =
      ∫ u in a..(a + h),
        4 * unitExponentialThirdDifferenceFirstGenerator a u ^ (2 : ℕ) +
          unitExponentialThirdDifferenceResponse a h u ^ (2 : ℕ) := by
    rw [intervalIntegral.integral_of_le (by linarith : a ≤ a + h)]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro u hu
    dsimp only [D]
    rw [leakDensity_unitExponentialThirdDifferenceGraphLeakProfile,
      unitExponentialThirdDifferenceWeakGenerator_eq_first hu.1 hu.2]
  have hc2 : (∫ u in Ioc (a + h) (a + 2 * h), D u) =
      ∫ u in (a + h)..(a + 2 * h),
        4 * unitExponentialThirdDifferenceMiddleGenerator a h u ^ (2 : ℕ) +
          unitExponentialThirdDifferenceResponse a h u ^ (2 : ℕ) := by
    rw [intervalIntegral.integral_of_le (by linarith : a + h ≤ a + 2 * h)]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro u hu
    dsimp only [D]
    rw [leakDensity_unitExponentialThirdDifferenceGraphLeakProfile,
      unitExponentialThirdDifferenceWeakGenerator_eq_middle hu.1 hu.2]
  have hc3 : (∫ u in Ioc (a + 2 * h) (a + 3 * h), D u) =
      ∫ u in (a + 2 * h)..(a + 3 * h),
        4 * unitExponentialThirdDifferenceLastGenerator a h u ^ (2 : ℕ) +
          unitExponentialThirdDifferenceResponse a h u ^ (2 : ℕ) := by
    rw [intervalIntegral.integral_of_le (by linarith : a + 2 * h ≤ a + 3 * h)]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro u hu
    dsimp only [D]
    rw [leakDensity_unitExponentialThirdDifferenceGraphLeakProfile,
      unitExponentialThirdDifferenceWeakGenerator_eq_last hu.1 hu.2]
  have hs0 : Ioi (0 : ℝ) = Ioc 0 a ∪ Ioi a :=
    (Ioc_union_Ioi_eq_Ioi ha).symm
  have hs1 : Ioi a = Ioc a (a + h) ∪ Ioi (a + h) :=
    (Ioc_union_Ioi_eq_Ioi (by linarith)).symm
  have hs2 : Ioi (a + h) = Ioc (a + h) (a + 2 * h) ∪ Ioi (a + 2 * h) :=
    (Ioc_union_Ioi_eq_Ioi (by linarith)).symm
  have hs3 : Ioi (a + 2 * h) =
      Ioc (a + 2 * h) (a + 3 * h) ∪ Ioi (a + 3 * h) :=
    (Ioc_union_Ioi_eq_Ioi (by linarith)).symm
  rw [show (∫ u in Ioi (0 : ℝ),
        leakDensity (unitExponentialThirdDifferenceGraphLeakProfile a h) u) =
      ∫ u in Ioi (0 : ℝ), D u from rfl]
  rw [hs0, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi h0 ht0,
    hs1, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi h1 ht1,
    hs2, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi h2 ht2,
    hs3, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi h3 ht3,
    hz0, hz3, hc1, hc2, hc3]
  unfold unitExponentialThirdDifferenceGeneratorEnergy
  ring

/-- Exact CCM-HG weld: coherent packet's source Gram is one quarter of initial Hankel boundary
relative-trace slope of complex first-order graph leak `2g' + i g`. -/
theorem tendsto_boundaryRelativeTrace_div_unitExponentialThirdDifferenceGraphLeakProfile
    {a h : ℝ} (ha : 0 ≤ a) (hh : 0 ≤ h) :
    Tendsto (fun u : ℝ =>
        boundaryRelativeTrace (unitExponentialThirdDifferenceGraphLeakProfile a h) u / u)
      (𝓝[>] (0 : ℝ))
      (𝓝 (4 * unitExponentialThirdDifferenceSourceGram a h)) := by
  have hlim := tendsto_boundaryRelativeTrace_div
    (leakProfile_unitExponentialThirdDifferenceGraphLeakProfile (a := a) (h := h) hh)
  rw [integral_leakDensity_unitExponentialThirdDifferenceGraphLeakProfile ha hh,
    unitExponentialThirdDifferenceGeneratorEnergy_eq_sourceGram a hh] at hlim
  exact hlim

/-- On coherent third-difference packets, HG four-unit infinitesimal contractivity is exactly the
unit ball of source-Gram energy. -/
theorem unitExponentialThirdDifferenceGraphLeakProfile_density_le_four_iff
    {a h : ℝ} (ha : 0 ≤ a) (hh : 0 ≤ h) :
    (∀ L : ℝ,
        Tendsto (fun u : ℝ =>
            boundaryRelativeTrace (unitExponentialThirdDifferenceGraphLeakProfile a h) u / u)
          (𝓝[>] (0 : ℝ)) (𝓝 L) → L ≤ 4) ↔
      unitExponentialThirdDifferenceSourceGram a h ≤ 1 := by
  have hlim :=
    tendsto_boundaryRelativeTrace_div_unitExponentialThirdDifferenceGraphLeakProfile ha hh
  constructor
  · intro hall
    have hle := hall _ hlim
    linarith
  · intro hgram L hL
    have hEq : L = 4 * unitExponentialThirdDifferenceSourceGram a h :=
      tendsto_nhds_unique hL hlim
    rw [hEq]
    linarith

/-- Fixed coherent evaluation is recovered exactly from the HG graph-leak boundary slope. -/
theorem tendsto_unitExponentialThirdDifference_fixedSample_boundaryDensity
    {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
    Tendsto (fun u : ℝ =>
        ((Real.exp (h / 2) - Real.exp (-h / 2)) /
          (8 * unitExponentialThirdDifferenceCoefficient h)) *
        (boundaryRelativeTrace
          (unitExponentialThirdDifferenceGraphLeakProfile (1 - h) h) u / u))
      (𝓝[>] (0 : ℝ))
      (𝓝 (unitExponentialThirdDifferenceResponse (1 - h) h 1 ^ (2 : ℕ))) := by
  have hlim :=
    (tendsto_boundaryRelativeTrace_div_unitExponentialThirdDifferenceGraphLeakProfile
      (a := 1 - h) (h := h) (by linarith) hh.le).const_mul
        ((Real.exp (h / 2) - Real.exp (-h / 2)) /
          (8 * unitExponentialThirdDifferenceCoefficient h))
  have hsample := unitExponentialThirdDifference_fixedSample_eq_sourceGram hh
  convert hlim using 1
  rw [hsample]
  field_simp
  ring

end GaloisForLFunctions.RHTower

