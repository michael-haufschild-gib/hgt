import GaloisForLFunctions.RHTower.CCMLogarithmicWeilFormTransport
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# Explicit global archimedean Weil distribution

The pointwise density `√ρ/2 (1/(1+ρ)+1/|1-ρ|)` in Connes--Consani Proposition
`lemsch7(iii)` is not a function at `ρ=1`; it denotes a finite-part distribution.  This file
constructs that distribution independently of any operator trace, using the cancellation formula
from the paper's Appendix.  Its natural literature test space `C_c^∞(ℝ₊*)` is represented after
logarithmic pullback by compactly supported Schwartz functions.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace FourierTransform SchwartzMap

noncomputable section

namespace RHTower

/-- Logarithmic model of a `C_c^∞(ℝ₊*)` test.  An explicit support radius makes compact
support usable without any theorem premise at the distribution endpoint. -/
structure CCMCompactSchwartzLogTest where
  toSchwartzMap : SchwartzMap ℝ ℂ
  radius : ℝ
  one_lt_radius : 1 < radius
  eq_zero_of_radius_le_abs : ∀ x : ℝ, radius ≤ |x| → toSchwartzMap x = 0

instance : CoeFun CCMCompactSchwartzLogTest (fun _ => ℝ → ℂ) :=
  ⟨fun F => F.toSchwartzMap⟩

/-- Half-density numerator whose zero at the origin cancels the Weil singularity. -/
def ccmArchimedeanWeilSharpNumerator
    (F : CCMCompactSchwartzLogTest) (h : ℝ) : ℂ :=
  (Real.exp (h / 2) : ℂ) * F h - F 0

/-- Explicit singular-cancellation integrand in logarithmic coordinates. -/
def ccmArchimedeanWeilSharpIntegrand
    (F : CCMCompactSchwartzLogTest) (h : ℝ) : ℂ :=
  ccmArchimedeanWeilSharpNumerator F h /
    (Real.exp h - Real.exp (-h) : ℝ)

theorem ccmArchimedeanWeilSharpNumerator_zero
    (F : CCMCompactSchwartzLogTest) :
    ccmArchimedeanWeilSharpNumerator F 0 = 0 := by
  simp [ccmArchimedeanWeilSharpNumerator]

theorem half_exp_le_exp_sub_exp_neg {h : ℝ} (hh : 1 ≤ h) :
    Real.exp h / 2 ≤ Real.exp h - Real.exp (-h) := by
  have hsq : 2 ≤ Real.exp h * Real.exp h := by
    calc
      2 ≤ 2 * h + 1 := by linarith
      _ ≤ Real.exp (2 * h) := Real.add_one_le_exp (2 * h)
      _ = Real.exp h * Real.exp h := by rw [show 2 * h = h + h by ring, Real.exp_add]
  have hinv : Real.exp (-h) * Real.exp h = 1 := by
    rw [← Real.exp_add]
    simp
  nlinarith [Real.exp_pos h, Real.exp_pos (-h)]

theorem inv_exp_sub_exp_neg_le {h : ℝ} (hh : 1 ≤ h) :
    (Real.exp h - Real.exp (-h))⁻¹ ≤ 2 * Real.exp (-h) := by
  have hlower := half_exp_le_exp_sub_exp_neg hh
  have hden : 0 < Real.exp h - Real.exp (-h) :=
    lt_of_lt_of_le (half_pos (Real.exp_pos h)) hlower
  rw [inv_le_iff_one_le_mul₀ hden]
  have hinv : Real.exp (-h) * Real.exp h = 1 := by
    rw [← Real.exp_add]
    simp
  nlinarith [Real.exp_pos h, Real.exp_pos (-h)]

private def ccmArchimedeanWeilAmplitude
    (F : CCMCompactSchwartzLogTest) (h : ℝ) : ℂ :=
  Complex.exp ((h : ℂ) / 2) * F h

private theorem exists_norm_ccmArchimedeanWeilSharpNumerator_le
    (F : CCMCompactSchwartzLogTest) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h ∈ Icc (0 : ℝ) 1,
      ‖ccmArchimedeanWeilSharpNumerator F h‖ ≤ C * h := by
  have hsmooth : ContDiff ℝ 1 (ccmArchimedeanWeilAmplitude F) := by
    unfold ccmArchimedeanWeilAmplitude
    exact (Complex.ofRealCLM.contDiff.div_const 2).cexp.mul
      (F.toSchwartzMap.smooth 1)
  have hderivCont : Continuous (fun h => ‖deriv (ccmArchimedeanWeilAmplitude F) h‖) :=
    (hsmooth.continuous_deriv (by norm_num)).norm
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr zero_le_one) hderivCont.continuousOn
  refine ⟨‖deriv (ccmArchimedeanWeilAmplitude F) x‖, norm_nonneg _, ?_⟩
  intro h hh
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := ccmArchimedeanWeilAmplitude F)
    (f' := deriv (ccmArchimedeanWeilAmplitude F))
    (C := ‖deriv (ccmArchimedeanWeilAmplitude F) x‖)
    (fun y _ => ((hsmooth.differentiable (by norm_num)) y).hasDerivAt.hasDerivWithinAt)
    (fun y hy => hmax (Ico_subset_Icc_self hy)) h hh
  simpa [ccmArchimedeanWeilAmplitude,
    ccmArchimedeanWeilSharpNumerator, Complex.ofReal_exp] using hmv

private theorem exists_norm_ccmArchimedeanWeilSharpIntegrand_le_local
    (F : CCMCompactSchwartzLogTest) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h ∈ Ioc (0 : ℝ) 1,
      ‖ccmArchimedeanWeilSharpIntegrand F h‖ ≤ C := by
  obtain ⟨C, hC, hnum⟩ := exists_norm_ccmArchimedeanWeilSharpNumerator_le F
  refine ⟨C, hC, ?_⟩
  intro h hh
  have hdenLower : h ≤ Real.exp h - Real.exp (-h) := by
    have h1 := Real.add_one_le_exp h
    have h2 : Real.exp (-h) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hh.1])
    linarith
  have hden : 0 < Real.exp h - Real.exp (-h) := lt_of_lt_of_le hh.1 hdenLower
  have hn := hnum h ⟨hh.1.le, hh.2⟩
  rw [ccmArchimedeanWeilSharpIntegrand, norm_div,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hden]
  rw [div_le_iff₀ hden]
  exact hn.trans (mul_le_mul_of_nonneg_left hdenLower hC)

private theorem measurable_ccmArchimedeanWeilSharpIntegrand
    (F : CCMCompactSchwartzLogTest) :
    Measurable (ccmArchimedeanWeilSharpIntegrand F) := by
  unfold ccmArchimedeanWeilSharpIntegrand ccmArchimedeanWeilSharpNumerator
  fun_prop

private theorem integrableOn_ccmArchimedeanWeilSharpIntegrand_near_zero
    (F : CCMCompactSchwartzLogTest) :
    IntegrableOn (ccmArchimedeanWeilSharpIntegrand F) (Ioc (0 : ℝ) 1) := by
  obtain ⟨C, -, hbound⟩ :=
    exists_norm_ccmArchimedeanWeilSharpIntegrand_le_local F
  have hconst : IntegrableOn
      (fun _ : ℝ => C) (Ioc (0 : ℝ) 1) :=
    integrableOn_const (ne_of_lt measure_Ioc_lt_top)
  refine hconst.mono'
    (measurable_ccmArchimedeanWeilSharpIntegrand F).aestronglyMeasurable.restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with h hh
  exact hbound h hh

private theorem integrableOn_ccmArchimedeanWeilSharpIntegrand_middle
    (F : CCMCompactSchwartzLogTest) :
    IntegrableOn (ccmArchimedeanWeilSharpIntegrand F) (Ioc 1 F.radius) := by
  have hcont : ContinuousOn (ccmArchimedeanWeilSharpIntegrand F) (Icc 1 F.radius) := by
    unfold ccmArchimedeanWeilSharpIntegrand ccmArchimedeanWeilSharpNumerator
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro h hh
      exact_mod_cast sub_ne_zero.mpr (ne_of_gt
        (Real.exp_lt_exp.mpr (by linarith [hh.1])))
  exact (hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self)

private theorem norm_ccmArchimedeanWeilSharpIntegrand_le_tail
    (F : CCMCompactSchwartzLogTest) {h : ℝ} (hh : h ∈ Ioi F.radius) :
    ‖ccmArchimedeanWeilSharpIntegrand F h‖ ≤
      2 * ‖F 0‖ * Real.exp (-h) := by
  have hhR : F.radius < h := hh
  have hh1 : 1 ≤ h := by linarith [F.one_lt_radius, hhR]
  have hzero : F h = 0 := F.eq_zero_of_radius_le_abs h (by
    rw [abs_of_pos (by linarith [F.one_lt_radius, hhR])]
    exact hhR.le)
  have hden : 0 < Real.exp h - Real.exp (-h) :=
    lt_of_lt_of_le (half_pos (Real.exp_pos h)) (half_exp_le_exp_sub_exp_neg hh1)
  rw [ccmArchimedeanWeilSharpIntegrand,
    ccmArchimedeanWeilSharpNumerator, hzero, mul_zero, zero_sub,
    norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hden, norm_neg,
    div_eq_mul_inv]
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    (mul_le_mul_of_nonneg_left (inv_exp_sub_exp_neg_le hh1) (norm_nonneg (F 0)))

private theorem integrableOn_ccmArchimedeanWeilSharpIntegrand_tail
    (F : CCMCompactSchwartzLogTest) :
    IntegrableOn (ccmArchimedeanWeilSharpIntegrand F) (Ioi F.radius) := by
  have hdom : IntegrableOn (fun h : ℝ => 2 * ‖F 0‖ * Real.exp (-h))
      (Ioi F.radius) := by
    change Integrable (fun h : ℝ => 2 * ‖F 0‖ * Real.exp (-h))
      (volume.restrict (Ioi F.radius))
    simpa only [one_mul, neg_mul] using
      (exp_neg_integrableOn_Ioi F.radius (b := 1) zero_lt_one).const_mul
        (2 * ‖F 0‖)
  refine hdom.mono'
    (measurable_ccmArchimedeanWeilSharpIntegrand F).aestronglyMeasurable.restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
  exact norm_ccmArchimedeanWeilSharpIntegrand_le_tail F hh

/-- The finite-part cancellation formula is genuinely Lebesgue integrable on every compact smooth
logarithmic test.  This is the analytic well-definedness missing from a pointwise use of
`1/|1-ρ|`. -/
theorem ccmArchimedeanWeilSharpIntegrand_integrableOn_Ioi
    (F : CCMCompactSchwartzLogTest) :
    IntegrableOn (ccmArchimedeanWeilSharpIntegrand F) (Ioi (0 : ℝ)) := by
  have hparts := (integrableOn_ccmArchimedeanWeilSharpIntegrand_near_zero F).union
    ((integrableOn_ccmArchimedeanWeilSharpIntegrand_middle F).union
      (integrableOn_ccmArchimedeanWeilSharpIntegrand_tail F))
  have hset : Ioc (0 : ℝ) 1 ∪ (Ioc 1 F.radius ∪ Ioi F.radius) = Ioi 0 := by
    ext h
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (⟨h0, h1⟩ | ⟨h1, hR⟩ | hR)
      · exact h0
      · linarith
      · linarith [F.one_lt_radius]
    · intro h0
      rcases le_total h 1 with h1 | h1
      · exact Or.inl ⟨h0, h1⟩
      · by_cases heq1 : h = 1
        · subst h
          exact Or.inl ⟨zero_lt_one, le_rfl⟩
        · have h1' : 1 < h := lt_of_le_of_ne h1 (Ne.symm heq1)
          rcases le_total h F.radius with hR | hR
          · exact Or.inr (Or.inl ⟨h1', hR⟩)
          · by_cases heq : h = F.radius
            · subst h
              exact Or.inr (Or.inl ⟨F.one_lt_radius, le_rfl⟩)
            · exact Or.inr (Or.inr (lt_of_le_of_ne hR (Ne.symm heq)))
  rw [← hset]
  exact hparts

/-- Explicit global one-sided archimedean Weil distribution `W_ℝ#`, defined independently of
the CCM operator trace. -/
def ccmArchimedeanWeilSharpDistribution
    (F : CCMCompactSchwartzLogTest) : ℂ :=
  F 0 / 2 * (Real.log (4 * Real.pi) + Real.eulerMascheroniConstant : ℂ) +
    ∫ h in Ioi (0 : ℝ), ccmArchimedeanWeilSharpIntegrand F h

/-- Finite apertures recover exactly the already formalized restricted archimedean functional,
with the remaining term given by the absolutely convergent tail. -/
theorem ccmArchimedeanWeilSharpDistribution_eq_restricted_add_tail
    (F : CCMCompactSchwartzLogTest) (a : NNReal) :
    ccmArchimedeanWeilSharpDistribution F =
      ccmRestrictedArchimedeanSharp (a : ℝ) F +
        ∫ h in Ioi (2 * (a : ℝ)), ccmArchimedeanWeilSharpIntegrand F h := by
  have hleft := (ccmArchimedeanWeilSharpIntegrand_integrableOn_Ioi F).mono_set
    (show Ioc (0 : ℝ) (2 * (a : ℝ)) ⊆ Ioi 0 by intro h hh; exact hh.1)
  have hright := (ccmArchimedeanWeilSharpIntegrand_integrableOn_Ioi F).mono_set
    (show Ioi (2 * (a : ℝ)) ⊆ Ioi 0 by
      intro h hh
      have ha : 0 ≤ (a : ℝ) := a.property
      have hh' : 2 * (a : ℝ) < h := hh
      exact lt_of_le_of_lt (mul_nonneg (by norm_num) ha) hh')
  have hset : Ioc (0 : ℝ) (2 * (a : ℝ)) ∪ Ioi (2 * (a : ℝ)) = Ioi 0 := by
    ext h
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (⟨h0, htop⟩ | htail)
      · exact h0
      · have ha : 0 ≤ (a : ℝ) := a.property
        linarith
    · intro h0
      exact (le_total h (2 * (a : ℝ))).elim
        (fun hh => Or.inl ⟨h0, hh⟩) (fun hh => by
          rcases hh.eq_or_lt with rfl | hh
          · exact Or.inl ⟨h0, le_rfl⟩
          · exact Or.inr hh)
  have hsplit := setIntegral_union
    (f := ccmArchimedeanWeilSharpIntegrand F)
    (show Disjoint (Ioc (0 : ℝ) (2 * (a : ℝ))) (Ioi (2 * (a : ℝ))) by
      refine Set.disjoint_left.2 ?_
      intro h hleft hright
      exact (not_lt_of_ge hleft.2) hright)
    measurableSet_Ioi hleft hright
  rw [hset] at hsplit
  unfold ccmArchimedeanWeilSharpDistribution ccmRestrictedArchimedeanSharp
  rw [hsplit]
  simp only [ccmArchimedeanWeilSharpIntegrand,
    ccmArchimedeanWeilSharpNumerator]
  ring

end RHTower
