import GaloisForLFunctions.RHTower.CCM.CCMActualHeadWallGramSignedProducer
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilApertureMonotonicity
import GaloisForLFunctions.RHTower.CCM.CCMUnitRieszMarkovTransform
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCauchyWallUnitRieszIsometry

/-!
# Actual-head Γ-wall outgoing signed producer

The first Binet mode of the quarter-line Γ density is exactly `exp (-h/2)`, the same scalar
kernel carried by the Cauchy wall. On an aperture head its exterior translation defect is constant,
so this Γ mode splits into compact decaying polar debt plus the exact tail

`2 exp(-a) E_f(2a)`.

It therefore cancels the decaying half of `2 cosh(h/2) E_f(h)`. The tail simultaneously changes
the completed endpoint coefficient from

`4 sinh(a) - M(2a)` to `2 exp(a) - M(2a)`.

The resulting producer retains the literal higher Γ continuum, reflected prime-wall Gram, completed
arithmetic error, and growing polar continuum on one actual physical head. It is unconditionally
equal to the restricted-Weil source quadratic. On canonical finite Γ-Slepian heads its
nonnegativity is exactly the reverse-prime bound; no common-clock identification, RH premise,
numerical computation, or new axiom is used.
-/


open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct InnerProductSpace BigOperators

noncomputable section

namespace RHTower

/-- First atom in the quarter-line Γ Binet density. -/
def ccmGammaFirstBinetModeWeight (h : ℝ) : ℝ :=
  Real.exp (-(h / 2))

/-- Positive tail of the Γ Binet density after removing its first atom. -/
def ccmGammaHigherBinetModeDensity (h : ℝ) : ℝ :=
  Real.exp (-(h / 2)) * Real.exp (-(2 * h)) /
    (1 - Real.exp (-(2 * h)))

theorem ccmGammaHigherBinetModeDensity_pos {h : ℝ} (hh : 0 < h) :
    0 < ccmGammaHigherBinetModeDensity h := by
  unfold ccmGammaHigherBinetModeDensity
  exact div_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _))
    (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith)))

/-- Exact first-mode/higher-mode decomposition of the Γ translation density. -/
theorem ccmGammaTranslationDensity_eq_first_add_higher
    {h : ℝ} (hh : 0 < h) :
    ccmGammaTranslationDensity h =
      ccmGammaFirstBinetModeWeight h + ccmGammaHigherBinetModeDensity h := by
  let A : ℝ := Real.exp (-(h / 2))
  let B : ℝ := Real.exp (-(2 * h))
  have hden : 1 - B ≠ 0 :=
    ne_of_gt (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith)))
  unfold ccmGammaTranslationDensity ccmGammaFirstBinetModeWeight
    ccmGammaHigherBinetModeDensity
  change A / (1 - B) = A + A * B / (1 - B)
  field_simp [hden]
  ring

/-- The first Γ Binet mode is literally the real Cauchy-wall phase Gram at source separation
`h`. This is a scalar-kernel identification, not an identification of the CCM and Suzuki
operators. -/
theorem ccmGammaFirstBinetModeWeight_eq_cauchyWallPhaseInner_re
    {h : ℝ} (hh : 0 ≤ h) :
    ccmGammaFirstBinetModeWeight h =
      (GaloisForLFunctions.RHTower.suzukiCauchyWallPhaseInner 0 h).re := by
  rw [GaloisForLFunctions.RHTower.suzukiCauchyWallPhaseInner_eq]
  unfold ccmGammaFirstBinetModeWeight
  simp only [Complex.ofReal_re, zero_sub, abs_neg, abs_of_nonneg hh]
  congr 1
  ring

/-- The residual density is exactly the tail of the Γ Binet series after deleting its first
Cauchy-wall mode. -/
theorem ccmGammaHigherBinetModeDensity_eq_tsum_succ
    {h : ℝ} (hh : 0 < h) :
    ccmGammaHigherBinetModeDensity h =
      ∑' n : ℕ,
        Real.exp (-((2 * (((n + 1 : ℕ) : ℝ) + 1 / 4)) * h)) := by
  let T : ℕ → ℝ := fun n =>
    Real.exp (-((2 * ((n : ℝ) + 1 / 4)) * h))
  let x : ℝ := Real.exp (-(2 * h))
  let A : ℝ := Real.exp (-(h / 2))
  have hx0 : 0 ≤ x := by dsimp only [x]; positivity
  have hx1 : x < 1 := by
    dsimp only [x]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hterm (n : ℕ) : T n = A * x ^ n := by
    dsimp only [T, A, x]
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  have hsx : Summable fun n : ℕ => x ^ n :=
    summable_geometric_of_norm_lt_one (by
      rw [Real.norm_eq_abs, abs_of_nonneg hx0]
      exact hx1)
  have hs : Summable T := (hsx.mul_left A).congr fun n => (hterm n).symm
  have hsplit := hs.sum_add_tsum_nat_add 1
  have htotal := ccmGammaTranslationDensity_eq_tsum hh
  have hdecomp := ccmGammaTranslationDensity_eq_first_add_higher hh
  have hzero : T 0 = ccmGammaFirstBinetModeWeight h := by
    dsimp only [T]
    unfold ccmGammaFirstBinetModeWeight
    congr 1
    norm_num
    ring
  change ccmGammaHigherBinetModeDensity h = ∑' n : ℕ, T (n + 1)
  have htotalT : ccmGammaTranslationDensity h = ∑' n : ℕ, T n := by
    simpa only [T] using htotal
  have hdecompT : (∑' n : ℕ, T n) =
      ccmGammaFirstBinetModeWeight h + ccmGammaHigherBinetModeDensity h :=
    htotalT.symm.trans hdecomp
  simp only [Finset.sum_range_one] at hsplit
  rw [hzero] at hsplit
  linarith [hdecompT]

/-- Extended nonnegative first-Binet-mode translation energy of an actual head. -/
def ccmActualHeadGammaFirstBinetModeEnergyL (f : SoninL2) : ENNReal :=
  ∫⁻ h in Ioi (0 : ℝ), ENNReal.ofReal
    (ccmGammaFirstBinetModeWeight h * ccmActualHeadTranslationDefect h f)

/-- Extended nonnegative higher-Binet-mode translation energy of an actual head. -/
def ccmActualHeadGammaHigherBinetModeEnergyL (f : SoninL2) : ENNReal :=
  ∫⁻ h in Ioi (0 : ℝ), ENNReal.ofReal
    (ccmGammaHigherBinetModeDensity h * ccmActualHeadTranslationDefect h f)

/-- Finite real first-mode energy; finiteness follows for every `L²` head. -/
def ccmActualHeadGammaFirstBinetModeEnergy (f : SoninL2) : ℝ :=
  (ccmActualHeadGammaFirstBinetModeEnergyL f).toReal

/-- Real higher-mode Γ energy. It is finite on the complete archimedean form domain. -/
def ccmActualHeadGammaHigherBinetModeEnergy (f : SoninL2) : ℝ :=
  (ccmActualHeadGammaHigherBinetModeEnergyL f).toReal

theorem integrableOn_ccmGammaFirstBinetModeWeight_mul_translationDefect
    (f : SoninL2) :
    IntegrableOn (fun h : ℝ =>
      ccmGammaFirstBinetModeWeight h * ccmActualHeadTranslationDefect h f)
      (Ioi (0 : ℝ)) := by
  have hexp : IntegrableOn (fun h : ℝ => Real.exp (-(1 / 2 : ℝ) * h))
      (Ioi (0 : ℝ)) :=
    exp_neg_integrableOn_Ioi (b := (1 / 2 : ℝ)) (0 : ℝ) (by norm_num)
  have hmajor : IntegrableOn
      (fun h : ℝ => (4 * ‖f‖ ^ 2) * Real.exp (-(1 / 2 : ℝ) * h))
      (Ioi (0 : ℝ)) := hexp.const_mul _
  refine Integrable.mono' hmajor ?_ ?_
  · have hw : Continuous fun h : ℝ => ccmGammaFirstBinetModeWeight h := by
      unfold ccmGammaFirstBinetModeWeight
      fun_prop
    have hd : Continuous fun h : ℝ => ccmActualHeadTranslationDefect h f := by
      unfold ccmActualHeadTranslationDefect
      exact (((continuous_logTranslationCLM f).sub continuous_const).norm).pow 2
    exact (hw.mul hd).aestronglyMeasurable.restrict
  · filter_upwards with h
    have hw : 0 ≤ ccmGammaFirstBinetModeWeight h := by
      unfold ccmGammaFirstBinetModeWeight
      positivity
    have hdef : 0 ≤ ccmActualHeadTranslationDefect h f := by
      unfold ccmActualHeadTranslationDefect
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw hdef)]
    have hbound := ccmActualHeadTranslationDefect_le h f
    have heq : ccmGammaFirstBinetModeWeight h =
        Real.exp (-(1 / 2 : ℝ) * h) := by
      unfold ccmGammaFirstBinetModeWeight
      congr 1
      ring
    rw [heq]
    calc
      Real.exp (-(1 / 2 : ℝ) * h) * ccmActualHeadTranslationDefect h f ≤
          Real.exp (-(1 / 2 : ℝ) * h) * (4 * ‖f‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le
      _ = (4 * ‖f‖ ^ 2) * Real.exp (-(1 / 2 : ℝ) * h) := by ring

theorem ccmActualHeadGammaFirstBinetModeEnergy_eq_integral (f : SoninL2) :
    ccmActualHeadGammaFirstBinetModeEnergy f =
      ∫ h in Ioi (0 : ℝ),
        ccmGammaFirstBinetModeWeight h * ccmActualHeadTranslationDefect h f := by
  have hint := integrableOn_ccmGammaFirstBinetModeWeight_mul_translationDefect f
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fun h : ℝ =>
      ccmGammaFirstBinetModeWeight h * ccmActualHeadTranslationDefect h f := by
    filter_upwards with h
    exact mul_nonneg (by unfold ccmGammaFirstBinetModeWeight; positivity)
      (by unfold ccmActualHeadTranslationDefect; positivity)
  unfold ccmActualHeadGammaFirstBinetModeEnergy
    ccmActualHeadGammaFirstBinetModeEnergyL
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg,
    ENNReal.toReal_ofReal (integral_nonneg_of_ae hnonneg)]

/-- Exact extended-energy split before taking finite real values. -/
theorem ccmActualHeadGammaAutocorrelationEnergyL_eq_first_add_higher
    (f : SoninL2) :
    ccmActualHeadGammaAutocorrelationEnergyL f =
      ccmActualHeadGammaFirstBinetModeEnergyL f +
        ccmActualHeadGammaHigherBinetModeEnergyL f := by
  let F : ℝ → ENNReal := fun h => ENNReal.ofReal
    (ccmGammaFirstBinetModeWeight h * ccmActualHeadTranslationDefect h f)
  let H : ℝ → ENNReal := fun h => ENNReal.ofReal
    (ccmGammaHigherBinetModeDensity h * ccmActualHeadTranslationDefect h f)
  have hFmeas : Measurable F := by
    dsimp only [F]
    apply Measurable.ennreal_ofReal
    have hw : Continuous fun h : ℝ => ccmGammaFirstBinetModeWeight h := by
      unfold ccmGammaFirstBinetModeWeight
      fun_prop
    have hd : Continuous fun h : ℝ => ccmActualHeadTranslationDefect h f := by
      unfold ccmActualHeadTranslationDefect
      exact (((continuous_logTranslationCLM f).sub continuous_const).norm).pow 2
    exact (hw.mul hd).measurable
  have hpoint : EqOn (fun h : ℝ => ENNReal.ofReal
      (ccmGammaTranslationDensity h * ccmActualHeadTranslationDefect h f))
      (fun h => F h + H h) (Ioi (0 : ℝ)) := by
    intro h hh
    have hfirst : 0 ≤ ccmGammaFirstBinetModeWeight h *
        ccmActualHeadTranslationDefect h f := mul_nonneg
      (by unfold ccmGammaFirstBinetModeWeight; positivity)
      (by unfold ccmActualHeadTranslationDefect; positivity)
    have hhigher : 0 ≤ ccmGammaHigherBinetModeDensity h *
        ccmActualHeadTranslationDefect h f := mul_nonneg
      (ccmGammaHigherBinetModeDensity_pos hh).le
      (by unfold ccmActualHeadTranslationDefect; positivity)
    dsimp only [F, H]
    rw [← ENNReal.ofReal_add hfirst hhigher]
    congr 1
    rw [ccmGammaTranslationDensity_eq_first_add_higher hh]
    ring
  unfold ccmActualHeadGammaAutocorrelationEnergyL
    ccmActualHeadGammaFirstBinetModeEnergyL
    ccmActualHeadGammaHigherBinetModeEnergyL
  rw [setLIntegral_congr_fun measurableSet_Ioi hpoint]
  exact lintegral_add_left hFmeas H

theorem ccmActualHeadGammaAutocorrelationEnergy_eq_first_add_higher_formDomain
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    ccmActualHeadGammaAutocorrelationEnergy
        (ccmArchimedeanFormToAperture a u : SoninL2) =
      ccmActualHeadGammaFirstBinetModeEnergy
          (ccmArchimedeanFormToAperture a u : SoninL2) +
        ccmActualHeadGammaHigherBinetModeEnergy
          (ccmArchimedeanFormToAperture a u : SoninL2) := by
  let f : SoninL2 := ccmArchimedeanFormToAperture a u
  have hgamma : ccmActualHeadGammaAutocorrelationEnergyL f ≠ ⊤ := by
    rw [ccmActualHeadGammaAutocorrelationEnergyL_formDomain]
    exact ENNReal.ofReal_ne_top
  have hsplit := ccmActualHeadGammaAutocorrelationEnergyL_eq_first_add_higher f
  have hfirst : ccmActualHeadGammaFirstBinetModeEnergyL f ≠ ⊤ := by
    apply ne_top_of_le_ne_top hgamma
    rw [hsplit]
    exact le_add_right le_rfl
  have hhigher : ccmActualHeadGammaHigherBinetModeEnergyL f ≠ ⊤ := by
    apply ne_top_of_le_ne_top hgamma
    rw [hsplit]
    exact le_add_left le_rfl
  unfold ccmActualHeadGammaAutocorrelationEnergy
    ccmActualHeadGammaFirstBinetModeEnergy
    ccmActualHeadGammaHigherBinetModeEnergy
  rw [hsplit, ENNReal.toReal_add hfirst hhigher]

theorem ccmActualHeadGammaHigherBinetModeEnergy_nonneg (f : SoninL2) :
    0 ≤ ccmActualHeadGammaHigherBinetModeEnergy f := ENNReal.toReal_nonneg

/-- Beyond aperture diameter, overlap vanishes and translation loss is constant. -/
theorem ccmActualHeadTranslationDefect_eq_two_norm_sq_of_two_aperture_lt
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a)
    {h : ℝ} (hh : 2 * a.1 < h) :
    ccmActualHeadTranslationDefect h f.1 = 2 * ‖f‖ ^ 2 := by
  have hpos := inner_logTranslationCLM_eq_zero_of_aperture a f hh
  have hneg : inner ℂ (logTranslationCLM (-h) f.1) f.1 = 0 := by
    rw [inner_logTranslationCLM (-h)]
    simp only [neg_neg]
    exact inner_eq_zero_symm.mpr hpos
  unfold ccmActualHeadTranslationDefect
  rw [logTranslation_defect_eq, hpos, hneg]
  simp only [add_zero, Complex.zero_re, sub_zero]
  rw [show ‖(f.1 : SoninL2)‖ = ‖f‖ by rfl]

/-- Exact exterior tail of the first Γ mode on an aperture head. -/
theorem integral_Ioi_gammaFirstBinetMode_mul_translationDefect_apertureTail
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    (∫ h in Ioi (2 * a.1),
        ccmGammaFirstBinetModeWeight h * ccmActualHeadTranslationDefect h f.1) =
      2 * Real.exp (-a.1) *
        ccmActualHeadTranslationDefect (2 * a.1) f.1 := by
  have hsub : Ioi (2 * a.1) ⊆ Ioi (0 : ℝ) := by
    intro h hh
    exact lt_trans (mul_pos (by norm_num) a.property) hh
  have hint :=
    (integrableOn_ccmGammaFirstBinetModeWeight_mul_translationDefect f.1).mono_set hsub
  have hcongr :
      (∫ h in Ioi (2 * a.1),
        ccmGammaFirstBinetModeWeight h * ccmActualHeadTranslationDefect h f.1) =
      ∫ h in Ioi (2 * a.1),
        Real.exp (-((1 / 2 : ℝ) * h)) * (2 * ‖f‖ ^ 2) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun h hh => ?_
    rw [ccmActualHeadTranslationDefect_eq_two_norm_sq_of_two_aperture_lt a f hh]
    unfold ccmGammaFirstBinetModeWeight
    congr 2
    ring
  rw [hcongr, integral_mul_const]
  rw [GaloisForLFunctions.RHTower.integral_Ioi_rexp_neg_mul_shift
    (by norm_num : (0 : ℝ) < 1 / 2)]
  rw [ccmActualHeadTranslationDefect_two_aperture]
  congr 1
  rw [show -((1 / 2 : ℝ) * (2 * a.1)) = -a.1 by ring]
  ring

/-- First Γ mode equals compact decaying polar energy plus the exact aperture tail. -/
theorem ccmActualHeadGammaFirstBinetModeEnergy_eq_compact_add_apertureTail
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    ccmActualHeadGammaFirstBinetModeEnergy f.1 =
      (∫ h in Icc (0 : ℝ) (2 * a.1),
        ccmGammaFirstBinetModeWeight h * ccmActualHeadTranslationDefect h f.1) +
      2 * Real.exp (-a.1) *
        ccmActualHeadTranslationDefect (2 * a.1) f.1 := by
  let G : ℝ → ℝ := fun h =>
    ccmGammaFirstBinetModeWeight h * ccmActualHeadTranslationDefect h f.1
  have hL : 0 ≤ 2 * a.1 := by linarith [a.property]
  have hint := integrableOn_ccmGammaFirstBinetModeWeight_mul_translationDefect f.1
  have hIoc : IntegrableOn G (Ioc (0 : ℝ) (2 * a.1)) :=
    hint.mono_set Ioc_subset_Ioi_self
  have hIoi : IntegrableOn G (Ioi (2 * a.1)) := by
    apply hint.mono_set
    intro h hh
    exact lt_trans (mul_pos (by norm_num) a.property) hh
  have hsplit : Ioc (0 : ℝ) (2 * a.1) ∪ Ioi (2 * a.1) = Ioi 0 :=
    Ioc_union_Ioi_eq_Ioi hL
  rw [ccmActualHeadGammaFirstBinetModeEnergy_eq_integral]
  change (∫ h in Ioi (0 : ℝ), G h) = _
  rw [← hsplit, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hIoc hIoi]
  rw [integral_Ioi_gammaFirstBinetMode_mul_translationDefect_apertureTail]
  congr 1
  exact (MeasureTheory.integral_Icc_eq_integral_Ioc).symm

/-- Growing half of the polar translation-defect continuum. -/
def ccmActualHeadOutgoingPolarEnergy
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) : ℝ :=
  ∫ h in Icc (0 : ℝ) (2 * a.1),
    Real.exp (h / 2) * ccmActualHeadTranslationDefect h f.1

/-- Polar debt splits exactly into growing and first-Γ-mode decaying halves. -/
theorem ccmContinuousPolarTranslationDefectEnergy_eq_outgoing_add_first
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    ccmContinuousPolarTranslationDefectEnergy a f =
      ccmActualHeadOutgoingPolarEnergy a f +
        ∫ h in Icc (0 : ℝ) (2 * a.1),
          ccmGammaFirstBinetModeWeight h * ccmActualHeadTranslationDefect h f.1 := by
  unfold ccmContinuousPolarTranslationDefectEnergy ccmActualHeadOutgoingPolarEnergy
  have hd : Continuous fun h : ℝ => ccmActualHeadTranslationDefect h f.1 := by
    unfold ccmActualHeadTranslationDefect
    exact (((continuous_logTranslationCLM f.1).sub continuous_const).norm).pow 2
  have hout : IntegrableOn (fun h : ℝ =>
      Real.exp (h / 2) * ccmActualHeadTranslationDefect h f.1)
      (Icc (0 : ℝ) (2 * a.1)) :=
    ((by fun_prop : Continuous fun h : ℝ => Real.exp (h / 2)).mul hd).integrableOn_Icc
  have hw : Continuous fun h : ℝ => ccmGammaFirstBinetModeWeight h := by
    unfold ccmGammaFirstBinetModeWeight
    fun_prop
  have hdecay : IntegrableOn (fun h : ℝ =>
      ccmGammaFirstBinetModeWeight h * ccmActualHeadTranslationDefect h f.1)
      (Icc (0 : ℝ) (2 * a.1)) := (hw.mul hd).integrableOn_Icc
  rw [← integral_add hout hdecay]
  apply integral_congr_ae
  filter_upwards with h
  unfold ccmGammaFirstBinetModeWeight
  rw [Real.cosh_eq]
  ring

/-- The Γ exterior tail converts completed error to the outgoing arithmetic error. -/
theorem criticalMellinCompletedError_add_gammaTail_eq_outgoingError
    (a : SuzukiPositiveAperture) :
    criticalMellinCompletedError (2 * a.1) + 2 * Real.exp (-a.1) =
      2 * Real.exp a.1 - criticalMellinPrimeMass (2 * a.1) := by
  rw [criticalMellinCompletedError_eq_polar_sub_primeMass, Real.sinh_eq]
  ring

/-- Reduced signed producer after exact first-Γ-mode/polar cancellation. -/
def ccmRestrictedWeilActualHeadGammaWallOutgoingProducer
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) : ℝ :=
  let f := ccmArchimedeanFormToAperture a u
  let g := ccmArchimedeanWeightedToL2 u.1
  2 * gammaHardyPhaseRate 0 * ‖f‖ ^ 2 +
    ccmActualHeadGammaHigherBinetModeEnergy (f : SoninL2) +
    (2 * Real.exp a.1 - criticalMellinPrimeMass (2 * a.1)) *
      ccmActualHeadTranslationDefect (2 * a.1) f.1 +
    ccmActualHeadPrimeWallChordEnergy a g -
    ccmActualHeadOutgoingPolarEnergy a f

/-- The reduced producer is exactly the prior wall-Gram producer, with no lost source term. -/
theorem ccmRestrictedWeilActualHeadGammaWallOutgoingProducer_eq_wallGramSignedProducer
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    ccmRestrictedWeilActualHeadGammaWallOutgoingProducer a u =
      ccmRestrictedWeilActualHeadWallGramSignedProducer a u := by
  let f := ccmArchimedeanFormToAperture a u
  have hgamma :=
    ccmActualHeadGammaAutocorrelationEnergy_eq_first_add_higher_formDomain a u
  have hfirst :=
    ccmActualHeadGammaFirstBinetModeEnergy_eq_compact_add_apertureTail a f
  have hpolar :=
    ccmContinuousPolarTranslationDefectEnergy_eq_outgoing_add_first a f
  have herror := criticalMellinCompletedError_add_gammaTail_eq_outgoingError a
  unfold ccmRestrictedWeilActualHeadGammaWallOutgoingProducer
    ccmRestrictedWeilActualHeadWallGramSignedProducer
  dsimp only
  rw [hgamma, hfirst, hpolar, ← herror]
  ring

/-- Unconditional source law for the reduced producer. -/
theorem ccmRestrictedWeilActualHeadGammaWallOutgoingProducer_eq_sourceQuadratic
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    ccmRestrictedWeilActualHeadGammaWallOutgoingProducer a u =
      ccmRestrictedWeilSourceQuadratic a u := by
  rw [ccmRestrictedWeilActualHeadGammaWallOutgoingProducer_eq_wallGramSignedProducer,
    ccmRestrictedWeilActualHeadWallGramSignedProducer_eq_sourceQuadratic]

/-- Canonical finite heads retain the exact ground-plus-vanishing-tail identity. -/
theorem ccmRestrictedWeilCanonicalGroundHead_gammaWallOutgoingProducer_eq_ground_add_tail
    (a : SuzukiPositiveAperture) (n : ℕ) :
    ccmRestrictedWeilActualHeadGammaWallOutgoingProducer a
        (ccmRestrictedWeilCanonicalGroundHead a n) =
      ccmRestrictedWeilGroundEnergy a *
          ‖ccmArchimedeanFormToAperture a
            (ccmRestrictedWeilCanonicalGroundHead a n)‖ ^ 2 +
        ccmRestrictedWeilCanonicalGroundHeadDefect a n := by
  rw [ccmRestrictedWeilActualHeadGammaWallOutgoingProducer_eq_wallGramSignedProducer,
    ccmRestrictedWeilCanonicalGroundHead_wallGramSignedProducer_eq_ground_add_tail]

/-- The RH-bearing reverse-prime bound is exactly the sign of the reduced producer. -/
theorem ccmRestrictedWeilCanonicalGroundHead_reversePrimeBound_iff_gammaWallOutgoingProducer_nonneg
    (a : SuzukiPositiveAperture) (n : ℕ) :
    CCMRestrictedWeilCanonicalGroundHeadReversePrimeBound a n ↔
      0 ≤ ccmRestrictedWeilActualHeadGammaWallOutgoingProducer a
        (ccmRestrictedWeilCanonicalGroundHead a n) := by
  rw [ccmRestrictedWeilCanonicalGroundHead_reversePrimeBound_iff_wallGramSignedProducer_nonneg,
    ccmRestrictedWeilActualHeadGammaWallOutgoingProducer_eq_wallGramSignedProducer]

end RHTower
