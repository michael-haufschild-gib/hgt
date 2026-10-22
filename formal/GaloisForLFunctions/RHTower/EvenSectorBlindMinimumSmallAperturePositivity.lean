import GaloisForLFunctions.RHTower.EvenSectorBlindVariationalAttainment
import GaloisForLFunctions.RHTower.EvenSectorExactMomentRealization
import GaloisForLFunctions.RHTower.EvenSectorPoleFreeBlindFarkas
import GaloisForLFunctions.RHTower.PolarGroundEnergyNonnegIffRiemannHypothesis
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilApertureMonotonicity

/-!
# Small-aperture positivity, aperture antitonicity, and RH equivalence for the EWU blind minimum

At each aperture `a`, the normalized even pole-free arithmetic-blind domain `BlindUnitSource a`
attains its minimum energy `evenBlindMinimum a` (`exists_blind_minimizer`).  This file establishes
four structural properties of `evenBlindMinimum`:

1. **Ground-energy dominance chain**:
   `ccmRestrictedWeilGroundEnergy a ≤ ccmRestrictedWeilPolarGroundEnergy a ≤ CCMEvenSector.evenGroundEnergy a ≤ evenBlindMinimum a`.
2. **Unconditional positivity past the prime `2`**:
   For every aperture `a ≤ ½(log 2 + 1/50)`, `1/20 ≤ evenBlindMinimum a` (and in particular
   `0 < evenBlindMinimum a`), because the pole-vanishing ground energy is unconditionally at least
   `1/20` on this window (`one_twentieth_le_ccmRestrictedWeilPolarGroundEnergy_of_le_primeTwo`).
3. **Aperture antitonicity**:
   `evenBlindMinimum` is antitone in the aperture `a` (`evenBlindMinimum_antitone`), since extending
   a smaller-aperture form vector by zero preserves parity, polar constraints, unit norm,
   entire autocorrelation profile (hence blindness at all `n ≥ 2`), and the Weil source quadratic.
4. **Exact equivalence with `PrimeBlindPositiveEvenPolar` and `RiemannHypothesis`**:
   Nonnegativity of `evenBlindMinimum a` for all apertures `a` is equivalent to
   `PrimeBlindPositiveEvenPolar` (`forall_evenBlindMinimum_nonneg_iff_primeBlindPositiveEvenPolar`)
   via exact single-source moment realization (`exists_single_smooth_exact_moments`), and hence by
   even pole-free Farkas duality (`exists_weilPositiveEvenPolar_iff`) and automatic polar
   completion (`weilPositiveFull_of_weilPositiveEvenPolar`) is equivalent to `RiemannHypothesis`
   (`riemannHypothesis_iff_forall_evenBlindMinimum_nonneg`,
   `riemannHypothesis_iff_evenBlindMinimum_nonneg_beyond_primeTwo`).
-/

open Complex MeasureTheory Set Filter Topology Finsupp Zeta23
open scoped InnerProduct NNReal ComplexConjugate

noncomputable section

namespace RHTower.EvenSector

open WeilOneSided WeilSpectral CCMRealRootedGround CCMGroundStructure

/-! ## The EWU blind minimum and ground-energy dominance chain -/

/-- A chosen normalized even polar arithmetic-blind minimizer at aperture `a`. -/
def evenBlindMinimizer (a : SuzukiPositiveAperture) : BlindUnitSource a :=
  (exists_blind_minimizer a).choose

/-- The minimum of the restricted Weil quadratic form on `BlindUnitSource a`. -/
def evenBlindMinimum (a : SuzukiPositiveAperture) : ℝ :=
  ccmRestrictedWeilSourceQuadratic a (evenBlindMinimizer a).1

theorem evenBlindMinimum_le (a : SuzukiPositiveAperture) (u : BlindUnitSource a) :
    evenBlindMinimum a ≤ ccmRestrictedWeilSourceQuadratic a u.1 :=
  (exists_blind_minimizer a).choose_spec u

theorem evenBlindMinimum_eq_gamma_integral (a : SuzukiPositiveAperture) :
    evenBlindMinimum a =
      ∫ ξ : ℝ, 2 * gammaHardyPhaseRate (2 * Real.pi * ξ) *
        ‖((evenBlindMinimizer a).1.1 : ℝ → ℂ) ξ‖ ^ 2 :=
  sourceQuadratic_blind_eq_gamma (evenBlindMinimizer a)

/-- The even polar ground energy bounds the EWU blind minimum from below. -/
theorem evenGroundEnergy_le_evenBlindMinimum (a : SuzukiPositiveAperture) :
    CCMEvenSector.evenGroundEnergy a ≤ evenBlindMinimum a := by
  unfold evenBlindMinimum
  let u := evenBlindMinimizer a
  have hf := CCMEvenSector.evenGroundEnergy_mul_le a u.1 u.2.1 u.2.2.1
  simpa only [u.2.2.2.1, one_pow, mul_one] using hf

/-- The pole-vanishing ground energy bounds the EWU blind minimum from below. -/
theorem ccmRestrictedWeilPolarGroundEnergy_le_evenBlindMinimum (a : SuzukiPositiveAperture) :
    ccmRestrictedWeilPolarGroundEnergy a ≤ evenBlindMinimum a := by
  unfold evenBlindMinimum
  let u := evenBlindMinimizer a
  have hf := ccmRestrictedWeilPolarGroundEnergy_mul_le a u.1 u.2.1
  simpa only [u.2.2.2.1, one_pow, mul_one] using hf

/-- The unconstrained restricted-Weil ground energy bounds the EWU blind minimum from below. -/
theorem ccmRestrictedWeilGroundEnergy_le_evenBlindMinimum (a : SuzukiPositiveAperture) :
    ccmRestrictedWeilGroundEnergy a ≤ evenBlindMinimum a :=
  (ccmRestrictedWeilGroundEnergy_le_polar a).trans
    (ccmRestrictedWeilPolarGroundEnergy_le_evenBlindMinimum a)

/-- **Rayleigh inequality on blind even polar form vectors.** -/
theorem evenBlindMinimum_mul_norm_sq_le {a : SuzukiPositiveAperture}
    (u : CCMArchimedeanFormDomain a) (hp : IsPolarConstrained a u)
    (he : CCMEvenSector.IsEven a u)
    (hb : energyProfile a (ccmArchimedeanFormToAperture a u) ∈ blindProfiles) :
    evenBlindMinimum a * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 ≤
      ccmRestrictedWeilSourceQuadratic a u := by
  by_cases hJ : ccmArchimedeanFormToAperture a u = 0
  · have hu0 : u = 0 := ccmArchimedeanFormToAperture_injective a (by rw [hJ, map_zero])
    rw [hJ, norm_zero, hu0, source_zero]
    simp
  · let r := ‖ccmArchimedeanFormToAperture a u‖
    have hr0 : 0 < r := norm_pos_iff.mpr hJ
    let c : ℂ := (r : ℂ)⁻¹
    let w : BlindUnitSource a := ⟨c • u, hp.smul c, he.smul a c, by
      rw [map_smul, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
      exact inv_mul_cancel₀ hr0.ne', fun n => by
      rw [map_smul, energyProfile_smul, hb n, mul_zero]⟩
    have hle := evenBlindMinimum_le a w
    change evenBlindMinimum a ≤ ccmRestrictedWeilSourceQuadratic a (c • u) at hle
    rw [ccmRestrictedWeilSourceQuadratic_smul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr0, inv_pow] at hle
    have hr2 : 0 < r ^ 2 := pow_pos hr0 2
    have hmul := mul_le_mul_of_nonneg_right hle hr2.le
    have hcancel : (r ^ 2)⁻¹ * ccmRestrictedWeilSourceQuadratic a u * r ^ 2 =
        ccmRestrictedWeilSourceQuadratic a u := by field_simp
    rwa [hcancel] at hmul

/-! ## Unconditional positivity up to and past the prime `2` -/

/-- **Unconditional positivity past the prime `2`.**  For every aperture
`a ≤ ½(log 2 + 1/50)`, the EWU blind minimum is at least `1/20`. -/
theorem one_twentieth_le_evenBlindMinimum_of_le_primeTwo (a : SuzukiPositiveAperture)
    (ha : a.1 ≤ (Real.log 2 + 1 / 50) / 2) :
    (1 / 20 : ℝ) ≤ evenBlindMinimum a :=
  (one_twentieth_le_ccmRestrictedWeilPolarGroundEnergy_of_le_primeTwo a ha).trans
    (ccmRestrictedWeilPolarGroundEnergy_le_evenBlindMinimum a)

theorem evenBlindMinimum_pos_of_le_primeTwo (a : SuzukiPositiveAperture)
    (ha : a.1 ≤ (Real.log 2 + 1 / 50) / 2) :
    0 < evenBlindMinimum a :=
  lt_of_lt_of_le (by norm_num) (one_twentieth_le_evenBlindMinimum_of_le_primeTwo a ha)

/-! ## Aperture inclusion and antitonicity -/

theorem energyProfile_eq_of_val_eq {a b : SuzukiPositiveAperture}
    {u : CCMArchimedeanFormDomain a} {v : CCMArchimedeanFormDomain b}
    (hvu : v.1 = u.1) :
    energyProfile b (ccmArchimedeanFormToAperture b v) =
      energyProfile a (ccmArchimedeanFormToAperture a u) := by
  funext h
  simp only [energyProfile, ccmApertureCorrelation]
  rw [ccmArchimedeanFormToAperture_coe_eq_of_val_eq hvu]

/-- Every normalized blind even polar source at aperture `a` extends to aperture `b ≥ a` with
identical autocorrelation profile and restricted-Weil energy. -/
theorem exists_blindUnitSource_extension {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1)
    (u : BlindUnitSource a) :
    ∃ v : BlindUnitSource b, v.1.1 = u.1.1 ∧
      ccmRestrictedWeilSourceQuadratic b v.1 = ccmRestrictedWeilSourceQuadratic a u.1 := by
  obtain ⟨v, hvu⟩ := exists_ccmArchimedeanFormDomain_extension hab u.1
  have hp : IsPolarConstrained b v := by
    refine ⟨?_, ?_⟩
    · rw [inner_ccmPolarApertureVector_eq_of_val_eq hab (1 / 2) hvu]
      exact u.2.1.1
    · rw [inner_ccmPolarApertureVector_eq_of_val_eq hab (-1 / 2) hvu]
      exact u.2.1.2
  have he : CCMEvenSector.IsEven b v := by
    apply ccmArchimedeanFormToAperture_injective b
    apply Subtype.ext
    rw [ccmArchimedeanFormToAperture_reflection,
      ccmArchimedeanFormToAperture_coe_eq_of_val_eq hvu]
    have hu := congrArg Subtype.val (congrArg (ccmArchimedeanFormToAperture a) u.2.2.1)
    rwa [ccmArchimedeanFormToAperture_reflection] at hu
  have hn : ‖ccmArchimedeanFormToAperture b v‖ = 1 := by
    rw [norm_ccmArchimedeanFormToAperture_eq_of_val_eq hvu]
    exact u.2.2.2.1
  have hb : energyProfile b (ccmArchimedeanFormToAperture b v) ∈ blindProfiles := by
    rw [energyProfile_eq_of_val_eq hvu]
    exact u.2.2.2.2
  exact ⟨⟨v, hp, he, hn, hb⟩, hvu, ccmRestrictedWeilSourceQuadratic_eq_of_val_eq hab hvu⟩

/-- **Aperture antitonicity of the EWU blind minimum.** -/
theorem evenBlindMinimum_antitone {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1) :
    evenBlindMinimum b ≤ evenBlindMinimum a := by
  obtain ⟨v, -, hQ⟩ := exists_blindUnitSource_extension hab (evenBlindMinimizer a)
  exact (evenBlindMinimum_le b v).trans hQ.le

/-! ## Equivalence with `PrimeBlindPositiveEvenPolar` and `RiemannHypothesis` -/

/-- Every smooth compact even pole-free test with vanishing integer trace is bounded below in
archimedean energy by `evenBlindMinimum a` at a supporting aperture `a`. -/
theorem exists_aperture_evenBlindMinimum_mul_le_smooth_blind (f : SmoothEvenPolarTestFn)
    (hf0 : logVector f.1.1 = 0) :
    ∃ a : SuzukiPositiveAperture, ∃ u : CCMArchimedeanFormDomain a,
      evenBlindMinimum a * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 ≤
        weilArchRe (EF.weilTest f.1.1.1 f.1.1.1) := by
  obtain ⟨R, hR⟩ := f.1.1.2.2.isCompact.isBounded.subset_closedBall 0
  let a : SuzukiPositiveAperture := ⟨|R| + 1, by positivity⟩
  have hs : tsupport f.1.1.1 ⊆ Ioo (-a.1) a.1 := by
    intro x hx
    have hh := hR hx
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hh
    exact abs_lt.mp (lt_of_le_of_lt hh (lt_of_le_of_lt (le_abs_self R) (by dsimp [a]; linarith)))
  let f_int : InteriorWindowedSmoothEvenPolarTestFn a := ⟨f, hs⟩
  let u := (interiorCCMSource f_int).toCCMFormVector
  have hblind : energyProfile a (ccmArchimedeanFormToAperture a u) ∈ blindProfiles := by
    intro n
    rw [(energyProfile_eq_zero_iff_trace_zero (even_interiorCCMSource f_int)
      (Real.log (n : ℕ))), energyProfile_interiorCCMSource]
    have hn0 : logVector f.1.1 n = 0 := by rw [hf0]; rfl
    rw [logVector_apply] at hn0
    unfold logValue at hn0
    have hsqrt : (Real.sqrt (n : ℕ) : ℝ) ≠ 0 :=
      (Real.sqrt_pos.mpr (by exact_mod_cast (lt_of_lt_of_le two_pos n.2))).ne'
    exact (div_eq_zero_iff.mp hn0).resolve_right hsqrt
  have hQ : ccmRestrictedWeilSourceQuadratic a u = weilArchRe (EF.weilTest f.1.1.1 f.1.1.1) := by
    rw [sourceEnergy_interiorCCMSource]
    unfold nativeProfileEnergy
    rw [re_weilFullFunctional_eq _ f.1.1, hf0, map_zero, sub_zero]
  refine ⟨a, u, ?_⟩
  rw [← hQ]
  exact evenBlindMinimum_mul_norm_sq_le u (polar_interiorCCMSource f_int)
    (even_interiorCCMSource f_int) hblind

/-- **Equivalence between all-aperture EWU blind positivity and `PrimeBlindPositiveEvenPolar`.** -/
theorem forall_evenBlindMinimum_nonneg_iff_primeBlindPositiveEvenPolar :
    (∀ a : SuzukiPositiveAperture, 0 ≤ evenBlindMinimum a) ↔ PrimeBlindPositiveEvenPolar := by
  constructor
  · intro hmin c hc hnull
    let d : WeilTestFn →₀ ℝ := c.mapDomain Subtype.val
    have hd : ∀ g, 0 ≤ d g := Finsupp.mapDomain_nonneg hc
    obtain ⟨f, hft, hfe⟩ := exists_single_smooth_exact_moments d hd
    have hd_trace : linearCombination ℝ logVector d = 0 := by
      rw [Finsupp.linearCombination_mapDomain]
      ext n
      rw [linearCombination_apply, Finsupp.sum_apply, Finsupp.coe_zero, Pi.zero_apply,
        ← hnull n n.2]
      refine Finsupp.sum_congr fun g _ => ?_
      simp only [Finsupp.smul_apply, Function.comp_apply, logVector_apply, smul_eq_mul]
    have hd_energy : fullMixtureEnergy d =
        c.sum fun g t => t * weilArchRe (EF.weilTest g.1.1 g.1.1) := by
      unfold fullMixtureEnergy
      rw [Finsupp.linearCombination_mapDomain, linearCombination_apply]
      simp only [Function.comp_apply, smul_eq_mul]
      rfl
    obtain ⟨a, u, hle⟩ := exists_aperture_evenBlindMinimum_mul_le_smooth_blind f
      (hft.trans hd_trace)
    rw [← hd_energy, ← hfe]
    exact (mul_nonneg (hmin a) (sq_nonneg _)).trans hle
  · intro hPB
    obtain ⟨lam, hlam⟩ := exists_weilPositiveEvenPolar_iff.mpr hPB
    have hfull : WeilPositiveFull lam := weilPositiveFull_of_weilPositiveEvenPolar hlam
    have heq : ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n :=
      source_unique_of_weilPositiveEvenPolar hlam
    have hRH : RiemannHypothesis :=
      (weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt.mp hfull).1
    intro a
    exact (WeilDeletion.ccmRestrictedWeilGroundEnergy_nonneg_of_riemannHypothesis hRH a).trans
      (ccmRestrictedWeilGroundEnergy_le_evenBlindMinimum a)

/-- **`PrimeBlindPositiveEvenPolar` is equivalent to `RiemannHypothesis`.** -/
theorem primeBlindPositiveEvenPolar_iff_riemannHypothesis :
    PrimeBlindPositiveEvenPolar ↔ RiemannHypothesis := by
  constructor
  · intro hPB
    obtain ⟨lam, hlam⟩ := exists_weilPositiveEvenPolar_iff.mpr hPB
    exact (weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt.mp
      (weilPositiveFull_of_weilPositiveEvenPolar hlam)).1
  · intro hRH
    refine forall_evenBlindMinimum_nonneg_iff_primeBlindPositiveEvenPolar.mp fun a => ?_
    exact (WeilDeletion.ccmRestrictedWeilGroundEnergy_nonneg_of_riemannHypothesis hRH a).trans
      (ccmRestrictedWeilGroundEnergy_le_evenBlindMinimum a)

/-- **The EWU blind minimum is nonnegative at every aperture iff `RiemannHypothesis` holds.** -/
theorem riemannHypothesis_iff_forall_evenBlindMinimum_nonneg :
    RiemannHypothesis ↔ ∀ a : SuzukiPositiveAperture, 0 ≤ evenBlindMinimum a :=
  primeBlindPositiveEvenPolar_iff_riemannHypothesis.symm.trans
    forall_evenBlindMinimum_nonneg_iff_primeBlindPositiveEvenPolar.symm

/-- **Reduction beyond the prime `2`.**  Because `1/20 ≤ evenBlindMinimum a` unconditionally for
all `a ≤ ½(log 2 + 1/50)`, the Riemann Hypothesis is equivalent to nonnegativity of
`evenBlindMinimum a` on apertures `a > ½(log 2 + 1/50)`. -/
theorem riemannHypothesis_iff_evenBlindMinimum_nonneg_beyond_primeTwo :
    RiemannHypothesis ↔ ∀ a : SuzukiPositiveAperture, (Real.log 2 + 1 / 50) / 2 < a.1 →
      0 ≤ evenBlindMinimum a := by
  rw [riemannHypothesis_iff_forall_evenBlindMinimum_nonneg]
  constructor
  · exact fun h a _ => h a
  · intro h a
    by_cases ha : a.1 ≤ (Real.log 2 + 1 / 50) / 2
    · exact le_trans (by norm_num) (one_twentieth_le_evenBlindMinimum_of_le_primeTwo a ha)
    · exact h a (lt_of_not_ge ha)

end RHTower.EvenSector

end
