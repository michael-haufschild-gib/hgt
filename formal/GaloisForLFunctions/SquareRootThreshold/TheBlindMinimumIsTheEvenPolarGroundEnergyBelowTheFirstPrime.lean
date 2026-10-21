import GaloisForLFunctions.SquareRootThreshold.TheRoutesMeasureOneAperture
import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftedGroundStateOddProfileCoordinates
import GaloisForLFunctions.RHTower.XiGaussianHeatWindowEvenSource

/-!
# The blind minimum is the even polar ground energy below the first prime

Route EWU reads the aperture `a` through the blind minimum `evenBlindMinimum a`, the least Weil
energy of a normalized even pole-free source at aperture `a` whose autocorrelation vanishes at every
integer lag `log n`, `n ≥ 2`. The blind minimum dominates the restricted Weil ground energy `μ(a)`,
so window positivity at aperture `a` gives `0 ≤ evenBlindMinimum a`; this module fixes what the
converse reads.

* **Below the first prime the blind constraint is void.** A source supported in `[−a, a]` has no
  correlation at lags beyond `2a`, so for `2a < log 2` every even polar source is blind and the
  blind minimum is the even polar ground energy `μᵉ(a)` of the restricted Weil form
  (`evenBlindMinimum_eq_evenGroundEnergy_of_two_mul_lt_log_two`). There the EWU receiver is the
  polar even window and nothing more: it inherits the unconditional floor `1/20` of the pole-free
  ground energy (`one_twentieth_le_evenGroundEnergy_of_le_primeTwo`), and `ZetaWindowPositive a`
  pays it through the chain `μ ≤ μ_polar ≤ μᵉ` (`evenGroundEnergy_nonneg_of_zetaWindowPositive`).
* **The reading on smooth tests.** `0 ≤ evenBlindMinimum a` gives `0 ≤ Re W(f, f)` for every
  smooth even pole-free test `f` supported strictly inside `(−a, a)` whose autocorrelation vanishes
  at every integer lag (`re_W_nonneg_of_evenBlindMinimum_nonneg`), and `0 ≤ Ẑ(F)` for the real
  ones (`fullZeroForm_nonneg_of_evenBlindMinimum_nonneg`): EWU at aperture `a` is the blind even
  window at aperture `a`.
* **The even window is the polar even window plus one affine slice.** On an even test
  `Ẑ(F) = markovEnergy(F) + 2 (∫ F cosh(x/2))²` (`fullZeroForm_eq_markovEnergy_add_of_even`), so
  `ZetaEvenWindowPositive A` holds iff the Markov energy is nonnegative on the even window tests of
  vanishing cosh moment and at least `−2` on those of unit cosh moment
  (`zetaEvenWindowPositive_iff_polar_and_unitCoshMoment`). Below the first prime the first conjunct
  is the EWU receiver; the graded converse of EWU is the second conjunct, a one-dimensional
  inequality in the pole direction, and a failure of the even window at any aperture refutes RH
  (`not_riemannHypothesis_of_not_zetaEvenWindowPositive`).
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower _root_.RHTower.EvenSector _root_.RHTower.CCMEvenSector
  GaloisForLFunctions.ArithmeticCriticalityTheory

/-! ### 1. Below the first prime every even polar source is blind -/

/-- A source at aperture `a` with `2a < log 2` has vanishing correlation at every integer lag
`log n ≥ log 2`. -/
theorem energyProfile_mem_blindProfiles_of_two_mul_lt_log_two {a : SuzukiPositiveAperture}
    (ha : 2 * a.1 < Real.log 2) (u : CCMArchimedeanFormDomain a) :
    energyProfile a (ccmArchimedeanFormToAperture a u) ∈ blindProfiles := by
  intro n
  unfold energyProfile
  apply ccmApertureCorrelation_eq_zero_of_outside
  intro hmem
  rw [mem_Icc] at hmem
  have h2 : Real.log 2 ≤ Real.log (n : ℕ) :=
    Real.log_le_log two_pos (by exact_mod_cast n.2)
  linarith [hmem.1]

/-- **The blind minimum is the even polar ground energy below the first prime.** -/
theorem evenBlindMinimum_eq_evenGroundEnergy_of_two_mul_lt_log_two {a : SuzukiPositiveAperture}
    (ha : 2 * a.1 < Real.log 2) : evenBlindMinimum a = evenGroundEnergy a := by
  refine le_antisymm (le_csInf (evenRayleighSet_nonempty a) ?_)
    (evenGroundEnergy_le_evenBlindMinimum a)
  rintro r ⟨u, hp, he, hne, rfl⟩
  have hpos : 0 < ‖ccmArchimedeanFormToAperture a u‖ ^ (2 : ℕ) := by
    have := norm_pos_iff.mpr hne
    positivity
  rw [le_div_iff₀ hpos]
  exact evenBlindMinimum_mul_norm_sq_le u hp he
    (energyProfile_mem_blindProfiles_of_two_mul_lt_log_two ha u)

theorem evenBlindMinimum_nonneg_iff_evenGroundEnergy_nonneg_of_two_mul_lt_log_two
    {a : SuzukiPositiveAperture} (ha : 2 * a.1 < Real.log 2) :
    0 ≤ evenBlindMinimum a ↔ 0 ≤ evenGroundEnergy a := by
  rw [evenBlindMinimum_eq_evenGroundEnergy_of_two_mul_lt_log_two ha]

/-- The even polar ground energy inherits the unconditional floor `1/20` of the pole-free ground
energy through `½(log 2 + 1/50)`. -/
theorem one_twentieth_le_evenGroundEnergy_of_le_primeTwo (a : SuzukiPositiveAperture)
    (ha : a.1 ≤ (Real.log 2 + 1 / 50) / 2) : (1 / 20 : ℝ) ≤ evenGroundEnergy a :=
  (one_twentieth_le_ccmRestrictedWeilPolarGroundEnergy_of_le_primeTwo a ha).trans
    (polarGroundEnergy_le_evenGroundEnergy a)

/-- Window positivity at aperture `a` pays the even polar ground energy: `0 ≤ μ ≤ μ_polar ≤ μᵉ`. -/
theorem evenGroundEnergy_nonneg_of_zetaWindowPositive (a : SuzukiPositiveAperture)
    (h : ZetaWindowPositive a.1) : 0 ≤ evenGroundEnergy a :=
  ((ccmRestrictedWeilGroundEnergy_nonneg_of_zetaWindowPositive a h).trans
    (ccmRestrictedWeilGroundEnergy_le_polar a)).trans (polarGroundEnergy_le_evenGroundEnergy a)

/-! ### 2. The reading of the blind minimum on smooth interior tests -/

/-- **EWU is the blind even window.** `0 ≤ evenBlindMinimum a` gives `0 ≤ Re W(f, f)` for every
smooth even pole-free test `f` supported strictly inside `(−a, a)` whose autocorrelation vanishes
at every integer lag `log n`, `n ≥ 2`. -/
theorem re_W_nonneg_of_evenBlindMinimum_nonneg {a : SuzukiPositiveAperture}
    (hmin : 0 ≤ evenBlindMinimum a) (f : InteriorWindowedSmoothEvenPolarTestFn a)
    (hblind : ∀ n : LogIndex, EF.weilTest f.1.1.1.1 f.1.1.1.1 (Real.log (n : ℕ)) = 0) :
    0 ≤ (zetaZeroConfig.W f.1.1.1.1 f.1.1.1.1).re := by
  have hb : energyProfile a
      (ccmArchimedeanFormToAperture a (interiorCCMSource f).toCCMFormVector) ∈ blindProfiles := by
    intro n
    rw [energyProfile_interiorCCMSource]
    exact hblind n
  have hle := evenBlindMinimum_mul_norm_sq_le (interiorCCMSource f).toCCMFormVector
    (polar_interiorCCMSource f) (even_interiorCCMSource f) hb
  rw [sourceEnergy_interiorCCMSource] at hle
  unfold nativeProfileEnergy at hle
  rw [zeta_W_eq_weilFullFunctional f.1.1.1.2.1 f.1.1.1.2.2]
  exact (mul_nonneg hmin (sq_nonneg _)).trans hle

/-- The same on a real test: `0 ≤ Ẑ(F)` for every real smooth even pole-free window test whose
autocorrelation vanishes at every integer lag. -/
theorem fullZeroForm_nonneg_of_evenBlindMinimum_nonneg {a : SuzukiPositiveAperture}
    (hmin : 0 ≤ evenBlindMinimum a) (f : InteriorWindowedSmoothEvenPolarTestFn a)
    (hblind : ∀ n : LogIndex, EF.weilTest f.1.1.1.1 f.1.1.1.1 (Real.log (n : ℕ)) = 0)
    {F : ℝ → ℝ} (hF : f.1.1.1.1 = fun x => (F x : ℂ)) : 0 ≤ fullZeroForm F := by
  have h := re_W_nonneg_of_evenBlindMinimum_nonneg hmin f hblind
  have hc : ContDiff ℝ 2 f.1.1.1.1 := f.1.1.1.2.1
  have hcs : HasCompactSupport f.1.1.1.1 := f.1.1.1.2.2
  rw [hF] at hc hcs h
  rw [GaloisForLFunctions.ArithmeticPositivityTheory.zeta_W_re_eq_fullZeroForm_re_add_im hc hcs]
    at h
  simpa [fullZeroForm_zero] using h

/-! ### 3. The even window is the polar even window plus one affine slice -/

/-- On an even test the full zero form is the Markov energy plus `2 (∫ F cosh(x/2))²`. -/
theorem fullZeroForm_eq_markovEnergy_add_of_even {F : ℝ → ℝ} (heven : ∀ x, F (-x) = F x) :
    fullZeroForm F = markovEnergy (fun x => (F x : ℂ)) + 2 * evenPoleMoment F ^ 2 := by
  unfold fullZeroForm
  rw [oddPoleMoment_eq_zero_of_even heven]
  ring

theorem evenPoleMoment_const_mul (c : ℝ) (F : ℝ → ℝ) :
    evenPoleMoment (fun x => c * F x) = c * evenPoleMoment F := by
  unfold evenPoleMoment
  simp_rw [mul_assoc]
  exact integral_const_mul c _

/-- The Markov energy of a real test is quadratic under real scaling. -/
theorem markovEnergy_ofReal_const_mul (c : ℝ) (F : ℝ → ℝ) :
    markovEnergy (fun x => ((c * F x : ℝ) : ℂ)) = c ^ 2 * markovEnergy (fun x => (F x : ℂ)) := by
  have e : (fun x => ((c * F x : ℝ) : ℂ)) = (c : ℂ) • fun x => (F x : ℂ) := by
    funext x
    simp [Complex.ofReal_mul]
  rw [e, markovEnergy_real_smul]

/-- **The even window is the polar even window plus one affine slice.** `ZetaEvenWindowPositive A`
iff the Markov energy is nonnegative on the even window tests of vanishing cosh moment and at
least `−2` on those of unit cosh moment. -/
theorem zetaEvenWindowPositive_iff_polar_and_unitCoshMoment (A : ℝ) :
    ZetaEvenWindowPositive A ↔
      (∀ F : ℝ → ℝ, ContDiff ℝ 2 F → HasCompactSupport F → (∀ x, F (-x) = F x) →
        (∀ x, A < |x| → F x = 0) → evenPoleMoment F = 0 →
          0 ≤ markovEnergy (fun x => (F x : ℂ))) ∧
      (∀ F : ℝ → ℝ, ContDiff ℝ 2 F → HasCompactSupport F → (∀ x, F (-x) = F x) →
        (∀ x, A < |x| → F x = 0) → evenPoleMoment F = 1 →
          -2 ≤ markovEnergy (fun x => (F x : ℂ))) := by
  constructor
  · intro h
    refine ⟨fun F hF hFc heven hv hp => ?_, fun F hF hFc heven hv hp => ?_⟩
    · have hZ := h F hF hFc heven hv
      rw [fullZeroForm_eq_markovEnergy_add_of_even heven, hp] at hZ
      linarith
    · have hZ := h F hF hFc heven hv
      rw [fullZeroForm_eq_markovEnergy_add_of_even heven, hp] at hZ
      linarith
  · rintro ⟨h0, h1⟩ F hF hFc heven hv
    rw [fullZeroForm_eq_markovEnergy_add_of_even heven]
    by_cases hp : evenPoleMoment F = 0
    · rw [hp]
      have hM := h0 F hF hFc heven hv hp
      linarith
    · have hne : evenPoleMoment F ≠ 0 := hp
      have hG : ContDiff ℝ 2 fun x => (evenPoleMoment F)⁻¹ * F x := contDiff_const.mul hF
      have hGc : HasCompactSupport fun x => (evenPoleMoment F)⁻¹ * F x := hFc.mul_left
      have hGe : ∀ x, (fun x => (evenPoleMoment F)⁻¹ * F x) (-x) =
          (fun x => (evenPoleMoment F)⁻¹ * F x) x := fun x => by simp only [heven]
      have hGv : ∀ x, A < |x| → (fun x => (evenPoleMoment F)⁻¹ * F x) x = 0 := fun x hx => by
        simp only [hv x hx, mul_zero]
      have hGp : evenPoleMoment (fun x => (evenPoleMoment F)⁻¹ * F x) = 1 := by
        rw [evenPoleMoment_const_mul, inv_mul_cancel₀ hne]
      have hM : -2 ≤ markovEnergy (fun x => (((evenPoleMoment F)⁻¹ * F x : ℝ) : ℂ)) :=
        h1 _ hG hGc hGe hGv hGp
      rw [markovEnergy_ofReal_const_mul] at hM
      have ht : 0 < evenPoleMoment F ^ 2 := by positivity
      have key : -(2 * evenPoleMoment F ^ 2) ≤ markovEnergy (fun x => (F x : ℂ)) := by
        have h' := mul_le_mul_of_nonneg_left hM ht.le
        rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hne, one_pow, one_mul] at h'
        linarith
      linarith

/-! ### 4. No separation without refuting RH -/

/-- A failure of the even window at any aperture refutes RH. -/
theorem not_riemannHypothesis_of_not_zetaEvenWindowPositive {A : ℝ}
    (h : ¬ ZetaEvenWindowPositive A) : ¬ RiemannHypothesis :=
  fun hRH => h fun F hF hFc _ _ => fullZeroForm_nonneg_of_riemannHypothesis hRH hF hFc

/-! ### 5. The collected statement -/

/-- **The blind minimum is the even polar ground energy below the first prime.** For `2a < log 2`
the EWU receiver `evenBlindMinimum a` is the even polar ground energy `μᵉ(a)`, paid by window
positivity at aperture `a`; and the even window at any aperture is the polar even window together
with the one-dimensional inequality `−2 ≤ markovEnergy` on the even tests of unit cosh moment. -/
theorem theBlindMinimumIsTheEvenPolarGroundEnergyBelowTheFirstPrime (a : SuzukiPositiveAperture)
    (ha : 2 * a.1 < Real.log 2) :
    evenBlindMinimum a = evenGroundEnergy a ∧
    (0 ≤ evenBlindMinimum a ↔ 0 ≤ evenGroundEnergy a) ∧
    (ZetaWindowPositive a.1 → 0 ≤ evenGroundEnergy a) ∧
    (ZetaEvenWindowPositive a.1 ↔
      (∀ F : ℝ → ℝ, ContDiff ℝ 2 F → HasCompactSupport F → (∀ x, F (-x) = F x) →
        (∀ x, a.1 < |x| → F x = 0) → evenPoleMoment F = 0 →
          0 ≤ markovEnergy (fun x => (F x : ℂ))) ∧
      (∀ F : ℝ → ℝ, ContDiff ℝ 2 F → HasCompactSupport F → (∀ x, F (-x) = F x) →
        (∀ x, a.1 < |x| → F x = 0) → evenPoleMoment F = 1 →
          -2 ≤ markovEnergy (fun x => (F x : ℂ)))) :=
  ⟨evenBlindMinimum_eq_evenGroundEnergy_of_two_mul_lt_log_two ha,
    evenBlindMinimum_nonneg_iff_evenGroundEnergy_nonneg_of_two_mul_lt_log_two ha,
    evenGroundEnergy_nonneg_of_zetaWindowPositive a,
    zetaEvenWindowPositive_iff_polar_and_unitCoshMoment a.1⟩

end GaloisForLFunctions.SquareRootThreshold

end
