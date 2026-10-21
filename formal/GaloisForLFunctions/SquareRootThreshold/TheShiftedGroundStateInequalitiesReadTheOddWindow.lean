import GaloisForLFunctions.SquareRootThreshold.TheRoutesMeasureOneAperture
import GaloisForLFunctions.ArithmeticCriticalityTheory.ZeroFormGaugeInvariance
import GaloisForLFunctions.ArithmeticCriticalityTheory.PoleFreeShiftAveragedVariationAndCrossEnergyLaw

/-!
# The shifted ground-state inequalities read the odd window

Route ACT states its frontier at one shift `a > 0` through the odd tests `m_a u = Φ(ω_a u)` of even
profiles `u`: the single-shift Markov inequality `markovEnergy(Φ(ω_a u)) ≥ 0` and the pole-free
variation inequality `D_a(u) ≤ 2 S_a(u) + V_a(u)`. This module reads both at a fixed aperture `A`
against the odd window `ZetaOddWindowPositive A` of the full zero form `Ẑ`.

* **The variation inequality is the odd window, exactly.** On an odd test the full zero form is
  `Ẑ(F) = markovEnergy(F) − 2 (∫ F sinh(x/2))²`, and on the ACT test this is the pole-free variation
  form: `Ẑ(m_a u) = 2 S_a(u) − D_a(u) + V_a(u)` (`fullZeroForm_phiDoob_shiftedGroundState`). Hence
  the odd window at `A` gives the variation inequality for every profile at `A` and every shift
  (`shiftVariationWindow_of_zetaOddWindowPositive`), and the variation inequality at `A` and one
  shift gives the odd window at `A` on the tests vanishing near the origin, through the quotient
  `u = F/m_a` (`zetaOddWindowPositiveOffOrigin_of_shiftVariationWindow`). On those tests the two
  are one predicate at every shift: the shift is a gauge at every aperture
  (`shiftVariationWindowOffOrigin_iff_zetaOddWindowPositiveOffOrigin`).
* **The Markov inequality is the odd window plus the pole energy.**
  `markovEnergy(m_a u) = Ẑ(m_a u) + 8 (∫_{x>0} u m_a sinh(x/2))²`
  (`markovEnergy_phiDoob_shiftedGroundState_eq_fullZeroForm_add`). So the odd window at `A` gives
  the Markov window at `A`; the Markov window at `A` is the pole-free odd window, `markovEnergy ≥ 0`
  on the odd tests at `A` vanishing near the origin, at every shift; and that gives `Ẑ ≥ 0` on the
  odd tests of vanishing pole moment, the polar odd window.
* **What the pole term separates.** The two ACT inequalities differ on a profile by exactly
  `8 (∫ u dμ_a)²`, which vanishes iff the test `m_a u` has zero pole moment: the pole term separates
  the Markov form from the variation form on every non-polar profile, and nothing else. The Markov
  window at `A` is the inequality `−8 (∫ u dμ_a)² ≤ Ẑ(m_a u)` on every window profile, so its
  converse to the odd window is the odd window on the tests of nonzero pole moment, OWU's capacity
  inequality; a failure of the odd window at any aperture refutes RH
  (`not_riemannHypothesis_of_not_zetaOddWindowPositive`).
* **Endpoint.** RH iff the variation inequality holds at every aperture at any one shift, iff the
  Markov inequality does, iff the odd window is positive at every aperture.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower GaloisForLFunctions.ArithmeticCriticalityTheory
  GaloisForLFunctions.ArithmeticPositivityTheory

/-! ### 1. The two ACT inequalities as window predicates -/

/-- The ACT pole-free variation inequality `D_a(u) ≤ 2 S_a(u) + V_a(u)` for every even `C²_c`
profile `u` vanishing outside `[−A, A]`. -/
def ShiftVariationWindow (a A : ℝ) : Prop :=
  ∀ u : ℝ → ℝ, ContDiff ℝ 2 u → HasCompactSupport u → (∀ x, u (-x) = u x) →
    (∀ x, A < |x| → u x = 0) →
      reflectedDifferenceEnergy (shiftedGroundState a) u ≤
        2 * sameSideEnergy (shiftedGroundState a) u + profileVariance a u

/-- The ACT single-shift Markov inequality `markovEnergy(Φ(ω_a u)) ≥ 0` for every even `C²_c`
profile `u` vanishing outside `[−A, A]`. -/
def ShiftMarkovWindow (a A : ℝ) : Prop :=
  ∀ u : ℝ → ℝ, ContDiff ℝ 2 u → HasCompactSupport u → (∀ x, u (-x) = u x) →
    (∀ x, A < |x| → u x = 0) →
      0 ≤ markovEnergy (fun x => (phiDoobTest (fun y => shiftedGroundState a y * u y) x : ℂ))

/-- The variation inequality at aperture `A` on the profiles vanishing on a neighbourhood of `0`. -/
def ShiftVariationWindowOffOrigin (a A : ℝ) : Prop :=
  ∀ u : ℝ → ℝ, ContDiff ℝ 2 u → HasCompactSupport u → (∀ x, u (-x) = u x) →
    (∀ x, A < |x| → u x = 0) → (∃ ε : ℝ, 0 < ε ∧ ∀ x, |x| < ε → u x = 0) →
      reflectedDifferenceEnergy (shiftedGroundState a) u ≤
        2 * sameSideEnergy (shiftedGroundState a) u + profileVariance a u

/-- The Markov inequality at aperture `A` on the profiles vanishing on a neighbourhood of `0`. -/
def ShiftMarkovWindowOffOrigin (a A : ℝ) : Prop :=
  ∀ u : ℝ → ℝ, ContDiff ℝ 2 u → HasCompactSupport u → (∀ x, u (-x) = u x) →
    (∀ x, A < |x| → u x = 0) → (∃ ε : ℝ, 0 < ε ∧ ∀ x, |x| < ε → u x = 0) →
      0 ≤ markovEnergy (fun x => (phiDoobTest (fun y => shiftedGroundState a y * u y) x : ℂ))

/-- The odd window on the tests vanishing on a neighbourhood of the origin. -/
def ZetaOddWindowPositiveOffOrigin (A : ℝ) : Prop :=
  ∀ F : ℝ → ℝ, ContDiff ℝ 2 F → HasCompactSupport F → (∀ x, F (-x) = -F x) →
    (∀ x, A < |x| → F x = 0) → (∃ ε : ℝ, 0 < ε ∧ ∀ x, |x| < ε → F x = 0) → 0 ≤ fullZeroForm F

/-- The pole-free odd window: the Markov energy is nonnegative on every odd window test. -/
def ZetaPoleFreeOddWindowPositive (A : ℝ) : Prop :=
  ∀ F : ℝ → ℝ, ContDiff ℝ 2 F → HasCompactSupport F → (∀ x, F (-x) = -F x) →
    (∀ x, A < |x| → F x = 0) → 0 ≤ markovEnergy (fun x => (F x : ℂ))

/-- The pole-free odd window on the tests vanishing on a neighbourhood of the origin. -/
def ZetaPoleFreeOddWindowPositiveOffOrigin (A : ℝ) : Prop :=
  ∀ F : ℝ → ℝ, ContDiff ℝ 2 F → HasCompactSupport F → (∀ x, F (-x) = -F x) →
    (∀ x, A < |x| → F x = 0) → (∃ ε : ℝ, 0 < ε ∧ ∀ x, |x| < ε → F x = 0) →
      0 ≤ markovEnergy (fun x => (F x : ℂ))

/-- The polar odd window: `Ẑ ≥ 0` on the odd window tests of vanishing pole moment. -/
def ZetaPolarOddWindowPositive (A : ℝ) : Prop :=
  ∀ F : ℝ → ℝ, ContDiff ℝ 2 F → HasCompactSupport F → (∀ x, F (-x) = -F x) →
    (∀ x, A < |x| → F x = 0) → oddPoleMoment F = 0 → 0 ≤ fullZeroForm F

/-! ### 2. The two forms on odd tests -/

/-- On an odd test the full zero form is the zero form `markovEnergy − 2 (∫ F sinh(x/2))²`. -/
theorem fullZeroForm_eq_zeroForm_of_odd {F : ℝ → ℝ} (hodd : ∀ x, F (-x) = -F x) :
    fullZeroForm F = zeroForm F := by
  unfold fullZeroForm zeroForm
  rw [evenPoleMoment_eq_zero_of_odd hodd]
  ring

/-- On an odd test the Markov energy exceeds the full zero form by the pole energy
`2 (∫ F sinh(x/2))²`. -/
theorem markovEnergy_eq_fullZeroForm_add_of_odd {F : ℝ → ℝ} (hodd : ∀ x, F (-x) = -F x) :
    markovEnergy (fun x => (F x : ℂ)) = fullZeroForm F + 2 * oddPoleMoment F ^ 2 := by
  rw [fullZeroForm_eq_zeroForm_of_odd hodd]
  unfold zeroForm
  ring

theorem fullZeroForm_le_markovEnergy_of_odd {F : ℝ → ℝ} (hodd : ∀ x, F (-x) = -F x) :
    fullZeroForm F ≤ markovEnergy (fun x => (F x : ℂ)) := by
  rw [markovEnergy_eq_fullZeroForm_add_of_odd hodd]
  nlinarith [sq_nonneg (oddPoleMoment F)]

/-! ### 3. The ACT test of a window profile -/

/-- The ACT test `Φ(ω_a u) = m_a u` of an even profile is odd. -/
theorem phiDoob_shiftedGroundState_odd (a : ℝ) {u : ℝ → ℝ} (heven : ∀ x, u (-x) = u x) (x : ℝ) :
    phiDoobTest (fun y => shiftedGroundState a y * u y) (-x) =
      -phiDoobTest (fun y => shiftedGroundState a y * u y) x := by
  simp only [phiDoobTest, riemannKernelReal_neg', shiftedGroundState_neg, heven]
  ring

/-- The ACT test of a window profile is a window test of the same aperture. -/
theorem phiDoob_shiftedGroundState_window {A a : ℝ} {u : ℝ → ℝ} (hv : ∀ x, A < |x| → u x = 0)
    (x : ℝ) (hx : A < |x|) : phiDoobTest (fun y => shiftedGroundState a y * u y) x = 0 := by
  simp [phiDoobTest, hv x hx]

/-- The ACT test of a profile vanishing near the origin vanishes near the origin. -/
theorem phiDoob_shiftedGroundState_eq_zero_of_abs_lt {ε a : ℝ} {u : ℝ → ℝ}
    (hvan : ∀ x, |x| < ε → u x = 0) (x : ℝ) (hx : |x| < ε) :
    phiDoobTest (fun y => shiftedGroundState a y * u y) x = 0 := by
  simp [phiDoobTest, hvan x hx]

/-- **The pole-free variation form is the full zero form of the ACT test:**
`Ẑ(m_a u) = 2 S_a(u) − D_a(u) + V_a(u)`. -/
theorem fullZeroForm_phiDoob_shiftedGroundState {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ}
    (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) (heven : ∀ x, u (-x) = u x) :
    fullZeroForm (phiDoobTest (fun y => shiftedGroundState a y * u y)) =
      2 * sameSideEnergy (shiftedGroundState a) u -
        reflectedDifferenceEnergy (shiftedGroundState a) u + profileVariance a u := by
  rw [poleFreeForm_eq_zeroForm ha hu huc heven,
    fullZeroForm_eq_zeroForm_of_odd (phiDoob_shiftedGroundState_odd a heven)]

/-- The variation inequality at a profile is `0 ≤ Ẑ(m_a u)`. -/
theorem variationInequality_iff_fullZeroForm_nonneg {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ}
    (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) (heven : ∀ x, u (-x) = u x) :
    reflectedDifferenceEnergy (shiftedGroundState a) u ≤
        2 * sameSideEnergy (shiftedGroundState a) u + profileVariance a u ↔
      0 ≤ fullZeroForm (phiDoobTest (fun y => shiftedGroundState a y * u y)) := by
  rw [fullZeroForm_phiDoob_shiftedGroundState ha hu huc heven]
  constructor <;> intro h <;> linarith

/-- **The Markov energy of the ACT test is `Ẑ(m_a u)` plus the pole energy `8 (∫ u dμ_a)²`.** -/
theorem markovEnergy_phiDoob_shiftedGroundState_eq_fullZeroForm_add {a : ℝ} (ha : 0 < a)
    {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) (heven : ∀ x, u (-x) = u x) :
    markovEnergy (fun x => (phiDoobTest (fun y => shiftedGroundState a y * u y) x : ℂ)) =
      fullZeroForm (phiDoobTest (fun y => shiftedGroundState a y * u y)) +
        8 * profileMoment a u ^ 2 := by
  rw [markovEnergy_phiDoob_shiftedGroundState_eq_poleFree_add_eight_profileMoment_sq ha hu huc
    heven, fullZeroForm_phiDoob_shiftedGroundState ha hu huc heven]

/-- The two ACT inequalities agree at a profile iff its `μ_a`-mean vanishes, iff the ACT test has
zero pole moment. -/
theorem markovEnergy_phiDoob_eq_fullZeroForm_iff {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ}
    (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) (heven : ∀ x, u (-x) = u x) :
    markovEnergy (fun x => (phiDoobTest (fun y => shiftedGroundState a y * u y) x : ℂ)) =
        fullZeroForm (phiDoobTest (fun y => shiftedGroundState a y * u y)) ↔
      oddPoleMoment (phiDoobTest (fun y => shiftedGroundState a y * u y)) = 0 := by
  rw [markovEnergy_phiDoob_shiftedGroundState_eq_fullZeroForm_add ha hu huc heven,
    oddPoleMoment_phiDoob_shiftedGroundState hu.continuous huc heven]
  constructor
  · intro h
    have hsq : profileMoment a u ^ 2 = 0 := by linarith
    have hM : profileMoment a u = 0 := (pow_eq_zero_iff two_ne_zero).mp hsq
    rw [hM]
    ring
  · intro h
    have hM : profileMoment a u = 0 := by linarith
    rw [hM]
    ring

/-! ### 4. The odd window is the variation inequality at every shift -/

/-- The odd window at `A` pays the variation inequality for every profile at `A` and every shift. -/
theorem shiftVariationWindow_of_zetaOddWindowPositive {A : ℝ} (h : ZetaOddWindowPositive A)
    {a : ℝ} (ha : 0 < a) : ShiftVariationWindow a A := by
  intro u hu huc heven hv
  rw [variationInequality_iff_fullZeroForm_nonneg ha hu huc heven]
  exact h _ (contDiff_phiDoobTest ((contDiff_shiftedGroundState a).mul hu))
    (hasCompactSupport_phiDoobTest huc.mul_left) (phiDoob_shiftedGroundState_odd a heven)
    (phiDoob_shiftedGroundState_window hv)

/-- **The graded converse.** The variation inequality at aperture `A` and one shift gives the odd
window at `A` on the tests vanishing near the origin: such a test is `m_a (F/m_a)` with an even
`C²` window profile `F/m_a`. -/
theorem zetaOddWindowPositiveOffOrigin_of_shiftVariationWindow {a A : ℝ} (ha : 0 < a)
    (h : ShiftVariationWindow a A) : ZetaOddWindowPositiveOffOrigin A := by
  intro F hF hFc hodd hv ⟨ε, hε, hvan⟩
  have h0 : F 0 = 0 := hvan 0 (by rwa [abs_zero])
  have hq := h (shiftQuotient a F) (contDiff_shiftQuotient ha hε hF hvan)
    (hasCompactSupport_shiftQuotient a hFc) (shiftQuotient_neg a hodd)
    (fun x hx => by unfold shiftQuotient; rw [hv x hx, zero_div])
  rw [variationInequality_iff_fullZeroForm_nonneg ha (contDiff_shiftQuotient ha hε hF hvan)
    (hasCompactSupport_shiftQuotient a hFc) (shiftQuotient_neg a hodd),
    funext (phiDoobTest_shiftedGroundState_mul_shiftQuotient ha h0)] at hq
  exact hq

/-- On the tests vanishing near the origin the variation inequality at any shift is the odd
window. -/
theorem shiftVariationWindowOffOrigin_iff_zetaOddWindowPositiveOffOrigin {a A : ℝ} (ha : 0 < a) :
    ShiftVariationWindowOffOrigin a A ↔ ZetaOddWindowPositiveOffOrigin A := by
  constructor
  · intro h F hF hFc hodd hv ⟨ε, hε, hvan⟩
    have h0 : F 0 = 0 := hvan 0 (by rwa [abs_zero])
    have hq := h (shiftQuotient a F) (contDiff_shiftQuotient ha hε hF hvan)
      (hasCompactSupport_shiftQuotient a hFc) (shiftQuotient_neg a hodd)
      (fun x hx => by unfold shiftQuotient; rw [hv x hx, zero_div])
      ⟨ε, hε, fun x hx => shiftQuotient_eq_zero_of_abs_lt hvan hx⟩
    rw [variationInequality_iff_fullZeroForm_nonneg ha (contDiff_shiftQuotient ha hε hF hvan)
      (hasCompactSupport_shiftQuotient a hFc) (shiftQuotient_neg a hodd),
      funext (phiDoobTest_shiftedGroundState_mul_shiftQuotient ha h0)] at hq
    exact hq
  · intro h u hu huc heven hv ⟨ε, hε, hvan⟩
    rw [variationInequality_iff_fullZeroForm_nonneg ha hu huc heven]
    exact h _ (contDiff_phiDoobTest ((contDiff_shiftedGroundState a).mul hu))
      (hasCompactSupport_phiDoobTest huc.mul_left) (phiDoob_shiftedGroundState_odd a heven)
      (phiDoob_shiftedGroundState_window hv)
      ⟨ε, hε, phiDoob_shiftedGroundState_eq_zero_of_abs_lt hvan⟩

/-- **The shift is a gauge at every aperture.** -/
theorem shiftVariationWindowOffOrigin_iff_of_pos {a b A : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ShiftVariationWindowOffOrigin a A ↔ ShiftVariationWindowOffOrigin b A := by
  rw [shiftVariationWindowOffOrigin_iff_zetaOddWindowPositiveOffOrigin ha,
    shiftVariationWindowOffOrigin_iff_zetaOddWindowPositiveOffOrigin hb]

theorem shiftVariationWindowOffOrigin_of_shiftVariationWindow {a A : ℝ}
    (h : ShiftVariationWindow a A) : ShiftVariationWindowOffOrigin a A :=
  fun u hu huc heven hv _ => h u hu huc heven hv

/-! ### 5. The Markov inequality is the pole-free odd window -/

/-- The odd window at `A` pays the Markov inequality at every shift. -/
theorem shiftMarkovWindow_of_zetaOddWindowPositive {A : ℝ} (h : ZetaOddWindowPositive A)
    (a : ℝ) : ShiftMarkovWindow a A := fun _ hu huc heven hv =>
  shiftedGroundState_markovEnergy_nonneg_of_zetaOddWindowPositive h a hu huc heven hv

/-- The odd window is contained in the pole-free odd window. -/
theorem zetaPoleFreeOddWindowPositive_of_zetaOddWindowPositive {A : ℝ}
    (h : ZetaOddWindowPositive A) : ZetaPoleFreeOddWindowPositive A :=
  fun F hF hFc hodd hv => (h F hF hFc hodd hv).trans (fullZeroForm_le_markovEnergy_of_odd hodd)

/-- The pole-free odd window is contained in the polar odd window. -/
theorem zetaPolarOddWindowPositive_of_zetaPoleFreeOddWindowPositive {A : ℝ}
    (h : ZetaPoleFreeOddWindowPositive A) : ZetaPolarOddWindowPositive A := by
  intro F hF hFc hodd hv hp
  have hM := h F hF hFc hodd hv
  rw [markovEnergy_eq_fullZeroForm_add_of_odd hodd, hp] at hM
  simpa using hM

/-- The pole-free odd window pays the Markov inequality at every shift and every profile. -/
theorem shiftMarkovWindow_of_zetaPoleFreeOddWindowPositive {A : ℝ}
    (h : ZetaPoleFreeOddWindowPositive A) (a : ℝ) : ShiftMarkovWindow a A :=
  fun _ hu huc heven hv =>
    h _ (contDiff_phiDoobTest ((contDiff_shiftedGroundState a).mul hu))
      (hasCompactSupport_phiDoobTest huc.mul_left) (phiDoob_shiftedGroundState_odd a heven)
      (phiDoob_shiftedGroundState_window hv)

/-- The Markov inequality at one shift gives the pole-free odd window on the tests vanishing
near the origin. -/
theorem zetaPoleFreeOddWindowPositiveOffOrigin_of_shiftMarkovWindow {a A : ℝ} (ha : 0 < a)
    (h : ShiftMarkovWindow a A) : ZetaPoleFreeOddWindowPositiveOffOrigin A := by
  intro F hF hFc hodd hv ⟨ε, hε, hvan⟩
  have h0 : F 0 = 0 := hvan 0 (by rwa [abs_zero])
  have hq := h (shiftQuotient a F) (contDiff_shiftQuotient ha hε hF hvan)
    (hasCompactSupport_shiftQuotient a hFc) (shiftQuotient_neg a hodd)
    (fun x hx => by unfold shiftQuotient; rw [hv x hx, zero_div])
  have e : (fun x => (phiDoobTest (fun y => shiftedGroundState a y * shiftQuotient a F y) x : ℂ)) =
      fun x => (F x : ℂ) :=
    funext fun x => by rw [phiDoobTest_shiftedGroundState_mul_shiftQuotient ha h0]
  rwa [e] at hq

/-- On the tests vanishing near the origin the Markov inequality at any shift is the pole-free odd
window. -/
theorem shiftMarkovWindowOffOrigin_iff_zetaPoleFreeOddWindowPositiveOffOrigin {a A : ℝ}
    (ha : 0 < a) :
    ShiftMarkovWindowOffOrigin a A ↔ ZetaPoleFreeOddWindowPositiveOffOrigin A := by
  constructor
  · intro h F hF hFc hodd hv ⟨ε, hε, hvan⟩
    have h0 : F 0 = 0 := hvan 0 (by rwa [abs_zero])
    have hq := h (shiftQuotient a F) (contDiff_shiftQuotient ha hε hF hvan)
      (hasCompactSupport_shiftQuotient a hFc) (shiftQuotient_neg a hodd)
      (fun x hx => by unfold shiftQuotient; rw [hv x hx, zero_div])
      ⟨ε, hε, fun x hx => shiftQuotient_eq_zero_of_abs_lt hvan hx⟩
    have e : (fun x =>
        (phiDoobTest (fun y => shiftedGroundState a y * shiftQuotient a F y) x : ℂ)) =
        fun x => (F x : ℂ) :=
      funext fun x => by rw [phiDoobTest_shiftedGroundState_mul_shiftQuotient ha h0]
    rwa [e] at hq
  · intro h u hu huc heven hv ⟨ε, hε, hvan⟩
    exact h _ (contDiff_phiDoobTest ((contDiff_shiftedGroundState a).mul hu))
      (hasCompactSupport_phiDoobTest huc.mul_left) (phiDoob_shiftedGroundState_odd a heven)
      (phiDoob_shiftedGroundState_window hv)
      ⟨ε, hε, phiDoob_shiftedGroundState_eq_zero_of_abs_lt hvan⟩

/-- The shift is a gauge for the Markov inequality at every aperture. -/
theorem shiftMarkovWindowOffOrigin_iff_of_pos {a b A : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ShiftMarkovWindowOffOrigin a A ↔ ShiftMarkovWindowOffOrigin b A := by
  rw [shiftMarkovWindowOffOrigin_iff_zetaPoleFreeOddWindowPositiveOffOrigin ha,
    shiftMarkovWindowOffOrigin_iff_zetaPoleFreeOddWindowPositiveOffOrigin hb]

/-! ### 6. What the pole term separates -/

/-- The Markov window gives the variation inequality exactly on the profiles of vanishing
`μ_a`-mean. -/
theorem variationInequality_of_shiftMarkovWindow_of_profileMoment_eq_zero {a A : ℝ} (ha : 0 < a)
    (h : ShiftMarkovWindow a A) {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u)
    (heven : ∀ x, u (-x) = u x) (hv : ∀ x, A < |x| → u x = 0) (hm : profileMoment a u = 0) :
    reflectedDifferenceEnergy (shiftedGroundState a) u ≤
      2 * sameSideEnergy (shiftedGroundState a) u + profileVariance a u := by
  rw [variationInequality_iff_fullZeroForm_nonneg ha hu huc heven]
  have hM := h u hu huc heven hv
  rw [markovEnergy_phiDoob_shiftedGroundState_eq_fullZeroForm_add ha hu huc heven, hm] at hM
  simpa using hM

/-- The Markov window at aperture `A` is the inequality `−8 (∫ u dμ_a)² ≤ Ẑ(m_a u)` on every
window profile: its converse to the odd window is the odd window on the tests of nonzero pole
moment. -/
theorem shiftMarkovWindow_iff_fullZeroForm_ge {a A : ℝ} (ha : 0 < a) :
    ShiftMarkovWindow a A ↔ ∀ u : ℝ → ℝ, ContDiff ℝ 2 u → HasCompactSupport u →
      (∀ x, u (-x) = u x) → (∀ x, A < |x| → u x = 0) →
        -(8 * profileMoment a u ^ 2) ≤
          fullZeroForm (phiDoobTest (fun y => shiftedGroundState a y * u y)) := by
  constructor
  · intro h u hu huc heven hv
    have hM := h u hu huc heven hv
    rw [markovEnergy_phiDoob_shiftedGroundState_eq_fullZeroForm_add ha hu huc heven] at hM
    linarith
  · intro h u hu huc heven hv
    rw [markovEnergy_phiDoob_shiftedGroundState_eq_fullZeroForm_add ha hu huc heven]
    linarith [h u hu huc heven hv]

/-- A failure of the odd window at any aperture refutes RH: the pole term cannot separate the
Markov window from the odd window unconditionally. -/
theorem not_riemannHypothesis_of_not_zetaOddWindowPositive {A : ℝ}
    (h : ¬ ZetaOddWindowPositive A) : ¬ RiemannHypothesis :=
  fun hRH => h fun _ hF hFc _ _ => fullZeroForm_nonneg_of_riemannHypothesis hRH hF hFc

/-! ### 7. The endpoint -/

/-- RH is the variation inequality at every aperture, at any one shift. -/
theorem riemannHypothesis_iff_forall_shiftVariationWindow {a : ℝ} (ha : 0 < a) :
    RiemannHypothesis ↔ ∀ A : ℝ, ShiftVariationWindow a A := by
  constructor
  · intro hRH A u hu huc heven _
    exact (riemannHypothesis_iff_forall_poleFreeVariationInequality ha).mp hRH u hu huc heven
  · intro h
    rw [riemannHypothesis_iff_forall_poleFreeVariationInequality ha]
    intro u hu huc heven
    obtain ⟨R, -, hR⟩ := exists_vanishing_radius_of_hasCompactSupport huc
    exact h R u hu huc heven hR

/-- RH is the Markov inequality at every aperture, at any one shift. -/
theorem riemannHypothesis_iff_forall_shiftMarkovWindow {a : ℝ} (ha : 0 < a) :
    RiemannHypothesis ↔ ∀ A : ℝ, ShiftMarkovWindow a A := by
  constructor
  · intro hRH A u hu huc heven _
    exact (riemannHypothesis_iff_forall_shiftedGroundState_markovEnergy_nonneg ha).mp hRH u hu
      huc heven
  · intro h
    rw [riemannHypothesis_iff_forall_shiftedGroundState_markovEnergy_nonneg ha]
    intro u hu huc heven
    obtain ⟨R, -, hR⟩ := exists_vanishing_radius_of_hasCompactSupport huc
    exact h R u hu huc heven hR

/-- RH is the odd window at every aperture. -/
theorem riemannHypothesis_iff_forall_zetaOddWindowPositive :
    RiemannHypothesis ↔ ∀ A : ℝ, ZetaOddWindowPositive A := by
  constructor
  · intro hRH A _ hF hFc _ _
    exact fullZeroForm_nonneg_of_riemannHypothesis hRH hF hFc
  · intro h
    rw [riemannHypothesis_iff_forall_odd_zeroForm_nonneg]
    intro v hv hvc hodd
    have hodd' : ∀ x, phiDoobTest v (-x) = -phiDoobTest v x := fun x => by
      simp only [phiDoobTest, riemannKernelReal_neg', hodd]
      ring
    obtain ⟨R, -, hR⟩ :=
      exists_vanishing_radius_of_hasCompactSupport (hasCompactSupport_phiDoobTest hvc)
    rw [← fullZeroForm_eq_zeroForm_of_odd hodd']
    exact h R _ (contDiff_phiDoobTest hv) (hasCompactSupport_phiDoobTest hvc) hodd' hR

/-- **The shifted ground-state inequalities read the odd window.** At every aperture `A` and shift
`a > 0`: the odd window gives the variation inequality on every profile; the variation inequality
gives the odd window on the tests vanishing near the origin, where the two coincide at every shift;
the odd window gives the Markov inequality, which on those tests is the pole-free odd window and
which gives the polar odd window; and at the endpoint each of them at every aperture is RH. -/
theorem theShiftedGroundStateInequalitiesReadTheOddWindow {a : ℝ} (ha : 0 < a) (A : ℝ) :
    (ZetaOddWindowPositive A → ShiftVariationWindow a A) ∧
    (ShiftVariationWindow a A → ZetaOddWindowPositiveOffOrigin A) ∧
    (ShiftVariationWindowOffOrigin a A ↔ ZetaOddWindowPositiveOffOrigin A) ∧
    (ZetaOddWindowPositive A → ShiftMarkovWindow a A) ∧
    (ShiftMarkovWindowOffOrigin a A ↔ ZetaPoleFreeOddWindowPositiveOffOrigin A) ∧
    (ZetaPoleFreeOddWindowPositive A → ZetaPolarOddWindowPositive A) ∧
    (RiemannHypothesis ↔ ∀ B : ℝ, ShiftVariationWindow a B) ∧
    (RiemannHypothesis ↔ ∀ B : ℝ, ZetaOddWindowPositive B) :=
  ⟨fun h => shiftVariationWindow_of_zetaOddWindowPositive h ha,
    zetaOddWindowPositiveOffOrigin_of_shiftVariationWindow ha,
    shiftVariationWindowOffOrigin_iff_zetaOddWindowPositiveOffOrigin ha,
    fun h => shiftMarkovWindow_of_zetaOddWindowPositive h a,
    shiftMarkovWindowOffOrigin_iff_zetaPoleFreeOddWindowPositiveOffOrigin ha,
    zetaPolarOddWindowPositive_of_zetaPoleFreeOddWindowPositive,
    riemannHypothesis_iff_forall_shiftVariationWindow ha,
    riemannHypothesis_iff_forall_zetaOddWindowPositive⟩

end GaloisForLFunctions.SquareRootThreshold

end
