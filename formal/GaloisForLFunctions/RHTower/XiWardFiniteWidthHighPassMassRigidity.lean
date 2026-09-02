import GaloisForLFunctions.RHTower.XiWardCellRandomizedAnnulusCoercivity
import GaloisForLFunctions.HTGeometry.HalfPlanePoissonKernel

/-!
# Finite-width high-pass mass rigidity for the Xi Ward route

A complete reflected Ward pair has total real-line mass `4 * π`, independent of
its positive interior width and reflected center.  Hence a finite signed mixture
of such profiles can dominate one pair only if its total coefficient is at least
one.  In particular, zero-mass differencing across finitely many interior widths
cannot both cancel a common width-independent source mode and preserve positive
pointwise domination of the Ward detector.
-/

open Complex Set MeasureTheory
open scoped BigOperators

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

private theorem wardLorentzianHalf_eq_poisson
    (x beta t : ℝ) :
    wardLorentzianHalf x beta t =
      Real.pi * halfPlanePoisson x (t + beta) := by
  unfold wardLorentzianHalf halfPlanePoisson
  by_cases hpi : Real.pi = 0
  · exact (Real.pi_ne_zero hpi).elim
  field_simp

/-- One Ward Lorentzian half-profile is integrable at every positive width. -/
theorem integrable_wardLorentzianHalf_profile
    {x : ℝ} (hx : 0 < x) (beta : ℝ) :
    Integrable (wardLorentzianHalf x beta) := by
  rw [show wardLorentzianHalf x beta = fun t : ℝ =>
      Real.pi * halfPlanePoisson x (t + beta) by
    funext t
    exact wardLorentzianHalf_eq_poisson x beta t]
  exact ((integrable_halfPlanePoisson hx).comp_add_right beta).const_mul Real.pi

/-- Width- and center-independent mass of one Ward Lorentzian half-profile. -/
theorem integral_wardLorentzianHalf_eq_pi
    {x : ℝ} (hx : 0 < x) (beta : ℝ) :
    (∫ t : ℝ, wardLorentzianHalf x beta t) = Real.pi := by
  rw [show wardLorentzianHalf x beta = fun t : ℝ =>
      Real.pi * halfPlanePoisson x (t + beta) by
    funext t
    exact wardLorentzianHalf_eq_poisson x beta t]
  rw [MeasureTheory.integral_const_mul,
    MeasureTheory.integral_add_right_eq_self,
    integral_halfPlanePoisson hx]
  ring

/-- A complete reflected Ward-pair profile is integrable at positive width. -/
theorem integrable_wardReflectedLorentzianProfile
    {x : ℝ} (hx : 0 < x) (beta : ℝ) :
    Integrable (wardReflectedLorentzianProfile x beta) := by
  unfold wardReflectedLorentzianProfile
  exact ((integrable_wardLorentzianHalf_profile hx beta).const_mul 2).add
    ((integrable_wardLorentzianHalf_profile hx (-beta)).const_mul 2)

/-- Every complete reflected Ward pair has total mass exactly `4 * π`. -/
theorem integral_wardReflectedLorentzianProfile_eq_four_pi
    {x : ℝ} (hx : 0 < x) (beta : ℝ) :
    (∫ t : ℝ, wardReflectedLorentzianProfile x beta t) = 4 * Real.pi := by
  unfold wardReflectedLorentzianProfile
  rw [MeasureTheory.integral_add
      ((integrable_wardLorentzianHalf_profile hx beta).const_mul 2)
      ((integrable_wardLorentzianHalf_profile hx (-beta)).const_mul 2),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    integral_wardLorentzianHalf_eq_pi hx beta,
    integral_wardLorentzianHalf_eq_pi hx (-beta)]
  ring

/-- Finite signed mixture of reflected Ward pairs at a common center. -/
def wardFiniteWidthMixture {ι : Type*}
    (S : Finset ι) (c x : ι → ℝ) (beta t : ℝ) : ℝ :=
  ∑ i ∈ S, c i * wardReflectedLorentzianProfile (x i) beta t

/-- Positive component widths make every finite signed width mixture integrable. -/
theorem integrable_wardFiniteWidthMixture
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (c x : ι → ℝ) (beta : ℝ)
    (hx : ∀ i ∈ S, 0 < x i) :
    Integrable (wardFiniteWidthMixture S c x beta) := by
  unfold wardFiniteWidthMixture
  apply integrable_finsetSum
  intro i hi
  exact (integrable_wardReflectedLorentzianProfile (hx i hi) beta).const_mul (c i)

/-- The only scalar mass retained by a finite width mixture is its coefficient sum. -/
theorem integral_wardFiniteWidthMixture_eq
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (c x : ι → ℝ) (beta : ℝ)
    (hx : ∀ i ∈ S, 0 < x i) :
    (∫ t : ℝ, wardFiniteWidthMixture S c x beta t) =
      4 * Real.pi * ∑ i ∈ S, c i := by
  unfold wardFiniteWidthMixture
  have hterm : ∀ i ∈ S, Integrable
      (fun t : ℝ => c i * wardReflectedLorentzianProfile (x i) beta t) := by
    intro i hi
    exact (integrable_wardReflectedLorentzianProfile (hx i hi) beta).const_mul (c i)
  rw [MeasureTheory.integral_finsetSum S hterm]
  calc
    (∑ i ∈ S, ∫ t : ℝ,
        c i * wardReflectedLorentzianProfile (x i) beta t) =
        ∑ i ∈ S, c i * (4 * Real.pi) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [MeasureTheory.integral_const_mul,
        integral_wardReflectedLorentzianProfile_eq_four_pi (hx i hi) beta]
    _ = 4 * Real.pi * ∑ i ∈ S, c i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

/--
Sharp mass rigidity: pointwise domination of one reflected Ward pair by a finite
signed width mixture forces at least one full unit of total coefficient mass.
-/
theorem one_le_sum_of_wardReflectedLorentzianProfile_le_widthMixture
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (c x : ι → ℝ) {targetX : ℝ} (htargetX : 0 < targetX)
    (beta : ℝ) (hx : ∀ i ∈ S, 0 < x i)
    (hdom : ∀ t : ℝ,
      wardReflectedLorentzianProfile targetX beta t ≤
        wardFiniteWidthMixture S c x beta t) :
    1 ≤ ∑ i ∈ S, c i := by
  have hle := MeasureTheory.integral_mono
    (integrable_wardReflectedLorentzianProfile htargetX beta)
    (integrable_wardFiniteWidthMixture S c x beta hx)
    hdom
  rw [integral_wardReflectedLorentzianProfile_eq_four_pi htargetX beta,
    integral_wardFiniteWidthMixture_eq S c x beta hx] at hle
  nlinarith [Real.pi_pos]

/-- Zero-total-coefficient finite width mixtures cannot dominate one Ward pair. -/
theorem not_forall_wardReflectedLorentzianProfile_le_zeroMassWidthMixture
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (c x : ι → ℝ) {targetX : ℝ} (htargetX : 0 < targetX)
    (beta : ℝ) (hx : ∀ i ∈ S, 0 < x i)
    (hzero : ∑ i ∈ S, c i = 0) :
    ¬ ∀ t : ℝ, wardReflectedLorentzianProfile targetX beta t ≤
      wardFiniteWidthMixture S c x beta t := by
  intro hdom
  have hone := one_le_sum_of_wardReflectedLorentzianProfile_le_widthMixture
    S c x htargetX beta hx hdom
  rw [hzero] at hone
  norm_num at hone

/--
Closed Route-G candidate class: a finite zero-mass interior-width high-pass
claimed to preserve pointwise domination of one complete reflected Ward pair.
-/
def XiWardFiniteZeroMassWidthHighPassMajorantRoute : Prop :=
  ∃ (n : ℕ) (c x : Fin n → ℝ) (targetX beta : ℝ),
    0 < targetX ∧
    (∀ i, 0 < x i) ∧
    (∑ i, c i = 0) ∧
    ∀ t : ℝ, wardReflectedLorentzianProfile targetX beta t ≤
      wardFiniteWidthMixture Finset.univ c x beta t

/--
**Route-G producer-class kill.** No finite zero-mass differencing across positive
interior widths can cancel the common scalar mode while retaining a positive
pointwise majorant of the complete reflected Ward detector.
-/
theorem xiWardFiniteZeroMassWidthHighPassMajorantRouteKilled :
    ¬ XiWardFiniteZeroMassWidthHighPassMajorantRoute := by
  rintro ⟨n, c, x, targetX, beta, htargetX, hx, hzero, hdom⟩
  exact (not_forall_wardReflectedLorentzianProfile_le_zeroMassWidthMixture
    Finset.univ c x htargetX beta (by
      intro i hi
      exact hx i) hzero) hdom

end
end RHTower
