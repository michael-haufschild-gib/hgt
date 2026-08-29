import GaloisForLFunctions.RHTower.ThetaCuspFifthRootCurvatureStationaryLocus
import Mathlib.Analysis.Calculus.Taylor

/-!
# Stationary acceleration obstruction for modular-center theta C5

Every modular-center C5 failure attains a negative local minimum.  This file records the next
literal consequence: the fourth source-flux jet makes the C5 acceleration nonnegative there.
At the same witness, the already-proved strict fourth-Turan law gives a scale-sensitive upper
bound on the fourth reflected logarithmic jet.  Thus any failure must satisfy one simultaneous
third/fourth-jet and nonlocal likelihood-tax obstruction.
-/

open Real Set Filter Topology

namespace RHTower

noncomputable section

private theorem contDiff_top_iteratedDeriv_real
    {f : ℝ → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (k : ℕ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (iteratedDeriv k f) := by
  rw [contDiff_iff_iteratedDeriv]
  constructor
  · intro m _
    rw [show iteratedDeriv m (iteratedDeriv k f) =
      iteratedDeriv (m + k) f by
        simp only [iteratedDeriv_eq_iterate]
        rw [Function.iterate_add_apply]]
    exact hf.continuous_iteratedDeriv _ (by exact_mod_cast le_top)
  · intro m _
    rw [show iteratedDeriv m (iteratedDeriv k f) =
      iteratedDeriv (m + k) f by
        simp only [iteratedDeriv_eq_iterate]
        rw [Function.iterate_add_apply]]
    exact hf.differentiable_iteratedDeriv _
      (by exact_mod_cast WithTop.coe_lt_top (m + k))

private theorem second_iteratedDeriv_nonneg_of_isLocalMin
    {f : ℝ → ℝ} {x : ℝ} (hf : ContDiff ℝ 2 f) (hmin : IsLocalMin f x) :
    0 ≤ iteratedDeriv 2 f x := by
  by_contra hnot
  have hsecond : iteratedDeriv 2 f x < 0 := lt_of_not_ge hnot
  have hfirst : iteratedDeriv 1 f x = 0 := by
    simpa only [iteratedDeriv_one] using hmin.hasDerivAt_eq_zero
      (hf.differentiable (by norm_num) x).hasDerivAt
  have htaylor := taylor_isLittleO_univ (f := f) (x₀ := x) (n := 2) hf
  have hquarter : 0 < -(iteratedDeriv 2 f x) / 4 := by linarith
  have hbound := htaylor.def hquarter
  have hpoly : ∀ y : ℝ,
      taylorWithinEval f 2 univ x y =
        f x + (y - x) * iteratedDeriv 1 f x +
          ((y - x) ^ 2 / 2) * iteratedDeriv 2 f x := by
    intro y
    rw [show 2 = 1 + 1 by norm_num, taylorWithinEval_succ,
      taylorWithinEval_succ, taylor_within_zero_eval]
    simp
    ring_nf
    simp
  have hevent : ∀ᶠ y in 𝓝 x,
      f x ≤ f y ∧
        ‖f y - taylorWithinEval f 2 univ x y‖ ≤
          (-(iteratedDeriv 2 f x) / 4) * ‖(y - x) ^ 2‖ :=
    hmin.and hbound
  obtain ⟨y, hy, hymin, hybound⟩ := hevent.exists_gt
  rw [hpoly y, hfirst] at hybound
  have hsquare : 0 < (y - x) ^ 2 := sq_pos_of_pos (sub_pos.mpr hy)
  have hnorm : ‖(y - x) ^ 2‖ = (y - x) ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (y - x))]
  rw [hnorm] at hybound
  have hremainder :
      f y - (f x + (y - x) ^ 2 / 2 * iteratedDeriv 2 f x) ≤
        -(iteratedDeriv 2 f x) / 4 * (y - x) ^ 2 := by
    calc
      _ ≤ |f y - (f x + (y - x) ^ 2 / 2 * iteratedDeriv 2 f x)| := le_abs_self _
      _ = ‖f y - (f x + (y - x) ^ 2 / 2 * iteratedDeriv 2 f x)‖ :=
        (Real.norm_eq_abs _).symm
      _ ≤ _ := by simpa only [mul_zero, add_zero] using hybound
  nlinarith

/-- Fourth displacement jet of the reflected logarithmic action. -/
def thetaCuspReflectedLogJetFour (u t : ℝ) : ℝ :=
  -iteratedDeriv 4 thetaCuspLogSource (u + t) -
    iteratedDeriv 4 thetaCuspLogSource (u - t)

theorem hasDerivAt_thetaCuspReflectedLogJetThree (u t : ℝ) :
    HasDerivAt (thetaCuspReflectedLogJetThree u)
      (thetaCuspReflectedLogJetFour u t) t := by
  have hp :=
    (hasDerivAt_iteratedDeriv_thetaCuspLogSource 3 (u + t)).comp t
      ((hasDerivAt_id t).const_add u)
  have hm :=
    (hasDerivAt_iteratedDeriv_thetaCuspLogSource 3 (u - t)).comp t
      ((hasDerivAt_id t).const_sub u)
  unfold thetaCuspReflectedLogJetThree thetaCuspLogCurvatureJet
    thetaCuspReflectedLogJetFour
  convert hp.neg.sub hm.neg using 1
  all_goals first | rfl | simp [sub_eq_add_neg]

/-- Fourth ordinary jet of the positive reflected-source decay flux. -/
def thetaCuspReflectedSourceDecayFluxFourthJet (u t : ℝ) : ℝ :=
  thetaCuspReflectedSourceProduct u t *
    (thetaCuspReflectedLogJetFour u t -
      4 * thetaCuspReflectedLogJetOne u t * thetaCuspReflectedLogJetThree u t -
      3 * thetaCuspReflectedLogJetTwo u t ^ 2 +
      6 * thetaCuspReflectedLogJetOne u t ^ 2 * thetaCuspReflectedLogJetTwo u t -
      thetaCuspReflectedLogJetOne u t ^ 4)

theorem hasDerivAt_thetaCuspReflectedSourceDecayFluxThirdJet (u t : ℝ) :
    HasDerivAt (thetaCuspReflectedSourceDecayFluxThirdJet u)
      (thetaCuspReflectedSourceDecayFluxFourthJet u t) t := by
  have hp := hasDerivAt_thetaCuspReflectedSourceProduct u t
  have hq1 := hasDerivAt_thetaCuspReflectedLogJetOne u t
  have hq2 := hasDerivAt_thetaCuspReflectedLogJetTwo u t
  have hq3 := hasDerivAt_thetaCuspReflectedLogJetThree u t
  have hinside := (hq3.sub ((hq1.mul hq2).const_mul 3)).add (hq1.pow 3)
  have hraw := hp.mul hinside
  have hfun :
      thetaCuspReflectedSourceProduct u *
          ((thetaCuspReflectedLogJetThree u -
              fun s => 3 * (thetaCuspReflectedLogJetOne u *
                thetaCuspReflectedLogJetTwo u) s) +
            thetaCuspReflectedLogJetOne u ^ 3) =
        fun s => thetaCuspReflectedSourceProduct u s *
          (thetaCuspReflectedLogJetThree u s -
            3 * thetaCuspReflectedLogJetOne u s *
              thetaCuspReflectedLogJetTwo u s +
            thetaCuspReflectedLogJetOne u s ^ 3) := by
    funext s
    simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply]
    ring
  rw [hfun] at hraw
  unfold thetaCuspReflectedSourceDecayFluxThirdJet
    thetaCuspReflectedSourceDecayFluxFourthJet
  refine hraw.congr_deriv ?_
  unfold thetaCuspReflectedSourceDecayFlux
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply,
    Nat.cast_ofNat, Nat.reduceSub]
  ring

/-- Ordinary displacement acceleration of the source fifth-root curvature numerator. -/
def thetaCuspReflectedSourceFifthRootCurvatureAcceleration (u t : ℝ) : ℝ :=
  let A := thetaCuspReflectedSourceFirstDrop u t
  let D := thetaCuspReflectedSourceDecayFlux u t
  let J := thetaCuspReflectedSourceDecayFluxCurvature u t
  let K := thetaCuspReflectedSourceDecayFluxThirdJet u t
  let L := thetaCuspReflectedSourceDecayFluxFourthJet u t
  22 * D ^ 2 + 40 * A * J - 39 * t * D * J + 11 * t * A * K +
    t ^ 2 * (2 * D * K + 5 * A * L - 3 * J ^ 2)

theorem hasDerivAt_thetaCuspReflectedSourceFifthRootCurvatureVelocity
    (u t : ℝ) :
    HasDerivAt (thetaCuspReflectedSourceFifthRootCurvatureVelocity u)
      (thetaCuspReflectedSourceFifthRootCurvatureAcceleration u t) t := by
  let A : ℝ → ℝ := thetaCuspReflectedSourceFirstDrop u
  let D : ℝ → ℝ := thetaCuspReflectedSourceDecayFlux u
  let J : ℝ → ℝ := thetaCuspReflectedSourceDecayFluxCurvature u
  let K : ℝ → ℝ := thetaCuspReflectedSourceDecayFluxThirdJet u
  let L : ℝ → ℝ := thetaCuspReflectedSourceDecayFluxFourthJet u
  have hA : HasDerivAt A (D t) t := by
    simpa only [A, D] using hasDerivAt_thetaCuspReflectedSourceFirstDrop u t
  have hD : HasDerivAt D (J t) t := by
    simpa only [D, J] using hasDerivAt_thetaCuspReflectedSourceDecayFlux u t
  have hJ : HasDerivAt J (K t) t := by
    simpa only [J, K] using hasDerivAt_thetaCuspReflectedSourceDecayFluxCurvature u t
  have hK : HasDerivAt K (L t) t := by
    simpa only [K, L] using hasDerivAt_thetaCuspReflectedSourceDecayFluxThirdJet u t
  have hraw :=
    (((hA.mul hD).const_mul 39).add
      ((((hasDerivAt_id t).mul hA).mul hJ))).sub
      ((((hasDerivAt_id t).mul (hD.pow 2)).const_mul 17)) |>.add
      (((hasDerivAt_id t).pow 2).mul
        (((hA.mul hK).const_mul 5).sub ((hD.mul hJ).const_mul 3)))
  refine (hraw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun s => ?_)).congr_deriv ?_
  · unfold thetaCuspReflectedSourceFifthRootCurvatureVelocity
    simp only [A, D, J, K, Pi.add_apply, Pi.sub_apply, Pi.mul_apply,
      Pi.pow_apply, id_eq]
    ring
  · unfold thetaCuspReflectedSourceFifthRootCurvatureAcceleration
    simp only [A, D, J, K, L, Pi.sub_apply, Pi.mul_apply,
      Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, one_mul]
    ring

theorem contDiff_two_thetaCuspReflectedSourceFifthRootCurvatureNumerator
    (u : ℝ) :
    ContDiff ℝ 2 (thetaCuspReflectedSourceFifthRootCurvatureNumerator u) := by
  have hjet (m : ℕ) :
      ContDiff ℝ (↑(⊤ : ℕ∞)) (iteratedDeriv m thetaCuspLogSource) :=
    contDiff_top_iteratedDeriv_real contDiff_thetaCuspLogSource m
  have hplus (m : ℕ) : ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun t : ℝ => iteratedDeriv m thetaCuspLogSource (u + t)) :=
    (hjet m).comp (contDiff_const.add contDiff_id)
  have hminus (m : ℕ) : ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun t : ℝ => iteratedDeriv m thetaCuspLogSource (u - t)) :=
    (hjet m).comp (contDiff_const.sub contDiff_id)
  have hq1 : ContDiff ℝ (↑(⊤ : ℕ∞)) (thetaCuspReflectedLogJetOne u) := by
    unfold thetaCuspReflectedLogJetOne thetaCuspLogDecaySlope
    fun_prop
  have hq2 : ContDiff ℝ (↑(⊤ : ℕ∞)) (thetaCuspReflectedLogJetTwo u) := by
    unfold thetaCuspReflectedLogJetTwo thetaCuspLogCurvature
    fun_prop
  have hP := contDiff_thetaCuspReflectedSourceProduct u
  have hA : ContDiff ℝ (↑(⊤ : ℕ∞)) (thetaCuspReflectedSourceFirstDrop u) := by
    unfold thetaCuspReflectedSourceFirstDrop
    fun_prop
  have hD : ContDiff ℝ (↑(⊤ : ℕ∞)) (thetaCuspReflectedSourceDecayFlux u) := by
    unfold thetaCuspReflectedSourceDecayFlux
    exact hP.mul hq1
  have hJ : ContDiff ℝ (↑(⊤ : ℕ∞))
      (thetaCuspReflectedSourceDecayFluxCurvature u) := by
    unfold thetaCuspReflectedSourceDecayFluxCurvature
    fun_prop
  unfold thetaCuspReflectedSourceFifthRootCurvatureNumerator
  change ContDiff ℝ 2 (fun t =>
    24 * thetaCuspReflectedSourceFirstDrop u t ^ 2 -
      9 * t * thetaCuspReflectedSourceFirstDrop u t *
        thetaCuspReflectedSourceDecayFlux u t +
      t ^ 2 *
        (5 * thetaCuspReflectedSourceFirstDrop u t *
            thetaCuspReflectedSourceDecayFluxCurvature u t -
          4 * thetaCuspReflectedSourceDecayFlux u t ^ 2))
  have htop : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun t =>
      24 * thetaCuspReflectedSourceFirstDrop u t ^ 2 -
        9 * t * thetaCuspReflectedSourceFirstDrop u t *
          thetaCuspReflectedSourceDecayFlux u t +
        t ^ 2 *
          (5 * thetaCuspReflectedSourceFirstDrop u t *
              thetaCuspReflectedSourceDecayFluxCurvature u t -
            4 * thetaCuspReflectedSourceDecayFlux u t ^ 2)) := by
    fun_prop
  exact htop.of_le (by exact WithTop.coe_le_coe.mpr le_top)

theorem iteratedDeriv_two_thetaCuspReflectedSourceFifthRootCurvatureNumerator
    (u t : ℝ) :
    iteratedDeriv 2 (thetaCuspReflectedSourceFifthRootCurvatureNumerator u) t =
      thetaCuspReflectedSourceFifthRootCurvatureAcceleration u t := by
  rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
  have hfirst : deriv (thetaCuspReflectedSourceFifthRootCurvatureNumerator u) =
      thetaCuspReflectedSourceFifthRootCurvatureVelocity u := by
    funext s
    exact (hasDerivAt_thetaCuspReflectedSourceFifthRootCurvatureNumerator u s).deriv
  rw [hfirst, (hasDerivAt_thetaCuspReflectedSourceFifthRootCurvatureVelocity u t).deriv]

/-- The strict source fourth-Turan law becomes a scale-sensitive upper bound on the fourth
reflected logarithmic action jet at modular center. -/
theorem thetaCuspReflectedLogJetFour_zero_add_threeHundredTwenty_lt_two_sq
    {t : ℝ} (ht : 0 < t) :
    thetaCuspReflectedLogJetFour 0 t + 320 <
      2 * thetaCuspReflectedLogJetTwo 0 t ^ 2 := by
  have hT := thetaCuspLogSource_fourthTuran_gt_one_hundred_sixty ht
  have h2 := iteratedDeriv_thetaCuspLogSource_neg 2 t
  have h4 := iteratedDeriv_thetaCuspLogSource_neg 4 t
  norm_num at h2 h4
  unfold thetaCuspReflectedLogJetFour thetaCuspReflectedLogJetTwo
    thetaCuspLogCurvature
  norm_num
  rw [h2, h4]
  nlinarith

/-- Every modular-center C5 failure has one negative stationary local-minimum witness whose
fourth-flux acceleration is nonnegative and whose fourth logarithmic jet obeys the strict theta
fourth-Turan ceiling. -/
theorem
    thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_failure_forces_stationary_acceleration
    (hfail : ∃ t : ℝ, 0 < t ∧
      thetaCuspReflectedSourceFifthRootCurvatureNumerator 0 t < 0) :
    ∃ t : ℝ, 0 < t ∧
      thetaCuspReflectedSourceFifthRootCurvatureNumerator 0 t < 0 ∧
      thetaCuspReflectedSourceFifthRootCurvatureVelocity 0 t = 0 ∧
      0 ≤ thetaCuspReflectedSourceFifthRootCurvatureAcceleration 0 t ∧
      thetaCuspReflectedLogJetFour 0 t + 320 <
        2 * thetaCuspReflectedLogJetTwo 0 t ^ 2 := by
  rcases hfail with ⟨t0, ht0, hneg0⟩
  rcases exists_thetaCuspReflectedSourceFifthRootCurvatureNumerator_pos_right 0 with
    ⟨delta0, hdelta0, hnear⟩
  rcases exists_thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_pos_tail with
    ⟨T0, hT0, htail⟩
  let delta := min (delta0 / 2) (t0 / 2)
  let T := max T0 (t0 + 1)
  have hdelta : 0 < delta := lt_min (by positivity) (by positivity)
  have hdeltadelta0 : delta < delta0 :=
    lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hdeltat0 : delta < t0 :=
    lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have ht0T : t0 < T := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hT0T : T0 ≤ T := le_max_left _ _
  have hdeltapos :
      0 < thetaCuspReflectedSourceFifthRootCurvatureNumerator 0 delta :=
    hnear delta hdelta hdeltadelta0
  have hTpos : 0 < thetaCuspReflectedSourceFifthRootCurvatureNumerator 0 T :=
    htail T hT0T
  have hcont : ContinuousOn
      (thetaCuspReflectedSourceFifthRootCurvatureNumerator 0) (Icc delta T) :=
    (continuous_thetaCuspReflectedSourceFifthRootCurvatureNumerator 0).continuousOn
  obtain ⟨t, ht, hmin⟩ := isCompact_Icc.exists_isMinOn
    ⟨t0, hdeltat0.le, ht0T.le⟩ hcont
  have hneg : thetaCuspReflectedSourceFifthRootCurvatureNumerator 0 t < 0 :=
    lt_of_le_of_lt (hmin ⟨hdeltat0.le, ht0T.le⟩) hneg0
  have hdeltat : delta < t := by
    exact lt_of_le_of_ne ht.1 (fun h => by
      subst t
      linarith)
  have htT : t < T := by
    exact lt_of_le_of_ne ht.2 (fun h => by
      subst t
      linarith)
  have hlocal : IsLocalMin
      (thetaCuspReflectedSourceFifthRootCurvatureNumerator 0) t :=
    hmin.isLocalMin (Icc_mem_nhds hdeltat htT)
  have hstationary := hlocal.hasDerivAt_eq_zero
    (hasDerivAt_thetaCuspReflectedSourceFifthRootCurvatureNumerator 0 t)
  have hacc := second_iteratedDeriv_nonneg_of_isLocalMin
    (contDiff_two_thetaCuspReflectedSourceFifthRootCurvatureNumerator 0) hlocal
  rw [iteratedDeriv_two_thetaCuspReflectedSourceFifthRootCurvatureNumerator] at hacc
  have htpos : 0 < t := hdelta.trans hdeltat
  exact ⟨t, htpos, hneg, hstationary, hacc,
    thetaCuspReflectedLogJetFour_zero_add_threeHundredTwenty_lt_two_sq htpos⟩

/-- Fully joined obstruction: every modular-center C5 failure simultaneously produces a
negative stationary local minimum, nonnegative fourth-flux acceleration, the strict theta
fourth-Turan ceiling, and a strict overspend of the exact cofinal likelihood reserve. -/
theorem
    thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_failure_forces_acceleration_taxOverspend
    (hfail : ∃ t : ℝ, 0 < t ∧
      thetaCuspReflectedSourceFifthRootCurvatureNumerator 0 t < 0) :
    ∃ t : ℝ, 0 < t ∧
      thetaCuspReflectedSourceFifthRootCurvatureVelocity 0 t = 0 ∧
      0 ≤ thetaCuspReflectedSourceFifthRootCurvatureAcceleration 0 t ∧
      thetaCuspReflectedLogJetFour 0 t + 320 <
        2 * thetaCuspReflectedLogJetTwo 0 t ^ 2 ∧
      thetaCuspCompletedProductFiberCofinalLikelihoodIntegralDriftReserveAtZero t <
        thetaCuspCompletedProductFiberCofinalLikelihoodTaxDensityAtZero t := by
  obtain ⟨t, ht, hneg, hstationary, hacc, hfour⟩ :=
    thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_failure_forces_stationary_acceleration
      hfail
  have hover :
      thetaCuspCompletedProductFiberCofinalLikelihoodIntegralDriftReserveAtZero t <
        thetaCuspCompletedProductFiberCofinalLikelihoodTaxDensityAtZero t := by
    apply lt_of_not_ge
    intro hreserve
    have hnonneg :=
      (thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_nonneg_iff_taxDensity_le_integralReserve
        ht).mpr hreserve
    exact (not_lt_of_ge hnonneg) hneg
  exact ⟨t, ht, hstationary, hacc, hfour, hover⟩

/-- Global modular-center C5 is equivalent to positivity only on stationary points whose C5
acceleration is nonnegative.  Negative-acceleration stationary points cannot be failure minima. -/
theorem
    thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_nonneg_all_iff_stationary_acceleration :
    (∀ t : ℝ, 0 < t →
      0 ≤ thetaCuspReflectedSourceFifthRootCurvatureNumerator 0 t) ↔
      ∀ t : ℝ, 0 < t →
        thetaCuspReflectedSourceFifthRootCurvatureVelocity 0 t = 0 →
        0 ≤ thetaCuspReflectedSourceFifthRootCurvatureAcceleration 0 t →
        0 ≤ thetaCuspReflectedSourceFifthRootCurvatureNumerator 0 t := by
  constructor
  · intro h t ht _ _
    exact h t ht
  · intro h t ht
    by_contra hneg
    obtain ⟨s, hs, hsneg, hsstationary, hsacc, _hsfour⟩ :=
      thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_failure_forces_stationary_acceleration
        ⟨t, ht, lt_of_not_ge hneg⟩
    exact (not_lt_of_ge (h s hs hsstationary hsacc)) hsneg

/-- Exact surviving C5-SA1 burden after stationary acceleration localization: the cofinal
likelihood tax need only be absorbed where velocity vanishes and acceleration is nonnegative. -/
theorem
    thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_nonneg_all_iff_stationary_acceleration_taxReserve :
    (∀ t : ℝ, 0 < t →
      0 ≤ thetaCuspReflectedSourceFifthRootCurvatureNumerator 0 t) ↔
      ∀ t : ℝ, 0 < t →
        thetaCuspReflectedSourceFifthRootCurvatureVelocity 0 t = 0 →
        0 ≤ thetaCuspReflectedSourceFifthRootCurvatureAcceleration 0 t →
        thetaCuspCompletedProductFiberCofinalLikelihoodTaxDensityAtZero t ≤
          thetaCuspCompletedProductFiberCofinalLikelihoodIntegralDriftReserveAtZero t := by
  rw [
    thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_nonneg_all_iff_stationary_acceleration]
  constructor
  · intro h t ht hstationary hacc
    exact
      (thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_nonneg_iff_taxDensity_le_integralReserve
        ht).mp (h t ht hstationary hacc)
  · intro h t ht hstationary hacc
    exact
      (thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_nonneg_iff_taxDensity_le_integralReserve
        ht).mpr (h t ht hstationary hacc)

end

end RHTower
