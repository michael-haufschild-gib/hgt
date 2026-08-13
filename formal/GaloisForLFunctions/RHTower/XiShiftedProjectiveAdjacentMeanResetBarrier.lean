import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionProjectiveCofinalSpread
import GaloisForLFunctions.HTGeometry.FavardJacobiMomentRealization

/-!
# Adjacent-mean transport, reset barrier, and the positive-Jacobi reset counterfamily

The projective packet at admission degree `n` carries the weighted flux
`Fₙ = 2·(α₀ + ⋯ + αₙ₋₁) + αₙ` of total mass `2n + 1`, its mean `μₙ = Fₙ/(2n+1)`, and its
centered square sum `Eₙ`.  Passing to degree `n + 1` adds one extra copy of `αₙ` and one new
observation `αₙ₊₁`.  The two-observation online-variance identity makes the energy increment an
exact sum of a two-point dispersion and a between-packet term, so Euclidean variance controls the
Euclidean mean displacement; the reciprocal projective clock `1/μ - y` instead sees the singular
metric `dμ/μ²`.  A bounded positive Jacobi counterfamily then shows that no locally bounded
function of the ordinary variance and Gauss-spread accounts can bound the negative clock reset:
the denominator weight is structurally necessary, and the corrected synchronization invariant is
the hyperbolic reset action `(Eₙ₊₁ - Eₙ)/(μₙ² μₙ₊₁²)`.
-/

open Filter Topology
open scoped BigOperators

namespace RHTower
namespace XiShiftedCanonicalAdmission

noncomputable section

/-! ## Packet flux, mean, energy, clock -/

/-- Weighted packet flux through degree `n`: two copies of every lower diagonal coordinate and
one current coordinate. -/
def projectiveAdmissionPacketFlux (s : ℕ → ℝ) (n : ℕ) : ℝ :=
  2 * (∑ j ∈ Finset.range n, HTGeometry.monicOrthoAlpha s j) +
    HTGeometry.monicOrthoAlpha s n

/-- Weighted packet mean of total mass `2n + 1`. -/
def projectiveAdmissionPacketMean (s : ℕ → ℝ) (n : ℕ) : ℝ :=
  projectiveAdmissionPacketFlux s n / (2 * (n : ℝ) + 1)

/-- Centered square sum of the weighted packet. -/
def projectiveAdmissionPacketEnergy (s : ℕ → ℝ) (n : ℕ) : ℝ :=
  2 * (∑ j ∈ Finset.range n,
      (HTGeometry.monicOrthoAlpha s j - projectiveAdmissionPacketMean s n) ^ 2) +
    (HTGeometry.monicOrthoAlpha s n - projectiveAdmissionPacketMean s n) ^ 2

/-- Scalar projective clock of the packet. -/
def projectiveAdmissionScalarClock (y : ℝ) (s : ℕ → ℝ) (n : ℕ) : ℝ :=
  1 / projectiveAdmissionPacketMean s n - y

/-- Hyperbolic reset action: the energy increment in the reciprocal-mean metric. -/
def projectiveAdmissionHyperbolicResetAction (s : ℕ → ℝ) (n : ℕ) : ℝ :=
  (projectiveAdmissionPacketEnergy s (n + 1) - projectiveAdmissionPacketEnergy s n) /
    (projectiveAdmissionPacketMean s n ^ 2 * projectiveAdmissionPacketMean s (n + 1) ^ 2)

theorem projectiveAdmissionPacketFlux_succ (s : ℕ → ℝ) (n : ℕ) :
    projectiveAdmissionPacketFlux s (n + 1) =
      projectiveAdmissionPacketFlux s n + HTGeometry.monicOrthoAlpha s n +
        HTGeometry.monicOrthoAlpha s (n + 1) := by
  unfold projectiveAdmissionPacketFlux
  rw [Finset.sum_range_succ]
  ring

/-- Raw form of the packet energy: square sum minus squared flux over total mass. -/
theorem projectiveAdmissionPacketEnergy_eq (s : ℕ → ℝ) (n : ℕ) :
    projectiveAdmissionPacketEnergy s n =
      (2 * (∑ j ∈ Finset.range n, HTGeometry.monicOrthoAlpha s j ^ 2) +
        HTGeometry.monicOrthoAlpha s n ^ 2) -
      projectiveAdmissionPacketFlux s n ^ 2 / (2 * (n : ℝ) + 1) := by
  have hc : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  set μ := projectiveAdmissionPacketMean s n with hμ
  have hexpand : (∑ j ∈ Finset.range n,
      (HTGeometry.monicOrthoAlpha s j - μ) ^ 2) =
      (∑ j ∈ Finset.range n, HTGeometry.monicOrthoAlpha s j ^ 2) -
        2 * μ * (∑ j ∈ Finset.range n, HTGeometry.monicOrthoAlpha s j) +
        (n : ℝ) * μ ^ 2 := by
    simp_rw [sub_sq]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have hmid : (∑ x ∈ Finset.range n, 2 * HTGeometry.monicOrthoAlpha s x * μ) =
        2 * μ * ∑ x ∈ Finset.range n, HTGeometry.monicOrthoAlpha s x := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [hmid]
    simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hFμ : projectiveAdmissionPacketFlux s n = (2 * (n : ℝ) + 1) * μ := by
    rw [hμ, projectiveAdmissionPacketMean]
    field_simp
  rw [projectiveAdmissionPacketEnergy, hexpand, hFμ]
  have hμF : μ * (2 * (n : ℝ) + 1) =
      2 * (∑ j ∈ Finset.range n, HTGeometry.monicOrthoAlpha s j) +
        HTGeometry.monicOrthoAlpha s n := by
    rw [hμ, projectiveAdmissionPacketMean, projectiveAdmissionPacketFlux]
    field_simp
  field_simp
  nlinarith [hμF]

/-- Exact mean displacement under one degree renewal. -/
theorem projectiveAdmissionPacketMean_succ_sub (s : ℕ → ℝ) (n : ℕ) :
    projectiveAdmissionPacketMean s (n + 1) - projectiveAdmissionPacketMean s n =
      2 * ((HTGeometry.monicOrthoAlpha s n + HTGeometry.monicOrthoAlpha s (n + 1)) / 2 -
        projectiveAdmissionPacketMean s n) / (2 * (n : ℝ) + 3) := by
  have h1 : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  have h2 : (2 * (n : ℝ) + 3) ≠ 0 := by positivity
  unfold projectiveAdmissionPacketMean
  rw [projectiveAdmissionPacketFlux_succ]
  push_cast
  field_simp
  ring

/-- **Two-observation online-variance identity.**  The energy increment under one degree renewal
is an exact two-point dispersion plus a between-packet term. -/
theorem projectiveAdmissionPacketEnergy_succ_sub (s : ℕ → ℝ) (n : ℕ) :
    projectiveAdmissionPacketEnergy s (n + 1) - projectiveAdmissionPacketEnergy s n =
      (HTGeometry.monicOrthoAlpha s n - HTGeometry.monicOrthoAlpha s (n + 1)) ^ 2 / 2 +
        2 * (2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 3) *
          ((HTGeometry.monicOrthoAlpha s n + HTGeometry.monicOrthoAlpha s (n + 1)) / 2 -
            projectiveAdmissionPacketMean s n) ^ 2 := by
  have h1 : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  have h2 : (2 * (n : ℝ) + 3) ≠ 0 := by positivity
  rw [projectiveAdmissionPacketEnergy_eq, projectiveAdmissionPacketEnergy_eq,
    Finset.sum_range_succ, projectiveAdmissionPacketFlux_succ]
  unfold projectiveAdmissionPacketMean
  push_cast
  field_simp
  ring

/-- Euclidean variance controls Euclidean mean displacement. -/
theorem projectiveAdmissionPacketEnergy_succ_sub_ge (s : ℕ → ℝ) (n : ℕ) :
    (2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3) / 2 *
      (projectiveAdmissionPacketMean s (n + 1) - projectiveAdmissionPacketMean s n) ^ 2 ≤
    projectiveAdmissionPacketEnergy s (n + 1) - projectiveAdmissionPacketEnergy s n := by
  have h2 : (0 : ℝ) < 2 * (n : ℝ) + 3 := by positivity
  rw [projectiveAdmissionPacketEnergy_succ_sub, projectiveAdmissionPacketMean_succ_sub]
  set q := (HTGeometry.monicOrthoAlpha s n + HTGeometry.monicOrthoAlpha s (n + 1)) / 2 -
    projectiveAdmissionPacketMean s n with hq
  have hkey : (2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3) / 2 *
      (2 * q / (2 * (n : ℝ) + 3)) ^ 2 =
      2 * (2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 3) * q ^ 2 := by
    field_simp
    ring
  rw [hkey]
  have hdisp : 0 ≤ (HTGeometry.monicOrthoAlpha s n -
      HTGeometry.monicOrthoAlpha s (n + 1)) ^ 2 / 2 := by positivity
  linarith

/-- The clock step is the negative mean displacement in the reciprocal-mean metric. -/
theorem projectiveAdmissionScalarClock_succ_sub (y : ℝ) (s : ℕ → ℝ) (n : ℕ)
    (hn : projectiveAdmissionPacketMean s n ≠ 0)
    (hn1 : projectiveAdmissionPacketMean s (n + 1) ≠ 0) :
    projectiveAdmissionScalarClock y s (n + 1) - projectiveAdmissionScalarClock y s n =
      -((projectiveAdmissionPacketMean s (n + 1) - projectiveAdmissionPacketMean s n) /
        (projectiveAdmissionPacketMean s n * projectiveAdmissionPacketMean s (n + 1))) := by
  unfold projectiveAdmissionScalarClock
  field_simp
  ring

/-- **Reset barrier.**  On a positive-mean window, the negative clock reset is bounded by the
square-root of the Euclidean energy increment, divided by the product of adjacent means: the
reciprocal clock sees the singular metric `dμ/μ²`. -/
theorem projectiveAdmissionScalarClock_reset_barrier (y : ℝ) (s : ℕ → ℝ) (n : ℕ)
    (hn : 0 < projectiveAdmissionPacketMean s n)
    (hn1 : 0 < projectiveAdmissionPacketMean s (n + 1)) :
    -(projectiveAdmissionScalarClock y s (n + 1) - projectiveAdmissionScalarClock y s n) ≤
      Real.sqrt (2 * (projectiveAdmissionPacketEnergy s (n + 1) -
          projectiveAdmissionPacketEnergy s n) /
        ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3))) /
        (projectiveAdmissionPacketMean s n * projectiveAdmissionPacketMean s (n + 1)) := by
  set δ := projectiveAdmissionPacketMean s (n + 1) - projectiveAdmissionPacketMean s n with hδ
  rw [projectiveAdmissionScalarClock_succ_sub y s n hn.ne' hn1.ne', neg_neg, ← hδ]
  have hprod : 0 < projectiveAdmissionPacketMean s n * projectiveAdmissionPacketMean s (n + 1) :=
    mul_pos hn hn1
  gcongr
  have hc : (0 : ℝ) < (2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3) := by positivity
  have hE := projectiveAdmissionPacketEnergy_succ_sub_ge s n
  have hsq : δ ^ 2 ≤ 2 * (projectiveAdmissionPacketEnergy s (n + 1) -
      projectiveAdmissionPacketEnergy s n) / ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3)) := by
    have h2 : δ ^ 2 * ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3)) ≤
        2 * (projectiveAdmissionPacketEnergy s (n + 1) -
          projectiveAdmissionPacketEnergy s n) := by
      nlinarith [hE]
    calc δ ^ 2 = δ ^ 2 * ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3)) /
        ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3)) := by field_simp
      _ ≤ 2 * (projectiveAdmissionPacketEnergy s (n + 1) -
          projectiveAdmissionPacketEnergy s n) /
          ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3)) := by gcongr
  calc δ ≤ |δ| := le_abs_self δ
    _ = Real.sqrt (δ ^ 2) := (Real.sqrt_sq_eq_abs δ).symm
    _ ≤ _ := Real.sqrt_le_sqrt hsq

/-- The reset barrier in hyperbolic-action form: the negative clock reset is controlled by the
square-root of the hyperbolic reset action alone. -/
theorem projectiveAdmissionScalarClock_reset_barrier_action (y : ℝ) (s : ℕ → ℝ) (n : ℕ)
    (hn : 0 < projectiveAdmissionPacketMean s n)
    (hn1 : 0 < projectiveAdmissionPacketMean s (n + 1)) :
    -(projectiveAdmissionScalarClock y s (n + 1) - projectiveAdmissionScalarClock y s n) ≤
      Real.sqrt (2 * projectiveAdmissionHyperbolicResetAction s n /
        ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3))) := by
  refine le_trans (projectiveAdmissionScalarClock_reset_barrier y s n hn hn1) (le_of_eq ?_)
  have hprod : 0 < projectiveAdmissionPacketMean s n *
      projectiveAdmissionPacketMean s (n + 1) := mul_pos hn hn1
  have hE : 0 ≤ 2 * (projectiveAdmissionPacketEnergy s (n + 1) -
      projectiveAdmissionPacketEnergy s n) /
      ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3)) := by
    have hge := projectiveAdmissionPacketEnergy_succ_sub_ge s n
    have hsqnn : 0 ≤ (2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3) / 2 *
        (projectiveAdmissionPacketMean s (n + 1) - projectiveAdmissionPacketMean s n) ^ 2 := by
      positivity
    have hnum : 0 ≤ projectiveAdmissionPacketEnergy s (n + 1) -
        projectiveAdmissionPacketEnergy s n := le_trans hsqnn hge
    positivity
  rw [show Real.sqrt (2 * (projectiveAdmissionPacketEnergy s (n + 1) -
        projectiveAdmissionPacketEnergy s n) /
      ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3))) /
      (projectiveAdmissionPacketMean s n * projectiveAdmissionPacketMean s (n + 1)) =
      Real.sqrt (2 * (projectiveAdmissionPacketEnergy s (n + 1) -
        projectiveAdmissionPacketEnergy s n) /
      ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3)) /
      (projectiveAdmissionPacketMean s n * projectiveAdmissionPacketMean s (n + 1)) ^ 2) by
    rw [Real.sqrt_div hE, Real.sqrt_sq hprod.le]]
  congr 1
  rw [projectiveAdmissionHyperbolicResetAction]
  have hμ : projectiveAdmissionPacketMean s n ≠ 0 := hn.ne'
  have hμ1 : projectiveAdmissionPacketMean s (n + 1) ≠ 0 := hn1.ne'
  have hc1 : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  have hc3 : (2 * (n : ℝ) + 3) ≠ 0 := by positivity
  field_simp
  ring

/-! ## The bounded positive-Jacobi reset counterfamily -/

/-- Diagonal data of the reset counterfamily. -/
def resetCounterAlpha (a ε : ℝ) : ℕ → ℝ
  | 0 => a
  | 1 => ε / 4 - a
  | 2 => ε / 2
  | 3 => ε / 2
  | _ + 4 => 0

/-- Lower data of the reset counterfamily: every positive-index edge is strictly positive. -/
def resetCounterBeta (b ε : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => b
  | 2 => ε ^ 2
  | _ + 3 => 1

@[simp] theorem resetCounterAlpha_zero (a ε : ℝ) : resetCounterAlpha a ε 0 = a := rfl
@[simp] theorem resetCounterAlpha_one (a ε : ℝ) : resetCounterAlpha a ε 1 = ε / 4 - a := rfl
@[simp] theorem resetCounterAlpha_two (a ε : ℝ) : resetCounterAlpha a ε 2 = ε / 2 := rfl
@[simp] theorem resetCounterAlpha_three (a ε : ℝ) : resetCounterAlpha a ε 3 = ε / 2 := rfl
@[simp] theorem resetCounterBeta_one (b ε : ℝ) : resetCounterBeta b ε 1 = b := rfl
@[simp] theorem resetCounterBeta_two (b ε : ℝ) : resetCounterBeta b ε 2 = ε ^ 2 := rfl

theorem resetCounterBeta_pos {b ε : ℝ} (hb : 0 < b) (hε : 0 < ε) (n : ℕ) :
    0 < resetCounterBeta b ε (n + 1) := by
  match n with
  | 0 => exact hb
  | 1 => exact pow_pos hε 2
  | m + 2 => exact one_pos

/-- Moment sequence of the reset counterfamily, through the Favard realization. -/
def resetCounterMoment (a b ε : ℝ) : ℕ → ℝ :=
  HTGeometry.favardMoment (resetCounterAlpha a ε) (resetCounterBeta b ε)

theorem resetCounterMoment_positiveMomentForm (a : ℝ) {b ε : ℝ} (hb : 0 < b) (hε : 0 < ε) :
    HTGeometry.PositiveMomentForm (resetCounterMoment a b ε) :=
  HTGeometry.favard_positiveMomentForm _ _ (resetCounterBeta_pos hb hε)

theorem resetCounterMoment_formBelow (a : ℝ) {b ε : ℝ} (hb : 0 < b) (hε : 0 < ε) (N : ℕ) :
    HTGeometry.PositiveMomentFormBelow (resetCounterMoment a b ε) N :=
  ⟨fun p hp _ => (resetCounterMoment_positiveMomentForm a hb hε).pos_of_ne_zero p hp⟩

theorem resetCounterMoment_alpha (a : ℝ) {b ε : ℝ} (hb : 0 < b) (hε : 0 < ε) (n : ℕ) :
    HTGeometry.monicOrthoAlpha (resetCounterMoment a b ε) n = resetCounterAlpha a ε n :=
  HTGeometry.monicOrthoAlpha_favardMoment _ _ (resetCounterBeta_pos hb hε) n

theorem resetCounterMoment_beta (a : ℝ) {b ε : ℝ} (hb : 0 < b) (hε : 0 < ε) {n : ℕ}
    (hn : 0 < n) :
    HTGeometry.monicOrthoBeta (resetCounterMoment a b ε) n = resetCounterBeta b ε n :=
  HTGeometry.monicOrthoBeta_favardMoment _ _ (resetCounterBeta_pos hb hε) hn

theorem resetCounter_flux_two (a : ℝ) {b ε : ℝ} (hb : 0 < b) (hε : 0 < ε) :
    projectiveAdmissionPacketFlux (resetCounterMoment a b ε) 2 = ε := by
  unfold projectiveAdmissionPacketFlux
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  simp only [resetCounterMoment_alpha a hb hε, resetCounterAlpha_zero,
    resetCounterAlpha_one, resetCounterAlpha_two]
  ring

theorem resetCounter_flux_three (a : ℝ) {b ε : ℝ} (hb : 0 < b) (hε : 0 < ε) :
    projectiveAdmissionPacketFlux (resetCounterMoment a b ε) 3 = 2 * ε := by
  unfold projectiveAdmissionPacketFlux
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  simp only [resetCounterMoment_alpha a hb hε, resetCounterAlpha_zero,
    resetCounterAlpha_one, resetCounterAlpha_two, resetCounterAlpha_three]
  ring

/-- Exact reset of the counterfamily: the clock jumps by `-3/(2ε)` at the degree-two renewal. -/
theorem resetCounter_clock_step (a y : ℝ) {b ε : ℝ} (hb : 0 < b) (hε : 0 < ε) :
    projectiveAdmissionScalarClock y (resetCounterMoment a b ε) 3 -
      projectiveAdmissionScalarClock y (resetCounterMoment a b ε) 2 = -(3 / (2 * ε)) := by
  have hε' : ε ≠ 0 := hε.ne'
  unfold projectiveAdmissionScalarClock projectiveAdmissionPacketMean
  rw [resetCounter_flux_two a hb hε, resetCounter_flux_three a hb hε]
  push_cast
  field_simp
  ring

/-- Exact energy increment of the counterfamily. -/
theorem resetCounter_energy_step (a : ℝ) {b ε : ℝ} (hb : 0 < b) (hε : 0 < ε) :
    projectiveAdmissionPacketEnergy (resetCounterMoment a b ε) 3 -
      projectiveAdmissionPacketEnergy (resetCounterMoment a b ε) 2 = 9 * ε ^ 2 / 70 := by
  rw [projectiveAdmissionPacketEnergy_succ_sub (resetCounterMoment a b ε) 2]
  unfold projectiveAdmissionPacketMean
  rw [resetCounter_flux_two a hb hε]
  simp only [resetCounterMoment_alpha a hb hε, resetCounterAlpha_two, resetCounterAlpha_three]
  push_cast
  field_simp
  ring

/-- Exact total energy account of the counterfamily at degree two. -/
theorem resetCounter_energy_two (a : ℝ) {b ε : ℝ} (hb : 0 < b) (hε : 0 < ε) :
    projectiveAdmissionPacketEnergy (resetCounterMoment a b ε) 2 =
      2 * ((a - ε / 5) ^ 2 + (ε / 4 - a - ε / 5) ^ 2) + (ε / 2 - ε / 5) ^ 2 := by
  unfold projectiveAdmissionPacketEnergy projectiveAdmissionPacketMean
  rw [resetCounter_flux_two a hb hε, Finset.sum_range_succ, Finset.sum_range_one]
  simp only [resetCounterMoment_alpha a hb hε, resetCounterAlpha_zero,
    resetCounterAlpha_one, resetCounterAlpha_two]
  push_cast
  ring

/-- Exact Gauss-spread increment of the counterfamily. -/
theorem resetCounter_spread_step (a : ℝ) {b ε : ℝ} (hb : 0 < b) (hε : 0 < ε) :
    projectiveGaussRootSpread (resetCounterMoment a b ε) 3 -
      projectiveGaussRootSpread (resetCounterMoment a b ε) 2 = 67 * ε ^ 2 / 32 := by
  rw [projectiveGaussRootSpread_succ_sub (resetCounterMoment_formBelow a hb hε 4)
    (le_refl 2) (by omega : 2 + 1 < 4)]
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  rw [resetCounterMoment_beta a hb hε (by omega : 0 < 2)]
  simp only [resetCounterMoment_alpha a hb hε, resetCounterAlpha_zero,
    resetCounterAlpha_one, resetCounterAlpha_two, resetCounterBeta_two]
  push_cast
  ring

/-- Exact total Gauss-spread account of the counterfamily at degree two. -/
theorem resetCounter_spread_two (a : ℝ) {b ε : ℝ} (hb : 0 < b) (hε : 0 < ε) :
    projectiveGaussRootSpread (resetCounterMoment a b ε) 2 =
      a ^ 2 + (ε / 4 - a) ^ 2 - (ε / 4) ^ 2 / 2 + 2 * b := by
  rw [projectiveGaussRootSpread_eq_alphaDispersion_add_betaInventory
    (resetCounterMoment_formBelow a hb hε 4) (le_refl 2) (by omega : (2 : ℕ) < 4)]
  unfold projectiveJacobiLowerAlphaDispersion
  simp only [Finset.sum_range_succ, Finset.sum_range_one]
  rw [resetCounterMoment_beta a hb hε (by omega : 0 < 1)]
  simp only [resetCounterMoment_alpha a hb hε, resetCounterAlpha_zero,
    resetCounterAlpha_one, resetCounterBeta_one]
  rw [show HTGeometry.monicOrthoBeta (resetCounterMoment a b ε) 0 = 0 from rfl]
  push_cast
  ring

/-! ## Divergent reset with bounded accounts -/

/-- The negative clock reset diverges along the counterfamily. -/
theorem resetCounter_tendsto_reset_atTop (a : ℝ) {b : ℝ} (hb : 0 < b) (y : ℝ) :
    Tendsto (fun ε : ℝ =>
        -(projectiveAdmissionScalarClock y (resetCounterMoment a b ε) 3 -
          projectiveAdmissionScalarClock y (resetCounterMoment a b ε) 2))
      (nhdsWithin 0 (Set.Ioi 0)) atTop := by
  have hbase : Tendsto (fun ε : ℝ => 3 / (2 * ε)) (nhdsWithin 0 (Set.Ioi 0)) atTop := by
    have h1 : Tendsto (fun ε : ℝ => (3 / 2) * ε⁻¹) (nhdsWithin 0 (Set.Ioi 0)) atTop :=
      tendsto_inv_nhdsGT_zero.const_mul_atTop (by norm_num)
    exact h1.congr fun ε => by ring
  refine hbase.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [resetCounter_clock_step a y hb (Set.mem_Ioi.mp hε), neg_neg]

/-- The degree-two energy account converges along the counterfamily. -/
theorem resetCounter_tendsto_energy_two (a : ℝ) {b : ℝ} (hb : 0 < b) :
    Tendsto (fun ε : ℝ => projectiveAdmissionPacketEnergy (resetCounterMoment a b ε) 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (4 * a ^ 2)) := by
  have hcont : ContinuousAt (fun ε : ℝ =>
      2 * ((a - ε / 5) ^ 2 + (ε / 4 - a - ε / 5) ^ 2) + (ε / 2 - ε / 5) ^ 2) 0 := by
    fun_prop
  have hf := hcont.tendsto.mono_left nhdsWithin_le_nhds
  rw [show (2 * ((a - (0 : ℝ) / 5) ^ 2 + ((0 : ℝ) / 4 - a - (0 : ℝ) / 5) ^ 2) +
      ((0 : ℝ) / 2 - (0 : ℝ) / 5) ^ 2) = 4 * a ^ 2 by ring] at hf
  refine hf.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (resetCounter_energy_two a hb (Set.mem_Ioi.mp hε)).symm

/-- The degree-three energy account converges along the counterfamily. -/
theorem resetCounter_tendsto_energy_three (a : ℝ) {b : ℝ} (hb : 0 < b) :
    Tendsto (fun ε : ℝ => projectiveAdmissionPacketEnergy (resetCounterMoment a b ε) 3)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (4 * a ^ 2)) := by
  have h2 := resetCounter_tendsto_energy_two a hb
  have hq : Tendsto (fun ε : ℝ => 9 * ε ^ 2 / 70) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds 0) := by
    have hcont : ContinuousAt (fun ε : ℝ => 9 * ε ^ 2 / 70) 0 := by fun_prop
    have hf := hcont.tendsto.mono_left nhdsWithin_le_nhds
    rwa [show (9 * (0 : ℝ) ^ 2 / 70) = 0 by norm_num] at hf
  have hsum := h2.add hq
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hstep := resetCounter_energy_step a hb (Set.mem_Ioi.mp hε)
  linarith

/-- The degree-two Gauss-spread account converges along the counterfamily. -/
theorem resetCounter_tendsto_spread_two (a : ℝ) {b : ℝ} (hb : 0 < b) :
    Tendsto (fun ε : ℝ => projectiveGaussRootSpread (resetCounterMoment a b ε) 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (2 * a ^ 2 + 2 * b)) := by
  have hcont : ContinuousAt (fun ε : ℝ =>
      a ^ 2 + (ε / 4 - a) ^ 2 - (ε / 4) ^ 2 / 2 + 2 * b) 0 := by fun_prop
  have hf := hcont.tendsto.mono_left nhdsWithin_le_nhds
  rw [show (a ^ 2 + ((0 : ℝ) / 4 - a) ^ 2 - ((0 : ℝ) / 4) ^ 2 / 2 + 2 * b) =
      2 * a ^ 2 + 2 * b by ring] at hf
  refine hf.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (resetCounter_spread_two a hb (Set.mem_Ioi.mp hε)).symm

/-- The degree-three Gauss-spread account converges along the counterfamily. -/
theorem resetCounter_tendsto_spread_three (a : ℝ) {b : ℝ} (hb : 0 < b) :
    Tendsto (fun ε : ℝ => projectiveGaussRootSpread (resetCounterMoment a b ε) 3)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (2 * a ^ 2 + 2 * b)) := by
  have h2 := resetCounter_tendsto_spread_two a hb
  have hq : Tendsto (fun ε : ℝ => 67 * ε ^ 2 / 32) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds 0) := by
    have hcont : ContinuousAt (fun ε : ℝ => 67 * ε ^ 2 / 32) 0 := by fun_prop
    have hf := hcont.tendsto.mono_left nhdsWithin_le_nhds
    rwa [show (67 * (0 : ℝ) ^ 2 / 32) = 0 by norm_num] at hf
  have hsum := h2.add hq
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hstep := resetCounter_spread_step a hb (Set.mem_Ioi.mp hε)
  linarith

/-- **No locally bounded reset charge.**  Along the bounded positive-Jacobi counterfamily the
four ordinary variance and Gauss-spread accounts stay bounded while the negative clock reset
diverges, so no function of those accounts that is bounded on bounded boxes can dominate the
reset.  The denominator weight of the reset barrier is structurally necessary. -/
theorem resetCounter_no_locally_bounded_reset_charge (a : ℝ) {b : ℝ} (hb : 0 < b) :
    ¬ ∃ Φ : ℝ → ℝ → ℝ → ℝ → ℝ,
      (∀ R : ℝ, 0 < R → ∃ M : ℝ, ∀ e₂ e₃ g₂ g₃ : ℝ,
        |e₂| ≤ R → |e₃| ≤ R → |g₂| ≤ R → |g₃| ≤ R → Φ e₂ e₃ g₂ g₃ ≤ M) ∧
      (∀ y ε : ℝ, 0 < ε → ε ≤ 1 →
        -(projectiveAdmissionScalarClock y (resetCounterMoment a b ε) 3 -
            projectiveAdmissionScalarClock y (resetCounterMoment a b ε) 2) ≤
          Φ (projectiveAdmissionPacketEnergy (resetCounterMoment a b ε) 2)
            (projectiveAdmissionPacketEnergy (resetCounterMoment a b ε) 3)
            (projectiveGaussRootSpread (resetCounterMoment a b ε) 2)
            (projectiveGaussRootSpread (resetCounterMoment a b ε) 3)) := by
  rintro ⟨Φ, hloc, hbound⟩
  set R : ℝ := |4 * a ^ 2| + |2 * a ^ 2 + 2 * b| + 1 with hR
  have hRpos : 0 < R := by positivity
  obtain ⟨M, hM⟩ := hloc R hRpos
  have habs_bound : ∀ (f : ℝ → ℝ) (L : ℝ), |L| + 1 ≤ R →
      Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds L) →
      ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), |f ε| ≤ R := by
    intro f L hLR hf
    filter_upwards [hf (Metric.ball_mem_nhds L one_pos)] with ε hε
    rw [Metric.mem_ball, Real.dist_eq] at hε
    have htri : |f ε| ≤ |f ε - L| + |L| := by
      calc |f ε| = |(f ε - L) + L| := by rw [sub_add_cancel]
        _ ≤ |f ε - L| + |L| := abs_add_le _ _
    linarith
  have hL1 : |4 * a ^ 2| + 1 ≤ R := by
    rw [hR]
    have := abs_nonneg (2 * a ^ 2 + 2 * b)
    linarith
  have hL2 : |2 * a ^ 2 + 2 * b| + 1 ≤ R := by
    rw [hR]
    have := abs_nonneg (4 * a ^ 2)
    linarith
  have hbndE2 := habs_bound _ _ hL1 (resetCounter_tendsto_energy_two a hb)
  have hbndE3 := habs_bound _ _ hL1 (resetCounter_tendsto_energy_three a hb)
  have hbndG2 := habs_bound _ _ hL2 (resetCounter_tendsto_spread_two a hb)
  have hbndG3 := habs_bound _ _ hL2 (resetCounter_tendsto_spread_three a hb)
  have hreset := (resetCounter_tendsto_reset_atTop a hb 0).eventually_gt_atTop M
  have hmem : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ε ∈ Set.Ioi (0 : ℝ) :=
    self_mem_nhdsWithin
  have hlt1 : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ε < 1 :=
    (eventually_lt_nhds one_pos).filter_mono nhdsWithin_le_nhds
  obtain ⟨ε, hE2', hE3', hG2', hG3', hMlt, hmem', hε1⟩ :=
    (hbndE2.and (hbndE3.and (hbndG2.and (hbndG3.and
      (hreset.and (hmem.and hlt1)))))).exists
  have hεpos : 0 < ε := Set.mem_Ioi.mp hmem'
  have hb' := hbound 0 ε hεpos hε1.le
  have hΦ := hM _ _ _ _ hE2' hE3' hG2' hG3'
  linarith

end

end XiShiftedCanonicalAdmission
end RHTower
