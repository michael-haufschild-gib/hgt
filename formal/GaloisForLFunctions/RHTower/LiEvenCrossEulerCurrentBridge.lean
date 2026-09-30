import GaloisForLFunctions.RHTower.LiEvenCrossEulerJetOscillation
import GaloisForLFunctions.RHTower.LiEvenCrossCompletedAbelInteriorFirstZero
import GaloisForLFunctions.RHTower.XiShiftedHankelCassiniSourceJet

/-!
# The oscillating Euler jets belong to the actual first LI current

The zeroth completed-Abel current is a quadratic shifted-moment functional.
Its positive-mass logarithmic continuation is the literal Cassini log-mass current.
Evenization doubles its even jets, so the source coefficient oscillation theorem
excludes either eventual sign for these actual LI Euler jets.
-/

open Polynomial Complex

namespace RHTower

noncomputable section

theorem liEvenCrossSquareMassAdjacentCurrent_zero_eq_moments (v : ℝ) :
    liEvenCrossSquareMassAdjacentCurrent v 0 =
      2 * (xiShiftedReciprocalMoment v 0).re -
      6 * v * (xiShiftedReciprocalMoment v 1).re +
      4 * v ^ 2 * (xiShiftedReciprocalMoment v 2).re := by
  have hp : (liEvenCrossUnitFluxQuotient 0).comp (C v * X) =
      monomial 0 2 + monomial 1 (-6 * v) + monomial 2 (4 * v ^ 2) := by
    rw [liEvenCrossUnitFluxQuotient_eq_oddChebyshev]
    simp only [← Polynomial.C_mul_X_pow_eq_monomial]
    norm_num [Polynomial.Chebyshev.U_one, liEvenCrossUnitAffine,
      Polynomial.mul_comp, Polynomial.sub_comp, Polynomial.C_comp]
    simp only [map_ofNat]
    ring
  rw [liEvenCrossSquareMassAdjacentCurrent, hp]
  simp only [HTGeometry.momentFunctional_add, HTGeometry.momentFunctional_monomial]
  ring

theorem liEvenCrossCassiniLogMassCurrent_re_eq_first_current
    {v : ℝ} (hv : 0 < v) :
    (liEvenCrossCassiniLogMassCurrent v).re =
      v * liEvenCrossSquareMassAdjacentCurrent v 0 := by
  have h0 := congrArg Complex.re
    (neg_two_mul_cassiniLogDeriv_jet_one_sub_eq_xiShiftedMoment hv 0)
  have h1 := congrArg Complex.re
    (neg_two_mul_cassiniLogDeriv_jet_one_sub_eq_xiShiftedMoment hv 1)
  have h2 := congrArg Complex.re
    (neg_two_mul_cassiniLogDeriv_jet_one_sub_eq_xiShiftedMoment hv 2)
  norm_num [iteratedDeriv_succ, iteratedDeriv_one, Complex.mul_re] at h0 h1 h2
  rw [liEvenCrossSquareMassAdjacentCurrent_zero_eq_moments]
  norm_num [liEvenCrossCassiniLogMassCurrent, Complex.mul_re, ← Complex.ofReal_pow]
  linear_combination 2 * v * h0 - 6 * v ^ 2 * h1 + 2 * v ^ 3 * h2

theorem liEvenCrossCassiniLogMassCurrent_eq_first_current
    {v : ℝ} (hv : 0 < v) :
    liEvenCrossCassiniLogMassCurrent v =
      ((v * liEvenCrossSquareMassAdjacentCurrent v 0 : ℝ) : ℂ) := by
  have hc := liEvenCrossCassiniLogMassCurrent_conj (v : ℂ)
  simp only [Complex.conj_ofReal] at hc
  have hi := congrArg Complex.im hc
  simp only [Complex.conj_im] at hi
  apply Complex.ext
  · exact liEvenCrossCassiniLogMassCurrent_re_eq_first_current hv
  · simp only [Complex.ofReal_im]
    linarith

/-- Complex logarithmic-mass continuation of the actual first current. -/
def liEvenCrossLogMassFirstCurrent (v : ℝ) (t : ℂ) : ℂ :=
  liEvenCrossCassiniLogMassCurrent ((v : ℂ) * Complex.exp t)

theorem liEvenCrossLogMassFirstCurrent_real {v : ℝ} (hv : 0 < v) (t : ℝ) :
    liEvenCrossLogMassFirstCurrent v t =
      ((v * Real.exp t *
        liEvenCrossSquareMassAdjacentCurrent (v * Real.exp t) 0 : ℝ) : ℂ) := by
  unfold liEvenCrossLogMassFirstCurrent
  rw [show (v : ℂ) * Complex.exp (t : ℂ) = ((v * Real.exp t : ℝ) : ℂ) by
    simp [Complex.ofReal_exp]]
  exact liEvenCrossCassiniLogMassCurrent_eq_first_current
    (mul_pos hv (Real.exp_pos t))

/-- The even shifted Euler jet, read in logarithmic mass at the specified positive mass. -/
def liEvenCrossFirstCurrentEvenEulerJet (v : ℝ) (k : ℕ) : ℝ :=
  (iteratedDeriv (2 * k) (liEvenCrossLogMassFirstCurrent v) 0).re

theorem liEvenCrossEvenLogMassGerm_even_jet_eq_twice_first_current
    {v : ℝ} (hv : 0 < v) (k : ℕ) :
    (iteratedDeriv (2 * k) (liEvenCrossCassiniEvenLogMassGerm v) 0).re =
      2 * liEvenCrossFirstCurrentEvenEulerJet v k := by
  have hsource := analyticAt_liEvenCrossCassiniLogMassCurrent_of_source_ne_zero
    (xiSquaredSeamCassiniSource_one_sub_posMass_ne_zero hv)
  have hf : AnalyticAt ℂ (liEvenCrossLogMassFirstCurrent v) 0 := by
    exact hsource.comp_of_eq (f := fun t : ℂ => (v : ℂ) * Complex.exp t) (x := 0)
      (by fun_prop) (by simp)
  have hn : AnalyticAt ℂ (fun t : ℂ => liEvenCrossLogMassFirstCurrent v (-t)) 0 := by
    exact hf.comp_of_eq
      (by fun_prop : AnalyticAt ℂ (fun t : ℂ => -t) 0) (by simp)
  have hsplit : liEvenCrossCassiniEvenLogMassGerm v =
      liEvenCrossLogMassFirstCurrent v +
        (fun t : ℂ => liEvenCrossLogMassFirstCurrent v (-t)) := rfl
  rw [hsplit, iteratedDeriv_add hf.contDiffAt hn.contDiffAt,
    iteratedDeriv_comp_neg, neg_zero, smul_eq_mul]
  simp [liEvenCrossFirstCurrentEvenEulerJet, two_mul]

theorem liEvenCrossEulerJetTaylorCoeff_eq_first_current_jet
    (v : LiEvenCrossPositiveMass) (k : ℕ) :
    liEvenCrossEulerJetTaylorCoeff v (2 * k) =
      2 * liEvenCrossFirstCurrentEvenEulerJet v.val k / ((2 * k).factorial : ℝ) := by
  rw [liEvenCrossEulerJetTaylorCoeff_eq_real_jet,
    liEvenCrossEvenLogMassGerm_even_jet_eq_twice_first_current v.property]

/-- **Actual LI Euler-jet oscillation:** every tail contains a jet of either strict sign. -/
theorem liEvenCrossFirstCurrentEvenEulerJet_cofinal_both_signs
    (v : LiEvenCrossPositiveMass) :
    (∀ N : ℕ, ∃ k, N ≤ k ∧ liEvenCrossFirstCurrentEvenEulerJet v.val k < 0) ∧
      (∀ N : ℕ, ∃ k, N ≤ k ∧ 0 < liEvenCrossFirstCurrentEvenEulerJet v.val k) := by
  have hs := liEvenCrossEulerJet_real_cofinal_both_signs v
  constructor
  · intro N
    obtain ⟨k, hNk, hk⟩ := hs.1 N
    refine ⟨k, hNk, ?_⟩
    rw [liEvenCrossEvenLogMassGerm_even_jet_eq_twice_first_current v.property] at hk
    linarith
  · intro N
    obtain ⟨k, hNk, hk⟩ := hs.2 N
    refine ⟨k, hNk, ?_⟩
    rw [liEvenCrossEvenLogMassGerm_even_jet_eq_twice_first_current v.property] at hk
    linarith

theorem liEvenCrossFirstCurrentEvenEulerJet_not_all_nonneg
    (v : LiEvenCrossPositiveMass) :
    ¬ ∀ k, 0 ≤ liEvenCrossFirstCurrentEvenEulerJet v.val k := by
  intro h
  obtain ⟨k, _, hk⟩ := (liEvenCrossFirstCurrentEvenEulerJet_cofinal_both_signs v).1 0
  exact (not_lt_of_ge (h k)) hk

theorem liEvenCrossFirstCurrentEvenEulerJet_not_all_nonpos
    (v : LiEvenCrossPositiveMass) :
    ¬ ∀ k, liEvenCrossFirstCurrentEvenEulerJet v.val k ≤ 0 := by
  intro h
  obtain ⟨k, _, hk⟩ := (liEvenCrossFirstCurrentEvenEulerJet_cofinal_both_signs v).2 0
  exact (not_lt_of_ge (h k)) hk

end

end RHTower
