import GaloisForLFunctions.RHTower.ThetaCuspFullReflectionEighthBoundaryKreinReduction
import GaloisForLFunctions.HTGeometry.ShiftedEulerTangentFiltration
import GaloisForLFunctions.RHTower.EnvelopeJetAgreement

/-!
# Ninth-jet torsor at a singular reflected rank-three face

The current reflected moments through order eight do not orient their own first crossing, even
inside the class of entire functions that are strictly positive on the real axis.  The positive
family

`cosh(x) * exp(c x^(9 : ℕ) / 9!)`

has one common jet through order eight.  Its ninth jet is `c`, while the common reflected Hankel
face is singular with strict leading rank-two minor.  The canonical boundary crossing is exactly
`32c`.  It therefore realizes every crossing value without changing the current face.

This kills every S6F/TCD boundary-flux proposal that derives orientation from positivity,
analyticity, or reflected moments only through order eight.  The positive survivor is sharp:
theta-specific ninth-jet dynamics, equivalently the exact projective drift, are indispensable.
-/

open Real

namespace HilbertMetric

noncomputable section

/-- Fixed lower jet with one free ninth coordinate. -/
def reflectedBoundaryNinthJet (c : ℝ) : ℕ → ℝ
  | 0 => 1
  | 2 => 1
  | 4 => 1
  | 6 => 1
  | 8 => 1
  | 9 => c
  | _ => 0

/-- The five current reflected even moments of the ninth-jet family. -/
def reflectedBoundaryNinthJetMoment (c : ℝ) : Fin 5 → ℝ :=
  let f := reflectedBoundaryNinthJet c
  ![f 0 ^ (2 : ℕ),
    reflectedProductSecondJet (f 0) (f 1) (f 2),
    reflectedProductFourthJet (f 0) (f 1) (f 2) (f 3) (f 4),
    reflectedProductSixthJet (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6),
    reflectedProductEighthJet
      (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7) (f 8)]

/-- The five center-shift directions of the ninth-jet family. -/
def reflectedBoundaryNinthJetShift (c : ℝ) : Fin 5 → ℝ :=
  let f := reflectedBoundaryNinthJet c
  ![reflectedProductZeroJetShift (f 0) (f 1),
    reflectedProductSecondJetShift (f 0) (f 1) (f 2) (f 3),
    reflectedProductFourthJetShift (f 0) (f 1) (f 2) (f 3) (f 4) (f 5),
    reflectedProductSixthJetShift
      (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7),
    reflectedProductEighthJetShift
      (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7) (f 8) (f 9)]

/-- The lower reflected face is independent of the ninth coordinate. -/
theorem reflectedBoundaryNinthJetMoment_eq (c : ℝ) :
    reflectedBoundaryNinthJetMoment c = ![1, 2, 8, 32, 128] := by
  funext i
  fin_cases i <;>
    norm_num [reflectedBoundaryNinthJetMoment, reflectedBoundaryNinthJet,
      reflectedProductSecondJet, reflectedProductFourthJet,
      reflectedProductSixthJet, reflectedProductEighthJet]

/-- Only the top center-shift direction sees the free ninth coordinate. -/
theorem reflectedBoundaryNinthJetShift_eq (c : ℝ) :
    reflectedBoundaryNinthJetShift c = ![0, 0, 0, 0, 2 * c] := by
  funext i
  fin_cases i <;>
    norm_num [reflectedBoundaryNinthJetShift, reflectedBoundaryNinthJet,
      reflectedProductZeroJetShift, reflectedProductSecondJetShift,
      reflectedProductFourthJetShift, reflectedProductSixthJetShift,
      reflectedProductEighthJetShift]

/-- Every member lies on the same singular rank-three Hankel face. -/
theorem reflectedBoundaryNinthJet_det_zero (c : ℝ) :
    let p := reflectedBoundaryNinthJetMoment c
    signedEvenHankelThreeDet (p 0) (p 1) (p 2) (p 3) (p 4) = 0 := by
  rw [reflectedBoundaryNinthJetMoment_eq]
  simp
  norm_num [signedEvenHankelThreeDet]

/-- The common singular face has strict leading rank-two minor `4`. -/
theorem reflectedBoundaryNinthJet_strictHead (c : ℝ) :
    let p := reflectedBoundaryNinthJetMoment c
    p 0 * p 2 - p 1 ^ (2 : ℕ) = 4 := by
  rw [reflectedBoundaryNinthJetMoment_eq]
  simp
  norm_num

/-- Canonical boundary crossing of the family. -/
def reflectedBoundaryNinthJetCrossing (c : ℝ) : ℝ :=
  let p := reflectedBoundaryNinthJetMoment c
  let q := reflectedBoundaryNinthJetShift c
  signedEvenHankelThreeBoundaryCrossing
    (p 0) (p 1) (p 2) (p 3) (q 0) (q 1) (q 2) (q 3) (q 4)

/-- **Ninth-jet torsor law.** Crossing is exactly `32` times the free ninth jet. -/
theorem reflectedBoundaryNinthJetCrossing_eq (c : ℝ) :
    reflectedBoundaryNinthJetCrossing c = 32 * c := by
  rw [reflectedBoundaryNinthJetCrossing,
    reflectedBoundaryNinthJetMoment_eq, reflectedBoundaryNinthJetShift_eq]
  simp
  norm_num [signedEvenHankelThreeBoundaryCrossing]
  ring

/-- The literal center-shift determinant variation is exactly `8c`. -/
theorem reflectedBoundaryNinthJetShiftVariation_eq (c : ℝ) :
    signedEvenHankelThreeShiftVariation (reflectedBoundaryNinthJet c) = 8 * c := by
  norm_num [signedEvenHankelThreeShiftVariation,
    signedEvenHankelThreeFirstVariation, reflectedBoundaryNinthJet,
    reflectedProductZeroJetShift, reflectedProductSecondJetShift,
    reflectedProductFourthJetShift, reflectedProductSixthJetShift,
    reflectedProductEighthJetShift, reflectedProductSecondJet,
    reflectedProductFourthJet, reflectedProductSixthJet,
    reflectedProductEighthJet]
  ring

/-- Current jets through order eight are literally fixed across the family. -/
theorem reflectedBoundaryNinthJet_eq_of_lt_nine
    (c d : ℝ) {n : ℕ} (hn : n < 9) :
    reflectedBoundaryNinthJet c n = reflectedBoundaryNinthJet d n := by
  interval_cases n <;> rfl

/-- Every real crossing value occurs on the same strict-head singular reflected face. -/
theorem exists_reflectedBoundaryNinthJetCrossing_eq (r : ℝ) :
    ∃ c : ℝ, reflectedBoundaryNinthJetCrossing c = r := by
  refine ⟨r / 32, ?_⟩
  rw [reflectedBoundaryNinthJetCrossing_eq]
  ring

/-! ## Positive entire realization -/

/-- Entire positive-real-axis realization of the ninth-jet torsor. -/
def reflectedBoundaryNinthEntireGauge (c z : ℂ) : ℂ :=
  Complex.cosh z * Complex.exp (c / 362880 * z ^ (9 : ℕ))

/-- Complex version of the prescribed jet. -/
def reflectedBoundaryNinthJetC (c : ℂ) : ℕ → ℂ
  | 0 => 1
  | 2 => 1
  | 4 => 1
  | 6 => 1
  | 8 => 1
  | 9 => c
  | _ => 0

/-- The entire gauge has the same jets as `cosh` through order eight. -/
theorem reflectedBoundaryNinthEntireGauge_lower
    (c : ℂ) {n : ℕ} (hn : n ≤ 8) :
    iteratedDeriv n (reflectedBoundaryNinthEntireGauge c) 0 =
      iteratedDeriv n Complex.cosh 0 := by
  have hgauge : ∀ j ≤ 8,
      iteratedDeriv j (fun z : ℂ => Complex.exp (c / 362880 * z ^ (9 : ℕ))) 0 =
        iteratedDeriv j (fun _z : ℂ => Complex.exp 0) 0 := by
    intro j hj
    apply GaloisForLFunctions.HTGeometry.iteratedDeriv_exp_congr_of_flat
      (L₁ := fun z : ℂ => c / 362880 * z ^ (9 : ℕ))
      (L₂ := fun _z : ℂ => 0)
      (k := 8) (W := fun _z : ℂ => c / 362880)
    · intro z
      fun_prop
    · intro z
      fun_prop
    · fun_prop
    · filter_upwards
      intro z
      ring
    · exact hj
  have hmul := RHTower.iteratedDeriv_mul_congr
    (A := Complex.cosh)
    (f := fun z : ℂ => Complex.exp (c / 362880 * z ^ (9 : ℕ)))
    (g := fun _z : ℂ => Complex.exp 0)
    (w := 0) (N := 8) (by fun_prop) (by fun_prop) (by fun_prop) hgauge n hn
  have hleft :
      Complex.cosh * (fun z : ℂ => Complex.exp (c / 362880 * z ^ (9 : ℕ))) =
        reflectedBoundaryNinthEntireGauge c := by
    funext z
    rfl
  have hright : Complex.cosh * (fun _z : ℂ => Complex.exp 0) = Complex.cosh := by
    funext z
    simp
  rw [hleft, hright] at hmul
  exact hmul

/-- The first escaping entire jet is exactly the parameter `c`. -/
theorem reflectedBoundaryNinthEntireGauge_top (c : ℂ) :
    iteratedDeriv 9 (reflectedBoundaryNinthEntireGauge c) 0 = c := by
  obtain ⟨psi, hpsiDiff, hpsiFactor, hpsiZero⟩ :=
    GaloisForLFunctions.HTGeometry.exists_mul_of_apply_eq_zero
      (f := fun w : ℂ => Complex.exp w - 1) (by fun_prop) (by simp)
  have hpsiZero' : psi 0 = 1 := by
    rw [hpsiZero]
    convert ((Complex.hasDerivAt_exp 0).sub_const 1).deriv using 1
    simp
  let a : ℂ := c / 362880
  let W : ℂ → ℂ := fun z => a * Complex.cosh z * psi (a * z ^ (9 : ℕ))
  have hW : AnalyticAt ℂ W 0 := by
    dsimp only [W]
    exact (analyticAt_const.mul (by fun_prop)).mul
      ((GaloisForLFunctions.HTGeometry.analyticAt_of_differentiable_univariate hpsiDiff _).comp
        (analyticAt_const.mul (analyticAt_id.pow 9)))
  have hdiff :
      (fun z => reflectedBoundaryNinthEntireGauge c z - Complex.cosh z) =
        fun z => z ^ (9 : ℕ) * W z := by
    funext z
    dsimp only [reflectedBoundaryNinthEntireGauge, W, a]
    calc
      Complex.cosh z * Complex.exp (c / 362880 * z ^ (9 : ℕ)) - Complex.cosh z =
          Complex.cosh z * (Complex.exp (c / 362880 * z ^ (9 : ℕ)) - 1) := by ring
      _ = Complex.cosh z *
          ((c / 362880 * z ^ (9 : ℕ)) * psi (c / 362880 * z ^ (9 : ℕ))) := by
        rw [hpsiFactor (c / 362880 * z ^ (9 : ℕ))]
      _ = z ^ (9 : ℕ) * (c / 362880 * Complex.cosh z * psi (c / 362880 * z ^ (9 : ℕ))) := by
        ring
  have htop := GaloisForLFunctions.HTGeometry.iteratedDeriv_pow_mul (m := 9) hW
  rw [← hdiff] at htop
  have hF : ∀ z : ℂ, AnalyticAt ℂ (reflectedBoundaryNinthEntireGauge c) z := by
    intro z
    change AnalyticAt ℂ
      (fun w : ℂ => Complex.cosh w * Complex.exp (c / 362880 * w ^ (9 : ℕ))) z
    fun_prop
  have hC : ∀ z : ℂ, AnalyticAt ℂ Complex.cosh z := by
    intro z
    fun_prop
  have hsub := GaloisForLFunctions.HTGeometry.iteratedDeriv_fun_sub 9 hF hC 0
  rw [hsub] at htop
  have hcosh : iteratedDeriv 9 Complex.cosh 0 = 0 := by
    have h := Complex.iteratedDeriv_odd_cosh 4
    convert h using 1
    norm_num
  rw [hcosh, sub_zero] at htop
  norm_num [W, a, hpsiZero'] at htop
  calc
    iteratedDeriv 9 (reflectedBoundaryNinthEntireGauge c) 0 =
        362880 * (c / 362880) := htop
    _ = c := by ring

/-- Complete depth-nine jet of the entire family. -/
theorem reflectedBoundaryNinthEntireGauge_jet
    (c : ℂ) {n : ℕ} (hn : n ≤ 9) :
    iteratedDeriv n (reflectedBoundaryNinthEntireGauge c) 0 =
      reflectedBoundaryNinthJetC c n := by
  interval_cases n
  all_goals first
    | exact reflectedBoundaryNinthEntireGauge_top c
    | rw [reflectedBoundaryNinthEntireGauge_lower c (by omega)]
      simp [reflectedBoundaryNinthJetC]

/-- Complex and real jet ledgers agree on the realized depth-nine section. -/
theorem reflectedBoundaryNinthJetC_ofReal
    (c : ℝ) {n : ℕ} (hn : n ≤ 9) :
    reflectedBoundaryNinthJetC (c : ℂ) n = (reflectedBoundaryNinthJet c n : ℂ) := by
  interval_cases n <;> rfl

/-- Positive real restriction of the entire gauge. -/
def reflectedBoundaryNinthPositiveGauge (c x : ℝ) : ℝ :=
  Real.cosh x * Real.exp (c / 362880 * x ^ (9 : ℕ))

theorem reflectedBoundaryNinthPositiveGauge_pos (c x : ℝ) :
    0 < reflectedBoundaryNinthPositiveGauge c x := by
  exact mul_pos (Real.cosh_pos x) (Real.exp_pos _)

/-- The complex entire family restricts exactly to the positive real family. -/
theorem reflectedBoundaryNinthEntireGauge_ofReal (c x : ℝ) :
    reflectedBoundaryNinthEntireGauge (c : ℂ) (x : ℂ) =
      (reflectedBoundaryNinthPositiveGauge c x : ℂ) := by
  simp [reflectedBoundaryNinthEntireGauge, reflectedBoundaryNinthPositiveGauge]

/-- Every crossing value has a strictly positive entire realization with the displayed jet. -/
theorem exists_positiveEntire_reflectedBoundaryNinthJetCrossing_eq (r : ℝ) :
    ∃ c : ℝ,
      (∀ x : ℝ, 0 < reflectedBoundaryNinthPositiveGauge c x) ∧
      (∀ n : ℕ, n ≤ 9 →
        iteratedDeriv n (reflectedBoundaryNinthEntireGauge (c : ℂ)) 0 =
          (reflectedBoundaryNinthJet c n : ℂ)) ∧
      reflectedBoundaryNinthJetCrossing c = r := by
  refine ⟨r / 32, reflectedBoundaryNinthPositiveGauge_pos _, ?_, ?_⟩
  · intro n hn
    rw [reflectedBoundaryNinthEntireGauge_jet _ hn,
      reflectedBoundaryNinthJetC_ofReal _ hn]
  · rw [reflectedBoundaryNinthJetCrossing_eq]
    ring

/-- Lower jets retained by the proposed finite spectral-flux closure. -/
def reflectedBoundaryNinthLowerJet (c : ℝ) : Fin 9 → ℝ :=
  fun n => reflectedBoundaryNinthJet c n

theorem reflectedBoundaryNinthLowerJet_eq (c d : ℝ) :
    reflectedBoundaryNinthLowerJet c = reflectedBoundaryNinthLowerJet d := by
  funext n
  exact reflectedBoundaryNinthJet_eq_of_lt_nine c d n.isLt

/-- **Finite-jet spectral-flux route kill.** No property of the positive entire source's current
depth-eight jet can determine the sign of its canonical rank-three boundary crossing. -/
theorem reflectedBoundaryNinthJetCrossingSign_not_determinedBy_lowerJet :
    ¬ ∃ phi : (Fin 9 → ℝ) → Prop, ∀ c : ℝ,
      (0 < reflectedBoundaryNinthJetCrossing c) ↔
        phi (reflectedBoundaryNinthLowerJet c) := by
  rintro ⟨phi, hphi⟩
  have hpos : 0 < reflectedBoundaryNinthJetCrossing 1 := by
    rw [reflectedBoundaryNinthJetCrossing_eq]
    norm_num
  have hneg : ¬ 0 < reflectedBoundaryNinthJetCrossing (-1) := by
    rw [reflectedBoundaryNinthJetCrossing_eq]
    norm_num
  have hs := reflectedBoundaryNinthLowerJet_eq (1 : ℝ) (-1)
  exact hneg ((hphi (-1)).2 (hs ▸ (hphi 1).1 hpos))

end

end HilbertMetric
