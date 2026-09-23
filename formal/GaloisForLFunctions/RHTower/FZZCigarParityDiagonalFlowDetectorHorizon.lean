import GaloisForLFunctions.RHTower.FZZCigarParityDiagonalRieszStabilization

/-!
# Finite reflection-detector horizon for stabilized FZZ diagonal flow

The source-gap stabilized FZZ generator has a rank-one polynomial law.  Its exact exponential flow
pulls unit diagonal energy back to the Hermitian coefficient parabola `(k^(2 : ℕ),-k,0,1)`.  This module
proves that the parabola lies in the sharp reflection-detector cone exactly through one finite,
source-defined time.  The lightlike boundary remains separating; every later time is phase-blind.
-/

open Complex

namespace RHTower

noncomputable section

/-- Real shear accumulated by the stabilized diagonal source flow. -/
def fzzCigarParityDilatedSecondDiagonalFlowShear
    (beta t : ℝ) : ℝ :=
  (fzzKreinQAt beta / fzzKreinRAt beta) *
    (Real.exp (fzzKreinPAt beta * t) - 1)

/-- Exact exponential flow of the source-gap stabilized rank-one generator. -/
def fzzCigarParityDilatedSecondDiagonalStabilizedFlow
    (beta t : ℝ) (u : ℂ × ℂ) : ℂ × ℂ :=
  (((Real.exp (fzzKreinPAt beta * t) : ℝ) : ℂ) * u.1,
    u.2 - (fzzCigarParityDilatedSecondDiagonalFlowShear beta t : ℂ) * u.1)

theorem fzzCigarParityDilatedSecondDiagonalFlowShear_zero (beta : ℝ) :
    fzzCigarParityDilatedSecondDiagonalFlowShear beta 0 = 0 := by
  simp [fzzCigarParityDilatedSecondDiagonalFlowShear]

theorem fzzCigarParityDilatedSecondDiagonalStabilizedFlow_zero
    (beta : ℝ) (u : ℂ × ℂ) :
    fzzCigarParityDilatedSecondDiagonalStabilizedFlow beta 0 u = u := by
  rcases u with ⟨u₁, u₂⟩
  simp [fzzCigarParityDilatedSecondDiagonalStabilizedFlow,
    fzzCigarParityDilatedSecondDiagonalFlowShear]

theorem fzzCigarParityDilatedSecondDiagonalFlowShear_add
    (beta s t : ℝ) :
    fzzCigarParityDilatedSecondDiagonalFlowShear beta (s + t) =
      fzzCigarParityDilatedSecondDiagonalFlowShear beta t +
        Real.exp (fzzKreinPAt beta * t) *
          fzzCigarParityDilatedSecondDiagonalFlowShear beta s := by
  rw [fzzCigarParityDilatedSecondDiagonalFlowShear,
    fzzCigarParityDilatedSecondDiagonalFlowShear,
    fzzCigarParityDilatedSecondDiagonalFlowShear]
  rw [show fzzKreinPAt beta * (s + t) =
    fzzKreinPAt beta * s + fzzKreinPAt beta * t by ring,
    Real.exp_add]
  ring

theorem fzzCigarParityDilatedSecondDiagonalStabilizedFlow_add
    (beta s t : ℝ) (u : ℂ × ℂ) :
    fzzCigarParityDilatedSecondDiagonalStabilizedFlow beta (s + t) u =
      fzzCigarParityDilatedSecondDiagonalStabilizedFlow beta s
        (fzzCigarParityDilatedSecondDiagonalStabilizedFlow beta t u) := by
  rcases u with ⟨u₁, u₂⟩
  rw [fzzCigarParityDilatedSecondDiagonalStabilizedFlow,
    fzzCigarParityDilatedSecondDiagonalStabilizedFlow,
    fzzCigarParityDilatedSecondDiagonalStabilizedFlow]
  rw [show fzzKreinPAt beta * (s + t) =
    fzzKreinPAt beta * s + fzzKreinPAt beta * t by ring,
    Real.exp_add,
    fzzCigarParityDilatedSecondDiagonalFlowShear_add]
  apply Prod.ext <;> simp <;> ring

/-- Closed polynomial functional calculus for the stabilized generator. -/
theorem fzzCigarParityDilatedSecondDiagonalStabilizedFlow_eq_generator
    {beta : ℝ} (hbeta : 0 < beta) (t : ℝ) (u : ℂ × ℂ) :
    fzzCigarParityDilatedSecondDiagonalStabilizedFlow beta t u =
      u +
        (((Real.exp (fzzKreinPAt beta * t) - 1) /
          fzzKreinPAt beta : ℝ) : ℂ) •
          fzzCigarParityDilatedSecondDiagonalPerturbedKreinOperator beta
            (fzzCigarParityDilatedSecondDiagonalStabilizingCoupling beta) u := by
  rw [fzzCigarParityDilatedSecondDiagonalPerturbedKreinOperator_stabilizingCoupling hbeta]
  rcases u with ⟨u₁, u₂⟩
  have hP : (fzzKreinPAt beta : ℂ) ≠ 0 := by
    exact_mod_cast (fzzKreinPAt_pos hbeta).ne'
  have hR : (fzzKreinRAt beta : ℂ) ≠ 0 := by
    exact_mod_cast (fzzKreinRAt_pos hbeta).ne'
  apply Prod.ext <;>
    simp [fzzCigarParityDilatedSecondDiagonalStabilizedFlow,
      fzzCigarParityDilatedSecondDiagonalFlowShear, smul_eq_mul] <;>
    field_simp [hP, hR] <;> ring

/-- Pullback of unit diagonal energy along the stabilized flow. -/
theorem fzzCigarParityDilatedSecondDiagonalStabilizedFlow_pullback
    (beta t : ℝ) (u : ℂ × ℂ) :
    fzzCigarParityHermitianQuadraticObservable 0 0 0 1
        (fzzCigarParityDilatedSecondDiagonalStabilizedFlow beta t u) =
      fzzCigarParityHermitianQuadraticObservable
        (fzzCigarParityDilatedSecondDiagonalFlowShear beta t ^ (2 : ℕ))
        (-fzzCigarParityDilatedSecondDiagonalFlowShear beta t) 0 1 u := by
  rcases u with ⟨u₁, u₂⟩
  simp [fzzCigarParityDilatedSecondDiagonalStabilizedFlow,
    fzzCigarParityHermitianQuadraticObservable, Complex.conj_ofReal,
    star_sub, star_mul]
  ring

/-- Universal reciprocal-radius separation by the transported diagonal energy. -/
def FZZCigarParityDilatedSecondDiagonalFlowUniversallySeparating
    (beta t : ℝ) : Prop :=
  FZZCigarParityHermitianUniversalRadialReflectionSeparating
    (fzzCigarParityDilatedSecondDiagonalFlowShear beta t ^ (2 : ℕ))
    (-fzzCigarParityDilatedSecondDiagonalFlowShear beta t) 0 1

theorem fzzCigarParityDilatedSecondDiagonalFlowUniversallySeparating_iff
    (beta t : ℝ) :
    FZZCigarParityDilatedSecondDiagonalFlowUniversallySeparating beta t ↔
      fzzCigarParityDilatedSecondDiagonalFlowShear beta t ^ (2 : ℕ) ≤ 1 := by
  rw [FZZCigarParityDilatedSecondDiagonalFlowUniversallySeparating,
    fzzCigarParityHermitianUniversalRadialReflectionSeparating_iff]
  simp

/-- Finite time at which the transported reporter reaches the lightlike detector boundary. -/
def fzzCigarParityDilatedSecondDiagonalDetectorHorizon
    (beta : ℝ) : ℝ :=
  Real.log (1 + fzzKreinRAt beta / fzzKreinQAt beta) /
    fzzKreinPAt beta

theorem fzzCigarParityDilatedSecondDiagonalDetectorHorizon_pos
    {beta : ℝ} (hbeta : 0 < beta) :
    0 < fzzCigarParityDilatedSecondDiagonalDetectorHorizon beta := by
  have hP := fzzKreinPAt_pos hbeta
  have hQ := fzzKreinQAt_pos hbeta
  have hR := fzzKreinRAt_pos hbeta
  rw [fzzCigarParityDilatedSecondDiagonalDetectorHorizon]
  apply div_pos
  · apply Real.log_pos
    have hRQ : 0 < fzzKreinRAt beta / fzzKreinQAt beta := div_pos hR hQ
    linarith
  · exact hP

theorem fzzCigarParityDilatedSecondDiagonalFlowShear_nonneg
    {beta t : ℝ} (hbeta : 0 < beta) (ht : 0 ≤ t) :
    0 ≤ fzzCigarParityDilatedSecondDiagonalFlowShear beta t := by
  rw [fzzCigarParityDilatedSecondDiagonalFlowShear]
  have hQR : 0 < fzzKreinQAt beta / fzzKreinRAt beta :=
    div_pos (fzzKreinQAt_pos hbeta) (fzzKreinRAt_pos hbeta)
  exact mul_nonneg hQR.le
    (sub_nonneg.mpr (Real.one_le_exp
      (mul_nonneg (fzzKreinPAt_pos hbeta).le ht)))

theorem fzzCigarParityDilatedSecondDiagonalFlowShear_mono_iff
    {beta : ℝ} (hbeta : 0 < beta) (s t : ℝ) :
    fzzCigarParityDilatedSecondDiagonalFlowShear beta s ≤
        fzzCigarParityDilatedSecondDiagonalFlowShear beta t ↔
      s ≤ t := by
  rw [fzzCigarParityDilatedSecondDiagonalFlowShear,
    fzzCigarParityDilatedSecondDiagonalFlowShear]
  have hQR : 0 < fzzKreinQAt beta / fzzKreinRAt beta :=
    div_pos (fzzKreinQAt_pos hbeta) (fzzKreinRAt_pos hbeta)
  have hP := fzzKreinPAt_pos hbeta
  constructor
  · intro h
    have hsub := le_of_mul_le_mul_left h hQR
    have hexp :
        Real.exp (fzzKreinPAt beta * s) ≤
          Real.exp (fzzKreinPAt beta * t) := by
      linarith
    have hmul := Real.exp_le_exp.mp hexp
    exact le_of_mul_le_mul_left hmul hP
  · intro h
    have hmul : fzzKreinPAt beta * s ≤ fzzKreinPAt beta * t :=
      mul_le_mul_of_nonneg_left h hP.le
    have hexp := Real.exp_le_exp.mpr hmul
    exact mul_le_mul_of_nonneg_left (sub_le_sub_right hexp 1) hQR.le

theorem fzzCigarParityDilatedSecondDiagonalFlowShear_horizon
    {beta : ℝ} (hbeta : 0 < beta) :
    fzzCigarParityDilatedSecondDiagonalFlowShear beta
      (fzzCigarParityDilatedSecondDiagonalDetectorHorizon beta) = 1 := by
  have hP := fzzKreinPAt_pos hbeta
  have hQ := fzzKreinQAt_pos hbeta
  have hR := fzzKreinRAt_pos hbeta
  have harg : 0 < 1 + fzzKreinRAt beta / fzzKreinQAt beta := by
    have hRQ : 0 < fzzKreinRAt beta / fzzKreinQAt beta := div_pos hR hQ
    linarith
  rw [fzzCigarParityDilatedSecondDiagonalFlowShear,
    fzzCigarParityDilatedSecondDiagonalDetectorHorizon]
  have hcancel :
      fzzKreinPAt beta *
          (Real.log (1 + fzzKreinRAt beta / fzzKreinQAt beta) /
            fzzKreinPAt beta) =
        Real.log (1 + fzzKreinRAt beta / fzzKreinQAt beta) := by
    field_simp [hP.ne']
  rw [hcancel, Real.exp_log harg]
  field_simp [hQ.ne', hR.ne']
  ring

theorem fzzCigarParityDilatedSecondDiagonalFlowShear_le_one_iff
    {beta : ℝ} (hbeta : 0 < beta) (t : ℝ) :
    fzzCigarParityDilatedSecondDiagonalFlowShear beta t ≤ 1 ↔
      t ≤ fzzCigarParityDilatedSecondDiagonalDetectorHorizon beta := by
  rw [← fzzCigarParityDilatedSecondDiagonalFlowShear_horizon hbeta]
  exact fzzCigarParityDilatedSecondDiagonalFlowShear_mono_iff hbeta t
    (fzzCigarParityDilatedSecondDiagonalDetectorHorizon beta)

/-- **Sharp detector horizon.** On nonnegative time, transported diagonal energy remains a
phase-robust reciprocal-radius detector exactly through the finite source horizon. -/
theorem fzzCigarParityDilatedSecondDiagonalFlowUniversallySeparating_iff_time_le
    {beta t : ℝ} (hbeta : 0 < beta) (ht : 0 ≤ t) :
    FZZCigarParityDilatedSecondDiagonalFlowUniversallySeparating beta t ↔
      t ≤ fzzCigarParityDilatedSecondDiagonalDetectorHorizon beta := by
  rw [fzzCigarParityDilatedSecondDiagonalFlowUniversallySeparating_iff]
  have hk := fzzCigarParityDilatedSecondDiagonalFlowShear_nonneg hbeta ht
  calc
    fzzCigarParityDilatedSecondDiagonalFlowShear beta t ^ (2 : ℕ) ≤ 1 ↔
        fzzCigarParityDilatedSecondDiagonalFlowShear beta t ^ (2 : ℕ) ≤ 1 ^ (2 : ℕ) := by
          norm_num
    _ ↔ fzzCigarParityDilatedSecondDiagonalFlowShear beta t ≤ 1 :=
      sq_le_sq₀ hk zero_le_one
    _ ↔ t ≤ fzzCigarParityDilatedSecondDiagonalDetectorHorizon beta :=
      fzzCigarParityDilatedSecondDiagonalFlowShear_le_one_iff hbeta t

theorem fzzCigarParityDilatedSecondDiagonalFlowUniversallySeparating_horizon
    {beta : ℝ} (hbeta : 0 < beta) :
    FZZCigarParityDilatedSecondDiagonalFlowUniversallySeparating beta
      (fzzCigarParityDilatedSecondDiagonalDetectorHorizon beta) := by
  apply (fzzCigarParityDilatedSecondDiagonalFlowUniversallySeparating_iff_time_le
    hbeta (fzzCigarParityDilatedSecondDiagonalDetectorHorizon_pos hbeta).le).mpr
  exact le_rfl

theorem not_fzzCigarParityDilatedSecondDiagonalFlowUniversallySeparating_of_horizon_lt
    {beta t : ℝ} (hbeta : 0 < beta)
    (ht : fzzCigarParityDilatedSecondDiagonalDetectorHorizon beta < t) :
    ¬ FZZCigarParityDilatedSecondDiagonalFlowUniversallySeparating beta t := by
  intro hsep
  have h0 : 0 ≤ t :=
    le_trans (fzzCigarParityDilatedSecondDiagonalDetectorHorizon_pos hbeta).le ht.le
  have hle :=
    (fzzCigarParityDilatedSecondDiagonalFlowUniversallySeparating_iff_time_le
      hbeta h0).mp hsep
  linarith

/-- During the complete detector window, evolved diagonal readings agree under functional
reflection exactly on the critical line. -/
theorem fzzCigarParityDilatedSecondDiagonalStabilizedFlow_mellinReading_eq_reflection_iff
    {beta t : ℝ} (hbeta : 0 < beta) (ht0 : 0 ≤ t)
    (ht : t ≤ fzzCigarParityDilatedSecondDiagonalDetectorHorizon beta) (rho : ℂ) :
    fzzCigarParityHermitianQuadraticObservable 0 0 0 1
        (fzzCigarParityDilatedSecondDiagonalStabilizedFlow beta t
          (fzzCigarParityMellinCharacterCarrier rho)) =
      fzzCigarParityHermitianQuadraticObservable 0 0 0 1
        (fzzCigarParityDilatedSecondDiagonalStabilizedFlow beta t
          (fzzCigarParityMellinCharacterCarrier
            (criticalLineReflectionPoint rho))) ↔
      rho.re = 1 / 2 := by
  rw [fzzCigarParityDilatedSecondDiagonalStabilizedFlow_pullback,
    fzzCigarParityDilatedSecondDiagonalStabilizedFlow_pullback]
  have hsep :=
    (fzzCigarParityDilatedSecondDiagonalFlowUniversallySeparating_iff_time_le
      hbeta ht0).mpr ht
  have hcone :=
    (fzzCigarParityHermitianUniversalRadialReflectionSeparating_iff
      (fzzCigarParityDilatedSecondDiagonalFlowShear beta t ^ (2 : ℕ))
      (-fzzCigarParityDilatedSecondDiagonalFlowShear beta t) 0 1).mp hsep
  exact fzzCigarParityMellinCharacterHermitianReading_eq_reflection_iff
    (fzzCigarParityDilatedSecondDiagonalFlowShear beta t ^ (2 : ℕ))
    (-fzzCigarParityDilatedSecondDiagonalFlowShear beta t) 0 1
    hcone.1 hcone.2 rho

end

end RHTower

