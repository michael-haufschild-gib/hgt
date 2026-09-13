import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# Algebraic core of arXiv:2608.10427

This file formalizes premise-free finite-dimensional consequences of the domain-delay
construction in *Causality Sum Rules in Conventional Scattering Matrices*.

The analytic logarithmic sum rules in that paper require causality, analyticity,
transparency, and regularity assumptions.  They are deliberately not asserted here.
The statements below isolate the unconditional algebra used before those hypotheses:
real-frequency delay phases are unitary, left delay correction preserves the full power
Gram matrix, and common delay preserves every coherent-return modulus and determinant
modulus.
-/

open Complex Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Channel phase which removes a real-frequency reference-domain time advance. -/
def causalityDomainDelayPhase (omega tau : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((omega * tau : ℝ) : ℂ))

@[simp] theorem norm_causalityDomainDelayPhase (omega tau : ℝ) :
    ‖causalityDomainDelayPhase omega tau‖ = 1 := by
  rw [causalityDomainDelayPhase, Complex.norm_exp]
  norm_num [Complex.mul_re]

@[simp] theorem star_causalityDomainDelayPhase_mul_self (omega tau : ℝ) :
    star (causalityDomainDelayPhase omega tau) * causalityDomainDelayPhase omega tau = 1 := by
  simp only [RCLike.star_def]
  rw [Complex.conj_mul', norm_causalityDomainDelayPhase]
  norm_num

/-- Diagonal earliest-arrival delay operator of the paper. -/
def causalityDomainDelayMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (omega : ℝ) (tau : ι → ℝ) : Matrix ι ι ℂ :=
  Matrix.diagonal fun i => causalityDomainDelayPhase omega (tau i)

/-- Every real-frequency domain-delay matrix is unitary, with no condition on delays. -/
@[simp] theorem causalityDomainDelayMatrix_star_mul_self {ι : Type*}
    [Fintype ι] [DecidableEq ι] (omega : ℝ) (tau : ι → ℝ) :
    (causalityDomainDelayMatrix omega tau)ᴴ * causalityDomainDelayMatrix omega tau = 1 := by
  rw [causalityDomainDelayMatrix, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact star_causalityDomainDelayPhase_mul_self omega (tau i)

/-- Conventional scattering matrix after removal of channel-dependent time advance. -/
def causalityDomainDelayedScattering {ι : Type*} [Fintype ι] [DecidableEq ι]
    (omega : ℝ) (tau : ι → ℝ) (S : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  causalityDomainDelayMatrix omega tau * S

/-- Equation (1)'s power-balance identity: delay correction preserves the complete Gram matrix. -/
theorem causalityDomainDelayedScattering_powerBalance {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (omega : ℝ) (tau : ι → ℝ) (S : Matrix ι ι ℂ) :
    (causalityDomainDelayedScattering omega tau S)ᴴ *
        causalityDomainDelayedScattering omega tau S = Sᴴ * S := by
  rw [causalityDomainDelayedScattering, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (causalityDomainDelayMatrix omega tau)ᴴ,
    causalityDomainDelayMatrix_star_mul_self]
  simp

/-- A common-delay correction is scalar multiplication by one unit-modulus phase. -/
theorem causalityDomainDelayMatrix_const {ι : Type*} [Fintype ι] [DecidableEq ι]
    (omega tau : ℝ) :
    causalityDomainDelayMatrix (ι := ι) omega (fun _ => tau) =
      causalityDomainDelayPhase omega tau • (1 : Matrix ι ι ℂ) := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    simp [causalityDomainDelayMatrix]
  · simp [causalityDomainDelayMatrix, hij]

/-- Same-channel coherent amplitude used in the paper's projected sum rule. -/
def causalityCoherentReturn {ι : Type*} [Fintype ι]
    (v : ι → ℂ) (S : Matrix ι ι ℂ) : ℂ :=
  star v ⬝ᵥ S.mulVec v

/-- Common delay changes coherent return only by a phase, so its measured modulus is unchanged. -/
theorem norm_causalityCoherentReturn_domainDelayed_const {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (omega tau : ℝ) (v : ι → ℂ) (S : Matrix ι ι ℂ) :
    ‖causalityCoherentReturn v
        (causalityDomainDelayedScattering omega (fun _ => tau) S)‖ =
      ‖causalityCoherentReturn v S‖ := by
  rw [causalityDomainDelayedScattering, causalityDomainDelayMatrix_const]
  simp [causalityCoherentReturn, Matrix.smul_mulVec, dotProduct_smul]

/-- Scalar one-channel instance: domain-delay correction preserves response modulus. -/
theorem norm_causalityDomainDelayPhase_mul (omega tau : ℝ) (s : ℂ) :
    ‖causalityDomainDelayPhase omega tau * s‖ = ‖s‖ := by
  rw [norm_mul, norm_causalityDomainDelayPhase, one_mul]

/-- Exact determinant phase introduced by channel-dependent domain delays. -/
theorem det_causalityDomainDelayedScattering {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (omega : ℝ) (tau : ι → ℝ) (S : Matrix ι ι ℂ) :
    (causalityDomainDelayedScattering omega tau S).det =
      (∏ i, causalityDomainDelayPhase omega (tau i)) * S.det := by
  rw [causalityDomainDelayedScattering, Matrix.det_mul]
  simp [causalityDomainDelayMatrix, Matrix.det_diagonal]

/-- Domain delay changes determinant only by a unit-modulus factor. -/
theorem norm_det_causalityDomainDelayedScattering {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (omega : ℝ) (tau : ι → ℝ) (S : Matrix ι ι ℂ) :
    ‖(causalityDomainDelayedScattering omega tau S).det‖ = ‖S.det‖ := by
  rw [causalityDomainDelayedScattering, Matrix.det_mul, norm_mul]
  suffices ‖(causalityDomainDelayMatrix omega tau).det‖ = 1 by simp [this]
  simp [causalityDomainDelayMatrix, Matrix.det_diagonal, norm_prod]

/-- A premise-free parametrization of a strict attenuation threshold in `(0, 1)`.
The paper's freely chosen threshold can be recovered by a logarithmic reparametrization. -/
def causalityAttenuationThreshold (x : ℝ) : ℝ :=
  Real.exp (-Real.exp x)

theorem causalityAttenuationThreshold_pos (x : ℝ) :
    0 < causalityAttenuationThreshold x :=
  Real.exp_pos _

theorem causalityAttenuationThreshold_lt_one (x : ℝ) :
    causalityAttenuationThreshold x < 1 := by
  rw [causalityAttenuationThreshold, Real.exp_lt_one_iff]
  exact neg_neg_of_pos (Real.exp_pos x)

/-- Clamp an arbitrary real channel datum to the passive singular-value range `[0, 1]`. -/
def causalityPassiveChannelModulus (x : ℝ) : ℝ :=
  min 1 |x|

theorem causalityPassiveChannelModulus_nonneg (x : ℝ) :
    0 ≤ causalityPassiveChannelModulus x := by
  simp [causalityPassiveChannelModulus]

theorem causalityPassiveChannelModulus_le_one (x : ℝ) :
    causalityPassiveChannelModulus x ≤ 1 :=
  min_le_left _ _

/-- Channels below the paper's threshold force a quantitative product loss.  This is
the finite-dimensional algebra behind the determinant/geometric-mean channel count:
each suppressed passive channel contributes one threshold factor, while every other
passive channel contributes at most one. -/
theorem passiveChannelProduct_le_threshold_pow_suppressedCount
    {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ℝ) (sigma : ι → ℝ) :
    (∏ i, causalityPassiveChannelModulus (sigma i)) ≤
      causalityAttenuationThreshold x ^
        (Finset.univ.filter fun i =>
          causalityPassiveChannelModulus (sigma i) ≤
            causalityAttenuationThreshold x).card := by
  classical
  let rho := causalityAttenuationThreshold x
  let a := fun i => causalityPassiveChannelModulus (sigma i)
  let suppressed := Finset.univ.filter fun i => a i ≤ rho
  calc
    (∏ i, a i) ≤ ∏ i, if i ∈ suppressed then rho else 1 := by
      apply Finset.prod_le_prod
      · intro i _
        exact causalityPassiveChannelModulus_nonneg (sigma i)
      · intro i _
        by_cases hi : i ∈ suppressed
        · rw [if_pos hi]
          exact (Finset.mem_filter.mp hi).2
        · rw [if_neg hi]
          exact causalityPassiveChannelModulus_le_one (sigma i)
    _ = rho ^ suppressed.card := by
      rw [Finset.prod_ite]
      simp

end

end GaloisForLFunctions.HTGeometry
