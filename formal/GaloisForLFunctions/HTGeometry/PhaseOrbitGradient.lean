import GaloisForLFunctions.HTGeometry.TorusTranslateDifference
import GaloisForLFunctions.HTGeometry.FiniteMaxGradient

/-!
# The gradient of a phase-orbit overlap score

A phase orbit rotates each component of a fixed family of vectors by its own phase, so the overlap
amplitude with a target is a trigonometric sum whose coordinate derivative is the corresponding
component overlap, scaled by the frequency.  The overlap score is the squared modulus of that
amplitude, so its coordinate derivative is twice the real pairing of the amplitude with the
coordinate derivative of the amplitude.

Consequently the squared gradient of the score is controlled by the amplitude times the sum of the
squared component overlaps, with no dependence on the number of targets.
-/

open scoped BigOperators ComplexConjugate
open Complex

noncomputable section

namespace GaloisForLFunctions.HTGeometry

section PhaseOrbit

set_option linter.unusedSectionVars false

variable {d : Type*} [Fintype d] [DecidableEq d]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- The phase-orbit overlap amplitude of a target with a family of vectors. -/
def overlapAmp (u : d → V) (z : V) (x : d → ℝ) : ℂ :=
  ∑ j : d, Complex.exp (-(2 * Real.pi * Complex.I) * (x j)) * (inner ℂ z (u j))

/-- The coordinate embedding of the vector model into the complex numbers. -/
def coordCLM (j : d) : (d → ℝ) →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (ContinuousLinearMap.proj j)

@[simp] theorem coordCLM_apply (j : d) (v : d → ℝ) : coordCLM j v = (v j : ℂ) := rfl

/-- The derivative of the overlap amplitude. -/
def overlapAmpDeriv (u : d → V) (z : V) (x : d → ℝ) : (d → ℝ) →L[ℝ] ℂ :=
  ∑ j : d, (-(2 * Real.pi * Complex.I) *
    Complex.exp (-(2 * Real.pi * Complex.I) * (x j)) * (inner ℂ z (u j))) • coordCLM j

theorem hasFDerivAt_overlapAmp (u : d → V) (z : V) (x : d → ℝ) :
    HasFDerivAt (overlapAmp u z) (overlapAmpDeriv u z x) x := by
  have hterm : ∀ j : d, HasFDerivAt
      (fun y : d → ℝ => Complex.exp (-(2 * Real.pi * Complex.I) * (y j)) * (inner ℂ z (u j)))
      ((-(2 * Real.pi * Complex.I) *
        Complex.exp (-(2 * Real.pi * Complex.I) * (x j)) * (inner ℂ z (u j))) • coordCLM j) x := by
    intro j
    have hlin : HasFDerivAt (fun y : d → ℝ => (-(2 * Real.pi * Complex.I)) * ((y j : ℝ) : ℂ))
        ((-(2 * Real.pi * Complex.I)) • coordCLM j) x :=
      ((coordCLM j).hasFDerivAt).const_mul (-(2 * Real.pi * Complex.I))
    have hexp := hlin.cexp
    have hmul := hexp.mul_const (inner ℂ z (u j))
    refine hmul.congr_fderiv ?_
    ext v
    simp only [smul_apply, coordCLM_apply, smul_eq_mul]
    ring
  have hfun : overlapAmp u z = ∑ i : d, fun y : d → ℝ =>
      Complex.exp (-(2 * Real.pi * Complex.I) * (y i)) * (inner ℂ z (u i)) := by
    funext y
    rw [Finset.sum_apply]
    rfl
  rw [hfun, overlapAmpDeriv]
  exact HasFDerivAt.sum fun j (_ : j ∈ Finset.univ) => hterm j

theorem overlapAmpDeriv_single (u : d → V) (z : V) (x : d → ℝ) (j : d) :
    overlapAmpDeriv u z x (Pi.single j 1) =
      -(2 * Real.pi * Complex.I) * Complex.exp (-(2 * Real.pi * Complex.I) * (x j)) *
        (inner ℂ z (u j)) := by
  rw [overlapAmpDeriv]
  rw [sum_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [Pi.single_eq_of_ne hij]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

theorem norm_overlapAmpDeriv_single (u : d → V) (z : V) (x : d → ℝ) (j : d) :
    ‖overlapAmpDeriv u z x (Pi.single j 1)‖ = 2 * Real.pi * ‖(inner ℂ z (u j) : ℂ)‖ := by
  rw [overlapAmpDeriv_single, norm_mul, norm_mul]
  have hexp : ‖Complex.exp (-(2 * Real.pi * Complex.I) * (x j))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [hexp, mul_one]
  congr 1
  simp [abs_of_nonneg Real.pi_pos.le]

/-- The overlap score of a target with the phase orbit. -/
def overlapScore (u : d → V) (z : V) (x : d → ℝ) : ℝ := ‖overlapAmp u z x‖ ^ 2

theorem hasFDerivAt_overlapScore (u : d → V) (z : V) (x : d → ℝ) :
    HasFDerivAt (overlapScore u z)
      ((2 : ℕ) • (innerSL ℝ (overlapAmp u z x)).comp (overlapAmpDeriv u z x)) x :=
  (hasFDerivAt_overlapAmp u z x).norm_sq

theorem differentiable_overlapScore (u : d → V) (z : V) :
    Differentiable ℝ (overlapScore u z) :=
  fun x => (hasFDerivAt_overlapScore u z x).differentiableAt

theorem abs_fderiv_overlapScore_single_le (u : d → V) (z : V) (x : d → ℝ) (j : d) :
    |fderiv ℝ (overlapScore u z) x (Pi.single j 1)| ≤
      2 * ‖overlapAmp u z x‖ * (2 * Real.pi * ‖(inner ℂ z (u j) : ℂ)‖) := by
  rw [(hasFDerivAt_overlapScore u z x).fderiv]
  have hval : ((2 : ℕ) • (innerSL ℝ (overlapAmp u z x)).comp (overlapAmpDeriv u z x))
      (Pi.single j 1) =
      2 * (inner ℝ (overlapAmp u z x) (overlapAmpDeriv u z x (Pi.single j 1))) := by
    simp [smul_apply, real_inner_eq_re_inner]
    ring
  rw [hval, abs_mul]
  have hcs : |(inner ℝ (overlapAmp u z x) (overlapAmpDeriv u z x (Pi.single j 1)) : ℝ)| ≤
      ‖overlapAmp u z x‖ * ‖overlapAmpDeriv u z x (Pi.single j 1)‖ :=
    abs_real_inner_le_norm _ _
  rw [norm_overlapAmpDeriv_single] at hcs
  have h2 : |(2 : ℝ)| = 2 := by norm_num
  rw [h2, mul_assoc]
  exact mul_le_mul_of_nonneg_left hcs (by norm_num)

/-- **Squared gradient of one overlap score.**  The squared coordinate gradient of the score is
controlled by the squared amplitude times the squared component overlaps. -/
theorem sum_sq_fderiv_overlapScore_le (u : d → V) (z : V) (x : d → ℝ) {p : ℝ}
    (hA : ‖overlapAmp u z x‖ ≤ 1)
    (hc : ∑ j : d, ‖(inner ℂ z (u j) : ℂ)‖ ^ 2 ≤ p) :
    ∑ j : d, (fderiv ℝ (overlapScore u z) x (Pi.single j 1)) ^ 2 ≤
      16 * Real.pi ^ 2 * p := by
  have hterm : ∀ j : d, (fderiv ℝ (overlapScore u z) x (Pi.single j 1)) ^ 2 ≤
      16 * Real.pi ^ 2 * ‖(inner ℂ z (u j) : ℂ)‖ ^ 2 := by
    intro j
    have habs := abs_fderiv_overlapScore_single_le u z x j
    have hnn : (0 : ℝ) ≤ 2 * ‖overlapAmp u z x‖ * (2 * Real.pi * ‖(inner ℂ z (u j) : ℂ)‖) := by
      have := Real.pi_pos
      positivity
    have hsq : (fderiv ℝ (overlapScore u z) x (Pi.single j 1)) ^ 2 ≤
        (2 * ‖overlapAmp u z x‖ * (2 * Real.pi * ‖(inner ℂ z (u j) : ℂ)‖)) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) habs 2
    refine le_trans hsq ?_
    have hA0 : (0 : ℝ) ≤ ‖overlapAmp u z x‖ := norm_nonneg _
    have hcj : (0 : ℝ) ≤ ‖(inner ℂ z (u j) : ℂ)‖ := norm_nonneg _
    have hpi : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
    have hA2 : ‖overlapAmp u z x‖ ^ 2 ≤ 1 := by nlinarith [hA0, hA]
    have hprod : 16 * Real.pi ^ 2 * ‖(inner ℂ z (u j) : ℂ)‖ ^ 2 * ‖overlapAmp u z x‖ ^ 2 ≤
        16 * Real.pi ^ 2 * ‖(inner ℂ z (u j) : ℂ)‖ ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left hA2 (by positivity)
    nlinarith [hprod]
  calc ∑ j : d, (fderiv ℝ (overlapScore u z) x (Pi.single j 1)) ^ 2
      ≤ ∑ j : d, 16 * Real.pi ^ 2 * ‖(inner ℂ z (u j) : ℂ)‖ ^ 2 := Finset.sum_le_sum fun j _ =>
        hterm j
    _ = 16 * Real.pi ^ 2 * ∑ j : d, ‖(inner ℂ z (u j) : ℂ)‖ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ 16 * Real.pi ^ 2 * p := by
        refine mul_le_mul_of_nonneg_left hc ?_
        have := Real.pi_pos
        positivity

end PhaseOrbit

end GaloisForLFunctions.HTGeometry
