import GaloisForLFunctions.HTGeometry.CompactSineSquaredPulse
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# Round-sphere dipole and odd-harmonic calibration

This module formalizes Okten--Turan, arXiv:2608.19244v1, equations `(59)`--`(64)` and
`(81)`--`(88)`.  Surface integrals are evaluated in standard spherical coordinates, where the
azimuthal integral and area density give the prefactor `2 * pi * R²`.
-/

open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

/-- Equation `(63)`: any homogeneous mode of degree `ell` has antipodal parity `(-1)^ell`. -/
theorem homogeneous_mode_antipodal_parity
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (P : V → ℝ) (ell : ℕ) (hhom : ∀ c x, P (c • x) = c ^ ell * P x) (x : V) :
    P (-x) = (-1 : ℝ) ^ ell * P x := by
  simpa using hhom (-1) x

/-- Odd homogeneous modes are antipodal-odd. -/
theorem odd_homogeneous_mode_antipodal
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (P : V → ℝ) {ell : ℕ} (hhom : ∀ c x, P (c • x) = c ^ ell * P x)
    (hell : Odd ell) (x : V) :
    P (-x) = -P x := by
  rw [homogeneous_mode_antipodal_parity P ell hhom x, hell.neg_one_pow, neg_one_mul]

/-- Polar integral entering the dipole L² norm. -/
theorem integral_zero_pi_sin_mul_cos_sq :
    ∫ theta in (0 : ℝ)..Real.pi, Real.sin theta * Real.cos theta ^ (2 : ℕ) = 2 / 3 := by
  rw [integral_sin_mul_cos_sq]
  simp
  norm_num

/-- Polar integral entering the dipole Dirichlet energy. -/
theorem integral_zero_pi_sin_cube :
    ∫ theta in (0 : ℝ)..Real.pi, Real.sin theta ^ (3 : ℕ) = 4 / 3 := by
  rw [integral_sin_pow_three]
  simp
  norm_num

/-- Equation `(81)`: squared L² norm of `a cos theta` on a round sphere. -/
theorem roundSphere_dipole_norm_sq (R a : ℝ) :
    (2 * Real.pi * R ^ (2 : ℕ)) *
        (∫ theta in (0 : ℝ)..Real.pi,
          Real.sin theta * (a * Real.cos theta) ^ (2 : ℕ)) =
      4 * Real.pi * R ^ (2 : ℕ) * a ^ (2 : ℕ) / 3 := by
  have hfun : (fun theta => Real.sin theta * (a * Real.cos theta) ^ (2 : ℕ)) =
      fun theta => a ^ (2 : ℕ) * (Real.sin theta * Real.cos theta ^ (2 : ℕ)) := by
    funext theta
    ring
  rw [hfun, intervalIntegral.integral_const_mul, integral_zero_pi_sin_mul_cos_sq]
  ring

/-- Equations `(60)` and `(86)`: squared norm of the centered dipole mismatch `2 a cos theta`. -/
theorem roundSphere_dipole_mismatch (R a : ℝ) :
    (2 * Real.pi * R ^ (2 : ℕ)) *
        (∫ theta in (0 : ℝ)..Real.pi,
          Real.sin theta * (2 * a * Real.cos theta) ^ (2 : ℕ)) =
      16 * Real.pi * R ^ (2 : ℕ) * a ^ (2 : ℕ) / 3 := by
  have hfun : (fun theta => Real.sin theta * (2 * a * Real.cos theta) ^ (2 : ℕ)) =
      fun theta => (2 * a) ^ (2 : ℕ) * (Real.sin theta * Real.cos theta ^ (2 : ℕ)) := by
    funext theta
    ring
  rw [hfun, intervalIntegral.integral_const_mul, integral_zero_pi_sin_mul_cos_sq]
  ring

/-- Equation `(61)`: Dirichlet energy of the round-sphere dipole; radius cancels. -/
theorem roundSphere_dipole_energy (a : ℝ) :
    (2 * Real.pi * a ^ (2 : ℕ)) *
        (∫ theta in (0 : ℝ)..Real.pi, Real.sin theta ^ (3 : ℕ)) =
      8 * Real.pi * a ^ (2 : ℕ) / 3 := by
  rw [integral_zero_pi_sin_cube]
  ring

/-- Equation `(62)`: the dipole attains the round-sphere spectral constant. -/
theorem roundSphere_dipole_saturates (R a : ℝ) (hR : R ≠ 0) :
    8 * Real.pi * a ^ (2 : ℕ) / 3 =
      1 / (2 * R ^ (2 : ℕ)) * (16 * Real.pi * R ^ (2 : ℕ) * a ^ (2 : ℕ) / 3) := by
  field_simp
  ring

/-- Square root of the maximal dipole mismatch in equation `(86)`. -/
theorem roundSphere_dipole_max_sqrt {R a0 : ℝ} (ha0 : 0 ≤ a0) :
    Real.sqrt (16 * Real.pi * R ^ (2 : ℕ) * a0 ^ (2 : ℕ) / 3) =
      2 * a0 * Real.sqrt (4 * Real.pi * R ^ (2 : ℕ) / 3) := by
  have hn : 0 ≤ 4 * Real.pi * R ^ (2 : ℕ) / 3 := by positivity
  have heq : 16 * Real.pi * R ^ (2 : ℕ) * a0 ^ (2 : ℕ) / 3 =
      (2 * a0 * Real.sqrt (4 * Real.pi * R ^ (2 : ℕ) / 3)) ^ (2 : ℕ) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hn]
    ring
  rw [heq, Real.sqrt_sq_eq_abs, abs_of_nonneg]
  positivity

/-- Time-dependent centered mismatch of the compact round-sphere dipole, equation `(86)`. -/
noncomputable def roundSphereDipoleMismatchHistory
    (R a0 u0 tau u : ℝ) : ℝ :=
  16 * Real.pi * R ^ (2 : ℕ) * sineSquaredPulse a0 u0 tau u ^ (2 : ℕ) / 3

/-- Every value of the compact dipole mismatch is bounded by its peak calibration. -/
theorem roundSphereDipoleMismatchHistory_le_max {a0 : ℝ} (ha0 : 0 ≤ a0)
    (R u0 tau u : ℝ) :
    roundSphereDipoleMismatchHistory R a0 u0 tau u ≤
      16 * Real.pi * R ^ (2 : ℕ) * a0 ^ (2 : ℕ) / 3 := by
  have hpulse := sineSquaredPulse_mem_Icc ha0 u0 tau u
  have hsquares : sineSquaredPulse a0 u0 tau u ^ (2 : ℕ) ≤ a0 ^ (2 : ℕ) :=
    (sq_le_sq₀ hpulse.1 ha0).2 hpulse.2
  unfold roundSphereDipoleMismatchHistory
  have hcoefficient : 0 ≤ 16 * Real.pi * R ^ (2 : ℕ) / 3 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hsquares hcoefficient]

/-- Equation `(86)`: the supremum of the mismatch history on the active interval is attained at
the midpoint and equals `16 * pi * R² * a0² / 3`. -/
theorem sSup_roundSphereDipoleMismatchHistory {a0 tau : ℝ}
    (ha0 : 0 ≤ a0) (htau : 0 < tau) (R u0 : ℝ) :
    sSup (roundSphereDipoleMismatchHistory R a0 u0 tau '' Icc u0 (u0 + tau)) =
      16 * Real.pi * R ^ (2 : ℕ) * a0 ^ (2 : ℕ) / 3 := by
  have hmidMem : u0 + tau / 2 ∈ Icc u0 (u0 + tau) := by constructor <;> linarith
  have hmid : roundSphereDipoleMismatchHistory R a0 u0 tau (u0 + tau / 2) =
      16 * Real.pi * R ^ (2 : ℕ) * a0 ^ (2 : ℕ) / 3 := by
    rw [roundSphereDipoleMismatchHistory, sineSquaredPulse_mid a0 u0 htau.ne']
  have hbounded : BddAbove
      (roundSphereDipoleMismatchHistory R a0 u0 tau '' Icc u0 (u0 + tau)) := by
    refine ⟨16 * Real.pi * R ^ (2 : ℕ) * a0 ^ (2 : ℕ) / 3, ?_⟩
    rintro y ⟨u, _hu, rfl⟩
    exact roundSphereDipoleMismatchHistory_le_max ha0 R u0 tau u
  apply le_antisymm
  · apply csSup_le
    · exact ⟨_, ⟨u0 + tau / 2, hmidMem, rfl⟩⟩
    · rintro y ⟨u, _hu, rfl⟩
      exact roundSphereDipoleMismatchHistory_le_max ha0 R u0 tau u
  · apply le_csSup hbounded
    exact ⟨u0 + tau / 2, hmidMem, hmid⟩

/-- Equations `(84)`--`(88)`: for `Jmin = 1`, compact dipole response equals the conformal
forcing scale. -/
theorem roundSphere_compactDipole_saturation {C R a0 : ℝ}
    (ha0 : 0 ≤ a0) :
    2 * C * a0 * Real.sqrt (4 * Real.pi * R ^ (2 : ℕ) / 3) =
      C * (2 / (1 + 1)) * Real.sqrt (16 * Real.pi * R ^ (2 : ℕ) * a0 ^ (2 : ℕ) / 3) := by
  rw [roundSphere_dipole_max_sqrt ha0]
  ring

/-- Equation `(82)`: spatial L² norm of the round-sphere conformal dipole defect. -/
noncomputable def roundSphereDipoleDefectNorm (C R a0 u0 tau u : ℝ) : ℝ :=
  |scalarConformalPulseDefect C a0 u0 tau u| *
    Real.sqrt (4 * Real.pi * R ^ (2 : ℕ) / 3)

/-- Equation `(84)`: exact time-integrated spatial L² response of the compact dipole. -/
theorem integral_roundSphereDipoleDefectNorm {C a0 tau : ℝ}
    (hC : 0 ≤ C) (ha0 : 0 ≤ a0) (htau : 0 < tau) (R u0 : ℝ) :
    ∫ u in u0..u0 + tau, roundSphereDipoleDefectNorm C R a0 u0 tau u =
      2 * C * a0 * Real.sqrt (4 * Real.pi * R ^ (2 : ℕ) / 3) := by
  change ∫ u in u0..u0 + tau, |scalarConformalPulseDefect C a0 u0 tau u| *
    Real.sqrt (4 * Real.pi * R ^ (2 : ℕ) / 3) = _
  rw [intervalIntegral.integral_mul_const,
    integral_abs_scalarConformalPulseDefect hC ha0 htau u0]

/-- The angular integral of a dipole vanishes on every round slice. -/
theorem roundSphere_dipole_angular_integral_eq_zero (R a : ℝ) :
    (2 * Real.pi * R ^ (2 : ℕ)) *
      (∫ theta in (0 : ℝ)..Real.pi, Real.sin theta * (a * Real.cos theta)) = 0 := by
  have hfun : (fun theta => Real.sin theta * (a * Real.cos theta)) =
      fun theta => a * (Real.sin theta * Real.cos theta) := by
    funext theta
    ring
  rw [hfun, intervalIntegral.integral_const_mul, integral_sin_mul_cos₂]
  simp

/-- Signed temporal response vanishes in every fixed angular channel. -/
theorem roundSphere_dipole_signed_time_integral_eq_zero {tau : ℝ} (htau : 0 < tau)
    (C a0 u0 z : ℝ) :
    ∫ u in u0..u0 + tau, z * scalarConformalPulseDefect C a0 u0 tau u = 0 := by
  rw [intervalIntegral.integral_const_mul,
    integral_scalarConformalPulseDefect_eq_zero htau C a0 u0, mul_zero]

/-- Equation `(64)`: an `ell`-eigenmode with antipodal mismatch norm squared `4 * normSq` has
normalized angular cost `ell * (ell + 1) / 2`.  The preceding parity theorem supplies the factor
four for every odd homogeneous spherical mode. -/
theorem oddHarmonic_calibration (ell R normSq : ℝ) (hR : R ≠ 0) (hn : normSq ≠ 0) :
    (ell * (ell + 1) / R ^ (2 : ℕ) * normSq) /
        ((4 * normSq) / (2 * R ^ (2 : ℕ))) = ell * (ell + 1) / 2 := by
  field_simp
  ring

end GaloisForLFunctions.HTGeometry
