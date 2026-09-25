import GaloisForLFunctions.RHTower.PhotonicHelicalInfiniteLadderCore
import Mathlib.Analysis.Real.Pi.Bounds

/-! Scratch for the exact co-rotating PTR dispersion test. -/

namespace RHTower

open GaloisForLFunctions.HTGeometry

private theorem mcast_ne_zero {m : ℤ} (hm : m ≠ 0) : (m : ℝ) ≠ 0 := by
  exact_mod_cast hm

theorem ptr_locked_phase_corotating (ω Ω θ t : ℝ) (ℓ m n : ℤ) (hm : m ≠ 0) :
    (floquetSidebandAngularMomentum ℓ m n : ℝ) * θ -
        floquetSidebandFrequency ω Ω n * t =
      (floquetSidebandAngularMomentum ℓ m n : ℝ) *
          (θ - Ω / (m : ℝ) * t) -
        (ω - (ℓ : ℝ) * Ω / (m : ℝ)) * t := by
  simp only [GaloisForLFunctions.HTGeometry.floquetSidebandAngularMomentum,
    GaloisForLFunctions.HTGeometry.floquetSidebandFrequency]
  have hm' := mcast_ne_zero hm
  push_cast
  field_simp
  ring

def ptrScaledHelicalPrincipal (c ε Ω R : ℝ) (m : ℤ) (ξr ξφ : ℝ) : ℝ :=
  (c * (m : ℝ) * R * ξr) ^ 2 +
    (c ^ 2 * (m : ℝ) ^ 2 - ε * (Ω * R) ^ 2) * ξφ ^ 2

theorem ptrScaledHelicalPrincipal_pos_of_subluminal
    (c ε Ω R : ℝ) (m : ℤ) (ξr ξφ : ℝ)
    (hsub : ε * (Ω * R) ^ 2 < c ^ 2 * (m : ℝ) ^ 2)
    (hξ : ξφ ≠ 0) :
    0 < ptrScaledHelicalPrincipal c ε Ω R m ξr ξφ := by
  unfold ptrScaledHelicalPrincipal
  have h1 : 0 ≤ (c * (m : ℝ) * R * ξr) ^ 2 := sq_nonneg _
  have h2 : 0 < ξφ ^ 2 := sq_pos_of_ne_zero hξ
  have h3 : 0 < (c ^ 2 * (m : ℝ) ^ 2 - ε * (Ω * R) ^ 2) * ξφ ^ 2 :=
    mul_pos (sub_pos.mpr hsub) h2
  linarith

/-- Exact light-cylinder boundary for a real normal characteristic root. -/
theorem ptrScaledHelicalPrincipal_has_real_normal_root_iff
    (c ε Ω R : ℝ) (m : ℤ)
    (hcmR : c * (m : ℝ) * R ≠ 0) :
    (∃ ξr : ℝ, ptrScaledHelicalPrincipal c ε Ω R m ξr 1 = 0) ↔
      c ^ 2 * (m : ℝ) ^ 2 ≤ ε * (Ω * R) ^ 2 := by
  constructor
  · rintro ⟨ξr, hroot⟩
    by_contra h
    have hsub : ε * (Ω * R) ^ 2 < c ^ 2 * (m : ℝ) ^ 2 := lt_of_not_ge h
    have hp := ptrScaledHelicalPrincipal_pos_of_subluminal
      c ε Ω R m ξr 1 hsub (by norm_num)
    linarith
  · intro h
    let A : ℝ := ε * (Ω * R) ^ 2 - c ^ 2 * (m : ℝ) ^ 2
    have hA : 0 ≤ A := sub_nonneg.mpr h
    refine ⟨Real.sqrt A / (c * (m : ℝ) * R), ?_⟩
    have he : c * (m : ℝ) * R * (Real.sqrt A / (c * (m : ℝ) * R)) =
        Real.sqrt A := mul_div_cancel₀ _ hcmR
    simp only [ptrScaledHelicalPrincipal, he]
    rw [Real.sq_sqrt hA]
    dsimp [A]
    ring

theorem ptr_scaled_dispersion_quadratic
    (c ε Ω R ω : ℝ) (ℓ m n : ℤ) :
    c ^ 2 * ((floquetSidebandAngularMomentum ℓ m n : ℝ)) ^ 2 -
      ε * R ^ 2 * (floquetSidebandFrequency ω Ω n) ^ 2 =
    (c ^ 2 * (m : ℝ) ^ 2 - ε * (Ω * R) ^ 2) * (n : ℝ) ^ 2 +
      2 * (c ^ 2 * (ℓ : ℝ) * (m : ℝ) - ε * R ^ 2 * ω * Ω) * (n : ℝ) +
      (c ^ 2 * (ℓ : ℝ) ^ 2 - ε * R ^ 2 * ω ^ 2) := by
  simp only [GaloisForLFunctions.HTGeometry.floquetSidebandAngularMomentum,
    GaloisForLFunctions.HTGeometry.floquetSidebandFrequency]
  push_cast
  ring

/-- At the largest modulation frequency displayed in the source paper, the
dimensionless rotation speed at the cylinder wall is `27π/200`. The maximal
real relative dielectric coefficient is `15`. -/
theorem ptr_paper_cylinder_strictly_inside_light_surface :
    (15 : ℝ) * ((27 : ℝ) / 200 * Real.pi) ^ 2 <
      ((299792458 : ℝ) / 100000000) ^ 2 := by
  have hpi : Real.pi < 4 := Real.pi_lt_four
  have hpi0 : 0 < Real.pi := Real.pi_pos
  have hv0 : 0 < (27 : ℝ) / 200 * Real.pi := by positivity
  have hv : (27 : ℝ) / 200 * Real.pi < 27 / 50 := by nlinarith
  have hc : (5 / 2 : ℝ) < (299792458 : ℝ) / 100000000 := by norm_num
  nlinarith [sq_nonneg ((27 : ℝ) / 200 * Real.pi), sq_nonneg ((299792458 : ℝ) / 100000000)]

/-- Exact nondimensionalization of the paper's largest displayed drive
`f=100 THz`, cylinder radius `R=270 nm`, and helicity `m=4`. -/
theorem ptr_paper_drive_wall_speed :
    ((2 * Real.pi * (100 * 10 ^ 12 : ℝ)) *
        (270 / 10 ^ 9 : ℝ) / 4) / (10 ^ 8 : ℝ) =
      (27 : ℝ) / 200 * Real.pi := by
  norm_num
  ring

noncomputable def ptrPaperDielectricReal (φ : ℝ) : ℝ :=
  (25 / 2) * (1 + (1 / 5) * Real.cos (4 * φ))

theorem ptrPaperDielectricReal_le_fifteen (φ : ℝ) :
    ptrPaperDielectricReal φ ≤ 15 := by
  unfold ptrPaperDielectricReal
  nlinarith [Real.cos_le_one (4 * φ)]

/-- Principal transmission conditions have no nonzero evanescent boundary
amplitude when both media lie inside the light surface. -/
theorem ptr_elliptic_interface_principal_kernel_zero
    (αin αout : ℝ) (hin : 0 < αin) (hout : 0 < αout)
    (ain aout : ℂ) (hvalue : ain = aout)
    (hflux : ((Real.sqrt αin : ℝ) : ℂ) * ain +
      ((Real.sqrt αout : ℝ) : ℂ) * aout = 0) :
    ain = 0 ∧ aout = 0 := by
  have hs : 0 < Real.sqrt αin + Real.sqrt αout :=
    add_pos (Real.sqrt_pos.2 hin) (Real.sqrt_pos.2 hout)
  have hs0 : (((Real.sqrt αin + Real.sqrt αout : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast ne_of_gt hs
  rw [← hvalue] at hflux
  have hmul : (((Real.sqrt αin + Real.sqrt αout : ℝ) : ℂ)) * ain = 0 := by
    push_cast
    linear_combination hflux
  have ha := (mul_eq_zero.mp hmul).resolve_left hs0
  exact ⟨ha, hvalue.symm.trans ha⟩

theorem ptr_paper_cylinder_principal_interface_kernel_zero
    (ain aout : ℂ) (hvalue : ain = aout)
    (hflux : ((Real.sqrt
        (((299792458 : ℝ) / 100000000) ^ 2 -
          15 * ((27 : ℝ) / 200 * Real.pi) ^ 2) : ℝ) : ℂ) * ain +
      ((Real.sqrt
        (((299792458 : ℝ) / 100000000) ^ 2 -
          ((27 : ℝ) / 200 * Real.pi) ^ 2) : ℝ) : ℂ) * aout = 0) :
    ain = 0 ∧ aout = 0 := by
  have hin : 0 < ((299792458 : ℝ) / 100000000) ^ 2 -
      15 * ((27 : ℝ) / 200 * Real.pi) ^ 2 :=
    sub_pos.mpr ptr_paper_cylinder_strictly_inside_light_surface
  have hout : 0 < ((299792458 : ℝ) / 100000000) ^ 2 -
      ((27 : ℝ) / 200 * Real.pi) ^ 2 := by
    nlinarith [sq_nonneg ((27 : ℝ) / 200 * Real.pi)]
  exact ptr_elliptic_interface_principal_kernel_zero _ _ hin hout
    ain aout hvalue hflux

/-- Uniform ellipticity for the actual angular dielectric profile at the
cylinder interface, not only its maximal value. -/
theorem ptr_paper_dielectric_helical_principal_pos
    (φ ξr ξφ : ℝ) (hξ : ξφ ≠ 0) :
    0 < ((299792458 : ℝ) / 100000000 * ξr) ^ 2 +
      (((299792458 : ℝ) / 100000000) ^ 2 -
        ptrPaperDielectricReal φ * ((27 : ℝ) / 200 * Real.pi) ^ 2) * ξφ ^ 2 := by
  have hv2 : 0 ≤ ((27 : ℝ) / 200 * Real.pi) ^ 2 := sq_nonneg _
  have hsub : ptrPaperDielectricReal φ * ((27 : ℝ) / 200 * Real.pi) ^ 2 <
      ((299792458 : ℝ) / 100000000) ^ 2 := by
    have hmax := ptr_paper_cylinder_strictly_inside_light_surface
    have hε := ptrPaperDielectricReal_le_fifteen φ
    nlinarith [mul_nonneg (sub_nonneg.mpr hε) hv2]
  have hpos : 0 < ξφ ^ 2 := sq_pos_of_ne_zero hξ
  have hrad : 0 ≤ ((299792458 : ℝ) / 100000000 * ξr) ^ 2 := sq_nonneg _
  nlinarith [mul_pos (sub_pos.mpr hsub) hpos]

end RHTower
