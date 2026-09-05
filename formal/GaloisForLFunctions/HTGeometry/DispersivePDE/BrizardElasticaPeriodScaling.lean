import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaPeriodNormalization
import Mathlib.Tactic

/-!
# Scaling laws for analytic Weierstrass data

This module supplies the homothety infrastructure absent from mathlib's current `PeriodPair` API.
Scaling a period lattice by a nonzero complex number transports its lattice points explicitly,
scales `G₄`, `G₆`, `g₂`, and `g₃` with weights `-4` and `-6`, and scales the analytic Weierstrass
function and derivative with weights `-2` and `-3`.  These are the scale laws behind the paper's
separation of the Jacobi shape parameter `m` from the curvature scale `q₀`.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

theorem scalePeriodPair_mul_mem_lattice (c : ℂˣ) (L : PeriodPair) (l : L.lattice) :
    (c : ℂ) * (l : ℂ) ∈ (scalePeriodPair c L).lattice := by
  obtain ⟨m, n, hmn⟩ := PeriodPair.mem_lattice.mp l.property
  rw [PeriodPair.mem_lattice]
  refine ⟨m, n, ?_⟩
  simp only [scalePeriodPair_ω₁, scalePeriodPair_ω₂]
  calc
    (m : ℂ) * ((c : ℂ) * L.ω₁) + (n : ℂ) * ((c : ℂ) * L.ω₂) =
        (c : ℂ) * ((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂) := by ring
    _ = (c : ℂ) * (l : ℂ) := by rw [hmn]

theorem scalePeriodPair_inv_mul_mem_lattice (c : ℂˣ) (L : PeriodPair)
    (l : (scalePeriodPair c L).lattice) :
    ((↑(c⁻¹) : ℂ) * (l : ℂ)) ∈ L.lattice := by
  obtain ⟨m, n, hmn⟩ := PeriodPair.mem_lattice.mp l.property
  rw [PeriodPair.mem_lattice]
  refine ⟨m, n, ?_⟩
  simp only [scalePeriodPair_ω₁, scalePeriodPair_ω₂] at hmn
  apply mul_left_cancel₀ c.ne_zero
  calc
    (c : ℂ) * ((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂) =
        (m : ℂ) * ((c : ℂ) * L.ω₁) + (n : ℂ) * ((c : ℂ) * L.ω₂) := by ring
    _ = (l : ℂ) := hmn
    _ = (c : ℂ) * ((↑(c⁻¹) : ℂ) * (l : ℂ)) := by simp

/-- Scaling gives an explicit equivalence of the old and new period lattices. -/
noncomputable def scaleLatticeEquiv (c : ℂˣ) (L : PeriodPair) :
    L.lattice ≃ (scalePeriodPair c L).lattice where
  toFun l := ⟨(c : ℂ) * (l : ℂ), scalePeriodPair_mul_mem_lattice c L l⟩
  invFun l := ⟨(↑(c⁻¹) : ℂ) * (l : ℂ), scalePeriodPair_inv_mul_mem_lattice c L l⟩
  left_inv l := by
    ext
    simp
  right_inv l := by
    ext
    simp

@[simp] theorem coe_scaleLatticeEquiv (c : ℂˣ) (L : PeriodPair) (l : L.lattice) :
    ((scaleLatticeEquiv c L l : (scalePeriodPair c L).lattice) : ℂ) =
      (c : ℂ) * (l : ℂ) := rfl

theorem scalePeriodPair_G_four (c : ℂˣ) (L : PeriodPair) :
    (scalePeriodPair c L).G 4 = (c : ℂ)⁻¹ ^ 4 * L.G 4 := by
  rw [PeriodPair.G, PeriodPair.G]
  rw [← (scaleLatticeEquiv c L).tsum_eq]
  calc
    ∑' l : L.lattice, (((c : ℂ) * (l : ℂ)) ^ 4)⁻¹ =
        ∑' l : L.lattice, (c : ℂ)⁻¹ ^ 4 * (((l : ℂ) ^ 4)⁻¹) := by
      apply tsum_congr
      intro l
      rw [mul_pow]
      by_cases hl : (l : ℂ) = 0
      · simp [hl]
      · field_simp
    _ = (c : ℂ)⁻¹ ^ 4 * ∑' l : L.lattice, (((l : ℂ) ^ 4)⁻¹) := by
      rw [tsum_mul_left]

theorem scalePeriodPair_G_six (c : ℂˣ) (L : PeriodPair) :
    (scalePeriodPair c L).G 6 = (c : ℂ)⁻¹ ^ 6 * L.G 6 := by
  rw [PeriodPair.G, PeriodPair.G]
  rw [← (scaleLatticeEquiv c L).tsum_eq]
  calc
    ∑' l : L.lattice, (((c : ℂ) * (l : ℂ)) ^ 6)⁻¹ =
        ∑' l : L.lattice, (c : ℂ)⁻¹ ^ 6 * (((l : ℂ) ^ 6)⁻¹) := by
      apply tsum_congr
      intro l
      rw [mul_pow]
      by_cases hl : (l : ℂ) = 0
      · simp [hl]
      · field_simp
    _ = (c : ℂ)⁻¹ ^ 6 * ∑' l : L.lattice, (((l : ℂ) ^ 6)⁻¹) := by
      rw [tsum_mul_left]

/-- The lattice invariant `g₂` has homogeneity weight `-4`. -/
theorem scalePeriodPair_g₂ (c : ℂˣ) (L : PeriodPair) :
    (scalePeriodPair c L).g₂ = (c : ℂ)⁻¹ ^ 4 * L.g₂ := by
  rw [PeriodPair.g₂, scalePeriodPair_G_four, PeriodPair.g₂]
  ring

/-- The lattice invariant `g₃` has homogeneity weight `-6`. -/
theorem scalePeriodPair_g₃ (c : ℂˣ) (L : PeriodPair) :
    (scalePeriodPair c L).g₃ = (c : ℂ)⁻¹ ^ 6 * L.g₃ := by
  rw [PeriodPair.g₃, scalePeriodPair_G_six, PeriodPair.g₃]
  ring

private theorem inv_sq_unit_mul (c : ℂˣ) (z : ℂ) :
    (((c : ℂ) * z) ^ 2)⁻¹ = (c : ℂ)⁻¹ ^ 2 * (z ^ 2)⁻¹ := by
  by_cases hz : z = 0
  · simp [hz]
  · field_simp

private theorem inv_cube_unit_mul (c : ℂˣ) (z : ℂ) :
    (((c : ℂ) * z) ^ 3)⁻¹ = (c : ℂ)⁻¹ ^ 3 * (z ^ 3)⁻¹ := by
  by_cases hz : z = 0
  · simp [hz]
  · field_simp

/-- Analytic `wp` has homogeneity weight `-2` under lattice scaling. -/
theorem scalePeriodPair_weierstrassP (c : ℂˣ) (L : PeriodPair) (z : ℂ) :
    (scalePeriodPair c L).weierstrassP ((c : ℂ) * z) =
      (c : ℂ)⁻¹ ^ 2 * L.weierstrassP z := by
  rw [PeriodPair.weierstrassP, PeriodPair.weierstrassP]
  rw [← (scaleLatticeEquiv c L).tsum_eq]
  calc
    ∑' l : L.lattice,
        (1 / ((c : ℂ) * z - (c : ℂ) * (l : ℂ)) ^ 2 -
          1 / ((c : ℂ) * (l : ℂ)) ^ 2) =
      ∑' l : L.lattice, (c : ℂ)⁻¹ ^ 2 *
        (1 / (z - (l : ℂ)) ^ 2 - 1 / (l : ℂ) ^ 2) := by
      apply tsum_congr
      intro l
      rw [show (c : ℂ) * z - (c : ℂ) * (l : ℂ) =
        (c : ℂ) * (z - (l : ℂ)) by ring]
      simp only [one_div]
      rw [inv_sq_unit_mul, inv_sq_unit_mul]
      ring
    _ = (c : ℂ)⁻¹ ^ 2 * ∑' l : L.lattice,
        (1 / (z - (l : ℂ)) ^ 2 - 1 / (l : ℂ) ^ 2) := by
      rw [tsum_mul_left]

/-- Analytic `wp'` has homogeneity weight `-3` under lattice scaling. -/
theorem scalePeriodPair_derivWeierstrassP (c : ℂˣ) (L : PeriodPair) (z : ℂ) :
    (scalePeriodPair c L).derivWeierstrassP ((c : ℂ) * z) =
      (c : ℂ)⁻¹ ^ 3 * L.derivWeierstrassP z := by
  rw [PeriodPair.derivWeierstrassP, PeriodPair.derivWeierstrassP]
  rw [← (scaleLatticeEquiv c L).tsum_eq]
  calc
    -(∑' l : L.lattice, 2 /
        ((c : ℂ) * z - (c : ℂ) * (l : ℂ)) ^ 3) =
      -(∑' l : L.lattice, (c : ℂ)⁻¹ ^ 3 *
        (2 / (z - (l : ℂ)) ^ 3)) := by
      congr 1
      apply tsum_congr
      intro l
      rw [show (c : ℂ) * z - (c : ℂ) * (l : ℂ) =
        (c : ℂ) * (z - (l : ℂ)) by ring]
      simp only [div_eq_mul_inv]
      rw [inv_cube_unit_mul]
      ring
    _ = (c : ℂ)⁻¹ ^ 3 *
        (-(∑' l : L.lattice, 2 / (z - (l : ℂ)) ^ 3)) := by
      rw [tsum_mul_left]
      ring

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
