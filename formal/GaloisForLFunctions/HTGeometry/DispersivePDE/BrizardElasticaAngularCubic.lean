import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaCylindricalGap
import Mathlib.Tactic

/-!
# Angular Weierstrass cubic reduction

The algebraic reduction used before the paper's sigma/zeta angular integration is isolated from the
unavailable special-function layer.  For parameters whose reconstructed speed and torsion squares
are nonnegative, the angular ratio lies in `[0,1)`, satisfies the stated torsion relation, and makes
the shifted `e₃` evaluation of the Weierstrass cubic collapse to the paper's negative square.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

/-- Parameters for which the paper's reconstructed `γ²` and `ν²` are genuine squares. -/
abbrev AngularPhysicalParameters :=
  {P : Parameters // 0 ≤ gammaSq P ∧ 0 ≤ nuSq P}

noncomputable def angularOmegaSq (P : AngularPhysicalParameters) : ℝ :=
  4 * nuSq P.val / ((2 + gammaSq P.val) ^ 2 + 4 * nuSq P.val)

theorem angularOmegaSq_den_pos (P : AngularPhysicalParameters) :
    0 < (2 + gammaSq P.val) ^ 2 + 4 * nuSq P.val := by
  have hbase : 0 < 2 + gammaSq P.val := by linarith [P.property.1]
  nlinarith [sq_pos_of_pos hbase, P.property.2]

theorem angularOmegaSq_nonneg (P : AngularPhysicalParameters) :
    0 ≤ angularOmegaSq P := by
  rw [angularOmegaSq]
  exact div_nonneg (mul_nonneg (by norm_num) P.property.2)
    (angularOmegaSq_den_pos P).le

theorem angularOmegaSq_lt_one (P : AngularPhysicalParameters) :
    angularOmegaSq P < 1 := by
  rw [angularOmegaSq, div_lt_one (angularOmegaSq_den_pos P)]
  have hbase : 0 < (2 + gammaSq P.val) ^ 2 :=
    sq_pos_of_pos (by linarith [P.property.1])
  linarith

theorem one_sub_angularOmegaSq (P : AngularPhysicalParameters) :
    1 - angularOmegaSq P =
      (2 + gammaSq P.val) ^ 2 /
        ((2 + gammaSq P.val) ^ 2 + 4 * nuSq P.val) := by
  rw [angularOmegaSq]
  field_simp [ne_of_gt (angularOmegaSq_den_pos P)]
  ring

/-- Torsion relation quoted in the angular derivation. -/
theorem angular_nuSq_relation (P : AngularPhysicalParameters) :
    nuSq P.val = angularOmegaSq P / (1 - angularOmegaSq P) *
      (1 + gammaSq P.val / 2) ^ 2 := by
  rw [div_mul_eq_mul_div]
  have hone : 1 - angularOmegaSq P ≠ 0 := by
    linarith [angularOmegaSq_lt_one P]
  apply (eq_div_iff hone).2
  rw [one_sub_angularOmegaSq, angularOmegaSq]
  have hden := ne_of_gt (angularOmegaSq_den_pos P)
  field_simp [hden]
  ring

theorem e₃_eq_neg_one_sub_gammaSq_div_three (P : Parameters) :
    e₃ P = -1 - gammaSq P / 3 := by
  rw [e₃, gammaSq]
  field_simp [P.q₀.ne_zero]
  ring

/-- Intermediate invariant identity used in the cubic expansion. -/
theorem twelve_e₃_sq_sub_g₂ (P : Parameters) :
    12 * e₃ P ^ 2 - g₂ P = 4 * P.modulus / (P.q₀ : ℝ) ^ 2 := by
  rw [e₃, g₂]
  field_simp [P.q₀.ne_zero]
  ring

theorem twelve_e₃_sq_sub_g₂_parameters (P : Parameters) :
    12 * e₃ P ^ 2 - g₂ P = 8 + 4 * (gammaSq P - nuSq P) := by
  rw [twelve_e₃_sq_sub_g₂, gammaSq, nuSq]
  field_simp [P.q₀.ne_zero]
  ring

/-- Cubic collapse driving the paper's angular quadrature. -/
theorem angular_shifted_e₃_cubic (P : AngularPhysicalParameters) :
    4 * (e₃ P.val + (1 - angularOmegaSq P)) ^ 3 -
        g₂ P.val * (e₃ P.val + (1 - angularOmegaSq P)) - g₃ P.val =
      -4 * angularOmegaSq P *
        (angularOmegaSq P + gammaSq P.val / 2) ^ 2 := by
  calc
    4 * (e₃ P.val + (1 - angularOmegaSq P)) ^ 3 -
          g₂ P.val * (e₃ P.val + (1 - angularOmegaSq P)) - g₃ P.val =
        (4 * e₃ P.val ^ 3 - g₂ P.val * e₃ P.val - g₃ P.val) +
          (1 - angularOmegaSq P) *
            (12 * e₃ P.val ^ 2 - g₂ P.val +
              12 * e₃ P.val * (1 - angularOmegaSq P) +
              4 * (1 - angularOmegaSq P) ^ 2) := by ring
    _ = (1 - angularOmegaSq P) *
          (12 * e₃ P.val ^ 2 - g₂ P.val +
            12 * e₃ P.val * (1 - angularOmegaSq P) +
            4 * (1 - angularOmegaSq P) ^ 2) := by
      rw [e₃_root]
      ring
    _ = 4 * (1 - angularOmegaSq P) *
          (-nuSq P.val + angularOmegaSq P *
            (1 + gammaSq P.val + angularOmegaSq P)) := by
      rw [twelve_e₃_sq_sub_g₂_parameters,
        e₃_eq_neg_one_sub_gammaSq_div_three]
      ring
    _ = -4 * angularOmegaSq P *
          (angularOmegaSq P + gammaSq P.val / 2) ^ 2 := by
      rw [angular_nuSq_relation]
      have hne : 1 - angularOmegaSq P ≠ 0 := by
        linarith [angularOmegaSq_lt_one P]
      field_simp [hne]
      ring

theorem angular_shifted_e₃_cubic_nonpos (P : AngularPhysicalParameters) :
    4 * (e₃ P.val + (1 - angularOmegaSq P)) ^ 3 -
        g₂ P.val * (e₃ P.val + (1 - angularOmegaSq P)) - g₃ P.val ≤ 0 := by
  rw [angular_shifted_e₃_cubic]
  nlinarith [angularOmegaSq_nonneg P,
    sq_nonneg (angularOmegaSq P + gammaSq P.val / 2)]

theorem angular_shifted_e₃_cubic_eq_zero_iff (P : AngularPhysicalParameters) :
    4 * (e₃ P.val + (1 - angularOmegaSq P)) ^ 3 -
        g₂ P.val * (e₃ P.val + (1 - angularOmegaSq P)) - g₃ P.val = 0 ↔
      nuSq P.val = 0 := by
  have hΩzero : angularOmegaSq P = 0 ↔ nuSq P.val = 0 := by
    rw [angularOmegaSq, div_eq_zero_iff]
    simp [ne_of_gt (angularOmegaSq_den_pos P)]
  constructor
  · rw [angular_shifted_e₃_cubic]
    intro h
    have hproduct : angularOmegaSq P *
        (angularOmegaSq P + gammaSq P.val / 2) ^ 2 = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hproduct with hΩ | hsum
    · exact hΩzero.mp hΩ
    · have hsumzero : angularOmegaSq P + gammaSq P.val / 2 = 0 :=
        sq_eq_zero_iff.mp hsum
      apply hΩzero.mp
      nlinarith [angularOmegaSq_nonneg P, P.property.1]
  · intro h
    rw [angular_shifted_e₃_cubic, hΩzero.mpr h]
    ring

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
