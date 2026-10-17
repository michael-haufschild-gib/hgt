import GaloisForLFunctions.BiScaleUncertainty.InfiniteCoprimeTraceProjection
import Mathlib.Data.Int.GCD

/-!+# Cross-family tent geometry

Integer tents interact exactly at coincident or adjacent centers. A common divisor
greater than one excludes the latter, making projection a coefficient restriction.+-/

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear

theorem inner_tentVelocity_cross (d e i j : ℕ) :
    ⟪tentVelocity d i, tentVelocity e j⟫ =
      if coprimeCenter d i = coprimeCenter e j then 2
      else if coprimeCenter d i + 1 = coprimeCenter e j ∨
          coprimeCenter e j + 1 = coprimeCenter d i then -1 else 0 := by
  have ha := coprimeCenter_ge_two d i
  have hb := coprimeCenter_ge_two e j
  simp only [tentVelocity, inner_sub_left, inner_sub_right, inner_unitCell]
  split_ifs <;> norm_num <;> omega

/-- The actual infinite orthogonal projection, bundled for continuity and adjoints. -/
def coprimeProjector (d : ℕ) : Velocity →L[ℝ] Velocity :=
  (tentSynthesis d).toContinuousLinearMap.comp (tentAnalysis d)

@[simp]
theorem coprimeProjector_apply (d : ℕ) (q : Velocity) :
    coprimeProjector d q = coprimeProjection d q := rfl

@[simp]
theorem coprimeProjector_adjoint (d : ℕ) :
    (coprimeProjector d).adjoint = coprimeProjector d := by
  simp [coprimeProjector, tentAnalysis, ContinuousLinearMap.adjoint_comp]

theorem coprimeExtension_single (d j : ℕ) (a : ℝ) :
    coprimeExtension d (lp.single 2 j a) = a • tentVelocity d j := by
  have hs : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  simp only [coprimeExtension, map_smul, tentSynthesis_single, normalizedTent, smul_smul]
  congr 1
  field_simp

theorem coprimeProjection_tent_self (d j : ℕ) :
    coprimeProjection d (tentVelocity d j) = tentVelocity d j := by
  apply (coprimeProjection_eq_self_iff d _).2
  exact ⟨lp.single 2 j 1, by simp [coprimeExtension_single]⟩

/-- Agreement on tents extends through the convergent Hilbert series. -/
theorem map_coprimeExtension_eq (d : ℕ) (A B : Velocity →L[ℝ] Velocity)
    (h : ∀ j, A (tentVelocity d j) = B (tentVelocity d j)) (v : TraceData) :
    A (coprimeExtension d v) = B (coprimeExtension d v) := by
  apply (A.hasSum (hasSum_coprimeExtension d v)).unique
  apply (B.hasSum (hasSum_coprimeExtension d v)).congr_fun
  intro j
  simp only [map_smul, h]

theorem comp_coprimeProjector_eq (d : ℕ) (A B : Velocity →L[ℝ] Velocity)
    (h : ∀ j, A (tentVelocity d j) = B (tentVelocity d j)) :
    A.comp (coprimeProjector d) = B.comp (coprimeProjector d) := by
  apply ContinuousLinearMap.ext
  intro q
  change A (coprimeProjection d q) = B (coprimeProjection d q)
  rw [coprimeProjection_eq_extension]
  exact map_coprimeExtension_eq d A B h _

theorem coprimeCenter_dvd (d j : ℕ) : d + 2 ∣ coprimeCenter d j :=
  Nat.dvd_mul_right _ _

theorem coprimeCenter_index {d a : ℕ} (ha : 0 < a) (hd : d + 2 ∣ a) :
    coprimeCenter d (a / (d + 2) - 1) = a := by
  obtain ⟨k, rfl⟩ := hd
  have hk : 0 < k := by nlinarith
  simp [coprimeCenter, Nat.sub_add_cancel hk]

theorem coprimeProjection_tent_of_dvd (d e j : ℕ)
    (h : d + 2 ∣ coprimeCenter e j) :
    coprimeProjection d (tentVelocity e j) = tentVelocity e j := by
  have hc := coprimeCenter_index (by have := coprimeCenter_ge_two e j; omega) h
  have ht : tentVelocity e j = tentVelocity d (coprimeCenter e j / (d + 2) - 1) := by
    simp only [tentVelocity, hc]
  rw [ht, coprimeProjection_tent_self]

theorem not_adjacent_of_common_divisor {a b g : ℕ}
    (hg : 2 ≤ g) (ha : g ∣ a) (hb : g ∣ b) : a + 1 ≠ b := by
  intro hab
  have h : g ∣ 1 := (Nat.dvd_add_iff_right ha).2 (hab ▸ hb)
  have := Nat.dvd_one.mp h
  omega

theorem coprimeProjection_tent_of_common_divisor (d e j g : ℕ)
    (hg : 2 ≤ g) (hd : g ∣ d + 2) (he : g ∣ e + 2) :
    coprimeProjection d (tentVelocity e j) =
      if d + 2 ∣ coprimeCenter e j then tentVelocity e j else 0 := by
  split_ifs with h
  · exact coprimeProjection_tent_of_dvd d e j h
  · have hz : tentAnalysis d (tentVelocity e j) = 0 := by
      apply lp.ext
      funext i
      have hi := hd.trans (coprimeCenter_dvd d i)
      have hj := he.trans (coprimeCenter_dvd e j)
      have hne : coprimeCenter d i ≠ coprimeCenter e j := by
        intro hc
        exact h (hc ▸ coprimeCenter_dvd d i)
      have hab := not_adjacent_of_common_divisor hg hi hj
      have hba := not_adjacent_of_common_divisor hg hj hi
      simp [tentAnalysis_apply, ← inner_tentVelocity_velocity, inner_tentVelocity_cross,
        hne, hab, hba]
    simp [coprimeProjection, hz]

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
