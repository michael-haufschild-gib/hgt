import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCenterTailRepresentation

/-!
# Convex aperture payment for two theta atoms

The hyperbolic aperture weight is increasing and midpoint-convex on the positive
half-line. Its clipped translates pay a damped cross term by two diagonal terms.
-/

set_option autoImplicit false

open Set
open RHTower

namespace GaloisForLFunctions.CompletedArithmeticForms

theorem thetaCenterTailWeight_superadd {a u v : ℝ}
    (ha : 0 ≤ a) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    thetaCuspCenterTailWeight a u + thetaCuspCenterTailWeight a v ≤
      thetaCuspCenterTailWeight a (u + v) := by
  have hxu : 0 ≤ a * u := mul_nonneg ha hu
  have hxv : 0 ≤ a * v := mul_nonneg ha hv
  have hsu : 0 ≤ Real.sinh (a * u) := Real.sinh_nonneg_iff.mpr hxu
  have hsv : 0 ≤ Real.sinh (a * v) := Real.sinh_nonneg_iff.mpr hxv
  have hcu : 0 ≤ Real.cosh (a * u) - 1 := sub_nonneg.mpr (Real.one_le_cosh _)
  have hcv : 0 ≤ Real.cosh (a * v) - 1 := sub_nonneg.mpr (Real.one_le_cosh _)
  have he : thetaCuspCenterTailWeight a (u + v) - thetaCuspCenterTailWeight a u -
      thetaCuspCenterTailWeight a v =
      Real.sinh (a * u) * (Real.cosh (a * v) - 1) +
      Real.sinh (a * v) * (Real.cosh (a * u) - 1) +
      (a * u) * Real.cosh (a * u) * (Real.cosh (a * v) - 1) +
      (a * v) * Real.cosh (a * v) * (Real.cosh (a * u) - 1) +
      (a * u + a * v) * Real.sinh (a * u) * Real.sinh (a * v) := by
    unfold thetaCuspCenterTailWeight
    rw [mul_add, Real.sinh_add, Real.cosh_add]
    ring
  have hn : 0 ≤ thetaCuspCenterTailWeight a (u + v) - thetaCuspCenterTailWeight a u -
      thetaCuspCenterTailWeight a v := by rw [he]; positivity
  linarith only [hn]

theorem thetaCenterTailWeight_mono {a u v : ℝ}
    (ha : 0 ≤ a) (hu : 0 ≤ u) (huv : u ≤ v) :
    thetaCuspCenterTailWeight a u ≤ thetaCuspCenterTailWeight a v := by
  have h := thetaCenterTailWeight_superadd ha hu (sub_nonneg.mpr huv)
  rw [show u + (v - u) = v by ring] at h
  exact (le_add_of_nonneg_right (thetaCuspCenterTailWeight_nonneg ha (sub_nonneg.mpr huv))).trans h

theorem thetaCenterTailWeight_midpoint {a u h : ℝ}
    (ha : 0 ≤ a) (hu : 0 ≤ u) (hh : 0 ≤ h) :
    2 * thetaCuspCenterTailWeight a u ≤
      thetaCuspCenterTailWeight a (u + h) + thetaCuspCenterTailWeight a (u - h) := by
  have hsu : 0 ≤ Real.sinh (a * u) := Real.sinh_nonneg_iff.mpr (mul_nonneg ha hu)
  have hsh : 0 ≤ Real.sinh (a * h) := Real.sinh_nonneg_iff.mpr (mul_nonneg ha hh)
  have hch : 0 ≤ Real.cosh (a * h) - 1 := sub_nonneg.mpr (Real.one_le_cosh _)
  have hw := thetaCuspCenterTailWeight_nonneg ha hu
  have he : thetaCuspCenterTailWeight a (u + h) + thetaCuspCenterTailWeight a (u - h) -
      2 * thetaCuspCenterTailWeight a u =
      2 * (Real.cosh (a * h) - 1) * thetaCuspCenterTailWeight a u +
        2 * (a * h) * Real.sinh (a * u) * Real.sinh (a * h) := by
    unfold thetaCuspCenterTailWeight
    rw [mul_add, mul_sub, Real.sinh_add, Real.sinh_sub, Real.cosh_add, Real.cosh_sub]
    ring
  have hn : 0 ≤ thetaCuspCenterTailWeight a (u + h) + thetaCuspCenterTailWeight a (u - h) -
      2 * thetaCuspCenterTailWeight a u := by rw [he]; positivity
  linarith only [hn]

theorem thetaCenterTailWeight_le_positivePart {a r : ℝ} (ha : 0 ≤ a) :
    thetaCuspCenterTailWeight a r ≤ thetaCuspCenterTailWeight a (max 0 r) := by
  by_cases hr : 0 ≤ r
  · rw [max_eq_right hr]
  · rw [max_eq_left (le_of_not_ge hr)]
    have har : a * r ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha (le_of_not_ge hr)
    have hs : Real.sinh (a * r) ≤ 0 := Real.sinh_nonpos_iff.mpr har
    have hc := mul_nonpos_of_nonpos_of_nonneg har (Real.cosh_pos (a * r)).le
    simp only [thetaCuspCenterTailWeight, mul_zero, Real.sinh_zero, Real.cosh_zero, zero_mul,
      add_zero]
    exact add_nonpos hs hc

/-- The two diagonal aperture weights pay a damped midpoint cross term. -/
theorem thetaCenterTailWeight_two_atom_payment {a h s p : ℝ}
    (ha : 0 ≤ a) (hh : 0 ≤ h) (hs : 0 ≤ s) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    2 * p * thetaCuspCenterTailWeight a (max 0 (s - h)) ≤
      thetaCuspCenterTailWeight a s + p ^ 2 * thetaCuspCenterTailWeight a (max 0 (s - 2 * h)) := by
  by_cases hsh : s ≤ h
  · rw [max_eq_left (sub_nonpos.mpr hsh)]
    simp only [thetaCuspCenterTailWeight, mul_zero, Real.sinh_zero, Real.cosh_zero,
      zero_mul, add_zero]
    have h1 := thetaCuspCenterTailWeight_nonneg ha hs
    have h2 := thetaCuspCenterTailWeight_nonneg ha (le_max_left 0 (s - 2 * h))
    change 0 ≤ thetaCuspCenterTailWeight a s + p ^ 2 * thetaCuspCenterTailWeight a (max 0 (s - 2 * h))
    positivity
  · have hmid : 2 * thetaCuspCenterTailWeight a (s - h) ≤
        thetaCuspCenterTailWeight a s + thetaCuspCenterTailWeight a (max 0 (s - 2 * h)) := by
      have ht := thetaCenterTailWeight_midpoint ha (sub_nonneg.mpr (le_of_not_ge hsh)) hh
      rw [sub_add_cancel, show s - h - h = s - 2 * h by ring] at ht
      exact ht.trans (add_le_add le_rfl (thetaCenterTailWeight_le_positivePart ha))
    have hV : 0 ≤ thetaCuspCenterTailWeight a (max 0 (s - 2 * h)) :=
      thetaCuspCenterTailWeight_nonneg ha (le_max_left _ _)
    have hVU : thetaCuspCenterTailWeight a (max 0 (s - 2 * h)) ≤ thetaCuspCenterTailWeight a s :=
      thetaCenterTailWeight_mono ha (le_max_left _ _)
        (max_le hs (by linarith only [hh]))
    have hpV : p * thetaCuspCenterTailWeight a (max 0 (s - 2 * h)) ≤ thetaCuspCenterTailWeight a s :=
      (mul_le_of_le_one_left hV hp1).trans hVU
    have hn := mul_nonneg (sub_nonneg.mpr hp1) (sub_nonneg.mpr hpV)
    rw [max_eq_right (sub_nonneg.mpr (le_of_not_ge hsh))]
    calc
      _ ≤ p * (thetaCuspCenterTailWeight a s + thetaCuspCenterTailWeight a (max 0 (s - 2 * h))) := by
        have ht := mul_le_mul_of_nonneg_left hmid hp
        linarith only [ht]
      _ ≤ _ := by nlinarith only [hn]

#print axioms thetaCenterTailWeight_two_atom_payment

end GaloisForLFunctions.CompletedArithmeticForms
