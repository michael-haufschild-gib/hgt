import GaloisForLFunctions.HTGeometry.SharpReciprocalTailBounds

/-!
# A robust unit-circle chord bound from a phase-tail interval
-/

open scoped Matrix

namespace GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

/-- On `[0,1]`, the unit-circle chord is strictly larger than the cubic Taylor minorant. -/
theorem phase_chord_gt_sub_cube {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    x - x ^ (3 : ℕ) / 24 <
      ‖Complex.exp (-(Complex.I * (x : ℂ))) - 1‖ := by
  have hxhalf : 0 < x / 2 := by linarith
  have hsin := Real.sin_gt_sub_cube hxhalf
  have hsin0 : 0 < Real.sin (x / 2) := by
    have hsubpos : 0 < x / 2 - (x / 2) ^ (3 : ℕ) / 6 := by
      have hx0 : 0 < x := hx
      nlinarith [sq_nonneg x]
    linarith
  have hnorm := norm_expI_sub_eq x 0
  have hzero : Complex.exp (-((0 : ℝ) : ℂ) * Complex.I) = 1 := by norm_num
  rw [hzero, sub_zero] at hnorm
  have hshape : Complex.exp (-(Complex.I * (x : ℂ))) =
      Complex.exp (-((x : ℝ) : ℂ) * Complex.I) := by
    congr 1
    ring
  rw [hshape, hnorm, abs_of_pos hsin0]
  nlinarith

/-- The cubic minorant `x - x³/24` is increasing on `[0,1]`. -/
theorem sub_cube_div_twentyfour_mono_on_unit {x y : ℝ}
    (hx0 : 0 ≤ x) (hxy : x ≤ y) (hy1 : y ≤ 1) :
    x - x ^ (3 : ℕ) / 24 ≤ y - y ^ (3 : ℕ) / 24 := by
  have hy0 : 0 ≤ y := le_trans hx0 hxy
  have hx1 : x ≤ 1 := hxy.trans hy1
  have hxx0 : 0 ≤ x * (1 - x) := mul_nonneg hx0 (sub_nonneg.mpr hx1)
  have hyy0 : 0 ≤ y * (1 - y) := mul_nonneg hy0 (sub_nonneg.mpr hy1)
  have hxx : x * x ≤ 1 := by nlinarith
  have hxy_le_x : x * y ≤ x := by nlinarith
  have hxy1 : x * y ≤ 1 := hxy_le_x.trans hx1
  have hyy : y * y ≤ 1 := by nlinarith
  have hcoef : 0 ≤ 24 - (y * y + y * x + x * x) := by nlinarith
  have hgap : 0 ≤ y - x := sub_nonneg.mpr hxy
  have hprod := mul_nonneg hgap hcoef
  nlinarith [show y ^ (3 : ℕ) - x ^ (3 : ℕ) = (y - x) * (y * y + y * x + x * x) by ring]

/-- If every possible residual phase lies between a certified small tail and `3π/2`, its chord
stays above `4ε`.  This is the analytic interval lemma used by the explicit monotonicity
counterexample. -/
theorem phase_chord_gt_four_mul_of_tail_interval {tau phi ε : ℝ}
    (htau0 : 0 < tau)
    (htauphi : tau ≤ phi) (hphi : phi < 3 * Real.pi / 2)
    (hcubic : 4 * ε < tau - tau ^ (3 : ℕ) / 24)
    (hsmall : 4 * ε < 1 / 2) :
    4 * ε < ‖Complex.exp (-(Complex.I * (phi : ℂ))) - 1‖ := by
  have hphi0 : 0 < phi := lt_of_lt_of_le htau0 htauphi
  by_cases hphi1 : phi ≤ 1
  · have hmono := sub_cube_div_twentyfour_mono_on_unit htau0.le htauphi hphi1
    have hchord := phase_chord_gt_sub_cube hphi0 hphi1
    linarith
  · have hphi1' : 1 < phi := lt_of_not_ge hphi1
    by_cases hphipi : phi ≤ Real.pi
    · have hchord := phase_chord_lower hphi0.le hphipi
      have hpi4 : Real.pi < 4 := Real.pi_lt_four
      have hhalf : (1 / 2 : ℝ) < 2 * phi / Real.pi := by
        rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 2) Real.pi_pos]
        nlinarith
      linarith
    · have hpilt : Real.pi < phi := lt_of_not_ge hphipi
      let psi := 2 * Real.pi - phi
      have hpsi0 : 0 < psi := by
        dsimp [psi]
        nlinarith [Real.pi_pos]
      have hpsipi : psi ≤ Real.pi := by
        dsimp [psi]
        linarith
      have hpsihalf : Real.pi / 2 < psi := by
        dsimp [psi]
        linarith
      have hreflect :
          ‖Complex.exp (-(Complex.I * (phi : ℂ))) - 1‖ =
            ‖Complex.exp (-(Complex.I * (psi : ℂ))) - 1‖ := by
        have hexp : Complex.exp (-(Complex.I * (phi : ℂ))) =
            Complex.exp (Complex.I * (psi : ℂ)) := by
          rw [show -(Complex.I * (phi : ℂ)) =
              Complex.I * (psi : ℂ) - Complex.I * ((2 * Real.pi : ℝ) : ℂ) by
                dsimp [psi]
                push_cast
                ring]
          rw [Complex.exp_sub]
          have hperiod : Complex.exp (Complex.I * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
            rw [show Complex.I * ((2 * Real.pi : ℝ) : ℂ) =
              ((2 * Real.pi : ℝ) : ℂ) * Complex.I by ring]
            rw [Complex.exp_mul_I]
            simp
          rw [hperiod, div_one]
        rw [hexp]
        have hconj : Complex.exp (-(Complex.I * (psi : ℂ))) =
            starRingEnd ℂ (Complex.exp (Complex.I * (psi : ℂ))) := by
          rw [← Complex.exp_conj]
          congr 1
          simp
        calc
          ‖Complex.exp (Complex.I * (psi : ℂ)) - 1‖ =
              ‖starRingEnd ℂ (Complex.exp (Complex.I * (psi : ℂ)) - 1)‖ :=
                (norm_star _).symm
          _ = ‖Complex.exp (-(Complex.I * (psi : ℂ))) - 1‖ := by
            rw [map_sub, map_one, ← hconj]
      have hchord := phase_chord_lower hpsi0.le hpsipi
      have hone : 1 < 2 * psi / Real.pi := by
        rw [lt_div_iff₀ Real.pi_pos]
        linarith
      rw [hreflect]
      linarith

end GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw
