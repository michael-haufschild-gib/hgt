import GaloisForLFunctions.RHTower.EulerDeletionRamareDilation

/-!
# Physical energy scaling for Euler-deletion Ramaré dilations

The physical reciprocal dilation has an exact bilinear energy law.  Its
lower edge moves from `1` to `1 / p`; for Ramaré cofactors that edge is later
removed only after proving their literal support.  This module records the
change of variables itself, without replacing the physical carrier by an
unweighted spectral norm.
-/

noncomputable section

open MeasureTheory Set

namespace RHTower.DeletionRamareDilation

/-- Exact physical bilinear scaling for a reciprocal dilation. -/
theorem integral_dilate_mul (p : ℕ) (hp : 0 < p) (f g : ℝ → ℝ) :
    (∫ u in Ioi (1 : ℝ), dilate p f u * dilate p g u) =
      (1 / (p : ℝ)) * ∫ v in Ioi (1 / (p : ℝ)), f v * g v := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  change (∫ u in Ioi (1 : ℝ),
      ((1 / (p : ℝ)) * f (u / (p : ℝ))) *
        ((1 / (p : ℝ)) * g (u / (p : ℝ)))) =
      (1 / (p : ℝ)) * ∫ v in Ioi (1 / (p : ℝ)), f v * g v
  calc
    _ = (1 / (p : ℝ)) ^ 2 *
        (∫ u in Ioi (1 : ℝ), f (u / (p : ℝ)) * g (u / (p : ℝ))) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      ring
    _ = (1 / (p : ℝ)) ^ 2 *
        (∫ u in Ioi (1 : ℝ), f ((p : ℝ)⁻¹ * u) * g ((p : ℝ)⁻¹ * u)) := by
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      have hu : u / (p : ℝ) = (p : ℝ)⁻¹ * u := by
        field_simp [hpR.ne']
      change f (u / (p : ℝ)) * g (u / (p : ℝ)) =
        f ((p : ℝ)⁻¹ * u) * g ((p : ℝ)⁻¹ * u)
      rw [hu]
    _ = (1 / (p : ℝ)) * ∫ v in Ioi (1 / (p : ℝ)), f v * g v := by
      have hscale := integral_comp_mul_left_Ioi (fun v : ℝ => f v * g v) 1
        (inv_pos.mpr hpR)
      rw [hscale]
      simp only [smul_eq_mul, mul_one, one_div]
      field_simp [hpR.ne']

/-- Exact physical covariance of two reciprocal dilations with different
scales.  The surviving kernel records their rational resonance; no absolute
value or componentwise estimate has been taken. -/
theorem integral_dilate_mul_unequal (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (f g : ℝ → ℝ) :
    (∫ u in Ioi (1 : ℝ), dilate p f u * dilate q g u) =
      (1 / (q : ℝ)) * ∫ v in Ioi (1 / (p : ℝ)),
        f v * g (((p : ℝ) / (q : ℝ)) * v) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  change (∫ u in Ioi (1 : ℝ),
      ((1 / (p : ℝ)) * f (u / (p : ℝ))) *
        ((1 / (q : ℝ)) * g (u / (q : ℝ)))) = _
  calc
    _ = ((1 / (p : ℝ)) * (1 / (q : ℝ))) *
        (∫ u in Ioi (1 : ℝ), f (u / (p : ℝ)) * g (u / (q : ℝ))) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      ring
    _ = ((1 / (p : ℝ)) * (1 / (q : ℝ))) *
        (∫ u in Ioi (1 : ℝ),
          (fun v => f v * g (((p : ℝ) / (q : ℝ)) * v)) ((p : ℝ)⁻¹ * u)) := by
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      have huP : u / (p : ℝ) = (p : ℝ)⁻¹ * u := by
        field_simp [hpR.ne']
      have huQ : u / (q : ℝ) = ((p : ℝ) / (q : ℝ)) * ((p : ℝ)⁻¹ * u) := by
        field_simp [hpR.ne', hqR.ne']
      change f (u / (p : ℝ)) * g (u / (q : ℝ)) =
        f ((p : ℝ)⁻¹ * u) * g (((p : ℝ) / (q : ℝ)) * ((p : ℝ)⁻¹ * u))
      rw [huP, huQ]
    _ = ((1 / (p : ℝ)) * (1 / (q : ℝ))) *
        ((p : ℝ) * ∫ v in Ioi (1 / (p : ℝ)),
          f v * g (((p : ℝ) / (q : ℝ)) * v)) := by
      congr 1
      have hscale := integral_comp_mul_left_Ioi
        (fun v : ℝ => f v * g (((p : ℝ) / (q : ℝ)) * v)) 1
        (inv_pos.mpr hpR)
      rw [inv_inv] at hscale
      simpa only [smul_eq_mul, mul_one, one_div] using hscale
    _ = _ := by
      field_simp [hpR.ne', hqR.ne']

/-- Diagonal form of `integral_dilate_mul`. -/
theorem integral_dilate_sq (p : ℕ) (hp : 0 < p) (f : ℝ → ℝ) :
    (∫ u in Ioi (1 : ℝ), dilate p f u ^ 2) =
      (1 / (p : ℝ)) * ∫ v in Ioi (1 / (p : ℝ)), f v ^ 2 := by
  simpa [pow_two] using integral_dilate_mul p hp f f

/-- Every generator with parameter in `[0, 1]` vanishes below the physical
unit boundary. -/
theorem bdGenReal_eq_zero_of_mem_Ioo_one {theta u : ℝ}
    (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1) (hu : u ∈ Ioo (0 : ℝ) 1) :
    bdGenReal theta u = 0 := by
  have hthetaU0 : 0 ≤ theta * u := mul_nonneg htheta0 hu.1.le
  have hthetaU1 : theta * u < 1 := by
    have hle : theta * u ≤ 1 * u := mul_le_mul_of_nonneg_right htheta1 hu.1.le
    have hu1 : 1 * u < 1 := by simpa only [one_mul] using hu.2
    exact hle.trans_lt hu1
  have hfractTheta : Int.fract (theta * u) = theta * u :=
    Int.fract_eq_self.mpr ⟨hthetaU0, hthetaU1⟩
  have hfractU : Int.fract u = u := Int.fract_eq_self.mpr ⟨hu.1.le, hu.2⟩
  rw [bdGenReal, hfractTheta, hfractU]
  ring

end RHTower.DeletionRamareDilation
