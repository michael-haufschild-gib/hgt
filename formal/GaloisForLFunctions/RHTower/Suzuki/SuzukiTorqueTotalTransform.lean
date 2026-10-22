import GaloisForLFunctions.RHTower.Suzuki.SuzukiTorquePrimeOrder

/-!
# `(14)`: the complete torque transform

Adding the two layers: the archimedean part transforms to an explicit rational function, the prime
part to the logarithmically weighted filtered Mangoldt series, and their sum is the card's `(14)`.
The only analytic input beyond the two transforms is integrability of the prime layer, which the
exponential-order bound `(17)` supplies — on the unit window by continuity, past it by the majorant
`L³e^{-(σ−3/2)L}`.
-/

open MeasureTheory Set

noncomputable section

namespace RHTower

theorem integrableOn_pow_mul_exp_neg_linear {k : ℕ} {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun L : ℝ => L ^ k * Real.exp (-r * L)) (Ioi 0) := by
  have h := GaloisForLFunctions.HTGeometry.integrableOn_rpow_mul_exp_neg_mul_Ioi
    (σ := (k : ℝ)) (a := r) (by
      have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith) hr
  refine h.congr_fun (fun u hu => ?_) measurableSet_Ioi
  have hu0 : (0 : ℝ) < u := hu
  show u ^ (k : ℝ) * Real.exp (-(r * u)) = u ^ k * Real.exp (-r * u)
  rw [Real.rpow_natCast, neg_mul]

/-- The prime layer is Laplace integrable to the right of `3/2`. -/
theorem integrableOn_suzukiFreePrimePositionTorque_mul_exp {σ : ℝ} (hσ : 3 / 2 < σ) :
    IntegrableOn (fun L : ℝ => suzukiFreePrimePositionTorque L * Real.exp (-σ * L)) (Ioi 0) := by
  have hcont : Continuous fun L : ℝ => suzukiFreePrimePositionTorque L * Real.exp (-σ * L) :=
    continuous_suzukiFreePrimePositionTorque.mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have hsplit : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 :=
    (Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)).symm
  have hnear : IntegrableOn
      (fun L : ℝ => suzukiFreePrimePositionTorque L * Real.exp (-σ * L)) (Ioc 0 1) :=
    (hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hfar : IntegrableOn
      (fun L : ℝ => suzukiFreePrimePositionTorque L * Real.exp (-σ * L)) (Ioi 1) := by
    have hr : (0 : ℝ) < σ - 3 / 2 := by linarith
    have hdom : IntegrableOn
        (fun L : ℝ => 1 / 2 * (L ^ 3 * Real.exp (-(σ - 3 / 2) * L))) (Ioi 1) :=
      ((integrableOn_pow_mul_exp_neg_linear (k := 3) hr).mono_set
        (Ioi_subset_Ioi (by norm_num))).const_mul _
    refine Integrable.mono' hdom hcont.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with L hL
    have hL1 : (1 : ℝ) < L := hL
    have hP := suzukiFreePrimePositionTorque_le (le_of_lt hL1)
    have hPnn : 0 ≤ suzukiFreePrimePositionTorque L := by
      rw [suzukiFreePrimePositionTorque_eq_tsum]
      exact tsum_nonneg fun n => suzukiTentTerm_nonneg n L
    have hexp : Real.exp (3 * L / 2) * Real.exp (-σ * L) = Real.exp (-(σ - 3 / 2) * L) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hPnn (Real.exp_pos _).le)]
    calc suzukiFreePrimePositionTorque L * Real.exp (-σ * L)
        ≤ (1 / 2 * L ^ 3 * Real.exp (3 * L / 2)) * Real.exp (-σ * L) :=
          mul_le_mul_of_nonneg_right hP (Real.exp_pos _).le
      _ = 1 / 2 * (L ^ 3 * Real.exp (-(σ - 3 / 2) * L)) := by
          rw [← hexp]; ring
  rw [hsplit]
  exact hnear.union hfar

/-- **`(14)`: the complete torque transform.** -/
theorem integral_suzukiFreePositionTorque_mul_exp {σ : ℝ} (hσ : 3 / 2 < σ) :
    (∫ L in Ioi (0 : ℝ), suzukiFreePositionTorque L * Real.exp (-σ * L))
      = 1 / (2 * σ ^ 2)
          * (1 / (σ + 1 / 2) ^ 2 - 1 / (σ - 3 / 2) ^ 2 + 1 / (σ + 3 / 2) ^ 2)
        + (∑' n : ℕ, suzukiTentCoeff n * Real.exp (-σ * Real.log n)) / σ ^ 2 := by
  have h1 : (3 : ℝ) / 2 < σ := hσ
  have harch : IntegrableOn
      (fun L : ℝ => suzukiFreeArchPositionTorque L * Real.exp (-σ * L)) (Ioi 0) := by
    have hcongr : (fun L : ℝ => suzukiFreeArchPositionTorque L * Real.exp (-σ * L))
        = fun L : ℝ =>
            (((-2 / 9 : ℝ) * L + 8 / 27) * Real.exp ((3 / 2 : ℝ) * L) * Real.exp (-σ * L)
              + ((2 : ℝ) * L + 8) * Real.exp ((-1 / 2 : ℝ) * L) * Real.exp (-σ * L)
              + ((2 / 9 : ℝ) * L + 8 / 27) * Real.exp ((-3 / 2 : ℝ) * L) * Real.exp (-σ * L))
            + ((2 : ℝ) * L + -(232 / 27)) * Real.exp ((0 : ℝ) * L) * Real.exp (-σ * L) := by
      funext L
      rw [suzukiFreeArchPositionTorque_closedForm]
      have e1 : Real.exp (3 * L / 2) = Real.exp ((3 / 2 : ℝ) * L) := by congr 1; ring
      have e2 : Real.exp (-L / 2) = Real.exp ((-1 / 2 : ℝ) * L) := by congr 1; ring
      have e3 : Real.exp (-3 * L / 2) = Real.exp ((-3 / 2 : ℝ) * L) := by congr 1; ring
      rw [e1, e2, e3, zero_mul, Real.exp_zero]
      ring
    rw [hcongr]
    exact (((integrableOn_affineExp (a := (-2 / 9 : ℝ)) (b := (8 / 27 : ℝ)) (c := (3 / 2 : ℝ))
        (σ := σ) h1).add
      (integrableOn_affineExp (a := (2 : ℝ)) (b := (8 : ℝ)) (c := (-1 / 2 : ℝ)) (σ := σ)
        (by linarith))).add
      (integrableOn_affineExp (a := (2 / 9 : ℝ)) (b := (8 / 27 : ℝ)) (c := (-3 / 2 : ℝ)) (σ := σ)
        (by linarith))).add
      (integrableOn_affineExp (a := (2 : ℝ)) (b := (-(232 / 27) : ℝ)) (c := (0 : ℝ)) (σ := σ)
        (by linarith))
  have hprime := integrableOn_suzukiFreePrimePositionTorque_mul_exp hσ
  have hcongr2 : (∫ L in Ioi (0 : ℝ), suzukiFreePositionTorque L * Real.exp (-σ * L))
      = ∫ L in Ioi (0 : ℝ), (suzukiFreeArchPositionTorque L * Real.exp (-σ * L)
          + suzukiFreePrimePositionTorque L * Real.exp (-σ * L)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun L _ => ?_
    rw [suzukiFreePositionTorque]
    ring
  rw [hcongr2, integral_add harch hprime, integral_suzukiFreeArchPositionTorque_mul_exp hσ,
    integral_suzukiFreePrimePositionTorque_mul_exp hσ]

end RHTower
