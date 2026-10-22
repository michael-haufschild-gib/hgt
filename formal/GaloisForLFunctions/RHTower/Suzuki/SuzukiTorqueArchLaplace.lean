import GaloisForLFunctions.RHTower.Suzuki.SuzukiTorquePrimeLaplace

/-!
# The archimedean layer's Laplace transform

Suzuki's principal-value/Gamma torque has an elementary closed form: a sum of four
`(aL+b)e^{cL}` pieces with `c ∈ {3/2, −1/2, −3/2, 0}`.  Each transforms to `a/(σ−c)² + b/(σ−c)`,
and the four combine — after cancelling the apparent simple poles — into the compact rational
expression the card displays.
-/

open MeasureTheory Set

noncomputable section

namespace RHTower

theorem integral_exp_neg_linear {r : ℝ} (hr : 0 < r) :
    (∫ L in Ioi (0 : ℝ), Real.exp (-r * L)) = 1 / r := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (1 : ℝ)) (r := r) (by norm_num) hr
  have hcongr : (∫ u in Ioi (0 : ℝ), u ^ ((1 : ℝ) - 1) * Real.exp (-(r * u)))
      = ∫ L in Ioi (0 : ℝ), Real.exp (-r * L) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu0 : (0 : ℝ) < u := hu
    rw [show (1 : ℝ) - 1 = 0 by norm_num, Real.rpow_zero, one_mul]
    congr 1
    ring
  rw [hcongr] at h
  rw [h, Real.rpow_one, show Real.Gamma (1 : ℝ) = 1 by simp]
  ring

theorem integral_id_mul_exp_neg_linear {r : ℝ} (hr : 0 < r) :
    (∫ L in Ioi (0 : ℝ), L * Real.exp (-r * L)) = 1 / r ^ 2 := by
  have h := integral_suzukiPositionTent_mul_exp r 0 hr
  have hcongr : (∫ L in Ioi (0 : ℝ), (L - 0) * Real.exp (-r * L))
      = ∫ L in Ioi (0 : ℝ), L * Real.exp (-r * L) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun L _ => ?_
    rw [sub_zero]
  rw [hcongr] at h
  rw [h]
  norm_num

theorem integrableOn_exp_neg_linear {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun L : ℝ => Real.exp (-r * L)) (Ioi 0) := by
  have h := GaloisForLFunctions.HTGeometry.integrableOn_rpow_mul_exp_neg_mul_Ioi
    (σ := (0 : ℝ)) (a := r) (by norm_num) hr
  refine h.congr_fun (fun u hu => ?_) measurableSet_Ioi
  have hu0 : (0 : ℝ) < u := hu
  show u ^ (0 : ℝ) * Real.exp (-(r * u)) = Real.exp (-r * u)
  rw [Real.rpow_zero, one_mul]
  congr 1
  ring

theorem integrableOn_affineExp {a b c σ : ℝ} (h : c < σ) :
    IntegrableOn (fun L : ℝ => (a * L + b) * Real.exp (c * L) * Real.exp (-σ * L)) (Ioi 0) := by
  have hr : 0 < σ - c := by linarith
  have hbase : IntegrableOn
      (fun L : ℝ => a * (L * Real.exp (-(σ - c) * L)) + b * Real.exp (-(σ - c) * L)) (Ioi 0) :=
    ((integrableOn_id_mul_exp_neg hr).const_mul a).add
      ((integrableOn_exp_neg_linear hr).const_mul b)
  refine hbase.congr_fun (fun L _ => ?_) measurableSet_Ioi
  have hexp : Real.exp (c * L) * Real.exp (-σ * L) = Real.exp (-(σ - c) * L) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc a * (L * Real.exp (-(σ - c) * L)) + b * Real.exp (-(σ - c) * L)
      = (a * L + b) * Real.exp (-(σ - c) * L) := by ring
    _ = (a * L + b) * Real.exp (c * L) * Real.exp (-σ * L) := by rw [← hexp]; ring

theorem integral_affineExp {a b c σ : ℝ} (h : c < σ) :
    (∫ L in Ioi (0 : ℝ), (a * L + b) * Real.exp (c * L) * Real.exp (-σ * L))
      = a / (σ - c) ^ 2 + b / (σ - c) := by
  have hr : 0 < σ - c := by linarith
  have hcongr : (∫ L in Ioi (0 : ℝ), (a * L + b) * Real.exp (c * L) * Real.exp (-σ * L))
      = ∫ L in Ioi (0 : ℝ),
          (a * (L * Real.exp (-(σ - c) * L)) + b * Real.exp (-(σ - c) * L)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun L _ => ?_
    have hexp : Real.exp (c * L) * Real.exp (-σ * L) = Real.exp (-(σ - c) * L) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc (a * L + b) * Real.exp (c * L) * Real.exp (-σ * L)
        = (a * L + b) * (Real.exp (c * L) * Real.exp (-σ * L)) := by ring
      _ = (a * L + b) * Real.exp (-(σ - c) * L) := by rw [hexp]
      _ = a * (L * Real.exp (-(σ - c) * L)) + b * Real.exp (-(σ - c) * L) := by ring
  rw [hcongr, integral_add ((integrableOn_id_mul_exp_neg hr).const_mul a)
    ((integrableOn_exp_neg_linear hr).const_mul b), integral_const_mul, integral_const_mul,
    integral_id_mul_exp_neg_linear hr, integral_exp_neg_linear hr]
  field_simp


/-- **The archimedean layer's Laplace transform.** -/
theorem integral_suzukiFreeArchPositionTorque_mul_exp {σ : ℝ} (hσ : 3 / 2 < σ) :
    (∫ L in Ioi (0 : ℝ), suzukiFreeArchPositionTorque L * Real.exp (-σ * L))
      = 1 / (2 * σ ^ 2)
        * (1 / (σ + 1 / 2) ^ 2 - 1 / (σ - 3 / 2) ^ 2 + 1 / (σ + 3 / 2) ^ 2) := by
  have h1 : (3 : ℝ) / 2 < σ := hσ
  have h2 : (-1 : ℝ) / 2 < σ := by linarith
  have h3 : (-3 : ℝ) / 2 < σ := by linarith
  have h4 : (0 : ℝ) < σ := by linarith
  have hcongr : (∫ L in Ioi (0 : ℝ), suzukiFreeArchPositionTorque L * Real.exp (-σ * L))
      = ∫ L in Ioi (0 : ℝ),
          (((-2 / 9 : ℝ) * L + 8 / 27) * Real.exp ((3 / 2 : ℝ) * L) * Real.exp (-σ * L)
            + ((2 : ℝ) * L + 8) * Real.exp ((-1 / 2 : ℝ) * L) * Real.exp (-σ * L)
            + ((2 / 9 : ℝ) * L + 8 / 27) * Real.exp ((-3 / 2 : ℝ) * L) * Real.exp (-σ * L)
            + ((2 : ℝ) * L + -(232 / 27)) * Real.exp ((0 : ℝ) * L) * Real.exp (-σ * L)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun L _ => ?_
    rw [suzukiFreeArchPositionTorque_closedForm]
    have e1 : Real.exp (3 * L / 2) = Real.exp ((3 / 2 : ℝ) * L) := by congr 1; ring
    have e2 : Real.exp (-L / 2) = Real.exp ((-1 / 2 : ℝ) * L) := by congr 1; ring
    have e3 : Real.exp (-3 * L / 2) = Real.exp ((-3 / 2 : ℝ) * L) := by congr 1; ring
    rw [e1, e2, e3, zero_mul, Real.exp_zero]
    ring
  have hi1 := integrableOn_affineExp (a := (-2 / 9 : ℝ)) (b := (8 / 27 : ℝ)) (c := (3 / 2 : ℝ))
    (σ := σ) h1
  have hi2 := integrableOn_affineExp (a := (2 : ℝ)) (b := (8 : ℝ)) (c := (-1 / 2 : ℝ))
    (σ := σ) h2
  have hi3 := integrableOn_affineExp (a := (2 / 9 : ℝ)) (b := (8 / 27 : ℝ)) (c := (-3 / 2 : ℝ))
    (σ := σ) h3
  have hi4 := integrableOn_affineExp (a := (2 : ℝ)) (b := (-(232 / 27) : ℝ)) (c := (0 : ℝ))
    (σ := σ) h4
  have hs3 : (∫ L in Ioi (0 : ℝ),
        (((-2 / 9 : ℝ) * L + 8 / 27) * Real.exp ((3 / 2 : ℝ) * L) * Real.exp (-σ * L)
          + ((2 : ℝ) * L + 8) * Real.exp ((-1 / 2 : ℝ) * L) * Real.exp (-σ * L)
          + ((2 / 9 : ℝ) * L + 8 / 27) * Real.exp ((-3 / 2 : ℝ) * L) * Real.exp (-σ * L))
        + ((2 : ℝ) * L + -(232 / 27)) * Real.exp ((0 : ℝ) * L) * Real.exp (-σ * L))
      = (∫ L in Ioi (0 : ℝ),
          (((-2 / 9 : ℝ) * L + 8 / 27) * Real.exp ((3 / 2 : ℝ) * L) * Real.exp (-σ * L)
            + ((2 : ℝ) * L + 8) * Real.exp ((-1 / 2 : ℝ) * L) * Real.exp (-σ * L)
            + ((2 / 9 : ℝ) * L + 8 / 27) * Real.exp ((-3 / 2 : ℝ) * L) * Real.exp (-σ * L)))
        + ∫ L in Ioi (0 : ℝ),
            ((2 : ℝ) * L + -(232 / 27)) * Real.exp ((0 : ℝ) * L) * Real.exp (-σ * L) :=
    integral_add ((hi1.add hi2).add hi3) hi4
  have hs2 : (∫ L in Ioi (0 : ℝ),
        (((-2 / 9 : ℝ) * L + 8 / 27) * Real.exp ((3 / 2 : ℝ) * L) * Real.exp (-σ * L)
          + ((2 : ℝ) * L + 8) * Real.exp ((-1 / 2 : ℝ) * L) * Real.exp (-σ * L))
        + ((2 / 9 : ℝ) * L + 8 / 27) * Real.exp ((-3 / 2 : ℝ) * L) * Real.exp (-σ * L))
      = (∫ L in Ioi (0 : ℝ),
          (((-2 / 9 : ℝ) * L + 8 / 27) * Real.exp ((3 / 2 : ℝ) * L) * Real.exp (-σ * L)
            + ((2 : ℝ) * L + 8) * Real.exp ((-1 / 2 : ℝ) * L) * Real.exp (-σ * L)))
        + ∫ L in Ioi (0 : ℝ),
            ((2 / 9 : ℝ) * L + 8 / 27) * Real.exp ((-3 / 2 : ℝ) * L) * Real.exp (-σ * L) :=
    integral_add (hi1.add hi2) hi3
  have hs1 : (∫ L in Ioi (0 : ℝ),
        ((-2 / 9 : ℝ) * L + 8 / 27) * Real.exp ((3 / 2 : ℝ) * L) * Real.exp (-σ * L)
          + ((2 : ℝ) * L + 8) * Real.exp ((-1 / 2 : ℝ) * L) * Real.exp (-σ * L))
      = (∫ L in Ioi (0 : ℝ),
          ((-2 / 9 : ℝ) * L + 8 / 27) * Real.exp ((3 / 2 : ℝ) * L) * Real.exp (-σ * L))
        + ∫ L in Ioi (0 : ℝ),
            ((2 : ℝ) * L + 8) * Real.exp ((-1 / 2 : ℝ) * L) * Real.exp (-σ * L) :=
    integral_add hi1 hi2
  rw [hcongr, hs3, hs2, hs1, integral_affineExp h1, integral_affineExp h2, integral_affineExp h3,
    integral_affineExp h4]
  rw [show σ - (-1 / 2 : ℝ) = σ + 1 / 2 by ring, show σ - (-3 / 2 : ℝ) = σ + 3 / 2 by ring,
    show σ - (0 : ℝ) = σ by ring]
  have hne1 : σ - 3 / 2 ≠ 0 := by intro h; linarith [sub_eq_zero.mp h]
  have hnea : σ + 1 / 2 ≠ 0 := by intro h; linarith [eq_neg_of_add_eq_zero_left h]
  have hneb : σ + 3 / 2 ≠ 0 := by intro h; linarith [eq_neg_of_add_eq_zero_left h]
  have hnec : σ ≠ 0 := by intro h; rw [h] at hσ; linarith
  have hu : 2 * σ - 3 ≠ 0 := by intro h; linarith [sub_eq_zero.mp h]
  have hv : 2 * σ + 1 ≠ 0 := by intro h; linarith [eq_neg_of_add_eq_zero_left h]
  have hw : 2 * σ + 3 ≠ 0 := by intro h; linarith [eq_neg_of_add_eq_zero_left h]
  rw [show σ - 3 / 2 = (2 * σ - 3) / 2 by ring, show σ + 1 / 2 = (2 * σ + 1) / 2 by ring,
    show σ + 3 / 2 = (2 * σ + 3) / 2 by ring]
  field_simp
  ring

end RHTower
