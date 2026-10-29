import GaloisForLFunctions.RHTower.KiKimLeeLargeHeightReality

/-!
# An Euler-region anchor for the de Bruijn–Newman heat flow

The Gaussian average at `X - 16i` has its tilted centre at
`16 + t log(X/(2π))`. When this displacement is at most one, the centre
stays in the Euler region. The exponential model for `ξ` then controls
the average uniformly as the heat time tends to zero.
-/

open Complex MeasureTheory Filter Topology Set

namespace RHTower.DeBruijn

noncomputable section

private theorem exp_neg_ten_le : Real.exp (-10 : ℝ) ≤ 1 / 32 := by
  have h5 := Real.add_one_le_exp (5 : ℝ)
  have h10 : Real.exp (10 : ℝ) = Real.exp 5 * Real.exp 5 := by
    rw [← Real.exp_add]
    norm_num
  have h10low : 36 ≤ Real.exp (10 : ℝ) := by
    rw [h10]
    nlinarith only [h5, sq_nonneg (Real.exp (5 : ℝ) - 6)]
  have hprod : Real.exp (-10 : ℝ) * Real.exp 10 = 1 := by
    rw [← Real.exp_add]
    norm_num
  nlinarith only [hprod,
    mul_le_mul_of_nonneg_left h10low (Real.exp_pos (-10 : ℝ)).le]

private theorem exp_neg_twenty_le : Real.exp (-20 : ℝ) ≤ 1 / 1024 := by
  have h := exp_neg_ten_le
  have hp := Real.exp_pos (-10 : ℝ)
  have he : Real.exp (-20 : ℝ) = Real.exp (-10) * Real.exp (-10) := by
    rw [← Real.exp_add]
    norm_num
  rw [he]
  nlinarith [mul_nonneg hp.le (sub_nonneg.mpr h)]

private theorem integrable_gaussDensity_shift {t : ℝ} (ht : 0 < t) (y : ℝ) :
    Integrable (fun w => gaussDensity t (w - y)) := by
  simpa using integrable_gaussDensity_sub_mul_rexp ht y 0

private theorem integral_gaussDensity_shift {t : ℝ} (ht : 0 < t) (y : ℝ) :
    (∫ w, gaussDensity t (w - y)) = 1 := by
  simpa using integral_gaussDensity_sub_mul_rexp ht y 0

/-- Completing the square centres the tilted Gaussian at `y + 2tα`. -/
theorem gaussDensity_tilt_scale {t : ℝ} (ht : 0 < t) (y α w : ℝ) :
    gaussDensity t (w - y) * Real.exp ((w - (y + 2 * t * α)) * α) =
      Real.exp (-(t * α ^ 2)) * gaussDensity t (w - (y + 2 * t * α)) := by
  unfold gaussDensity
  rw [mul_assoc, ← Real.exp_add, mul_left_comm (Real.exp (-(t * α ^ 2))),
    mul_assoc, ← Real.exp_add]
  congr 2
  field_simp
  ring

/-- The model's lower tail stays a fixed distance from the Euler anchor. -/
theorem heatEuler_lower_model_tail_le {t α N : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8)
    (hα : 0 ≤ α) (hN : 0 ≤ N) :
    N * Real.exp (-((16 + 2 * t * α) * α)) *
        (∫ w in Iic (9 / 2 : ℝ), gaussDensity t (w - 16) * Real.exp (w * α)) ≤
      N * Real.exp (-(t * α ^ 2)) / 32 := by
  have h := setIntegral_Iic_gaussDensity_sub_mul_rexp_le ht 16 α (9 / 2) 1 zero_le_one
  have he : -((16 + 2 * t * α) * α) +
      (1 * (9 / 2) + 16 * (α - 1) + t * (α - 1) ^ 2) =
      -(t * α ^ 2) + (-23 / 2 - 2 * t * α + t) := by ring
  have hb : -23 / 2 - 2 * t * α + t ≤ (-10 : ℝ) := by
    nlinarith [mul_nonneg ht.le hα]
  calc _ ≤ N * Real.exp (-((16 + 2 * t * α) * α)) *
        Real.exp (1 * (9 / 2) + 16 * (α - 1) + t * (α - 1) ^ 2) := by gcongr
    _ = N * Real.exp (-(t * α ^ 2)) * Real.exp (-23 / 2 - 2 * t * α + t) := by
      rw [mul_assoc, ← Real.exp_add, he, Real.exp_add, ← mul_assoc]
    _ ≤ N * Real.exp (-(t * α ^ 2)) * Real.exp (-10) := by gcongr
    _ ≤ _ := by simpa [div_eq_mul_inv] using
        mul_le_mul_of_nonneg_left exp_neg_ten_le (by positivity : 0 ≤ N * Real.exp (-(t * α ^ 2)))

/-- The model's upper tail starts at least fifteen units beyond its centre. -/
theorem heatEuler_upper_model_tail_le {t α N : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8)
    (htu : 2 * t * α ≤ 1) (hN : 0 ≤ N) :
    N * Real.exp (-((16 + 2 * t * α) * α)) *
        (∫ w in Ioi (32 : ℝ), gaussDensity t (w - 16) * Real.exp (w * α)) ≤
      N * Real.exp (-(t * α ^ 2)) / 32 := by
  rw [← integral_Ici_eq_integral_Ioi]
  have h := setIntegral_Ici_gaussDensity_sub_mul_rexp_le ht 16 α 32 1 zero_le_one
  have he : -((16 + 2 * t * α) * α) +
      (-(1 * 32) + 16 * (α + 1) + t * (α + 1) ^ 2) =
      -(t * α ^ 2) + (-16 + 2 * t * α + t) := by ring
  have hb : -16 + 2 * t * α + t ≤ (-10 : ℝ) := by linarith
  calc _ ≤ N * Real.exp (-((16 + 2 * t * α) * α)) *
        Real.exp (-(1 * 32) + 16 * (α + 1) + t * (α + 1) ^ 2) := by gcongr
    _ = N * Real.exp (-(t * α ^ 2)) * Real.exp (-16 + 2 * t * α + t) := by
      rw [mul_assoc, ← Real.exp_add, he, Real.exp_add, ← mul_assoc]
    _ ≤ N * Real.exp (-(t * α ^ 2)) * Real.exp (-10) := by gcongr
    _ ≤ _ := by simpa [div_eq_mul_inv] using
        mul_le_mul_of_nonneg_left exp_neg_ten_le (by positivity : 0 ≤ N * Real.exp (-(t * α ^ 2)))

private theorem integrable_gaussDensity_norm_xiLine {t : ℝ} (ht : 0 < t) (X y : ℝ) :
    Integrable (fun w => gaussDensity t (w - y) * ‖xiLine X w‖) := by
  refine (integrable_gaussDensity_sub_mul ht (continuous_xiLine X)
    (integrable_exp_mul_norm_xiLine ht X) y).norm.congr (Eventually.of_forall fun w => ?_)
  exact norm_gauss_mul t y w ht _

/-- The critical-strip part is polynomially small relative to the tilted Euler value. -/
theorem heatEuler_strip_mass_le {t X : ℝ} (ht : 0 < t) (hX : 2048 ≤ X)
    (hα : 0 ≤ (horizontalSlope X).re) (htu : 2 * t * (horizontalSlope X).re ≤ 1) (y : ℝ) :
    (∫ w in Ioc (0 : ℝ) (9 / 2), gaussDensity t (w - y) * ‖xiLine X w‖) ≤
      (‖xiLine X (16 + 2 * t * (horizontalSlope X).re)‖ *
        Real.exp (-(t * (horizontalSlope X).re ^ 2))) *
        (200 * (6 + X) * Real.exp (-(23 / 2) * (horizontalSlope X).re + 25 / 16)) := by
  set α := (horizontalSlope X).re
  set u := 16 + 2 * t * α
  set P := ‖xiLine X u‖ * Real.exp (-(t * α ^ 2))
  have hu0 : 16 ≤ u := by dsimp [u]; nlinarith [mul_nonneg ht.le hα]
  have hu1 : u ≤ 17 := by dsimp [u]; linarith
  have hu : u ∈ Icc (9 / 2 : ℝ) (X / 32 - 1 / 2) := ⟨by linarith, by linarith⟩
  have h9 : (9 / 2 : ℝ) ∈ Icc (9 / 2 : ℝ) (X / 32 - 1 / 2) := ⟨le_rfl, by linarith⟩
  have h9norm : ‖xiLine X (9 / 2)‖ ≤ P * Real.exp (-(23 / 2) * α + 25 / 16) := by
    have hm := norm_xiLine_le_model (by linarith : 200 ≤ X) hu h9
    calc _ ≤ ‖xiLine X u‖ * Real.exp ((9 / 2 - u) * α) * Real.exp (1 / 8 * |9 / 2 - u|) := hm
      _ = ‖xiLine X u‖ * Real.exp ((9 / 2 - u) * α + 1 / 8 * |9 / 2 - u|) := by
        rw [mul_assoc, ← Real.exp_add]
      _ ≤ ‖xiLine X u‖ * Real.exp (-(t * α ^ 2) + (-(23 / 2) * α + 25 / 16)) := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
        rw [abs_of_nonpos (by linarith : 9 / 2 - u ≤ 0)]
        have hu_eq : u = 16 + 2 * t * α := rfl
        nlinarith only [hu1, hu_eq, mul_nonneg ht.le (sq_nonneg α)]
      _ = _ := by rw [Real.exp_add]; exact (mul_assoc _ _ _).symm
  set B := P * (200 * (6 + X) * Real.exp (-(23 / 2) * α + 25 / 16))
  have hB : 0 ≤ B := by dsimp [B, P]; positivity
  have hnorm : ∀ w ∈ Ioc (0 : ℝ) (9 / 2), ‖xiLine X w‖ ≤ B := by
    intro w hw
    calc _ ≤ 200 * (6 + X) * ‖xiLine X (9 / 2)‖ :=
        norm_xiLine_le_strip (by linarith) hw.1.le hw.2
      _ ≤ 200 * (6 + X) * (P * Real.exp (-(23 / 2) * α + 25 / 16)) := by gcongr
      _ = B := by dsimp [B]; ring
  calc
    _ ≤ (∫ w in Ioc (0 : ℝ) (9 / 2), B * gaussDensity t (w - y)) := by
      refine setIntegral_mono_on (integrable_gaussDensity_norm_xiLine ht X y).integrableOn
        ((integrable_gaussDensity_shift ht y).const_mul B).integrableOn measurableSet_Ioc ?_
      intro w hw
      have := mul_le_mul_of_nonneg_left (hnorm w hw) (gaussDensity_pos ht (w - y)).le
      simpa [mul_comm] using this
    _ ≤ (∫ w, B * gaussDensity t (w - y)) :=
      setIntegral_le_integral ((integrable_gaussDensity_shift ht y).const_mul B)
        (Eventually.of_forall fun w => mul_nonneg hB (gaussDensity_pos ht _).le)
    _ = B := by rw [integral_const_mul, integral_gaussDensity_shift ht, mul_one]

private theorem euler_far_exponent_le {t X u v : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8)
    (hX : 2048 ≤ X) (hu : u ≤ 17) (hv : 15 ≤ v) :
    (2 + (v + u + 1 / 2) / (2 * X)) * v + 20 ≤ v ^ 2 / (8 * t) := by
  have hX0 : 0 < X := by linarith
  have hv0 : 0 ≤ v := by linarith
  have hlin : (u + 1 / 2) / (2 * X) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  have hquad : v ^ 2 / (2 * X) ≤ v ^ 2 / 16 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith only [mul_nonneg (sq_nonneg v) (show 0 ≤ X - 8 by linarith)]
  have hheat : v ^ 2 ≤ v ^ 2 / (8 * t) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [mul_nonneg (sq_nonneg v) (show 0 ≤ 1 - 8 * t by linarith)]
  have hsplit : (2 + (v + u + 1 / 2) / (2 * X)) * v =
      (2 + (u + 1 / 2) / (2 * X)) * v + v ^ 2 / (2 * X) := by ring
  rw [hsplit]
  have hprod := mul_le_mul_of_nonneg_right hlin hv0
  have hv2 : 15 * v ≤ v ^ 2 := by
    nlinarith only [mul_nonneg (show 0 ≤ v - 15 by linarith) hv0]
  nlinarith only [hprod, hquad, hheat, hv2, hv]

/-- The upper Euler tail is absorbed by a Gaussian of twice the variance. -/
theorem heatEuler_far_integrand_le {t X w : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8)
    (hX : 2048 ≤ X) (hα : 0 ≤ (horizontalSlope X).re)
    (htu : 2 * t * (horizontalSlope X).re ≤ 1) (hw : 32 ≤ w) :
    gaussDensity t (w - 16) * ‖xiLine X w‖ ≤
      (‖xiLine X (16 + 2 * t * (horizontalSlope X).re)‖ *
        Real.exp (-(t * (horizontalSlope X).re ^ 2))) *
        (2 * Real.exp (-20) * gaussDensity (2 * t) (w - (16 + 2 * t * (horizontalSlope X).re))) := by
  set α := (horizontalSlope X).re
  set u := 16 + 2 * t * α
  set v := w - u
  set N := ‖xiLine X u‖
  have hu0 : 16 ≤ u := by dsimp [u]; nlinarith only [mul_nonneg ht.le hα]
  have hu1 : u ≤ 17 := by dsimp [u]; linarith
  have hv : 15 ≤ v := by dsimp [v]; linarith
  have hαeq : Real.log (X / (2 * Real.pi)) / 2 = α := by simp [α, horizontalSlope]
  have hfar := norm_xiLine_le_far (by linarith : 200 ≤ X) (by linarith : 9 / 2 ≤ u)
    (by linarith : u ≤ w)
  rw [hαeq] at hfar
  have hexp : (2 + (w + 1 / 2) / (2 * X)) * v ≤ v ^ 2 / (8 * t) - 20 := by
    have h := euler_far_exponent_le ht ht8 hX hu1 hv
    have hw_eq : v + u = w := by dsimp [v]; ring
    rw [hw_eq] at h
    linarith
  have hsplit : (α + 2 + (w + 1 / 2) / (2 * X)) * (w - u) =
      (w - u) * α + (2 + (w + 1 / 2) / (2 * X)) * v := by dsimp [v]; ring
  calc _ ≤ gaussDensity t (w - 16) *
        (N * Real.exp ((α + 2 + (w + 1 / 2) / (2 * X)) * (w - u))) :=
      mul_le_mul_of_nonneg_left hfar (gaussDensity_pos ht _).le
    _ = (N * Real.exp (-(t * α ^ 2))) *
        (gaussDensity t v * Real.exp ((2 + (w + 1 / 2) / (2 * X)) * v)) := by
      rw [hsplit, Real.exp_add]
      calc _ = N * (gaussDensity t (w - 16) * Real.exp ((w - u) * α)) *
          Real.exp ((2 + (w + 1 / 2) / (2 * X)) * v) := by ring
        _ = _ := by rw [show u = 16 + 2 * t * α from rfl, gaussDensity_tilt_scale ht]; ring
    _ ≤ (N * Real.exp (-(t * α ^ 2))) *
        (Real.exp (-20) * (gaussDensity t v * Real.exp (v ^ 2 / (8 * t)))) := by
      rw [mul_left_comm (Real.exp (-20)), ← Real.exp_add]
      apply mul_le_mul_of_nonneg_left ?_ (by dsimp [N]; positivity)
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (gaussDensity_pos ht v).le
      linarith only [hexp]
    _ ≤ (N * Real.exp (-(t * α ^ 2))) *
        (Real.exp (-20) * (2 * gaussDensity (2 * t) v)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (gaussDensity_mul_exp_le ht v) (Real.exp_pos (-20)).le)
        (by dsimp [N]; positivity)
    _ = _ := by dsimp [N, u, v, α]; ring

/-- The integrated upper tail is at most one thirty-second of the tilted scale. -/
theorem heatEuler_far_mass_le {t X : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8)
    (hX : 2048 ≤ X) (hα : 0 ≤ (horizontalSlope X).re)
    (htu : 2 * t * (horizontalSlope X).re ≤ 1) :
    (∫ w in Ioi (32 : ℝ), gaussDensity t (w - 16) * ‖xiLine X w‖) ≤
      (‖xiLine X (16 + 2 * t * (horizontalSlope X).re)‖ *
        Real.exp (-(t * (horizontalSlope X).re ^ 2))) / 32 := by
  set u := 16 + 2 * t * (horizontalSlope X).re
  set P := ‖xiLine X u‖ * Real.exp (-(t * (horizontalSlope X).re ^ 2))
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hint := (integrable_gaussDensity_shift (show 0 < 2 * t by positivity) u).const_mul
    (P * (2 * Real.exp (-20)))
  calc
    _ ≤ (∫ w in Ioi (32 : ℝ), (P * (2 * Real.exp (-20))) * gaussDensity (2 * t) (w - u)) := by
      refine setIntegral_mono_on (integrable_gaussDensity_norm_xiLine ht X 16).integrableOn
        hint.integrableOn measurableSet_Ioi fun w hw => ?_
      simpa [u, P, mul_assoc] using heatEuler_far_integrand_le ht ht8 hX hα htu hw.le
    _ ≤ (∫ w, (P * (2 * Real.exp (-20))) * gaussDensity (2 * t) (w - u)) :=
      setIntegral_le_integral hint (Eventually.of_forall fun w =>
        mul_nonneg (mul_nonneg hP (by positivity)) (gaussDensity_pos (by positivity) _).le)
    _ = P * (2 * Real.exp (-20)) := by
      rw [integral_const_mul, integral_gaussDensity_shift (by positivity), mul_one]
    _ ≤ P / 32 := by nlinarith only [mul_le_mul_of_nonneg_left exp_neg_twenty_le hP, hP]

/-- At a fixed Euler anchor, the strip loss decays as a power of height. -/
theorem heatEuler_strip_factor_le {X : ℝ} (hX : 0 < X)
    (hα : 8 ≤ (horizontalSlope X).re) :
    200 * (6 + X) * Real.exp (-(23 / 2) * (horizontalSlope X).re + 25 / 16) ≤ 1 / 32 := by
  set α := (horizontalSlope X).re
  have he1 : 1 ≤ Real.exp (2 * α) := Real.one_le_exp (by dsimp [α]; linarith)
  have hbase : 200 * (6 + X) ≤ 2800 * Real.exp (2 * α) := by
    rw [height_eq hX]
    change 200 * (6 + 2 * Real.pi * Real.exp (2 * α)) ≤ 2800 * Real.exp (2 * α)
    have hpi := mul_le_mul_of_nonneg_right Real.pi_lt_four.le (Real.exp_pos (2 * α)).le
    nlinarith only [he1, hpi]
  have h50 : Real.exp (-50 : ℝ) ≤ (1 / 32 : ℝ) ^ 5 := by
    calc _ = Real.exp (-10 : ℝ) ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ _ := by gcongr; exact exp_neg_ten_le
  calc _ ≤ 2800 * Real.exp (2 * α) * Real.exp (-(23 / 2) * α + 25 / 16) := by gcongr
    _ = 2800 * Real.exp (-(19 / 2) * α + 25 / 16) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ 2800 * Real.exp (-50) := by gcongr; dsimp [α]; linarith
    _ ≤ 2800 * (1 / 32 : ℝ) ^ 5 := by gcongr
    _ ≤ 1 / 32 := by norm_num

private theorem integral_Ioi_split_real {f : ℝ → ℝ} {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hf : Integrable f) :
    (∫ w in Ioi (0 : ℝ), f w) =
      (∫ w in Ioc (0 : ℝ) a, f w) + (∫ w in Ioc a b, f w) + ∫ w in Ioi b, f w := by
  have hda : Disjoint (Ioc (0 : ℝ) a) (Ioi a) :=
    Set.disjoint_left.mpr fun w hw hw' => (not_lt.mpr hw.2) hw'
  have hdb : Disjoint (Ioc a b) (Ioi b) :=
    Set.disjoint_left.mpr fun w hw hw' => (not_lt.mpr hw.2) hw'
  rw [← Ioc_union_Ioi_eq_Ioi ha,
    setIntegral_union hda measurableSet_Ioi hf.integrableOn hf.integrableOn,
    ← Ioc_union_Ioi_eq_Ioi hab,
    setIntegral_union hdb measurableSet_Ioi hf.integrableOn hf.integrableOn]
  ring

/-- The absolute mass on the positive half-line is at most twice the tilted scale. -/
theorem heatEuler_positive_mass_le {t X : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8)
    (hX : 2048 ≤ X) (hα : 8 ≤ (horizontalSlope X).re)
    (htu : 2 * t * (horizontalSlope X).re ≤ 1) :
    (∫ w in Ioi (0 : ℝ), gaussDensity t (w - 16) * ‖xiLine X w‖) ≤
      2 * (‖xiLine X (16 + 2 * t * (horizontalSlope X).re)‖ *
        Real.exp (-(t * (horizontalSlope X).re ^ 2))) := by
  set α := (horizontalSlope X).re
  set u := 16 + 2 * t * α
  set P := ‖xiLine X u‖ * Real.exp (-(t * α ^ 2))
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hα0 : 0 ≤ (horizontalSlope X).re := by linarith
  have hu0 : 16 ≤ u := by dsimp [u]; nlinarith only [mul_nonneg ht.le hα0]
  have hu1 : u ≤ 17 := by dsimp [u]; linarith
  have hu : u ∈ Icc (9 / 2 : ℝ) (X / 32 - 1 / 2) := ⟨by linarith, by linarith⟩
  have hs := heatEuler_strip_mass_le ht hX hα0 htu 16
  have hb := heatEuler_strip_factor_le (by linarith : 0 < X) hα
  have hs' : (∫ w in Ioc (0 : ℝ) (9 / 2), gaussDensity t (w - 16) * ‖xiLine X w‖) ≤ P / 32 := by
    exact hs.trans (by simpa [P, u, α, div_eq_mul_inv] using mul_le_mul_of_nonneg_left hb hP)
  have hw := windowMass_le ht (by linarith : 200 ≤ X) (y := 16) hu
    (W := 32) (by linarith)
  have hc := modelConstant_le ht ht8
  have hw' : (∫ w in Ioc (9 / 2 : ℝ) 32, gaussDensity t (w - 16) * ‖xiLine X w‖) ≤ P * (13 / 10) := by
    refine hw.trans ?_
    change P * (1 + 2 * (1 / 8) * Real.exp (t * (1 + 1 / 8) ^ 2)) ≤ P * (13 / 10)
    gcongr
    linarith
  have hf := heatEuler_far_mass_le ht ht8 hX hα0 htu
  rw [integral_Ioi_split_real (a := 9 / 2) (b := 32) (by norm_num) (by norm_num)
    (integrable_gaussDensity_norm_xiLine ht X 16)]
  change _ ≤ 2 * P
  change _ ≤ P / 32 at hf
  linarith only [hs', hw', hf, hP]

private theorem gaussDensity_opposite_le {t w : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8)
    (hw : 9 / 2 ≤ w) :
    gaussDensity t (w + 16) ≤ Real.exp (-20) * gaussDensity t (w - 16) := by
  have he : -((w + 16) ^ 2 / (4 * t)) ≤ -20 + -((w - 16) ^ 2 / (4 * t)) := by
    have hn : -((w + 16) ^ 2) ≤ -20 * (4 * t) - (w - 16) ^ 2 := by
      nlinarith only [hw, ht8]
    have hd := div_le_div_of_nonneg_right hn (show 0 ≤ 4 * t by positivity)
    have heq : (-20 * (4 * t) - (w - 16) ^ 2) / (4 * t) =
        -20 + -((w - 16) ^ 2 / (4 * t)) := by
      field_simp
      ring
    rw [heq] at hd
    simpa only [neg_div] using hd
  unfold gaussDensity
  rw [mul_left_comm (Real.exp (-20)), ← Real.exp_add]
  gcongr

/-- Reflection is small at the Euler anchor; both strip and Euler parts are retained. -/
theorem heatEuler_opposite_mass_le {t X : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8)
    (hX : 2048 ≤ X) (hα : 8 ≤ (horizontalSlope X).re)
    (htu : 2 * t * (horizontalSlope X).re ≤ 1) :
    (∫ w in Ioi (0 : ℝ), gaussDensity t (w + 16) * ‖xiLine X w‖) ≤
      (‖xiLine X (16 + 2 * t * (horizontalSlope X).re)‖ *
        Real.exp (-(t * (horizontalSlope X).re ^ 2))) / 16 := by
  set P := ‖xiLine X (16 + 2 * t * (horizontalSlope X).re)‖ *
    Real.exp (-(t * (horizontalSlope X).re ^ 2))
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hα0 : 0 ≤ (horizontalSlope X).re := by linarith
  have hpos := heatEuler_positive_mass_le ht ht8 hX hα htu
  have hs := heatEuler_strip_mass_le ht hX hα0 htu (-16)
  have hb := heatEuler_strip_factor_le (by linarith : 0 < X) hα
  have hs' : (∫ w in Ioc (0 : ℝ) (9 / 2), gaussDensity t (w + 16) * ‖xiLine X w‖) ≤ P / 32 := by
    simpa only [sub_neg_eq_add] using hs.trans (by
      simpa [P, div_eq_mul_inv] using mul_le_mul_of_nonneg_left hb hP)
  have hi := integrable_gaussDensity_norm_xiLine ht X 16
  have hneg : Integrable (fun w => gaussDensity t (w + 16) * ‖xiLine X w‖) := by
    simpa only [sub_neg_eq_add] using integrable_gaussDensity_norm_xiLine ht X (-16)
  have htail : (∫ w in Ioi (9 / 2 : ℝ), gaussDensity t (w + 16) * ‖xiLine X w‖) ≤
      Real.exp (-20) * (2 * P) := by
    calc
      _ ≤ (∫ w in Ioi (9 / 2 : ℝ), Real.exp (-20) *
          (gaussDensity t (w - 16) * ‖xiLine X w‖)) := by
        refine setIntegral_mono_on hneg.integrableOn (hi.const_mul _).integrableOn
          measurableSet_Ioi fun w hw => ?_
        have := mul_le_mul_of_nonneg_right (gaussDensity_opposite_le ht ht8 hw.le) (norm_nonneg (xiLine X w))
        simpa only [mul_assoc] using this
      _ ≤ (∫ w in Ioi (0 : ℝ), Real.exp (-20) *
          (gaussDensity t (w - 16) * ‖xiLine X w‖)) := by
        refine setIntegral_mono_set (hi.const_mul _).integrableOn ?_ ?_
        · exact Eventually.of_forall fun w =>
            mul_nonneg (Real.exp_pos (-20)).le (mul_nonneg (gaussDensity_pos ht _).le (norm_nonneg _))
        · exact Eventually.of_forall fun w hw => lt_trans (by norm_num : (0 : ℝ) < 9 / 2) hw
      _ ≤ Real.exp (-20) * (2 * P) := by rw [integral_const_mul]; gcongr
  have hd : Disjoint (Ioc (0 : ℝ) (9 / 2)) (Ioi (9 / 2 : ℝ)) :=
    Set.disjoint_left.mpr fun w hw hw' => (not_lt.mpr hw.2) hw'
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 9 / 2),
    setIntegral_union hd measurableSet_Ioi hneg.integrableOn hneg.integrableOn]
  change _ ≤ P / 16
  nlinarith only [hs', htail, mul_le_mul_of_nonneg_left exp_neg_twenty_le hP, hP]

private theorem norm_halfGaussTransform_le_mass {t : ℝ} (ht : 0 < t) (X y : ℝ) :
    ‖halfGaussTransform t (xiLine X) y‖ ≤
      ∫ w in Ioi (0 : ℝ), gaussDensity t (w - y) * ‖xiLine X w‖ := by
  unfold halfGaussTransform
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  congr 1
  funext w
  exact norm_gauss_mul t y w ht _

/-- A fixed positive fraction of the tilted Euler value survives the full heat average. -/
theorem heatEuler_tilted_scale_le {t X : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8)
    (hX : 2048 ≤ X) (hα : 8 ≤ (horizontalSlope X).re)
    (htu : 2 * t * (horizontalSlope X).re ≤ 1) :
    (‖xiLine X (16 + 2 * t * (horizontalSlope X).re)‖ *
      Real.exp (-(t * (horizontalSlope X).re ^ 2))) / 4 ≤
      ‖riemannHeat t ((X : ℂ) - 16 * I)‖ := by
  set a := horizontalSlope X
  set α := a.re
  set u := 16 + 2 * t * α
  set N := ‖xiLine X u‖
  set P := N * Real.exp (-(t * α ^ 2))
  set Q := halfGaussTransform t (xiLine X) 16
  set Q' := halfGaussTransform t (xiLine X) (-16)
  set M := xiLine X u * Complex.exp (-(u * a)) * Complex.exp (16 * a + t * a ^ 2)
  have hP : 0 ≤ P := by dsimp [P, N]; positivity
  have hα0 : 0 ≤ (horizontalSlope X).re := by linarith
  have hu0 : 16 ≤ u := by dsimp [u]; nlinarith only [mul_nonneg ht.le hα0]
  have hu1 : u ≤ 17 := by dsimp [u]; linarith
  have hu : u ∈ Icc (9 / 2 : ℝ) (X / 32 - 1 / 2) := ⟨by linarith, by linarith⟩
  have hmodel : ∀ w ∈ Icc (9 / 2 : ℝ) 32, ‖xiLine X w - xiLine X u *
      Complex.exp (((w - u : ℝ) : ℂ) * a)‖ ≤
      N * Real.exp ((w - u) * a.re) * (Real.exp (1 / 8 * |w - u|) - 1) := by
    intro w hw
    exact norm_xiLine_sub_model_le (by linarith) hu ⟨hw.1, by linarith [hw.2]⟩
  have hQ := norm_halfGaussTransform_sub_main_le ht (continuous_xiLine X)
    (integrable_exp_mul_norm_xiLine ht X) (y := 16) (by norm_num) (by norm_num)
    (by norm_num : (9 / 2 : ℝ) ≤ 32) hmodel
  have hl := heatEuler_lower_model_tail_le ht ht8 hα0 (norm_nonneg (xiLine X u))
  have hr := heatEuler_upper_model_tail_le ht ht8 htu (norm_nonneg (xiLine X u))
  have hm := modelError_le ht (norm_nonneg (xiLine X u)) (α := α) (y := 16)
  have hc := modelConstant_le ht ht8
  have hm' := mul_le_mul_of_nonneg_left hc hP
  have hs := heatEuler_strip_mass_le ht hX hα0 htu 16
  have hb := mul_le_mul_of_nonneg_left (heatEuler_strip_factor_le (by linarith : 0 < X) hα) hP
  have hf := heatEuler_far_mass_le ht ht8 hX hα0 htu
  have herr : ‖Q - M‖ ≤ (17 / 40) * P := by
    change ‖Q - M‖ ≤ _ at hQ
    change _ ≤ P / 32 at hl hr hf
    change _ ≤ P * _ at hm hs
    nlinarith only [hQ, hl, hr, hm, hm', hs, hb, hf]
  have hmain : (23 / 25) * P ≤ ‖M‖ := by
    have heq := norm_main_eq (t := t) (X := X) (y := 16) (xiLine X u)
    change ‖M‖ = P * Real.exp (-(t * (Real.pi / 4) ^ 2)) at heq
    rw [heq]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (gaussPhase_ge ht8 ht) hP
  have hneg : ‖Q'‖ ≤ P / 16 := by
    have hn := norm_halfGaussTransform_le_mass ht X (-16)
    simp only [sub_neg_eq_add] at hn
    exact hn.trans (heatEuler_opposite_mass_le ht ht8 hX hα htu)
  have hheat : riemannHeat t ((X : ℂ) - 16 * I) = Q + starRingEnd ℂ Q' := by
    have heq := riemannHeat_eq_halfGaussAverage ht X (-16)
    norm_num only [neg_neg, Complex.ofReal_neg, Complex.ofReal_ofNat] at heq
    simp only [halfGaussAverage_eq_halfGaussTransform] at heq
    change riemannHeat t ((X : ℂ) + I * (-16)) = Q + starRingEnd ℂ Q' at heq
    rw [show (X : ℂ) - 16 * I = X + I * (-16) by ring]
    exact heq
  have htri1 := norm_sub_norm_le M Q
  rw [norm_sub_rev] at htri1
  have htri2 := norm_sub_norm_le Q (Q + starRingEnd ℂ Q')
  simp only [sub_add_cancel_left, norm_neg, Complex.norm_conj] at htri2
  rw [hheat]
  change P / 4 ≤ _
  linarith only [herr, hmain, hneg, htri1, htri2, hP]

/-- The heat flow has a uniform lower anchor on the fixed line `Im z = -16`. -/
theorem norm_xiLine_sixteen_le_eight_mul_norm_riemannHeat {t X : ℝ}
    (ht : 0 < t) (ht8 : t ≤ 1 / 8) (hX : 2048 ≤ X)
    (hα : 8 ≤ (horizontalSlope X).re) (htu : 2 * t * (horizontalSlope X).re ≤ 1) :
    ‖xiLine X 16‖ ≤ 8 * ‖riemannHeat t ((X : ℂ) - 16 * I)‖ := by
  set α := (horizontalSlope X).re
  set u := 16 + 2 * t * α
  set P := ‖xiLine X u‖ * Real.exp (-(t * α ^ 2))
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hα0 : 0 ≤ α := by dsimp [α]; linarith
  have hu0 : 16 ≤ u := by dsimp [u]; nlinarith only [mul_nonneg ht.le hα0]
  have hu1 : u ≤ 17 := by dsimp [u]; linarith
  have hu : u ∈ Icc (9 / 2 : ℝ) (X / 32 - 1 / 2) := ⟨by linarith, by linarith⟩
  have h16 : (16 : ℝ) ∈ Icc (9 / 2 : ℝ) (X / 32 - 1 / 2) := ⟨by norm_num, by linarith⟩
  have hm := norm_xiLine_le_model (by linarith : 200 ≤ X) hu h16
  have hcomp : ‖xiLine X 16‖ ≤ P * Real.exp (1 / 8) := by
    calc _ ≤ ‖xiLine X u‖ * Real.exp ((16 - u) * α) * Real.exp (1 / 8 * |16 - u|) := hm
      _ = ‖xiLine X u‖ * Real.exp ((16 - u) * α + 1 / 8 * |16 - u|) := by
        rw [mul_assoc, ← Real.exp_add]
      _ ≤ ‖xiLine X u‖ * Real.exp (-(t * α ^ 2) + 1 / 8) := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
        rw [abs_of_nonpos (by linarith : 16 - u ≤ 0)]
        have hu_eq : u = 16 + 2 * t * α := rfl
        nlinarith only [hu1, hu_eq, mul_nonneg ht.le (sq_nonneg α)]
      _ = _ := by rw [Real.exp_add]; exact (mul_assoc _ _ _).symm
  have he : Real.exp (1 / 8 : ℝ) ≤ 2 := by
    have h := Real.exp_bound_div_one_sub_of_interval' (x := 1 / 8) (by norm_num) (by norm_num)
    norm_num at h
    linarith
  have hheat := heatEuler_tilted_scale_le ht ht8 hX hα htu
  change P / 4 ≤ _ at hheat
  nlinarith only [hcomp, mul_le_mul_of_nonneg_left he hP, hheat]

end

end RHTower.DeBruijn
