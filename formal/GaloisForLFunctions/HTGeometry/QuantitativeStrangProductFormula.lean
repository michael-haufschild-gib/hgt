import GaloisForLFunctions.HTGeometry.QuantitativeLieProductFormula

open Set NormedSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {A : Type*} [CStarAlgebra A]

theorem cstarExponentialTaylor_two (x : A) (t : ℝ) :
    cstarExponentialTaylor x 2 t =
      1 + t • x + (t ^ (2 : ℕ) / 2) • x ^ (2 : ℕ) := by
  rw [show cstarExponentialTaylor x 2 t =
      (∑ k ∈ Finset.range 3, (t ^ k / (k.factorial : ℝ)) • x ^ k) by
        simp [cstarExponentialTaylor]]
  norm_num [Finset.sum_range_succ]

variable [Nontrivial A]

set_option maxHeartbeats 800000 in
theorem norm_exp_half_mul_exp_mul_exp_half_sub_exp_add_le
    (x y : A) (hx : x ∈ skewAdjoint A) (hy : y ∈ skewAdjoint A)
    (t : ℝ) (hsmall : |t| * (‖x‖ + ‖y‖) ≤ 1) :
    ‖exp ((t / 2) • x) * exp (t • y) * exp ((t / 2) • x) -
        exp (t • (x + y))‖ ≤
      8 * (‖x‖ + ‖y‖) ^ (3 : ℕ) * |t| ^ (3 : ℕ) := by
  let _ : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A
  let a : A := (t / 2) • x
  let b : A := t • y
  let Qa : A := ((t / 2) ^ (2 : ℕ) / 2) • x ^ (2 : ℕ)
  let Qb : A := (t ^ (2 : ℕ) / 2) • y ^ (2 : ℕ)
  let La : A := 1 + a
  let Lb : A := 1 + b
  let Ta : A := La + Qa
  let Tb : A := Lb + Qb
  let Txy : A := 1 + t • (x + y) + (t ^ (2 : ℕ) / 2) • (x + y) ^ (2 : ℕ)
  let u : ℝ := |t| * (‖x‖ + ‖y‖)
  have hu0 : 0 ≤ u := by positivity
  have hu1 : u ≤ 1 := hsmall
  have hx0 : 0 ≤ ‖x‖ := norm_nonneg _
  have hy0 : 0 ≤ ‖y‖ := norm_nonneg _
  have hB0 : 0 ≤ ‖x‖ + ‖y‖ := by positivity
  have ha : ‖a‖ ≤ u / 2 := by
    dsimp [a, u]
    rw [norm_smul, Real.norm_eq_abs, abs_div]
    norm_num
    have := mul_le_mul_of_nonneg_left (show ‖x‖ ≤ ‖x‖ + ‖y‖ by linarith)
      (abs_nonneg t)
    linarith
  have hb : ‖b‖ ≤ u := by
    dsimp [b, u]
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg t)
  have hQa : ‖Qa‖ ≤ u ^ (2 : ℕ) / 8 := by
    dsimp [Qa, u]
    rw [norm_smul, Real.norm_eq_abs]
    have hcoef : |(t / 2) ^ (2 : ℕ) / 2| = |t| ^ (2 : ℕ) / 8 := by
      rw [abs_div, abs_pow, abs_div]
      norm_num
      nlinarith [sq_abs t]
    rw [hcoef]
    calc
      |t| ^ (2 : ℕ) / 8 * ‖x ^ (2 : ℕ)‖ ≤
          (|t| ^ (2 : ℕ) / 8) * ‖x‖ ^ (2 : ℕ) := by
            gcongr
            exact norm_pow_le' x (by omega : 0 < 2)
      _ ≤ u ^ (2 : ℕ) / 8 := by
        dsimp [u]
        have hxle : ‖x‖ ≤ ‖x‖ + ‖y‖ := by linarith
        have hsquare : ‖x‖ ^ (2 : ℕ) ≤ (‖x‖ + ‖y‖) ^ (2 : ℕ) := by nlinarith
        nlinarith [sq_nonneg |t|]
  have hQb : ‖Qb‖ ≤ u ^ (2 : ℕ) / 2 := by
    dsimp [Qb, u]
    rw [norm_smul, Real.norm_eq_abs]
    have hcoef : |t ^ (2 : ℕ) / 2| = |t| ^ (2 : ℕ) / 2 := by
      rw [abs_div, abs_pow]
      norm_num
    rw [hcoef]
    have hpow := norm_pow_le' y (by omega : 0 < 2)
    have hyle : ‖y‖ ≤ ‖x‖ + ‖y‖ := by linarith
    have hsquare : ‖y‖ ^ (2 : ℕ) ≤ (‖x‖ + ‖y‖) ^ (2 : ℕ) := by nlinarith
    calc
      |t| ^ (2 : ℕ) / 2 * ‖y ^ (2 : ℕ)‖ ≤ |t| ^ (2 : ℕ) / 2 * ‖y‖ ^ (2 : ℕ) := by gcongr
      _ ≤ u ^ (2 : ℕ) / 2 := by dsimp [u]; nlinarith [sq_nonneg |t|]
  have hTaSub : ‖Ta - 1‖ ≤ 5 * u / 8 := by
    have hid : Ta - 1 = a + Qa := by dsimp [Ta, La]; noncomm_ring
    rw [hid]
    calc
      ‖a + Qa‖ ≤ ‖a‖ + ‖Qa‖ := norm_add_le _ _
      _ ≤ u / 2 + u ^ (2 : ℕ) / 8 := add_le_add ha hQa
      _ ≤ 5 * u / 8 := by nlinarith [mul_nonneg hu0 (sub_nonneg.mpr hu1)]
  have hTbSub : ‖Tb - 1‖ ≤ 3 * u / 2 := by
    have hid : Tb - 1 = b + Qb := by dsimp [Tb, Lb]; noncomm_ring
    rw [hid]
    calc
      ‖b + Qb‖ ≤ ‖b‖ + ‖Qb‖ := norm_add_le _ _
      _ ≤ u + u ^ (2 : ℕ) / 2 := add_le_add hb hQb
      _ ≤ 3 * u / 2 := by nlinarith [mul_nonneg hu0 (sub_nonneg.mpr hu1)]
  have hTa : ‖Ta‖ ≤ 2 := by
    calc
      ‖Ta‖ = ‖(Ta - 1) + 1‖ := by congr 1; noncomm_ring
      _ ≤ ‖Ta - 1‖ + ‖(1 : A)‖ := norm_add_le _ _
      _ ≤ 5 * u / 8 + 1 := by
        rw [norm_one]
        exact add_le_add hTaSub le_rfl
      _ ≤ 2 := by nlinarith
  have hTb : ‖Tb‖ ≤ 3 := by
    calc
      ‖Tb‖ = ‖(Tb - 1) + 1‖ := by congr 1; noncomm_ring
      _ ≤ ‖Tb - 1‖ + ‖(1 : A)‖ := norm_add_le _ _
      _ ≤ 3 * u / 2 + 1 := by
        rw [norm_one]
        exact add_le_add hTbSub le_rfl
      _ ≤ 3 := by nlinarith
  have hLaSub : ‖La - 1‖ ≤ u / 2 := by
    have hid : La - 1 = a := by dsimp [La]; noncomm_ring
    simpa [hid] using ha
  have hLbSub : ‖Lb - 1‖ ≤ u := by
    have hid : Lb - 1 = b := by dsimp [Lb]; noncomm_ring
    simpa [hid] using hb
  have hLa : ‖La‖ ≤ 2 := by
    calc
      ‖La‖ = ‖(La - 1) + 1‖ := by congr 1; noncomm_ring
      _ ≤ ‖La - 1‖ + ‖(1 : A)‖ := norm_add_le _ _
      _ ≤ u / 2 + 1 := by
        rw [norm_one]
        exact add_le_add hLaSub le_rfl
      _ ≤ 2 := by nlinarith
  have hLb : ‖Lb‖ ≤ 2 := by
    calc
      ‖Lb‖ = ‖(Lb - 1) + 1‖ := by congr 1; noncomm_ring
      _ ≤ ‖Lb - 1‖ + ‖(1 : A)‖ := norm_add_le _ _
      _ ≤ u + 1 := by
        rw [norm_one]
        exact add_le_add hLbSub le_rfl
      _ ≤ 2 := by nlinarith
  have hpolyIdentity :
      Ta * Tb * Ta - Txy =
        a * b * a +
          (Qa * Tb * Ta - Qa) +
          (La * Qb * Ta - Qb) +
          (La * Lb * Qa - Qa) := by
    dsimp [Ta, Tb, Txy, La, Lb, a, b, Qa, Qb]
    simp only [pow_two, add_mul, mul_add, one_mul, mul_one]
    simp_rw [smul_mul_smul]
    simp only [div_eq_mul_inv]
    module
  have hpoly : ‖Ta * Tb * Ta - Txy‖ ≤ 3 * u ^ (3 : ℕ) := by
    rw [hpolyIdentity]
    calc
      ‖a * b * a + (Qa * Tb * Ta - Qa) +
          (La * Qb * Ta - Qb) + (La * Lb * Qa - Qa)‖ ≤
        ‖a * b * a‖ + ‖Qa * Tb * Ta - Qa‖ +
          ‖La * Qb * Ta - Qb‖ + ‖La * Lb * Qa - Qa‖ := by
            calc
              _ ≤ ‖a * b * a + (Qa * Tb * Ta - Qa) +
                    (La * Qb * Ta - Qb)‖ + ‖La * Lb * Qa - Qa‖ := norm_add_le _ _
              _ ≤ (‖a * b * a + (Qa * Tb * Ta - Qa)‖ +
                    ‖La * Qb * Ta - Qb‖) + ‖La * Lb * Qa - Qa‖ := by
                      gcongr; exact norm_add_le _ _
              _ ≤ ((‖a * b * a‖ + ‖Qa * Tb * Ta - Qa‖) +
                    ‖La * Qb * Ta - Qb‖) + ‖La * Lb * Qa - Qa‖ := by
                      gcongr; exact norm_add_le _ _
              _ = _ := by ring
      _ ≤ (u ^ (3 : ℕ) / 4) + (29 * u ^ (3 : ℕ) / 64) +
          (13 * u ^ (3 : ℕ) / 16) + (u ^ (3 : ℕ) / 4) := by
        have haba : ‖a * b * a‖ ≤ u ^ (3 : ℕ) / 4 := by
          calc
            ‖a * b * a‖ ≤ ‖a‖ * ‖b‖ * ‖a‖ := by
              exact (norm_mul_le _ _).trans
                (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
            _ ≤ (u / 2) * u * (u / 2) := by gcongr
            _ = u ^ (3 : ℕ) / 4 := by ring
        have hqa : ‖Qa * Tb * Ta - Qa‖ ≤ 29 * u ^ (3 : ℕ) / 64 := by
          have hid : Qa * Tb * Ta - Qa = Qa * ((Tb - 1) * Ta + (Ta - 1)) := by
            noncomm_ring
          rw [hid]
          calc
            ‖Qa * ((Tb - 1) * Ta + (Ta - 1))‖ ≤
                ‖Qa‖ * ‖(Tb - 1) * Ta + (Ta - 1)‖ := norm_mul_le _ _
            _ ≤ (u ^ (2 : ℕ) / 8) *
                (‖Tb - 1‖ * ‖Ta‖ + ‖Ta - 1‖) := by
                  gcongr
                  exact (norm_add_le _ _).trans
                    (add_le_add (norm_mul_le _ _) le_rfl)
            _ ≤ (u ^ (2 : ℕ) / 8) * ((3 * u / 2) * 2 + 5 * u / 8) := by gcongr
            _ = 29 * u ^ (3 : ℕ) / 64 := by ring
        have hqb : ‖La * Qb * Ta - Qb‖ ≤ 13 * u ^ (3 : ℕ) / 16 := by
          have hid : La * Qb * Ta - Qb =
              (La - 1) * Qb * Ta + Qb * (Ta - 1) := by noncomm_ring
          rw [hid]
          calc
            ‖(La - 1) * Qb * Ta + Qb * (Ta - 1)‖ ≤
                ‖(La - 1) * Qb * Ta‖ + ‖Qb * (Ta - 1)‖ := norm_add_le _ _
            _ ≤ (‖La - 1‖ * ‖Qb‖) * ‖Ta‖ + ‖Qb‖ * ‖Ta - 1‖ := by
              exact add_le_add
                ((norm_mul_le _ _).trans
                  (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg Ta)))
                (norm_mul_le _ _)
            _ ≤ ((u / 2) * (u ^ (2 : ℕ) / 2)) * 2 +
                (u ^ (2 : ℕ) / 2) * (5 * u / 8) := by gcongr
            _ = 13 * u ^ (3 : ℕ) / 16 := by ring
        have hqlast : ‖La * Lb * Qa - Qa‖ ≤ u ^ (3 : ℕ) / 4 := by
          have hid : La * Lb * Qa - Qa =
              ((La - 1) * Lb + (Lb - 1)) * Qa := by noncomm_ring
          rw [hid]
          calc
            ‖((La - 1) * Lb + (Lb - 1)) * Qa‖ ≤
                ‖(La - 1) * Lb + (Lb - 1)‖ * ‖Qa‖ := norm_mul_le _ _
            _ ≤ (‖La - 1‖ * ‖Lb‖ + ‖Lb - 1‖) * (u ^ (2 : ℕ) / 8) := by
              gcongr
              exact (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) le_rfl)
            _ ≤ ((u / 2) * 2 + u) * (u ^ (2 : ℕ) / 8) := by gcongr
            _ = u ^ (3 : ℕ) / 4 := by ring
        exact add_le_add (add_le_add (add_le_add haba hqa) hqb) hqlast
      _ ≤ 3 * u ^ (3 : ℕ) := by nlinarith [pow_nonneg hu0 3]
  have hRa : ‖exp ((t / 2) • x) - Ta‖ ≤ u ^ (3 : ℕ) / 48 := by
    have h := norm_exp_sub_cstarExponentialTaylor_le x hx 2 (t / 2)
    have hform : cstarExponentialTaylor x 2 (t / 2) = Ta := by
      dsimp [Ta, La, a, Qa]
      rw [cstarExponentialTaylor_two]
    rw [hform] at h
    norm_num at h
    calc
      ‖exp ((t / 2) • x) - Ta‖ ≤ ‖x‖ ^ (3 : ℕ) * |t / 2| ^ (3 : ℕ) / 6 := by simpa using h
      _ ≤ u ^ (3 : ℕ) / 48 := by
        rw [abs_div]
        norm_num
        have hxle : ‖x‖ ≤ ‖x‖ + ‖y‖ := by linarith
        have hcube : ‖x‖ ^ (3 : ℕ) ≤ (‖x‖ + ‖y‖) ^ (3 : ℕ) := by gcongr
        dsimp [u]
        nlinarith [pow_nonneg (abs_nonneg t) 3]
  have hRb : ‖exp (t • y) - Tb‖ ≤ u ^ (3 : ℕ) / 6 := by
    have h := norm_exp_sub_cstarExponentialTaylor_le y hy 2 t
    have hform : cstarExponentialTaylor y 2 t = Tb := by
      dsimp [Tb, Lb, b, Qb]
      rw [cstarExponentialTaylor_two]
    rw [hform] at h
    norm_num at h
    calc
      ‖exp (t • y) - Tb‖ ≤ ‖y‖ ^ (3 : ℕ) * |t| ^ (3 : ℕ) / 6 := by simpa using h
      _ ≤ u ^ (3 : ℕ) / 6 := by
        have hyle : ‖y‖ ≤ ‖x‖ + ‖y‖ := by linarith
        have hcube : ‖y‖ ^ (3 : ℕ) ≤ (‖x‖ + ‖y‖) ^ (3 : ℕ) := by gcongr
        dsimp [u]
        nlinarith [pow_nonneg (abs_nonneg t) 3]
  have hRxy : ‖exp (t • (x + y)) - Txy‖ ≤ u ^ (3 : ℕ) / 6 := by
    have hxy : x + y ∈ skewAdjoint A := (skewAdjoint A).add_mem hx hy
    have h := norm_exp_sub_cstarExponentialTaylor_le (x + y) hxy 2 t
    have hform : cstarExponentialTaylor (x + y) 2 t = Txy := by
      dsimp [Txy]
      rw [cstarExponentialTaylor_two]
    rw [hform] at h
    norm_num at h
    calc
      ‖exp (t • (x + y)) - Txy‖ ≤ ‖x + y‖ ^ (3 : ℕ) * |t| ^ (3 : ℕ) / 6 := by simpa using h
      _ ≤ u ^ (3 : ℕ) / 6 := by
        have hnorm := norm_add_le x y
        have hcube : ‖x + y‖ ^ (3 : ℕ) ≤ (‖x‖ + ‖y‖) ^ (3 : ℕ) := by gcongr
        dsimp [u]
        nlinarith [pow_nonneg (abs_nonneg t) 3]
  have hsplit :
      exp ((t / 2) • x) * exp (t • y) * exp ((t / 2) • x) -
          exp (t • (x + y)) =
        (exp ((t / 2) • x) - Ta) * exp (t • y) * exp ((t / 2) • x) +
        Ta * (exp (t • y) - Tb) * exp ((t / 2) • x) +
        Ta * Tb * (exp ((t / 2) • x) - Ta) +
        (Ta * Tb * Ta - Txy) +
        (Txy - exp (t • (x + y))) := by noncomm_ring
  rw [hsplit]
  have hEx : ‖exp ((t / 2) • x)‖ = 1 :=
    CStarRing.norm_of_mem_unitary
      (exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem (t / 2) hx))
  have hEy : ‖exp (t • y)‖ = 1 :=
    CStarRing.norm_of_mem_unitary
      (exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem t hy))
  calc
    ‖(exp ((t / 2) • x) - Ta) * exp (t • y) * exp ((t / 2) • x) +
        Ta * (exp (t • y) - Tb) * exp ((t / 2) • x) +
        Ta * Tb * (exp ((t / 2) • x) - Ta) +
        (Ta * Tb * Ta - Txy) + (Txy - exp (t • (x + y)))‖ ≤
      ‖(exp ((t / 2) • x) - Ta) * exp (t • y) * exp ((t / 2) • x)‖ +
      ‖Ta * (exp (t • y) - Tb) * exp ((t / 2) • x)‖ +
      ‖Ta * Tb * (exp ((t / 2) • x) - Ta)‖ +
      ‖Ta * Tb * Ta - Txy‖ + ‖Txy - exp (t • (x + y))‖ := by
        calc
          _ ≤ ‖(exp ((t / 2) • x) - Ta) * exp (t • y) * exp ((t / 2) • x) +
                Ta * (exp (t • y) - Tb) * exp ((t / 2) • x) +
                Ta * Tb * (exp ((t / 2) • x) - Ta) +
                (Ta * Tb * Ta - Txy)‖ + ‖Txy - exp (t • (x + y))‖ := norm_add_le _ _
          _ ≤ (‖(exp ((t / 2) • x) - Ta) * exp (t • y) * exp ((t / 2) • x) +
                Ta * (exp (t • y) - Tb) * exp ((t / 2) • x) +
                Ta * Tb * (exp ((t / 2) • x) - Ta)‖ +
                ‖Ta * Tb * Ta - Txy‖) + ‖Txy - exp (t • (x + y))‖ := by
                  gcongr; exact norm_add_le _ _
          _ ≤ ((‖(exp ((t / 2) • x) - Ta) * exp (t • y) * exp ((t / 2) • x) +
                  Ta * (exp (t • y) - Tb) * exp ((t / 2) • x)‖ +
                  ‖Ta * Tb * (exp ((t / 2) • x) - Ta)‖) +
                  ‖Ta * Tb * Ta - Txy‖) + ‖Txy - exp (t • (x + y))‖ := by
                    gcongr; exact norm_add_le _ _
          _ ≤ (((‖(exp ((t / 2) • x) - Ta) * exp (t • y) * exp ((t / 2) • x)‖ +
                  ‖Ta * (exp (t • y) - Tb) * exp ((t / 2) • x)‖) +
                  ‖Ta * Tb * (exp ((t / 2) • x) - Ta)‖) +
                  ‖Ta * Tb * Ta - Txy‖) + ‖Txy - exp (t • (x + y))‖ := by
                    gcongr; exact norm_add_le _ _
          _ = _ := by ring
    _ ≤ (u ^ (3 : ℕ) / 48) + 2 * (u ^ (3 : ℕ) / 6) + 6 * (u ^ (3 : ℕ) / 48) +
          3 * u ^ (3 : ℕ) + u ^ (3 : ℕ) / 6 := by
      have h1 : ‖(exp ((t / 2) • x) - Ta) * exp (t • y) *
          exp ((t / 2) • x)‖ ≤ u ^ (3 : ℕ) / 48 := by
        calc
          _ ≤ (‖exp ((t / 2) • x) - Ta‖ * ‖exp (t • y)‖) *
                ‖exp ((t / 2) • x)‖ := by
            exact (norm_mul_le _ _).trans
              (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
          _ ≤ (u ^ (3 : ℕ) / 48 * 1) * 1 := by
            rw [hEy, hEx]
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hRa (by norm_num)) (by norm_num)
          _ = _ := by ring
      have h2 : ‖Ta * (exp (t • y) - Tb) * exp ((t / 2) • x)‖ ≤
          2 * (u ^ (3 : ℕ) / 6) := by
        calc
          _ ≤ (‖Ta‖ * ‖exp (t • y) - Tb‖) * ‖exp ((t / 2) • x)‖ := by
            exact (norm_mul_le _ _).trans
              (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
          _ ≤ (2 * (u ^ (3 : ℕ) / 6)) * 1 := by
            rw [hEx]
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul hTa hRb (norm_nonneg _) (by positivity)) (by norm_num)
          _ = _ := by ring
      have h3 : ‖Ta * Tb * (exp ((t / 2) • x) - Ta)‖ ≤
          6 * (u ^ (3 : ℕ) / 48) := by
        calc
          _ ≤ (‖Ta‖ * ‖Tb‖) * ‖exp ((t / 2) • x) - Ta‖ := by
            exact (norm_mul_le _ _).trans
              (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
          _ ≤ (2 * 3) * (u ^ (3 : ℕ) / 48) := by
            exact mul_le_mul
              (mul_le_mul hTa hTb (norm_nonneg _) (by positivity)) hRa
              (norm_nonneg _) (by positivity)
          _ = _ := by ring
      have h5 : ‖Txy - exp (t • (x + y))‖ ≤ u ^ (3 : ℕ) / 6 := by
        rw [norm_sub_rev]
        exact hRxy
      exact add_le_add (add_le_add (add_le_add (add_le_add h1 h2) h3) hpoly) h5
    _ ≤ 8 * (‖x‖ + ‖y‖) ^ (3 : ℕ) * |t| ^ (3 : ℕ) := by
      dsimp [u]
      nlinarith [mul_nonneg (pow_nonneg hB0 3)
        (pow_nonneg (abs_nonneg t) 3)]

/-- Recursive symmetric second-order product for a finite generator list. -/
def listStrangProduct (z : List A) (t : ℝ) : A :=
  match z with
  | [] => 1
  | x :: tail =>
      exp ((t / 2) • x) * listStrangProduct tail t * exp ((t / 2) • x)

omit [Nontrivial A] in
/-- The recursive Strang product is one forward half-sweep followed by one
reverse half-sweep. This is the circuit-compilation form of the definition. -/
theorem listStrangProduct_eq_forward_mul_reverse
    (z : List A) (t : ℝ) :
    listStrangProduct z t =
      (z.map fun x => exp ((t / 2) • x)).prod *
        (z.reverse.map fun x => exp ((t / 2) • x)).prod := by
  induction z with
  | nil => simp [listStrangProduct]
  | cons x tail ih =>
      simp only [listStrangProduct, List.map_cons, List.prod_cons,
        List.reverse_cons, List.map_append, List.prod_append, List.map_nil,
        List.prod_nil, ih, mul_one, mul_assoc]

omit [Nontrivial A] in
theorem listStrangProduct_mem_unitary
    (z : List A) (hz : ∀ x ∈ z, x ∈ skewAdjoint A) (t : ℝ) :
    listStrangProduct z t ∈ unitary A := by
  let _ : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A
  induction z with
  | nil => simp [listStrangProduct]
  | cons x tail ih =>
      have hx : x ∈ skewAdjoint A := hz x (by simp)
      have htail : ∀ y ∈ tail, y ∈ skewAdjoint A := by
        intro y hy
        exact hz y (by simp [hy])
      simp only [listStrangProduct]
      exact mul_mem
        (mul_mem
          (exp_mem_unitary_of_mem_skewAdjoint
            (skewAdjoint.smul_mem (t / 2) hx))
          (ih htail))
        (exp_mem_unitary_of_mem_skewAdjoint
          (skewAdjoint.smul_mem (t / 2) hx))

set_option maxHeartbeats 800000 in
/-- Finite-list Strang formula. Its one-step error is cubic rather than the
quadratic error of the Lie product. -/
theorem norm_listStrangProduct_sub_exp_sum_le
    (z : List A) (hz : ∀ x ∈ z, x ∈ skewAdjoint A)
    (t : ℝ) (hsmall : |t| * (z.map norm).sum ≤ 1) :
    ‖listStrangProduct z t - exp (t • z.sum)‖ ≤
      8 * z.length * (z.map norm).sum ^ (3 : ℕ) * |t| ^ (3 : ℕ) := by
  let _ : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A
  induction z with
  | nil => simp [listStrangProduct]
  | cons x tail ih =>
      let B : ℝ := ‖x‖ + (tail.map norm).sum
      have hx : x ∈ skewAdjoint A := hz x (by simp)
      have htail : ∀ y ∈ tail, y ∈ skewAdjoint A := by
        intro y hy
        exact hz y (by simp [hy])
      have htailSum : tail.sum ∈ skewAdjoint A :=
        list_sum_mem_addSubgroup (skewAdjoint A) tail htail
      have htailNorm : ‖tail.sum‖ ≤ (tail.map norm).sum :=
        norm_list_sum_le tail
      have htailNonneg : 0 ≤ (tail.map norm).sum :=
        List.sum_nonneg (by simp)
      have hB0 : 0 ≤ B := by dsimp [B]; positivity
      have htailSmall : |t| * (tail.map norm).sum ≤ 1 := by
        calc
          |t| * (tail.map norm).sum ≤ |t| * B := by
            gcongr
            dsimp [B]
            linarith [norm_nonneg x]
          _ ≤ 1 := by simpa [B] using hsmall
      have hpairSmall : |t| * (‖x‖ + ‖tail.sum‖) ≤ 1 := by
        calc
          |t| * (‖x‖ + ‖tail.sum‖) ≤ |t| * B := by
            gcongr
            dsimp [B]
            linarith
          _ ≤ 1 := by simpa [B] using hsmall
      have hih := ih htail htailSmall
      have hpair := norm_exp_half_mul_exp_mul_exp_half_sub_exp_add_le
        x tail.sum hx htailSum t hpairSmall
      let E : A := exp ((t / 2) • x)
      let Etail : A := exp (t • tail.sum)
      have hEunitary : E ∈ unitary A :=
        exp_mem_unitary_of_mem_skewAdjoint
          (skewAdjoint.smul_mem (t / 2) hx)
      have hsplit :
          E * listStrangProduct tail t * E - exp (t • (x + tail.sum)) =
            E * (listStrangProduct tail t - Etail) * E +
              (E * Etail * E - exp (t • (x + tail.sum))) := by
        noncomm_ring
      simp only [listStrangProduct, List.sum_cons, List.map_cons,
        List.sum_cons, List.length_cons]
      change ‖E * listStrangProduct tail t * E -
          exp (t • (x + tail.sum))‖ ≤ _
      rw [hsplit]
      calc
        ‖E * (listStrangProduct tail t - Etail) * E +
            (E * Etail * E - exp (t • (x + tail.sum)))‖ ≤
          ‖E * (listStrangProduct tail t - Etail) * E‖ +
            ‖E * Etail * E - exp (t • (x + tail.sum))‖ := norm_add_le _ _
        _ = ‖listStrangProduct tail t - Etail‖ +
            ‖E * Etail * E - exp (t • (x + tail.sum))‖ := by
              rw [CStarRing.norm_mul_mem_unitary _ hEunitary,
                CStarRing.norm_mem_unitary_mul _ hEunitary]
        _ ≤ 8 * tail.length * (tail.map norm).sum ^ (3 : ℕ) * |t| ^ (3 : ℕ) +
            8 * (‖x‖ + ‖tail.sum‖) ^ (3 : ℕ) * |t| ^ (3 : ℕ) := by
              exact add_le_add hih (by simpa [E, Etail] using hpair)
        _ ≤ 8 * tail.length * B ^ (3 : ℕ) * |t| ^ (3 : ℕ) +
            8 * B ^ (3 : ℕ) * |t| ^ (3 : ℕ) := by
          have htailB : (tail.map norm).sum ≤ B := by
            dsimp [B]
            linarith [norm_nonneg x]
          have hpairB : ‖x‖ + ‖tail.sum‖ ≤ B := by
            dsimp [B]
            linarith
          have htailCube : (tail.map norm).sum ^ (3 : ℕ) ≤ B ^ (3 : ℕ) := by gcongr
          have hpairCube : (‖x‖ + ‖tail.sum‖) ^ (3 : ℕ) ≤ B ^ (3 : ℕ) := by gcongr
          exact add_le_add (by gcongr) (by gcongr)
        _ = 8 * (tail.length + 1) * B ^ (3 : ℕ) * |t| ^ (3 : ℕ) := by
          ring
        _ = 8 * (((tail.length + 1 : ℕ) : ℝ)) *
            (‖x‖ + (tail.map norm).sum) ^ (3 : ℕ) * |t| ^ (3 : ℕ) := by
          simp [B, Nat.cast_add, Nat.cast_one]

set_option maxHeartbeats 800000 in
/-- Repeating the symmetric list product improves the global simulation
error from `1/r` to `1/r²`. -/
theorem norm_listStrangProduct_pow_sub_exp_sum_le
    (z : List A) (hz : ∀ x ∈ z, x ∈ skewAdjoint A)
    (t : ℝ) (r : ℕ) (hr : 0 < r)
    (hsmall : |t / (r : ℝ)| * (z.map norm).sum ≤ 1) :
    ‖listStrangProduct z (t / (r : ℝ)) ^ r - exp (t • z.sum)‖ ≤
      8 * z.length * (z.map norm).sum ^ (3 : ℕ) * |t| ^ (3 : ℕ) / (r : ℝ) ^ (2 : ℕ) := by
  let _ : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A
  let step : A := listStrangProduct z (t / (r : ℝ))
  let exactStep : A := exp ((t / (r : ℝ)) • z.sum)
  have hstepUnitary : step ∈ unitary A :=
    listStrangProduct_mem_unitary z hz (t / (r : ℝ))
  have hsumSkew : z.sum ∈ skewAdjoint A :=
    list_sum_mem_addSubgroup (skewAdjoint A) z hz
  have hexactUnitary : exactStep ∈ unitary A :=
    exp_mem_unitary_of_mem_skewAdjoint
      (skewAdjoint.smul_mem (t / (r : ℝ)) hsumSkew)
  have hone := norm_listStrangProduct_sub_exp_sum_le
    z hz (t / (r : ℝ)) hsmall
  have hpower := unitary_pow_norm_sub_pow_le
    step exactStep hstepUnitary hexactUnitary r
  have hrReal : (0 : ℝ) < r := by exact_mod_cast hr
  have hexactPow : exactStep ^ r = exp (t • z.sum) := by
    dsimp [exactStep]
    rw [exp_real_smul_pow]
    congr 2
    field_simp
  rw [← hexactPow]
  calc
    ‖step ^ r - exactStep ^ r‖ ≤ (r : ℝ) * ‖step - exactStep‖ := hpower
    _ ≤ (r : ℝ) *
        (8 * z.length * (z.map norm).sum ^ (3 : ℕ) *
          |t / (r : ℝ)| ^ (3 : ℕ)) := by gcongr
    _ = 8 * z.length * (z.map norm).sum ^ (3 : ℕ) * |t| ^ (3 : ℕ) /
        (r : ℝ) ^ (2 : ℕ) := by
      rw [abs_div, abs_of_pos hrReal]
      field_simp

end GaloisForLFunctions.HTGeometry
