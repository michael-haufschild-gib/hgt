import GaloisForLFunctions.RHTower.ZeroDetectionEM
import GaloisForLFunctions.RHTower.ZetaEulerMaclaurinThirdOrder

/-!
# Zero detection from the third-order Euler–Maclaurin formula

At a zero `ρ` of `ζ` in `Re s > 0` the third-order representation gives

`Σ_{n ≤ N} n^{-ρ} = -N^{1-ρ}/(ρ-1) + N^{-ρ}/2 - (ρ/12) N^{-ρ-1} + ρ(ρ+1)(ρ+2) R₃(N, ρ)`,

so the detection polynomial `D_N M_y - 1` satisfies `|D_N M_y(ρ) - 1 + 1| ≤ |M_y(ρ)|·E₃(N, ρ)` with an
explicit remainder `E₃`.  At height `T ≤ |Im ρ| ≤ 2T` and `Re ρ ≥ 1/2`, every term of `E₃` is at most
`T^{-1/20}` once `T^{61/50} ≤ N ≤ 2T^{61/50}`.  With a mollifier of length `y ≤ T^{1/40}` the detection
polynomial therefore has modulus at least `1/2` at every such zero as soon as `T ≥ 2^{120}`.

The detection polynomial has length `Ny ≤ 2T^{1.245}`: short enough that the mean value theorem on it
costs `T^{(2.49+o(1))(1-σ)}`, below the `8/3` needed for short-interval windows of exponent `5/8`.
-/

namespace RHTower

noncomputable section

open Complex

theorem dirichletPoly_eq_sum_Icc (N : ℕ) (s : ℂ) :
    dirichletPoly N s = ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s) := by
  rw [← dpolyC_one, dpolyC_apply]
  simp

/-- At a zero of `ζ` in `Re s > 0` the Dirichlet block equals the negated third-order
correction. -/
theorem dirichletPoly_eq_of_zeta_eq_zero_third {N : ℕ} (hN : 1 ≤ N) {ρ : ℂ} (hσ : 0 < ρ.re)
    (hzero : riemannZeta ρ = 0) :
    dirichletPoly N ρ = -emPole N ρ + (N : ℂ) ^ (-ρ) / 2 - ρ / 12 * (N : ℂ) ^ (-ρ - 1)
      + ρ * (ρ + 1) * (ρ + 2) * zetaBernoulliThirdTail N ρ := by
  have hρ1 : ρ ≠ 1 := riemannZeta_zero_ne_one hzero
  have h := riemannZeta_eq_eulerMaclaurinThird hN hσ hρ1
  rw [hzero, ← dirichletPoly_eq_sum_Icc] at h
  unfold emPole
  linear_combination -h

/-- **The third-order detection identity.** -/
theorem detPolyC_add_one_eq_third {N y : ℕ} (hN : 1 ≤ N) (hy : 1 ≤ y) {ρ : ℂ}
    (hσ : 0 < ρ.re) (hzero : riemannZeta ρ = 0) :
    detPolyC N y ρ + 1 = mollifierC y ρ * (-emPole N ρ + (N : ℂ) ^ (-ρ) / 2
      - ρ / 12 * (N : ℂ) ^ (-ρ - 1) + ρ * (ρ + 1) * (ρ + 2) * zetaBernoulliThirdTail N ρ) := by
  rw [detPolyC_eq hN hy, dirichletPoly_eq_of_zeta_eq_zero_third hN hσ hzero]
  ring

/-- The explicit third-order detection remainder. -/
def detectionRemainderThird (N : ℕ) (ρ : ℂ) : ℝ :=
  (N : ℝ) ^ (1 - ρ.re) / ‖ρ - 1‖ + (N : ℝ) ^ (-ρ.re) / 2 + ‖ρ‖ / 12 * (N : ℝ) ^ (-ρ.re - 1)
    + ‖ρ * (ρ + 1) * (ρ + 2)‖ * ((N : ℝ) ^ (-ρ.re - 2) / (48 * (ρ.re + 2)))

theorem norm_detPolyC_add_one_le_third {N y : ℕ} (hN : 1 ≤ N) (hy : 1 ≤ y) {ρ : ℂ}
    (hσ : 0 < ρ.re) (hzero : riemannZeta ρ = 0) :
    ‖detPolyC N y ρ + 1‖ ≤ ‖mollifierC y ρ‖ * detectionRemainderThird N ρ := by
  have hN0 : 0 < N := by omega
  rw [detPolyC_add_one_eq_third hN hy hσ hzero, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have h1 : ‖-emPole N ρ‖ = (N : ℝ) ^ (1 - ρ.re) / ‖ρ - 1‖ := by
    rw [norm_neg, norm_emPole hN0]
  have h2 : ‖(N : ℂ) ^ (-ρ) / 2‖ = (N : ℝ) ^ (-ρ.re) / 2 := by
    rw [norm_div, Complex.norm_natCast_cpow_of_pos hN0]
    simp
  have h3 : ‖ρ / 12 * (N : ℂ) ^ (-ρ - 1)‖ = ‖ρ‖ / 12 * (N : ℝ) ^ (-ρ.re - 1) := by
    rw [norm_mul, norm_div, Complex.norm_natCast_cpow_of_pos hN0]
    simp
  have h4 : ‖ρ * (ρ + 1) * (ρ + 2) * zetaBernoulliThirdTail N ρ‖
      ≤ ‖ρ * (ρ + 1) * (ρ + 2)‖ * ((N : ℝ) ^ (-ρ.re - 2) / (48 * (ρ.re + 2))) := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_zetaBernoulliThirdTail_le hN (by linarith))
      (norm_nonneg _)
  unfold detectionRemainderThird
  calc ‖-emPole N ρ + (N : ℂ) ^ (-ρ) / 2 - ρ / 12 * (N : ℂ) ^ (-ρ - 1)
        + ρ * (ρ + 1) * (ρ + 2) * zetaBernoulliThirdTail N ρ‖
      ≤ ‖-emPole N ρ‖ + ‖(N : ℂ) ^ (-ρ) / 2‖ + ‖ρ / 12 * (N : ℂ) ^ (-ρ - 1)‖
        + ‖ρ * (ρ + 1) * (ρ + 2) * zetaBernoulliThirdTail N ρ‖ := by
        refine le_trans (norm_add_le _ _) (add_le_add ?_ le_rfl)
        refine le_trans (norm_sub_le _ _) (add_le_add ?_ le_rfl)
        exact norm_add_le _ _
    _ ≤ _ := by rw [h1, h2, h3]; linarith

/-- **Third-order zero detection.**  If the mollified third-order remainder is at most `1/2`, the
detection polynomial has modulus at least `1/2` at the zero. -/
theorem half_le_norm_detPolyC_third {N y : ℕ} (hN : 1 ≤ N) (hy : 1 ≤ y) {ρ : ℂ}
    (hσ : 0 < ρ.re) (hzero : riemannZeta ρ = 0)
    (hsmall : ‖mollifierC y ρ‖ * detectionRemainderThird N ρ ≤ 1 / 2) :
    1 / 2 ≤ ‖detPolyC N y ρ‖ := by
  have hb := le_trans (norm_detPolyC_add_one_le_third hN hy hσ hzero) hsmall
  have htri : (1 : ℝ) ≤ ‖detPolyC N y ρ + 1‖ + ‖detPolyC N y ρ‖ := by
    have h := norm_sub_le (detPolyC N y ρ + 1) (detPolyC N y ρ)
    simpa using h
  linarith

/-! ## The power-parameter regime -/

/-- The mollifier is at most its length on `Re s ≥ 0`. -/
theorem norm_mollifierC_le_length (y : ℕ) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖mollifierC y s‖ ≤ y := by
  refine le_trans (norm_mollifierC_le y s) ?_
  calc ∑ m ∈ Finset.Icc 1 y, (m : ℝ) ^ (-s.re)
      ≤ ∑ _m ∈ Finset.Icc 1 y, (1 : ℝ) := by
        refine Finset.sum_le_sum fun m hm => ?_
        have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hm).1
        exact Real.rpow_le_one_of_one_le_of_nonpos hm1 (by linarith)
    _ = y := by simp

/-- **Every remainder term is below `T^{-1/20}`.**  For `Re ρ ∈ [1/2, 1]`, `T ≤ |Im ρ| ≤ 2T`, `T ≥ 8`
and `T^{61/50} ≤ N ≤ 2T^{61/50}`, the third-order remainder is at most `4 T^{-1/20}`. -/
theorem detectionRemainderThird_le {N : ℕ} {T : ℝ} {ρ : ℂ} (hT : 8 ≤ T)
    (hσ1 : 1 / 2 ≤ ρ.re) (hσ2 : ρ.re ≤ 1) (hγ1 : T ≤ |ρ.im|) (hγ2 : |ρ.im| ≤ 2 * T)
    (hN1 : T ^ (61 / 50 : ℝ) ≤ N) (hN2 : (N : ℝ) ≤ 2 * T ^ (61 / 50 : ℝ)) :
    detectionRemainderThird N ρ ≤ 4 * T ^ (-(1 / 20 : ℝ)) := by
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hA0 : 0 < T ^ (61 / 50 : ℝ) := Real.rpow_pos_of_pos hT0 _
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le hA0 hN1
  set σ := ρ.re with hσdef
  -- the three norms
  have hρ1 : T ≤ ‖ρ - 1‖ := by
    refine le_trans hγ1 (le_trans ?_ (Complex.abs_im_le_norm (ρ - 1)))
    simp
  have hnorm0 : ‖ρ‖ ≤ 3 * T := by
    have := Complex.norm_le_abs_re_add_abs_im ρ
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ ρ.re)] at this
    linarith
  have hnorm1 : ‖ρ + 1‖ ≤ 3 * T := by
    have := Complex.norm_le_abs_re_add_abs_im (ρ + 1)
    simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im, add_zero] at this
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ ρ.re + 1)] at this
    linarith
  have hnorm2 : ‖ρ + 2‖ ≤ 3 * T := by
    have := Complex.norm_le_abs_re_add_abs_im (ρ + 2)
    have h2re : (ρ + 2).re = ρ.re + 2 := by simp
    have h2im : (ρ + 2).im = ρ.im := by simp
    rw [h2re, h2im, abs_of_nonneg (by linarith : (0 : ℝ) ≤ ρ.re + 2)] at this
    linarith
  have hprod : ‖ρ * (ρ + 1) * (ρ + 2)‖ ≤ 27 * T ^ (3 : ℕ) := by
    rw [norm_mul, norm_mul]
    have := mul_le_mul (mul_le_mul hnorm0 hnorm1 (norm_nonneg _) (by linarith)) hnorm2
      (norm_nonneg _) (by positivity)
    nlinarith
  -- the powers of `N`
  have hNa : (N : ℝ) ^ (1 - σ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by
    rcases le_or_gt 1 (N : ℝ) with h | h
    · exact Real.rpow_le_rpow_of_exponent_le h (by linarith)
    · exact absurd (le_trans (Real.one_le_rpow hT1 (by norm_num)) hN1) (by linarith)
  have hN1' : (1 : ℝ) ≤ N := le_trans (Real.one_le_rpow hT1 (by norm_num)) hN1
  have hNb : (N : ℝ) ^ (-σ) ≤ (N : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
  have hNc : (N : ℝ) ^ (-σ - 1) ≤ (N : ℝ) ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
  have hNd : (N : ℝ) ^ (-σ - 2) ≤ (N : ℝ) ^ (-(5 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
  -- `N` against powers of `T`
  have hup : (N : ℝ) ^ (1 / 2 : ℝ) ≤ 2 * T ^ (61 / 100 : ℝ) := by
    calc (N : ℝ) ^ (1 / 2 : ℝ) ≤ (2 * T ^ (61 / 50 : ℝ)) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow hN0.le hN2 (by norm_num)
      _ = 2 ^ (1 / 2 : ℝ) * T ^ (61 / 100 : ℝ) := by
          rw [Real.mul_rpow (by norm_num) hA0.le, ← Real.rpow_mul hT0.le]
          norm_num
      _ ≤ 2 * T ^ (61 / 100 : ℝ) := by
          have h2 : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
            calc (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
              _ = 2 := Real.rpow_one 2
          exact mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hT0.le _)
  have hlow : ∀ c : ℝ, 0 ≤ c → (N : ℝ) ^ (-c) ≤ T ^ (-(61 / 50 : ℝ) * c) := by
    intro c hc
    calc (N : ℝ) ^ (-c) ≤ (T ^ (61 / 50 : ℝ)) ^ (-c) :=
          Real.rpow_le_rpow_of_nonpos hA0 hN1 (by linarith)
      _ = T ^ (-(61 / 50 : ℝ) * c) := by
          rw [← Real.rpow_mul hT0.le]
          ring_nf
  have hmono : ∀ a b : ℝ, a ≤ b → T ^ a ≤ T ^ b := fun a b hab =>
    Real.rpow_le_rpow_of_exponent_le hT1 hab
  -- each term
  have t1 : (N : ℝ) ^ (1 - σ) / ‖ρ - 1‖ ≤ T ^ (-(1 / 20 : ℝ)) := by
    have hnum : (N : ℝ) ^ (1 - σ) ≤ 2 * T ^ (61 / 100 : ℝ) := le_trans hNa hup
    have hq : (N : ℝ) ^ (1 - σ) / ‖ρ - 1‖ ≤ 2 * T ^ (61 / 100 : ℝ) / T := by
      gcongr
    refine le_trans hq ?_
    have h2 : (2 : ℝ) ≤ T ^ (34 / 100 : ℝ) := by
      calc (2 : ℝ) ≤ 8 ^ (34 / 100 : ℝ) := by
            rw [show (8 : ℝ) = 2 ^ (3 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
            calc (2 : ℝ) = 2 ^ (1 : ℝ) := (Real.rpow_one 2).symm
              _ ≤ 2 ^ ((3 : ℝ) * (34 / 100)) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ ≤ T ^ (34 / 100 : ℝ) := Real.rpow_le_rpow (by norm_num) hT (by norm_num)
    have hsplit : T ^ (-(1 / 20 : ℝ)) * T = T ^ (34 / 100 : ℝ) * T ^ (61 / 100 : ℝ) := by
      rw [← Real.rpow_add hT0, ← Real.rpow_add_one hT0.ne']
      norm_num
    rw [div_le_iff₀ hT0, hsplit]
    exact mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hT0.le _)
  have t2 : (N : ℝ) ^ (-σ) / 2 ≤ T ^ (-(1 / 20 : ℝ)) := by
    have h := le_trans hNb (hlow (1 / 2) (by norm_num))
    have h' : T ^ (-(61 / 50 : ℝ) * (1 / 2)) ≤ T ^ (-(1 / 20 : ℝ)) := hmono _ _ (by norm_num)
    have hnn : 0 ≤ (N : ℝ) ^ (-σ) := Real.rpow_nonneg hN0.le _
    linarith
  have t3 : ‖ρ‖ / 12 * (N : ℝ) ^ (-σ - 1) ≤ T ^ (-(1 / 20 : ℝ)) := by
    have hc := le_trans hNc (hlow (3 / 2) (by norm_num))
    have hnn : 0 ≤ (N : ℝ) ^ (-σ - 1) := Real.rpow_nonneg hN0.le _
    have h1 : ‖ρ‖ / 12 * (N : ℝ) ^ (-σ - 1) ≤ T * T ^ (-(61 / 50 : ℝ) * (3 / 2)) := by
      have := mul_le_mul (show ‖ρ‖ / 12 ≤ T by linarith) hc hnn hT0.le
      linarith
    refine le_trans h1 ?_
    rw [← Real.rpow_one_add' hT0.le (by norm_num)]
    exact hmono _ _ (by norm_num)
  have t4 : ‖ρ * (ρ + 1) * (ρ + 2)‖ * ((N : ℝ) ^ (-σ - 2) / (48 * (σ + 2)))
      ≤ T ^ (-(1 / 20 : ℝ)) := by
    have hd := le_trans hNd (hlow (5 / 2) (by norm_num))
    have hnn : 0 ≤ (N : ℝ) ^ (-σ - 2) := Real.rpow_nonneg hN0.le _
    have hden : (N : ℝ) ^ (-σ - 2) / (48 * (σ + 2)) ≤ (N : ℝ) ^ (-σ - 2) / 27 := by
      apply div_le_div_of_nonneg_left hnn (by norm_num)
      linarith
    have h1 : ‖ρ * (ρ + 1) * (ρ + 2)‖ * ((N : ℝ) ^ (-σ - 2) / (48 * (σ + 2)))
        ≤ 27 * T ^ (3 : ℕ) * ((N : ℝ) ^ (-σ - 2) / 27) :=
      mul_le_mul hprod hden (by positivity) (by positivity)
    refine le_trans h1 ?_
    have h2 : 27 * T ^ (3 : ℕ) * ((N : ℝ) ^ (-σ - 2) / 27)
        ≤ T ^ (3 : ℕ) * T ^ (-(61 / 50 : ℝ) * (5 / 2)) := by
      have : 27 * T ^ (3 : ℕ) * ((N : ℝ) ^ (-σ - 2) / 27) = T ^ (3 : ℕ) * (N : ℝ) ^ (-σ - 2) := by
        ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hd (by positivity)
    refine le_trans h2 (le_of_eq ?_)
    rw [← Real.rpow_natCast, ← Real.rpow_add hT0]
    norm_num
  unfold detectionRemainderThird
  rw [← hσdef]
  linarith

/-- **Detection at every zero of the height box.**  For `T ≥ 2^{120}`, a mollifier length
`1 ≤ y ≤ T^{1/40}` and a block length `T^{61/50} ≤ N ≤ 2T^{61/50}`, every zero `ρ` of `ζ` with
`1/2 ≤ Re ρ ≤ 1` and `T ≤ |Im ρ| ≤ 2T` makes the detection polynomial `D_N M_y - 1` at least `1/2`
in modulus. -/
theorem half_le_norm_detPolyC_of_height {N y : ℕ} {T : ℝ} {ρ : ℂ}
    (hT : (2 : ℝ) ^ (120 : ℕ) ≤ T) (hy : 1 ≤ y) (hyT : (y : ℝ) ≤ T ^ (1 / 40 : ℝ))
    (hN1 : T ^ (61 / 50 : ℝ) ≤ N) (hN2 : (N : ℝ) ≤ 2 * T ^ (61 / 50 : ℝ))
    (hσ1 : 1 / 2 ≤ ρ.re) (hσ2 : ρ.re ≤ 1) (hγ1 : T ≤ |ρ.im|) (hγ2 : |ρ.im| ≤ 2 * T)
    (hzero : riemannZeta ρ = 0) :
    1 / 2 ≤ ‖detPolyC N y ρ‖ := by
  have h8 : (8 : ℝ) ≤ T := le_trans (by norm_num) hT
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hN : 1 ≤ N := by
    have : (1 : ℝ) ≤ N := le_trans (Real.one_le_rpow hT1 (by norm_num)) hN1
    exact_mod_cast this
  refine half_le_norm_detPolyC_third hN hy (by linarith) hzero ?_
  have hE := detectionRemainderThird_le h8 hσ1 hσ2 hγ1 hγ2 hN1 hN2
  have hM := norm_mollifierC_le_length y (s := ρ) (by linarith)
  have hE0 : 0 ≤ detectionRemainderThird N ρ := by
    unfold detectionRemainderThird
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have h2 : (0 : ℝ) < 48 * (ρ.re + 2) := by linarith
    positivity
  have hprod : ‖mollifierC y ρ‖ * detectionRemainderThird N ρ
      ≤ T ^ (1 / 40 : ℝ) * (4 * T ^ (-(1 / 20 : ℝ))) :=
    mul_le_mul (le_trans hM hyT) hE hE0 (Real.rpow_nonneg hT0.le _)
  refine le_trans hprod ?_
  have hcomb : T ^ (1 / 40 : ℝ) * (4 * T ^ (-(1 / 20 : ℝ))) = 4 * T ^ (-(1 / 40 : ℝ)) := by
    rw [mul_left_comm, ← Real.rpow_add hT0]
    norm_num
  rw [hcomb]
  have h8' : (8 : ℝ) ≤ T ^ (1 / 40 : ℝ) := by
    calc (8 : ℝ) = ((2 : ℝ) ^ (120 : ℕ)) ^ (1 / 40 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
          norm_num
      _ ≤ T ^ (1 / 40 : ℝ) := Real.rpow_le_rpow (by positivity) hT (by norm_num)
  have hinv : T ^ (-(1 / 40 : ℝ)) = (T ^ (1 / 40 : ℝ))⁻¹ := Real.rpow_neg hT0.le _
  rw [hinv]
  have hpos : 0 < T ^ (1 / 40 : ℝ) := Real.rpow_pos_of_pos hT0 _
  rw [← div_eq_mul_inv, div_le_iff₀ hpos]
  linarith

end

end RHTower
