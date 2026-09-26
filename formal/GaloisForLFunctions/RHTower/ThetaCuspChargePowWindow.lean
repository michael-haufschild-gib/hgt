import GaloisForLFunctions.RHTower.ThetaCuspChargeHardyRigidity

open Complex UpperHalfPlane ModularGroup
open scoped MatrixGroups Real

namespace RHTower

noncomputable section

open Bottcher

/-- **Farey-type bound for `θ₃hⁿ⁺¹ = θ₂^{4(n+1)}θ₄^{4(n+1)}/θ₃^{8n+7}`.** -/
theorem norm_thetaForm_farey_pow (n : ℕ) (τ : ℍ) :
    ∃ g : SL(2, ℤ), (4 : ℝ) / 5 ≤ (g • τ).im ∧
      ‖thetaTwo τ ^ (4 * (n + 1)) * thetaFour τ ^ (4 * (n + 1)) / thetaThree τ ^ (8 * n + 7)‖ ≤
        3 ^ (8 * (n + 1)) * 2 ^ (8 * (n + 1)) * ‖slDen g τ‖ ^ (-(1 / 2 : ℝ)) *
          (if Odd (g 1 0) ∧ Odd (g 1 1) then
            Real.exp ((8 * n + 7 : ℕ) * Real.pi / 4 * (g • τ).im) else 1) := by
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd τ
  refine ⟨g, ?_, ?_⟩
  · have h3 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hg
    have hpos := (g • τ).im_pos
    nlinarith
  set z' : ℍ := g • τ with hz'
  have him : (4 : ℝ) / 5 ≤ (z' : ℂ).im := by
    have h3 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hg
    have hpos := z'.im_pos
    show (4 : ℝ) / 5 ≤ z'.im
    nlinarith
  have hτeq : (τ : ℂ) = ((g⁻¹ • z' : ℍ) : ℂ) := by rw [hz', inv_smul_smul]
  have hlaw := thetaModulusLaw g⁻¹ z'
  set D : ℝ := ‖slDen g⁻¹ (z' : ℂ)‖ with hD
  have hcoc := slDen_mul g⁻¹ g τ
  rw [inv_mul_cancel, slDen_one, ← hz'] at hcoc
  have hDpos : 0 < D := norm_pos_iff.mpr (slDen_ne_zero _ _)
  have hGpos : 0 < ‖slDen g (τ : ℂ)‖ := norm_pos_iff.mpr (slDen_ne_zero _ _)
  have hDG : D * ‖slDen g (τ : ℂ)‖ = 1 := by rw [hD, ← norm_mul, ← hcoc, norm_one]
  have hDhalf : D ^ (1 / 2 : ℝ) = ‖slDen g (τ : ℂ)‖ ^ (-(1 / 2 : ℝ)) := by
    have : D = ‖slDen g (τ : ℂ)‖⁻¹ := by field_simp; linarith
    rw [this, Real.inv_rpow hGpos.le, Real.rpow_neg hGpos.le]
  set a2 := charAct ![0, 1] (slRed g⁻¹)
  set a3 := charAct ![1, 1] (slRed g⁻¹)
  set a4 := charAct ![1, 0] (slRed g⁻¹)
  have hn2 : (![0, 1] : Fin 2 → ZMod 2) ≠ 0 := by decide
  have hn3 : (![1, 1] : Fin 2 → ZMod 2) ≠ 0 := by decide
  have hn4 : (![1, 0] : Fin 2 → ZMod 2) ≠ 0 := by decide
  have e2 := hlaw _ hn2
  have e3 := hlaw _ hn3
  have e4 := hlaw _ hn4
  rw [thetaChar_two, ← hτeq] at e2
  rw [thetaChar_three, ← hτeq] at e3
  rw [thetaChar_four, ← hτeq] at e4
  have ha2 : a2 ≠ 0 := charAct_ne_zero hn2 _
  have ha3 : a3 ≠ 0 := charAct_ne_zero hn3 _
  have ha4 : a4 ≠ 0 := charAct_ne_zero hn4 _
  -- injectivity of the action separates the images
  have hinj : ∀ {u v : Fin 2 → ZMod 2}, charAct u (slRed g⁻¹) = charAct v (slRed g⁻¹) → u = v := by
    intro u v h
    have := congrArg (fun w => charAct w (slRed g⁻¹)⁻¹) h
    simp only [← charAct_mul, mul_inv_cancel] at this
    simpa [charAct] using this
  set A := ‖thetaChar a2 (z' : ℂ)‖
  set B := ‖thetaChar a3 (z' : ℂ)‖
  set C := ‖thetaChar a4 (z' : ℂ)‖
  have hA3 : A ≤ 3 := norm_thetaChar_le_three ha2 him
  have hC3 : C ≤ 3 := norm_thetaChar_le_three ha4 him
  have hA0 : 0 ≤ A := norm_nonneg _
  have hC0 : 0 ≤ C := norm_nonneg _
  have hθ3ne : thetaThree (τ : ℂ) ≠ 0 := thetaThree_ne_zero_of_im_pos τ.im_pos
  have hB0 : 0 < B := by
    have : ‖thetaThree (τ : ℂ)‖ = D ^ (1 / 2 : ℝ) * B := e3
    have h' : 0 < ‖thetaThree (τ : ℂ)‖ := norm_pos_iff.mpr hθ3ne
    rw [this] at h'
    exact pos_of_mul_pos_right h' (Real.rpow_nonneg hDpos.le _)
  set pp : ℕ := 4 * (n + 1) with hpp
  set mm : ℕ := 8 * n + 7 with hmm
  have hpm : pp + pp = mm + 1 := by omega
  have hnorm : ‖thetaTwo τ ^ pp * thetaFour τ ^ pp / thetaThree τ ^ mm‖ =
      D ^ (1 / 2 : ℝ) * (A ^ pp * C ^ pp / B ^ mm) := by
    rw [norm_div, norm_mul, norm_pow, norm_pow, norm_pow, e2, e3, e4]
    set sD := D ^ (1 / 2 : ℝ) with hsD
    have hs : 0 < sD := Real.rpow_pos_of_pos hDpos _
    have hsp : sD ^ pp * sD ^ pp = sD ^ mm * sD := by
      rw [← pow_add, hpm, pow_succ]
    rw [mul_pow, mul_pow, mul_pow]
    have hBm : 0 < B ^ mm := pow_pos hB0 mm
    field_simp
    linear_combination (A ^ pp * C ^ pp) * hsp
  rw [hnorm, hDhalf]
  have hSpos : 0 < ‖slDen g (τ : ℂ)‖ ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hGpos _
  have hK1 : (1 : ℝ) ≤ 3 ^ (8 * (n + 1)) := one_le_pow₀ (by norm_num)
  have hK2 : (1 : ℝ) ≤ 2 ^ (8 * (n + 1)) := one_le_pow₀ (by norm_num)
  by_cases hpar : Odd (g 1 0) ∧ Odd (g 1 1)
  · rw [if_pos hpar]
    have ha3eq : a3 = ![0, 1] := (charAct_three_inv_eq_two_iff g).mpr hpar
    have ha2ne : a2 ≠ ![0, 1] := by
      intro h; exact absurd (hinj (h.trans ha3eq.symm)) (by decide)
    have ha4ne : a4 ≠ ![0, 1] := by
      intro h; exact absurd (hinj (h.trans ha3eq.symm)) (by decide)
    have hA2 : A ≤ 2 := norm_thetaChar_le_two ha2 ha2ne him
    have hC2 : C ≤ 2 := norm_thetaChar_le_two ha4 ha4ne him
    have hBlo : Real.exp (-Real.pi * (z' : ℂ).im / 4) ≤ B := by
      have := (norm_thetaTwo_bounds him).1
      simp only [B, ha3eq, thetaChar_two]; exact this
    have hE : 0 < Real.exp (-Real.pi * (z' : ℂ).im / 4) := Real.exp_pos _
    have hBm : Real.exp (-Real.pi * (z' : ℂ).im / 4) ^ mm ≤ B ^ mm := pow_le_pow_left₀ hE.le hBlo mm
    have hEm : Real.exp (-Real.pi * (z' : ℂ).im / 4) ^ mm *
        Real.exp ((mm : ℕ) * Real.pi / 4 * (g • τ).im) = 1 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      have : ((mm : ℕ) : ℝ) * (-Real.pi * (z' : ℂ).im / 4) + (mm : ℕ) * Real.pi / 4 * (g • τ).im = 0 := by
        rw [hz']; simp only [UpperHalfPlane.coe_im]; try ring
      rw [this, Real.exp_zero]
    have hnum : A ^ pp * C ^ pp ≤ 2 ^ (8 * (n + 1)) := by
      have h1 : A ^ pp ≤ 2 ^ pp := pow_le_pow_left₀ hA0 hA2 pp
      have h2 : C ^ pp ≤ 2 ^ pp := pow_le_pow_left₀ hC0 hC2 pp
      have h3 : (2 : ℝ) ^ pp * 2 ^ pp = 2 ^ (8 * (n + 1)) := by rw [← pow_add, show pp + pp = 8 * (n + 1) by omega]
      calc A ^ pp * C ^ pp ≤ 2 ^ pp * 2 ^ pp :=
            mul_le_mul h1 h2 (pow_nonneg hC0 _) (by positivity)
        _ = _ := h3
    have hX := Real.exp_pos ((mm : ℕ) * Real.pi / 4 * (g • τ).im)
    have hkey : A ^ pp * C ^ pp / B ^ mm ≤
        3 ^ (8 * (n + 1)) * 2 ^ (8 * (n + 1)) * Real.exp ((mm : ℕ) * Real.pi / 4 * (g • τ).im) := by
      rw [div_le_iff₀ (pow_pos hB0 mm)]
      have hEmp : 0 < Real.exp (-Real.pi * (z' : ℂ).im / 4) ^ mm := pow_pos hE mm
      calc A ^ pp * C ^ pp ≤ 2 ^ (8 * (n + 1)) := hnum
        _ = 2 ^ (8 * (n + 1)) * (Real.exp (-Real.pi * (z' : ℂ).im / 4) ^ mm *
              Real.exp ((mm : ℕ) * Real.pi / 4 * (g • τ).im)) := by rw [hEm, mul_one]
        _ = 2 ^ (8 * (n + 1)) * Real.exp ((mm : ℕ) * Real.pi / 4 * (g • τ).im) *
              Real.exp (-Real.pi * (z' : ℂ).im / 4) ^ mm := by ring
        _ ≤ 2 ^ (8 * (n + 1)) * Real.exp ((mm : ℕ) * Real.pi / 4 * (g • τ).im) * B ^ mm :=
            mul_le_mul_of_nonneg_left hBm (by positivity)
        _ ≤ 3 ^ (8 * (n + 1)) * (2 ^ (8 * (n + 1)) *
              Real.exp ((mm : ℕ) * Real.pi / 4 * (g • τ).im) * B ^ mm) :=
            le_mul_of_one_le_left (by positivity) hK1
        _ = 3 ^ (8 * (n + 1)) * 2 ^ (8 * (n + 1)) *
              Real.exp ((mm : ℕ) * Real.pi / 4 * (g • τ).im) * B ^ mm := by ring
    calc ‖slDen g (τ : ℂ)‖ ^ (-(1 / 2 : ℝ)) * (A ^ pp * C ^ pp / B ^ mm)
        ≤ ‖slDen g (τ : ℂ)‖ ^ (-(1 / 2 : ℝ)) *
            (3 ^ (8 * (n + 1)) * 2 ^ (8 * (n + 1)) *
              Real.exp ((mm : ℕ) * Real.pi / 4 * (g • τ).im)) :=
          mul_le_mul_of_nonneg_left hkey hSpos.le
      _ = _ := by ring
  · rw [if_neg hpar, mul_one]
    have ha3ne : a3 ≠ ![0, 1] := fun h => hpar ((charAct_three_inv_eq_two_iff g).mp h)
    have hBlo : 1 / 2 ≤ B := half_le_norm_thetaChar ha3 ha3ne him
    have hnum : A ^ pp * C ^ pp ≤ 3 ^ (8 * (n + 1)) := by
      have h1 : A ^ pp ≤ 3 ^ pp := pow_le_pow_left₀ hA0 hA3 pp
      have h2 : C ^ pp ≤ 3 ^ pp := pow_le_pow_left₀ hC0 hC3 pp
      have h3 : (3 : ℝ) ^ pp * 3 ^ pp = 3 ^ (8 * (n + 1)) := by rw [← pow_add, show pp + pp = 8 * (n + 1) by omega]
      calc A ^ pp * C ^ pp ≤ 3 ^ pp * 3 ^ pp :=
            mul_le_mul h1 h2 (pow_nonneg hC0 _) (by positivity)
        _ = _ := h3
    have hBm : (1 / 2 : ℝ) ^ mm ≤ B ^ mm := pow_le_pow_left₀ (by norm_num) hBlo mm
    have h2m : (2 : ℝ) ^ mm * (1 / 2) ^ mm = 1 := by rw [← mul_pow]; norm_num
    have h2le : (2 : ℝ) ^ mm ≤ 2 ^ (8 * (n + 1)) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hkey : A ^ pp * C ^ pp / B ^ mm ≤ 3 ^ (8 * (n + 1)) * 2 ^ (8 * (n + 1)) := by
      rw [div_le_iff₀ (pow_pos hB0 mm)]
      calc A ^ pp * C ^ pp ≤ 3 ^ (8 * (n + 1)) := hnum
        _ = 3 ^ (8 * (n + 1)) * (2 ^ mm * (1 / 2) ^ mm) := by rw [h2m, mul_one]
        _ ≤ 3 ^ (8 * (n + 1)) * (2 ^ (8 * (n + 1)) * B ^ mm) := by
            gcongr
        _ = _ := by ring
    calc ‖slDen g (τ : ℂ)‖ ^ (-(1 / 2 : ℝ)) * (A ^ pp * C ^ pp / B ^ mm)
        ≤ ‖slDen g (τ : ℂ)‖ ^ (-(1 / 2 : ℝ)) * (3 ^ (8 * (n + 1)) * 2 ^ (8 * (n + 1))) :=
          mul_le_mul_of_nonneg_left hkey hSpos.le
      _ = _ := by ring

/-- The normalized cusp error of `θ₄^{4(n+1)}θ₃^{4(n+1)}/θ₂^{8n+7}`. -/
def chargeErrPow (n : ℕ) (v : ℂ) : ℂ :=
  2 ^ (8 * n + 7) * thetaFour v ^ (4 * (n + 1)) * thetaThree v ^ (4 * (n + 1)) /
    jacobiTheta₂ (v / 2) v ^ (8 * n + 7) - 1

/-- **Exact window law at the pole cusp for `θ₃hⁿ⁺¹`.** -/
theorem thetaGroupBasis_succ_window (n : ℕ) {v : ℂ} (hv : 0 < v.im) :
    thetaGroupBasis (n + 1) (1 + -1 / v) = (-1) ^ (n + 1) * (-Complex.I * v) ^ (1 / 2 : ℂ) *
      ((2 : ℂ) ^ (8 * n + 7))⁻¹ * Complex.exp (-((8 * n + 7 : ℕ) * π * Complex.I * v / 4)) *
        (1 + chargeErrPow n v) := by
  have hv0 : v ≠ 0 := fun h => by rw [h] at hv; simp at hv
  set τ₀ : ℂ := -1 / v with hτ₀
  set P : ℂ := (-Complex.I * v) ^ (1 / 2 : ℂ) with hP
  have hIv : Complex.I / v = (-Complex.I * v)⁻¹ := by
    field_simp; exact Complex.I_sq
  have hQ : (Complex.I / v) ^ (1 / 2 : ℂ) = P⁻¹ := by
    rw [hIv, Complex.inv_cpow _ _ (arg_neg_I_mul_ne_pi hv)]
  have hP0 : P ≠ 0 := by
    rw [hP]; intro h
    rw [Complex.cpow_eq_zero_iff] at h
    exact (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hv0) h.1
  have h2 := thetaTwo_S v hv0
  have h3 := thetaThree_S v hv0
  have h4 := thetaFour_S v hv0
  rw [hQ, one_div, inv_inv] at h2 h4
  rw [← hP] at h3
  have ht2 : thetaTwo v ≠ 0 := thetaTwo_ne_zero_of_im_pos hv
  have ht3 : thetaThree v ≠ 0 := thetaThree_ne_zero_of_im_pos hv
  have ht4 : thetaFour v ≠ 0 := thetaFour_ne_zero_of_im_pos hv
  have hθ2 : thetaTwo v = Complex.exp (π * Complex.I * v / 4) * jacobiTheta₂ (v / 2) v := rfl
  have hJ0 : jacobiTheta₂ (v / 2) v ≠ 0 := by
    intro h; apply ht2; rw [hθ2, h, mul_zero]
  set E : ℂ := Complex.exp (π * Complex.I * v / 4) with hE
  set J : ℂ := jacobiTheta₂ (v / 2) v with hJ
  have hE0 : E ≠ 0 := Complex.exp_ne_zero _
  have hexp : E ^ (8 * n + 7) * Complex.exp (-((8 * n + 7 : ℕ) * π * Complex.I * v / 4)) = 1 := by
    rw [hE, ← Complex.exp_nat_mul, ← Complex.exp_add]; ring_nf; simp
  have hbasis : thetaGroupBasis (n + 1) (1 + τ₀) =
      thetaFour τ₀ * (-(thetaTwo τ₀ ^ 4) * thetaThree τ₀ ^ 4 / thetaFour τ₀ ^ 8) ^ (n + 1) := by
    unfold thetaGroupBasis thetaGroupHauptmodul
    rw [add_comm, thetaThree_add_one, thetaTwo_pow4_add_one, thetaFour_add_one]
  have hinner : -(thetaTwo τ₀ ^ 4) * thetaThree τ₀ ^ 4 / thetaFour τ₀ ^ 8 =
      -(thetaFour v ^ 4 * thetaThree v ^ 4 / thetaTwo v ^ 8) := by
    rw [h2, h3, h4]; field_simp
  rw [hbasis, hinner, h4, hθ2]
  unfold chargeErrPow
  rw [add_sub_cancel]
  have hX : (thetaFour v ^ 4 * thetaThree v ^ 4) ^ (n + 1) =
      thetaFour v ^ (4 * (n + 1)) * thetaThree v ^ (4 * (n + 1)) := by
    rw [mul_pow, ← pow_mul, ← pow_mul]
  rw [neg_eq_neg_one_mul (thetaFour v ^ 4 * thetaThree v ^ 4 / (E * J) ^ 8), mul_pow, div_pow, hX]
  have hJm : J ^ (8 * n + 7) ≠ 0 := pow_ne_zero _ hJ0
  have hpow : ((E * J) ^ 8) ^ (n + 1) = (E * J) ^ (8 * n + 7) * (E * J) := by
    rw [← pow_mul, show 8 * (n + 1) = 8 * n + 7 + 1 by ring, pow_succ]
  rw [hpow, ← hJ]
  field_simp
  linear_combination (-(J ^ (8 * n + 7))) * hexp

theorem one_add_pow_le_exp_mul {r : ℝ} (hr : 0 ≤ r) (N : ℕ) : (1 + r) ^ N ≤ Real.exp (N * r) := by
  have h := Real.add_one_le_exp r
  calc (1 + r) ^ N ≤ Real.exp r ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
    _ = Real.exp (N * r) := by rw [← Real.exp_nat_mul]

theorem norm_one_add_pow_sub_one_le_small {w : ℂ} {N : ℕ} (hw : N * ‖w‖ ≤ 1) :
    ‖(1 + w) ^ N - 1‖ ≤ 2 * (N * ‖w‖) := by
  have h1 := norm_one_add_pow_sub_one_le_charge w N
  have h2 := one_add_pow_le_exp_mul (norm_nonneg w) N
  have hNw : 0 ≤ (N : ℝ) * ‖w‖ := mul_nonneg (Nat.cast_nonneg N) (norm_nonneg w)
  have h3 := Real.abs_exp_sub_one_le (x := N * ‖w‖) (by rw [abs_of_nonneg hNw]; exact hw)
  rw [abs_of_nonneg hNw] at h3
  have h4 : Real.exp (N * ‖w‖) - 1 ≤ 2 * (N * ‖w‖) := by
    have := le_abs_self (Real.exp (N * ‖w‖) - 1); linarith
  linarith

theorem norm_chargeErrPow_le (n : ℕ) {v : ℂ} (h2 : 2 ≤ v.im)
    (hsmall : 600 * (n + 1) * Real.exp (-(π / 2 * v.im)) ≤ 1) : ‖chargeErrPow n v‖ ≤ 1 / 8 := by
  have hv0 : 0 < v.im := by linarith
  set e : ℝ := Real.exp (-(π / 2 * v.im)) with he
  have hepos : 0 < e := Real.exp_pos _
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  have he1 : e ≤ 1 / (600 * (n + 1)) := by rw [le_div_iff₀ (by positivity)]; linarith
  have hepi : e ≤ Real.exp (-π) := Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  have hK := jacobiThetaTailConstant_mul_exp_neg_pi_lt
  have hKpos := jacobiThetaTailConstant_pos
  have hsq : Real.exp (-π * v.im) = e * e := by rw [he, ← Real.exp_add]; congr 1; ring
  have hxy : jacobiThetaTailConstant * Real.exp (-π * v.im) ≤ 1 / (1200 * (n + 1)) := by
    rw [hsq]
    have : jacobiThetaTailConstant * e ≤ 1 / 2 := by
      have := mul_le_mul_of_nonneg_left hepi hKpos.le; linarith
    have h5 : jacobiThetaTailConstant * (e * e) ≤ 1 / 2 * e := by nlinarith
    have h6 : 1 / 2 * e ≤ 1 / 2 * (1 / (600 * (n + 1))) := by linarith
    calc jacobiThetaTailConstant * (e * e) ≤ 1 / 2 * (1 / (600 * (n + 1))) := le_trans h5 h6
      _ = 1 / (1200 * (n + 1)) := by field_simp; ring
  set x : ℂ := thetaThree v - 1 with hx_def
  set y : ℂ := thetaFour v - 1 with hy_def
  set z : ℂ := jacobiTheta₂ (v / 2) v / 2 - 1 with hz_def
  have hx : ‖x‖ ≤ 1 / (1200 * (n + 1)) := le_trans (norm_thetaThree_sub_one_le (by linarith)) hxy
  have hy : ‖y‖ ≤ 1 / (1200 * (n + 1)) := le_trans (norm_thetaFour_sub_one_le (by linarith)) hxy
  have hz : ‖z‖ ≤ 1 / (400 * (n + 1)) := by
    have h1 := norm_jacobiTheta₂_half_sub_two_le_exp (τ := v) (by linarith)
    have hzeq : z = (jacobiTheta₂ (v / 2) v - 2) / 2 := by rw [hz_def]; ring
    rw [hzeq, norm_div, Complex.norm_ofNat]
    have : 3 * e / 2 ≤ 1 / (400 * (n + 1)) := by
      rw [le_div_iff₀ (by positivity)]; rw [le_div_iff₀ (by positivity)] at he1; nlinarith
    calc ‖jacobiTheta₂ (v / 2) v - 2‖ / 2 ≤ 3 * e / 2 := by rw [he]; linarith
      _ ≤ _ := this
  have h3 : thetaThree v = 1 + x := by rw [hx_def]; ring
  have h4 : thetaFour v = 1 + y := by rw [hy_def]; ring
  have hJ : jacobiTheta₂ (v / 2) v = 2 * (1 + z) := by rw [hz_def]; ring
  have hzsmall : ‖z‖ ≤ 1 / 400 := le_trans hz (by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith)
  have hz1 : 1 - ‖z‖ ≤ ‖(1 : ℂ) + z‖ := by
    have h5 : ‖(1:ℂ)‖ ≤ ‖1 + z‖ + ‖z‖ := by
      calc ‖(1:ℂ)‖ = ‖(1 + z) + -z‖ := by ring_nf
        _ ≤ ‖1 + z‖ + ‖-z‖ := norm_add_le _ _
        _ = ‖1 + z‖ + ‖z‖ := by rw [norm_neg]
    rw [norm_one] at h5; linarith
  have hz0 : (1 : ℂ) + z ≠ 0 := by
    intro h; rw [h, norm_zero] at hz1; linarith
  set w : ℂ := x + y + x * y with hw
  have hwb : ‖w‖ ≤ 1 / (400 * (n + 1)) := by
    have hxy1 : ‖x‖ * ‖y‖ ≤ ‖x‖ := by
      have : ‖y‖ ≤ 1 := le_trans hy (by rw [div_le_one (by positivity)]; nlinarith)
      nlinarith [norm_nonneg x]
    calc ‖w‖ ≤ ‖x‖ + ‖y‖ + ‖x‖ * ‖y‖ := by
          refine le_trans (norm_add_le _ _) ?_
          rw [norm_mul]; linarith [norm_add_le x y]
      _ ≤ 3 * (1 / (1200 * (n + 1))) := by linarith
      _ = 1 / (400 * (n + 1)) := by field_simp; ring
  have hNa : ((4 * (n + 1) : ℕ) : ℝ) = 4 * (n + 1) := by push_cast; ring
  have hNb : ((8 * n + 7 : ℕ) : ℝ) = 8 * n + 7 := by push_cast; ring
  have hA : ‖(1 + w) ^ (4 * (n + 1)) - 1‖ ≤ 2 / 100 := by
    have hb : ((4 * (n + 1)) : ℝ) * ‖w‖ ≤ 1 / 100 := by
      calc 4 * ((n : ℝ) + 1) * ‖w‖ ≤ 4 * (n + 1) * (1 / (400 * (n + 1))) := by gcongr
        _ = 1 / 100 := by field_simp; ring
    have := norm_one_add_pow_sub_one_le_small (w := w) (N := (4 * (n + 1))) (by rw [hNa]; linarith)
    rw [hNa] at this; linarith
  have hB : ‖(1 + z) ^ (8 * n + 7) - 1‖ ≤ 4 / 100 := by
    have hb : ((8 * n + 7) : ℝ) * ‖z‖ ≤ 2 / 100 := by
      calc (8 * (n : ℝ) + 7) * ‖z‖ ≤ (8 * n + 8) * (1 / (400 * (n + 1))) := by
            gcongr; linarith
        _ = 2 / 100 := by field_simp; ring
    have := norm_one_add_pow_sub_one_le_small (w := z) (N := (8 * n + 7)) (by rw [hNb]; linarith)
    rw [hNb] at this; linarith
  have hden : 98 / 100 ≤ ‖(1 + z) ^ (8 * n + 7)‖ := by
    rw [norm_pow]
    have hb : ((8 * n + 7) : ℝ) * ‖z‖ ≤ 2 / 100 := by
      calc (8 * (n : ℝ) + 7) * ‖z‖ ≤ (8 * n + 8) * (1 / (400 * (n + 1))) := by
            gcongr; linarith
        _ = 2 / 100 := by field_simp; ring
    have hber := one_add_mul_le_pow (a := -‖z‖) (by linarith [norm_nonneg z]) (8 * n + 7)
    rw [hNb] at hber
    have hmono : (1 + -‖z‖) ^ (8 * n + 7) ≤ ‖1 + z‖ ^ (8 * n + 7) :=
      pow_le_pow_left₀ (by linarith) (by linarith) (8 * n + 7)
    nlinarith
  have herr : chargeErrPow n v = (((1 + w) ^ (4 * (n + 1)) - 1) - ((1 + z) ^ (8 * n + 7) - 1)) / (1 + z) ^ (8 * n + 7) := by
    unfold chargeErrPow
    rw [h3, h4, hJ]
    have hw' : (1 + y) ^ (4 * (n + 1)) * (1 + x) ^ (4 * (n + 1)) = (1 + w) ^ (4 * (n + 1)) := by
      rw [← mul_pow, hw]; ring_nf
    have hz' : (1 + z) ^ (8 * n + 7) ≠ 0 := pow_ne_zero _ hz0
    rw [mul_pow]
    field_simp
    rw [hw']
    ring
  rw [herr, norm_div, div_le_iff₀ (lt_of_lt_of_le (by norm_num) hden)]
  calc ‖((1 + w) ^ (4 * (n + 1)) - 1) - ((1 + z) ^ (8 * n + 7) - 1)‖
      ≤ ‖(1 + w) ^ (4 * (n + 1)) - 1‖ + ‖(1 + z) ^ (8 * n + 7) - 1‖ := norm_sub_le _ _
    _ ≤ 6 / 100 := by linarith
    _ ≤ 1 / 8 * (98 / 100) := by norm_num
    _ ≤ 1 / 8 * ‖(1 + z) ^ (8 * n + 7)‖ := by linarith

end

end RHTower
