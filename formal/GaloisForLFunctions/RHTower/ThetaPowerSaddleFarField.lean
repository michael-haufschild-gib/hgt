import GaloisForLFunctions.RHTower.ThetaPowerSaddleWindow

/-!
# The Farey far field of `F_a` on the saddle line

The modulus `|F_a| = |θ₂|^a |θ₄|^a |θ₃|^{1-2a}` is branch-free, so the `SL(2,ℤ)` modulus law of the
three theta constants transports it to the standard fundamental domain:
`|F_a(τ)| ≤ 36^a |cτ+d|^{-1/2} e^{(2a-1)π Im(gτ)/4}` when `g` sends `τ` near the cusp class of `1`
(both lower entries odd), and `≤ 36^a |cτ+d|^{-1/2}` otherwise.  On the saddle ray outside the
window the exponent is capped at `R₀/3` by the Farey bound `|cτ+d|² ≥ 12ρt⁴`, which depends on the
pole order only through the linear factor `mπ/4`.
-/

open Complex UpperHalfPlane ModularGroup
open scoped Real MatrixGroups

namespace RHTower

noncomputable section

open Bottcher

theorem norm_thetaPowerForm_rpow (a : ℝ) {τ : ℂ} (hτ : 0 < τ.im) :
    ‖thetaPowerForm a τ‖ =
      ‖thetaTwo τ‖ ^ a * ‖thetaFour τ‖ ^ a * ‖thetaThree τ‖ ^ (1 - 2 * a) := by
  have h2 : 0 < ‖thetaTwo τ‖ := norm_pos_iff.mpr (thetaTwo_ne_zero_of_im_pos hτ)
  have h3 : 0 < ‖thetaThree τ‖ := norm_pos_iff.mpr (thetaThree_ne_zero_of_im_pos hτ)
  have h4 : 0 < ‖thetaFour τ‖ := norm_pos_iff.mpr (thetaFour_ne_zero_of_im_pos hτ)
  rw [norm_thetaPowerForm hτ]
  unfold thetaGroupHauptmodul
  rw [norm_div, norm_mul, norm_pow, norm_pow, norm_pow]
  rw [Real.div_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity)]
  have e1 : ∀ x : ℝ, 0 < x → ∀ k : ℕ, (x ^ k) ^ (a / 4) = x ^ ((k : ℝ) * (a / 4)) := by
    intro x hx k
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
  rw [e1 _ h2, e1 _ h4, e1 _ h3]
  have e3 : ‖thetaThree τ‖ ^ (1 - 2 * a) =
      ‖thetaThree τ‖ / ‖thetaThree τ‖ ^ ((8 : ℕ) * (a / 4) : ℝ) := by
    rw [show (1 : ℝ) - 2 * a = 1 - (8 : ℕ) * (a / 4) by push_cast; ring,
      Real.rpow_sub h3, Real.rpow_one]
  rw [e3]
  have e4 : ((4 : ℕ) : ℝ) * (a / 4) = a := by push_cast; ring
  rw [e4]
  field_simp

theorem rpow_theta_modulus {a sD A B C : ℝ} (hsD : 0 < sD) (hA : 0 ≤ A) (hB : 0 < B)
    (hC : 0 ≤ C) :
    (sD * A) ^ a * (sD * C) ^ a * (sD * B) ^ (1 - 2 * a) = sD * (A ^ a * C ^ a * B ^ (1 - 2 * a)) := by
  rw [Real.mul_rpow hsD.le hA, Real.mul_rpow hsD.le hC, Real.mul_rpow hsD.le hB.le]
  have hsum : sD ^ a * sD ^ a * sD ^ (1 - 2 * a) = sD := by
    rw [← Real.rpow_add hsD, ← Real.rpow_add hsD]
    rw [show a + a + (1 - 2 * a) = 1 by ring, Real.rpow_one]
  calc sD ^ a * A ^ a * (sD ^ a * C ^ a) * (sD ^ (1 - 2 * a) * B ^ (1 - 2 * a))
      = (sD ^ a * sD ^ a * sD ^ (1 - 2 * a)) * (A ^ a * C ^ a * B ^ (1 - 2 * a)) := by ring
    _ = sD * (A ^ a * C ^ a * B ^ (1 - 2 * a)) := by rw [hsum]

theorem rpow_theta_odd_le {a A B C e : ℝ} (ha : 1 / 2 < a) (hA0 : 0 ≤ A) (hA : A ≤ 2)
    (hC0 : 0 ≤ C) (hC : C ≤ 2) (he : 0 < e) (hB : e ≤ B) :
    A ^ a * C ^ a * B ^ (1 - 2 * a) ≤ 36 ^ a * e ^ (1 - 2 * a) := by
  have ha0 : 0 ≤ a := by linarith
  have hAa : A ^ a ≤ 2 ^ a := Real.rpow_le_rpow hA0 hA ha0
  have hCa : C ^ a ≤ 2 ^ a := Real.rpow_le_rpow hC0 hC ha0
  have hBm : B ^ (1 - 2 * a) ≤ e ^ (1 - 2 * a) :=
    Real.rpow_le_rpow_of_nonpos he hB (by linarith)
  have h22 : (2 : ℝ) ^ a * 2 ^ a = 4 ^ a := by
    rw [← Real.mul_rpow (by norm_num) (by norm_num)]; norm_num
  have h41 : (4 : ℝ) ^ a ≤ 36 ^ a := Real.rpow_le_rpow (by norm_num) (by norm_num) ha0
  have h1 : A ^ a * C ^ a ≤ 2 ^ a * 2 ^ a :=
    mul_le_mul hAa hCa (Real.rpow_nonneg hC0 _) (Real.rpow_nonneg (by norm_num) _)
  have hE : 0 ≤ e ^ (1 - 2 * a) := Real.rpow_nonneg he.le _
  calc A ^ a * C ^ a * B ^ (1 - 2 * a) ≤ (2 ^ a * 2 ^ a) * e ^ (1 - 2 * a) :=
        mul_le_mul h1 hBm (Real.rpow_nonneg (le_trans he.le hB) _) (by positivity)
    _ = 4 ^ a * e ^ (1 - 2 * a) := by rw [h22]
    _ ≤ 36 ^ a * e ^ (1 - 2 * a) := mul_le_mul_of_nonneg_right h41 hE

theorem rpow_theta_even_le {a A B C : ℝ} (ha : 1 / 2 < a) (hA0 : 0 ≤ A) (hA : A ≤ 3)
    (hC0 : 0 ≤ C) (hC : C ≤ 3) (hB : 1 / 2 ≤ B) :
    A ^ a * C ^ a * B ^ (1 - 2 * a) ≤ 36 ^ a := by
  have ha0 : 0 ≤ a := by linarith
  have hAa : A ^ a ≤ 3 ^ a := Real.rpow_le_rpow hA0 hA ha0
  have hCa : C ^ a ≤ 3 ^ a := Real.rpow_le_rpow hC0 hC ha0
  have hBm : B ^ (1 - 2 * a) ≤ (1 / 2 : ℝ) ^ (1 - 2 * a) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hB (by linarith)
  have h4 : (4 : ℝ) ^ a = 2 ^ (2 * a) := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
  have hhalf : (1 / 2 : ℝ) ^ (1 - 2 * a) ≤ 4 ^ a := by
    rw [h4, one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h33 : (3 : ℝ) ^ a * 3 ^ a = 9 ^ a := by
    rw [← Real.mul_rpow (by norm_num) (by norm_num)]; norm_num
  have h36 : (36 : ℝ) ^ a = 9 ^ a * 4 ^ a := by
    rw [← Real.mul_rpow (by norm_num) (by norm_num)]; norm_num
  have h1 : A ^ a * C ^ a ≤ 3 ^ a * 3 ^ a :=
    mul_le_mul hAa hCa (Real.rpow_nonneg hC0 _) (Real.rpow_nonneg (by norm_num) _)
  calc A ^ a * C ^ a * B ^ (1 - 2 * a) ≤ (3 ^ a * 3 ^ a) * 4 ^ a :=
        mul_le_mul h1 (hBm.trans hhalf) (Real.rpow_nonneg (by linarith) _) (by positivity)
    _ = 36 ^ a := by rw [h33, h36]

/-- **Farey bound for `F_a`, `a > 1/2`.** -/
theorem norm_thetaPowerForm_farey {a : ℝ} (ha : 1 / 2 < a) (τ : ℍ) :
    ∃ g : SL(2, ℤ), (4 : ℝ) / 5 ≤ (g • τ).im ∧
      ‖thetaPowerForm a τ‖ ≤ 36 ^ a * ‖slDen g τ‖ ^ (-(1 / 2 : ℝ)) *
        (if Odd (g 1 0) ∧ Odd (g 1 1) then
          Real.exp ((2 * a - 1) * Real.pi / 4 * (g • τ).im) else 1) := by
  have ha0 : 0 ≤ a := by linarith
  have hneg : 1 - 2 * a ≤ 0 := by linarith
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
  have hsD : 0 < D ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hDpos _
  have hB0 : 0 < B := by
    have : ‖thetaThree (τ : ℂ)‖ = D ^ (1 / 2 : ℝ) * B := e3
    have h' : 0 < ‖thetaThree (τ : ℂ)‖ := norm_pos_iff.mpr hθ3ne
    rw [this] at h'
    exact pos_of_mul_pos_right h' hsD.le
  have hnorm : ‖thetaPowerForm a (τ : ℂ)‖ = D ^ (1 / 2 : ℝ) * (A ^ a * C ^ a * B ^ (1 - 2 * a)) := by
    rw [norm_thetaPowerForm_rpow a τ.im_pos, e2, e3, e4]
    exact rpow_theta_modulus hsD hA0 hB0 hC0
  rw [hnorm, hDhalf]
  have hSpos : 0 < ‖slDen g (τ : ℂ)‖ ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hGpos _
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
      have h := (norm_thetaTwo_bounds him).1
      have hB3 : thetaChar a3 (z' : ℂ) = thetaTwo (z' : ℂ) := by rw [ha3eq, thetaChar_two]
      show Real.exp (-Real.pi * (z' : ℂ).im / 4) ≤ ‖thetaChar a3 (z' : ℂ)‖
      rw [hB3]; exact h
    have hEm : Real.exp (-Real.pi * (z' : ℂ).im / 4) ^ (1 - 2 * a) =
        Real.exp ((2 * a - 1) * Real.pi / 4 * (g • τ).im) := by
      rw [← Real.exp_mul]; congr 1; rw [hz']; simp only [UpperHalfPlane.coe_im]; ring
    have hkey := rpow_theta_odd_le ha hA0 hA2 hC0 hC2 (Real.exp_pos _) hBlo
    rw [hEm] at hkey
    calc ‖slDen g (τ : ℂ)‖ ^ (-(1 / 2 : ℝ)) * (A ^ a * C ^ a * B ^ (1 - 2 * a))
        ≤ ‖slDen g (τ : ℂ)‖ ^ (-(1 / 2 : ℝ)) *
            (36 ^ a * Real.exp ((2 * a - 1) * Real.pi / 4 * (g • τ).im)) :=
          mul_le_mul_of_nonneg_left hkey hSpos.le
      _ = _ := by ring
  · rw [if_neg hpar, mul_one]
    have ha3ne : a3 ≠ ![0, 1] := fun h => hpar ((charAct_three_inv_eq_two_iff g).mp h)
    have hBlo : 1 / 2 ≤ B := half_le_norm_thetaChar ha3 ha3ne him
    have hkey := rpow_theta_even_le ha hA0 hA3 hC0 hC3 hBlo
    calc ‖slDen g (τ : ℂ)‖ ^ (-(1 / 2 : ℝ)) * (A ^ a * C ^ a * B ^ (1 - 2 * a))
        ≤ ‖slDen g (τ : ℂ)‖ ^ (-(1 / 2 : ℝ)) * 36 ^ a :=
          mul_le_mul_of_nonneg_left hkey hSpos.le
      _ = _ := by ring

section FarFieldA

variable {a t : ℝ}

/-- **Farey bound for `F_a` on the saddle ray.** -/
theorem norm_thetaPower_line_farey (ha : 1 / 2 < a) (ht : 0 < t) (ht4 : t ^ 4 ≤ 1 / 6) {s : ℝ}
    (hs : 2 * t ^ 2 ≤ |s|) (hin : chKap t ≤ Real.exp (2 * s)) :
    ‖thetaPowerForm a ((Real.exp (2 * s) : ℂ) * chOmega t)‖ ≤
      36 ^ a * (chKap t)⁻¹ * Real.exp (chR0m (chMa a) t / 3) := by
  have ht4' : t ^ 4 ≤ 1 := by linarith
  have ht2 : t ^ 2 ≤ 1 / 2 := by nlinarith [pow_pos ht 2]
  have hκ := chKap_pos ht (by linarith)
  have hκ1 := chKap_le_one ht2
  have him : 0 < ((Real.exp (2 * s) : ℂ) * chOmega t).im := by
    rw [im_line_point]; have := chB_nonneg (t := t); positivity
  set τ : ℍ := ⟨(Real.exp (2 * s) : ℂ) * chOmega t, him⟩ with hτ
  have hτc : (τ : ℂ) = (Real.exp (2 * s) : ℂ) * chOmega t := rfl
  have hτim : τ.im = Real.exp (2 * s) * chKap t := by
    show ((τ : ℂ)).im = _; rw [hτc, im_line_point]; rfl
  obtain ⟨g, -, hg⟩ := norm_thetaPowerForm_farey ha τ
  rw [hτc] at hg
  refine le_trans hg ?_
  have hden : ‖slDen g τ‖ ^ (-(1 / 2 : ℝ)) ≤ (chKap t)⁻¹ := by
    by_cases hc : g 1 0 = 0
    · have hdet := Matrix.SpecialLinearGroup.det_coe g
      rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at hdet
      have hd : g 1 1 = 1 ∨ g 1 1 = -1 :=
        Int.eq_one_or_neg_one_of_mul_eq_one (by rw [mul_comm]; exact hdet)
      have hn : ‖slDen g τ‖ = 1 := by
        unfold slDen; rw [hc]; rcases hd with h | h <;> rw [h] <;> simp
      rw [hn, Real.one_rpow]
      rw [le_inv_comm₀ one_pos hκ, inv_one]; exact hκ1
    · have hlow : chKap t * chKap t ≤ ‖slDen g τ‖ := by
        have h1 : |(slDen g τ).im| ≤ ‖slDen g τ‖ := Complex.abs_im_le_norm _
        have h2 : (slDen g τ).im = (g 1 0 : ℝ) * τ.im := by
          unfold slDen; simp
        have h3 : (1 : ℝ) ≤ |(g 1 0 : ℝ)| := by
          rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hc
        rw [h2, abs_mul, abs_of_pos τ.im_pos, hτim] at h1
        have h4 : chKap t * chKap t ≤ Real.exp (2 * s) * chKap t :=
          mul_le_mul_of_nonneg_right hin hκ.le
        nlinarith [Real.exp_pos (2 * s)]
      have hpos : 0 < chKap t * chKap t := by positivity
      calc ‖slDen g τ‖ ^ (-(1 / 2 : ℝ)) ≤ (chKap t * chKap t) ^ (-(1 / 2 : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos hpos hlow (by norm_num)
        _ = (chKap t)⁻¹ := by
            rw [Real.rpow_neg hpos.le, ← Real.sqrt_eq_rpow, Real.sqrt_mul_self hκ.le]
  have hexp : (if Odd (g 1 0) ∧ Odd (g 1 1) then
      Real.exp ((2 * a - 1) * Real.pi / 4 * (g • τ).im) else 1)
      ≤ Real.exp (chR0m (chMa a) t / 3) := by
    have hR : 0 ≤ chR0m (chMa a) t := by
      unfold chR0m chMa; have := chB_nonneg (t := t)
      have : 0 ≤ 2 * a - 1 := by linarith
      positivity
    split_ifs with hodd
    · apply Real.exp_le_exp.mpr
      rw [sl_im_smul_eq, hτim]
      have hN := normSq_den_line_ge ht (by linarith) hodd.1 hodd.2 hs
      have hNeq := normSq_den_line ht4' (g 1 0) (g 1 1) s
      have hsl : slDen g τ = ((g 1 0 : ℤ) : ℂ) * ((Real.exp (2 * s) : ℂ) * chOmega t) +
          ((g 1 1 : ℤ) : ℂ) := by unfold slDen; rw [hτc]
      rw [hsl, hNeq]
      have hNpos : 0 < 12 * Real.exp (2 * s) * t ^ 4 := by positivity
      have hq : Real.exp (2 * s) * chKap t /
          ((g 1 0 : ℝ) ^ 2 * Real.exp (2 * s) ^ 2 +
            2 * (g 1 0 : ℝ) * (g 1 1 : ℝ) * Real.exp (2 * s) * (1 - 2 * t ^ 4) + (g 1 1 : ℝ) ^ 2)
          ≤ Real.exp (2 * s) * chKap t / (12 * Real.exp (2 * s) * t ^ 4) :=
        div_le_div_of_nonneg_left (by positivity) hNpos hN
      have hval : Real.exp (2 * s) * chKap t / (12 * Real.exp (2 * s) * t ^ 4) =
          chB t / (6 * t ^ 2) := by
        unfold chKap; field_simp; ring
      rw [hval] at hq
      have h7 : (2 * a - 1) * Real.pi / 4 * (chB t / (6 * t ^ 2)) = chR0m (chMa a) t / 3 := by
        unfold chR0m chMa; field_simp; ring
      have hm0 : 0 ≤ (2 * a - 1) * Real.pi / 4 := by
        have : 0 ≤ 2 * a - 1 := by linarith
        positivity
      calc (2 * a - 1) * Real.pi / 4 * _ ≤ (2 * a - 1) * Real.pi / 4 * (chB t / (6 * t ^ 2)) :=
            mul_le_mul_of_nonneg_left hq hm0
        _ = chR0m (chMa a) t / 3 := h7
    · exact Real.one_le_exp (by linarith)
  have h36 : (0 : ℝ) ≤ 36 ^ a := by positivity
  calc 36 ^ a * ‖slDen g τ‖ ^ (-(1 / 2 : ℝ)) *
        (if Odd (g 1 0) ∧ Odd (g 1 1) then
          Real.exp ((2 * a - 1) * Real.pi / 4 * (g • τ).im) else 1)
      ≤ 36 ^ a * (chKap t)⁻¹ * Real.exp (chR0m (chMa a) t / 3) := by
        gcongr

/-- The far-field constant of `F_a`. -/
def chBfarA (a t M : ℝ) : ℝ :=
  max (36 ^ a * (chKap t)⁻¹ ^ 3 * Real.exp (chR0m (chMa a) t / 3) / 2)
    (M / 2 * (1 / (π * a / 4 * chKap t)))

theorem chBfarA_nonneg (ht : 0 < t) (ht4 : t ^ 4 ≤ 3 / 4) (M : ℝ) : 0 ≤ chBfarA a t M := by
  refine le_trans ?_ (le_max_left _ _)
  have hκ := chKap_pos ht ht4
  have hκ' := inv_nonneg.mpr hκ.le
  have h36 : (0 : ℝ) ≤ 36 ^ a := by positivity
  exact div_nonneg (mul_nonneg (mul_nonneg h36 (pow_nonneg hκ' 3)) (Real.exp_pos _).le)
    (by norm_num)

/-- **Far field of the tail of `F_a` on the saddle line.** -/
theorem norm_chargeTailA_far (ha : 1 / 2 < a) (ht : 0 < t) (ht4 : t ^ 4 ≤ 1 / 6) {M : ℝ}
    (hM : ∀ τ : ℂ, 1 ≤ τ.im → ‖thetaPowerForm a τ‖ ≤ M * Real.exp (-(π * a / 4) * τ.im))
    {s : ℝ} (hs : 2 * t ^ 2 ≤ |s|) :
    ‖chargeTailC (thetaPowerForm a) ((s : ℂ) - (chBeta t : ℂ) * Complex.I)‖ ≤
      chBfarA a t M * Real.exp (-|s|) := by
  have hr : 0 < π * a / 4 := by have := Real.pi_pos; nlinarith
  have ht2 : t ^ 2 ≤ 1 / 2 := by nlinarith [pow_pos ht 2]
  have ht21 : t ^ 2 ≤ 1 := by linarith
  have hκ := chKap_pos ht (by linarith)
  have hκ1 := chKap_le_one ht2
  have hβ0 := chBeta_nonneg ht2
  have hβ := chBeta_lt ht ht21
  have hcos : Real.cos (2 * chBeta t) = chKap t := cos_two_chBeta ht21
  set z : ℂ := (s : ℂ) - (chBeta t : ℂ) * Complex.I with hz
  have hzre : z.re = s := by simp [hz]
  have hzim : |z.im| ≤ chBeta t := by simp [hz, abs_of_nonneg hβ0]
  obtain ⟨hA, hB⟩ := norm_chargeTailC_le_cusp_rate hr (thetaPowerForm_inversion a) hM hβ hzim
  rw [hzre, hcos] at hA hB
  have hM0 : 0 ≤ M := by
    have h := hM Complex.I (by simp)
    have h1 : (0:ℝ) ≤ M * Real.exp (-(π * a / 4) * Complex.I.im) := le_trans (norm_nonneg _) h
    exact nonneg_of_mul_nonneg_left h1 (Real.exp_pos _)
  by_cases h1 : 1 ≤ Real.exp (2 * s) * chKap t
  · have hs0 : 0 ≤ s := by
      by_contra hneg; push Not at hneg
      have : Real.exp (2 * s) < 1 := by
        rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
      nlinarith
    have hkey := exp_half_mul_exp_neg_rate_le hr hκ hκ1 h1
    rw [abs_of_nonneg hs0]
    calc ‖chargeTailC (thetaPowerForm a) z‖
        ≤ M / 2 * (Real.exp (s / 2) * Real.exp (-(π * a / 4) * (Real.exp (2 * s) * chKap t))) := by
          rw [← mul_assoc]; exact hA h1
      _ ≤ M / 2 * (1 / (π * a / 4 * chKap t) * Real.exp (-s)) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ ≤ chBfarA a t M * Real.exp (-s) := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
  by_cases h2 : 1 ≤ Real.exp (-2 * s) * chKap t
  · have hs0 : s ≤ 0 := by
      by_contra hneg; push Not at hneg
      have : Real.exp (-2 * s) < 1 := by
        rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
      nlinarith
    have hkey := exp_half_mul_exp_neg_rate_le (x := -s) hr hκ hκ1
      (by rw [show 2 * -s = -2 * s by ring]; exact h2)
    rw [abs_of_nonpos hs0]
    calc ‖chargeTailC (thetaPowerForm a) z‖
        ≤ M / 2 * (Real.exp (-s / 2) *
            Real.exp (-(π * a / 4) * (Real.exp (-2 * s) * chKap t))) := by
          rw [← mul_assoc]; exact hB h2
      _ = M / 2 * (Real.exp (-s / 2) *
            Real.exp (-(π * a / 4) * (Real.exp (2 * -s) * chKap t))) := by ring_nf
      _ ≤ M / 2 * (1 / (π * a / 4 * chKap t) * Real.exp (- -s)) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ ≤ chBfarA a t M * Real.exp (- -s) := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
  · push Not at h1 h2
    have hin : chKap t ≤ Real.exp (2 * s) := by
      have h3 : Real.exp (-2 * s) * Real.exp (2 * s) = 1 := by rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos (2 * s), Real.exp_pos (-2 * s)]
    have hF := norm_thetaPower_line_farey ha ht ht4 hs hin
    have habs : Real.exp (2 * |s|) * chKap t < 1 := by
      rcases abs_cases s with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
      · exact h1
      · rw [show 2 * -s = -2 * s by ring]; exact h2
    have he1 : Real.exp (s / 2) ≤ (chKap t)⁻¹ := by
      rw [le_inv_comm₀ (Real.exp_pos _) hκ]
      have : Real.exp (s / 2) ≤ Real.exp (2 * |s|) :=
        Real.exp_le_exp.mpr (by have := le_abs_self s; have := abs_nonneg s; linarith)
      rw [inv_eq_one_div, le_div_iff₀ (Real.exp_pos _)]
      nlinarith
    have he2 : 1 ≤ (chKap t)⁻¹ * Real.exp (-|s|) := by
      have : Real.exp |s| ≤ Real.exp (2 * |s|) :=
        Real.exp_le_exp.mpr (by have := abs_nonneg s; linarith)
      have h4 : Real.exp |s| * Real.exp (-|s|) = 1 := by rw [← Real.exp_add]; simp
      rw [← div_eq_inv_mul, le_div_iff₀ hκ]
      nlinarith [Real.exp_pos (-|s|), Real.exp_pos |s|]
    have hval : ‖chargeTailC (thetaPowerForm a) z‖ =
        Real.exp (s / 2) * ‖thetaPowerForm a ((Real.exp (2 * s) : ℂ) * chOmega t)‖ / 2 := by
      unfold chargeTailC
      rw [hz, I_mul_cexp_line ht21, norm_div, norm_mul, norm_cexp_half, Complex.norm_ofNat]
      simp
    rw [hval]
    have hFnn := norm_nonneg (thetaPowerForm a ((Real.exp (2 * s) : ℂ) * chOmega t))
    have h36 : (0 : ℝ) ≤ 36 ^ a := by positivity
    calc Real.exp (s / 2) * ‖thetaPowerForm a ((Real.exp (2 * s) : ℂ) * chOmega t)‖ / 2
        ≤ (chKap t)⁻¹ * (36 ^ a * (chKap t)⁻¹ * Real.exp (chR0m (chMa a) t / 3)) / 2 := by
          gcongr
      _ ≤ (chKap t)⁻¹ * (36 ^ a * (chKap t)⁻¹ * Real.exp (chR0m (chMa a) t / 3)) / 2 *
            ((chKap t)⁻¹ * Real.exp (-|s|)) :=
          le_mul_of_one_le_right (by positivity) he2
      _ = 36 ^ a * (chKap t)⁻¹ ^ 3 * Real.exp (chR0m (chMa a) t / 3) / 2 * Real.exp (-|s|) := by
          ring
      _ ≤ chBfarA a t M * Real.exp (-|s|) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le

end FarFieldA

end

end RHTower
