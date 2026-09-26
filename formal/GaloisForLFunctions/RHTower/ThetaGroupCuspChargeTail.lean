import GaloisForLFunctions.RHTower.ThetaGroupOffLineStripZero

open Complex MeasureTheory Filter Topology
open scoped Real

namespace RHTower

noncomputable section

variable {F : ℂ → ℂ} {M : ℝ}

/-- Generic transfer: a continuous function with a norm-symmetric super-exponential far bound beats
every exponential weight. -/
theorem exists_exp_bound_of_superexp {f : ℝ → ℂ} (hf : Continuous f)
    (hsym : ∀ x, ‖f (-x)‖ = ‖f x‖) {K : ℝ} (hK : 0 ≤ K)
    (hfar : ∀ x : ℝ, 3 ≤ Real.exp (2 * x) → ‖f x‖ ≤ K * Real.exp (x / 2) *
      (3 * Real.exp (2 * x) + 2 * Real.exp (2 * x) ^ 2) * Real.exp (-π * Real.exp (2 * x)))
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖f x‖ ≤ C * Real.exp (-(B * |x|)) := by
  set x₀ : ℝ := Real.log 3 / 2 with hx₀
  have hx₀pos : 0 ≤ x₀ := by
    have : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    linarith
  set N : ℕ := ⌈B⌉₊ + 1 with hN
  have hfar' : ∀ x : ℝ, x₀ ≤ x →
      ‖f x‖ ≤ 5 * K * ((N + 2).factorial : ℝ) * Real.exp (-(B * x)) := by
    intro x hx
    have hx0 : 0 ≤ x := hx₀pos.trans hx
    set y := Real.exp (2 * x) with hy
    have hy3 : 3 ≤ y := by
      have : Real.exp (2 * x₀) = 3 := by
        rw [hx₀, show 2 * (Real.log 3 / 2) = Real.log 3 by ring, Real.exp_log (by norm_num)]
      rw [← this]; exact Real.exp_le_exp.mpr (by linarith)
    have hbound := hfar x hy3
    rw [← hy] at hbound
    have hBN : B + 1 / 2 ≤ 2 * (N : ℝ) := by
      have := Nat.le_ceil B
      rw [hN]; push_cast; linarith
    have hpow : Real.exp (B * x) * Real.exp (x / 2) ≤ y ^ N := by
      rw [← Real.exp_add, hy, ← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      nlinarith
    have hpoly : 3 * y + 2 * y ^ 2 ≤ 5 * y ^ 2 := by nlinarith
    have hfac : y ^ (N + 2) * Real.exp (-π * y) ≤ ((N + 2).factorial : ℝ) := by
      have h1 := Real.pow_div_factorial_le_exp (x := y) (by linarith) (N + 2)
      have hfpos : (0 : ℝ) < ((N + 2).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
      have h2 : y ^ (N + 2) ≤ ((N + 2).factorial : ℝ) * Real.exp y := by
        rw [div_le_iff₀ hfpos] at h1; linarith
      have h3 : Real.exp y * Real.exp (-π * y) ≤ 1 := by
        rw [← Real.exp_add]; apply Real.exp_le_one_iff.mpr; nlinarith [Real.pi_gt_three]
      calc y ^ (N + 2) * Real.exp (-π * y)
          ≤ ((N + 2).factorial : ℝ) * Real.exp y * Real.exp (-π * y) :=
            mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
        _ = ((N + 2).factorial : ℝ) * (Real.exp y * Real.exp (-π * y)) := by ring
        _ ≤ ((N + 2).factorial : ℝ) * 1 := mul_le_mul_of_nonneg_left h3 hfpos.le
        _ = _ := by ring
    have hkey : Real.exp (B * x) * ‖f x‖ ≤ 5 * K * ((N + 2).factorial : ℝ) := by
      calc Real.exp (B * x) * ‖f x‖
          ≤ Real.exp (B * x) * (K * Real.exp (x / 2) * (3 * y + 2 * y ^ 2) *
              Real.exp (-π * y)) := mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le
        _ = K * (Real.exp (B * x) * Real.exp (x / 2)) * (3 * y + 2 * y ^ 2) *
              Real.exp (-π * y) := by ring
        _ ≤ K * y ^ N * (5 * y ^ 2) * Real.exp (-π * y) := by gcongr
        _ = 5 * K * (y ^ (N + 2) * Real.exp (-π * y)) := by ring
        _ ≤ 5 * K * ((N + 2).factorial : ℝ) := mul_le_mul_of_nonneg_left hfac (by positivity)
    have hexpB : Real.exp (-(B * x)) = (Real.exp (B * x))⁻¹ := Real.exp_neg _
    rw [hexpB, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)]
    linarith [hkey]
  have hcomp : IsCompact (Set.Icc (-x₀) x₀) := isCompact_Icc
  obtain ⟨C₀, hC₀⟩ := hcomp.exists_bound_of_continuousOn hf.continuousOn
  set C₁ : ℝ := 5 * K * ((N + 2).factorial : ℝ) with hC₁
  have hC₁0 : 0 ≤ C₁ := by positivity
  refine ⟨max C₁ (max C₀ 0 * Real.exp (B * x₀)), le_max_of_le_left hC₁0, fun x => ?_⟩
  by_cases hmid : |x| ≤ x₀
  · have hxI : x ∈ Set.Icc (-x₀) x₀ := ⟨by linarith [(abs_le.mp hmid).1], (abs_le.mp hmid).2⟩
    have h0 := hC₀ x hxI
    have hexp : 1 ≤ Real.exp (B * x₀) * Real.exp (-(B * |x|)) := by
      rw [← Real.exp_add]; apply Real.one_le_exp; nlinarith
    calc ‖f x‖ ≤ max C₀ 0 := h0.trans (le_max_left _ _)
      _ ≤ max C₀ 0 * (Real.exp (B * x₀) * Real.exp (-(B * |x|))) :=
          le_mul_of_one_le_right (le_max_right _ _) hexp
      _ = max C₀ 0 * Real.exp (B * x₀) * Real.exp (-(B * |x|)) := by ring
      _ ≤ max C₁ (max C₀ 0 * Real.exp (B * x₀)) * Real.exp (-(B * |x|)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
  · have hmid := not_le.mp hmid
    rcases le_or_gt 0 x with hx | hx
    · rw [abs_of_nonneg hx] at hmid ⊢
      exact (hfar' x hmid.le).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
    · rw [abs_of_neg hx] at hmid ⊢
      rw [← hsym x]
      exact (hfar' (-x) hmid.le).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)


section Tail

variable (hF : DifferentiableOn ℂ F modUpperSet)
  (hS : ∀ x : ℝ, F (modAxisPoint (-x)) = (Real.exp x : ℂ) * F (modAxisPoint x))
  (hdec : ∀ τ : ℂ, 1 ≤ τ.im → ‖F τ - 0‖ ≤ M * Real.exp (-π * τ.im))
include hF hS hdec

omit hF hdec in
theorem modTail_zero_even (x : ℝ) : modTail F 0 (-x) = modTail F 0 x := by
  have := modTail_neg (F := F) 0 hS x
  simpa using this

omit hdec in
theorem modTailDeriv_zero_odd (x : ℝ) : modTailDeriv F 0 (-x) = -modTailDeriv F 0 x := by
  have hrefl : modTail F 0 ∘ Neg.neg = modTail F 0 := by
    funext y; exact modTail_zero_even hS y
  have hl := (hasDerivAt_modTail 0 hF (-x)).scomp x (hasDerivAt_neg x)
  rw [hrefl] at hl
  have := hl.unique (hasDerivAt_modTail 0 hF x)
  simp only [neg_smul, one_smul] at this
  linear_combination -this

omit hS hdec in
theorem continuous_modTail_zero : Continuous (modTail F 0) :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_modTail 0 hF x).continuousAt

omit hS hdec in
theorem continuous_modTailDeriv_zero : Continuous (modTailDeriv F 0) :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_modTailDeriv 0 hF x).continuousAt

theorem exists_norm_modTail_le_exp {B : ℝ} (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖modTail F 0 x‖ ≤ C * Real.exp (-(B * |x|)) := by
  have hM := cuspDecay_const_nonneg hdec
  refine exists_exp_bound_of_superexp (continuous_modTail_zero hF)
    (fun x => by rw [modTail_zero_even hS]) hM (fun x hx => ?_) hB
  set y := Real.exp (2 * x) with hy
  have hpim : (modAxisPoint x).im = y := modAxisPoint_im x
  have h0 := hdec (modAxisPoint x) (by rw [hpim]; linarith)
  rw [hpim, sub_zero] at h0
  unfold modTail
  rw [sub_zero, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), show ‖(2 : ℂ)‖ = 2 by norm_num]
  have hy0 : 0 ≤ y := (Real.exp_pos _).le
  have hE := Real.exp_pos (x / 2)
  have hE2 := Real.exp_pos (-π * y)
  calc Real.exp (x / 2) * ‖F (modAxisPoint x)‖ / 2
      ≤ Real.exp (x / 2) * (M * Real.exp (-π * y)) / 2 := by gcongr
    _ ≤ M * Real.exp (x / 2) * (3 * y + 2 * y ^ 2) * Real.exp (-π * y) := by
        have : (1 : ℝ) ≤ 3 * y + 2 * y ^ 2 := by nlinarith
        have hMe : 0 ≤ M * Real.exp (x / 2) * Real.exp (-π * y) := by positivity
        nlinarith

theorem exists_norm_modTailDeriv_le_exp {B : ℝ} (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖modTailDeriv F 0 x‖ ≤ C * Real.exp (-(B * |x|)) := by
  have hM := cuspDecay_const_nonneg hdec
  set K : ℝ := M + 2 * M * Real.exp (π / 2) with hK
  have hK0 : 0 ≤ K := by positivity
  refine exists_exp_bound_of_superexp (continuous_modTailDeriv_zero hF)
    (fun x => by rw [modTailDeriv_zero_odd hF hS, norm_neg]) hK0 (fun x hx => ?_) hB
  set y := Real.exp (2 * x) with hy
  have hpim : (modAxisPoint x).im = y := modAxisPoint_im x
  have h0 := hdec (modAxisPoint x) (by rw [hpim]; linarith)
  rw [hpim, sub_zero] at h0
  have h1 := norm_deriv_le_of_cuspDecay (c := 0) hF hdec (τ := modAxisPoint x) (by rw [hpim]; linarith)
  rw [hpim] at h1
  have hy0 : 0 ≤ y := (Real.exp_pos _).le
  have hE := Real.exp_pos (x / 2)
  have hE2 := Real.exp_pos (-π * y)
  have hinner : ‖(F (modAxisPoint x) - 0) / 2 + 2 * modAxisPoint x * deriv F (modAxisPoint x)‖ ≤
      M * Real.exp (-π * y) / 2 + 2 * y * (2 * M * Real.exp (π / 2) * Real.exp (-π * y)) := by
    refine (norm_add_le _ _).trans ?_
    rw [sub_zero, norm_div, norm_mul, norm_mul, norm_modAxisPoint, ← hy,
      show ‖(2 : ℂ)‖ = 2 by norm_num]
    gcongr
  unfold modTailDeriv
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hE,
    show ‖(2 : ℂ)‖ = 2 by norm_num]
  have hP : 0 ≤ M * Real.exp (π / 2) := by positivity
  calc Real.exp (x / 2) * ‖(F (modAxisPoint x) - 0) / 2 + 2 * modAxisPoint x *
        deriv F (modAxisPoint x)‖ / 2
      ≤ Real.exp (x / 2) * (M * Real.exp (-π * y) / 2 +
          2 * y * (2 * M * Real.exp (π / 2) * Real.exp (-π * y))) / 2 := by gcongr
    _ ≤ K * Real.exp (x / 2) * (3 * y + 2 * y ^ 2) * Real.exp (-π * y) := by
        rw [hK]
        have hy3 : (3 : ℝ) ≤ y := hx
        have hEE : 0 ≤ Real.exp (x / 2) * Real.exp (-π * y) := by positivity
        nlinarith [mul_nonneg hEE hP, mul_nonneg hEE hM, mul_nonneg (mul_nonneg hEE hP) hy0,
          mul_nonneg (mul_nonneg hEE hM) hy0]


omit hF hS hdec in
theorem integrable_exp_line_mul {f : ℝ → ℂ} (hf : Continuous f) (w : ℂ) {C : ℝ}
    (hC : ∀ x : ℝ, ‖f x‖ ≤ C * Real.exp (-((|w.im| + 1) * |x|))) :
    Integrable (fun x : ℝ => Complex.exp (-Complex.I * w * x) * f x) := by
  refine Integrable.mono' ((integrable_exp_neg_mul_abs_modSource (a := 1) one_pos).const_mul C)
    (by fun_prop) (Eventually.of_forall fun x => ?_)
  rw [norm_mul, Complex.norm_exp]
  have hre : (-Complex.I * w * (x : ℂ)).re = w.im * x := by simp [Complex.mul_re]
  rw [hre]
  have hwx : w.im * x ≤ |w.im| * |x| := by
    calc w.im * x ≤ |w.im * x| := le_abs_self _
      _ = |w.im| * |x| := abs_mul _ _
  calc Real.exp (w.im * x) * ‖f x‖
      ≤ Real.exp (|w.im| * |x|) * (C * Real.exp (-((|w.im| + 1) * |x|))) :=
        mul_le_mul (Real.exp_le_exp.mpr hwx) (hC x) (norm_nonneg _) (Real.exp_pos _).le
    _ = C * Real.exp (-1 * |x|) := by rw [mul_left_comm, ← Real.exp_add]; congr 2; ring

/-- **Two integrations by parts.**  `Ξ_F(w) = −(w² + 1/4) ∫ e^{−iwx} T(x) dx` for the tail
`T(x) = e^{x/2}F(ie^{2x})/2` of a form with vanishing cusp value. -/
theorem modXi_eq_tailTransform (w : ℂ) :
    modXi F w = -(w ^ 2 + 1 / 4) *
      ∫ x : ℝ, Complex.exp (-Complex.I * w * x) * modTail F 0 x := by
  have hB : (0 : ℝ) ≤ |w.im| + 1 := by positivity
  obtain ⟨C0, _, hC0⟩ := exists_norm_modTail_le_exp hF hS hdec hB
  obtain ⟨C1, _, hC1⟩ := exists_norm_modTailDeriv_le_exp hF hS hdec hB
  obtain ⟨Cs, _, hCs⟩ := exists_norm_modSource_le_exp (c := 0) (M := M) hF hS hdec hB
  have hT0 := continuous_modTail_zero hF
  have hT1 := continuous_modTailDeriv_zero hF
  have hS0 := continuous_modSource hF
  have hT2eq : ∀ x, modTailDeriv2 F 0 x = modSource F x + modTail F 0 x / 4 := by
    intro x; rw [modSource_eq F 0 x]; ring
  have hT2cont : Continuous (modTailDeriv2 F 0) := by
    have : modTailDeriv2 F 0 = fun x => modSource F x + modTail F 0 x / 4 := funext hT2eq
    rw [this]; fun_prop
  have hC2 : ∀ x : ℝ, ‖modTailDeriv2 F 0 x‖ ≤ (Cs + C0) * Real.exp (-((|w.im| + 1) * |x|)) := by
    intro x
    rw [hT2eq]
    have hE := Real.exp_pos (-((|w.im| + 1) * |x|))
    calc ‖modSource F x + modTail F 0 x / 4‖ ≤ ‖modSource F x‖ + ‖modTail F 0 x‖ / 4 := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_div, show ‖(4 : ℂ)‖ = 4 by norm_num]
      _ ≤ Cs * Real.exp (-((|w.im| + 1) * |x|)) + C0 * Real.exp (-((|w.im| + 1) * |x|)) := by
          have := hC0 x; have := hCs x; nlinarith
      _ = (Cs + C0) * Real.exp (-((|w.im| + 1) * |x|)) := by ring
  set e : ℝ → ℂ := fun x => Complex.exp (-Complex.I * w * x) with he
  have hde : ∀ x : ℝ, HasDerivAt e ((-Complex.I * w) * e x) x := by
    intro x
    have h := ((hasDerivAt_id (x : ℂ)).const_mul (-Complex.I * w)).cexp
    have h2 := h.comp_ofReal
    simp only [he]
    convert h2 using 1
    · funext y; simp
    · simp; ring
  have iT0 := integrable_exp_line_mul hT0 w hC0
  have iT1 := integrable_exp_line_mul hT1 w hC1
  have iT2 := integrable_exp_line_mul hT2cont w hC2
  -- first integration by parts: ∫ e T'' = −∫ e' T'
  have ibp1 : ∫ x : ℝ, e x * modTailDeriv2 F 0 x =
      -∫ x : ℝ, ((-Complex.I * w) * e x) * modTailDeriv F 0 x := by
    refine integral_mul_deriv_eq_deriv_mul_of_integrable (fun x _ => hde x)
      (fun x _ => hasDerivAt_modTailDeriv 0 hF x) iT2 ?_ iT1
    exact (iT1.const_mul (-Complex.I * w)).congr (Eventually.of_forall fun x => by
      simp only [Pi.mul_apply]; ring)
  have ibp2 : ∫ x : ℝ, e x * modTailDeriv F 0 x =
      -∫ x : ℝ, ((-Complex.I * w) * e x) * modTail F 0 x := by
    refine integral_mul_deriv_eq_deriv_mul_of_integrable (fun x _ => hde x)
      (fun x _ => hasDerivAt_modTail 0 hF x) iT1 ?_ iT0
    exact (iT0.const_mul (-Complex.I * w)).congr (Eventually.of_forall fun x => by
      simp only [Pi.mul_apply]; ring)
  have hpull : ∀ g : ℝ → ℂ, ∫ x : ℝ, ((-Complex.I * w) * e x) * g x =
      (-Complex.I * w) * ∫ x : ℝ, e x * g x := by
    intro g
    rw [← integral_const_mul]; congr 1; funext x; ring
  have hI2 : ∫ x : ℝ, e x * modTailDeriv2 F 0 x = -w ^ 2 * ∫ x : ℝ, e x * modTail F 0 x := by
    rw [ibp1, hpull, ibp2, hpull]
    have : Complex.I ^ 2 = -1 := Complex.I_sq
    linear_combination (w ^ 2 * ∫ x : ℝ, e x * modTail F 0 x) * this
  unfold modXi modXiIntegrand
  have hsplit : (fun x : ℝ => Complex.exp (-Complex.I * w * x) * modSource F x) =
      fun x => e x * modTailDeriv2 F 0 x - (1 / 4 : ℂ) * (e x * modTail F 0 x) := by
    funext x; rw [modSource_eq F 0 x]; simp only [he]; ring
  rw [hsplit, integral_sub iT2 (iT0.const_mul _), integral_const_mul, hI2]
  ring

end Tail

end

end RHTower
