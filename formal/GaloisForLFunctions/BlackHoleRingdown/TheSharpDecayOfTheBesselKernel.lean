import GaloisForLFunctions.RHTower.BesselKImaginaryOrderUniformBound

/-!
# Sharp decay of the Bessel kernel in the order

Moving the Schläfli line to `Im t = θ`, `0 ≤ θ < π/2`, makes the modulus of the integrand at order
`ν = η + iξ` equal to `exp(-x cos θ cosh t + ηt - ξθ)`. At `θ = π/2 - 1/(1+|ξ|)` this gives

`‖K_x(ν)‖ ≤ C ((1+|ξ|)/x)^B exp(-x/(π(1+|ξ|))) exp(-π|ξ|/2)`,

uniformly for `|η| ≤ R`. The factor `exp(-π|ξ|/2)` is the true size. The price of the shift is that the
decay in `x` only starts at `x ≈ 1+|ξ|`, which costs a power of `1+|ξ|` when one sums over Fourier modes.
-/

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower

theorem integrable_exp_neg_abs : Integrable fun t : ℝ => Real.exp (-|t|) := by
  have h1 : IntegrableOn (fun t : ℝ => Real.exp (-|t|)) (Iic 0) := by
    refine (integrableOn_exp_Iic 0).congr_fun (fun t ht => ?_) measurableSet_Iic
    rw [abs_of_nonpos ht, neg_neg]
  have h2 : IntegrableOn (fun t : ℝ => Real.exp (-|t|)) (Ioi 0) := by
    refine (integrableOn_exp_neg_Ioi 0).congr_fun (fun t ht => ?_) measurableSet_Ioi
    simp only
    rw [abs_of_pos ht]
  have h := h1.union h2
  rwa [Iic_union_Ioi, integrableOn_univ] at h

theorem integral_exp_neg_abs : ∫ t : ℝ, Real.exp (-|t|) = 2 := by
  have hint := integrable_exp_neg_abs
  have hsplit : (∫ t : ℝ, Real.exp (-|t|)) =
      (∫ t in Iic (0 : ℝ), Real.exp (-|t|)) + ∫ t in Ioi (0 : ℝ), Real.exp (-|t|) := by
    rw [← setIntegral_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hint.integrableOn
      hint.integrableOn, Set.Iic_union_Ioi]
    exact setIntegral_univ.symm
  have h1 : ∫ t in Iic (0 : ℝ), Real.exp (-|t|) = 1 := by
    have h : ∫ t in Iic (0 : ℝ), Real.exp (-|t|) = ∫ t in Iic (0 : ℝ), Real.exp t :=
      setIntegral_congr_fun measurableSet_Iic fun t ht => by
        rw [abs_of_nonpos ht, neg_neg]
    rw [h, integral_exp_Iic, Real.exp_zero]
  have h2 : ∫ t in Ioi (0 : ℝ), Real.exp (-|t|) = 1 := by
    have h : ∫ t in Ioi (0 : ℝ), Real.exp (-|t|) = ∫ t in Ioi (0 : ℝ), Real.exp (-t) :=
      setIntegral_congr_fun measurableSet_Ioi fun t ht => by
        rw [abs_of_pos ht]
    rw [h, integral_exp_neg_Ioi, neg_zero, Real.exp_zero]
  rw [hsplit, h1, h2]
  norm_num

/-- The Schläfli kernel on a shifted line, against the exponential envelope. -/
theorem exp_neg_mul_cosh_le {y : ℝ} (hy : 0 < y) {η R : ℝ} (hη : |η| ≤ R) {B : ℕ}
    (hB : R + 1 ≤ B) (t : ℝ) :
    Real.exp (-y * Real.cosh t + η * t) ≤
      Real.exp (-(y / 2)) * ((B.factorial : ℝ) * (4 / y) ^ B) * Real.exp (-|t|) := by
  set s := |t| with hs
  have hs0 : 0 ≤ s := abs_nonneg t
  set z := y / 4 * Real.exp s with hz
  have hzpos : 0 < z := by positivity
  have hcosh : y / 2 + z ≤ y * Real.cosh t := by
    have h1 : 1 ≤ Real.cosh t := Real.one_le_cosh t
    have h2 : Real.exp s / 2 ≤ Real.cosh t := by
      rw [← Real.cosh_abs, ← hs, Real.cosh_eq]
      linarith [Real.exp_pos (-s)]
    rw [hz]
    nlinarith
  have hηt : η * t ≤ R * s := by
    refine (le_abs_self _).trans ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hη hs0
  set W := (4 / y) ^ B * Real.exp (-((B : ℝ) * s)) with hW
  have hWpos : 0 < W := by positivity
  have hzW : z ^ B * W = 1 := by
    have h1 : (y / 4) ^ B * (4 / y) ^ B = 1 := by
      rw [← mul_pow]
      have : y / 4 * (4 / y) = 1 := by field_simp
      rw [this, one_pow]
    have h2 : Real.exp s ^ B * Real.exp (-((B : ℝ) * s)) = 1 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
    rw [hz, mul_pow, hW]
    calc (y / 4) ^ B * Real.exp s ^ B * ((4 / y) ^ B * Real.exp (-((B : ℝ) * s)))
        = ((y / 4) ^ B * (4 / y) ^ B) * (Real.exp s ^ B * Real.exp (-((B : ℝ) * s))) := by ring
      _ = 1 := by rw [h1, h2, one_mul]
  have hfac : Real.exp (-z) ≤ (B.factorial : ℝ) * W := by
    have h := Real.pow_div_factorial_le_exp z hzpos.le B
    have hB0 : (0 : ℝ) < B.factorial := by exact_mod_cast B.factorial_pos
    rw [div_le_iff₀ hB0] at h
    have h3 : Real.exp (-z) * z ^ B ≤ (B.factorial : ℝ) := by
      calc Real.exp (-z) * z ^ B ≤ Real.exp (-z) * (Real.exp z * (B.factorial : ℝ)) :=
            mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
        _ = (B.factorial : ℝ) := by
            rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
    calc Real.exp (-z) = Real.exp (-z) * (z ^ B * W) := by rw [hzW, mul_one]
      _ = (Real.exp (-z) * z ^ B) * W := by ring
      _ ≤ (B.factorial : ℝ) * W := mul_le_mul_of_nonneg_right h3 hWpos.le
  have hexp : Real.exp (R * s) * Real.exp (-((B : ℝ) * s)) ≤ Real.exp (-s) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    nlinarith
  have hprefactor : 0 ≤ Real.exp (-(y / 2)) * ((B.factorial : ℝ) * (4 / y) ^ B) := by positivity
  calc Real.exp (-y * Real.cosh t + η * t)
      ≤ Real.exp (-(y / 2) + -z + R * s) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (-(y / 2)) * Real.exp (-z) * Real.exp (R * s) := by
        rw [Real.exp_add, Real.exp_add]
    _ ≤ Real.exp (-(y / 2)) * ((B.factorial : ℝ) * W) * Real.exp (R * s) := by
        gcongr
    _ = Real.exp (-(y / 2)) * ((B.factorial : ℝ) * (4 / y) ^ B) *
          (Real.exp (R * s) * Real.exp (-((B : ℝ) * s))) := by
        rw [hW]
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hexp hprefactor

/-- The Bessel kernel on the shifted line, at nonnegative imaginary part of the order. -/
theorem norm_modifiedBesselKOrder_le_shifted {x : ℝ} (hx : 0 < x) (ν : ℂ) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ : θ < Real.pi / 2) {R : ℝ} (hν : |ν.re| ≤ R) {B : ℕ} (hB : R + 1 ≤ B) :
    ‖modifiedBesselKOrder x ν‖ ≤
      Real.exp (-(ν.im * θ)) * (Real.exp (-(x * Real.cos θ / 2)) *
        ((B.factorial : ℝ) * (4 / (x * Real.cos θ)) ^ B)) := by
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ⟩
  have hy : 0 < x * Real.cos θ := mul_pos hx hcos
  set y := x * Real.cos θ with hydef
  have h2 := integral_besselOrderExpKernel_eq_two_mul hx ν
  rw [integral_besselOrderExpKernel_eq_shifted hx ν hθ0 hθ] at h2
  set P := Real.exp (-(y / 2)) * ((B.factorial : ℝ) * (4 / y) ^ B) with hP
  have hP0 : 0 ≤ P := by positivity
  have hbound : ∀ t : ℝ, ‖besselOrderEntireKernel x ν ((t : ℂ) + (θ : ℂ) * I)‖ ≤
      Real.exp (-(ν.im * θ)) * (P * Real.exp (-|t|)) := by
    intro t
    rw [norm_besselOrderEntireKernel]
    have hsplit : -x * (Real.cosh t * Real.cos θ) + (ν.re * t - ν.im * θ) =
        -(ν.im * θ) + (-y * Real.cosh t + ν.re * t) := by
      rw [hydef]
      ring
    rw [hsplit, Real.exp_add]
    exact mul_le_mul_of_nonneg_left (exp_neg_mul_cosh_le hy hν hB t) (Real.exp_pos _).le
  have hnorm : ‖∫ t : ℝ, besselOrderEntireKernel x ν ((t : ℂ) + (θ : ℂ) * I)‖ ≤
      Real.exp (-(ν.im * θ)) * (P * 2) := by
    have hG : Integrable fun t : ℝ => Real.exp (-(ν.im * θ)) * (P * Real.exp (-|t|)) :=
      (integrable_exp_neg_abs.const_mul P).const_mul _
    refine (norm_integral_le_of_norm_le hG (Eventually.of_forall hbound)).trans (le_of_eq ?_)
    rw [integral_const_mul, integral_const_mul, integral_exp_neg_abs]
  rw [h2, norm_mul, Complex.norm_ofNat] at hnorm
  have hE := Real.exp_pos (-(ν.im * θ))
  nlinarith [norm_nonneg (modifiedBesselKOrder x ν)]

/-- The sharp bound at nonnegative imaginary part of the order. -/
theorem norm_modifiedBesselKOrder_sharp_of_nonneg {x : ℝ} (hx : 0 < x) {ν : ℂ} (hν0 : 0 ≤ ν.im)
    {R : ℝ} (hν : |ν.re| ≤ R) {B : ℕ} (hB : R + 1 ≤ B) :
    ‖modifiedBesselKOrder x ν‖ ≤
      Real.exp 1 * (B.factorial : ℝ) * (2 * Real.pi) ^ B * ((1 + ν.im) / x) ^ B *
        Real.exp (-(x / (Real.pi * (1 + ν.im)))) * Real.exp (-(Real.pi * ν.im / 2)) := by
  set ξ := ν.im with hξ
  have hpi := Real.pi_gt_three
  have hpi0 := Real.pi_pos
  have h1ξ : 0 < 1 + ξ := by linarith
  set δ := 1 / (1 + ξ) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by
    rw [hδ, div_le_one h1ξ]
    linarith
  have hθ0 : 0 ≤ Real.pi / 2 - δ := by linarith
  have hθ : Real.pi / 2 - δ < Real.pi / 2 := by linarith
  have hmain := norm_modifiedBesselKOrder_le_shifted hx ν hθ0 hθ hν hB
  rw [Real.cos_pi_div_two_sub] at hmain
  have hsin : 2 / Real.pi * δ ≤ Real.sin δ := Real.mul_le_sin hδ0.le (by linarith)
  have hsin0 : 0 < Real.sin δ := lt_of_lt_of_le (by positivity) hsin
  have hy : 2 * x / (Real.pi * (1 + ξ)) ≤ x * Real.sin δ := by
    have h : 2 * x / (Real.pi * (1 + ξ)) = x * (2 / Real.pi * δ) := by
      rw [hδ]
      field_simp
    rw [h]
    exact mul_le_mul_of_nonneg_left hsin hx.le
  have hypos : 0 < 2 * x / (Real.pi * (1 + ξ)) := by positivity
  have h4 : 4 / (x * Real.sin δ) ≤ 2 * Real.pi * ((1 + ξ) / x) := by
    have h : 2 * Real.pi * ((1 + ξ) / x) = 4 / (2 * x / (Real.pi * (1 + ξ))) := by
      field_simp
      ring
    rw [h]
    exact div_le_div_of_nonneg_left (by norm_num) hypos hy
  have hpow : (4 / (x * Real.sin δ)) ^ B ≤ (2 * Real.pi) ^ B * ((1 + ξ) / x) ^ B := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h4 B
  have hexp1 : Real.exp (-(x * Real.sin δ / 2)) ≤ Real.exp (-(x / (Real.pi * (1 + ξ)))) := by
    refine Real.exp_le_exp.mpr ?_
    have h : x / (Real.pi * (1 + ξ)) = (2 * x / (Real.pi * (1 + ξ))) / 2 := by ring
    rw [h]
    linarith
  have hexp2 : Real.exp (-(ξ * (Real.pi / 2 - δ))) ≤
      Real.exp 1 * Real.exp (-(Real.pi * ξ / 2)) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hξδ : ξ * δ ≤ 1 := by
      rw [hδ, mul_one_div, div_le_one h1ξ]
      linarith
    linarith
  refine hmain.trans ?_
  have hA := mul_le_mul hexp1 (mul_le_mul_of_nonneg_left hpow (by positivity :
    (0 : ℝ) ≤ (B.factorial : ℝ))) (by positivity) (Real.exp_pos _).le
  calc Real.exp (-(ξ * (Real.pi / 2 - δ))) * (Real.exp (-(x * Real.sin δ / 2)) *
        ((B.factorial : ℝ) * (4 / (x * Real.sin δ)) ^ B))
      ≤ (Real.exp 1 * Real.exp (-(Real.pi * ξ / 2))) *
          (Real.exp (-(x / (Real.pi * (1 + ξ)))) *
            ((B.factorial : ℝ) * ((2 * Real.pi) ^ B * ((1 + ξ) / x) ^ B))) :=
        mul_le_mul hexp2 hA (by positivity) (by positivity)
    _ = _ := by ring

/-- **Sharp decay in the order.**  For `|Re ν| ≤ R`, `x > 0`, with `ξ = |Im ν|`,
`‖K_x(ν)‖ ≤ C ((1+ξ)/x)^B exp(-x/(π(1+ξ))) exp(-πξ/2)`. -/
theorem exists_norm_modifiedBesselKOrder_sharp {R : ℝ} (hR : 0 ≤ R) :
    ∃ (C : ℝ) (B : ℕ), 0 ≤ C ∧ ∀ (x : ℝ) (ν : ℂ), 0 < x → |ν.re| ≤ R →
      ‖modifiedBesselKOrder x ν‖ ≤
        C * ((1 + |ν.im|) / x) ^ B * Real.exp (-(x / (Real.pi * (1 + |ν.im|)))) *
          Real.exp (-(Real.pi * |ν.im| / 2)) := by
  set B := ⌈R⌉₊ + 1 with hBdef
  have hB : R + 1 ≤ B := by
    rw [hBdef]
    push_cast
    linarith [Nat.le_ceil R]
  refine ⟨Real.exp 1 * (B.factorial : ℝ) * (2 * Real.pi) ^ B, B, by positivity, fun x ν hx hν => ?_⟩
  rcases le_total 0 ν.im with h | h
  · rw [abs_of_nonneg h]
    exact norm_modifiedBesselKOrder_sharp_of_nonneg hx h hν hB
  · have hneg : (-ν).im = |ν.im| := by
      rw [abs_of_nonpos h]
      simp
    have hre : |(-ν).re| ≤ R := by simpa using hν
    have h0 : 0 ≤ (-ν).im := by
      rw [hneg]
      exact abs_nonneg _
    have hmain := norm_modifiedBesselKOrder_sharp_of_nonneg hx h0 hre hB
    rw [modifiedBesselKOrder_neg, hneg] at hmain
    exact hmain

end GaloisForLFunctions.BlackHoleRingdown

end
