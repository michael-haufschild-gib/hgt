import GaloisForLFunctions.HTGeometry.GammaVerticalModulus

/-!
# Gamma on the half-integer lines to the left, and vertical decay to the right

* `Real.Gamma_nat_add_three_halves` — `Γ(K + 3/2) = √π ∏_{j ≤ K} (j + 1/2)`.
* `norm_Gamma_neg_half_line_le` — on the line `Re u = -K - 1/2`,
  `‖Γ(u)‖ ≤ π / (Γ(K + 3/2) √cosh(π Im u))`, uniformly in `K`: the functional equation carries the
  line to the critical line `Re = 1/2`, where `‖Γ(1/2+it)‖² = π/cosh(πt)` exactly, and every factor
  `‖u + j‖` is at least its real part.
* `norm_Gamma_le_Gamma_re_div` — to the right of the imaginary axis,
  `‖Γ(z)‖ ≤ Γ(Re z) / (1 + (Im z)²/(Re z + 1)²)`: two steps of the functional equation and the
  bound `‖Γ‖ ≤ Γ(Re)`.
* `integrable_inv_one_add_affine_sq`, `integral_inv_one_add_affine_sq` — the resulting
  Cauchy-profile weight is integrable with total mass `π B/|b|`.
-/

open Complex MeasureTheory

namespace GaloisForLFunctions.HTGeometry

theorem Real.Gamma_nat_add_three_halves (K : ℕ) :
    Real.Gamma ((K : ℝ) + 3 / 2) =
      Real.sqrt Real.pi * ∏ j ∈ Finset.range (K + 1), ((j : ℝ) + 1 / 2) := by
  induction K with
  | zero =>
      have h := Real.Gamma_add_one (s := (1 / 2 : ℝ)) (by norm_num)
      rw [show (1 / 2 : ℝ) + 1 = 3 / 2 by norm_num, Real.Gamma_one_half_eq] at h
      simp only [Nat.cast_zero, zero_add, Finset.range_one, Finset.prod_singleton]
      rw [h]
      ring
  | succ K ih =>
      have hne : ((K : ℝ) + 3 / 2) ≠ 0 := by positivity
      have h := Real.Gamma_add_one hne
      rw [show ((K : ℝ) + 3 / 2) + 1 = ((K + 1 : ℕ) : ℝ) + 3 / 2 by push_cast; ring] at h
      rw [h, ih, Finset.prod_range_succ (n := K + 1)]
      push_cast
      ring

theorem one_div_sqrt_cosh_le (x : ℝ) :
    1 / Real.sqrt (Real.cosh x) ≤ Real.sqrt 2 * Real.exp (-(|x| / 2)) := by
  have hcosh : Real.exp |x| / 2 ≤ Real.cosh x := by
    rw [← Real.cosh_abs, Real.cosh_eq]
    have := Real.exp_pos (-|x|)
    linarith
  have hpos : 0 < Real.exp |x| / 2 := by positivity
  have hsqrt : Real.sqrt (Real.exp |x| / 2) ≤ Real.sqrt (Real.cosh x) := Real.sqrt_le_sqrt hcosh
  have hs : Real.sqrt (Real.exp |x| / 2) = Real.exp (|x| / 2) / Real.sqrt 2 := by
    rw [Real.sqrt_div (Real.exp_pos _).le, ← Real.exp_half]
  have hspos : 0 < Real.sqrt (Real.exp |x| / 2) := Real.sqrt_pos.2 hpos
  calc 1 / Real.sqrt (Real.cosh x) ≤ 1 / Real.sqrt (Real.exp |x| / 2) :=
        one_div_le_one_div_of_le hspos hsqrt
    _ = Real.sqrt 2 * Real.exp (-(|x| / 2)) := by
        rw [hs, Real.exp_neg]
        field_simp

/-- **`Γ` on the line `Re u = -K - 1/2`**, uniformly in `K`. -/
theorem norm_Gamma_neg_half_line_le (K : ℕ) (t : ℝ) :
    ‖Complex.Gamma (-(K : ℂ) - 1 / 2 + (t : ℂ) * I)‖ ≤
      Real.pi / (Real.Gamma ((K : ℝ) + 3 / 2) * Real.sqrt (Real.cosh (Real.pi * t))) := by
  set z : ℂ := -(K : ℂ) - 1 / 2 + (t : ℂ) * I with hz
  have hre : ∀ i : ℕ, (z + (i : ℂ)).re = (i : ℝ) - K - 1 / 2 := by
    intro i
    simp [hz]
    ring
  have hne : ∀ i : ℕ, i < K + 1 → z + (i : ℂ) ≠ 0 := by
    intro i _ h
    have := hre i
    rw [h, Complex.zero_re] at this
    have hhalf : (2 : ℝ) * ((i : ℝ) - K) = 1 := by linarith
    have hint : (2 : ℤ) * ((i : ℤ) - K) = 1 := by exact_mod_cast hhalf
    omega
  have hadd := norm_Gamma_add_nat z (K + 1) hne
  have hzK : z + ((K + 1 : ℕ) : ℂ) = 1 / 2 + (t : ℂ) * I := by
    rw [hz]
    push_cast
    ring
  rw [hzK] at hadd
  -- the product of the moduli is at least the product of the real parts
  have hprod : ∏ j ∈ Finset.range (K + 1), ((j : ℝ) + 1 / 2) ≤
      ∏ i ∈ Finset.range (K + 1), ‖z + (i : ℂ)‖ := by
    rw [← Finset.prod_range_reflect (fun j => ((j : ℝ) + 1 / 2)) (K + 1)]
    refine Finset.prod_le_prod (fun j _ => by positivity) fun i hi => ?_
    have hiK : i ≤ K := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    calc ((K + 1 - 1 - i : ℕ) : ℝ) + 1 / 2 = |(z + (i : ℂ)).re| := by
          rw [hre i, Nat.add_sub_cancel, Nat.cast_sub hiK, abs_of_neg (by
            have : (i : ℝ) ≤ K := by exact_mod_cast hiK
            linarith)]
          ring
      _ ≤ ‖z + (i : ℂ)‖ := Complex.abs_re_le_norm _
  have hGamma := Real.Gamma_nat_add_three_halves K
  have hGpos : 0 < Real.Gamma ((K : ℝ) + 3 / 2) := Real.Gamma_pos_of_pos (by positivity)
  have hpprod : 0 < ∏ j ∈ Finset.range (K + 1), ((j : ℝ) + 1 / 2) :=
    Finset.prod_pos fun j _ => by positivity
  have hcosh : 0 < Real.cosh (Real.pi * t) := Real.cosh_pos _
  have hhalf : ‖Complex.Gamma (1 / 2 + (t : ℂ) * I)‖ =
      Real.sqrt (Real.pi / Real.cosh (Real.pi * t)) := by
    rw [← norm_Gamma_half_add_I_sq t, Real.sqrt_sq (norm_nonneg _)]
  have hpi : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi :=
    Real.mul_self_sqrt Real.pi_pos.le
  -- `‖Γ(z)‖ · ∏ (j + 1/2) ≤ ‖Γ(1/2 + it)‖`
  have hkey : ‖Complex.Gamma z‖ * ∏ j ∈ Finset.range (K + 1), ((j : ℝ) + 1 / 2) ≤
      Real.sqrt (Real.pi / Real.cosh (Real.pi * t)) := by
    rw [← hhalf, hadd, mul_comm]
    exact mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
  rw [le_div_iff₀ (by positivity)]
  rw [hGamma]
  calc ‖Complex.Gamma z‖ * ((Real.sqrt Real.pi * ∏ j ∈ Finset.range (K + 1), ((j : ℝ) + 1 / 2)) *
        Real.sqrt (Real.cosh (Real.pi * t)))
      = (‖Complex.Gamma z‖ * ∏ j ∈ Finset.range (K + 1), ((j : ℝ) + 1 / 2)) *
          (Real.sqrt Real.pi * Real.sqrt (Real.cosh (Real.pi * t))) := by ring
    _ ≤ Real.sqrt (Real.pi / Real.cosh (Real.pi * t)) *
          (Real.sqrt Real.pi * Real.sqrt (Real.cosh (Real.pi * t))) :=
        mul_le_mul_of_nonneg_right hkey (by positivity)
    _ = Real.pi := by
        rw [Real.sqrt_div Real.pi_pos.le]
        field_simp
        rw [Real.sq_sqrt Real.pi_pos.le]

/-- The same bound with the hyperbolic cosine replaced by its exponential envelope. -/
theorem norm_Gamma_neg_half_line_le_exp (K : ℕ) (t : ℝ) :
    ‖Complex.Gamma (-(K : ℂ) - 1 / 2 + (t : ℂ) * I)‖ ≤
      Real.pi * Real.sqrt 2 * Real.exp (-(Real.pi * |t| / 2)) / Real.Gamma ((K : ℝ) + 3 / 2) := by
  have hGpos : 0 < Real.Gamma ((K : ℝ) + 3 / 2) := Real.Gamma_pos_of_pos (by positivity)
  have hcosh := one_div_sqrt_cosh_le (Real.pi * t)
  have habs : |Real.pi * t| / 2 = Real.pi * |t| / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
  rw [habs] at hcosh
  refine (norm_Gamma_neg_half_line_le K t).trans ?_
  have hsq : 0 < Real.sqrt (Real.cosh (Real.pi * t)) := Real.sqrt_pos.2 (Real.cosh_pos _)
  calc Real.pi / (Real.Gamma ((K : ℝ) + 3 / 2) * Real.sqrt (Real.cosh (Real.pi * t)))
      = Real.pi / Real.Gamma ((K : ℝ) + 3 / 2) * (1 / Real.sqrt (Real.cosh (Real.pi * t))) := by
        field_simp
    _ ≤ Real.pi / Real.Gamma ((K : ℝ) + 3 / 2) *
          (Real.sqrt 2 * Real.exp (-(Real.pi * |t| / 2))) :=
        mul_le_mul_of_nonneg_left hcosh (by positivity)
    _ = _ := by ring

/-- **Vertical decay to the right of the imaginary axis.** -/
theorem norm_Gamma_le_Gamma_re_div {z : ℂ} (hz : 0 < z.re) :
    ‖Complex.Gamma z‖ ≤ Real.Gamma z.re / (1 + z.im ^ 2 / (z.re + 1) ^ 2) := by
  have hz0 : z ≠ 0 := fun h => by rw [h, Complex.zero_re] at hz; linarith
  have hz1 : z + 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h
    simp at this
    linarith
  have hstep : Complex.Gamma (z + 2) = (z + 1) * z * Complex.Gamma z := by
    rw [show z + 2 = (z + 1) + 1 by ring, Complex.Gamma_add_one _ hz1,
      Complex.Gamma_add_one _ hz0]
    ring
  have hre2 : 0 < (z + 2).re := by simp; linarith
  set X := z.re with hX
  set Y := z.im with hY
  have hbound := norm_Gamma_le_Gamma_re hre2
  rw [hstep, norm_mul, norm_mul] at hbound
  have hre2' : (z + 2).re = X + 2 := by simp [hX]
  rw [hre2'] at hbound
  have hG2 : Real.Gamma (X + 2) = (X + 1) * X * Real.Gamma X := by
    rw [show X + 2 = (X + 1) + 1 by ring, Real.Gamma_add_one (by linarith),
      Real.Gamma_add_one (by linarith)]
    ring
  rw [hG2] at hbound
  have hGX : 0 < Real.Gamma X := Real.Gamma_pos_of_pos hz
  have hn0 : ‖z‖ ^ 2 = X ^ 2 + Y ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hn1 : ‖z + 1‖ ^ 2 = (X + 1) ^ 2 + Y ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [hX, hY]
    ring
  -- `X ((X+1)² + Y²) ≤ (X+1) ‖z‖ ‖z+1‖`
  have hkey : X * ((X + 1) ^ 2 + Y ^ 2) ≤ (X + 1) * ‖z‖ * ‖z + 1‖ := by
    have hlhs : 0 ≤ X * ((X + 1) ^ 2 + Y ^ 2) := by positivity
    have hrhs : 0 ≤ (X + 1) * ‖z‖ * ‖z + 1‖ := by positivity
    refine (sq_le_sq₀ hlhs hrhs).mp ?_
    rw [mul_pow, mul_pow, mul_pow, hn0, hn1]
    nlinarith [sq_nonneg Y, sq_nonneg X, hz]
  have hnorm_pos : 0 < ‖z‖ * ‖z + 1‖ := by positivity
  have hden : 0 < 1 + Y ^ 2 / (X + 1) ^ 2 := by positivity
  rw [le_div_iff₀ hden]
  have h1 : ‖Complex.Gamma z‖ * (‖z + 1‖ * ‖z‖) ≤ (X + 1) * X * Real.Gamma X := by
    calc ‖Complex.Gamma z‖ * (‖z + 1‖ * ‖z‖) = ‖z + 1‖ * ‖z‖ * ‖Complex.Gamma z‖ := by ring
      _ ≤ _ := hbound
  have hX1 : 0 < X + 1 := by linarith
  have hexp : 1 + Y ^ 2 / (X + 1) ^ 2 = ((X + 1) ^ 2 + Y ^ 2) / (X + 1) ^ 2 := by
    field_simp
  rw [hexp]
  have hGz := norm_nonneg (Complex.Gamma z)
  -- combine
  have h2 : ‖Complex.Gamma z‖ * ((X + 1) ^ 2 + Y ^ 2) * X ≤
      ‖Complex.Gamma z‖ * ((X + 1) * ‖z‖ * ‖z + 1‖) :=
    by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (by linarith [hkey]) hGz
  have h3 : ‖Complex.Gamma z‖ * ((X + 1) * ‖z‖ * ‖z + 1‖) ≤ (X + 1) * ((X + 1) * X * Real.Gamma X) := by
    calc ‖Complex.Gamma z‖ * ((X + 1) * ‖z‖ * ‖z + 1‖) =
        (X + 1) * (‖Complex.Gamma z‖ * (‖z + 1‖ * ‖z‖)) := by ring
      _ ≤ (X + 1) * ((X + 1) * X * Real.Gamma X) := mul_le_mul_of_nonneg_left h1 hX1.le
  rw [mul_div_assoc', div_le_iff₀ (by positivity)]
  have h4 : ‖Complex.Gamma z‖ * ((X + 1) ^ 2 + Y ^ 2) * X ≤ Real.Gamma X * (X + 1) ^ 2 * X := by
    nlinarith [h2, h3]
  exact le_of_mul_le_mul_right (by linarith [h4]) hz

theorem integrable_inv_one_add_affine_sq {a b B : ℝ} (hb : b ≠ 0) (hB : 0 < B) :
    Integrable (fun t : ℝ => (1 + (a + b * t) ^ 2 / B ^ 2)⁻¹) := by
  have hbase := integrable_inv_one_add_sq
  have h1 : Integrable (fun t : ℝ => (1 + ((b / B) * t + a / B) ^ 2)⁻¹) :=
    (hbase.comp_add_right (a / B)).comp_mul_left' (div_ne_zero hb hB.ne')
  refine h1.congr (Filter.Eventually.of_forall fun t => ?_)
  simp only
  congr 1
  field_simp
  ring

theorem integral_inv_one_add_affine_sq {a b B : ℝ} (hb : b ≠ 0) (hB : 0 < B) :
    ∫ t : ℝ, (1 + (a + b * t) ^ 2 / B ^ 2)⁻¹ = Real.pi * B / |b| := by
  have hfun : (fun t : ℝ => (1 + (a + b * t) ^ 2 / B ^ 2)⁻¹) =
      fun t : ℝ => (fun v : ℝ => (1 + (v + a / B) ^ 2)⁻¹) ((b / B) * t) := by
    funext t
    congr 1
    field_simp
    ring
  rw [hfun, MeasureTheory.Measure.integral_comp_mul_left
    (fun v : ℝ => (1 + (v + a / B) ^ 2)⁻¹) (b / B),
    MeasureTheory.integral_add_right_eq_self (fun v : ℝ => (1 + v ^ 2)⁻¹) (a / B),
    integral_univ_inv_one_add_sq, smul_eq_mul, inv_div, abs_div, abs_of_pos hB]
  field_simp

end GaloisForLFunctions.HTGeometry
