import GaloisForLFunctions.RHTower.DegreeThreeHankelTriplicationTwist

/-!
# The twist symbol of the cube-root Voronoi transform

For `R(v) = Γ(v/2)² / (Γ(v/2 + 1/3) Γ(v/2 + 2/3))` the twist symbol is
`v(w) = R((2 - w)/3) / R((1 + w)/3)`.

* `twistSymbol` is holomorphic on `-3 < Re w < 2` and zero-free on `-1 < Re w < 2`.
* `|twistSymbol (1/2 + it)| = 1`: the two arguments are complex conjugates on the critical line.
* Gauss triplication factors the Mellin multiplier of the degree-three Voronoi transform in the
  cube-root chart, `3^{w - 1/2} Γℝ((w + 1)/3)³ / Γℝ((2 - w)/3)³`, as the sine-transform multiplier
  `Γℝ(w + 1) / Γℝ(2 - w)` times `twistSymbol (1 - w)`.
-/

namespace RHTower.DegreeThreeHankel

open Complex

/-- The Mellin symbol `R((2 - w)/3) / R((1 + w)/3)`, written as a product of Gamma values and
reciprocal Gamma values. -/
noncomputable def twistSymbol (w : ℂ) : ℂ :=
  Gamma ((2 - w) / 6) ^ 2 * (Gamma ((2 - w) / 6 + 1 / 3))⁻¹ * (Gamma ((2 - w) / 6 + 2 / 3))⁻¹ *
    (Gamma ((1 + w) / 6 + 1 / 3) * Gamma ((1 + w) / 6 + 2 / 3) * ((Gamma ((1 + w) / 6))⁻¹) ^ 2)

/-- The twist symbol is the quotient of the triplication remainders `tripR`. -/
theorem twistSymbol_eq_tripR_mul_inv (w : ℂ) :
    twistSymbol w = tripR ((2 - w) / 3) * (tripR ((1 + w) / 3))⁻¹ := by
  have e1 : (2 - w) / 3 / 2 = (2 - w) / 6 := by ring
  have e2 : (1 + w) / 3 / 2 = (1 + w) / 6 := by ring
  unfold twistSymbol tripR
  rw [e1, e2]
  simp only [mul_inv, inv_inv, inv_pow]
  ring

private lemma ne_neg_nat_of_re_pos {z : ℂ} (hz : 0 < z.re) : ∀ m : ℕ, z ≠ -m := by
  intro m h
  have := congrArg Complex.re h
  simp at this
  linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

private lemma re_div_six (z : ℂ) : (z / 6).re = z.re / 6 := Complex.div_ofNat_re z 6

/-- Holomorphy on the strip `-3 < Re w < 2`: every Gamma factor that is not inverted has an
argument of positive real part there. -/
theorem differentiableOn_twistSymbol :
    DifferentiableOn ℂ twistSymbol {w : ℂ | -3 < w.re ∧ w.re < 2} := by
  intro w hw
  obtain ⟨h1, h2⟩ := hw
  have hA : 0 < ((2 - w) / 6).re := by rw [re_div_six]; simp; linarith
  have hB : 0 < ((1 + w) / 6 + 1 / 3).re := by rw [add_re, re_div_six]; norm_num; linarith
  have hC : 0 < ((1 + w) / 6 + 2 / 3).re := by rw [add_re, re_div_six]; norm_num; linarith
  have dA : DifferentiableAt ℂ (fun w : ℂ => Gamma ((2 - w) / 6)) w :=
    (differentiableAt_Gamma _ (ne_neg_nat_of_re_pos hA)).comp w (by fun_prop)
  have dB : DifferentiableAt ℂ (fun w : ℂ => Gamma ((1 + w) / 6 + 1 / 3)) w :=
    (differentiableAt_Gamma _ (ne_neg_nat_of_re_pos hB)).comp w (by fun_prop)
  have dC : DifferentiableAt ℂ (fun w : ℂ => Gamma ((1 + w) / 6 + 2 / 3)) w :=
    (differentiableAt_Gamma _ (ne_neg_nat_of_re_pos hC)).comp w (by fun_prop)
  have dI1 : DifferentiableAt ℂ (fun w : ℂ => (Gamma ((2 - w) / 6 + 1 / 3))⁻¹) w :=
    (differentiable_one_div_Gamma _).comp w (by fun_prop)
  have dI2 : DifferentiableAt ℂ (fun w : ℂ => (Gamma ((2 - w) / 6 + 2 / 3))⁻¹) w :=
    (differentiable_one_div_Gamma _).comp w (by fun_prop)
  have dI3 : DifferentiableAt ℂ (fun w : ℂ => (Gamma ((1 + w) / 6))⁻¹) w :=
    (differentiable_one_div_Gamma _).comp w (by fun_prop)
  exact ((((dA.pow 2).mul dI1).mul dI2).mul ((dB.mul dC).mul (dI3.pow 2))).differentiableWithinAt

/-- The twist symbol has no zeros on the strip `-1 < Re w < 2`. -/
theorem twistSymbol_ne_zero {w : ℂ} (h1 : -1 < w.re) (h2 : w.re < 2) : twistSymbol w ≠ 0 := by
  have hA : 0 < ((2 - w) / 6).re := by rw [re_div_six]; simp; linarith
  have hA1 : 0 < ((2 - w) / 6 + 1 / 3).re := by rw [add_re, re_div_six]; norm_num; linarith
  have hA2 : 0 < ((2 - w) / 6 + 2 / 3).re := by rw [add_re, re_div_six]; norm_num; linarith
  have hB : 0 < ((1 + w) / 6 + 1 / 3).re := by rw [add_re, re_div_six]; norm_num; linarith
  have hC : 0 < ((1 + w) / 6 + 2 / 3).re := by rw [add_re, re_div_six]; norm_num; linarith
  have hD : 0 < ((1 + w) / 6).re := by rw [re_div_six]; simp; linarith
  unfold twistSymbol
  simp only [ne_eq, mul_eq_zero, pow_eq_zero_iff, inv_eq_zero, OfNat.ofNat_ne_zero,
    not_false_eq_true, not_or]
  exact ⟨⟨⟨Gamma_ne_zero_of_re_pos hA, Gamma_ne_zero_of_re_pos hA1⟩, Gamma_ne_zero_of_re_pos hA2⟩,
    ⟨Gamma_ne_zero_of_re_pos hB, Gamma_ne_zero_of_re_pos hC⟩, Gamma_ne_zero_of_re_pos hD⟩

/-- Unimodularity on the critical line: at `w = 1/2 + it` the symbol is `conj X / X`. -/
theorem norm_twistSymbol_critical (t : ℝ) : ‖twistSymbol (1 / 2 + t * I)‖ = 1 := by
  have hconj : (2 - (1 / 2 + t * I)) / 6 = (starRingEnd ℂ) ((1 + (1 / 2 + t * I)) / 6) := by
    simp only [map_div₀, map_add, map_mul, map_one, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
    ring
  unfold twistSymbol
  rw [hconj]
  set a : ℂ := (1 + (1 / 2 + t * I)) / 6 with ha
  have hre : a.re = 1 / 4 := by rw [ha, re_div_six]; simp; norm_num
  have hp1 : 0 < a.re := by rw [hre]; norm_num
  have hp2 : 0 < (a + 1 / 3).re := by rw [add_re, hre]; norm_num
  have hp3 : 0 < (a + 2 / 3).re := by rw [add_re, hre]; norm_num
  have c1 : (starRingEnd ℂ) a + 1 / 3 = (starRingEnd ℂ) (a + 1 / 3) := by
    simp only [map_add, map_div₀, map_one, map_ofNat]
  have c2 : (starRingEnd ℂ) a + 2 / 3 = (starRingEnd ℂ) (a + 2 / 3) := by
    simp only [map_add, map_div₀, map_ofNat]
  rw [c1, c2, Gamma_conj, Gamma_conj, Gamma_conj]
  have n1 := Gamma_ne_zero_of_re_pos hp1
  have n2 := Gamma_ne_zero_of_re_pos hp2
  have n3 := Gamma_ne_zero_of_re_pos hp3
  set X : ℂ := Gamma a ^ 2 * (Gamma (a + 1 / 3))⁻¹ * (Gamma (a + 2 / 3))⁻¹ with hX
  have hXne : X ≠ 0 := by
    rw [hX]; exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 n1) (inv_ne_zero n2)) (inv_ne_zero n3)
  have e : (starRingEnd ℂ) (Gamma a) ^ 2 * ((starRingEnd ℂ) (Gamma (a + 1 / 3)))⁻¹ *
      ((starRingEnd ℂ) (Gamma (a + 2 / 3)))⁻¹ *
      (Gamma (a + 1 / 3) * Gamma (a + 2 / 3) * ((Gamma a)⁻¹) ^ 2) = (starRingEnd ℂ) X * X⁻¹ := by
    rw [hX]
    simp only [map_mul, map_pow, map_inv₀, mul_inv, inv_inv, inv_pow]
    ring
  rw [e, norm_mul, norm_inv, Complex.norm_conj]
  exact mul_inv_cancel₀ (norm_ne_zero_iff.mpr hXne)

/-- Symbol-level factorization of the cube-root Voronoi transform: on `-1 < Re w < 2` its Mellin
multiplier is the sine-transform multiplier times the twist symbol at `1 - w`. -/
theorem voronoi_multiplier_eq_sine_mul_twist {w : ℂ} (h1 : -1 < w.re) (h2 : w.re < 2) :
    (3 : ℂ) ^ (w - 1 / 2) * (Gammaℝ ((w + 1) / 3) ^ 3 * (Gammaℝ ((2 - w) / 3) ^ 3)⁻¹)
      = Gammaℝ (w + 1) * (Gammaℝ (2 - w))⁻¹ * twistSymbol (1 - w) := by
  have hs : 0 < ((w + 1) / 3 / 2).re := by
    rw [div_div, show ((3 : ℂ) * 2) = 6 by norm_num, re_div_six]; simp; linarith
  have hr : 0 < ((1 - (w + 1) / 3) / 2).re := by
    rw [show (1 - (w + 1) / 3) / 2 = (2 - w) / 6 by ring, re_div_six]; simp; linarith
  have T := triplication_twist ((w + 1) / 3) (ne_neg_nat_of_re_pos hs) (ne_neg_nat_of_re_pos hr)
  rw [show 3 * ((w + 1) / 3) = w + 1 by ring, show 1 - (w + 1) / 3 = (2 - w) / 3 by ring,
    show 3 * ((2 - w) / 3) = 2 - w by ring, show w + 1 - 1 - 1 / 2 = w - 1 / 2 by ring] at T
  rw [twistSymbol_eq_tripR_mul_inv, show (2 - (1 - w)) / 3 = (w + 1) / 3 by ring,
    show (1 + (1 - w)) / 3 = (2 - w) / 3 by ring]
  have gs : Gammaℝ ((w + 1) / 3) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by
    have := hs; rw [div_div, show ((3 : ℂ) * 2) = 6 by norm_num, re_div_six] at this
    rw [show (w + 1) / 3 = (w + 1) / 6 * 2 by ring, mul_re]; simp; linarith)
  have gr : Gammaℝ ((2 - w) / 3) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by
    rw [show (2 - w) / 3 = (2 - w) / 6 * 2 by ring, mul_re, re_div_six]; simp; linarith)
  have g1 : Gammaℝ (w + 1) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  have g2 : Gammaℝ (2 - w) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  have tr : tripR ((2 - w) / 3) ≠ 0 := by
    have hA : 0 < ((2 - w) / 3 / 2).re := by
      rw [show (2 - w) / 3 / 2 = (2 - w) / 6 by ring, re_div_six]; simp; linarith
    have hA1 : 0 < ((2 - w) / 3 / 2 + 1 / 3).re := by
      rw [add_re, show (2 - w) / 3 / 2 = (2 - w) / 6 by ring, re_div_six]; norm_num; linarith
    have hA2 : 0 < ((2 - w) / 3 / 2 + 2 / 3).re := by
      rw [add_re, show (2 - w) / 3 / 2 = (2 - w) / 6 by ring, re_div_six]; norm_num; linarith
    unfold tripR
    simp only [ne_eq, mul_eq_zero, pow_eq_zero_iff, inv_eq_zero, OfNat.ofNat_ne_zero,
      not_false_eq_true, not_or]
    exact ⟨⟨Gamma_ne_zero_of_re_pos hA, Gamma_ne_zero_of_re_pos hA1⟩, Gamma_ne_zero_of_re_pos hA2⟩
  field_simp
  field_simp at T
  linear_combination T

end RHTower.DegreeThreeHankel
